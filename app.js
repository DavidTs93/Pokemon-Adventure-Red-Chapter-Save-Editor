"use strict";

const SECTION_SIZE = 0x1000;
const CHUNK_SIZES = [0xF24, 0xFF0, 0xFF0, 0xFF0, 0xD98, 0xFF0, 0xFF0, 0xFF0, 0xFF0, 0xFF0, 0xFF0, 0xFF0, 0xFF0, 0x450];
const PARTY_OFFSET = 0x38;
const PARTY_RECORD_SIZE = 100;
const BOX_RECORD_SIZE = 80;
const BOX_CAPACITY = 30;
const BOX_COUNT = 14;
const POKEMON_EXPORT_FORMAT = "pokemon-adventure-red-records";
const POKEMON_EXPORT_VERSION = 1;
const STATS = ["HP", "Attack", "Defense", "Speed", "Sp. Atk", "Sp. Def"];
const DISPLAY_STAT_INDICES = [0, 1, 2, 4, 5, 3];
const NATURES = ["Hardy", "Lonely", "Brave", "Adamant", "Naughty", "Bold", "Docile", "Relaxed", "Impish", "Lax", "Timid", "Hasty", "Serious", "Jolly", "Naive", "Modest", "Mild", "Quiet", "Bashful", "Rash", "Calm", "Gentle", "Sassy", "Careful", "Quirky"];
const SUBSTRUCT_ORDERS = [
  "GAEM", "GAME", "GEAM", "GEMA", "GMAE", "GMEA",
  "AGEM", "AGME", "AEGM", "AEMG", "AMGE", "AMEG",
  "EGAM", "EGMA", "EAGM", "EAMG", "EMGA", "EMAG",
  "MGAE", "MGEA", "MAGE", "MAEG", "MEGA", "MEAG"
];

const $ = selector => document.querySelector(selector);
const state = {
  bytes: null, layout: null, fileName: "", changes: 0, current: null, game: null,
  selection: new Map(), selectMode: false, clipboard: [], context: null, lastLocation: null,
  allowIllegalMoves: false, allowIllegalEvs: false, history: [], searchQuery: "", itemById: new Map(),
  renameBoxIndex: 0, importTarget: null
};

const els = {
  input: $("#saveInput"), loader: $("#loader"), workspace: $("#workspace"), error: $("#loadError"),
  download: $("#downloadButton"), undo: $("#undoButton"), reset: $("#resetButton"), fileName: $("#fileName"), trainer: $("#trainerName"), slot: $("#saveSlot"),
  changes: $("#changeCount"), party: $("#partyGrid"), boxSelect: $("#boxSelect"), box: $("#boxGrid"),
  dialog: $("#editorDialog"), form: $("#pokemonForm"), editorLocation: $("#editorLocation"), editorTitle: $("#editorTitle"),
  species: $("#speciesField"), nickname: $("#nicknameField"), level: $("#levelField"), nature: $("#natureField"),
  ability: $("#abilityField"), item: $("#itemField"), friendship: $("#friendshipField"), formError: $("#formError"),
  moves: [...document.querySelectorAll(".move-field")], moveInfos: [...document.querySelectorAll(".move-info")],
  ivs: $("#ivFields"), evs: $("#evFields"), calculatedStats: $("#calculatedStats"),
  clearPokemon: $("#clearPokemon"), illegalMoves: $("#illegalMovesToggle"), illegalEvs: $("#illegalEvsToggle"),
  hiddenPower: $("#hiddenPowerType"), selectMode: $("#selectMode"), selectionCount: $("#selectionCount"),
  movePanelToggle: $("#movePanelToggle"), editorLayout: $("#editorLayout"), movePanel: $("#movePanel"),
  moveBoxSelect: $("#moveBoxSelect"), moveBox: $("#moveBoxGrid"), actionStatus: $("#actionStatus"), contextMenu: $("#pokemonMenu"),
  boxSearch: $("#boxSearch"), clearBoxSearch: $("#clearBoxSearch"), searchPanel: $("#boxSearchPanel"),
  searchCount: $("#boxSearchCount"), searchResults: $("#boxSearchResults"), exportSelected: $("#exportSelected"),
  importInput: $("#pokemonImportInput"), renameDialog: $("#renameBoxDialog"), renameForm: $("#renameBoxForm"),
  boxNameField: $("#boxNameField"), reportDialog: $("#reportDialog"), reportSummary: $("#reportSummary"),
  reportDetails: $("#reportDetails"), confirmDownload: $("#confirmDownload")
};

function u16(bytes, offset) { return bytes[offset] | (bytes[offset + 1] << 8); }
function u32(bytes, offset) { return (u16(bytes, offset) | (u16(bytes, offset + 2) << 16)) >>> 0; }
function w16(bytes, offset, value) { bytes[offset] = value & 255; bytes[offset + 1] = (value >>> 8) & 255; }
function w32(bytes, offset, value) { w16(bytes, offset, value); w16(bytes, offset + 2, value >>> 16); }
function clamp(value, min, max) { return Math.max(min, Math.min(max, Number(value) || 0)); }

const decodeMap = new Map([[0x00, " "], [0x1B, "é"], [0xAB, "!"], [0xAC, "?"], [0xAD, "."], [0xAE, "-"], [0xB4, "'"], [0xB5, "♂"], [0xB6, "♀"], [0xB8, ","], [0xBA, "/"], [0xF0, ":"]]);
for (let i = 0; i < 10; i++) decodeMap.set(0xA1 + i, String(i));
for (let i = 0; i < 26; i++) { decodeMap.set(0xBB + i, String.fromCharCode(65 + i)); decodeMap.set(0xD5 + i, String.fromCharCode(97 + i)); }
const encodeMap = new Map([...decodeMap].map(([key, value]) => [value, key]));
const spriteDataCache = new Map();
const spriteDataPromises = new Map();

function decodeText(bytes, offset, length) {
  let output = "";
  for (let i = 0; i < length; i++) {
    const value = bytes[offset + i];
    if (value === 0xFF) break;
    output += decodeMap.get(value) ?? "?";
  }
  return output.trimEnd();
}

function decodeTextRaw(bytes, offset, length) {
  let output = "";
  for (let i = 0; i < length; i++) {
    const value = bytes[offset + i];
    if (value === 0xFF) break;
    output += decodeMap.get(value) ?? "?";
  }
  return output;
}

function encodeText(bytes, offset, length, text) {
  bytes.fill(0xFF, offset, offset + length);
  [...String(text).slice(0, length)].forEach((character, index) => { bytes[offset + index] = encodeMap.get(character) ?? 0xAC; });
}

function checksum(bytes, offset, size) {
  let sum = 0;
  for (let i = 0; i < size; i += 4) sum = (sum + u32(bytes, offset + i)) >>> 0;
  return ((sum & 0xFFFF) + (sum >>> 16)) & 0xFFFF;
}

function inspectSlot(bytes, firstSector) {
  const sections = new Map();
  const counters = [];
  for (let physical = firstSector; physical < firstSector + 14; physical++) {
    const offset = physical * SECTION_SIZE;
    const id = u16(bytes, offset + 0xFF4);
    if (id > 13 || sections.has(id)) continue;
    const expected = u16(bytes, offset + 0xFF6);
    if (checksum(bytes, offset, CHUNK_SIZES[id]) !== expected) continue;
    sections.set(id, offset);
    counters.push(u32(bytes, offset + 0xFFC));
  }
  if (sections.size !== 14) return null;
  return { firstSector, sections, counter: counters[0] >>> 0 };
}

function isNewerCounter(a, b) { return a === b || (((a - b) >>> 0) < 0x80000000); }

function assemble(bytes, sections, ids, totalSize) {
  const output = new Uint8Array(totalSize);
  let target = 0;
  ids.forEach(id => {
    const size = CHUNK_SIZES[id];
    output.set(bytes.subarray(sections.get(id), sections.get(id) + size), target);
    target += size;
  });
  return output;
}

function parseSave(bytes) {
  if (bytes.length < 0x20000) throw new Error("Adventure Red uses a 128 KiB save. This file is too small.");
  const first = inspectSlot(bytes, 0);
  const second = inspectSlot(bytes, 14);
  if (!first && !second) throw new Error("No complete Adventure Red/FireRed save slot with valid checksums was found.");
  const active = !first ? second : !second ? first : (isNewerCounter(second.counter, first.counter) ? second : first);
  const sb2 = assemble(bytes, active.sections, [0], 0xF24);
  const sb1 = assemble(bytes, active.sections, [1, 2, 3, 4], 0x3D68);
  const storage = assemble(bytes, active.sections, [5, 6, 7, 8, 9, 10, 11, 12, 13], 0x83D0);
  return { active, sb1, sb2, storage };
}

function copyChunk(target, offset, source, sourceOffset, size) { target.set(source.subarray(sourceOffset, sourceOffset + size), offset); }

function serializeSave() {
  compactParty();
  const { active, sb1, sb2, storage } = state.layout;
  const logical = new Map();
  logical.set(0, [sb2, 0]);
  let cursor = 0;
  for (let id = 1; id <= 4; id++) { logical.set(id, [sb1, cursor]); cursor += CHUNK_SIZES[id]; }
  cursor = 0;
  for (let id = 5; id <= 13; id++) { logical.set(id, [storage, cursor]); cursor += CHUNK_SIZES[id]; }

  for (let id = 0; id < 14; id++) {
    const sectionOffset = active.sections.get(id);
    const [source, sourceOffset] = logical.get(id);
    copyChunk(state.bytes, sectionOffset, source, sourceOffset, CHUNK_SIZES[id]);
    w16(state.bytes, sectionOffset + 0xFF6, checksum(state.bytes, sectionOffset, CHUNK_SIZES[id]));
  }
  return state.bytes;
}

function getBoxRecord(box, slot) {
  return { bytes: state.layout.storage, offset: 4 + (box * BOX_CAPACITY + slot) * BOX_RECORD_SIZE };
}

function getPartyRecord(slot) { return { bytes: state.layout.sb1, offset: PARTY_OFFSET + slot * PARTY_RECORD_SIZE }; }

function decryptPokemonBlocks(bytes, offset) {
  const personality = u32(bytes, offset);
  const key = (personality ^ u32(bytes, offset + 4)) >>> 0;
  const order = SUBSTRUCT_ORDERS[personality % 24];
  const blocks = {};
  for (let physical = 0; physical < 4; physical++) {
    const block = new Uint8Array(12);
    for (let word = 0; word < 3; word++) {
      const encrypted = u32(bytes, offset + 32 + physical * 12 + word * 4);
      w32(block, word * 4, (encrypted ^ key) >>> 0);
    }
    blocks[order[physical]] = block;
  }
  return blocks;
}

function pokemonChecksum(blocks) {
  let sum = 0;
  for (const label of "GAEM") {
    for (let offset = 0; offset < 12; offset += 2) sum = (sum + u16(blocks[label], offset)) & 0xFFFF;
  }
  return sum;
}

function encryptPokemonBlocks(bytes, offset, blocks, personality) {
  const key = (personality ^ u32(bytes, offset + 4)) >>> 0;
  const order = SUBSTRUCT_ORDERS[personality % 24];
  for (let physical = 0; physical < 4; physical++) {
    const block = blocks[order[physical]];
    for (let word = 0; word < 3; word++) {
      w32(bytes, offset + 32 + physical * 12 + word * 4, (u32(block, word * 4) ^ key) >>> 0);
    }
  }
  w16(bytes, offset + 28, pokemonChecksum(blocks));
}

function readPokemon(kind, index, box = 0) {
  const record = kind === "party" ? getPartyRecord(index) : getBoxRecord(box, index);
  const { bytes, offset } = record;
  const party = kind === "party";
  const personality = u32(bytes, offset);
  const blocks = decryptPokemonBlocks(bytes, offset);
  const species = u16(blocks.G, 0);
  const ivWord = u32(blocks.M, 4);
  const experience = u32(blocks.G, 4);
  const storedNicknameRaw = decodeTextRaw(bytes, offset + 8, 10);
  const defaultName = speciesName(species).slice(0, 10);
  // A trailing space is an invisible on-save marker for an explicitly entered
  // nickname that is identical to the species name. Ordinary default names end
  // at the species name and are followed by 0xFF padding.
  const sameNameNickname = defaultName.length < 10 && storedNicknameRaw === `${defaultName} `;
  const nickname = storedNicknameRaw === defaultName ? "" : (sameNameNickname ? defaultName : storedNicknameRaw.trimEnd());
  return {
    kind, index, box, record, species, personality, blocks,
    nickname,
    item: u16(blocks.G, 2),
    experience,
    level: party ? bytes[offset + 84] : levelFromExperience(species, experience),
    friendship: blocks.G[9],
    moves: [0, 1, 2, 3].map(i => u16(blocks.A, i * 2)),
    ivs: [0, 1, 2, 3, 4, 5].map(i => (ivWord >>> (i * 5)) & 31),
    evs: [0, 1, 2, 3, 4, 5].map(i => blocks.E[i]),
    ability: (ivWord >>> 31) ? 2 : 0,
    nature: personality % 25,
    isEgg: Boolean((ivWord >>> 30) & 1),
    checksumValid: pokemonChecksum(blocks) === u16(bytes, offset + 28)
  };
}

function growthExperience(rate, level) {
  const n = clamp(level, 1, 100), n2 = n * n, n3 = n2 * n;
  if (rate === 1) {
    if (n <= 50) return Math.floor(n3 * (100 - n) / 50);
    if (n <= 68) return Math.floor(n3 * (150 - n) / 100);
    if (n <= 98) return Math.floor(n3 * Math.floor((1911 - 10 * n) / 3) / 500);
    return Math.floor(n3 * (160 - n) / 100);
  }
  if (rate === 2) {
    if (n <= 15) return Math.floor(n3 * (Math.floor((n + 1) / 3) + 24) / 50);
    if (n <= 36) return Math.floor(n3 * (n + 14) / 50);
    return Math.floor(n3 * (Math.floor(n / 2) + 32) / 50);
  }
  if (rate === 3) return Math.max(0, Math.floor(6 * n3 / 5 - 15 * n2 + 100 * n - 140));
  if (rate === 4) return Math.floor(4 * n3 / 5);
  if (rate === 5) return Math.floor(5 * n3 / 4);
  return n3;
}

function levelFromExperience(speciesId, experience) {
  const rate = state.game.species[speciesId]?.growthRate ?? 0;
  let level = 1;
  while (level < 100 && growthExperience(rate, level + 1) <= experience) level++;
  return level;
}

function speciesName(id) { return state.game.species[id]?.name || (id ? `Unknown #${id}` : "Empty slot"); }
function moveName(id) { return state.game.moves[id]?.name || (id ? `Unknown #${id}` : "—"); }

function setPersonality(oldValue, nature) {
  return (oldValue - oldValue % 25 + nature) >>> 0;
}

function writePokemon(mon, values) {
  const { bytes, offset } = mon.record;
  const party = mon.kind === "party";
  if (!values.species) { bytes.fill(0, offset, offset + (party ? PARTY_RECORD_SIZE : BOX_RECORD_SIZE)); return; }

  if (!mon.species) initializePokemon(mon, values.species);
  const current = readPokemon(mon.kind, mon.index, mon.box);
  const blocks = current.blocks;
  const personality = setPersonality(current.personality, values.nature);
  w32(bytes, offset, personality);
  const defaultName = speciesName(values.species).slice(0, 10);
  const nickname = values.nickname === "" ? defaultName
    : (values.nickname === defaultName && defaultName.length < 10 ? `${defaultName} ` : values.nickname);
  encodeText(bytes, offset + 8, 10, nickname);
  w16(blocks.G, 0, values.species);
  w16(blocks.G, 2, values.item);
  w32(blocks.G, 4, growthExperience(state.game.species[values.species]?.growthRate ?? 0, values.level));
  blocks.G[9] = values.friendship;
  values.moves.forEach((move, index) => w16(blocks.A, index * 2, move));
  const ppBonuses = blocks.G[8];
  values.moves.forEach((move, index) => {
    const basePP = state.game.moves[move]?.pp || 0;
    const bonus = (ppBonuses >>> (index * 2)) & 3;
    blocks.A[8 + index] = Math.floor(basePP * (5 + bonus) / 5);
  });
  values.evs.forEach((value, index) => { blocks.E[index] = value; });
  const oldIvWord = u32(blocks.M, 4);
  let ivWord = oldIvWord & 0x40000000;
  values.ivs.forEach((value, index) => { ivWord |= (value & 31) << (index * 5); });
  if (values.ability === 2) ivWord = (ivWord | 0x80000000) >>> 0;
  w32(blocks.M, 4, ivWord >>> 0);
  encryptPokemonBlocks(bytes, offset, blocks, personality);
  if (party) {
    bytes[offset + 84] = values.level;
    recalculatePartyStats(bytes, offset, values.species, values.level, values.ivs, values.evs, personality % 25);
  }
}

function initializePokemon(mon, species) {
  const { bytes, offset } = mon.record;
  const size = mon.kind === "party" ? PARTY_RECORD_SIZE : BOX_RECORD_SIZE;
  bytes.fill(0, offset, offset + size);
  const otId = u32(state.layout.sb2, 0x0A);
  const personality = (crypto.getRandomValues(new Uint32Array(1))[0] || 1) >>> 0;
  w32(bytes, offset, personality);
  w32(bytes, offset + 4, otId);
  encodeText(bytes, offset + 8, 10, speciesName(species).slice(0, 10));
  bytes[offset + 18] = 2;
  bytes[offset + 19] = 2;
  encodeText(bytes, offset + 20, 7, decodeText(state.layout.sb2, 0, 8).slice(0, 7));
  const blocks = { G: new Uint8Array(12), A: new Uint8Array(12), E: new Uint8Array(12), M: new Uint8Array(12) };
  w16(blocks.G, 0, species);
  blocks.G[9] = 70;
  blocks.G[10] = 4;
  encryptPokemonBlocks(bytes, offset, blocks, personality);
  if (mon.kind === "party") bytes[offset + 84] = 5;
}

function recalculatePartyStats(bytes, offset, speciesId, level, ivs, evs, nature) {
  const calculated = calculatePokemonStats(speciesId, level, ivs, evs, nature);
  if (!calculated) return;
  const hp = calculated[0];
  const oldHp = u16(bytes, offset + 86), oldMax = u16(bytes, offset + 88);
  w16(bytes, offset + 86, oldMax ? Math.max(1, Math.min(hp, Math.round(oldHp * hp / oldMax))) : hp);
  [88, 90, 92, 94, 96, 98].forEach((fieldOffset, index) => w16(bytes, offset + fieldOffset, calculated[index]));
}

function calculatePokemonStats(speciesId, level, ivs, evs, nature) {
  const base = state.game.species[speciesId]?.stats;
  if (!base) return null;
  const raw = base.map((stat, index) => Math.floor(((2 * stat + ivs[index] + Math.floor(evs[index] / 4)) * level) / 100));
  const hp = base[0] === 1 ? 1 : raw[0] + level + 10;
  const up = Math.floor(nature / 5), down = nature % 5;
  const calculated = [hp];
  for (let i = 1; i < 6; i++) {
    let value = raw[i] + 5;
    const natureIndex = i - 1;
    if (up !== down) {
      if (natureIndex === up) value = Math.floor(value * 1.1);
      if (natureIndex === down) value = Math.floor(value * 0.9);
    }
    calculated.push(value);
  }
  return calculated;
}

function compactParty() {
  const occupied = [];
  for (let i = 0; i < 6; i++) {
    const record = getPartyRecord(i);
    if (readPokemon("party", i).species) occupied.push(record.bytes.slice(record.offset, record.offset + PARTY_RECORD_SIZE));
  }
  for (let i = 0; i < 6; i++) {
    const record = getPartyRecord(i);
    record.bytes.fill(0, record.offset, record.offset + PARTY_RECORD_SIZE);
    if (occupied[i]) record.bytes.set(occupied[i], record.offset);
  }
  state.layout.sb1[0x34] = occupied.length;
}

function boxName(box) {
  if (box < 14) return decodeText(state.layout.storage, 0x8344 + box * 9, 9) || `Box ${box + 1}`;
  return `Box ${box + 1}`;
}

function refreshBoxSelectors() {
  if (!state.layout) return;
  const mainValue = els.boxSelect.value || "0";
  const moveValue = els.moveBoxSelect.value || "1";
  const counts = Array(BOX_COUNT).fill(0);
  if (state.searchQuery.trim()) {
    allBoxMatches().forEach(mon => { counts[mon.box]++; });
  }
  const makeOptions = () => Array.from({ length: BOX_COUNT }, (_, box) => {
    const suffix = state.searchQuery.trim() ? ` · ${counts[box]} match${counts[box] === 1 ? "" : "es"}` : "";
    return new Option(`${box + 1} · ${boxName(box)}${suffix}`, box);
  });
  els.boxSelect.replaceChildren(...makeOptions());
  els.moveBoxSelect.replaceChildren(...makeOptions());
  els.boxSelect.value = mainValue;
  els.moveBoxSelect.value = moveValue;
}

function openRenameBox(box) {
  state.renameBoxIndex = box;
  els.boxNameField.value = boxName(box);
  els.renameDialog.showModal();
  els.boxNameField.focus();
  els.boxNameField.select();
}

function renameBox(box, name) {
  const trimmed = name.trim();
  if (!trimmed) {
    els.boxNameField.setCustomValidity("Enter a box name."); els.boxNameField.reportValidity(); return false;
  }
  if ([...trimmed].some(character => !encodeMap.has(character))) {
    els.boxNameField.setCustomValidity("Use letters, numbers, spaces, or standard Pokémon punctuation."); els.boxNameField.reportValidity(); return false;
  }
  if (trimmed === boxName(box)) return false;
  encodeText(state.layout.storage, 0x8344 + box * 9, 9, trimmed.slice(0, 8));
  markChanged();
  refreshBoxSelectors(); renderAllSlots();
  setActionStatus(`Box ${box + 1} renamed to ${boxName(box)}.`);
  return true;
}

function renderParty() {
  els.party.replaceChildren();
  for (let index = 0; index < 6; index++) {
    const mon = readPokemon("party", index);
    const button = document.createElement("button");
    button.className = `mon-card${mon.species ? "" : " empty"}${state.selection.has(pokemonKey(mon)) ? " selected" : ""}`;
    button.innerHTML = pokemonCardMarkup(mon, `Party ${index + 1}`);
    setupPokemonCard(button, mon);
    els.party.append(button);
  }
}

function renderBox() {
  const box = Number(els.boxSelect.value || 0);
  els.box.replaceChildren();
  for (let index = 0; index < BOX_CAPACITY; index++) {
    const mon = readPokemon("box", index, box);
    const button = document.createElement("button");
    const searchClass = state.searchQuery ? (mon.species && pokemonMatchesSearch(mon, state.searchQuery) ? " search-match" : " search-muted") : "";
    button.className = `box-slot${mon.species ? "" : " empty"}${state.selection.has(pokemonKey(mon)) ? " selected" : ""}${searchClass}`;
    button.innerHTML = pokemonCardMarkup(mon, String(index + 1), state.searchQuery);
    setupPokemonCard(button, mon);
    els.box.append(button);
  }
}

function renderMoveBox() {
  if (!state.layout || els.movePanel.hidden) return;
  const box = Number(els.moveBoxSelect.value || 0);
  els.moveBox.replaceChildren();
  for (let index = 0; index < BOX_CAPACITY; index++) {
    const mon = readPokemon("box", index, box);
    const button = document.createElement("button");
    button.className = `box-slot${mon.species ? "" : " empty"}${state.selection.has(pokemonKey(mon)) ? " selected" : ""}`;
    button.innerHTML = pokemonCardMarkup(mon, String(index + 1));
    setupPokemonCard(button, mon);
    els.moveBox.append(button);
  }
}

function renderAllSlots() { renderParty(); renderBox(); renderMoveBox(); renderSearchResults(); }

function speciesSpriteSource(id) { return state.game.species[id]?.sprite || "missing.svg"; }

function isSameSpriteColor(r1, g1, b1, r2, g2, b2, tolerance = 1) {
  return Math.abs(r1 - r2) <= tolerance && Math.abs(g1 - g2) <= tolerance && Math.abs(b1 - b2) <= tolerance;
}

function createSpeciesSpriteData(id) {
  const source = speciesSpriteSource(id);
  if (source === "missing.svg" || source === "blank.svg" || source.endsWith("/missing.svg") || source.endsWith("/blank.svg")) {
    return Promise.resolve(source);
  }
  if (spriteDataCache.has(id)) return Promise.resolve(spriteDataCache.get(id));
  if (spriteDataPromises.has(id)) return spriteDataPromises.get(id);
  const promise = new Promise((resolve, reject) => {
    const sprite = new Image();
    sprite.crossOrigin = "anonymous";
    sprite.onload = () => {
      try {
        // This mirrors the Dex image-data pipeline: render the 64×64 source,
        // remove pixels matching its top-left background colour, and use the
        // resulting canvas data URL everywhere that species is displayed.
        const canvas = document.createElement("canvas");
        canvas.width = 64; canvas.height = 64;
        const context = canvas.getContext("2d");
        context.clearRect(0, 0, canvas.width, canvas.height);
        context.drawImage(sprite, 0, 0);
        const imageData = context.getImageData(0, 0, canvas.width, canvas.height);
        const [backgroundR, backgroundG, backgroundB] = imageData.data;
        for (let pixel = 0; pixel < imageData.data.length; pixel += 4) {
          if (isSameSpriteColor(imageData.data[pixel], imageData.data[pixel + 1], imageData.data[pixel + 2], backgroundR, backgroundG, backgroundB, 1)) {
            imageData.data[pixel + 3] = 0;
          }
        }
        context.putImageData(imageData, 0, 0);
        const dataUrl = canvas.toDataURL("image/png");
        spriteDataCache.set(id, dataUrl);
        document.querySelectorAll(`.mon-sprite[data-species-id="${id}"]`).forEach(image => { image.src = dataUrl; });
        resolve(dataUrl);
      } catch (error) { reject(error); }
    };
    sprite.onerror = () => reject(new Error(`Could not load the sprite for species ${id}.`));
    sprite.src = source;
  }).finally(() => spriteDataPromises.delete(id));
  spriteDataPromises.set(id, promise);
  return promise;
}

function hydratePokemonSprite(container, speciesId) {
  if (!speciesId) return;
  const image = container.querySelector(".mon-sprite");
  if (!image) return;
  image.addEventListener("error", () => { image.src = "missing.svg"; }, { once: true });
  createSpeciesSpriteData(speciesId).then(dataUrl => {
    if (image.isConnected && image.dataset.speciesId === String(speciesId)) image.src = dataUrl;
  }).catch(() => { if (image.isConnected) image.src = "missing.svg"; });
}

function highlightSearch(value, query) {
  const text = String(value);
  const needle = query.trim();
  if (!needle) return escapeHtml(text);
  const index = text.toLocaleLowerCase().indexOf(needle.toLocaleLowerCase());
  if (index < 0) return escapeHtml(text);
  return `${escapeHtml(text.slice(0, index))}<mark>${escapeHtml(text.slice(index, index + needle.length))}</mark>${escapeHtml(text.slice(index + needle.length))}`;
}

function pokemonCardMarkup(mon, slotLabel, highlightQuery = "", reason = "") {
  if (!mon.species) return `<span class="slot">${escapeHtml(slotLabel)}</span><strong>Empty slot</strong><span class="details">Empty</span>`;
  const name = mon.nickname || speciesName(mon.species);
  const nameClass = mon.nickname ? "mon-name nickname" : "mon-name";
  const details = mon.nickname ? `${speciesName(mon.species)} · Lv. ${mon.level}` : `Lv. ${mon.level}`;
  const sprite = spriteDataCache.get(mon.species) || speciesSpriteSource(mon.species);
  return `<span class="slot">${escapeHtml(slotLabel)}</span><img class="mon-sprite" data-species-id="${mon.species}" src="${escapeHtml(sprite)}" alt="" loading="lazy"><strong class="${nameClass}">${highlightSearch(name, highlightQuery)}</strong><span class="details">${highlightSearch(details, highlightQuery)}</span>${reason ? `<span class="search-reason">${escapeHtml(reason)}</span>` : ""}`;
}

function pokemonSearchFields(mon) {
  const species = state.game.species[mon.species];
  const item = state.itemById.get(mon.item)?.name || "";
  const moves = mon.moves.filter(Boolean).map(moveName);
  const abilities = species?.abilities || [];
  return { species: speciesName(mon.species), nickname: mon.nickname, item, moves, abilities };
}

function pokemonMatchesSearch(mon, query) {
  if (!mon.species) return false;
  const fields = pokemonSearchFields(mon);
  const haystack = [fields.species, fields.nickname, fields.item, ...fields.moves, ...fields.abilities, `level ${mon.level}`, `lv ${mon.level}`].join(" ").toLocaleLowerCase();
  return query.trim().toLocaleLowerCase().split(/\s+/).every(term => haystack.includes(term));
}

function pokemonSearchReason(mon, query) {
  const term = query.trim().toLocaleLowerCase();
  if (!term) return "";
  const fields = pokemonSearchFields(mon);
  if (fields.species.toLocaleLowerCase().includes(term)) return "Species match";
  if (fields.nickname.toLocaleLowerCase().includes(term)) return "Nickname match";
  const move = fields.moves.find(name => name.toLocaleLowerCase().includes(term));
  if (move) return `Move: ${move}`;
  if (fields.item.toLocaleLowerCase().includes(term)) return `Item: ${fields.item}`;
  const ability = fields.abilities.find(name => name.toLocaleLowerCase().includes(term));
  if (ability) return `Ability: ${ability}`;
  return "Matched multiple terms";
}

function allBoxMatches(query = state.searchQuery) {
  const matches = [];
  if (!query.trim()) return matches;
  for (let box = 0; box < BOX_COUNT; box++) {
    for (let index = 0; index < BOX_CAPACITY; index++) {
      const mon = readPokemon("box", index, box);
      if (pokemonMatchesSearch(mon, query)) matches.push(mon);
    }
  }
  return matches;
}

function renderSearchResults() {
  if (!state.layout) return;
  const query = state.searchQuery.trim();
  els.clearBoxSearch.disabled = !query;
  els.searchPanel.hidden = !query;
  els.searchResults.replaceChildren();
  if (!query) return;
  const matches = allBoxMatches(query);
  els.searchCount.textContent = `${matches.length} found`;
  for (const mon of matches) {
    const button = document.createElement("button");
    button.className = `box-slot search-match${state.selection.has(pokemonKey(mon)) ? " selected" : ""}`;
    button.innerHTML = pokemonCardMarkup(mon, `${boxName(mon.box)} · ${mon.index + 1}`, query, pokemonSearchReason(mon, query));
    setupPokemonCard(button, mon);
    els.searchResults.append(button);
  }
  if (!matches.length) {
    const empty = document.createElement("p");
    empty.className = "field-note"; empty.textContent = "No Pokémon in any PC box match this search.";
    els.searchResults.append(empty);
  }
}

function pokemonKey(mon) { return mon.kind === "party" ? `party:${mon.index}` : `box:${mon.box}:${mon.index}`; }
function locationOf(mon) { return { kind: mon.kind, index: mon.index, box: mon.box || 0 }; }
function readLocation(location) { return readPokemon(location.kind, location.index, location.box || 0); }

function setupPokemonCard(button, mon) {
  const location = locationOf(mon);
  hydratePokemonSprite(button, mon.species);
  button.draggable = Boolean(mon.species);
  button.addEventListener("click", event => {
    state.lastLocation = location;
    if (button.dataset.longPressed === "true") { button.dataset.longPressed = "false"; return; }
    if (state.selectMode || event.ctrlKey || event.metaKey) {
      if (mon.species) toggleSelection(mon);
      else if (state.selection.size) moveLocationsToTarget([...state.selection.values()], location);
      return;
    }
    openEditor(mon);
  });
  button.addEventListener("contextmenu", event => {
    event.preventDefault(); state.lastLocation = location; showContextMenu(event.clientX, event.clientY, location);
  });
  let longPress;
  button.addEventListener("pointerdown", event => {
    if (event.pointerType === "mouse") return;
    longPress = setTimeout(() => {
      button.dataset.longPressed = "true";
      showContextMenu(event.clientX || 12, event.clientY || 12, location);
    }, 550);
  });
  ["pointerup", "pointercancel", "pointermove"].forEach(type => button.addEventListener(type, () => clearTimeout(longPress)));
  button.addEventListener("dragstart", event => {
    state.lastLocation = location;
    event.dataTransfer.effectAllowed = "move";
    event.dataTransfer.setData("text/plain", pokemonKey(mon));
    state.draggedLocations = state.selection.has(pokemonKey(mon)) && state.selection.size > 1
      ? [...state.selection.values()] : [location];
  });
  button.addEventListener("dragend", () => { state.draggedLocations = null; button.classList.remove("drop-target"); });
  button.addEventListener("dragover", event => { event.preventDefault(); button.classList.add("drop-target"); });
  button.addEventListener("dragleave", () => button.classList.remove("drop-target"));
  button.addEventListener("drop", event => {
    event.preventDefault(); button.classList.remove("drop-target");
    if (state.draggedLocations?.length > 1) moveLocationsToTarget(state.draggedLocations, location);
    else if (state.draggedLocations?.length) swapLocations(state.draggedLocations[0], location);
    state.draggedLocations = null;
  });
}

function escapeHtml(value) { const node = document.createElement("span"); node.textContent = value; return node.innerHTML; }

function recordForLocation(location) {
  return location.kind === "party" ? getPartyRecord(location.index) : getBoxRecord(location.box, location.index);
}

function snapshotLocation(location) {
  const mon = readLocation(location);
  if (!mon.species) return null;
  const { bytes, offset } = mon.record;
  return {
    core: bytes.slice(offset, offset + BOX_RECORD_SIZE),
    partyTail: mon.kind === "party" ? bytes.slice(offset + BOX_RECORD_SIZE, offset + PARTY_RECORD_SIZE) : null
  };
}

function clearLocation(location) {
  const record = recordForLocation(location);
  record.bytes.fill(0, record.offset, record.offset + (location.kind === "party" ? PARTY_RECORD_SIZE : BOX_RECORD_SIZE));
}

function writePayloadToLocation(payload, location) {
  if (!payload) return;
  const record = recordForLocation(location);
  clearLocation(location);
  record.bytes.set(payload.core, record.offset);
  if (location.kind !== "party") return;
  if (payload.partyTail) {
    record.bytes.set(payload.partyTail, record.offset + BOX_RECORD_SIZE);
    return;
  }
  const mon = readPokemon("party", location.index);
  const level = levelFromExperience(mon.species, mon.experience);
  record.bytes[record.offset + 84] = level;
  recalculatePartyStats(record.bytes, record.offset, mon.species, level, mon.ivs, mon.evs, mon.nature);
}

function refreshAfterSlotChange(message) {
  state.selection.clear();
  compactParty();
  markChanged();
  if (state.searchQuery.trim()) refreshBoxSelectors();
  renderAllSlots(); updateSelectionUi();
  setActionStatus(message);
}

function swapLocations(first, second) {
  if (pokemonKey(first) === pokemonKey(second)) return;
  const firstPayload = snapshotLocation(first), secondPayload = snapshotLocation(second);
  clearLocation(first); clearLocation(second);
  writePayloadToLocation(firstPayload, second);
  writePayloadToLocation(secondPayload, first);
  refreshAfterSlotChange("Pokémon moved.");
}

function toggleSelection(mon) {
  const key = pokemonKey(mon);
  if (state.selection.has(key)) state.selection.delete(key);
  else state.selection.set(key, locationOf(mon));
  renderAllSlots(); updateSelectionUi();
}

function updateSelectionUi() {
  const count = state.selection.size;
  els.selectionCount.textContent = `${count} selected`;
  els.exportSelected.disabled = count === 0;
}

function setActionStatus(message, error = false) {
  els.actionStatus.textContent = message;
  els.actionStatus.style.color = error ? "var(--danger)" : "";
}

function moveLocationsToTarget(sources, target) {
  if (!sources.length) return;
  const capacity = target.kind === "party" ? 6 : 30;
  if (target.index + sources.length > capacity) { setActionStatus("There is not enough room after that target slot.", true); return; }
  const targets = sources.map((_, offset) => ({ ...target, index: target.index + offset }));
  const sourceKeys = new Set(sources.map(pokemonKey));
  const occupiedOutsiders = targets.filter(target => readLocation(target).species && !sourceKeys.has(pokemonKey(target)));
  if (occupiedOutsiders.length) {
    if (sources.length === 1 && targets.length === 1) { swapLocations(sources[0], targets[0]); return; }
    setActionStatus("For multiple Pokémon, all target slots must be empty or part of the selection.", true); return;
  }
  const payloads = sources.map(snapshotLocation);
  sources.forEach(clearLocation);
  targets.forEach((target, index) => writePayloadToLocation(payloads[index], target));
  refreshAfterSlotChange(`${payloads.length} Pokémon moved.`);
}

function copyLocations(locations) {
  state.clipboard = locations.map(snapshotLocation).filter(Boolean);
  updateSelectionUi();
  setActionStatus(`${state.clipboard.length} Pokémon copied. Choose a destination and paste.`);
}

function pastePayloadsAt(targets) {
  if (!state.clipboard.length) return;
  if (!targets || targets.length !== state.clipboard.length) { setActionStatus("There is not enough room to paste there.", true); return; }
  const occupied = targets.some(target => readLocation(target).species);
  if (occupied && !window.confirm("Replace the occupied target slot(s)?")) return;
  targets.forEach((target, index) => writePayloadToLocation(state.clipboard[index], target));
  refreshAfterSlotChange(`${state.clipboard.length} Pokémon pasted.`);
}

function pasteAtLocation(location) {
  const capacity = location.kind === "party" ? 6 : 30;
  if (location.index + state.clipboard.length > capacity) { setActionStatus("There is not enough room after that slot.", true); return; }
  const targets = state.clipboard.map((_, offset) => ({ ...location, index: location.index + offset }));
  pastePayloadsAt(targets);
}

function removeLocations(locations) {
  const occupied = locations.filter(location => readLocation(location).species);
  if (!occupied.length || !window.confirm(`Remove ${occupied.length} Pokémon?`)) return;
  occupied.forEach(clearLocation);
  refreshAfterSlotChange(`${occupied.length} Pokémon removed.`);
}

function bytesToBase64(bytes) {
  let binary = "";
  bytes.forEach(value => { binary += String.fromCharCode(value); });
  return btoa(binary);
}

function base64ToBytes(value) {
  const binary = atob(value);
  return Uint8Array.from(binary, character => character.charCodeAt(0));
}

function downloadBlob(blob, fileName) {
  const link = document.createElement("a");
  link.href = URL.createObjectURL(blob);
  link.download = fileName;
  link.click();
  setTimeout(() => URL.revokeObjectURL(link.href), 1000);
}

function safeFileName(value) {
  return String(value).replace(/[^a-z0-9._-]+/gi, "-").replace(/^-+|-+$/g, "") || "pokemon";
}

function exportPokemon(locations) {
  const occupied = locations.map(readLocation).filter(mon => mon.species);
  if (!occupied.length) return;
  const data = {
    format: POKEMON_EXPORT_FORMAT,
    version: POKEMON_EXPORT_VERSION,
    game: "Pokemon Adventure Red Chapter",
    records: occupied.map(mon => ({
      species: mon.species,
      name: mon.nickname || speciesName(mon.species),
      data: bytesToBase64(snapshotLocation(mon).core)
    }))
  };
  const name = occupied.length === 1 ? safeFileName(occupied[0].nickname || speciesName(occupied[0].species)) : `${occupied.length}-pokemon`;
  downloadBlob(new Blob([JSON.stringify(data, null, 2)], { type: "application/json" }), `${name}.arpokemon`);
  setActionStatus(`${occupied.length} Pokémon exported.`);
}

function validateImportedRecord(record, index) {
  if (!record || typeof record.data !== "string") throw new Error(`Record ${index + 1} has no Pokémon data.`);
  let core;
  try { core = base64ToBytes(record.data); }
  catch { throw new Error(`Record ${index + 1} contains invalid encoded data.`); }
  if (core.length !== BOX_RECORD_SIZE) throw new Error(`Record ${index + 1} is not an 80-byte Pokémon record.`);
  const blocks = decryptPokemonBlocks(core, 0);
  const species = u16(blocks.G, 0);
  if (!species || !state.game.species[species] || state.game.species[species].unused) throw new Error(`Record ${index + 1} has an unknown Pokémon ID (${species}).`);
  if (pokemonChecksum(blocks) !== u16(core, 28)) throw new Error(`Record ${index + 1} has a corrupt Pokémon checksum.`);
  return { core, partyTail: null };
}

function firstFreePcLocations(count) {
  const locations = [];
  for (let box = 0; box < BOX_COUNT && locations.length < count; box++) {
    for (let index = 0; index < BOX_CAPACITY && locations.length < count; index++) {
      const location = { kind: "box", box, index };
      if (!readLocation(location).species) locations.push(location);
    }
  }
  return locations;
}

async function importPokemonFile(file, target = null) {
  let parsed;
  try { parsed = JSON.parse(await file.text()); }
  catch { throw new Error("This is not a valid Pokémon export file."); }
  if (parsed?.format !== POKEMON_EXPORT_FORMAT || parsed?.version !== POKEMON_EXPORT_VERSION || !Array.isArray(parsed.records) || !parsed.records.length) {
    throw new Error("This file is not a supported Adventure Red Pokémon export.");
  }
  const payloads = parsed.records.map(validateImportedRecord);
  let targets;
  if (target) {
    const capacity = target.kind === "party" ? 6 : BOX_CAPACITY;
    if (target.index + payloads.length > capacity) throw new Error("The imported Pokémon do not fit after that slot.");
    targets = payloads.map((_, offset) => ({ ...target, index: target.index + offset }));
    if (targets.some(location => readLocation(location).species) && !window.confirm("Replace the occupied target slot(s) with the imported Pokémon?")) return;
  } else {
    targets = firstFreePcLocations(payloads.length);
    if (targets.length !== payloads.length) throw new Error(`Only ${targets.length} empty PC slots are available for ${payloads.length} imported Pokémon.`);
  }
  targets.forEach((location, index) => writePayloadToLocation(payloads[index], location));
  refreshAfterSlotChange(`${payloads.length} Pokémon imported${target ? "" : " into the first available PC slots"}.`);
  if (!target && targets.length) {
    els.boxSelect.value = String(targets[0].box);
    document.querySelector('.tab[data-view="boxes"]').click();
    renderBox();
  }
}

function choosePokemonImport(target = null) {
  state.importTarget = target;
  state.importTargetLocked = Boolean(target);
  els.importInput.value = "";
  els.importInput.click();
}

function showContextMenu(x, y, location) {
  state.context = location;
  const mon = readLocation(location);
  els.contextMenu.querySelector('[data-action="edit"]').disabled = !mon.species;
  els.contextMenu.querySelector('[data-action="copy"]').disabled = !mon.species;
  els.contextMenu.querySelector('[data-action="export"]').disabled = !mon.species;
  els.contextMenu.querySelector('[data-action="paste"]').disabled = !state.clipboard.length;
  els.contextMenu.querySelector('[data-action="move"]').disabled = !state.selection.size;
  els.contextMenu.querySelector('[data-action="remove"]').disabled = !mon.species;
  els.contextMenu.hidden = false;
  const width = 170, height = els.contextMenu.offsetHeight;
  els.contextMenu.style.left = `${Math.max(6, Math.min(x, window.innerWidth - width - 6))}px`;
  els.contextMenu.style.top = `${Math.max(6, Math.min(y, window.innerHeight - height - 6))}px`;
}

function hideContextMenu() { els.contextMenu.hidden = true; state.context = null; }

function snapshotLayout() {
  return { sb1: state.layout.sb1.slice(), sb2: state.layout.sb2.slice(), storage: state.layout.storage.slice() };
}

function restoreLayout(snapshot) {
  state.layout.sb1.set(snapshot.sb1);
  state.layout.sb2.set(snapshot.sb2);
  state.layout.storage.set(snapshot.storage);
}

function updateHistoryButtons() {
  const changed = Math.max(0, state.history.length - 1);
  state.changes = changed;
  els.changes.textContent = String(changed);
  els.undo.disabled = changed === 0;
  els.reset.disabled = changed === 0;
}

function undoLastChange() {
  if (state.history.length <= 1) return;
  state.history.pop();
  restoreLayout(state.history[state.history.length - 1]);
  state.selection.clear();
  refreshBoxSelectors(); renderAllSlots(); updateSelectionUi(); updateHistoryButtons();
  setActionStatus("Last change undone.");
}

function resetChanges() {
  if (state.history.length <= 1 || !window.confirm("Undo all changes made since this save was opened?")) return;
  restoreLayout(state.history[0]);
  state.history = [snapshotLayout()];
  state.selection.clear();
  refreshBoxSelectors(); renderAllSlots(); updateSelectionUi(); updateHistoryButtons();
  setActionStatus("All changes reset.");
}

function fillSelect(select, entries, emptyLabel = null) {
  const fragment = document.createDocumentFragment();
  if (emptyLabel !== null) fragment.append(new Option(emptyLabel, "0"));
  entries.forEach(([value, label]) => fragment.append(new Option(label, value)));
  select.replaceChildren(fragment);
}

function updateAbilityOptions(selected = 0) {
  const species = state.game.species[Number(els.species.value)];
  const abilities = species?.abilities || [];
  const options = [];
  const first = abilities[0];
  const second = abilities[1];
  if (first) options.push([0, `Ability 1: ${first}`]);
  // Adventure Red stores the displayed second ability in the Gen III
  // hidden-ability flag. This is the same selector that the working Lua
  // script exposes as ABILITY_SLOT = 3.
  if (second) options.push([2, `Ability 2: ${second}`]);
  if (!options.length) options.push([0, "Default"]);
  fillSelect(els.ability, options);
  els.ability.value = options.some(option => option[0] === selected) ? String(selected) : String(options[0][0]);
}

function legalMovesForSpecies(speciesId) {
  return new Set(state.game.species[speciesId]?.legalMoves || []);
}

function displayMoveValue(value) {
  if (value === undefined || value === null || value === "") return "—";
  return String(value);
}

function renderMoveInfo(index) {
  const container = els.moveInfos[index];
  const moveId = Number(els.moves[index].value || 0);
  const move = state.game.moves[moveId];
  container.replaceChildren();
  if (!move) {
    container.textContent = "No move selected";
    return;
  }
  const legal = legalMovesForSpecies(Number(els.species.value)).has(moveId);
  const fields = [
    ["ID", move.id],
    ["Type", move.type],
    ...(move.category ? [["Kind", move.category]] : []),
    ["Power", move.power === 0 ? "—" : move.power],
    ["Accuracy", move.accuracy === 0 ? "—" : move.accuracy],
    ["PP", move.pp]
  ];
  fields.forEach(([label, value]) => {
    const item = document.createElement("span");
    item.className = "move-info-item";
    const strong = document.createElement("strong");
    strong.textContent = `${label}: `;
    item.append(strong, displayMoveValue(value));
    container.append(item);
  });
  if (!legal) {
    const warning = document.createElement("span");
    warning.className = "move-info-item illegal";
    warning.textContent = "⚠ Illegal for this species";
    container.append(warning);
  }
}

function renderAllMoveInfo() {
  els.moves.forEach((_, index) => renderMoveInfo(index));
}

function populateMoveFields(selectedMoves = els.moves.map(field => Number(field.value))) {
  const legal = legalMovesForSpecies(Number(els.species.value));
  const allMoves = Object.values(state.game.moves).filter(Boolean).sort((a, b) => a.name.localeCompare(b.name));
  els.moves.forEach((field, fieldIndex) => {
    const selected = Number(selectedMoves[fieldIndex] || 0);
    const fragment = document.createDocumentFragment();
    fragment.append(new Option("—", "0"));
    for (const move of allMoves) {
      const isLegal = legal.has(move.id);
      if (!state.allowIllegalMoves && !isLegal && move.id !== selected) continue;
      const suffix = isLegal ? "" : " · ⚠ Illegal";
      const option = new Option(`${move.name}${suffix}`, move.id);
      if (!isLegal) option.className = "illegal";
      fragment.append(option);
    }
    field.replaceChildren(fragment);
    field.value = String(selected);
  });
  renderAllMoveInfo();
}

function readStatFields(container, maximum) {
  const values = Array(6).fill(0);
  container.querySelectorAll("input").forEach(field => { values[Number(field.dataset.index)] = clamp(field.value, 0, maximum); });
  return values;
}

function updateCalculatedStats() {
  const stats = calculatePokemonStats(
    Number(els.species.value),
    clamp(els.level.value, 1, 100),
    readStatFields(els.ivs, 31),
    readStatFields(els.evs, 255),
    Number(els.nature.value)
  );
  els.calculatedStats.replaceChildren();
  if (!stats) return;
  DISPLAY_STAT_INDICES.forEach(index => {
    const item = document.createElement("div");
    item.className = "calculated-stat";
    const label = document.createElement("span");
    label.textContent = STATS[index];
    const value = document.createElement("strong");
    value.textContent = stats[index];
    item.append(label, value);
    els.calculatedStats.append(item);
  });
}

function openEditor(mon) {
  state.current = mon;
  els.editorLocation.textContent = mon.kind === "party" ? `Party slot ${mon.index + 1}` : `${boxName(mon.box)} · Slot ${mon.index + 1}`;
  els.editorTitle.textContent = mon.species ? (mon.nickname || speciesName(mon.species)) : "Add Pokémon";
  els.species.value = String(mon.species || 1);
  els.nickname.value = mon.nickname || "";
  els.level.value = mon.level || 5;
  els.nature.value = String(mon.nature || 0);
  els.item.value = String(mon.item || 0);
  els.friendship.value = mon.friendship ?? 70;
  populateMoveFields(mon.moves);
  els.ivs.querySelectorAll("input").forEach(field => { field.value = mon.ivs[Number(field.dataset.index)] ?? 10; });
  els.evs.querySelectorAll("input").forEach(field => { field.value = mon.evs[Number(field.dataset.index)] ?? 0; });
  if (mon.evs.reduce((sum, value) => sum + value, 0) > 510) state.allowIllegalEvs = true;
  els.illegalMoves.setAttribute("aria-pressed", String(state.allowIllegalMoves));
  els.illegalEvs.setAttribute("aria-pressed", String(state.allowIllegalEvs));
  els.illegalMoves.textContent = state.allowIllegalMoves ? "Use legal moves only" : "Allow illegal moves";
  els.illegalEvs.textContent = state.allowIllegalEvs ? "Enforce 510 total EVs" : "Allow more than 510 total EVs";
  updateAbilityOptions(mon.ability);
  updateHiddenPower();
  updateCalculatedStats();
  els.clearPokemon.disabled = !mon.species;
  els.formError.textContent = "";
  els.dialog.showModal();
}

function applyEditor() {
  const evs = readStatFields(els.evs, 255);
  if (!state.allowIllegalEvs && evs.reduce((sum, value) => sum + value, 0) > 510) { els.formError.textContent = "Combined EVs cannot exceed 510."; return false; }
  const values = {
    species: Number(els.species.value), nickname: els.nickname.value, level: clamp(els.level.value, 1, 100),
    nature: Number(els.nature.value), ability: Number(els.ability.value), item: Number(els.item.value),
    friendship: clamp(els.friendship.value, 0, 255), moves: els.moves.map(field => Number(field.value)),
    ivs: readStatFields(els.ivs, 31), evs
  };
  writePokemon(state.current, values);
  compactParty();
  markChanged();
  if (state.searchQuery.trim()) refreshBoxSelectors();
  renderAllSlots(); updateSelectionUi();
  return true;
}

function updateHiddenPower() {
  const ivs = readStatFields(els.ivs, 31);
  const bits = ivs.reduce((sum, value, index) => sum + (value & 1) * (2 ** index), 0);
  const types = ["Fighting", "Flying", "Poison", "Ground", "Rock", "Bug", "Ghost", "Steel", "Fire", "Water", "Grass", "Electric", "Psychic", "Ice", "Dragon", "Dark"];
  els.hiddenPower.textContent = `Hidden Power: ${types[Math.floor(bits * 15 / 63)]}`;
}

function clampNumericField(field, minimum, maximum) {
  if (field.value === "") return;
  field.value = String(clamp(field.value, minimum, maximum));
}

function enforceEvLimit(changedField) {
  clampNumericField(changedField, 0, 255);
  if (state.allowIllegalEvs || changedField.value === "") return;
  const fields = [...els.evs.querySelectorAll("input")];
  const others = fields.reduce((sum, field) => field === changedField ? sum : sum + clamp(field.value, 0, 255), 0);
  changedField.value = String(Math.min(clamp(changedField.value, 0, 255), Math.max(0, 510 - others)));
}

function markChanged() {
  state.history.push(snapshotLayout());
  updateHistoryButtons();
}

async function loadGameData() {
  const game = await fetch("game-data.json?v=20261008-2").then(response => response.json());
  state.game = game;
  state.itemById = new Map(game.items.map(item => [item.id, item]));
  fillSelect(els.species, Object.values(game.species).filter(entry => entry && !entry.unused).map(entry => [entry.id, `${entry.name} · #${entry.id}`]));
  const usableItems = game.items.filter(item => item.name.replace(/[?\s-]/g, "").length > 0);
  fillSelect(els.item, usableItems.sort((a, b) => a.name.localeCompare(b.name)).map(item => [item.id, `${item.name} · #${item.id}`]), "None");
  const natureStats = ["Atk", "Def", "Speed", "Sp. Atk", "Sp. Def"];
  fillSelect(els.nature, NATURES.map((name, index) => {
    const up = Math.floor(index / 5), down = index % 5;
    const effect = up === down ? "neutral" : `${natureStats[up]} ↑, ${natureStats[down]} ↓`;
    return [index, `${name} (${effect})`];
  }));
  DISPLAY_STAT_INDICES.forEach(index => {
    const name = STATS[index];
    const ivLabel = document.createElement("label"); ivLabel.textContent = name; ivLabel.innerHTML += `<input type="number" min="0" max="31" data-index="${index}">`; els.ivs.append(ivLabel);
    const evLabel = document.createElement("label"); evLabel.textContent = name; evLabel.innerHTML += `<input type="number" min="0" max="255" data-index="${index}">`; els.evs.append(evLabel);
  });
}

async function loadSave(file) {
  els.error.textContent = "";
  try {
    await gameDataPromise;
    const bytes = new Uint8Array(await file.arrayBuffer());
    const layout = parseSave(bytes);
    state.bytes = bytes; state.layout = layout; state.fileName = file.name; state.changes = 0;
    state.selection.clear(); state.clipboard = []; state.current = null; state.lastLocation = null;
    state.searchQuery = ""; els.boxSearch.value = "";
    state.history = [snapshotLayout()];
    els.fileName.textContent = file.name;
    els.trainer.textContent = decodeText(layout.sb2, 0, 8) || "Unnamed";
    els.slot.textContent = `${layout.active.firstSector === 0 ? "A" : "B"} · counter ${layout.active.counter}`;
    els.changes.textContent = "0";
    refreshBoxSelectors();
    els.moveBoxSelect.value = els.boxSelect.value === "0" ? "1" : "0";
    els.loader.hidden = true; els.workspace.hidden = false; els.download.disabled = false;
    renderAllSlots(); updateSelectionUi(); updateHistoryButtons(); setActionStatus("");
  } catch (error) {
    console.error(error); els.error.textContent = error.message || "Could not read this save.";
  }
}

function pokemonLocationLabel(mon) {
  return mon.kind === "party" ? `Party slot ${mon.index + 1}` : `${boxName(mon.box)} slot ${mon.index + 1}`;
}

function runSaveReport() {
  const errors = [], warnings = [];
  const occupied = [];
  for (let index = 0; index < 6; index++) {
    const mon = readPokemon("party", index);
    if (mon.species) occupied.push(mon);
  }
  for (let box = 0; box < BOX_COUNT; box++) {
    for (let index = 0; index < BOX_CAPACITY; index++) {
      const mon = readPokemon("box", index, box);
      if (mon.species) occupied.push(mon);
    }
  }
  const partyMons = occupied.filter(mon => mon.kind === "party");
  if (state.layout.sb1[0x34] !== partyMons.length) errors.push(`Party count says ${state.layout.sb1[0x34]}, but ${partyMons.length} occupied party slots were found.`);
  const firstEmpty = Array.from({ length: 6 }, (_, index) => readPokemon("party", index)).findIndex(mon => !mon.species);
  if (firstEmpty >= 0 && Array.from({ length: 6 - firstEmpty - 1 }, (_, offset) => readPokemon("party", firstEmpty + offset + 1)).some(mon => mon.species)) {
    warnings.push("The party contains a gap; it will be compacted when downloaded.");
  }
  for (const mon of occupied) {
    const location = pokemonLocationLabel(mon);
    const species = state.game.species[mon.species];
    if (!mon.checksumValid) errors.push(`${location}: the Pokémon record checksum is corrupt.`);
    if (!species || species.unused) {
      errors.push(`${location}: unknown or unavailable species ID ${mon.species}.`);
      continue;
    }
    if (mon.kind === "party" && (mon.level < 1 || mon.level > 100)) errors.push(`${location} (${species.name}): level ${mon.level} is outside 1–100.`);
    if (mon.item && !state.itemById.has(mon.item)) warnings.push(`${location} (${species.name}): held item ID ${mon.item} is unknown.`);
    const legalMoves = legalMovesForSpecies(mon.species);
    for (const move of mon.moves.filter(Boolean)) {
      if (!state.game.moves[move]) errors.push(`${location} (${species.name}): move ID ${move} is unknown.`);
      else if (!legalMoves.has(move)) warnings.push(`${location} (${species.name}): ${moveName(move)} is not in this species' legal move pool.`);
    }
    const evTotal = mon.evs.reduce((sum, value) => sum + value, 0);
    if (evTotal > 510) warnings.push(`${location} (${species.name}): total EVs are ${evTotal}, above the legal limit of 510.`);
    if (mon.ability === 2 && !species.abilities?.[1]) warnings.push(`${location} (${species.name}): Ability 2 is selected, but no second ability is defined.`);
  }
  return { errors, warnings, checked: occupied.length };
}

function renderSaveReport(report) {
  els.reportSummary.innerHTML = `
    <div class="report-stat"><span>Pokémon checked</span><strong>${report.checked}</strong></div>
    <div class="report-stat errors"><span>Corruption errors</span><strong>${report.errors.length}</strong></div>
    <div class="report-stat warnings"><span>Legality warnings</span><strong>${report.warnings.length}</strong></div>`;
  els.reportDetails.replaceChildren();
  const addSection = (title, entries, className) => {
    if (!entries.length) return;
    const section = document.createElement("section"); section.className = `report-section ${className}`;
    const heading = document.createElement("h3"); heading.textContent = title; section.append(heading);
    const list = document.createElement("ul");
    entries.forEach(message => { const item = document.createElement("li"); item.textContent = message; list.append(item); });
    section.append(list); els.reportDetails.append(section);
  };
  addSection("Corruption / structural errors", report.errors, "errors");
  addSection("Legality warnings", report.warnings, "warnings");
  if (!report.errors.length && !report.warnings.length) {
    const okay = document.createElement("div"); okay.className = "report-ok";
    okay.textContent = "No corruption or legality problems were found. The save is ready to download.";
    els.reportDetails.append(okay);
  }
  els.confirmDownload.textContent = report.errors.length || report.warnings.length ? "Download anyway" : "Download save";
}

function downloadSave() {
  renderSaveReport(runSaveReport());
  els.reportDialog.showModal();
}

function performDownload() {
  const output = serializeSave();
  downloadBlob(new Blob([output], { type: "application/octet-stream" }), state.fileName.replace(/(\.[^.]+)?$/, "-edited$1") || "adventure-red-edited.sav");
  els.reportDialog.close();
}

document.querySelectorAll(".tab").forEach(button => button.addEventListener("click", () => {
  document.querySelectorAll(".tab").forEach(tab => tab.classList.toggle("active", tab === button));
  $("#partyView").hidden = button.dataset.view !== "party";
  $("#boxesView").hidden = button.dataset.view !== "boxes";
}));
els.input.addEventListener("change", event => { if (event.target.files[0]) loadSave(event.target.files[0]); });
els.boxSelect.addEventListener("change", renderBox);
els.boxSearch.addEventListener("input", () => {
  state.searchQuery = els.boxSearch.value;
  refreshBoxSelectors(); renderBox(); renderSearchResults();
});
els.clearBoxSearch.addEventListener("click", () => {
  els.boxSearch.value = ""; state.searchQuery = "";
  refreshBoxSelectors(); renderBox(); renderSearchResults(); els.boxSearch.focus();
});
$("#renameBoxButton").addEventListener("click", () => openRenameBox(Number(els.boxSelect.value || 0)));
$("#renameMoveBoxButton").addEventListener("click", () => openRenameBox(Number(els.moveBoxSelect.value || 0)));
els.boxNameField.addEventListener("input", () => els.boxNameField.setCustomValidity(""));
els.renameForm.addEventListener("submit", event => {
  event.preventDefault();
  if (els.boxNameField.value.trim() === boxName(state.renameBoxIndex) || renameBox(state.renameBoxIndex, els.boxNameField.value)) els.renameDialog.close();
});
$("#closeRenameBox").addEventListener("click", () => els.renameDialog.close());
$("#cancelRenameBox").addEventListener("click", () => els.renameDialog.close());
els.renameDialog.addEventListener("click", event => { if (event.target === els.renameDialog) els.renameDialog.close(); });
els.species.addEventListener("change", () => { updateAbilityOptions(0); populateMoveFields(); updateCalculatedStats(); });
els.form.addEventListener("submit", event => { event.preventDefault(); if (applyEditor()) els.dialog.close(); });
$("#closeDialog").addEventListener("click", () => els.dialog.close());
$("#cancelEdit").addEventListener("click", () => els.dialog.close());
$("#clearPokemon").addEventListener("click", () => {
  writePokemon(state.current, { species: 0 });
  state.selection.delete(pokemonKey(state.current));
  compactParty(); markChanged();
  if (state.searchQuery.trim()) refreshBoxSelectors();
  renderAllSlots(); updateSelectionUi();
  els.dialog.close();
});
els.download.addEventListener("click", downloadSave);
els.confirmDownload.addEventListener("click", performDownload);
$("#closeReport").addEventListener("click", () => els.reportDialog.close());
$("#cancelDownload").addEventListener("click", () => els.reportDialog.close());
els.reportDialog.addEventListener("click", event => { if (event.target === els.reportDialog) els.reportDialog.close(); });
els.undo.addEventListener("click", undoLastChange);
els.reset.addEventListener("click", resetChanges);
els.dialog.addEventListener("click", event => { if (event.target === els.dialog) els.dialog.close(); });
els.level.addEventListener("input", () => { clampNumericField(els.level, 1, 100); updateCalculatedStats(); });
els.nature.addEventListener("change", updateCalculatedStats);
els.friendship.addEventListener("input", () => clampNumericField(els.friendship, 0, 255));
els.moves.forEach((field, index) => field.addEventListener("change", () => renderMoveInfo(index)));
els.ivs.addEventListener("input", event => {
  if (!event.target.matches("input")) return;
  clampNumericField(event.target, 0, 31); updateHiddenPower(); updateCalculatedStats();
});
els.evs.addEventListener("input", event => {
  if (!event.target.matches("input")) return;
  enforceEvLimit(event.target); updateCalculatedStats();
});
els.illegalMoves.addEventListener("click", () => {
  state.allowIllegalMoves = !state.allowIllegalMoves;
  els.illegalMoves.setAttribute("aria-pressed", String(state.allowIllegalMoves));
  els.illegalMoves.textContent = state.allowIllegalMoves ? "Use legal moves only" : "Allow illegal moves";
  populateMoveFields();
});
els.illegalEvs.addEventListener("click", () => {
  state.allowIllegalEvs = !state.allowIllegalEvs;
  els.illegalEvs.setAttribute("aria-pressed", String(state.allowIllegalEvs));
  els.illegalEvs.textContent = state.allowIllegalEvs ? "Enforce 510 total EVs" : "Allow more than 510 total EVs";
  if (!state.allowIllegalEvs) {
    let remaining = 510;
    [...els.evs.querySelectorAll("input")].forEach(field => {
      const value = Math.min(clamp(field.value, 0, 255), remaining);
      field.value = String(value); remaining -= value;
    });
  }
  updateCalculatedStats();
});
els.selectMode.addEventListener("click", () => {
  state.selectMode = !state.selectMode;
  els.selectMode.setAttribute("aria-pressed", String(state.selectMode));
  els.selectMode.textContent = state.selectMode ? "Done selecting" : "Select";
  setActionStatus(state.selectMode ? "Tap Pokémon to select more than one." : "");
});
els.exportSelected.addEventListener("click", () => exportPokemon([...state.selection.values()]));
els.importInput.addEventListener("click", () => {
  if (!state.importTargetLocked) state.importTarget = null;
  state.importTargetLocked = false;
});
els.importInput.addEventListener("change", async event => {
  const file = event.target.files[0];
  if (!file) return;
  try { await importPokemonFile(file, state.importTarget); }
  catch (error) { setActionStatus(error.message || "Could not import this Pokémon file.", true); }
  finally { event.target.value = ""; state.importTarget = null; }
});
els.movePanelToggle.addEventListener("click", () => {
  const opening = els.movePanel.hidden;
  els.movePanel.hidden = !opening;
  els.editorLayout.classList.toggle("has-move-panel", opening);
  els.movePanelToggle.textContent = opening ? "Close move panel" : "Open move panel";
  if (opening) renderMoveBox();
});
$("#closeMovePanel").addEventListener("click", () => {
  els.movePanel.hidden = true;
  els.editorLayout.classList.remove("has-move-panel");
  els.movePanelToggle.textContent = "Open move panel";
});
els.moveBoxSelect.addEventListener("change", renderMoveBox);
els.contextMenu.addEventListener("click", event => {
  const action = event.target.closest("button")?.dataset.action;
  const location = state.context;
  if (!action || !location) return;
  const selectedGroup = state.selection.has(pokemonKey(location)) ? [...state.selection.values()] : [location];
  hideContextMenu();
  if (action === "edit") openEditor(readLocation(location));
  if (action === "copy") copyLocations(selectedGroup);
  if (action === "export") exportPokemon(selectedGroup);
  if (action === "paste") pasteAtLocation(location);
  if (action === "import") choosePokemonImport(location);
  if (action === "move") moveLocationsToTarget([...state.selection.values()], location);
  if (action === "remove") removeLocations(selectedGroup);
});
document.addEventListener("pointerdown", event => { if (!els.contextMenu.hidden && !els.contextMenu.contains(event.target)) hideContextMenu(); });
document.addEventListener("keydown", event => {
  if (event.key === "Escape") { hideContextMenu(); return; }
  if (els.dialog.open || event.target.matches("input, select, textarea, [contenteditable]")) return;
  if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === "c" && state.selection.size) {
    event.preventDefault(); copyLocations([...state.selection.values()]);
  }
  if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === "v" && state.clipboard.length) {
    event.preventDefault();
    if (state.lastLocation) pasteAtLocation(state.lastLocation);
    else setActionStatus("Select or right-click a destination before pasting.", true);
  }
  if ((event.key === "Delete" || event.key === "Backspace") && state.selection.size) {
    event.preventDefault(); removeLocations([...state.selection.values()]);
  }
});

const gameDataPromise = loadGameData().catch(error => {
  console.error(error);
  els.error.textContent = "Could not load the editor's game data.";
  throw error;
});

window.AdventureRedSaveEditor = { parseSave, checksum, readPokemon, serializeSave, growthExperience };
