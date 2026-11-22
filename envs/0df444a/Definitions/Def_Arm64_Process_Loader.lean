-- Prove2me | Definitions.Def_Arm64_Process_Loader
-- name    : Arm64_Process_Loader
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:17:46.743203+00:00
-- url     : https://prove2.me/theorems/de83be43-5a3a-4f5e-b8d1-82f0cc185e0c
-- title:
--   Arm64.Trusted.Process.Loader — Static ELF64 Loader & Linux AArch64 Initial Process State
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Process/Loader.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Loader.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Process/Loader.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Loader.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Process/Loader.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
Also removed `public meta import Arm64.Trusted.Process.Types` (already imported).
Also 6 interpolated strings written out as their elaboration `toString … ++ …`, because prove2.me rejects interpolated strings.
No other change.
-/

module

public import Definitions.Def_Arm64_Process_Types
public import Definitions.Def_Arm64_Object_Reloc

/-!
# Static ELF64 Loader & Linux AArch64 Initial Process State (`Arm64.Trusted.Process.Loader`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: Pure-Lean static ELF64 `ET_EXEC` parser (`ElfImage.parse`,
  including `SHT_SYMTAB`/`SHT_STRTAB` function symbol extraction),
  well-formedness check (`ElfImage.WellFormed`), deterministic Linux AArch64 initial
  stack/auxiliary-vector builder (`buildInitialStack`), initial file-descriptor and in-memory
  file-system setup (`initFsState`), process state loader (`ElfImage.loadState`, `loadElf`).
- **When to read**: Read when auditing how a statically linked ELF64 binary is validated and
  mapped into an initial `Arm64.State` (`PT_LOAD` segments, `SHT_SYMTAB` symbols, `brkStart`,
  `argc`/`argv`/`envp`/`auxv` on the stack, and `fd 0/1/2` in `State.fs`).
-/

@[expose] public section

namespace Arm64.Process

/-! ## Little-Endian Byte Readers for ELF64 Parsing -/

/-- Read byte `off` of `bs : List (BitVec 8)` as a `Nat` (`0` if out of bounds). -/
def listGetByte (bs : List (BitVec 8)) (off : Nat) : Nat :=
  match (bs.drop off).head? with
  | some b => b.toNat
  | none   => 0

/-- Read a 16-bit little-endian unsigned integer from `bs : List (BitVec 8)` at byte offset `off`. -/
def listReadU16LE (bs : List (BitVec 8)) (off : Nat) : Nat :=
  match bs.drop off with
  | b0 :: b1 :: _ => b0.toNat ||| (b1.toNat <<< 8)
  | [b0]          => b0.toNat
  | []            => 0

/-- Read a 32-bit little-endian unsigned integer from `bs : List (BitVec 8)` at byte offset `off`. -/
def listReadU32LE (bs : List (BitVec 8)) (off : Nat) : Nat :=
  match bs.drop off with
  | b0 :: b1 :: b2 :: b3 :: _ =>
    b0.toNat ||| (b1.toNat <<< 8) ||| (b2.toNat <<< 16) ||| (b3.toNat <<< 24)
  | _ => listReadU16LE bs off ||| (listReadU16LE bs (off + 2) <<< 16)

/-- Read a 64-bit little-endian unsigned integer from `bs : List (BitVec 8)` at byte offset `off`. -/
def listReadU64LE (bs : List (BitVec 8)) (off : Nat) : Nat :=
  match bs.drop off with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
    b0.toNat ||| (b1.toNat <<< 8) ||| (b2.toNat <<< 16) ||| (b3.toNat <<< 24) |||
    (b4.toNat <<< 32) ||| (b5.toNat <<< 40) ||| (b6.toNat <<< 48) ||| (b7.toNat <<< 56)
  | _ => listReadU32LE bs off ||| (listReadU32LE bs (off + 4) <<< 32)

/-- Round `n` down to a multiple of `Obj.pageSize` (`4096`). -/
def pageAlignDown (n : Nat) : Nat :=
  (n / Obj.pageSize) * Obj.pageSize

/-- Round `n` up to a multiple of `Obj.pageSize` (`4096`). -/
def pageAlignUp (n : Nat) : Nat :=
  ((n + (Obj.pageSize - 1)) / Obj.pageSize) * Obj.pageSize

/-- Round `n` up to a multiple of `16`. -/
def alignUp16 (n : Nat) : Nat :=
  ((n + 15) / 16) * 16

/-! ## Pure-Lean ELF64 `ET_EXEC` Parser (`ElfImage.parse`) -/

/-- Insert a `Snapshot.Region` into a list ordered by ascending `start.toNat`. -/
def insertRegionSorted (r : Snapshot.Region) : List Snapshot.Region → List Snapshot.Region
  | [] => [r]
  | q :: qs =>
    if r.start.toNat ≤ q.start.toNat then r :: q :: qs
    else q :: insertRegionSorted r qs

/-- Check that a single region is page-aligned, non-empty, within 48-bit user address space,
    mapped, and W^X compliant. -/
def regionAlignedValid (r : Snapshot.Region) : Bool :=
  let len := r.bytes.length
  r.start.toNat ≥ Obj.pageSize &&
  r.start.toNat % Obj.pageSize == 0 &&
  len > 0 &&
  len % Obj.pageSize == 0 &&
  r.start.toNat + len ≤ 2 ^ 48 &&
  !(r.perm.w && r.perm.x) &&
  (r.perm.r || r.perm.w || r.perm.x)

/-- Check that adjacent regions in a sorted list are strictly non-overlapping and page-aligned. -/
def regionsDisjointAndAligned : List Snapshot.Region → Bool
  | [] => true
  | [r] => regionAlignedValid r
  | r1 :: r2 :: rest =>
    regionAlignedValid r1 &&
    r1.start.toNat + r1.bytes.length ≤ r2.start.toNat &&
    regionsDisjointAndAligned (r2 :: rest)

/-- Check that `entry` is 4-byte aligned and lies within an executable (`perm.x`) region. -/
def entryInExecRegion (entry : BitVec 64) (regions : List Snapshot.Region) : Bool :=
  entry.toNat % 4 == 0 &&
  regions.any fun r =>
    r.perm.x &&
    r.start.toNat ≤ entry.toNat &&
    entry.toNat + 4 ≤ r.start.toNat + r.bytes.length

/-- Structural well-formedness check on a parsed `ElfImage`. -/
def ElfImage.WellFormed (img : ElfImage) : Bool :=
  !img.segments.isEmpty &&
  img.phent == 56 &&
  regionsDisjointAndAligned img.segments &&
  entryInExecRegion img.entry img.segments &&
  img.brkStart.toNat % Obj.pageSize == 0 &&
  img.segments.all (fun r => r.start.toNat + r.bytes.length ≤ img.brkStart.toNat)

/-- Parse a single 56-byte ELF64 program header `ph` over `bytes : List (BitVec 8)` of length `fileSize`.
    Fails closed on `PT_INTERP`, `PT_DYNAMIC`, executable `PT_GNU_STACK`,
    W+X segments, or unknown segment types. -/
def parseProgramHeader (bytes : List (BitVec 8)) (fileSize : Nat) (ph : List (BitVec 8))
    (ePhoff ePhBytes : Nat) (accRegions : List Snapshot.Region) (accPhdrVaddr : BitVec 64)
    (accMaxEnd : Nat) : Except String (List Snapshot.Region × BitVec 64 × Nat) := do
  let pType   := listReadU32LE ph 0
  let pFlags  := listReadU32LE ph 4
  let pOffset := listReadU64LE ph 8
  let pVaddr  := listReadU64LE ph 16
  let pFilesz := listReadU64LE ph 32
  let pMemsz  := listReadU64LE ph 40
  if pType == 0 then
    pure (accRegions, accPhdrVaddr, accMaxEnd)
  else if pType == 2 then
    .error "ElfImage.parse: dynamic ELF (PT_DYNAMIC) is not supported"
  else if pType == 3 then
    .error "ElfImage.parse: dynamic interpreter (PT_INTERP) is not supported"
  else if pType == 6 then
    pure (accRegions, BitVec.ofNat 64 pVaddr, accMaxEnd)
  else if pType == 0x6474e551 then
    if (pFlags &&& 1) != 0 then
      .error "ElfImage.parse: executable stack (PT_GNU_STACK with PF_X) is not supported"
    else
      pure (accRegions, accPhdrVaddr, accMaxEnd)
  else if pType == 4 || pType == 7 || pType == 0x6474e550 || pType == 0x6474e552 ||
          pType == 0x6474e553 || pType == 0x70000002 then
    pure (accRegions, accPhdrVaddr, accMaxEnd)
  else if pType == 1 then
    if pMemsz == 0 then
      pure (accRegions, accPhdrVaddr, accMaxEnd)
    else
      if pOffset + pFilesz > fileSize then
        .error "ElfImage.parse: PT_LOAD segment exceeds file size"
      if pFilesz > pMemsz then
        .error "ElfImage.parse: PT_LOAD p_filesz exceeds p_memsz"
      if pVaddr < Obj.pageSize then
        .error "ElfImage.parse: PT_LOAD maps below first page (0x1000)"
      if pVaddr % Obj.pageSize != pOffset % Obj.pageSize then
        .error "ElfImage.parse: PT_LOAD p_vaddr and p_offset are not page-congruent"
      let perm : Perm :=
        { r := (pFlags &&& 4) != 0
          w := (pFlags &&& 2) != 0
          x := (pFlags &&& 1) != 0 }
      if perm.w && perm.x then
        .error "ElfImage.parse: W+X PT_LOAD segment is not supported"
      if !(perm.r || perm.w || perm.x) then
        .error "ElfImage.parse: PT_LOAD segment has no permissions"
      if pFilesz < pMemsz && !perm.w then
        .error "ElfImage.parse: non-writable PT_LOAD segment has p_filesz < p_memsz"
      let pageStart := pageAlignDown pVaddr
      let lead      := pVaddr - pageStart
      let pageEnd   := pageAlignUp (pVaddr + pMemsz)
      if pageEnd > 2 ^ 48 then
        .error "ElfImage.parse: PT_LOAD segment exceeds 48-bit user address space"
      let regionSize := pageEnd - pageStart
      let regBytes : List (BitVec 8) :=
        if pFilesz == pMemsz then
          let fileStart := pOffset - lead
          let avail     := Nat.min regionSize (fileSize - fileStart)
          let fileBytes := (bytes.drop fileStart).take avail
          let padLen    := regionSize - avail
          if padLen == 0 then fileBytes else fileBytes ++ List.replicate padLen 0#8
        else if pFilesz > 0 then
          let fileStart := pOffset - lead
          let fileLen   := (pOffset + pFilesz) - fileStart
          let fileBytes := (bytes.drop fileStart).take fileLen
          let tailLen   := pageEnd - (pVaddr + pFilesz)
          if tailLen == 0 then fileBytes else fileBytes ++ List.replicate tailLen 0#8
        else
          List.replicate regionSize 0#8
      let nonAnonLen := if pFilesz > 0 then pageAlignUp (pVaddr + pFilesz) - pageStart else 0
      let reg : Snapshot.Region :=
        { start      := BitVec.ofNat 64 pageStart
          perm       := perm
          bytes      := regBytes
          nonAnonLen := nonAnonLen }
      let fileMapStart := if pOffset ≥ lead && pFilesz > 0 then pOffset - lead else pOffset
      let fileMapEnd   := pOffset + pFilesz
      let phdrVaddr' :=
        if accPhdrVaddr != 0#64 then accPhdrVaddr
        else if fileMapStart ≤ ePhoff && ePhoff + ePhBytes ≤ fileMapEnd then
          BitVec.ofNat 64 (pageStart + (ePhoff - fileMapStart) +
            (if fileMapStart == pOffset then lead else 0))
        else 0#64
      pure (insertRegionSorted reg accRegions, phdrVaddr', Nat.max accMaxEnd pageEnd)
  else
    .error (toString "ElfImage.parse: unsupported program header type " ++ toString (pType) : String)

/-- Parse `ePhnum` 56-byte program headers from `phTable`. -/
def parseProgramHeaders (bytes : List (BitVec 8)) (fileSize ePhoff ePhBytes : Nat) :
    Nat → List (BitVec 8) → List Snapshot.Region → BitVec 64 → Nat →
    Except String (List Snapshot.Region × BitVec 64 × Nat)
  | 0, _, regs, phdr, mx => pure (regs, phdr, mx)
  | n + 1, phTable, regs, phdr, mx => do
    let (regs', phdr', mx') ←
      parseProgramHeader bytes fileSize phTable ePhoff ePhBytes regs phdr mx
    parseProgramHeaders bytes fileSize ePhoff ePhBytes n (phTable.drop 56) regs' phdr' mx'

/-- Read a NUL-terminated string from `bs` within `rem` remaining bytes of `.strtab`. -/
def readStrtabCString : Nat → List (BitVec 8) → List Char → Option String
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | rem + 1, b :: bs, acc =>
    if b == 0#8 then
      some (String.ofList acc.reverse)
    else
      readStrtabCString rem bs (Char.ofNat b.toNat :: acc)

/-- Walk `numEntries` 24-byte ELF64 `SHT_SYMTAB` entries by structural recursion on `numEntries`,
    extracting defined `STT_FUNC` (`(st_info &&& 0xf) == 2`, `st_shndx != 0`, `st_name != 0`)
    symbols `(name, vaddr)`. -/
def parseSymtabEntries (strtab : List (BitVec 8)) (strSize : Nat) :
    Nat → List (BitVec 8) → List (String × BitVec 64) →
    Except String (List (String × BitVec 64))
  | 0, _, acc => .ok acc.reverse
  | n + 1, sym, acc =>
    let nextSym := sym.drop 24
    if (listGetByte sym 4 &&& 0xf) == 2 && listReadU16LE sym 6 != 0 then
      let stName := listReadU32LE sym 0
      if stName == 0 then
        parseSymtabEntries strtab strSize n nextSym acc
      else if stName ≥ strSize then
        .error "ElfImage.parse: symbol st_name out of bounds in .strtab"
      else
        match readStrtabCString (strSize - stName) (strtab.drop stName) [] with
        | none => .error "ElfImage.parse: unterminated symbol name in .strtab"
        | some name =>
          let stValue := listReadU64LE sym 8
          parseSymtabEntries strtab strSize n nextSym
            ((name, BitVec.ofNat 64 stValue) :: acc)
    else
      parseSymtabEntries strtab strSize n nextSym acc

/-- Scan `eShnum` 64-byte section headers in `shTable` for `SHT_SYMTAB` (`sh_type == 2`),
    returning `some (shOffset, shSize, shLink, shInfo, shEntsize)`. -/
def findSymtabShdr : Nat → List (BitVec 8) → Option (Nat × Nat × Nat × Nat × Nat)
  | 0, _ => none
  | n + 1, sh =>
    if listReadU32LE sh 4 == 2 then
      some (listReadU64LE sh 24, listReadU64LE sh 32, listReadU32LE sh 40,
            listReadU32LE sh 44, listReadU64LE sh 56)
    else
      findSymtabShdr n (sh.drop 64)

/-- Extract defined `STT_FUNC` symbols from `SHT_SYMTAB` / `SHT_STRTAB` in `bytes : List (BitVec 8)`. -/
def parseSymtab (bytes : List (BitVec 8)) (fileSize eShoff eShentsize eShnum : Nat) :
    Except String (List (String × BitVec 64)) := do
  if eShnum == 0 then
    pure []
  else
    if eShentsize != 64 then
      .error (toString "ElfImage.parse: expected e_shentsize=64, got " ++ toString (eShentsize) : String)
    let eShBytes := eShnum * 64
    if eShoff + eShBytes > fileSize then
      .error "ElfImage.parse: section header table exceeds file size"
    let shTable := bytes.drop eShoff
    match findSymtabShdr eShnum shTable with
    | none => pure []
    | some (shOffset, shSize, shLink, shInfo, shEntsize) =>
      if shEntsize != 24 then
        .error (toString "ElfImage.parse: expected SHT_SYMTAB sh_entsize=24, got " ++ toString (shEntsize) : String)
      if shOffset + shSize > fileSize then
        .error "ElfImage.parse: SHT_SYMTAB section exceeds file size"
      if shSize % 24 != 0 then
        .error "ElfImage.parse: SHT_SYMTAB sh_size is not a multiple of 24"
      let totalEntries := shSize / 24
      if shInfo > totalEntries then
        .error "ElfImage.parse: SHT_SYMTAB sh_info exceeds symbol count"
      if shLink ≥ eShnum then
        .error "ElfImage.parse: SHT_SYMTAB sh_link out of bounds"
      let strSh     := shTable.drop (shLink * 64)
      let strType   := listReadU32LE strSh 4
      let strOffset := listReadU64LE strSh 24
      let strSize   := listReadU64LE strSh 32
      if strType != 3 then
        .error "ElfImage.parse: SHT_SYMTAB sh_link is not SHT_STRTAB (3)"
      if strOffset + strSize > fileSize then
        .error "ElfImage.parse: SHT_STRTAB section exceeds file size"
      let symStart := shOffset + shInfo * 24
      let symtab   := bytes.drop symStart
      let strtab   := bytes.drop strOffset
      parseSymtabEntries strtab strSize (totalEntries - shInfo) symtab []

/-- Parse a raw ELF64 `ET_EXEC` AArch64 binary (`List (BitVec 8)`) into an `ElfImage`.
    References:
    - System V ABI (ELF-64 Object File Format):
      https://refspecs.linuxfoundation.org/elf/gabi4+/contents.html
    - ELF for the Arm 64-bit Architecture (AAELF64):
      https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst -/
def ElfImage.parse (bytes : List (BitVec 8)) : Except String ElfImage := do
  let fileSize := bytes.length
  if fileSize < 64 then
    .error "ElfImage.parse: file shorter than 64-byte ELF64 header"
  if listGetByte bytes 0 != 0x7f || listGetByte bytes 1 != 0x45 ||
     listGetByte bytes 2 != 0x4c || listGetByte bytes 3 != 0x46 then
    .error "ElfImage.parse: bad ELF magic"
  if listGetByte bytes 4 != 2 then
    .error "ElfImage.parse: expected ELFCLASS64 (2)"
  if listGetByte bytes 5 != 1 then
    .error "ElfImage.parse: expected ELFDATA2LSB (1, little-endian)"
  if listGetByte bytes 6 != 1 then
    .error "ElfImage.parse: expected EV_CURRENT (1)"
  let eType      := listReadU16LE bytes 16
  let eMachine   := listReadU16LE bytes 18
  let eEntry     := listReadU64LE bytes 24
  let ePhoff     := listReadU64LE bytes 32
  let eShoff     := listReadU64LE bytes 40
  let ePhentsize := listReadU16LE bytes 54
  let ePhnum     := listReadU16LE bytes 56
  let eShentsize := listReadU16LE bytes 58
  let eShnum     := listReadU16LE bytes 60
  if eType != 2 then
    .error (toString "ElfImage.parse: expected static ET_EXEC (2), got e_type=" ++ toString (eType) : String)
  if eMachine != 183 then
    .error (toString "ElfImage.parse: expected EM_AARCH64 (183), got e_machine=" ++ toString (eMachine) : String)
  if ePhentsize != 56 then
    .error (toString "ElfImage.parse: expected e_phentsize=56, got " ++ toString (ePhentsize) : String)
  if ePhnum == 0 then
    .error "ElfImage.parse: e_phnum is 0"
  let ePhBytes := ePhnum * 56
  if ePhoff + ePhBytes > fileSize then
    .error "ElfImage.parse: program header table exceeds file size"
  let (regions, phdrVaddr, maxEnd) ←
    parseProgramHeaders bytes fileSize ePhoff ePhBytes ePhnum (bytes.drop ePhoff) [] 0#64 0
  let symbols ← parseSymtab bytes fileSize eShoff eShentsize eShnum
  let img : ElfImage :=
    { entry     := BitVec.ofNat 64 eEntry
      phdrVaddr := phdrVaddr
      phent     := 56
      phnum     := ePhnum
      segments  := regions
      brkStart  := BitVec.ofNat 64 maxEnd
      symbols   := symbols }
  if !img.WellFormed then
    .error "ElfImage.parse: resulting segment layout failed WellFormed check (overlapping segments or invalid entry)"
  pure img

/-! ## Deterministic Linux AArch64 Initial Stack & Auxiliary Vector Construction -/

/-- Pack a list of NUL-terminated byte strings into a flat byte buffer starting at `baseAddr`,
    returning `(endOffset, flatBytes, stringAddresses)`. -/
def packCStringList (baseAddr : BitVec 64) (strs : List (List (BitVec 8))) :
    Nat × List (BitVec 8) × List (BitVec 64) :=
  strs.foldl
    (fun (off, accBytes, accAddrs) s =>
      let entry := s ++ [0#8]
      let addr := baseAddr + BitVec.ofNat 64 off
      (off + entry.length, accBytes ++ entry, accAddrs ++ [addr]))
    (0, [], [])

/-- Construct the initial Linux AArch64 user stack frame (`[sp, stackTop)`) for `img` and `inputs`
    (following Linux `fs/exec.c` `bprm_mm_init` + `fs/binfmt_elf.c` `create_elf_tables` and QEMU
    `linux-user/elfload.c` `setup_arg_pages` + `create_elf_tables`):
    - Top of stack (`[infoBase, stackTop)`): 16-byte `AT_RANDOM` buffer at 16-byte-aligned
      `infoBase`, `< 16` zero alignment bytes, `"aarch64\0"` platform string (`AT_PLATFORM`),
      NUL-terminated `argv` strings, NUL-terminated `envp` strings, NUL-terminated `inputs.execfn`
      string (`AT_EXECFN`), and the 8-byte top-of-stack zero sentinel word (`sizeof(void *)`).
    - Frame table (`[sp, infoBase)`): `argc`, `argv[0..argc-1]`, `NULL`, `envp[0..envc-1]`, `NULL`,
      and `auxv` `(a_type, a_val)` pairs ending with `(AT_NULL, 0)`, padded to 16-byte alignment
      so `sp % 16 == 0`. -/
def buildInitialStack (img : ElfImage) (inputs : ProcessInputs) :
    Except String (BitVec 64 × Snapshot.Region) := do
  if inputs.init.auxv.randomBytes.length != 16 then
    .error "buildInitialStack: auxv.randomBytes must be exactly 16 bytes"
  if inputs.argv.any (fun s => s.contains 0#8) then
    .error "buildInitialStack: argv string contains embedded NUL byte"
  if inputs.envp.any (fun s => s.contains 0#8) then
    .error "buildInitialStack: envp string contains embedded NUL byte"
  if inputs.execfn.contains 0#8 then
    .error "buildInitialStack: execfn string contains embedded NUL byte"
  let top := inputs.init.stackTop.toNat
  if top % Obj.pageSize != 0 || inputs.init.stackSize == 0 || inputs.init.stackSize % Obj.pageSize != 0 then
    .error "buildInitialStack: stackTop and stackSize must be non-zero multiples of pageSize"
  if inputs.init.stackSize > top then
    .error "buildInitialStack: stack underflows address space"
  let stackBase := top - inputs.init.stackSize
  if img.brkStart.toNat > stackBase then
    .error "buildInitialStack: stack overlaps image or brkStart"
  -- "aarch64\0"
  let platformBytes : List (BitVec 8) :=
    [0x61#8, 0x61#8, 0x72#8, 0x63#8, 0x68#8, 0x36#8, 0x34#8, 0x00#8]
  let execfnBytes : List (BitVec 8) := inputs.execfn ++ [0#8]
  let topSentinelBytes : List (BitVec 8) := List.replicate 8 0#8
  let upperRawLen :=
    platformBytes.length +
    (inputs.argv.foldl (fun n s => n + s.length + 1) 0) +
    (inputs.envp.foldl (fun n s => n + s.length + 1) 0) +
    execfnBytes.length + topSentinelBytes.length
  let upperAlignedLen := alignUp16 upperRawLen
  let infoPadLen := upperAlignedLen - upperRawLen
  let infoLen := 16 + upperAlignedLen
  if infoLen > inputs.init.stackSize then
    .error "buildInitialStack: argv/envp strings exceed stackSize"
  let infoBaseNat := top - infoLen
  let infoBase := BitVec.ofNat 64 infoBaseNat
  let randomAddr := infoBase
  let platformAddr := infoBase + BitVec.ofNat 64 (16 + infoPadLen)
  let argvBase := platformAddr + BitVec.ofNat 64 platformBytes.length
  let (off1, argvBytes, argvAddrs) := packCStringList argvBase inputs.argv
  let envpBase := argvBase + BitVec.ofNat 64 off1
  let (off2, envpBytes, envpAddrs) := packCStringList envpBase inputs.envp
  let execfnAddr := envpBase + BitVec.ofNat 64 off2
  let infoBytes :=
    inputs.init.auxv.randomBytes ++ List.replicate infoPadLen 0#8 ++
    platformBytes ++ argvBytes ++ envpBytes ++ execfnBytes ++ topSentinelBytes
  let auxvPairs : List (BitVec 64 × BitVec 64) :=
    [ (AuxvTag.phdr,     img.phdrVaddr)
    , (AuxvTag.phent,    BitVec.ofNat 64 img.phent)
    , (AuxvTag.phnum,    BitVec.ofNat 64 img.phnum)
    , (AuxvTag.pagesz,   BitVec.ofNat 64 Obj.pageSize)
    , (AuxvTag.base,     0#64)
    , (AuxvTag.flags,    0#64)
    , (AuxvTag.entry,    img.entry)
    , (AuxvTag.uid,      inputs.init.auxv.uid)
    , (AuxvTag.euid,     inputs.init.auxv.euid)
    , (AuxvTag.gid,      inputs.init.auxv.gid)
    , (AuxvTag.egid,     inputs.init.auxv.egid)
    , (AuxvTag.platform, platformAddr)
    , (AuxvTag.hwcap,    inputs.init.auxv.hwcap)
    , (AuxvTag.clktck,   100#64)
    , (AuxvTag.secure,   inputs.init.auxv.secure)
    , (AuxvTag.random,   randomAddr)
    , (AuxvTag.hwcap2,   inputs.init.auxv.hwcap2)
    , (AuxvTag.execfn,   execfnAddr) ] ++
    inputs.init.auxv.extra ++
    [ (AuxvTag.null,     0#64) ]
  let headerWords : List (BitVec 64) :=
    [BitVec.ofNat 64 inputs.argv.length] ++ argvAddrs ++ [0#64] ++ envpAddrs ++ [0#64]
  let auxvWords : List (BitVec 64) :=
    auxvPairs.flatMap fun (t, v) => [t, v]
  let unpaddedWords := headerWords ++ auxvWords
  let tableWords :=
    if unpaddedWords.length % 2 == 0 then unpaddedWords else unpaddedWords ++ [0#64]
  let tableBytes : List (BitVec 8) := tableWords.flatMap (Obj.bytesLE 8)
  if tableBytes.length + infoBytes.length > inputs.init.stackSize then
    .error "buildInitialStack: initial stack frame exceeds stackSize"
  let spNat := infoBaseNat - tableBytes.length
  let sp := BitVec.ofNat 64 spNat
  let stackRegion : Snapshot.Region :=
    { start := sp
      perm  := Perm.rw
      bytes := tableBytes ++ infoBytes }
  pure (sp, stackRegion)

/-! ## Initial File-System & Standard-Stream State (`initFsState`) -/

/-- Construct the initial `FsState` from `inputs`:
    - `fd 0` is open `.rdonly` (`kind := .stdio`) at offset `0` backed by `fs.stdin = inputs.stdin`;
    - `fd 1` and `fd 2` are open `.wronly` (`kind := .stdio`) streams;
    - `entries` contains only CWD (`[] = .dir`), non-empty path prefixes of `inputs.dirs`, strict
      ancestor prefixes of `inputs.files`, and each `(p, bs)` in `inputs.files` under
      `normalizePath p` (standard streams never pollute the CWD file namespace). -/
def initFsState (inputs : ProcessInputs) : FsState :=
  let withDirs := inputs.dirs.foldl
    (fun fs d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) fs) ({} : FsState)
  let withFiles := inputs.files.foldl
    (fun fs (p, bs) =>
      let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) fs
      withAnc.setFile p (some (.file bs))) withDirs
  let fs1 := withFiles.setFd 0#64 (some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio })
  let fs2 := fs1.setFd 1#64 (some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio })
  { (fs2.setFd 2#64 (some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio })) with
    stdin := inputs.stdin }

/-! ## Process State Loader (`ElfImage.loadState`, `loadElf`) -/

/-- Load a validated `ElfImage` with `inputs` into its initial `Arm64.State`:
    - Rejects any `inputs.dirs` or `inputs.files` path with a leading `'/'` or `".."` segment, or
      any initial regular file exceeding `MAX_LFS_FILESIZE` (`2 ^ 63 - 1`), fail-closed
      (`Except.error`).
    - All `PT_LOAD` segments and the populated stack frame `[sp, stackTop)` are mapped via
      `Snapshot.cellAt`, and the remaining stack `[stackTop - stackSize, sp)` is mapped
      zero-filled `Perm.rw` via `Memory.mapZero`.
    - `pc = img.entry`, `sp` is the 16-byte-aligned initial stack pointer, `regs` and `vregs`
      are zeroed (`ELF_PLAT_INIT`), `brkStart = brk = img.brkStart`,
      `physMemAvail = inputs.init.physMemAvail`, `fs = initFsState inputs`, and
      `oracle = inputs.init.oracle`. -/
def ElfImage.loadState (img : ElfImage) (inputs : ProcessInputs := {}) : Except String State := do
  if !img.WellFormed then
    .error "ElfImage.loadState: image is not WellFormed"
  if inputs.dirs.any (fun d => hasLeadingSlash d || hasDotDot d) then
    .error "ElfImage.loadState: inputs.dirs paths must be relative without '..'"
  if inputs.files.any (fun (p, bs) => hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) then
    .error "ElfImage.loadState: inputs.files paths must be relative without '..' and size <= MAX_LFS_FILESIZE"
  let (sp, stackRegion) ← buildInitialStack img inputs
  let stackBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)
  let baseMem : Memory := ⟨Snapshot.loadCellAt (img.segments ++ [stackRegion])⟩
  let mem := baseMem.mapZero stackBase inputs.init.stackSize
  let symtab : String → String → Option (BitVec 64) :=
    fun _ name => (img.symbols.find? (·.1 == name)).map (·.2)
  pure {
    regs         := RegFile.empty
    vregs        := VRegFile.empty
    sp           := sp
    pc           := img.entry
    pstate       := PState.zero
    mem          := mem
    tpidrEl0     := 0#64
    brkStart     := img.brkStart
    brk          := img.brkStart
    physMemAvail := inputs.init.physMemAvail
    fs           := initFsState inputs
    oracle       := inputs.init.oracle
    oracleIdx    := 0
    exclFails    := inputs.init.oracle.exclFails
    trace        := []
    status       := .Running
    symtab       := symtab }

/-- Parse raw ELF64 `ET_EXEC` bytes (`List (BitVec 8)`) and load the initial process `State`. -/
def loadElf (elfBytes : List (BitVec 8)) (inputs : ProcessInputs := {}) : Except String State := do
  let img ← ElfImage.parse elfBytes
  img.loadState inputs

end Arm64.Process


