-- Prove2me | Definitions.Def_Arm64_Process_Overrides
-- name    : Arm64_Process_Overrides
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:19:39.457725+00:00
-- url     : https://prove2.me/theorems/ab139a57-1932-4938-b40b-9a54a93eae8c
-- title:
--   Arm64.Trusted.Process.Overrides — Symbol-Keyed Hook Overrides for Whole-Binary ELF Judgments
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Process/Overrides.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Overrides.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Process/Overrides.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Overrides.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Process/Overrides.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
Also 4 interpolated strings written out as their elaboration `toString … ++ …`, because prove2.me rejects interpolated strings.
No other change.
-/

module

public import Definitions.Def_Arm64_Process_Semantics

/-!
# Symbol-Keyed Hook Overrides for Whole-Binary ELF Judgments (`Arm64.Trusted.Process.Overrides`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: Full `.symtab` parse (`ElfSym`, `ElfShdr`, `parseSymtabFull`),
  fail-closed resolution of function names to addresses (`resolveSym`, `resolveAddrs`), the
  address-keyed hook program (`Program.ofSites`), and the whole-binary judgment that replaces named
  functions by Lean models (`ElfRunsToWithOverrides`). `ElfSym` / `ElfShdr` stay public because
  the kernel-speed resolution checker in `ProofLib/Process/Overrides.lean` mirrors their parsers.
- **When to read**: Read when auditing a whole-binary theorem that models some functions of the
  executable (extern stubs, verified subroutines) instead of executing their machine code.
-/

@[expose] public section

namespace Arm64

/-- Hook program for whole-binary runs: supervisor calls go to `svc`, and override `f` replaces
    the function whose entry point is the absolute address `addr` for each `(name, addr, f)` in
    `sites`. `base = 0`, so a site fires exactly when `pc.toNat = addr` (`Program.externAt?`).
    `code` is empty: process steps fetch from `s.mem` (`Program.fetchMem`). -/
def Program.ofSites (svc : State → State) (sites : List (String × Nat × (State → State))) :
    Program :=
  { base := 0#64, code := [], stubs := [], externs := fun _ => none, svc := svc
    symbols := sites.map fun (n, a, _) => (n, a)
    overrides := fun n => (sites.find? (·.1 == n)).map (·.2.2) }

namespace Process

/-- One `.symtab` entry (`Elf64_Sym`): `type = st_info & 0xf`, `bind = st_info >> 4`. -/
structure ElfSym where
  name  : String
  value : Nat
  size  : Nat
  type  : Nat
  bind  : Nat
  shndx : Nat
  deriving DecidableEq, Repr

/-- The fields of one section header (`Elf64_Shdr`) that override resolution checks. -/
structure ElfShdr where
  type  : Nat
  flags : Nat
  addr  : Nat
  size  : Nat
  deriving DecidableEq, Repr

/-- Parse `n` 24-byte `Elf64_Sym` entries from `sym`, with names from `.strtab`. Fails on a name
    offset outside `.strtab` or an unterminated name. -/
def parseSymEntries (strtab : List (BitVec 8)) (strSize : Nat) :
    Nat → List (BitVec 8) → Except String (List ElfSym)
  | 0, _ => .ok []
  | n + 1, sym => do
    let stName := listReadU32LE sym 0
    if stName ≥ strSize then .error "symtab: st_name out of bounds"
    let some name := readStrtabCString (strSize - stName) (strtab.drop stName) []
      | .error "symtab: unterminated name"
    let info := listGetByte sym 4
    let e : ElfSym := { name, value := listReadU64LE sym 8, size := listReadU64LE sym 16,
                        type := info % 16, bind := info / 16, shndx := listReadU16LE sym 6 }
    return e :: (← parseSymEntries strtab strSize n (sym.drop 24))

/-- Parse `n` 64-byte section headers from `sh`. -/
def parseShdrs : Nat → List (BitVec 8) → List ElfShdr
  | 0, _ => []
  | n + 1, sh =>
    { type := listReadU32LE sh 4, flags := listReadU64LE sh 8, addr := listReadU64LE sh 16,
      size := listReadU64LE sh 32 } :: parseShdrs n (sh.drop 64)

/-- All entries (local and global) of the first `SHT_SYMTAB` section, and all section headers,
    with the same layout checks as `parseSymtab`. Fails if there is no `.symtab`. -/
def parseSymtabFull (bytes : List (BitVec 8)) : Except String (List ElfSym × List ElfShdr) := do
  let fileSize := bytes.length
  let eShoff := listReadU64LE bytes 40
  let eShnum := listReadU16LE bytes 60
  if fileSize < 64 || listReadU16LE bytes 58 != 64 || eShnum == 0 then .error "symtab: no shdrs"
  if eShoff + eShnum * 64 > fileSize then .error "symtab: shdrs exceed file"
  let shTable := bytes.drop eShoff
  let some (shOff, shSize, shLink, _, shEnt) := findSymtabShdr eShnum shTable
    | .error "symtab: no SHT_SYMTAB"
  if shEnt != 24 || shSize % 24 != 0 || shOff + shSize > fileSize || shLink ≥ eShnum then
    .error "symtab: bad SHT_SYMTAB header"
  let strSh := shTable.drop (shLink * 64)
  let strOff := listReadU64LE strSh 24
  let strSize := listReadU64LE strSh 32
  if listReadU32LE strSh 4 != 3 || strOff + strSize > fileSize then
    .error "symtab: bad SHT_STRTAB header"
  let syms ← parseSymEntries (bytes.drop strOff) strSize (shSize / 24) (bytes.drop shOff)
  return (syms, parseShdrs eShnum shTable)

/-- Resolve `name` to the address of a function: `name` must have exactly one `.symtab` entry (of
    any type or binding), and it must be `STT_FUNC` (2) with nonzero size, 4-aligned, in a regular
    section (`0 < st_shndx < SHN_LORESERVE`) that is `SHT_PROGBITS` (1) with
    `SHF_ALLOC | SHF_EXECINSTR` (`0x2 | 0x4`), and `[value, value + size)` must lie inside that
    section and inside one executable `PT_LOAD` segment of `img`. -/
def resolveSym (img : ElfImage) (syms : List ElfSym) (shdrs : List ElfShdr) (name : String) :
    Except String Nat :=
  match syms.filter (·.name == name) with
  | [e] =>
    match shdrs[e.shndx]? with
    | some sh =>
      if e.type == 2 && e.size != 0 && e.value % 4 == 0 && e.shndx != 0 && e.shndx < 0xff00 &&
          sh.type == 1 && sh.flags &&& 6 == 6 &&
          sh.addr ≤ e.value && e.value + e.size ≤ sh.addr + sh.size &&
          img.segments.any (fun r => r.perm.x && r.start.toNat ≤ e.value &&
            e.value + e.size ≤ r.start.toNat + r.bytes.length) then .ok e.value
      else .error (toString "override " ++ toString (name) ++ toString ": not a sized, aligned function in executable code" : String)
    | none => .error (toString "override " ++ toString (name) ++ toString ": bad st_shndx" : String)
  | [] => .error (toString "override " ++ toString (name) ++ toString ": no .symtab entry" : String)
  | _ => .error (toString "override " ++ toString (name) ++ toString ": duplicate .symtab entries" : String)

/-- Resolve each name in `names` (`resolveSym`); fails unless the names and the resolved addresses
    are pairwise distinct. -/
def resolveAddrs (bytes : List (BitVec 8)) (img : ElfImage) (names : List String) :
    Except String (List Nat) := do
  let (syms, shdrs) ← parseSymtabFull bytes
  let addrs ← names.mapM (resolveSym img syms shdrs)
  if names.Nodup ∧ addrs.Nodup then return addrs else .error "overrides: duplicate name or address"

/-- `Program.ofSites svc` with each override `(name, f) ∈ os` placed at the address of `name`. -/
def overrideProgram (svc : State → State) (os : List (String × (State → State)))
    (addrs : List Nat) : Program :=
  Program.ofSites svc (os.zipWith (fun (n, f) a => (n, a, f)) addrs)

/-- `ElfRunsTo` where each function named in `os` is replaced by its model: `elfBytes` parses to
    `img`, every name in `os` resolves (`resolveAddrs`) in the parsed `.symtab` (both
    unconditionally, outside `∀ inputs`), and for every `inputs` with `pre inputs`, loading
    succeeds and the run of `overrideProgram svc os addrs` satisfies
    `ProcessRunsTo … (post inputs) (oom inputs)`. False unless every name resolves. -/
def ElfRunsToWithOverrides (svc : State → State) (os : List (String × (State → State)))
    (elfBytes : List (BitVec 8))
    (pre : ProcessInputs → Prop)
    (post : ProcessInputs → ProcessOutcome → Prop)
    (oom : ProcessInputs → State → Prop := fun _ _ => False) : Prop :=
  ∃ img addrs, ElfImage.parse elfBytes = .ok img ∧
    resolveAddrs elfBytes img (os.map (·.1)) = .ok addrs ∧
    ∀ inputs, pre inputs →
      ∃ s0, img.loadState inputs = .ok s0 ∧
        ProcessRunsTo (overrideProgram svc os addrs) s0 (post inputs) (oom inputs)

end Process

end Arm64


