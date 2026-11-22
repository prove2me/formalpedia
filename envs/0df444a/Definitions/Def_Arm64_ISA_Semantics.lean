-- Prove2me | Definitions.Def_Arm64_ISA_Semantics
-- name    : Arm64_ISA_Semantics
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:11:36.521831+00:00
-- url     : https://prove2.me/theorems/2ba86e9b-a42e-47e6-a082-4da24d674446
-- title:
--   Arm64.Trusted.ISA.Semantics — ARM64 Small-Step Operational Semantics
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/ISA/Semantics.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Semantics.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/ISA/Semantics.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Semantics.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/ISA/Semantics.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
Also the constructor `Step.extern` renamed `Step.externHook` in comments (see below).
Also the `Step` constructor `extern` renamed `externHook`, because prove2.me rejects the token `extern` in code.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_Syntax
public import Definitions.Def_Arm64_ISA_Memory
public import Definitions.Def_Arm64_ISA_State
public import Definitions.Def_Arm64_ISA_Decode
public import Definitions.Def_Arm64_ISA_Eval
public import Definitions.Def_Arm64_Syscalls

/-!
# ARM64 Small-Step Operational Semantics (`Arm64.Semantics`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: Read-only relocated code image (`Program`), instruction fetch and
  decode from executable memory (`Program.fetchMem`) and from the static image (`Program.fetch`),
  code-in-memory invariant (`Program.CodeLoaded`), single-step transition relation (`Step`),
  and multi-step closure (`Steps`). The executable fuel-bounded evaluators (`ProofLib.stepState`,
  `execN`, `execUntilPC`) and the test-memory builder `Program.loadCode` are untrusted and live in
  `ProofLib/Exec.lean`.
- **When to read**: Read when auditing how `Step` fetches from `s.mem` (`fetchMem`), dispatches
  `externs`/`overrides` hooks (`Step.externHook`), or enforces `Memory.KeepsFrozen`. For proof
  stepping lemmas, see `ProofLib/Semantics.lean`.

Instructions are fetched from **memory** (`Program.fetchMem`) at an aligned, executable `pc`.
Because executable memory is never writable (`canWrite` requires `¬x`) and every `Step` preserves
frozen bytes (`Memory.KeepsFrozen`), `Program.CodeLoaded` is invariant across execution and
`Program.fetch` agrees with `Program.fetchMem` on loaded states.
-/

@[expose] public section

namespace Arm64

/-- Compatibility abbreviation executing a single `Instr` with `Syscall.standard`. -/
abbrev execInst : Instr → State → State := execInstWithSvc Syscall.standard

/-- Apply supervisor-call handler `svc` while preserving frozen memory (`Perm.frozen`),
    `tpidrEl0`, and `symtab`, matching architectural user-space supervisor-call invariants. -/
def evalSvc (svc : State → State) (s : State) : State :=
  let s' := svc s
  { s' with
    mem := ⟨fun a => if (s.mem.perm a).frozen then s.mem.cells a else s'.mem.cells a⟩
    tpidrEl0 := s.tpidrEl0
    symtab := s.symtab }

/-- A read-only AArch64 code image:
    - `base`: load address of `code`,
    - `code`: instruction bytes, with relocations applied,
    - `symbols`: defined symbols (demangled names) and their offsets from `base`,
    - `stubs`: extern functions and the offsets of their stubs,
    - `externs`: behaviour of extern functions, consulted at stub offsets,
    - `overrides`: replacement behaviour for defined functions, consulted at symbol offsets,
    - `svc`: supervisor-call (`SVC #0`) handler bundle, defaulting to `Syscall.standard`.
    See `Step.externHook` and `Step.exec`. -/
structure Program where
  base : BitVec 64 := 0#64
  code : List (BitVec 8) := []
  symbols : List (String × Nat) := []
  stubs : List (String × Nat) := []
  externs : String → Option (State → State) := fun _ => none
  overrides : String → Option (State → State) := fun _ => none
  svc : State → State := Syscall.standard

namespace Program

/-- The default `Program` is the empty program. -/
instance : Inhabited Program := ⟨{}⟩

/-- Empty code/hook `Program` configured with explicit supervisor-call handler `svc` (without
    referencing `Syscall.standard` in its constant closure). -/
def ofSvc (svc : State → State) : Program :=
  { base := 0#64, code := [], symbols := [], stubs := [],
    externs := fun _ => none, overrides := fun _ => none, svc := svc }

/-- Replace the supervisor-call handler of `prog` with `svc`. -/
def withSvc (prog : Program) (svc : State → State) : Program :=
  { prog with svc := svc }

/-- Execute a single decoded `Instr` under `prog`'s supervisor-call handler (`evalSvc prog.svc`). -/
def evalInst (prog : Program) (inst : Instr) (s : State) : State :=
  execInstWithSvc (evalSvc prog.svc) inst s

/-- Decompose a 32-bit little-endian instruction word into its 4 raw bytes `[b0, b1, b2, b3]`. -/
def wordToBytesLE (w : BitVec 32) : List (BitVec 8) :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- Build a `Program` from 32-bit little-endian machine code words loaded at `base`. Symbol
    addresses in `symbols` are absolute and must lie at or after `base`. -/
def ofWords (base : BitVec 64) (words : List (BitVec 32))
    (symbols : List (String × BitVec 64) := [])
    (svc : State → State := Syscall.standard) : Program :=
  { base, code := words.flatMap wordToBytesLE
    symbols := symbols.map fun (n, a) => (n, (a - base).toNat)
    stubs := [], externs := fun _ => none, overrides := fun _ => none
    svc }

/-- Offset of the defined symbol or extern stub `name`, or `none` if absent. -/
def findSymbol? (prog : Program) (name : String) : Option Nat :=
  ((prog.symbols.find? (·.1 == name)).orElse fun _ => prog.stubs.find? (·.1 == name)).map (·.2)

/-- Offset of symbol or stub `name` (`0` if absent). -/
def fnOff (prog : Program) (name : String) : Nat :=
  (prog.findSymbol? name).getD 0

/-- Address of symbol or stub `name` (`prog.base` if absent). -/
def fnAddr (prog : Program) (name : String) : BitVec 64 :=
  prog.base + BitVec.ofNat 64 (prog.fnOff name)

/-- `prog` relocated to base `b` with extern hooks `X` and override hooks `O`. -/
def rebase (prog : Program) (b : BitVec 64)
    (X : String → Option (State → State) := fun _ => none)
    (O : String → Option (State → State) := fun _ => none) : Program :=
  { prog with base := b, externs := X, overrides := O }

/-- The hook at offset `off`: an extern at a stub, or an override at a defined symbol. -/
def hookAtOff? (prog : Program) (off : Nat) : Option (State → State) :=
  (prog.stubs.findSome? fun (n, o) => if o == off then prog.externs n else none).or
    (prog.symbols.findSome? fun (n, o) => if o == off then prog.overrides n else none)

/-- The hook, if any, whose entry point is `pc`. -/
def externAt? (prog : Program) (pc : BitVec 64) : Option (State → State) :=
  prog.hookAtOff? (pc - prog.base).toNat

/-- Read a 32-bit little-endian word at byte offset `off` of `prog.code`. Instructions are
    4-byte aligned, so an offset that is not a multiple of 4 reads `none`. -/
def readWordOff (prog : Program) (off : Nat) : Option (BitVec 32) :=
  if off % 4 ≠ 0 then none else
  match prog.code.drop off with
  | b0 :: b1 :: b2 :: b3 :: _ => some (b3 ++ b2 ++ b1 ++ b0)
  | _ => none

/-- Fetch and decode the instruction at `pc` from the code image `prog.code` (not from
    memory: `Step` uses `fetchMem`, which agrees with `fetch` when the code is loaded,
    `CodeLoaded`). At a hooked entry point (`prog.externAt? pc = some f`) `fetch` returns
    `none` so that `Step.externHook` handles the call in one step. An address below `base` wraps to
    an offset past the end of `code` (`Obj.CodeBlock.Placeable.no_wrap` ensures the code does not
    wrap), so it fetches `none`. -/
def fetch (prog : Program) (pc : BitVec 64) : Option Instr :=
  if (prog.externAt? pc).isSome then none
  else (prog.readWordOff (pc - prog.base).toNat).bind decode

/-- Fetch and decode the instruction at `pc` from memory `m`: the 32-bit little-endian word at
    `pc`, which must be 4-byte aligned and executable (`Memory.canExec`); otherwise `none`
    (the real machine faults). At a hooked entry point `fetchMem` returns `none`, as `fetch`
    does. -/
def fetchMem (prog : Program) (m : Memory) (pc : BitVec 64) : Option Instr :=
  if (prog.externAt? pc).isSome then none
  else if pc.toNat % 4 ≠ 0 then none
  else if !m.canExec pc 4 then none
  else decode (m.read32 pc)

/-- The code of `prog` is loaded in memory `m`: byte `i` of `prog.code` is at `prog.base + i`,
    mapped read-execute (`Perm.rx`). The base is 4-byte aligned and the code does not wrap
    around the address space. This depends only on `prog.base` and `prog.code`.

    Irreducible, so that no `simp` / `decide` / `whnf` in client proofs unfolds it (and the
    potentially large `prog.code` list). Reason about it via `Program.codeLoaded_iff` and the
    accessor lemmas in `ProofLib.Invariant`. -/
@[irreducible] def CodeLoaded (prog : Program) (m : Memory) : Prop :=
  prog.base.toNat % 4 = 0 ∧ prog.base.toNat + prog.code.length ≤ 2 ^ 64 ∧
  ∀ (i : Nat) (hi : i < prog.code.length),
    m.read8 (prog.base + BitVec.ofNat 64 i) = prog.code[i] ∧
    m.perm (prog.base + BitVec.ofNat 64 i) = some Perm.rx ∧
    m.isLazyFree (prog.base + BitVec.ofNat 64 i) = false

/-- No hook has its entry point in `[off, off + len)`. -/
def hookFree (prog : Program) (off len : Nat) : Prop :=
  (prog.stubs.all fun (n, o) => !(off ≤ o && o < off + len) || (prog.externs n).isNone) = true ∧
  (prog.symbols.all fun (n, o) => !(off ≤ o && o < off + len) || (prog.overrides n).isNone) = true

instance (prog : Program) (off len : Nat) : Decidable (prog.hookFree off len) :=
  inferInstanceAs (Decidable (_ = true ∧ _ = true))

/-- `prog.code` holds `words` at byte offset `off` and no hook has its entry point there.
    The range must fit below `2 ^ 64`. This does not depend on `prog.base`. -/
def hasWordsOff (prog : Program) (off : Nat) (words : List (BitVec 32)) : Prop :=
  off + 4 * words.length ≤ 2 ^ 64 ∧
  (∀ (i : Nat) (hi : i < words.length), prog.readWordOff (off + 4 * i) = some (words[i]'hi)) ∧
  prog.hookFree off (4 * words.length)

/-- `prog.hasWordsOff` at the offset of absolute address `addr`. -/
def hasWords (prog : Program) (addr : BitVec 64) (words : List (BitVec 32)) : Prop :=
  prog.hasWordsOff (addr - prog.base).toNat words

/-- `prog.hasWords addr hex` (accepting either a `List (BitVec 32)` or a hex string literal
    elaborated at elaboration time). -/
def hasCode (prog : Program) (addr : BitVec 64) (hex : List (BitVec 32)) : Prop :=
  prog.hasWords addr hex

/-- Decision procedure for bounded universal quantification `∀ i (hi : i < n), P i hi`. -/
def decidableForallLT : (n : Nat) → (P : (i : Nat) → i < n → Prop) →
    [∀ i hi, Decidable (P i hi)] → Decidable (∀ i (hi : i < n), P i hi)
  | 0, _, _ => isTrue (fun _ hi => absurd hi (Nat.not_lt_zero _))
  | n + 1, P, inst =>
    match decidableForallLT n (fun i hi => P i (Nat.lt_succ_of_lt hi)) with
    | isFalse hnot => isFalse (fun hall => hnot (fun i hi => hall i (Nat.lt_succ_of_lt hi)))
    | isTrue hall =>
      match inst n (Nat.lt_succ_self n) with
      | isTrue hn => isTrue (fun i hi =>
        match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with
        | Or.inl heq => heq ▸ hn
        | Or.inr hlt => hall i hlt)
      | isFalse hnotn => isFalse (fun hall => hnotn (hall n (Nat.lt_succ_self n)))

instance (prog : Program) (off : Nat) (words : List (BitVec 32)) :
    Decidable (prog.hasWordsOff off words) :=
  @instDecidableAnd _ _ (Nat.decLe _ _)
    (@instDecidableAnd _ _
      (decidableForallLT words.length (fun i hi =>
        prog.readWordOff (off + 4 * i) = some (words[i]'hi)))
      inferInstance)

instance (prog : Program) (addr : BitVec 64) (words : List (BitVec 32)) :
    Decidable (prog.hasWords addr words) :=
  inferInstanceAs (Decidable (prog.hasWordsOff _ words))

instance (prog : Program) (addr : BitVec 64) (hex : List (BitVec 32)) :
    Decidable (prog.hasCode addr hex) :=
  inferInstanceAs (Decidable (prog.hasWords addr hex))

end Program

/-- Trusted small-step operational semantics relation `Step prog s s'`.

    At an extern entry point (`prog.externAt? s.pc = some f`) exactly one of `extern` /
    `extern_fault` applies (`fetchMem` returns `none` there); elsewhere exactly one of `exec` /
    `halt_unmapped` applies, so `Step` is deterministic. -/
inductive Step (prog : Program) : State → State → Prop where
  /-- Execute one instruction, fetched from memory and decoded, when `s.status = .Running`. -/
  | exec {s : State} {inst : Instr}
      (h_run : s.status = .Running)
      (h_fetch : prog.fetchMem s.mem s.pc = some inst) :
      Step prog s (prog.evalInst inst s)
  /-- Halt when no valid instruction can be fetched at `s.pc` (unmapped, not executable,
      misaligned, or not decodable) and `s.pc` is not a hooked entry point. This includes an
      extern stub with no `externs` entry. -/
  | halt_unmapped {s : State}
      (h_run : s.status = .Running)
      (h_fetch : prog.fetchMem s.mem s.pc = none)
      (h_ext : prog.externAt? s.pc = none) :
      Step prog s { s with status := .Halted }
  /-- A call to a hooked function at `s.pc` takes effect in one step: the architectural
      state `s` is mapped to `f s`, provided `f` keeps every frozen (mapped, non-writable)
      byte (`Memory.KeepsFrozen`) and preserves `symtab`, as any real function must. Otherwise
      `extern_fault` applies. Beyond that the semantics places no constraint on `f`; whoever
      supplies it is responsible for `f` representing a sensible return. -/
  | externHook {s : State} {f : State → State}
      (h_run : s.status = .Running)
      (h_ext : prog.externAt? s.pc = some f)
      (h_keep : s.mem.KeepsFrozen (f s).mem)
      (h_symtab : (f s).symtab = s.symtab := by rfl) :
      Step prog s (f s)
  /-- A hook that would change a frozen byte (e.g. code or read-only data) or the symbol
      table faults instead, leaving the state unchanged except for the status. -/
  | extern_fault {s : State} {f : State → State}
      (h_run : s.status = .Running)
      (h_ext : prog.externAt? s.pc = some f)
      (h_nkeep : ¬ (s.mem.KeepsFrozen (f s).mem ∧ (f s).symtab = s.symtab)) :
      Step prog s { s with status := .Exception "extern hook modified read-only memory or symbol table" }

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps (prog : Program) : State → State → Prop where
  | refl (s : State) : Steps prog s s
  | step {s1 s2 s3 : State} (h1 : Step prog s1 s2) (h2 : Steps prog s2 s3) : Steps prog s1 s3

/-- Reflexive-transitive execution of `prog` that stops as soon as `stop s` holds:
    no intermediate state prior to the final state satisfies `stop`. -/
inductive StepsUntil (prog : Program) (stop : State → Prop) : State → State → Prop where
  | refl (s : State) : StepsUntil prog stop s s
  | step {s1 s2 s3 : State}
      (h_cont : ¬ stop s1)
      (h_step : Step prog s1 s2)
      (h_rest : StepsUntil prog stop s2 s3) :
      StepsUntil prog stop s1 s3

end Arm64


