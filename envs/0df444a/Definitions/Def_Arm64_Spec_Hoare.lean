-- Prove2me | Definitions.Def_Arm64_Spec_Hoare
-- name    : Arm64_Spec_Hoare
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:15:13.024923+00:00
-- url     : https://prove2.me/theorems/1c274150-b906-4ec2-bdb4-39dfc594ecfa
-- title:
--   Arm64.Trusted.Spec.Hoare — ARM64 Subroutine Specifications
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Spec/Hoare.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/Hoare.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Spec/Hoare.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/Hoare.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Spec/Hoare.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_Syntax
public import Definitions.Def_Arm64_ISA_Memory
public import Definitions.Def_Arm64_ISA_State
public import Definitions.Def_Arm64_ISA_Decode
public import Definitions.Def_Arm64_ISA_Eval
public import Definitions.Def_Arm64_ISA_Semantics
public import Definitions.Def_Arm64_Spec_SepLogic

/-!
# ARM64 Subroutine Specifications

Relational separation-logic contracts (`Spec`), AAPCS64 calling-convention invariants
(`CalleeSavedPreserved`, `CallingConventionPreserved`, `Returned`, `SubroutineStop`,
`SubroutineOutcome`), execution judgments (`reaches_stop`, `safe_until`, `safe_reaches`,
`reaches_outcome`, `exits_with`), framed Hoare triples (`subroutine_ok`, `safe_subroutine_ok`,
`exit_ok`, `HookOk`, `HookSat`), symbol-addressed program judgments (`Program.subroutineOk`,
`Program.safeSubroutineOk`, `Program.exitOk`), and subroutine-to-hook primitives
(`subroutineHook`).

`reaches_outcome` and `subroutine_ok` are defined inside a plain `public section` (not
`@[expose]`), so client modules see only their abstract signatures while `ProofLib` rules and
adequacy tests in `Arm64/Testing` import `all Arm64.Trusted.Spec.Hoare` explicitly. Frame,
consequence, and bare-machine adequacy properties are checked in
[`Arm64/Testing/Tours/SepLogicLawsTour.lean`](../../Testing/Tours/SepLogicLawsTour.lean) and
[`Arm64/Testing/Tours/SpecAdequacyTour.lean`](../../Testing/Tours/SpecAdequacyTour.lean).

All judgments assume `prog.CodeLoaded s0.mem` and quantify over an arbitrary frame `R : SepProp`.
`subroutine_ok` states total correctness: from any 16-byte-aligned `.Running` entry state
satisfying `spec.pre x s0 ∗ R`, execution terminates in a valid `SubroutineOutcome`.
`safe_subroutine_ok` states safety-style partial correctness: execution either reaches a valid
`SubroutineOutcome` or runs forever in `.Running` with a `Step` successor at every reachable
state, so faulting (`.Exception`) and halting (`.Halted`) runs are excluded.
-/

namespace Arm64

@[expose] public section

/-! ## AAPCS64 Callee-Saved Registers and Calling Convention Invariants -/

/-- Snapshot of the 8 AAPCS64 callee-saved SIMD registers (`D8..D15`, low 64 bits `[63:0]` of `V8..V15`)
    extracted directly from the `VRegFile` component of the machine state. -/
def VRegFile.calleeSaved (vf : VRegFile) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  ((vf.read 8#5).truncate 64, (vf.read 9#5).truncate 64,
   (vf.read 10#5).truncate 64, (vf.read 11#5).truncate 64,
   (vf.read 12#5).truncate 64, (vf.read 13#5).truncate 64,
   (vf.read 14#5).truncate 64, (vf.read 15#5).truncate 64)

/-- Snapshot of the 8 AAPCS64 callee-saved SIMD registers (`D8..D15`, low 64 bits `[63:0]` of `V8..V15`). -/
abbrev calleeSavedVRegs (s : State) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  VRegFile.calleeSaved s.vregs

/-- AAPCS64 callee-saved SIMD registers (`D8..D15`, i.e., low 64 bits `[63:0]` of `V8..V15`)
    have identical values in `s0` and `sf`. -/
@[simp]
abbrev CalleeSavedVRegsPreserved (s0 sf : State) : Prop :=
  calleeSavedVRegs sf = calleeSavedVRegs s0

/-- AAPCS64 callee-saved registers have identical values in `s0` and `sf`:
    general-purpose registers `X19..X28`, frame pointer `X29` (`fp`), and the low
    64 bits (`D8..D15` / `V8..V15[63:0]`) of SIMD registers `V8..V15`. -/
def CalleeSavedPreserved (s0 sf : State) : Prop :=
  sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) ∧
  sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) ∧
  sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  sf.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  sf.readReg64 Reg.fp = s0.readReg64 Reg.fp ∧
  calleeSavedVRegs sf = calleeSavedVRegs s0

/-- AAPCS64 calling-convention register preservation between entry state `s0` and return state `sf`:
    1. Stack pointer is restored (`sf.sp = s0.sp`),
    2. Callee-saved general-purpose registers `X19..X28`, frame pointer `X29` (`fp`), and low
       64 bits of SIMD registers `V8..V15` (`D8..D15`) are preserved.
    (Memory and parent-stack preservation are enforced automatically via the separation-logic frame `R`.) -/
def CallingConventionPreserved (s0 sf : State) : Prop :=
  sf.sp = s0.sp ∧
  CalleeSavedPreserved s0 sf

/-- The machine has returned to the caller of entry state `s0`: `pc` is at `s0.readReg64 Reg.lr`,
    the stack pointer `sp` is restored to `s0.sp`, and `status = .Running`. -/
def Returned (s0 s : State) : Prop :=
  s.pc = s0.readReg64 Reg.lr ∧ s.sp = s0.sp ∧ s.status = .Running

/-- Terminal stopping condition for a subroutine entered at `s0`: normal return (`Returned s0 s`),
    panic (`s.status = .Panicked`), process exit (`s.status = .Exited code`), or out-of-memory
    in `brk`/`mmap`/`mprotect`/`mremap` (`s.status = .OutOfMemory`). -/
def SubroutineStop (s0 s : State) : Prop :=
  Returned s0 s ∨ s.status = .Panicked ∨ (∃ code, s.status = .Exited code) ∨ s.status = .OutOfMemory

/-! ## Execution Judgments -/

/-- Total-correctness reachability to a stop condition `stop`: if the code of `prog` is loaded in
    `s0` (`prog.CodeLoaded s0.mem`), execution of `prog` from `s0` reaches a first state `sf`
    satisfying `stop sf`, and at that state `Q sf` holds. -/
def reaches_stop (prog : Program) (stop : State → Prop) (s0 : State) (Q : State → Prop) : Prop :=
  prog.CodeLoaded s0.mem →
    ∃ sf, StepsUntil prog stop s0 sf ∧ stop sf ∧ Q sf

/-- Safety-style partial correctness up to a stop condition `stop`: if the code of `prog` is
    loaded in `s0`, every state `s` reachable from `s0` before (or at) the first state
    satisfying `stop` is either:
    - a stopping state (`stop s`) where `Q s` holds,
    - a terminal out-of-memory state (`s.status = .OutOfMemory`) satisfying `oom s` (default `False`), or
    - a `.Running` non-stopping state (`¬ stop s ∧ s.status = .Running`).
    A run that faults (`.Exception`) or halts (`.Halted`) before satisfying `stop` does not satisfy
    `safe_until` vacuously. Termination is not required. -/
def safe_until (prog : Program) (stop : State → Prop) (s0 : State) (Q : State → Prop)
    (oom : State → Prop := fun _ => False) : Prop :=
  prog.CodeLoaded s0.mem →
    ∀ s, StepsUntil prog stop s0 s →
      (stop s ∧ Q s) ∨ (s.status = .OutOfMemory ∧ oom s) ∨ (¬ stop s ∧ s.status = .Running)

/-- Safety-style partial correctness up to the first visit to `target_pc`. -/
abbrev safe_until_pc (prog : Program) (target_pc : BitVec 64) (s0 : State) (post : State → Prop)
    (oom : State → Prop := fun _ => False) : Prop :=
  safe_until prog (fun s => s.pc = target_pc) s0 (fun sf => sf.status = .Running ∧ post sf) oom

/-- Safety-style partial correctness for reachability (`Steps`): if the code of `prog` is
    loaded in `s0`, either execution from `s0` reaches a state `sf` satisfying `Q sf`, or
    execution runs forever (`∀ s, Steps prog s0 s → s.status = .Running ∧ ∃ s', Step prog s s'`)
    without faulting, halting, panicking, or exiting. -/
def safe_reaches (prog : Program) (s0 : State) (Q : State → Prop) : Prop :=
  prog.CodeLoaded s0.mem →
    (∃ sf, Steps prog s0 sf ∧ Q sf) ∨
    (∀ s, Steps prog s0 s → s.status = .Running ∧ ∃ s', Step prog s s')

/-! ## Relational Specifications and Subroutine Judgments -/

/-- Separation-logic specification parameterized by logical ghost state `α` (defaulting to `Unit`).
    - `pre`: Precondition `SepProp` on ghost value `x` and entry state `s0`
      (evaluated as `s0.mem ⊨ spec.pre x s0 ∗ R`).
    - `post`: Relational postcondition `SepProp` on ghost value `x`, entry state `s0`, and
      return state `sf` (evaluated as `sf.mem ⊨ spec.post x s0 sf ∗ R`).
    - `onPanic`: Relational postcondition `SepProp` when the subroutine panics (`sf.status = .Panicked`);
      defaults to `⌜False⌝` (panicking is forbidden).
    - `onExit`: Relational postcondition `SepProp` when the subroutine exits (`sf.status = .Exited code`);
      defaults to `⌜False⌝` (process exit is forbidden).
    - `onOom`: Relational postcondition `SepProp` when the subroutine exhausts virtual address
      space or `State.physMemAvail` in `brk`/`mmap`/`mprotect`/`mremap` (`sf.status = .OutOfMemory`);
      defaults to `⌜False⌝` (out-of-memory is forbidden). -/
structure Spec (α : Type := Unit) where
  pre     : α → State → SepProp
  post    : α → State → State → SepProp
  onPanic : α → State → State → SepProp := fun _ _ _ => ⌜False⌝
  onExit  : α → BitVec 64 → State → State → SepProp := fun _ _ _ _ => ⌜False⌝
  onOom   : α → State → State → SepProp := fun _ _ _ => ⌜False⌝

namespace Spec

/-- Permit panicking (`sf.status = .Panicked`) whenever `φ x s0 sf` holds, with arbitrary memory. -/
def allowPanicWhen {α : Type} (spec : Spec α) (φ : α → State → State → Prop) : Spec α :=
  { spec with onPanic := fun x s0 sf => ⌜φ x s0 sf⌝ ∗ anyHeap }

/-- Permit out-of-memory termination (`sf.status = .OutOfMemory`) whenever `φ x s0 sf` holds. -/
def allowOomWhen {α : Type} (spec : Spec α) (φ : α → State → State → Prop) : Spec α :=
  { spec with onOom := fun x s0 sf => ⌜φ x s0 sf⌝ }

/-- Permit out-of-memory termination (`sf.status = .OutOfMemory`), preserving the caller frame `R`. -/
def allowOom {α : Type} (spec : Spec α) : Spec α :=
  { spec with onOom := fun _ _ _ => ⌜True⌝ }

end Spec

/-- Terminal outcome of a subroutine execution from entry state `s0` to final state `sf` with frame `R`:
    - Normal return (`Returned s0 sf`): `sf.pc = s0.readReg64 Reg.lr`, `sf.sp = s0.sp`,
      `sf.status = .Running`, `CallingConventionPreserved s0 sf`, and `sf.mem ⊨ spec.post x s0 sf ∗ R`;
    - Panic (`sf.status = .Panicked`): `sf.mem ⊨ spec.onPanic x s0 sf ∗ R`;
    - Process exit (`sf.status = .Exited code`): `sf.mem ⊨ spec.onExit x code s0 sf ∗ R`;
    - Out of virtual address space or `State.physMemAvail` in `brk`/`mmap`/`mprotect`/`mremap`
      (`sf.status = .OutOfMemory`): `sf.mem ⊨ spec.onOom x s0 sf ∗ R`. -/
def SubroutineOutcome {α : Type} (spec : Spec α) (x : α) (R : SepProp) (s0 sf : State) : Prop :=
  (Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧ (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∨
  (sf.status = .Panicked ∧ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R)) ∨
  (∃ code, sf.status = .Exited code ∧ (sf.mem ⊨ spec.onExit x code s0 sf ∗ R)) ∨
  (sf.status = .OutOfMemory ∧ (sf.mem ⊨ spec.onOom x s0 sf ∗ R))

/-- Standard AAPCS64 subroutine entry invariant: the machine is `.Running` at `entry_pc` with a
    16-byte-aligned stack pointer (`s0.spAligned = true`, per AAPCS64 section 6.2.2). -/
def AapcsEntry (s0 : State) (entry_pc : BitVec 64) : Prop :=
  s0.pc = entry_pc ∧ s0.status = .Running ∧ s0.spAligned = true

end -- @[expose] public section

public section

/-- If the code of `prog` is loaded in `s` (`prog.CodeLoaded s.mem`), execution of `prog` from
    current state `s` via `Steps` reaches a terminal subroutine outcome `sf` for entry state `s0`
    (`SubroutineOutcome spec x R s0 sf`). -/
def reaches_outcome (prog : Program) {α : Type} (spec : Spec α) (x : α) (R : SepProp) (s0 s : State) : Prop :=
  prog.CodeLoaded s.mem → ∃ sf, Steps prog s sf ∧ SubroutineOutcome spec x R s0 sf

/-- Total-correctness framed AAPCS64 subroutine Hoare triple: for all ghost values `x : α`,
    separation-logic frames `R : SepProp`, and entry states `s0` at `s0.pc = entry_pc` with
    `s0.status = .Running`, `s0.mem ⊨ spec.pre x s0 ∗ R`, and 16-byte-aligned stack pointer
    `s0.spAligned = true`, execution of `prog` terminates in a state `sf` satisfying
    `SubroutineOutcome spec x R s0 sf`. -/
def subroutine_ok {α : Type} (prog : Program) (entry_pc : BitVec 64) (spec : Spec α) : Prop :=
  ∀ (x : α) (R : SepProp) (s0 : State),
    s0.pc = entry_pc →
    s0.status = .Running →
    (s0.mem ⊨ spec.pre x s0 ∗ R) →
    s0.spAligned = true →
    reaches_outcome prog spec x R s0 s0

end -- public section

@[expose] public section

/-- Function-pointer specification predicate at code address `addr`: reducible alias for
    `subroutine_ok prog addr spec` usable in struct representation predicates and callback
    preconditions. -/
abbrev FnPtrSpec {α : Type} (prog : Program) (addr : BitVec 64) (spec : Spec α) : Prop :=
  subroutine_ok prog addr spec

/-- Safety-style partial-correctness framed AAPCS64 subroutine Hoare triple: from any valid
    entry state (`AapcsEntry s0 entry_pc`, `s0.mem ⊨ spec.pre x s0 ∗ R`), either execution
    reaches a valid terminal outcome (`SubroutineOutcome spec x R s0 sf`) or it runs forever
    in `.Running` status without faulting, halting, panicking, or exiting.
    Termination is not required.

    With a trivial `spec.post`, this states memory safety of the subroutine: it never accesses
    unpermitted memory, and on return it preserves any frame `R` outside its precondition
    footprint. -/
def safe_subroutine_ok {α : Type} (prog : Program) (entry_pc : BitVec 64) (spec : Spec α) : Prop :=
  ∀ (x : α) (R : SepProp) (s0 : State),
    AapcsEntry s0 entry_pc →
    (s0.mem ⊨ spec.pre x s0 ∗ R) →
    safe_reaches prog s0 (SubroutineOutcome spec x R s0)

/-- Partial-correctness function-pointer specification predicate at code address `addr`:
    reducible alias for `safe_subroutine_ok prog addr spec`. -/
abbrev SafeFnPtrSpec {α : Type} (prog : Program) (addr : BitVec 64) (spec : Spec α) : Prop :=
  safe_subroutine_ok prog addr spec

/-- If the code of `prog` is loaded in `s0` (`prog.CodeLoaded s0.mem`), execution of `prog` from
    `s0` via `Steps` terminates via `exit` or `exit_group` with exit status `code`
    (`sf.status = .Exited code`) in a state `sf` satisfying `post sf` (or terminates in
    `sf.status = .OutOfMemory` satisfying `oom sf`, default `False`). -/
def exits_with (prog : Program) (code : BitVec 64) (s0 : State) (post : State → Prop)
    (oom : State → Prop := fun _ => False) : Prop :=
  prog.CodeLoaded s0.mem →
    ∃ sf, Steps prog s0 sf ∧ ((sf.status = .Exited code ∧ post sf) ∨ (sf.status = .OutOfMemory ∧ oom sf))

/-- Framed total-correctness Hoare contract for programs or entry points that terminate via `exit` / `exit_group`:
    For all ghost values `x : α`, frames `R : SepProp`, and initial states `s0` with
    `s0.pc = entry_pc`, `s0.status = .Running`, and `s0.mem ⊨ spec.pre x s0 ∗ R`,
    execution of `prog` terminates with `sf.status = .Exited (code x)`
    in a state `sf` satisfying `sf.mem ⊨ spec.post x s0 sf ∗ R`
    (or terminates in `.OutOfMemory` satisfying `sf.mem ⊨ spec.onOom x s0 sf ∗ R`). -/
def exit_ok {α : Type} (prog : Program) (entry_pc : BitVec 64) (code : α → BitVec 64) (spec : Spec α) : Prop :=
  ∀ (x : α) (R : SepProp) (s0 : State),
    s0.pc = entry_pc →
    s0.status = .Running →
    (s0.mem ⊨ spec.pre x s0 ∗ R) →
    exits_with prog (code x) s0
      (fun sf => sf.mem ⊨ spec.post x s0 sf ∗ R)
      (fun sf => sf.mem ⊨ spec.onOom x s0 sf ∗ R)

/-! ## Extern Hook Contracts -/

/-- A hook `f` meets `spec`: from a running state `s0` at the hook's entry satisfying the
    precondition with any frame `R` and 16-byte aligned `sp`, `f s0` keeps frozen memory,
    preserves the symbol table, and satisfies `SubroutineOutcome spec x R s0 (f s0)`. -/
def HookOk {α : Type} (f : State → State) (spec : Spec α) : Prop :=
  ∀ (x : α) (R : SepProp) (s0 : State),
    s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
    s0.mem.KeepsFrozen (f s0).mem ∧ (f s0).symtab = s0.symtab ∧
    SubroutineOutcome spec x R s0 (f s0)

/-- Hook `name` is present in `hooks` and meets `spec`. -/
def HookSat {α : Type} (hooks : String → Option (State → State)) (name : String)
    (spec : Spec α) : Prop :=
  ∃ f, hooks name = some f ∧ HookOk f spec

namespace Program

/-- Position-independent code assumption by symbol name: `prog` contains the contiguous sequence
    of 32-bit instruction words `hex` at `prog.fnOff name`. Independent of `prog.base`. -/
def codeAt (prog : Program) (name : String) (hex : List (BitVec 32)) : Prop :=
  prog.hasWordsOff (prog.fnOff name) hex

instance (prog : Program) (name : String) (hex : List (BitVec 32)) :
    Decidable (prog.codeAt name hex) :=
  inferInstanceAs (Decidable (prog.hasWordsOff (prog.fnOff name) hex))

/-- Code assumption by symbol name with a pinned offset from `prog.base`: `prog.fnOff name = off`
    and `prog.codeAt name hex`. Used when a function contains PC-relative references (`adrp`,
    `bl`, `b`) to other symbols that fix the distance between them. Independent of `prog.base`. -/
def codeAtOff (prog : Program) (name : String) (off : Nat) (hex : List (BitVec 32)) : Prop :=
  prog.fnOff name = off ∧ prog.codeAt name hex

instance (prog : Program) (name : String) (off : Nat) (hex : List (BitVec 32)) :
    Decidable (prog.codeAtOff name off hex) :=
  inferInstanceAs (Decidable (prog.fnOff name = off ∧ prog.codeAt name hex))

/-- Code assumption by symbol name with a pinned absolute entry address: `prog.fnAddr name = addr`
    and `prog.codeAt name hex`. Prefer `codeAtOff` unless `prog.base` is fixed. -/
def codeAtAddr (prog : Program) (name : String) (addr : BitVec 64) (hex : List (BitVec 32)) : Prop :=
  prog.fnAddr name = addr ∧ prog.codeAt name hex

instance (prog : Program) (name : String) (addr : BitVec 64) (hex : List (BitVec 32)) :
    Decidable (prog.codeAtAddr name addr hex) :=
  inferInstanceAs (Decidable (prog.fnAddr name = addr ∧ prog.codeAt name hex))

end Program

/-- Where a function's code is pinned, if anywhere. -/
inductive FnPin where
  /-- Anywhere (`Program.codeAt`). -/
  | none
  /-- At a fixed offset from `prog.base` (`Program.codeAtOff`). -/
  | off (off : Nat)
  /-- At a fixed absolute address (`Program.codeAtAddr`). -/
  | addr (addr : BitVec 64)

/-- Specification of a function's expected machine code by symbol name `fnName`,
    32-bit instruction word sequence `hex` (elaborated from a hex string literal at
    elaboration time or given directly as `List (BitVec 32)`), and optional pinned
    location `pin` (for functions with PC-relative references to other symbols). -/
structure FnCode where
  fnName : String
  hex : List (BitVec 32)
  pin : FnPin := .none

namespace FnCode

/-- Alias for `c.hex` as a list of 32-bit instruction words. -/
abbrev words (c : FnCode) : List (BitVec 32) := c.hex

/-- Construct a position-independent `FnCode` specification for symbol `fnName`. -/
def ofFn (fnName : String) (hex : List (BitVec 32)) : FnCode :=
  { fnName, hex, pin := .none }

/-- Construct an `FnCode` specification for symbol `fnName` at entry address `addr`. -/
def atAddr (fnName : String) (addr : BitVec 64) (hex : List (BitVec 32)) : FnCode :=
  { fnName, hex, pin := .addr addr }

/-- `prog` satisfies this function code specification. -/
def holds (spec : FnCode) (prog : Program) : Prop :=
  match spec.pin with
  | .none => prog.codeAt spec.fnName spec.hex
  | .off off => prog.codeAtOff spec.fnName off spec.hex
  | .addr addr => prog.codeAtAddr spec.fnName addr spec.hex

instance : (spec : FnCode) → (prog : Program) → Decidable (spec.holds prog)
  | { fnName, hex, pin := .none }, prog =>
    inferInstanceAs (Decidable (prog.codeAt fnName hex))
  | { fnName, hex, pin := .off off }, prog =>
    inferInstanceAs (Decidable (prog.codeAtOff fnName off hex))
  | { fnName, hex, pin := .addr addr }, prog =>
    inferInstanceAs (Decidable (prog.codeAtAddr fnName addr hex))

end FnCode

/-- A bundle of `FnCode` specifications. -/
abbrev CodeBundle := List FnCode

namespace Program

/-- `prog` satisfies every `FnCode` specification in `specs`. -/
def hasCodeBundle (prog : Program) : List FnCode → Prop
  | [] => True
  | [s] => s.holds prog
  | s :: s2 :: ss => s.holds prog ∧ prog.hasCodeBundle (s2 :: ss)

instance instDecidableHasCodeBundle (prog : Program) : (specs : List FnCode) →
    Decidable (prog.hasCodeBundle specs)
  | [] => isTrue trivial
  | [s] => inferInstanceAs (Decidable (s.holds prog))
  | s :: s2 :: ss =>
    @instDecidableAnd (s.holds prog) (prog.hasCodeBundle (s2 :: ss))
      (inferInstanceAs (Decidable (s.holds prog)))
      (instDecidableHasCodeBundle prog (s2 :: ss))

end Program

/-- A position-independent subroutine specification parameterized by the load base `base : BitVec 64`. -/
abbrev BaseSpec (α : Type := Unit) := BitVec 64 → Spec α

/-- Typeclass unifying base-independent `Spec α` and base-dependent `BaseSpec α := BitVec 64 → Spec α`
    so program judgments (`Program.subroutineOk`, `Program.rawSubroutineOk`,
    `Program.safeSubroutineOk`, `Program.relocSubroutineOk`, `Program.alignedSubroutineOk`,
    `Obj.PlacedLib.subroutineOk`) accept both uniformly. A `c_spec` / `rust_spec` declaring
    `load_addr b` produces a `BaseSpec α` (after applying its `ctx` arguments). -/
class ToBaseSpec (S : Type) (α : outParam Type) where
  toSpec : S → BitVec 64 → Spec α

attribute [reducible] ToBaseSpec.toSpec

/-- Base-independent specs. Also the default instance, so an anonymous structure instance
    `prog.subroutineOk "f" { pre := .., post := .. }` elaborates at `S := Spec α`. -/
@[reducible, default_instance] instance instToBaseSpecId {α : Type} : ToBaseSpec (Spec α) α where
  toSpec s _ := s

@[reducible] instance instToBaseSpecFn {α : Type} : ToBaseSpec (BitVec 64 → Spec α) α where
  toSpec f b := f b

/-- Position-independent subroutine correctness by symbol name:
    `subroutine_ok prog (prog.fnAddr fnName) spec`. A base-dependent spec (`BaseSpec α`, e.g. from
    `load_addr b`) is instantiated at the program's load base `prog.base`; for `spec : Spec α` this
    is definitionally `subroutine_ok prog (prog.fnAddr fnName) spec`. -/
abbrev Program.subroutineOk {S α : Type} [ToBaseSpec S α] (prog : Program) (fnName : String)
    (spec : S) : Prop :=
  subroutine_ok prog (prog.fnAddr fnName) (ToBaseSpec.toSpec spec prog.base)

/-- Position-independent safety-style partial-correctness subroutine contract by symbol name:
    `safe_subroutine_ok prog (prog.fnAddr fnName) spec`. A base-dependent spec (`BaseSpec α`) is
    instantiated at the program's load base `prog.base`. -/
abbrev Program.safeSubroutineOk {S α : Type} [ToBaseSpec S α] (prog : Program) (fnName : String)
    (spec : S) : Prop :=
  safe_subroutine_ok prog (prog.fnAddr fnName) (ToBaseSpec.toSpec spec prog.base)

/-- Alias for `Program.subroutineOk`: `subroutine_ok` at `prog.fnAddr fnName`. -/
abbrev fn_subroutine_ok {S α : Type} [ToBaseSpec S α] (prog : Program) (fnName : String)
    (spec : S) : Prop :=
  prog.subroutineOk fnName spec

/-- Position-independent subroutine correctness with universal quantification over the
    load base `base : BitVec 64` built in:
    for every `base : BitVec 64`, `subroutine_ok` holds for `prog.rebase base externs overrides`
    at `(prog.rebase base externs overrides).fnAddr fnName` with `ToBaseSpec.toSpec spec base`. -/
abbrev Program.relocSubroutineOk {S α : Type} [ToBaseSpec S α] (prog : Program)
    (fnName : String) (spec : S)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none) : Prop :=
  ∀ (base : BitVec 64),
    (prog.rebase base externs overrides).subroutineOk fnName (ToBaseSpec.toSpec spec base)

/-- Position-independent subroutine correctness across all 4KB page-aligned load bases
    `base : BitVec 64` (`base &&& 0xfff#64 = 0#64`, required by `ADRP` addressing). -/
abbrev Program.alignedSubroutineOk {S α : Type} [ToBaseSpec S α] (prog : Program)
    (fnName : String) (spec : S)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none) : Prop :=
  ∀ (base : BitVec 64), base &&& 0xfff#64 = 0#64 →
    (prog.rebase base externs overrides).subroutineOk fnName (ToBaseSpec.toSpec spec base)

/-- Position-independent `exit_ok` contract by symbol name:
    `exit_ok prog (prog.fnAddr fnName) code spec`. -/
abbrev Program.exitOk {α : Type} (prog : Program) (fnName : String)
    (code : α → BitVec 64) (spec : Spec α) : Prop :=
  exit_ok prog (prog.fnAddr fnName) code spec

/-- Conjunction of a list of propositions (without a trailing `∧ True` for non-empty lists). -/
def allHold : List Prop → Prop
  | [] => True
  | [p] => p
  | p :: p2 :: ps => p ∧ allHold (p2 :: ps)

/-- `prog` satisfies a bundle of program-indexed subroutine contracts
    (e.g. `[fun p => p.subroutineOk "foo" fooSpec, fun p => p.subroutineOk "baz" bazSpec]`). -/
def Program.calleesOk (prog : Program) (contracts : List (Program → Prop)) : Prop :=
  allHold (contracts.map (fun c => c prog))

/-! ## Subroutine-to-Hook Primitives -/

/-- Overlay `prog.code` with `Perm.rx` (preserving `m.isAnon` and clearing `lazyFree`) onto
    `[prog.base, prog.base + prog.code.length)` in `m`, leaving already-matching `Perm.rx` non-lazy
    code cells and all cells outside that region unchanged. -/
def loadCodeMem (prog : Program) (m : Memory) : Memory :=
  ⟨fun a =>
    if h : InRegion prog.base prog.code.length a then
      let b := prog.code[(a - prog.base).toNat]'h
      if m.perm a == some Perm.rx && !m.isLazyFree a && m.read8 a == b then m.cells a
      else some (some { Perm.rx with anon := m.isAnon a }, b)
    else
      m.cells a⟩

/-- Restore the cells of `m0` on `[prog.base, prog.base + prog.code.length)` into `mf`,
    keeping `mf`'s cells when permissions, `isLazyFree`, and bytes already match `m0` and outside
    that region. -/
def restoreCodeMem (prog : Program) (m0 mf : Memory) : Memory :=
  ⟨fun a =>
    if InRegion prog.base prog.code.length a then
      if mf.perm a == m0.perm a && mf.isLazyFree a == m0.isLazyFree a && mf.read8 a == m0.read8 a then mf.cells a
      else m0.cells a
    else
      mf.cells a⟩

/-- Entry state used when running `prog` at `entry_pc` as a hook from caller state `s0`:
    sets `pc := entry_pc`, `x30 (lr) := prog.base + 1#64` (an unaligned sentinel address
    where `fetchMem = none`), and overlays `prog.code` into memory via `loadCodeMem`. -/
def subroutineHookEntry (prog : Program) (entry_pc : BitVec 64) (s0 : State) : State :=
  ((s0.writeReg64 .lr (prog.base + 1#64)).setPC entry_pc).setMem (loadCodeMem prog s0.mem)

/-- Restore the caller's link register `lr := s0.readReg64 .lr`, return PC (when `sf'` stopped at
    the sentinel `prog.base + 1#64`), and code-region memory (`restoreCodeMem prog s0.mem sf'.mem`). -/
def subroutineHookExit (prog : Program) (s0 sf' : State) : State :=
  let lr0 := s0.readReg64 .lr
  let sf1 := if sf'.pc = prog.base + 1#64 ∧ sf'.status = .Running then sf'.setPC lr0 else sf'
  (sf1.writeReg64 .lr lr0).setMem (restoreCodeMem prog s0.mem sf'.mem)

open Classical in
/-- State-transformer hook (`State → State`) induced by running subroutine `entry_pc` of `prog`
    from `subroutineHookEntry prog entry_pc s0` until `SubroutineStop` and restoring the code
    region and link register via `subroutineHookExit`. -/
noncomputable def subroutineHook (prog : Program) (entry_pc : BitVec 64) (s0 : State) : State :=
  let s0' := subroutineHookEntry prog entry_pc s0
  if h : ∃ sf', StepsUntil prog (SubroutineStop s0') s0' sf' ∧ SubroutineStop s0' sf' then
    subroutineHookExit prog s0 (Classical.choose h)
  else
    s0

end -- @[expose] public section

end Arm64


