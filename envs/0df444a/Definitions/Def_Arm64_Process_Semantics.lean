-- Prove2me | Definitions.Def_Arm64_Process_Semantics
-- name    : Arm64_Process_Semantics
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:18:33.513829+00:00
-- url     : https://prove2.me/theorems/6ef13e60-723a-4eb9-8ab5-a40930272a59
-- title:
--   Arm64.Trusted.Process.Semantics — Whole-Binary ELF Process Semantics & Safety/Correctness Specifications
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Process/Semantics.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Semantics.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Process/Semantics.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Semantics.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Process/Semantics.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Process_Loader
public import Definitions.Def_Arm64_Process_Assumptions

/-!
# Whole-Binary ELF Process Semantics & Safety/Correctness Specifications (`Arm64.Trusted.Process.Semantics`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: Process-level termination and safety relations over `Arm64.Step` /
  `Arm64.Steps` (`Program.pureWithSvc`, `Program.pureMem`, `ProcessTerminatedOutcome`,
  `ProcessExitsWith`, the partial-correctness `ProcessPartialRunsTo`, `ProcessTerminates`, and the
  total `ProcessRunsTo := ProcessTerminates ∧ ProcessPartialRunsTo`) and the top-level
  whole-binary specifications over raw ELF bytes, an input precondition `pre`, and a relational
  postcondition `post`: total `ElfRunsTo` (with the wrappers `ElfCorrect` (exit `0`) and `ElfSafe`
  (exit `0`, trivial `post`)) and partial `ElfPartialRunsTo` (no termination claim).
- **When to read**: Read when auditing a whole-binary theorem statement (`ElfRunsTo`,
  `ElfPartialRunsTo`, `ElfCorrect`, `ElfSafe`). Proof rules, per-image stepping stones, and
  executable runners live in `ProofLib/Process.lean`.
-/

@[expose] public section

namespace Arm64

/-- Hook-free `Program` (`externs = none`, `overrides = none`) executing supervisor calls via
    bundle `svc`. Passing a minimal bundle (such as `Program.stdioCli` or `Program.fileIo`) to
    `ElfSafe`, `ElfCorrect`, or `ElfRunsTo` excludes unused syscall families from the
    specification's constant closure. -/
def Program.pureWithSvc (svc : State → State) : Program :=
  Program.ofSvc svc

/-- Hook-free `Program` trapping on every supervisor call (`noSyscalls`). -/
def Program.noSyscalls : Program := Program.pureWithSvc Arm64.noSyscalls

/-- Hook-free `Program` permitting only `write` (`Syscall.stdioWrite`). -/
def Program.stdioWrite : Program := Program.pureWithSvc Syscall.stdioWrite

/-- Hook-free `Program` permitting only `read`, `write`, `exit`, and `exit_group`
    (`Syscall.stdioCli`). -/
def Program.stdioCli : Program := Program.pureWithSvc Syscall.stdioCli

/-- Hook-free `Program` permitting stream/file-descriptor syscalls (`Syscall.fileIo`). -/
def Program.fileIo : Program := Program.pureWithSvc Syscall.fileIo

/-- Hook-free `Program` permitting virtual-memory allocator syscalls (`Syscall.alloc`). -/
def Program.alloc : Program := Program.pureWithSvc Syscall.alloc

/-- Default hook-free `Program` running the full modeled Linux syscall table (`Syscall.standard`).
    Under `Step Program.pureMem`, every instruction is fetched directly from executable memory
    `s.mem` (`Program.fetchMem`) with zero external hook assumptions. -/
abbrev Program.pureMem : Program := Program.pureWithSvc Syscall.standard

namespace Process

/-- State `sf` has terminated normally (`SYS_exit` / `SYS_exit_group` with `signal = none`) or
    by fatal signal (`ExecStatus.Signaled sig` with `exitCode = 128 + sig.toNat` and
    `signal = some sig.toNat`), yielding observable outcome `out`. -/
def ProcessTerminatedOutcome (sf : State) (out : ProcessOutcome) : Prop :=
  (∃ code, sf.status = .Exited code ∧ out = ProcessOutcome.ofState code sf) ∨
  (∃ sig, sf.status = .Signaled sig ∧ out = ProcessOutcome.ofSignal sig sf)

/-- Execution of `prog` from initial state `s0` reaches a terminated state `sf` (`.Exited` or
    `.Signaled`) whose observable outcome (`exitCode`, `signal`, `stdout`, `stderr`, `fs`) is
    `out`. -/
def ProcessExitsWith (prog : Program) (s0 : State) (out : ProcessOutcome) : Prop :=
  ∃ sf,
    Steps prog s0 sf ∧
    ProcessTerminatedOutcome sf out

/-- Partial correctness (step safety) of the process run of `prog` from initial state `s0`: every
    state `s'` reachable from `s0` under `Steps prog` either
    - has terminated (`ProcessTerminatedOutcome s' out`, `.Exited` or `.Signaled`) with
      `post out`,
    - has stopped with virtual or physical memory exhaustion (`.OutOfMemory` in
      `brk`/`mmap`/`mprotect`/`mremap`) and satisfies `oom s'` (default `False`), or
    - is `.Running` and can take a valid `Step prog` transition.
    In particular, no reachable state ever faults (`.Exception`), halts on unmapped/undecodable
    memory (`.Halted`), or hits a hook panic (`.Panicked`), and every terminated outcome satisfies
    `post`. This makes **no termination claim**: a run that never stops satisfies it as long as it
    never gets stuck, so `post` and `oom` constrain only the runs that do stop. -/
def ProcessPartialRunsTo (prog : Program) (s0 : State)
    (post : ProcessOutcome → Prop)
    (oom : State → Prop := fun _ => False) : Prop :=
  ∀ s', Steps prog s0 s' →
    (∃ out, ProcessTerminatedOutcome s' out ∧ post out) ∨
    (s'.status = .OutOfMemory ∧ oom s') ∨
    (s'.status = .Running ∧ ∃ s'', Step prog s' s'')

/-- Termination of the process run of `prog` from initial state `s0`: some run reaches a
    terminated state (`ProcessExitsWith prog s0 out`, `.Exited` or `.Signaled`) whose outcome
    satisfies `post out`, or stops with `.OutOfMemory` in a state satisfying `oom`
    (default `False`). -/
def ProcessTerminates (prog : Program) (s0 : State)
    (post : ProcessOutcome → Prop)
    (oom : State → Prop := fun _ => False) : Prop :=
  (∃ out, ProcessExitsWith prog s0 out ∧ post out) ∨
  (∃ sf, Steps prog s0 sf ∧ sf.status = .OutOfMemory ∧ oom sf)

/-- Total correctness of the process run of `prog` from initial state `s0`: the run terminates
    (`ProcessTerminates`) and satisfies step safety (`ProcessPartialRunsTo`) with the same `post`
    and `oom`. -/
def ProcessRunsTo (prog : Program) (s0 : State)
    (post : ProcessOutcome → Prop)
    (oom : State → Prop := fun _ => False) : Prop :=
  ProcessTerminates prog s0 post oom ∧ ProcessPartialRunsTo prog s0 post oom

/-- Whole-binary specification over raw ELF64 `ET_EXEC` bytes:
    1. `elfBytes` parses (`ElfImage.parse`) to a `WellFormed` static image `img`, unconditionally
       (even if `pre` is unsatisfiable), and
    2. for **every** `inputs : ProcessInputs` satisfying `pre inputs`, loading `img` with `inputs`
       succeeds (`img.loadState inputs = .ok s0`) and the run of `prog` from `s0` satisfies
       `ProcessRunsTo prog s0 (post inputs) (oom inputs)`.
    `post` and `oom` relate the outcome to the inputs. Passing a minimal syscall bundle
    (`(prog := Program.stdioCli)`, `Program.fileIo`) keeps unused syscall families out of the
    statement's constant closure. -/
def ElfRunsTo (elfBytes : List (BitVec 8))
    (pre : ProcessInputs → Prop)
    (post : ProcessInputs → ProcessOutcome → Prop)
    (oom : ProcessInputs → State → Prop := fun _ _ => False)
    (prog : Program := Program.pureMem) : Prop :=
  ∃ img,
    ElfImage.parse elfBytes = .ok img ∧
    ∀ inputs, pre inputs →
      ∃ s0, img.loadState inputs = .ok s0 ∧
        ProcessRunsTo prog s0 (post inputs) (oom inputs)

/-- Whole-binary **partial-correctness** specification: `ElfRunsTo` with `ProcessPartialRunsTo` in
    place of `ProcessRunsTo`. `elfBytes` parses to a `WellFormed` image `img` unconditionally, and
    for every `inputs` satisfying `pre inputs`, loading succeeds and every reachable state is
    terminated with `post inputs`, out of memory with `oom inputs`, or `.Running` with a next step.
    It makes **no termination claim**: it holds vacuously of the outcome for runs that diverge. -/
def ElfPartialRunsTo (elfBytes : List (BitVec 8))
    (pre : ProcessInputs → Prop)
    (post : ProcessInputs → ProcessOutcome → Prop)
    (oom : ProcessInputs → State → Prop := fun _ _ => False)
    (prog : Program := Program.pureMem) : Prop :=
  ∃ img,
    ElfImage.parse elfBytes = .ok img ∧
    ∀ inputs, pre inputs →
      ∃ s0, img.loadState inputs = .ok s0 ∧
        ProcessPartialRunsTo prog s0 (post inputs) (oom inputs)

/-- Whole-binary functional correctness: `ElfRunsTo` where every run with at least
    `minPhysMem inputs` bytes of initial dynamic physical memory
    (`inputs.init.physMemAvail ≥ minPhysMem inputs`, default `fun _ => 2 ^ 30` = `1 GiB`) exits
    normally with status `0` (`out.exitCode = 0#64 ∧ out.signal = none`), satisfies
    `post inputs out`, and never runs out of memory. -/
abbrev ElfCorrect (elfBytes : List (BitVec 8))
    (pre : ProcessInputs → Prop)
    (post : ProcessInputs → ProcessOutcome → Prop)
    (prog : Program := Program.pureMem)
    (minPhysMem : ProcessInputs → Nat := fun _ => 2 ^ 30) : Prop :=
  ElfRunsTo elfBytes
    (fun inputs => inputs.init.physMemAvail ≥ minPhysMem inputs ∧ pre inputs)
    (fun inputs out => out.exitCode = 0#64 ∧ out.signal = none ∧ post inputs out)
    (oom := fun _ _ => False) (prog := prog)

/-- Whole-binary safety and clean exit: `ElfCorrect` with a trivial postcondition. -/
abbrev ElfSafe (elfBytes : List (BitVec 8))
    (pre : ProcessInputs → Prop := ProcessInputs.Valid)
    (prog : Program := Program.pureMem)
    (minPhysMem : ProcessInputs → Nat := fun _ => 2 ^ 30) : Prop :=
  ElfCorrect elfBytes pre (fun _ _ => True) (prog := prog) (minPhysMem := minPhysMem)

end Process

end Arm64


