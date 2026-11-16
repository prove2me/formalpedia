-- Prove2me | Definitions.Def_GuardedSSSP_Supplement_MachineRuns
-- name    : GuardedSSSP_Supplement_MachineRuns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:20:20.727208+00:00
-- url     : https://prove2.me/theorems/8f66e4fb-3d52-49af-a20f-a7a00bd7db75
-- title:
--   Runs of the comparison–addition RAM from a given state: halting time, final state, operation counts and written cells
-- statement:
--   The base mission's comparison–addition RAM executes a program one instruction per step from a machine state (two memory banks, registers, a program counter). For a program $P$, a word bound $W$ and a start state $\sigma$:
--
--   1. $P$ **halts** from $\sigma$ if some step reaches a halted state; the **running time** is the index of the first halted state, and the **final state** is the state at that time (halted states do not change);
--   2. the **comparison–addition count** is the number of executed real additions and real comparisons before halting, and the **comparison count** the number of executed real comparisons;
--   3. the **space** is the number of distinct integer-memory and real-memory addresses written by store instructions before halting.
--
--   These measures express the running time, the numerical cost and the storage of the algorithms of Theorems C.1 and F.1, which run programs from states other than the base mission's SSSP input.
--
--   **Formalization Note** The running time is defined as $0$ when the run never halts; every theorem that uses it also asserts halting. Every executed instruction, `halt` included, costs one step, as in the base mission.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), §4.1, p.9 (PDF p.10); Appendix D, pp.37–38 (PDF pp.38–39)

import Mathlib
import Definitions.Def_GuardedSSSP_Machine

namespace GuardedSSSP

namespace Supplement

open GuardedSSSP.Machine

/-!
# Runs of the base RAM from an arbitrary state: halting time, final state, operation counts, space

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), §4.1, p.9 (PDF p.10), and Appendix D, pp.37–38 (PDF pp.38–39):
"We work in a comparison-addition RAM. A numerical instruction adds two held real values, compares two
held real values, or copies one. Graph traversal, pointers, allocation and integer metadata are also paid
in RAM time. An infinity tag is handled by control flow. Real values are never used as addresses, hashed,
or inspected bit by bit."

The base mission's `GuardedSSSP.Machine` fixes the instruction set and the one-step semantics
`Machine.step U W` under a word bound `W`. Theorems C.1 and F.1 run programs from states other than the
base SSSP input, so this module measures a run of a program from any state `σ`.

**Formalization Note.**
* `Halts P W σ`: some iterate of `step P W` from `σ` is halted. `haltTime P W σ` is the least such
  iterate count (the index of the first halted state: every executed instruction, `halt` included, costs
  one step, as in the base mission). It is defined as `0` when the run never halts; every theorem that uses
  it also asserts `Halts`, so that value is never used.
* `finalState P W σ` is the state at `haltTime`; a halted state stutters, so it is the state at every
  later time as well.
* `countInstr p P W σ` counts the instructions `i` with `p i = true` executed before `haltTime`;
  `numCA` is `radd` plus `rcmp` (the paper's additions and comparisons), `numCmp` is `rcmp` alone.
* `writtenInt` / `writtenReal` are the sets of distinct integer-memory / real-memory addresses written by
  an `istore` / `rstore` executed before `haltTime` (a store whose address does not fit the word bound
  sends the machine to the stuck state and writes nothing).
-/

/-- The state after `t` steps of `P` under word bound `W`, started from `σ`. -/
noncomputable def runFrom (P : Program) (W : ℤ) (σ : State) (t : ℕ) : State :=
  (step P W)^[t] σ

/-- The run of `P` from `σ` halts. -/
def Halts (P : Program) (W : ℤ) (σ : State) : Prop :=
  ∃ t : ℕ, (runFrom P W σ t).halted = true

open Classical in
/-- The running time: the index of the first halted state (`0` if the run never halts). -/
noncomputable def haltTime (P : Program) (W : ℤ) (σ : State) : ℕ :=
  if h : Halts P W σ then Nat.find h else 0

/-- The state at the halting time. -/
noncomputable def finalState (P : Program) (W : ℤ) (σ : State) : State :=
  runFrom P W σ (haltTime P W σ)

/-- The instruction executed at time `t` (none if the state is halted or stuck, or the program counter is
invalid). -/
noncomputable def executed (P : Program) (W : ℤ) (σ : State) (t : ℕ) : Option Instr :=
  let s := runFrom P W σ t
  if s.halted || s.stuck then none else P.code[s.pc]?

/-- The number of executed instructions satisfying `p`, before the halting time. -/
noncomputable def countInstr (p : Instr → Bool) (P : Program) (W : ℤ) (σ : State) : ℕ :=
  ((List.range (haltTime P W σ)).filter (fun t =>
    match executed P W σ t with
    | some i => p i
    | none => false)).length

/-- Real additions and real comparisons. -/
def Instr.isCA : Instr → Bool
  | .radd _ _ _ => true
  | .rcmp _ _ _ _ _ => true
  | _ => false

/-- Real comparisons. -/
def Instr.isCmp : Instr → Bool
  | .rcmp _ _ _ _ _ => true
  | _ => false

/-- Real addition or the real literal zero (the instructions that create real values other than by
copying). -/
def Instr.isRealArith : Instr → Bool
  | .radd _ _ _ => true
  | .rzero _ => true
  | _ => false

/-- The number of real additions and comparisons executed (the comparison–addition count). -/
noncomputable def numCA (P : Program) (W : ℤ) (σ : State) : ℕ := countInstr Instr.isCA P W σ

/-- The number of real comparisons executed. -/
noncomputable def numCmp (P : Program) (W : ℤ) (σ : State) : ℕ := countInstr Instr.isCmp P W σ

/-- The distinct integer-memory addresses written before the halting time. -/
noncomputable def writtenInt (P : Program) (W : ℤ) (σ : State) : Finset ℤ :=
  ((List.range (haltTime P W σ)).filterMap (fun t =>
    match executed P W σ t with
    | some (.istore a _) =>
        let s := runFrom P W σ t
        if Fits W (s.ireg a) then some (s.ireg a) else none
    | _ => none)).toFinset

/-- The distinct real-memory addresses written before the halting time. -/
noncomputable def writtenReal (P : Program) (W : ℤ) (σ : State) : Finset ℤ :=
  ((List.range (haltTime P W σ)).filterMap (fun t =>
    match executed P W σ t with
    | some (.rstore a _) =>
        let s := runFrom P W σ t
        if Fits W (s.ireg a) then some (s.ireg a) else none
    | _ => none)).toFinset

/-- The number of distinct memory cells (integer and real) written before the halting time. -/
noncomputable def space (P : Program) (W : ℤ) (σ : State) : ℕ :=
  (writtenInt P W σ).card + (writtenReal P W σ).card

end Supplement

end GuardedSSSP


