-- Prove2me | Definitions.Def_ObliviousAdaptive172_Parallel_parallelWrapper
-- name    : ObliviousAdaptive172_Parallel_parallelWrapper
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:34.517214+00:00
-- url     : https://prove2.me/theorems/67abfddd-793f-4909-bade-ef01a07df0fa
-- title:
--   Algorithm 2 — interrupted parallel repetition with a frozen first witness
-- statement:
--   Given a primitive, a number $L$ of independent private tapes and budget $T_A$, initialize $L$ private copies, their cumulative executed times and done flags, an empty stored handle, a zero done count and an unset trigger flag. Initialization is processed as action zero. On every action before triggering, visit unfinished copies in fixed index order and execute their actual instructions, interrupting a copy when its cumulative work first exceeds $T_A$. A returned witness freezes that copy and fills the stored handle only if it is empty. A timeout also freezes a copy and counts as done, without producing a witness. A return on the boundary instruction is inspected before the timeout branch, as in the source pseudocode.
--
--   The public trigger is exactly
--
--   $$
--   4\,\operatorname{doneCount}\ge L\quad\text{and}\quad\operatorname{stored}\ne\bot.
--   $$
--
--   Before that guard succeeds the answer is “no”. Afterwards every update returns the identical stored witness and executes no more primitive instructions. There is no validity oracle: acceptance uses only the primitive's returned handle and its one-sided contract.
--
--   Work charges input delivery, each primitive instruction, ten control operations per visited copy and ten per untriggered public action. Copy allocation costs $L+1$, and a frozen handle return costs one. The incremental done counter implements the source's cardinality guard. For desired confidence $c>0$, define $L=\lceil64(c+1)\ln n\rceil$; the full theorem uses a uniform threshold $n\ge N\ge2$. These definitions specify the actual compiler, not its desired success event or its runtime bound.
-- source:
--   Shiri Chechik, Inbal Hadad, From Oblivious to Adaptive Adversaries: Black-Box Reductions for Monotone Dynamic Problems with Applications to Cuts, Distances, and Clustering, STOC 2027 submission #172 (October 2026), p. 12, Algorithm 2 (PDF p. 14); pp. 28–29, Appendix B.1 (PDF pp. 30–31)

import Mathlib
import Definitions.Def_ObliviousAdaptive172_Parallel_WeakStableCertifying
set_option autoImplicit false

namespace ObliviousAdaptive172.Parallel

/-- Hidden per-copy state and cumulative *executed* primitive work. -/
structure CopyState (Q W : Type) where
  config : Configuration Q W
  time : ℕ
  done : Bool

variable {U W R Q : Type}

/-- Algorithm 2, line 8: abort *inside* an update as soon as the cumulative work
exceeds `T`. The extra unit implements the printed strict `> T` test. A return on
the last executed instruction is inspected before the timeout branch, as in lines 9–15.
No validity test or certificate search is granted to the wrapper. -/
def cappedAction (A : PrivateTapeExecution U W R Q) (T : ℕ) (r : R)
    (input : Option U) (s : CopyState Q W) : CopyState Q W × Option W × ℕ :=
  if s.done then (s, none, 0) else
    let entered := s.time + 1
    if entered > T then (⟨s.config, entered, true⟩, none, 1) else
      let z := runFor A r input (T + 1 - entered) s.config
      let time := entered + z.ticks
      let done := z.answer.isSome || !z.returned || decide (time > T)
      (⟨z.config, time, done⟩, z.answer, 1 + z.ticks)

structure Sweep (R Q W : Type) where
  copies : List (R × CopyState Q W)
  stored : Option W
  newlyDone : ℕ
  work : ℕ

/-- Fixed index order. Each visited copy incurs ten control operations (test, read,
write, counter/handle operations, and loop control), in addition to primitive work.
Only previously absent storage is filled. Timeouts count as done but supply no witness. -/
def sweepCopies (A : PrivateTapeExecution U W R Q) (T : ℕ) (input : Option U) :
    List (R × CopyState Q W) → Option W → Sweep R Q W
  | [], stored => ⟨[], stored, 0, 0⟩
  | (r, s) :: rest, stored =>
    let z := cappedAction A T r input s
    let first := stored.or z.2.1
    let tail := sweepCopies A T input rest first
    ⟨(r, z.1) :: tail.copies, tail.stored,
      (if !s.done && z.1.done then 1 else 0) + tail.newlyDone,
      10 + z.2.2 + tail.work⟩

structure WrapperState (R Q W : Type) where
  copies : List (R × CopyState Q W)
  stored : Option W
  doneCount : ℕ
  triggered : Bool
  work : ℕ

/-- No internal witness, timing, or completion count is published. -/
def WrapperState.answer (s : WrapperState R Q W) : Option W :=
  if s.triggered then s.stored else none

/-- Algorithm 2's entire atomic public update. Returning a frozen witness handle costs
one operation. Otherwise, ten final control operations cover threshold, flag, and output.
The completion count is maintained incrementally, rather than rescanning the copies. -/
def wrapperAction (A : PrivateTapeExecution U W R Q) (L T : ℕ) (input : Option U)
    (s : WrapperState R Q W) : WrapperState R Q W :=
  if s.triggered then {s with work := s.work + 1} else
    let z := sweepCopies A T input s.copies s.stored
    let count := s.doneCount + z.newlyDone
    ⟨z.copies, z.stored, count, decide (L ≤ 4 * count) && z.stored.isSome,
      s.work + z.work + 10⟩

/-- The operational compiler, including initialization as action zero. Allocation of
the `L` private-state handles costs `L+1`; primitive initialization is then executed
with the same interruption mechanism as updates. No source property is queried here. -/
def parallelWrapper (A : PrivateTapeExecution U W R Q) (L T : ℕ)
    (tapes : Fin L → R) (h : List U) : WrapperState R Q W :=
  let copies := List.ofFn (fun i : Fin L => (tapes i, (⟨⟨A.boot, fun _ => none⟩, 0, false⟩ : CopyState Q W)))
  let initial := wrapperAction A L T none ⟨copies, none, 0, false, L + 1⟩
  h.foldl (fun s u => wrapperAction A L T (some u) s) initial

/-- Source L=ceil(64 d ln n), with an explicit confidence instantiation `d=c+1`.
For n=0 or 1 this returns zero; the asymptotic theorem has a uniform threshold N≥2. -/
noncomputable def repetitions (c : ℝ) (n : ℕ) : ℕ :=
  ⌈64 * (c + 1) * Real.log (n : ℝ)⌉₊

end ObliviousAdaptive172.Parallel


