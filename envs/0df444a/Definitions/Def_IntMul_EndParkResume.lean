-- Prove2me | Definitions.Def_IntMul_EndParkResume
-- name    : IntMul_EndParkResume
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T03:34:09.949031+00:00
-- url     : https://prove2.me/theorems/b559aa1d-b0f7-4415-8bcb-9188701a7d56
-- title:
--   Complete fixed-tape result-only parent return with continuation recovery and parked work heads
-- statement:
--   One deterministic finite physical return table on a fixed visited-bit alphabet and exactly k+3 tapes. Its phases selectively restore only the parent result head, physically pop and erase a finite continuation record, place the returned child word into the parent result bank with old-tail erasure, and enter the finite ready state containing the recovered label. Other work heads remain at the first fresh cells after their retained parent extents; all ancestor prefixes, root input, shared result buffer and older continuation records are preserved. The fixed result-tape selection and finite label count are compiled into the table. Offsets, extents, words, positions and depths occur only in specification frames, never as inputs to delta. The full table charges all phase dispatches. A fast recursive body and optimized full scheduler integration remain separate work.
-- source:
--   Original complete result-only physical parent-return table for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedSelectiveParentRestore
import Definitions.Def_IntMul_TrackedParentOutputBridge
import Definitions.Def_IntMul_FiniteContinuationStack
import Definitions.Def_IntMul_FixedTapeExtension

namespace IntMul.EndParkResume

open IntMul.TrackedBankedSimulation (Sym)

/-- The fixed result-tape selection; no runtime address enters the table. -/
noncomputable def active (M : MultitapeTM) : Fin M.k → Bool := fun j => decide (j=M.outTape)

noncomputable abbrev restoreMachine (M : MultitapeTM) :=
  FixedTapeExtension.machine (TrackedSelectiveParentRestore.machine M (active M))

noncomputable abbrev outputMachine (M : MultitapeTM) :=
  FixedTapeExtension.machine (TrackedParentOutputBridge.machine M)

inductive State (n : ℕ)
  | restore (s : TrackedSelectiveParentRestore.State)
  | pop (s : FiniteContinuationStack.State n)
  | output (q : Fin n) (s : TrackedParentOutputBridge.State)
  | ready (q : Fin n)
  | halt

noncomputable instance (n : ℕ) : Fintype (State n) := by
  classical
  exact {
    elems := (Finset.univ.image State.restore) ∪ (Finset.univ.image State.pop) ∪
      (Finset.univ.image (fun qs : Fin n × TrackedParentOutputBridge.State => State.output qs.1 qs.2)) ∪
      (Finset.univ.image State.ready) ∪ {.halt}
    complete := by intro q; cases q <;> simp }

noncomputable def transition (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k+3) → Sym M) : State n × (Fin (M.k+3) → Sym M × Move) := by
  classical
  exact match q with
  | .restore s =>
    if s=(restoreMachine M).qHalt then (.pop .popStart,fun i => (a i,.stay))
    else let r := (restoreMachine M).δ s a; (.restore r.1,r.2)
  | .pop s =>
    match s with
    | .resume label => (.output label .before,fun i => (a i,.stay))
    | _ => let r := FiniteContinuationStack.transition M n s a; (.pop r.1,r.2)
  | .output label s =>
    if s=(outputMachine M).qHalt then (.ready label,fun i => (a i,.stay))
    else let r := (outputMachine M).δ s a; (.output label r.1,r.2)
  | .ready label => (.ready label,fun i => (a i,.stay))
  | .halt => (.halt,fun i => (a i,.stay))

private theorem transition_actions (M : MultitapeTM) (n : ℕ)
    (a : Fin (M.k+3) → Sym M) (P : (Fin (M.k+3) → Sym M × Move) → Prop)
    (stay : P (fun i => (a i,.stay)))
    (restoreP : ∀ s, P ((restoreMachine M).δ s a).2)
    (stackP : ∀ s, P (FiniteContinuationStack.transition M n s a).2)
    (outputP : ∀ s, P ((outputMachine M).δ s a).2) (q : State n) :
    P (transition M n q a).2 := by
  classical
  cases q with
  | restore s =>
    by_cases h : s=(restoreMachine M).qHalt
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using restoreP s
  | pop s =>
    cases s <;> simp only [transition]
    all_goals first | exact stay | exact stackP _
  | output label s =>
    by_cases h : s=(outputMachine M).qHalt
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using outputP s
  | ready label => simpa only [transition] using stay
  | halt => simpa only [transition] using stay

/-- A complete finite physical return service: restore only the parent result
head, pop and recover the continuation, place its result and enter that
finite ready control. All other work heads remain parked at their suffixes.
The same finite visited-bit alphabet and k+3 tapes work at arbitrary depth. -/
noncomputable abbrev machine (M : MultitapeTM) (n : ℕ) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State n
  qStart := .restore .rewind
  qHalt := .halt
  start_ne_halt := by simp
  k := M.k+3
  two_le_k := by omega
  δ := transition M n
  start_preserved := by
    classical
    intro q a i hi
    apply transition_actions M n a (fun r => (r i).1=none ∧ (r i).2≠.left)
    · simp [hi]
    · intro s; exact (restoreMachine M).start_preserved s a i hi
    · intro s; exact (FiniteContinuationStack.machine M n).start_preserved s a i hi
    · intro s; exact (outputMachine M).start_preserved s a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    apply transition_actions M n a (fun r => (r i).1≠none)
    · exact hi
    · intro s; exact (restoreMachine M).start_only_at_start s a i hi
    · intro s; exact (FiniteContinuationStack.machine M n).start_only_at_start s a i hi
    · intro s; exact (outputMachine M).start_only_at_start s a i hi
  halt_fixed := by intro a; rfl
  input_readonly := by
    intro q a
    apply transition_actions M n a (fun r => (r ⟨0,by omega⟩).1=a ⟨0,by omega⟩)
    · rfl
    · intro s; exact (restoreMachine M).input_readonly s a
    · intro s; exact (FiniteContinuationStack.machine M n).input_readonly s a
    · intro s; exact (outputMachine M).input_readonly s a

noncomputable def liftRestore (M : MultitapeTM) (n : ℕ)
    (c : (restoreMachine M).Cfg) : (machine M n).Cfg where
  state := .restore c.state
  cells := c.cells
  head := c.head

noncomputable def liftPop (M : MultitapeTM) (n : ℕ)
    (c : (FiniteContinuationStack.machine M n).Cfg) : (machine M n).Cfg where
  state := .pop c.state
  cells := c.cells
  head := c.head

noncomputable def liftOutput (M : MultitapeTM) (n : ℕ) (label : Fin n)
    (c : (outputMachine M).Cfg) : (machine M n).Cfg where
  state := .output label c.state
  cells := c.cells
  head := c.head

noncomputable def relabel (M : MultitapeTM) (n : ℕ) (state : State n)
    (c : (machine M n).Cfg) : (machine M n).Cfg where
  state := state
  cells := c.cells
  head := c.head

/-- Logical parent after result placement. Non-result heads deliberately
remain at the first fresh cell beyond the parent's retained visited extent. -/
noncomputable def parentAtEnds (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg) : M.Cfg where
  state := c.state
  cells := c.cells
  head := fun j => if j=M.outTape then 0 else extent j+1

noncomputable def restorePlainBase (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (sigma : ℕ) (w : List Bool) : (TrackedSelectiveParentRestore.machine M (active M)).Cfg where
  state := .rewind
  cells := fun i => if i.val=1 then
    TrackedOutputReturn.bufferTape M
      (base.cells (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) i)) sigma w
    else base.cells (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) i)
  head := fun i => if i.val=1 then sigma+w.length+1 else
    base.head (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) i)

noncomputable def restorePadBase (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho : ℕ) (label : Fin n) : (restoreMachine M).Cfg where
  state := .rewind
  cells := fun i => if i=FiniteContinuationStack.stackTape M then
    FiniteContinuationStack.recordTape M n (base.cells i) rho label n else base.cells i
  head := fun i => if i=FiniteContinuationStack.stackTape M then rho+n+1 else base.head i

noncomputable def restoreStart (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) : (restoreMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedSelectiveParentRestore.machine M (active M))
    (restorePadBase M n base rho label)
    (TrackedSelectiveParentRestore.initialFrame M (active M)
      (restorePlainBase M n base sigma w) offset extent c (fun j => extent j+1))

noncomputable def restoreFinal (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) : (restoreMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedSelectiveParentRestore.machine M (active M))
    (restorePadBase M n base rho label)
    (TrackedSelectiveParentRestore.finalFrame M (active M)
      (restorePlainBase M n base sigma w) offset extent c (fun j => extent j+1))

noncomputable def initialFrame (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) : (machine M n).Cfg :=
  liftRestore M n (restoreStart M n base rho sigma offset extent c label w)

noncomputable def popParent (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) : (FiniteContinuationStack.machine M n).Cfg where
  state := .popStart
  cells := (restoreFinal M n base rho sigma offset extent c label w).cells
  head := (restoreFinal M n base rho sigma offset extent c label w).head

noncomputable def popped (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) : (FiniteContinuationStack.machine M n).Cfg :=
  FiniteContinuationStack.finalFrame M n
    (popParent M n base rho sigma offset extent c label w) rho label

noncomputable def outputPlainBase (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) : (TrackedParentOutputBridge.machine M).Cfg where
  state := .before
  cells := fun i => (popped M n base rho sigma offset extent c label w).cells
    (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) i)
  head := fun i => (popped M n base rho sigma offset extent c label w).head
    (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) i)

noncomputable def outputPadBase (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) : (outputMachine M).Cfg where
  state := .before
  cells := (popped M n base rho sigma offset extent c label w).cells
  head := (popped M n base rho sigma offset extent c label w).head

noncomputable def outputStart (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) : (outputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedParentOutputBridge.machine M)
    (outputPadBase M n base rho sigma offset extent c label w)
    (TrackedParentOutputBridge.initialFrame M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w)

noncomputable def outputFinal (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) : (outputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedParentOutputBridge.machine M)
    (outputPadBase M n base rho sigma offset extent c label w)
    (TrackedParentOutputBridge.finalFrame M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w)

noncomputable def finalFrame (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) : (machine M n).Cfg where
  state := .ready label
  cells := (outputFinal M n base rho sigma offset extent c label w).cells
  head := (outputFinal M n base rho sigma offset extent c label w).head

end IntMul.EndParkResume


