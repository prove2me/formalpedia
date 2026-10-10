-- Prove2me | Definitions.Def_IntMul_SavedContinuationCall
-- name    : IntMul_SavedContinuationCall
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T00:06:37.317107+00:00
-- url     : https://prove2.me/theorems/5d09a6bb-54fb-46a1-be6c-86dc23b2baf2
-- title:
--   Physical shared-tape child caller saving and recovering finite continuation control
-- statement:
--   A fixed finite caller on k+3 tapes and the common tagged alphabet physically pushes a finite continuation label, runs the complete parent-preserving child-call service with an exactly retained stack tape, then physically pops the label into finite resume control. Its phases share a finite sum of states. The completed-push and child-halt transitions each spend one real stay step dispatching to the next phase. The stack counter and labels range over fixed finite sets of size n, never over input length or recursion depth. Parent banks are allocated, tracked, cleaned and physically restored by the child service. Arbitrary older continuation prefixes are retained, and the recovered resume state is a return-control state rather than the designated global halt. Exact initial/final frames keep caller input production explicit; no host stack, address oracle, depth-dependent tape set or free return instruction is introduced.
-- source:
--   Original complete physical saved-continuation child caller for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FiniteContinuationStack
import Definitions.Def_IntMul_FixedTapeExtension
import Definitions.Def_IntMul_TrackedReentrantCall

namespace IntMul.SavedContinuationCall

open IntMul.TrackedBankedSimulation (Sym)

noncomputable abbrev childMachine (M : MultitapeTM) : MultitapeTM :=
  FixedTapeExtension.machine (TrackedReentrantCall.machine M)

abbrev State (M : MultitapeTM) (n : ℕ) := FiniteContinuationStack.State n ⊕
  (TrackedReentrantCall.State M ⊕ FiniteContinuationStack.State n)

noncomputable def transition (M : MultitapeTM) (n : ℕ) (q : State M n)
    (a : Fin (M.k + 3) → Sym M) : State M n × (Fin (M.k + 3) → Sym M × Move) := by
  classical
  exact match q with
  | .inl q =>
      if q = .pushDone then (.inr (.inl (childMachine M).qStart),fun i => (a i,.stay)) else
        let r := FiniteContinuationStack.transition M n q a
        (.inl r.1,r.2)
  | .inr (.inl q) =>
      if q = (childMachine M).qHalt then (.inr (.inr .popStart),fun i => (a i,.stay)) else
        let r := (childMachine M).δ q a
        (.inr (.inl r.1),r.2)
  | .inr (.inr q) =>
      let r := FiniteContinuationStack.transition M n q a
      (.inr (.inr r.1),r.2)

/-- Push an actual finite continuation, physically run the shared-tape
child with stack preservation, then recover the saved finite resume state.
The same table handles arbitrary older stack prefixes and recursion depths. -/
noncomputable abbrev machine (M : MultitapeTM) (n : ℕ) (initial : Fin n) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State M n
  qStart := .inl (.pushStart initial)
  qHalt := .inr (.inr .halt)
  start_ne_halt := by simp
  k := M.k + 3
  two_le_k := by omega
  δ := transition M n
  start_preserved := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        by_cases h : q = .pushDone
        · simp [transition,h,hi]
        · simpa [transition,h] using (FiniteContinuationStack.machine M n).start_preserved q a i hi
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = (childMachine M).qHalt
            · simp [transition,h,hi]
            · simpa [transition,h] using (childMachine M).start_preserved q a i hi
        | inr q => simpa only [transition] using (FiniteContinuationStack.machine M n).start_preserved q a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        by_cases h : q = .pushDone
        · simpa [transition,h] using hi
        · simpa [transition,h] using (FiniteContinuationStack.machine M n).start_only_at_start q a i hi
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = (childMachine M).qHalt
            · simpa [transition,h] using hi
            · simpa [transition,h] using (childMachine M).start_only_at_start q a i hi
        | inr q => simpa only [transition] using (FiniteContinuationStack.machine M n).start_only_at_start q a i hi
  halt_fixed := by
    intro a
    have h := (FiniteContinuationStack.machine M n).halt_fixed a
    change FiniteContinuationStack.transition M n .halt a = (.halt,fun i => (a i,.stay)) at h
    simp only [transition,h]
  input_readonly := by
    classical
    intro q a
    cases q with
    | inl q =>
        by_cases h : q = .pushDone
        · simp [transition,h]
        · simpa [transition,h] using (FiniteContinuationStack.machine M n).input_readonly q a
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = (childMachine M).qHalt
            · simp [transition,h]
            · simpa [transition,h] using (childMachine M).input_readonly q a
        | inr q => simpa only [transition] using (FiniteContinuationStack.machine M n).input_readonly q a

noncomputable def liftPush (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (c : (FiniteContinuationStack.machine M n).Cfg) : (machine M n initial).Cfg where
  state := .inl c.state
  cells := c.cells
  head := c.head

noncomputable def liftChild (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (c : (childMachine M).Cfg) : (machine M n initial).Cfg where
  state := .inr (.inl c.state)
  cells := c.cells
  head := c.head

noncomputable def liftPop (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (c : (FiniteContinuationStack.machine M n).Cfg) : (machine M n initial).Cfg where
  state := .inr (.inr c.state)
  cells := c.cells
  head := c.head

noncomputable def childBase (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) : (childMachine M).Cfg where
  state := (childMachine M).qStart
  cells := base.cells
  head := base.head

noncomputable def stackBase (M : MultitapeTM) (n : ℕ)
    (c : (childMachine M).Cfg) : (FiniteContinuationStack.machine M n).Cfg where
  state := .popStart
  cells := c.cells
  head := c.head

noncomputable def initialFrame (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n)
    (c : (TrackedReentrantCall.machine M).Cfg) : (machine M n initial).Cfg :=
  liftPush M n initial (FiniteContinuationStack.pushStartFrame M n
    (stackBase M n (FixedTapeExtension.embed (TrackedReentrantCall.machine M) (childBase M n initial base) c)) rho q)

noncomputable def finalFrame (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n)
    (c : (TrackedReentrantCall.machine M).Cfg) : (machine M n initial).Cfg :=
  liftPop M n initial (FiniteContinuationStack.finalFrame M n
    (stackBase M n (FixedTapeExtension.embed (TrackedReentrantCall.machine M) (childBase M n initial base) c)) rho q)

noncomputable def callInitialFrame (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n)
    (parent : (TrackedReentrantCall.machine M).Cfg) (offset extent : Fin M.k → ℕ) (c : M.Cfg) :
    (machine M n initial).Cfg :=
  initialFrame M n initial base rho q (TrackedReentrantCall.initialFrame M parent offset extent c)

noncomputable def callFinalFrame (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n)
    (parent : (TrackedReentrantCall.machine M).Cfg) (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (x y : List Bool) (T : ℕ) (w : List Bool) : (machine M n initial).Cfg :=
  finalFrame M n initial base rho q (TrackedReentrantCall.finalFrame M parent sigma offset extent c x y T w)

end IntMul.SavedContinuationCall


