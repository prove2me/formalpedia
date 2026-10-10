-- Prove2me | Definitions.Def_IntMul_TrackedBankedCall
-- name    : IntMul_TrackedBankedCall
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T22:48:43.073041+00:00
-- url     : https://prove2.me/theorems/39728091-9a45-4fcb-8cd4-6eef0d01a17f
-- title:
--   Complete physical tracked child caller with preparation and fresh-bank return
-- statement:
--   One fixed finite M.k+2-tape caller combines four-state physical tracked input preparation with the finite child/output/cleanup program. All phases use Option(M.Sym×Bool) and the same tapes. Preparation physically writes local markers, copies and erases a caller-computed x#y buffer, initializes exact visited flags and rewinds the child input. One charged switch starts tracked execution, output return and complete bank cleanup. The full finite state sum has the child states plus eleven fixed states. Proof-side offsets and extents never enter delta. The full final buffer contains the returned child output; all child banks and local markers are erased to fresh blank at their original offsets, with work heads parked there. Input production and fresh-suffix allocation remain caller obligations.
-- source:
--   Original complete physical tracked interior caller for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankPreparation
import Definitions.Def_IntMul_TrackedReturnCall

namespace IntMul.TrackedBankedCall

open IntMul.TrackedBankedSimulation (Sym)

abbrev State (M : MultitapeTM) := TrackedBankPreparation.State ⊕ TrackedReturnCall.State M

noncomputable def transition (M : MultitapeTM) (q : State M)
    (a : Fin (M.k + 2) → Sym M) : State M × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .inl q =>
      if q = .halt then (.inr (.inl M.qStart),fun i => (a i,.stay)) else
        let r := TrackedBankPreparation.transition M q a
        (.inl r.1,r.2)
  | .inr q =>
      let r := TrackedReturnCall.transition M q a
      (.inr r.1,r.2)

/-- One fixed finite caller performs physical setup, tracked execution,
output return and fresh-bank cleanup on the same tapes and alphabet. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State M
  qStart := .inl .mark
  qHalt := .inr (.inr (.inr .halt))
  start_ne_halt := by simp
  k := M.k + 2
  two_le_k := by omega
  δ := transition M
  start_preserved := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        by_cases h : q = .halt
        · simp [transition,h,hi]
        · simpa [transition,h] using (TrackedBankPreparation.machine M).start_preserved q a i hi
    | inr q => simpa only [transition] using (TrackedReturnCall.machine M).start_preserved q a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        by_cases h : q = .halt
        · simpa [transition,h] using hi
        · simpa [transition,h] using (TrackedBankPreparation.machine M).start_only_at_start q a i hi
    | inr q => simpa only [transition] using (TrackedReturnCall.machine M).start_only_at_start q a i hi
  halt_fixed := by
    intro a
    have h := (TrackedReturnCall.machine M).halt_fixed a
    change TrackedReturnCall.transition M (.inr (.inr .halt)) a =
      (.inr (.inr .halt),fun i => (a i,.stay)) at h
    simp only [transition,h]
  input_readonly := by
    classical
    intro q a
    cases q with
    | inl q =>
        by_cases h : q = .halt
        · simp [transition,h]
        · simpa [transition,h] using (TrackedBankPreparation.machine M).input_readonly q a
    | inr q => simpa only [transition] using (TrackedReturnCall.machine M).input_readonly q a

noncomputable def liftPreparation (M : MultitapeTM) (c : (TrackedBankPreparation.machine M).Cfg) : (machine M).Cfg where
  state := .inl c.state
  cells := c.cells
  head := c.head

noncomputable def liftCall (M : MultitapeTM) (c : (TrackedReturnCall.machine M).Cfg) : (machine M).Cfg where
  state := .inr c.state
  cells := c.cells
  head := c.head

noncomputable def preparationBase (M : MultitapeTM) (base : (machine M).Cfg) :
    (TrackedBankPreparation.machine M).Cfg where
  state := .mark
  cells := base.cells
  head := base.head

noncomputable def callBase (M : MultitapeTM) (base : (machine M).Cfg) :
    (TrackedReturnCall.machine M).Cfg where
  state := .inl M.qStart
  cells := base.cells
  head := base.head

noncomputable def initialFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) : (machine M).Cfg :=
  liftPreparation M (TrackedBankPreparation.initialFrame M (preparationBase M base) sigma offset x y)

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) : (machine M).Cfg :=
  liftCall M (TrackedReturnCall.finalFrame M (callBase M base) sigma offset extent c w)

end IntMul.TrackedBankedCall


