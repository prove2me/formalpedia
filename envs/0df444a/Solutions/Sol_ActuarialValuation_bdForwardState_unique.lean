-- Prove2me | solution 1 for ActuarialValuation.bdForwardState_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:07:05.246281+00:00
-- url     : https://prove2.me/submissions/6bcfc639-84e0-4f97-8639-dda6e36a9d3a

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardStatePayment
import Definitions.Def_actuarial_bdRiskNeutralForward
import Definitions.Def_actuarial_bdStateZeroBond

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p discount delivery : Fin m → ℝ) (K : ℝ) (h : bdStateZeroBond p discount ≠ 0) (hzero : bdForwardStatePayment p discount delivery K = 0) : K = bdRiskNeutralForward p discount delivery := by
  have hdecomp (k : ℝ) :
      bdForwardStatePayment p discount delivery k =
        bdStatePV p discount delivery - k * bdStateZeroBond p discount := by
    unfold bdForwardStatePayment bdStateZeroBond bdStatePV
    simp only [mul_one]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    ring
  rw [hdecomp] at hzero
  unfold bdRiskNeutralForward
  apply (eq_div_iff h).2
  exact (sub_eq_zero.mp hzero).symm
