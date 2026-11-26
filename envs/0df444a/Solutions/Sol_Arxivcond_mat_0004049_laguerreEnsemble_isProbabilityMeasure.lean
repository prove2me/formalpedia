-- Prove2me | solution 1 for Arxivcond_mat_0004049.laguerreEnsemble_isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T14:40:20.960248+00:00
-- url     : https://prove2.me/submissions/041cd2ed-2f8b-4341-bc7f-53bc871bc4c5

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic
import Theorems.Thm_Arxivcond_mat_0004049_laguerre_normalization_pos_finite

open MeasureTheory ProbabilityTheory

open Arxivcond_mat_0004049 in
/-- The total mass is `Z⁻¹ * Z = 1`, with `0 < Z < ∞` from `laguerre_normalization_pos_finite`. -/
theorem solution (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    IsProbabilityMeasure (laguerreEnsemble N γ) := by
  obtain ⟨h0, htop⟩ := laguerre_normalization_pos_finite N γ hγ
  refine ⟨?_⟩
  rw [laguerreEnsemble, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 htop
