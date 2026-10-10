-- Prove2me | solution 1 for ActuarialValuation.finiteExponentialMoment_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:29:16.790852+00:00
-- url     : https://prove2.me/submissions/c029bee6-cef1-4f8a-806c-eea7e12a132c

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_actuarial_finiteExponentialMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ)
    (gamma : ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hsum : (∑ ω : Ω, w ω) = 1) :
    0 < finiteExponentialMoment w X gamma := by
  have hweight : ∃ ω : Ω, 0 < w ω := by
    have hsumpos : 0 < ∑ ω : Ω, w ω := by
      rw [hsum]
      norm_num
    rcases (Finset.sum_pos_iff_of_nonneg
      (s := (Finset.univ : Finset Ω))
      (fun ω _ => hw ω)).mp hsumpos with ⟨ω, _, hω⟩
    exact ⟨ω, hω⟩
  unfold finiteExponentialMoment
  apply (Finset.sum_pos_iff_of_nonneg
    (s := (Finset.univ : Finset Ω))
    (fun ω _ => mul_nonneg (hw ω) (le_of_lt (Real.exp_pos _)))).mpr
  rcases hweight with ⟨ω, hω⟩
  exact ⟨ω, Finset.mem_univ _, mul_pos hω (Real.exp_pos _)⟩
