-- Prove2me | solution 1 for Apery.real_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-11T23:44:59.01443+00:00
-- url     : https://prove2.me/submissions/c3a621fc-720b-41b0-b44a-96f6acf014d5

/-
# Irrationality of $\\zeta(5)$ via normalized Hankel determinants
# Proposition 6.3 (real-value estimate) — reduction to the Section 6 estimates

This file proves the platform theorem `Apery.real_bound`,

  `0 < aeval zeta5 (F n) ∧
     Real.log (aeval zeta5 (F n)) ≤ (U : ℝ) * Kr n ^ 2 + 27 * Kr n * Real.log (Kr n) + 200 * Kr n`

for `n > 0`, from the decomposition stated in the source module `Apery/RealBound.lean`
of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0: the determinant estimate
(6.14) `Apery.log_delta_le`, the Stirling bound (6.15) `Apery.log_S_le`, the numerical
inequality (6.4) `Apery.energy_const`, and the positivity `Apery.delta_pos` (already
proved on the platform).
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure
import Theorems.Thm_Apery_delta_pos
import Theorems.Thm_Apery_log_delta_le
import Theorems.Thm_Apery_log_S_le
import Theorems.Thm_Apery_energy_const

set_option autoImplicit false

open Polynomial Filter Topology Finset

namespace Apery

lemma S_pos (n : ℕ) : 0 < S n := by unfold S; positivity

/-- **Proposition 6.3**, from the four statements above. -/
theorem real_bound_aux (n : ℕ) (hn : 0 < n) :
    0 < aeval zeta5 (F n) ∧
      Real.log (aeval zeta5 (F n)) ≤
        (U : ℝ) * Kr n ^ 2 + 27 * Kr n * Real.log (Kr n) + 200 * Kr n := by
  have hS : (0 : ℝ) < S n := by exact_mod_cast S_pos n
  have hΔ := delta_pos n hn
  have hF : aeval zeta5 (F n) = (S n : ℝ) * aeval zeta5 (Δ n) := by
    simp [F, aeval_C]
  refine ⟨by rw [hF]; positivity, ?_⟩
  rw [hF, Real.log_mul hS.ne' hΔ.ne']
  have h1 := log_delta_le n hn
  have h2 := log_S_le n hn
  have h3 := energy_const
  have hK : 0 < Kr n := by simp only [Kr]; positivity
  have hlogK : 0 ≤ Real.log (Kr n) := Real.log_nonneg (by simp only [Kr]; norm_cast; omega)
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3' : (lam * M0 - Irho + Cstar) * Kr n ^ 2 ≤ (U : ℝ) * Kr n ^ 2 :=
    mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
  have hlow : 0 ≤ (n : ℝ) * Real.log (Kr n) := mul_nonneg hn' hlogK
  simp only [Kr] at *
  norm_num [lam, alph] at h1 h2 h3' hlow ⊢
  nlinarith

end Apery

open MeasureTheory Polynomial in
/-- The platform target `Apery.real_bound`, restated at top level as `solution`. -/
theorem solution (n : ℕ) (hn : 0 < n) :
    0 < aeval Apery.zeta5 (Apery.F n) ∧
      Real.log (aeval Apery.zeta5 (Apery.F n)) ≤
        (Apery.U : ℝ) * Apery.Kr n ^ 2 + 27 * Apery.Kr n * Real.log (Apery.Kr n) + 200 * Apery.Kr n :=
  Apery.real_bound_aux n hn
