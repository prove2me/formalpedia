-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F001
-- name    : LevyStochCalc_Ito_PicardOutputWeighting_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:45:10.987422+00:00
-- url     : https://prove2.me/theorems/932707da-4bfa-4bb5-ba50-0b9808ef0407
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardOutputWeighting
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardOutputWeighting. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki weighting and the per-component difference bounds

The Bielecki norm with rate `β` dominates the second moment at each time of `[0, T]` after
reweighting by `e^{2βs}`, and the doubly-integrated energy over `[0, t]` by
`e^{2βt}/(2β)`, the factor `1/(2β)` being what makes the Picard rate small for large `β`.
Combined with the Lipschitz bounds on the coefficients this bounds the drift, diffusion and
jump components of the difference of two Picard steps by the energy of the difference of the
two frozen paths.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Weighting

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- A Bochner integral of a nonnegative function is below the corresponding lower integral, with
no integrability hypothesis: when the integrand is not integrable the Bochner integral is `0`. -/
theorem ofReal_setIntegral_le_lintegral {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (s : Set ℝ) :
    ENNReal.ofReal (∫ x in s, f x ∂volume) ≤ ∫⁻ x in s, ENNReal.ofReal (f x) ∂volume := by
  have h1 : ENNReal.ofReal (∫ x in s, f x ∂volume) ≤ ‖∫ x in s, f x ∂volume‖ₑ := by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  refine h1.trans ((MeasureTheory.enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_))
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf x)]
omit [MeasurableSpace Ω] [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The window energy in the supremum norm is below the window energy in coordinates. -/
theorem lintegral_window_norm_le_sum {Z : ℝ → Ω → (Fin n → ℝ)} (t : ℝ) (ω : Ω) :
    ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖Z s ω‖ ^ 2 ∂volume)
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume := by
  refine (ofReal_setIntegral_le_lintegral (fun x => by positivity) _).trans ?_
  exact lintegral_mono fun s => ofReal_sq_norm_le_sum (Z s ω)
end Weighting

end LevyStochCalc.Ito.Picard


