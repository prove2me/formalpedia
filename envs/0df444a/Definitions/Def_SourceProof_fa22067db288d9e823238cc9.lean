-- Prove2me | Definitions.Def_SourceProof_fa22067db288d9e823238cc9
-- name    : SourceProof_fa22067db288d9e823238cc9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:45:06.180547+00:00
-- url     : https://prove2.me/theorems/e1dbb2ca-3800-4703-9504-f28f9e6e5afa
-- title:
--   LevyStochCalc source proof: LevyStochCalc.norm_le_sum_abs_apply
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CoordDerivative_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Partial derivatives on `Fin n → ℝ`

A continuous linear functional on `Fin n → ℝ` is determined by its values on the standard basis
vectors `Pi.single p 1`, so the first- and second-order terms of a Taylor expansion split into
partial derivatives. The bounds and Lipschitz constants of those scalar functions come from the
operator norms of the Fréchet derivatives.

## Main statements

* `LevyStochCalc.clm_apply_pi` — expansion of a continuous linear map on `Fin n → ℝ`.
* `LevyStochCalc.coordDeriv`, `LevyStochCalc.coordDeriv₂` — the partial derivatives.
* `LevyStochCalc.apply_eq_sum_coordDeriv`, `LevyStochCalc.apply₂_eq_sum_coordDeriv₂` — the
  first- and second-order terms in coordinates.
* `LevyStochCalc.abs_coordDeriv_sub_le` — the Lipschitz bound of a partial derivative, from
  the bound on the second derivative.
-/

namespace LevyStochCalc

open ContinuousLinearMap

variable {n : ℕ}

section Expansion

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end Expansion

section Coord

variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}


theorem _root_.Prove2MeSourceProof.h_fa22067db288d9e823238cc9 (A : (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, |A (Pi.single p 1)| := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun p _ => abs_nonneg _) fun x => ?_
  have hx : A x = ∑ p, x p * A (Pi.single p 1) := by
    conv_lhs => rw [← LevyStochCalc.sum_single_eq x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [map_smul]; simp
  rw [Real.norm_eq_abs, hx]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [abs_mul]
  have h1 : |x p| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x p
  calc |x p| * |A (Pi.single p 1)|
      ≤ ‖x‖ * |A (Pi.single p 1)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |A (Pi.single p 1)| * ‖x‖ := by ring
end Coord

end LevyStochCalc


