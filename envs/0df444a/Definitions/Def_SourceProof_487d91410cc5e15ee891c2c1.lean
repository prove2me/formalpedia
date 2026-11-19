-- Prove2me | Definitions.Def_SourceProof_487d91410cc5e15ee891c2c1
-- name    : SourceProof_487d91410cc5e15ee891c2c1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:44:51.417301+00:00
-- url     : https://prove2.me/theorems/62cd8238-9a1f-4e7e-bb92-250a1be3c528
-- title:
--   LevyStochCalc source proof: LevyStochCalc.norm_le_sum_abs_apply₂
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


theorem _root_.Prove2MeSourceProof.h_487d91410cc5e15ee891c2c1 (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by
  refine A.opNorm_le_bound₂ (Finset.sum_nonneg fun p _ =>
    Finset.sum_nonneg fun q _ => abs_nonneg _) fun x y => ?_
  have hx : A x y = ∑ p, x p * (A (Pi.single p 1) y) := by
    conv_lhs => rw [← LevyStochCalc.sum_single_eq x]
    rw [map_sum]
    simp only [_root_.sum_apply]
    exact Finset.sum_congr rfl fun p _ => by rw [map_smul]; simp
  have hy : ∀ p : Fin n, A (Pi.single p 1) y
      = ∑ q, y q * (A (Pi.single p 1) (Pi.single q 1)) := by
    intro p
    conv_lhs => rw [← LevyStochCalc.sum_single_eq y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [map_smul]; simp
  have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hynn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  rw [Real.norm_eq_abs, hx]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      |x p * (A (Pi.single p 1) y)|
        ≤ ‖x‖ * ‖y‖ * ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by
    intro p _
    rw [abs_mul, hy p]
    have h1 : |x p| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x p
    have h2 : |∑ q, y q * (A (Pi.single p 1) (Pi.single q 1))|
        ≤ ‖y‖ * ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q _ => ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      simpa [Real.norm_eq_abs] using norm_le_pi_norm y q
    calc |x p| * |∑ q, y q * (A (Pi.single p 1) (Pi.single q 1))|
        ≤ ‖x‖ * (‖y‖ * ∑ q, |A (Pi.single p 1) (Pi.single q 1)|) :=
          mul_le_mul h1 h2 (abs_nonneg _) hxnn
      _ = ‖x‖ * ‖y‖ * ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  ring
end Coord

end LevyStochCalc


