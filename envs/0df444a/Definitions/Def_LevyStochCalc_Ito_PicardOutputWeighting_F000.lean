-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F000
-- name    : LevyStochCalc_Ito_PicardOutputWeighting_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:44:50.836897+00:00
-- url     : https://prove2.me/theorems/2bd62c30-c517-4d7e-8083-2058436c9967
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

omit [MeasurableSpace E] in
/-- The second moment at a single time of `[0, T]`, weighted back up from the Bielecki norm. -/
theorem lintegral_sq_le_bieleckiNorm_sq_weighted (β T : ℝ) (Z : ℝ → Ω → (Fin n → ℝ))
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (Real.exp (2 * β * s)) * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
  set A : ℝ≥0∞ := ∫⁻ ω, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P with hA
  have hle : ENNReal.ofReal (Real.exp (-β * s)) * A ^ ((1 : ℝ) / 2)
      ≤ bieleckiNorm (P := P) β T Z := by
    unfold bieleckiNorm
    exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) s hs
  have hmul : A ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.exp (β * s)) * bieleckiNorm (P := P) β T Z := by
    refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl hle)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  calc A = (A ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := by
        rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ (ENNReal.ofReal (Real.exp (β * s)) * bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) :=
        pow_le_pow_left' hmul 2
    _ = ENNReal.ofReal (Real.exp (2 * β * s)) * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
        rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
        ring_nf
end Weighting

end LevyStochCalc.Ito.Picard


