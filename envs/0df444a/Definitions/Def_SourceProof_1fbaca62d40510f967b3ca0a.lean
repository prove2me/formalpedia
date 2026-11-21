-- Prove2me | Definitions.Def_SourceProof_1fbaca62d40510f967b3ca0a
-- name    : SourceProof_1fbaca62d40510f967b3ca0a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:50:14.298328+00:00
-- url     : https://prove2.me/theorems/72e45e87-2d0e-4547-a198-cb987ddb75cb
-- title:
--   LevyStochCalc source module: SourceProof_1fbaca62d40510f967b3ca0a
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.bieleckiNorm_le_of_perTime` comes from the `LevyStochCalc.Ito.PicardOutputWeighting` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F002
import Definitions.Def_SourceProof_b2989301f1b63168bf3b94aa

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

theorem _root_.Prove2MeSourceProof.h_1fbaca62d40510f967b3ca0a {β : ℝ} (hβ : 0 < β) {T C : ℝ} (hC : 0 ≤ C)
    (U Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P
        ≤ ENNReal.ofReal C
            * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P) :
    bieleckiNorm (P := P) β T U
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * bieleckiNorm (P := P) β T Z := by
  have hβ2 : (0 : ℝ) < 2 * β := by linarith
  refine iSup₂_le fun t ht => ?_
  have hcongr : (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P := by
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real (U t ω i)
  have hA : (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ ENNReal.ofReal (C / (2 * β)) * ENNReal.ofReal (Real.exp (2 * β * t))
          * (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
    calc (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P := hcongr
      _ ≤ ENNReal.ofReal C
            * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P := hbd t ht
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β))
            * (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z) ^ (2 : ℕ)) :=
          mul_le_mul' le_rfl (_root_.Prove2MeSourceProof.h_b2989301f1b63168bf3b94aa hβ T Z hZ ht)
      _ = ENNReal.ofReal (C / (2 * β)) * ENNReal.ofReal (Real.exp (2 * β * t))
            * (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC,
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C / (2 * β))]
          congr 2
          field_simp
  have hsqrt : (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * ENNReal.ofReal (Real.exp (β * t))
          * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z := by
    refine le_trans (ENNReal.rpow_le_rpow hA (by norm_num)) (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    · congr 1
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
        show 2 * β * t * ((1 : ℝ) / 2) = β * t by ring]
    · rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
      norm_num
  calc ENNReal.ofReal (Real.exp (-β * t))
        * (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.exp (-β * t))
          * ((ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2)
            * ENNReal.ofReal (Real.exp (β * t)) * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z) :=
        mul_le_mul' le_rfl hsqrt
    _ = (ENNReal.ofReal (Real.exp (-β * t)) * ENNReal.ofReal (Real.exp (β * t)))
          * ((ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2)
            * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z) := by ring
    _ = (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2)
          * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        simp
end Weighting

end LevyStochCalc.Ito.Picard


