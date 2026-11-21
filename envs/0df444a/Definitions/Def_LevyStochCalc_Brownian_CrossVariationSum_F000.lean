-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_CrossVariationSum_F000
-- name    : LevyStochCalc_Brownian_CrossVariationSum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:32:49.862099+00:00
-- url     : https://prove2.me/theorems/ab6ede8c-d260-41e0-bdf7-3337cd49a5c6
-- title:
--   Source declarations: LevyStochCalc.Brownian.CrossVariationSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.CrossVariationSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossVariation_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
import Definitions.Def_LevyStochCalc_Probability_MartingaleDifference_F000
import Definitions.Def_SourceProof_071eab4bde5a9ae7a7d5b921
import Definitions.Def_SourceProof_2b50de3fda4320b525536839

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Weighted sums of cross increments

For two distinct Brownian coordinates the product of the increments of the Itô integrals across a
cell is conditionally centred at the cell's left endpoint, so a weighted sum of such products over
a partition is a sum of martingale differences whenever the weights are measurable at the left
endpoints. Its second moment is therefore the sum of the termwise second moments, and each of
those is bounded through the fourth moments of the two increments.

## Main statements

* `LevyStochCalc.Brownian.Ito.integrable_sq_mul_and_le` — the square of a product is integrable
  with second moment at most half the sum of the fourth moments.
* `LevyStochCalc.Brownian.Ito.crossIncrement` — the product of the increments of the Itô
  integrals against two coordinates across a cell.
* `LevyStochCalc.Brownian.Ito.integrable_sq_crossIncrement_and_le` — its square is integrable,
  with second moment at most `(6 + c)·(C_H⁴ + C_K⁴)/2·(b − a)²`.
* `LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le` — the second moment of a weighted
  sum over a grid is at most `D²·(6 + c)·(C_H⁴ + C_K⁴)/2·∑ᵢ (tᵢ₊₁ − tᵢ)²`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
/-- The square of a product of two functions with integrable fourth powers is integrable, and its
integral is at most half the sum of the two fourth moments. -/
theorem integrable_sq_mul_and_le {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA4 : Integrable (fun ω => A ω ^ 4) P) (hB4 : Integrable (fun ω => B ω ^ 4) P) :
    Integrable (fun ω => (A ω * B ω) ^ 2) P
      ∧ ∫ ω, (A ω * B ω) ^ 2 ∂P ≤ (∫ ω, A ω ^ 4 ∂P + ∫ ω, B ω ^ 4 ∂P) / 2 := by
  have hdom : Integrable (fun ω => (A ω ^ 4 + B ω ^ 4) / 2) P := (hA4.add hB4).div_const 2
  have hpt : ∀ ω, (A ω * B ω) ^ 2 ≤ (A ω ^ 4 + B ω ^ 4) / 2 := fun ω => by
    nlinarith [sq_nonneg (A ω ^ 2 - B ω ^ 2), sq_nonneg (A ω * B ω)]
  have hint : Integrable (fun ω => (A ω * B ω) ^ 2) P := by
    refine Integrable.mono' hdom ((hAm.mul hBm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  have hle : ∫ ω, (A ω * B ω) ^ 2 ∂P ≤ ∫ ω, (A ω ^ 4 + B ω ^ 4) / 2 ∂P :=
    MeasureTheory.integral_mono hint hdom hpt
  rwa [MeasureTheory.integral_div, MeasureTheory.integral_add hA4 hB4] at hle
section CrossSum

open LevyStochCalc.Brownian.Multidim

variable {d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- The product of the increments of the Itô integrals against the coordinates `i` and `j`
across `(a, b]`. -/
noncomputable def crossIncrement (i j : Fin d) (a b : ℝ) (ω : Ω) : ℝ :=
  (stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
      - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
    * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
      - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)
/-- The cross increment is measurable. -/
theorem measurable_crossIncrement (i j : Fin d) (a b : ℝ) :
    Measurable (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) :=
  (measurable_sub_stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a b).mul
    (measurable_sub_stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a b)
/-- The cross increment across `(a, b]` is measurable for the σ-algebra at `b`. -/
theorem stronglyMeasurable_crossIncrement (i j : Fin d) {a b : ℝ} (hab : a ≤ b) :
    StronglyMeasurable[ℱ b] (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) := by
  have hib := stochasticIntegralBrownian_stronglyAdapted (W.W i) ℱ (hcoord i) H hHm hHp hHs b
  have hia := (stochasticIntegralBrownian_stronglyAdapted (W.W i) ℱ (hcoord i) H hHm hHp hHs
    a).mono (ℱ.mono hab)
  have hjb := stochasticIntegralBrownian_stronglyAdapted (W.W j) ℱ (hcoord j) K hKm hKp hKs b
  have hja := (stochasticIntegralBrownian_stronglyAdapted (W.W j) ℱ (hcoord j) K hKm hKp hKs
    a).mono (ℱ.mono hab)
  exact (hib.sub hia).mul (hjb.sub hja)
variable {CH CK : ℝ} (hCH0 : 0 ≤ CH) (hCH : ∀ ω s, |H ω s| ≤ CH)
  (hCK0 : 0 ≤ CK) (hCK : ∀ ω s, |K ω s| ≤ CK)

include hCH0 hCH hCK0 hCK in
/-- **Second moment of a cross increment.** Both increments have fourth moments bounded through
the integrand bounds, and the square of a product is dominated by half the sum of the fourth
powers. -/
theorem integrable_sq_crossIncrement_and_le (i j : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Integrable (fun ω =>
        (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b ω) ^ 2) P
      ∧ ∫ ω, (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b ω) ^ 2 ∂P
        ≤ (6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2 * (b - a) ^ 2 := by
  obtain ⟨hA4, hA4le⟩ :=
    _root_.Prove2MeSourceProof.h_071eab4bde5a9ae7a7d5b921 (W.W i) ℱ (hcoord i) H hHm hHp hHs hCH0 hCH ha hab
  obtain ⟨hB4, hB4le⟩ :=
    _root_.Prove2MeSourceProof.h_071eab4bde5a9ae7a7d5b921 (W.W j) ℱ (hcoord j) K hKm hKp hKs hCK0 hCK ha hab
  obtain ⟨hint, hle⟩ := integrable_sq_mul_and_le
    (measurable_sub_stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a b)
    (measurable_sub_stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a b) hA4 hB4
  refine ⟨hint, le_trans hle ?_⟩
  linarith [hA4le, hB4le]
include hCH0 hCH hCK0 hCK in
/-- The cross increment lies in `L²`. -/
theorem memLp_two_crossIncrement (i j : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) 2 P :=
  (memLp_two_iff_integrable_sq
      (measurable_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b).aestronglyMeasurable).2
    (integrable_sq_crossIncrement_and_le W hcoord hHm hHp hHs hKm hKp hKs hCH0 hCH hCK0 hCK
      i j ha hab).1
/-- The cross increment is conditionally centred at the left endpoint of its cell. -/
theorem condExp_crossIncrement {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b | ℱ a] =ᵐ[P] 0 :=
  _root_.Prove2MeSourceProof.h_2b50de3fda4320b525536839 W hcoord hHm hHp hHs hKm hKp hKs hij ha hab
end CrossSum

end LevyStochCalc.Brownian.Ito


