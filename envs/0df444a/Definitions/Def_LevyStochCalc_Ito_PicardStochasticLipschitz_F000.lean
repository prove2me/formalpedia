-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardStochasticLipschitz_F000
-- name    : LevyStochCalc_Ito_PicardStochasticLipschitz_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:32:33.060353+00:00
-- url     : https://prove2.me/theorems/a041b635-c5a2-4676-be7e-6ae6edf89934
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardStochasticLipschitz
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardStochasticLipschitz. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F001
import Definitions.Def_SourceProof_9ab1096355abba8f677466b8
import Mathlib.Algebra.Order.Chebyshev

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Lipschitz estimates for the stochastic components of the Picard map

The `L²`-isometry `𝔼|∫_0^T H₁ dW - ∫_0^T H₂ dW|² = 𝔼 ∫_0^T |H₁ - H₂|² ds` for the difference of
two Brownian Itô integrals, the discrete Cauchy-Schwarz inequality and the `ℝ≥0∞` norm-square
identities it is combined with, and the resulting per-component `L²` Lipschitz bounds for the
diffusion and the jump component of the Picard map in terms of the Lipschitz constants of `σ` and
`γ`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **L²-isometry for the *difference* of two Brownian Itô integrals** (formerly
cited axiom #17, now a theorem).

For two progressively-measurable, L²-bounded integrands `H₁, H₂`, the
difference `M¹_T - M²_T := ∫_0^T H₁ dW - ∫_0^T H₂ dW` satisfies the
L²-isometry against the *integrand difference*:

  `𝔼 |M¹_T - M²_T|² = 𝔼 ∫_0^T |H₁(s) - H₂(s)|² ds`.

**Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*,
Springer 1991, **Theorem 3.2.6** + the unique-extension lemma for the
L²-Itô integral as a continuous linear isometry from `L²(Ω × [0, T])`
to `L²(Ω)` (Karatzas-Shreve §3.2.B).

Now that `stochasticIntegral` is the genuine `L²`-limit construction
(`stochasticIntegralBrownian`), this follows from
`isometry_diff_stochasticIntegralBrownian`: both the integral difference and the
integrand difference are `L²`-limits of the same simple-integral difference. -/
theorem itoIsometry_diff_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H₁ H₂ : Ω → ℝ → ℝ)
    (h_meas₁ : Measurable (Function.uncurry H₁))
    (h_meas₂ : Measurable (Function.uncurry H₂))
    (h_progMeas₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (h_progMeas₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (h_sq_int_global₁ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_sq_int_global₂ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq_int_global₁ T ω
              - stochasticIntegral W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq_int_global₂ T ω‖₊
            : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  unfold stochasticIntegral
  exact _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ H₁ H₂ h_meas₁ h_meas₂
    h_progMeas₁ h_progMeas₂ h_sq_int_global₁ h_sq_int_global₂ hT
end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Cauchy-Schwarz on a finite sum (real form).**

For `d` real numbers `a₀, ..., a_{d-1}`, the discrete Cauchy-Schwarz
inequality gives `(∑_j a_j)² ≤ d · ∑_j a_j²`. Used below to bound the
squared norm of the row-`i` diffusion sum `∑_j ∫ σ(X)_{ij} dW^j_s` from
the per-component bounds. -/
lemma sum_sq_le_card_mul_sum_sq_real
    {d : ℕ} (a : Fin d → ℝ) :
    (∑ j : Fin d, a j) ^ 2 ≤ (d : ℝ) * ∑ j : Fin d, (a j) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := a)
  simpa [Finset.card_univ, Fintype.card_fin] using h
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Real-to-ENNReal nnnorm-square identity.**  For `r : ℝ`,

  `(‖r‖₊ : ℝ≥0∞)² = ENNReal.ofReal (r²)`.

The bridge between the real-side bookkeeping (where we manipulate
`(∑ j a_j)²` with ring/algebra rules) and the ENNReal-side bookkeeping
(where we apply isometry / lintegral mono). -/
lemma ennreal_nnnorm_sq_real (r : ℝ) :
    ((‖r‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (r ^ 2) := by
  have h1 : ((‖r‖₊ : ℝ≥0∞)) = ENNReal.ofReal |r| := by
    rw [show ((‖r‖₊ : ℝ≥0∞)) = ‖r‖ₑ from rfl, Real.enorm_eq_ofReal_abs]
  rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Normed-space ENNReal nnnorm-square identity.**  For a normed group
element `r : α`,

  `(‖r‖₊ : ℝ≥0∞)² = ENNReal.ofReal (‖r‖²)`.

Generalization of `ennreal_nnnorm_sq_real` to any `NormedAddCommGroup`,
used below for `Fin n → ℝ`-valued differences `X s ω - Y s ω`. -/
lemma ennreal_nnnorm_sq_normed {α : Type*} [NormedAddCommGroup α] (r : α) :
    ((‖r‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖r‖ ^ 2) := by
  have h : ((‖r‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖r‖ :=
    (ofReal_norm r).symm
  rw [h, ← ENNReal.ofReal_pow (norm_nonneg _)]
end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

end LevyStochCalc.Ito.Picard


