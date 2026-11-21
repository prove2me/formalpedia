-- Prove2me | Definitions.Def_SourceProof_1e4a5244ae2a7fe3cb105b9a
-- name    : SourceProof_1e4a5244ae2a7fe3cb105b9a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:18:25.467267+00:00
-- url     : https://prove2.me/theorems/609bbe60-d3ad-44d1-9534-14ed03ffa297
-- title:
--   LevyStochCalc source module: SourceProof_1e4a5244ae2a7fe3cb105b9a
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_continuous_modification_stochasticIntegralBrownian` comes from the `LevyStochCalc.Brownian.ItoQuadVarSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003
import Definitions.Def_SourceProof_0895508398bff4a45b14f57f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated square increments of the Itô integral

The increment `(M_b − M_a)² − ∫_a^b H_s² ds` of the compensated square of the Itô integral is
conditionally centred at its left endpoint, so a weighted sum of such increments over a
partition is a sum of martingale differences.

## Main statements

* `LevyStochCalc.Brownian.Ito.quadVarIncrement` — the compensated square increment.
* `LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement` — it is conditionally centred at the
  left endpoint.
* `LevyStochCalc.Brownian.Ito.compensator_sub_bounds` — the compensator increment across
  `(a, b]` lies between `0` and `C²(b − a)`.
* `LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le` — its second moment is at most
  `(2(6 + c) + 2)·C⁴·(b − a)²`.
* `LevyStochCalc.Brownian.Ito.integral_sq_weighted_quadVarSum_le` — the second moment of a
  weighted sum over a grid is at most `D²·(2(6 + c) + 2)·C⁴·∑ᵢ (tᵢ₊₁ − tᵢ)²`.
* `LevyStochCalc.Brownian.Ito.exists_continuous_modification_stochasticIntegralBrownian` — the
  Itô integral of a bounded integrand has a modification with continuous paths.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section QuadVarIncrement

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end QuadVarIncrement

section Bounds

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end Bounds

section IncrementL2

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end IncrementL2

section WeightedSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end WeightedSum

section ContinuousModification

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_1e4a5244ae2a7fe3cb105b9a :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous fun t => Y t ω)
        ∧ ∀ t : ℝ, 0 ≤ t →
            Y t =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
  classical
  set K : ℝ := (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 with hK
  have hK0 : 0 ≤ K := by
    have := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
    positivity
  set Xc : ℝ → Ω → ℝ :=
    fun t ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (max t 0) ω with hXc
  have hXmeas : ∀ t : ℝ, Measurable (Xc t) := fun t =>
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq (max t 0)).mono
      (ℱ.le _)).measurable
  -- the Kolmogorov condition with exponents `(4, 2)`
  have hpair : ∀ a b : ℝ, 0 ≤ a → a < b →
      ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
        ≤ ENNReal.ofReal (K * (b - a) ^ 2) := by
    intro a b ha hab
    have hswap : ∀ ω : Ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω‖₊ : ℝ≥0∞)
        = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) := by
      intro ω
      rw [← nnnorm_neg, neg_sub]
    simp_rw [hswap]
    exact _root_.Prove2MeSourceProof.h_0895508398bff4a45b14f57f W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hkol : ∀ s t : ℝ, ∫⁻ ω, edist (Xc s ω) (Xc t ω) ^ (4 : ℝ) ∂P
      ≤ (K.toNNReal : ℝ≥0∞) * edist s t ^ (2 : ℝ) := by
    intro s t
    have hnat4 : ∀ ω : Ω, edist (Xc s ω) (Xc t ω) ^ (4 : ℝ)
        = (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞) ^ (4 : ℕ) := by
      intro ω
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast,
        LevyStochCalc.Brownian.Ito.edist_eq_coe_nnnorm_sub]
    have hnat2 : edist s t ^ (2 : ℝ) = ENNReal.ofReal (|s - t| ^ 2) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, edist_dist,
        Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _)]
    have hdiff : |max s 0 - max t 0| ≤ |s - t| := abs_max_sub_max_le_abs s t 0
    simp_rw [hnat4]
    rw [hnat2, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      Real.coe_toNNReal K hK0]
    rcases lt_trichotomy (max s 0) (max t 0) with hst | hst | hst
    · refine le_trans (hpair (max s 0) (max t 0) (le_max_right _ _) hst) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : max t 0 - max s 0 ≤ |s - t| := by
        rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ max t 0 - max s 0), abs_sub_comm]
        exact hdiff
      have h2 : (0 : ℝ) ≤ max t 0 - max s 0 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) hK0
    · have hzero : ∀ ω : Ω, (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞) ^ (4 : ℕ) = 0 := by
        intro ω
        simp [hXc, hst]
      simp_rw [hzero]
      simp
    · have hswap : ∀ ω : Ω, (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞)
          = (‖Xc t ω - Xc s ω‖₊ : ℝ≥0∞) := fun ω => by rw [← nnnorm_neg, neg_sub]
      simp_rw [hswap]
      refine le_trans (hpair (max t 0) (max s 0) (le_max_right _ _) hst) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : max s 0 - max t 0 ≤ |s - t| := by
        rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ max s 0 - max t 0)]
        exact hdiff
      have h2 : (0 : ℝ) ≤ max s 0 - max t 0 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) hK0
  have hKolProc : ProbabilityTheory.IsKolmogorovProcess Xc P 4 2 K.toNNReal :=
    ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology hXmeas hkol
      (by norm_num) (by norm_num)
  obtain ⟨Y, hYcont, hYmod⟩ :=
    _root_.Prove2MeSourceProof.h_00d6535be52148842f88e973 P Xc hKolProc
      (by norm_num)
  refine ⟨Y, hYcont, fun t ht => ?_⟩
  have h := hYmod t
  simp only [hXc, max_eq_left ht] at h
  exact h
end ContinuousModification

end LevyStochCalc.Brownian.Ito


