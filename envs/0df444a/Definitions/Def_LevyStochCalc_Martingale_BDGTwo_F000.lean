-- Prove2me | Definitions.Def_LevyStochCalc_Martingale_BDGTwo_F000
-- name    : LevyStochCalc_Martingale_BDGTwo_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:09:44.303077+00:00
-- url     : https://prove2.me/theorems/10a8bf9b-2f5f-4bbc-8d38-e4dede9a9c8f
-- title:
--   Source declarations: LevyStochCalc.Martingale.BDGTwo
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Martingale.BDGTwo. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002
import Definitions.Def_LevyStochCalc_Poisson_Compensated_F001
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F003
import Definitions.Def_SourceProof_7aea30f549f53f05062f1907

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The `p = 2` Burkholder–Davis–Gundy upper bound for the stochastic integrals

Doob's `L²` inequality bounds the expected squared supremum of a right-continuous martingale by
four times its terminal second moment, and each integral's isometry identifies that second moment
with the energy of its integrand. For the compensated-Poisson integral the martingale and càdlàg
hypotheses are already available; for the Brownian integral they are carried by a right-continuous
martingale version of it.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Martingale

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Doob's bound for the Brownian Itô integral.** The expected squared supremum of a
right-continuous martingale version of `∫ H dW` over `[0, T]` is at most four times the energy of
`H` on `[0, T]`. -/
theorem lintegral_iSup_sq_le_energy_brownian {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {M : ℝ → Ω → ℝ} {F : Filtration ℝ ‹MeasurableSpace Ω›}
    (hMart : MeasureTheory.Martingale M F P)
    (hcad : ∀ᵐ ω ∂P, ∀ t : ℝ, Filter.Tendsto (fun s => M s ω)
      (nhdsWithin t (Set.Ioi t)) (nhds (M t ω)))
    (hMT : M T =ᵐ[P] Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hiso : ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    rw [← _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ H hm hp hq hT]
    exact lintegral_congr_ae (by filter_upwards [hMT] with ω hω; rw [hω])
  rw [← hiso]
  exact Probability.lintegral_iSup_sq_le_of_martingale hMart hT.le hcad
variable {E : Type v} [MeasurableSpace E]

/-- **Doob's bound for the compensated-Poisson integral.** The expected squared supremum of
`∫∫ φ dÑ` over `[0, T]` is at most four times the energy of `φ` on `[0, T]`. -/
theorem lintegral_iSup_sq_le_energy_compensated {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq_int_global : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Poisson.Compensated.stochasticIntegral N ℱ hℱ φ
        h_meas h_progMeas h_sq_int_global (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ φ h_meas h_progMeas
    h_sq_int_global T hT]
  refine Probability.lintegral_iSup_sq_le_of_martingale
    (Poisson.Compensated.martingale_stochasticIntegral_rightCont N ℱ hℱ φ h_meas h_progMeas
      h_sq_int_global) hT.le ?_
  filter_upwards [Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱ φ h_meas h_progMeas
    h_sq_int_global] with ω hω t
  exact (hω t).1
/-- The squared extended norm of a sum is at most twice the sum of the squares. -/
theorem sq_enorm_add_le (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  have h : ∀ z : ℝ, (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := fun z => by
    rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  rw [h, h, h, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])
/-- **Doob's bound for a sum of two right-continuous martingales.** -/
theorem lintegral_iSup_sq_sum_le {P : Measure Ω} [IsProbabilityMeasure P] {A B : ℝ → Ω → ℝ}
    {F : Filtration ℝ ‹MeasurableSpace Ω›} (hA : MeasureTheory.Martingale A F P)
    (hB : MeasureTheory.Martingale B F P)
    (hcadA : ∀ᵐ ω ∂P, ∀ t : ℝ, Filter.Tendsto (fun s => A s ω)
      (nhdsWithin t (Set.Ioi t)) (nhds (A t ω)))
    (hcadB : ∀ᵐ ω ∂P, ∀ t : ℝ, Filter.Tendsto (fun s => B s ω)
      (nhdsWithin t (Set.Ioi t)) (nhds (B t ω)))
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖A (t : ℝ) ω + B (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 8 * (∫⁻ ω, (‖A T ω‖₊ : ℝ≥0∞) ^ 2 ∂P) + 8 * ∫⁻ ω, (‖B T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  have hcad : ∀ᵐ ω ∂P, ∀ t : ℝ, Filter.Tendsto (fun s => A s ω + B s ω)
      (nhdsWithin t (Set.Ioi t)) (nhds (A t ω + B t ω)) := by
    filter_upwards [hcadA, hcadB] with ω h1 h2 t
    exact (h1 t).add (h2 t)
  have hmart : MeasureTheory.Martingale (fun t ω => A t ω + B t ω) F P := hA.add hB
  have hdoob := Probability.lintegral_iSup_sq_le_of_martingale hmart hT hcad
  refine hdoob.trans ?_
  have hmA : Measurable fun ω => (‖A T ω‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp
      ((hA.1 T).mono (F.le T)).measurable).coe_nnreal_ennreal).pow_const 2
  have hmB : Measurable fun ω => (‖B T ω‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp
      ((hB.1 T).mono (F.le T)).measurable).coe_nnreal_ennreal).pow_const 2
  have hsplit : ∫⁻ ω, (‖A T ω + B T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * (∫⁻ ω, (‖A T ω‖₊ : ℝ≥0∞) ^ 2 ∂P) + 2 * ∫⁻ ω, (‖B T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    rw [← lintegral_const_mul 2 hmA, ← lintegral_const_mul 2 hmB,
      ← lintegral_add_left (hmA.const_mul 2)]
    refine lintegral_mono fun ω => ?_
    calc (‖A T ω + B T ω‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖A T ω‖₊ : ℝ≥0∞) ^ 2 + (‖B T ω‖₊ : ℝ≥0∞) ^ 2) := sq_enorm_add_le _ _
      _ = 2 * (‖A T ω‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖B T ω‖₊ : ℝ≥0∞) ^ 2 := by ring
  calc 4 * ∫⁻ ω, (‖A T ω + B T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 4 * (2 * (∫⁻ ω, (‖A T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
          + 2 * ∫⁻ ω, (‖B T ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by gcongr
    _ = 8 * (∫⁻ ω, (‖A T ω‖₊ : ℝ≥0∞) ^ 2 ∂P) + 8 * ∫⁻ ω, (‖B T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by ring
end LevyStochCalc.Martingale


