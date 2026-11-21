-- Prove2me | Definitions.Def_SourceProof_645d257df9a95d8a5a50a5aa
-- name    : SourceProof_645d257df9a95d8a5a50a5aa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:09:15.731933+00:00
-- url     : https://prove2.me/theorems/8d6c25b5-12c8-4095-a9d7-fdde0c2c5037
-- title:
--   LevyStochCalc source module: SourceProof_645d257df9a95d8a5a50a5aa
-- statement:
--   The original source theorem `LevyStochCalc.Driver.pairing_of_product_rule` comes from the `LevyStochCalc.Driver.CellPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellPairing_F001
import Definitions.Def_SourceProof_a9b2a38c74a3c7fa36616196

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing the jump term of the product rule

A weight orthogonal to every compensated integral over the horizon does not see the compensated
half of a window integral against the random measure: pairing it, times a bounded weight
measurable before the window, with the integral of a continuous adapted factor against the
random measure leaves only the integral against the reference intensity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section JumpTerm

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ}

end JumpTerm

section BrownianTerm

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

end BrownianTerm

section Assembly

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

include hℱN hℱW in

theorem _root_.Prove2MeSourceProof.h_645d257df9a95d8a5a50a5aa {T : ℝ} (hT : 0 < T) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (haT : a ≤ T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {Xg : ℝ → Ω → ℝ} (hXc : ∀ ω, Continuous fun t => Xg t ω)
    (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (Xg t)) {C : ℝ} (hC0 : 0 ≤ C)
    (hXb : ∀ s ω, |Xg s ω| ≤ C)
    {Y Yminus : ℝ → Ω → ℝ} (hYm : ∀ s, Measurable (Y s)) (hYb : ∀ s ω, |Y s ω| ≤ 1)
    (hYmm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Yminus s ω))
    (hYmb : ∀ s ω, |Yminus s ω| ≤ 1)
    {bdrift : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry bdrift)) {B : ℝ}
    (hBb : ∀ ω s, |bdrift ω s| ≤ B)
    (G : MarkedHorizonIntegrand P ν ℱ T) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun)
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {Cg : ℝ} (hGb : ∀ ω s e, |G.toFun ω s e| ≤ Cg)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {K : Ω → ℝ → ℝ} (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K) {Kb : ℝ}
    (hKbd : ∀ ω s, |K ω s| ≤ Kb)
    (hmg : Measurable (Function.uncurry fun ω s => K ω s * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => K ω s * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hid : ∀ᵐ ω ∂P, Xg t ω * Y t ω - Xg 0 ω * Y 0 ω
      = stochasticIntegralBrownian W ℱ hℱW
          (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω
        + (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume)
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) :
    ∫ ω, Z ω * V ω * (Xg t ω * Y t ω) ∂P
      = ∫ ω, Z ω * V ω * (Xg 0 ω * Y 0 ω) ∂P
        + ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
            Yminus s ω * bdrift ω s ∂volume) ∂P
        + ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            Xg q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by
  classical
  have hVm : Measurable V := hVa.measurable.mono (ℱ.le a) le_rfl
  -- the four bounded or square-integrable pieces
  have hSIBint : Integrable (fun ω => Z ω * V ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱW
      (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω) P :=
    LevyStochCalc.Driver.integrable_mul_bdd_mul hZ2 (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱW _ hmg hpg hqg t) hVm hVb
  have hDm : StronglyMeasurable fun ω => ∫ s in Set.Ioc (0 : ℝ) t,
      Yminus s ω * bdrift ω s ∂volume :=
    (hYmm.mul hbm).stronglyMeasurable.integral_prod_right'
  have hDb : ∀ ω, ‖∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume‖
      ≤ B * (volume (Set.Ioc (0 : ℝ) t)).toReal := by
    intro ω
    refine norm_setIntegral_le_of_norm_le_const ?_ fun s _ => ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · rw [Real.norm_eq_abs, abs_mul]
      calc |Yminus s ω| * |bdrift ω s| ≤ 1 * B :=
            mul_le_mul (hYmb s ω) (hBb ω s) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
  have hDint : Integrable (fun ω => Z ω * V ω * ∫ s in Set.Ioc (0 : ℝ) t,
      Yminus s ω * bdrift ω s ∂volume) P :=
    LevyStochCalc.Driver.integrable_mul_bdd_mul hZ2 (MemLp.of_bound hDm.aestronglyMeasurable _
      (Filter.Eventually.of_forall hDb)) hVm hVb
  have hprod : ∀ r : ℝ, Integrable (fun ω => Z ω * V ω * (Xg r ω * Y r ω)) P := by
    intro r
    refine LevyStochCalc.Driver.integrable_mul_bdd_mul hZ2 (MemLp.of_bound ?_ C ?_) hVm hVb
    · exact ((((hXa r).mono (ℱ.le r)).measurable.mul (hYm r))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_mul]
      calc |Xg r ω| * |Y r ω| ≤ C * 1 := mul_le_mul (hXb r ω) (hYb r ω) (abs_nonneg _) hC0
        _ = C := mul_one C
  have hjumpint : Integrable (fun ω => Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
      Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) P := by
    refine Integrable.congr (((hprod t).sub (hprod 0)).sub (hSIBint.add hDint)) ?_
    filter_upwards [hid] with ω hω
    simp only [Pi.sub_apply, Pi.add_apply]
    linear_combination (Z ω * V ω) * hω
  -- the two pairings that vanish or convert
  have hSIBzero := LevyStochCalc.Driver.integral_mul_stochasticIntegralBrownian_eq_zero W hℱW ha hab hZ2 hZito hVm
    hMv0 hVb hVa hKm hKp hKbd hmg hpg hqg ht
  have hjumpeq := _root_.Prove2MeSourceProof.h_a9b2a38c74a3c7fa36616196 N hℱN hT hZ2 hZcomp ha haT hVa hVb G hGpred
    hGa hGb hXc hXa hC0 hXb hA hAν htT
  -- assemble
  have hstep : ∫ ω, Z ω * V ω * (Xg t ω * Y t ω) ∂P
      = ∫ ω, (Z ω * V ω * (Xg 0 ω * Y 0 ω)
          + (Z ω * V ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱW
              (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω
            + (Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume)
              + Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
                  Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)))) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hid] with ω hω
    linear_combination (Z ω * V ω) * hω
  have h34 : Integrable (fun ω => Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
        Yminus s ω * bdrift ω s ∂volume)
      + Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) P := hDint.add hjumpint
  have h234 : Integrable (fun ω => Z ω * V ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱW
        (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω
      + (Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume)
        + Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω))) P := hSIBint.add h34
  rw [hstep, integral_add (hprod 0) h234, integral_add hSIBint h34,
    integral_add hDint hjumpint, hSIBzero, hjumpeq]
  ring
end Assembly

end LevyStochCalc.Driver


