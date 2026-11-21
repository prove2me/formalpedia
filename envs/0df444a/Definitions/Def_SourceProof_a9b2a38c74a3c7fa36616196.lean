-- Prove2me | Definitions.Def_SourceProof_a9b2a38c74a3c7fa36616196
-- name    : SourceProof_a9b2a38c74a3c7fa36616196
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:03:57.674962+00:00
-- url     : https://prove2.me/theorems/9a2bb10d-793f-4752-8dac-70e99460e695
-- title:
--   LevyStochCalc source module: SourceProof_a9b2a38c74a3c7fa36616196
-- statement:
--   The original source theorem `LevyStochCalc.Driver.integral_mul_setIntegral_count` comes from the `LevyStochCalc.Driver.CellPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellPairing_F000
import Definitions.Def_SourceProof_31426d8eac40eee65570d324
import Definitions.Def_SourceProof_f2734a4bc0d51d1dd6733e48

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


theorem _root_.Prove2MeSourceProof.h_a9b2a38c74a3c7fa36616196 (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G.integral N hℱ ω ∂P = 0)
    {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V)
    {Mv : ℝ} (hVb : ∀ ω, |V ω| ≤ Mv)
    (G : MarkedHorizonIntegrand P ν ℱ T) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun)
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {Cg : ℝ} (hGb : ∀ ω s e, |G.toFun ω s e| ≤ Cg)
    {X : ℝ → Ω → ℝ} (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t)) {C : ℝ} (hC0 : 0 ≤ C)
    (hXb : ∀ s ω, |X s ω| ≤ C) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {τ : ℝ} (hτT : τ ≤ T) :
    ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
        X q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) ∂P
      = ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
          X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by
  classical
  have hVm : Measurable V := hVa.measurable.mono (ℱ.le a) le_rfl
  set F := G.cutMul hXc hXa hC0 hXb hA hAν hGpred τ with hFdef
  have hFa : ∀ ω s e, s ≤ a → F.toFun ω s e = 0 := by
    intro ω s e hs
    change LevyStochCalc.Poisson.Compensated.cutWindow X A τ ω s e * G.toFun ω s e = 0
    rw [hGa ω s e hs, mul_zero]
  -- the compensated half pairs to zero
  have hzero : ∫ ω, Z ω * V ω * F.integral N hℱ ω ∂P = 0 := by
    have hpull := _root_.Prove2MeSourceProof.h_f2734a4bc0d51d1dd6733e48 N hℱ hT F ha haT hFa hVa hVb
    have hcongr : ∫ ω, Z ω * ((F.mulLeft hFa hVa hVb).integral N hℱ ω) ∂P
        = ∫ ω, Z ω * V ω * F.integral N hℱ ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hpull] with ω hω
      rw [hω, mul_assoc]
    rw [← hcongr]
    exact hperp _
  -- the pathwise split of the window integral
  have hsplit := _root_.Prove2MeSourceProof.h_31426d8eac40eee65570d324 N hℱ G hXc hXa hC0
    hXb hA hAν hGpred hT hτT
  have hFint : MemLp (F.integral N hℱ) 2 P := LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ F
  have hIint : Integrable (fun ω => Z ω * V ω * F.integral N hℱ ω) P :=
    LevyStochCalc.Driver.integrable_mul_bdd_mul hZ2 hFint hVm hVb
  -- the compensator half is a bounded measurable function of the sample point
  have hXjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω) := by
    have h : Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) => X t ω) :=
      measurable_uncurry_of_continuous_of_measurable (fun ω => hXc ω)
        (fun t => ((hXa t).mono (ℱ.le t)).measurable)
    exact h.comp measurable_swap
  have hjoint : Measurable fun p : Ω × (ℝ × E) => X p.2.1 p.1 * G.toFun p.1 p.2.1 p.2.2 :=
    (hXjoint.comp (measurable_fst.prodMk measurable_snd.fst)).mul G.measurable_uncurry
  have hWfin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) τ ×ˢ A) ≠ ⊤ :=
    LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top hAν τ
  haveI : IsFiniteMeasure ((LevyStochCalc.Poisson.referenceIntensity ν).restrict (Set.Ioc (0 : ℝ) τ ×ˢ A)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hWfin⟩
  have hDm : StronglyMeasurable fun ω => ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
      X q.1 ω * G.toFun ω q.1 q.2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  have hDb : ∀ ω, ‖∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
      X q.1 ω * G.toFun ω q.1 q.2 ∂(LevyStochCalc.Poisson.referenceIntensity ν)‖
      ≤ (C * Cg) * ((LevyStochCalc.Poisson.referenceIntensity ν) (Set.Ioc (0 : ℝ) τ ×ˢ A)).toReal := by
    intro ω
    refine norm_setIntegral_le_of_norm_le_const ?_ fun q _ => ?_
    · exact lt_top_iff_ne_top.mpr hWfin
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hXb q.1 ω) (hGb ω q.1 q.2) (abs_nonneg _) hC0
  have hDint : Integrable (fun ω => Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
      X q.1 ω * G.toFun ω q.1 q.2 ∂(LevyStochCalc.Poisson.referenceIntensity ν)) P := by
    refine LevyStochCalc.Driver.integrable_mul_bdd_mul hZ2 ?_ hVm hVb
    exact MemLp.of_bound hDm.aestronglyMeasurable _
      (Filter.Eventually.of_forall hDb)
  -- assemble
  have hLHS : ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
        X q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) ∂P
      = ∫ ω, (Z ω * V ω * F.integral N hℱ ω
          + Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
              X q.1 ω * G.toFun ω q.1 q.2 ∂(LevyStochCalc.Poisson.referenceIntensity ν)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hsplit] with ω hω
    rw [hω]
    ring
  rw [hLHS, integral_add hIint hDint, hzero, zero_add]
end JumpTerm

section BrownianTerm

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

end BrownianTerm

section Assembly

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

end Assembly

end LevyStochCalc.Driver


