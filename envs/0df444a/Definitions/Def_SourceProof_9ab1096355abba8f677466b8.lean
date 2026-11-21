-- Prove2me | Definitions.Def_SourceProof_9ab1096355abba8f677466b8
-- name    : SourceProof_9ab1096355abba8f677466b8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:41:28.116173+00:00
-- url     : https://prove2.me/theorems/3caef21e-10e7-499c-aa39-42b25bcd457b
-- title:
--   LevyStochCalc source module: SourceProof_9ab1096355abba8f677466b8
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian` comes from the `LevyStochCalc.Brownian.ItoL2CompletionApi` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F001
import Definitions.Def_SourceProof_2554b195ead815ae5442020c
import Definitions.Def_SourceProof_711d7a58a27af1d1b25e8dc9
import Definitions.Def_SourceProof_f68e93dfb81b09358de9c4e9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the `stochasticIntegral` API

The martingale property of the compensated square for the right-continuation `ℱ₊` of `ℱ`,
the unified existence theorem `itoIsometry_brownian_unified_existence` combining the
martingale, quadratic-variation and isometry conclusions, the isometry for differences of
integrands, and the `stochasticIntegral` interface with `itoIsometry`,
`quadVar_stochasticIntegral` and `martingale_stochasticIntegral`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end MasterSequence


theorem _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) (H₁ H₂ : Ω → ℝ → ℝ)
    (h_meas₁ : Measurable (Function.uncurry H₁)) (h_meas₂ : Measurable (Function.uncurry H₂))
    (h_progMeas₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (h_progMeas₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (h_sq₁ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_sq₂ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ T ω
        - stochasticIntegralBrownian W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have ht_nn : (0 : ℝ) ≤ T := le_of_lt hT
  set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  -- abbreviations for the two simple-integral sequences and the two limits
  have hImeas : ∀ (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
      (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
      (hs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (n : ℕ),
      Measurable (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hs n) T ω) := by
    intro H hm hp hs n
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ (fun i _ =>
      ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hs n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _)))
  -- the bridge `∫⁻_{P⊗ν} ‖f‖² = ∫⁻∫⁻_{[0,T]} ‖f(ω,s)‖²`
  have hbridge : ∀ f : Ω × ℝ → ℝ, Measurable f →
      ∫⁻ p, (‖f p‖₊ : ℝ≥0∞) ^ 2 ∂(P.prod ν)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro f hf
    rw [MeasureTheory.lintegral_prod _
      (((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
  -- `eval_n(H) → H` in `L²(P⊗ν)` for each integrand.
  have hevalL2 : ∀ (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
      (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
      (hs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun p : Ω × ℝ => (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hs n).eval p.2 p.1 - H p.1 p.2) 2 (P.prod ν))
        Filter.atTop (nhds 0) := by
    intro H hm hp hs
    have h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun p : Ω × ℝ => (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hs n).eval p.2 p.1 - H p.1 p.2) 2 (P.prod ν)
        ^ (2 : ℝ)) Filter.atTop (nhds 0) := by
      have he := _root_.Prove2MeSourceProof.h_f68e93dfb81b09358de9c4e9 (t := T) ℱ H hm hp hs
      refine he.congr (fun n => ?_)
      rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq,
        hbridge (fun p : Ω × ℝ => (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hs n).eval p.2 p.1 - H p.1 p.2)
          (((LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hs n).eval_jointly_measurable).sub hm)]
      refine lintegral_congr (fun ω => ?_)
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
      rw [show (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hs n).eval s ω‖₊ : ℝ≥0∞)
          = ‖(LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hs n).eval s ω - H ω s‖₊ from by
        rw [← nnnorm_neg]; congr 1; ring_nf]
    have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr (fun n => ?_)
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  -- LHS: `∫⁻‖Iₙ(H₁)−Iₙ(H₂)‖² → ∫⁻‖F₁−F₂‖²`
  have hLHS : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n) T ω
        - LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds (∫⁻ ω,
        (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ h_meas₂ h_progMeas₂
            h_sq₂ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)) := by
    refine _root_.Prove2MeSourceProof.h_711d7a58a27af1d1b25e8dc9
      (fun n => ((hImeas H₁ h_meas₁ h_progMeas₁ h_sq₁ n).sub
        (hImeas H₂ h_meas₂ h_progMeas₂ h_sq₂ n)).aestronglyMeasurable)
      ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₁ h_meas₁ h_progMeas₁
        h_sq₁ T).aestronglyMeasurable.sub
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₂ h_meas₂ h_progMeas₂
          h_sq₂ T).aestronglyMeasurable)
      (by
        refine (lt_of_le_of_lt (MeasureTheory.eLpNorm_sub_le
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₁ h_meas₁ h_progMeas₁
            h_sq₁ T).aestronglyMeasurable
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₂ h_meas₂ h_progMeas₂
            h_sq₂ T).aestronglyMeasurable
          (by norm_num)) (ENNReal.add_lt_top.mpr
            ⟨(LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ T).2,
              (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ T).2⟩)).ne)
      ?_
    have hsum := (_root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c W ℱ hℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ ht_nn).add
      (_root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c W ℱ hℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ ht_nn)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hsum)
      (Filter.Eventually.of_forall (fun n => bot_le))
      (Filter.Eventually.of_forall (fun n => ?_))
    refine le_trans ?_ (MeasureTheory.eLpNorm_sub_le
      ((hImeas H₁ h_meas₁ h_progMeas₁ h_sq₁ n).aestronglyMeasurable.sub
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₁ h_meas₁ h_progMeas₁
          h_sq₁ T).aestronglyMeasurable)
      ((hImeas H₂ h_meas₂ h_progMeas₂ h_sq₂ n).aestronglyMeasurable.sub
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₂ h_meas₂ h_progMeas₂
          h_sq₂ T).aestronglyMeasurable)
      (by norm_num))
    exact le_of_eq (MeasureTheory.eLpNorm_congr_ae
      (Filter.Eventually.of_forall (fun ω => by simp only [Pi.sub_apply]; ring)))
  -- RHS: `∫⁻∫⁻‖evalₙ(H₁)−evalₙ(H₂)‖² → ∫⁻∫⁻‖H₁−H₂‖²`
  have hHdfin : MeasureTheory.eLpNorm (fun p : Ω × ℝ => H₁ p.1 p.2 - H₂ p.1 p.2) 2 (P.prod ν)
      ≠ ⊤ :=
    (lt_of_le_of_lt (MeasureTheory.eLpNorm_sub_le
      (_root_.Prove2MeSourceProof.h_560d23a90584c8e4562d928f H₁ h_meas₁ h_sq₁ hT).1
      (_root_.Prove2MeSourceProof.h_560d23a90584c8e4562d928f H₂ h_meas₂ h_sq₂ hT).1 (by norm_num))
      (ENNReal.add_lt_top.mpr ⟨(_root_.Prove2MeSourceProof.h_560d23a90584c8e4562d928f H₁ h_meas₁ h_sq₁ hT).2,
        (_root_.Prove2MeSourceProof.h_560d23a90584c8e4562d928f H₂ h_meas₂ h_sq₂ hT).2⟩)).ne
  have hRHS' := _root_.Prove2MeSourceProof.h_711d7a58a27af1d1b25e8dc9
    (μ := P.prod ν)
    (gₙ := fun n p => (LevyStochCalc.Brownian.Ito.masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval p.2 p.1
      - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval p.2 p.1)
    (g := fun p => H₁ p.1 p.2 - H₂ p.1 p.2)
    (fun n => (((LevyStochCalc.Brownian.Ito.masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval_jointly_measurable).sub
      ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H₂ h_meas₂ h_progMeas₂
        h_sq₂ n).eval_jointly_measurable)).aestronglyMeasurable)
    (h_meas₁.aestronglyMeasurable.sub h_meas₂.aestronglyMeasurable) hHdfin
    (by
      have hsum := (hevalL2 H₁ h_meas₁ h_progMeas₁ h_sq₁).add
        (hevalL2 H₂ h_meas₂ h_progMeas₂ h_sq₂)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hsum)
        (Filter.Eventually.of_forall (fun n => bot_le))
        (Filter.Eventually.of_forall (fun n => ?_))
      refine le_trans ?_ (MeasureTheory.eLpNorm_sub_le
        (((LevyStochCalc.Brownian.Ito.masterApprox ℱ H₁ h_meas₁ h_progMeas₁
          h_sq₁ n).eval_jointly_measurable).aestronglyMeasurable.sub
          h_meas₁.aestronglyMeasurable)
        (((LevyStochCalc.Brownian.Ito.masterApprox ℱ H₂ h_meas₂ h_progMeas₂
          h_sq₂ n).eval_jointly_measurable).aestronglyMeasurable.sub
          h_meas₂.aestronglyMeasurable) (by norm_num))
      exact le_of_eq (MeasureTheory.eLpNorm_congr_ae
        (Filter.Eventually.of_forall (fun p => by simp only [Pi.sub_apply]; ring))))
  rw [hbridge (fun p : Ω × ℝ => H₁ p.1 p.2 - H₂ p.1 p.2) (h_meas₁.sub h_meas₂)] at hRHS'
  have hRHS : Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.Brownian.Ito.masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval s ω
        - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
    refine hRHS'.congr' (Filter.Eventually.of_forall (fun n => ?_))
    exact (hbridge _ (((LevyStochCalc.Brownian.Ito.masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval_jointly_measurable).sub
      ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval_jointly_measurable)))
  -- the two sequences agree (cross diff isometry); equate the limits.
  refine tendsto_nhds_unique (hLHS.congr' (Filter.Eventually.of_forall (fun n => ?_))) hRHS
  exact LevyStochCalc.Brownian.Ito.masterApprox_cross_diff_isometry W ℱ hℱ H₁ H₂ h_meas₁ h_meas₂ h_progMeas₁ h_progMeas₂
    h_sq₁ h_sq₂ n ht_nn
end LevyStochCalc.Brownian.Ito


