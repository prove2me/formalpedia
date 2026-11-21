-- Prove2me | Definitions.Def_SourceProof_d5966497ad5bdb51775a8311
-- name    : SourceProof_d5966497ad5bdb51775a8311
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:25:35.883915+00:00
-- url     : https://prove2.me/theorems/aae5dfbd-8df8-4327-ae7b-0f356d5260e4
-- title:
--   LevyStochCalc source module: SourceProof_d5966497ad5bdb51775a8311
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_combineBM` comes from the `LevyStochCalc.Brownian.ItoDriverLinear` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000
import Definitions.Def_SourceProof_2554b195ead815ae5442020c
import Definitions.Def_SourceProof_7e6dc0a5b3abba2670f5e8de

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the Itô integral in the driver

The elementary integral of a simple integrand against a linear combination of Brownian motions is
the corresponding combination of the elementary integrals, and both sides of the resulting
identity are `L²`-limits along the same approximating sequence, so the identity passes to the
`L²` Itô integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}


theorem _root_.Prove2MeSourceProof.h_d5966497ad5bdb51775a8311 (W : Multidim.MultidimBrownianMotion P d)
    {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱB : IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ hℱB H hm hp hq t
      =ᵐ[P] fun ω => ∑ i, c i
        * stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω := by
  have hp1 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hSm : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (n : ℕ),
      AEStronglyMeasurable (LevyStochCalc.Brownian.Ito.simpleIntegral V (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) t) P := by
    intro V n
    refine (Finset.measurable_sum _ fun k _ => ?_).aestronglyMeasurable
    exact ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).ξ_measurable k).mul
      ((V.measurable_eval _).sub (V.measurable_eval _))
  have hIm : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (hV : LevyStochCalc.Brownian.IsBrownianFiltration V ℱ),
      AEStronglyMeasurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hV H hm hp hq t) P := by
    intro V hV
    exact ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted V ℱ hV H hm hp hq t).mono
      (ℱ.le t)).aestronglyMeasurable
  have hgm : AEStronglyMeasurable
      (fun ω => ∑ i, c i * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω) P := by
    have hpi : (fun ω => ∑ i, c i
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω)
        = ∑ i, fun ω => c i * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω := by
      funext ω; rw [Finset.sum_apply]
    rw [hpi]
    exact Finset.aestronglyMeasurable_sum _ fun i _ => (hIm (W.W i) (hℱi i)).const_mul _
  have hFf := _root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combineBM W hc)
    ℱ hℱB H hm hp hq ht
  have hFg : Filter.Tendsto (fun n => eLpNorm (fun ω =>
      LevyStochCalc.Brownian.Ito.simpleIntegral (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combineBM W hc)
          (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) t ω
        - ∑ i, c i * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω) 2 P)
      Filter.atTop (nhds 0) := by
    have hbound : ∀ n : ℕ, eLpNorm (fun ω =>
        LevyStochCalc.Brownian.Ito.simpleIntegral (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combineBM W hc)
            (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) t ω
          - ∑ i, c i * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω) 2 P
        ≤ ∑ i, ‖c i‖ₑ * eLpNorm (fun ω =>
            LevyStochCalc.Brownian.Ito.simpleIntegral (W.W i) (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) t ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω) 2 P := by
      intro n
      have hpi : (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combineBM W hc)
            (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) t ω
          - ∑ i, c i * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω)
          = ∑ i, (c i) • fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral (W.W i) (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) t ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω := by
        funext ω
        rw [Finset.sum_apply, LevyStochCalc.Brownian.Ito.simpleIntegral_combineBM W hc, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
      rw [hpi]
      refine le_trans (eLpNorm_sum_le (fun i _ => ?_) hp1) (le_of_eq ?_)
      · exact ((hSm (W.W i) n).sub (hIm (W.W i) (hℱi i))).const_smul _
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [eLpNorm_const_smul]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => zero_le) hbound
    have hzero : ∀ i : Fin d, Filter.Tendsto (fun n => ‖c i‖ₑ
        * eLpNorm (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral (W.W i) (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω) 2 P)
        Filter.atTop (nhds 0) := by
      intro i
      have hlim := _root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c (W.W i) ℱ (hℱi i) H hm hp hq ht
      have := ENNReal.Tendsto.const_mul (a := ‖c i‖ₑ) hlim (Or.inr (by simp))
      simpa using this
    simpa using tendsto_finsetSum Finset.univ fun i _ => hzero i
  exact _root_.Prove2MeSourceProof.h_7e6dc0a5b3abba2670f5e8de (fun n => hSm _ n) (hIm _ hℱB) hgm hFf hFg
end LevyStochCalc.Brownian.Ito


