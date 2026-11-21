-- Prove2me | Definitions.Def_SourceProof_37464a1abdaa096cc46d9376
-- name    : SourceProof_37464a1abdaa096cc46d9376
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:25:40.084469+00:00
-- url     : https://prove2.me/theorems/28517a88-9126-4eaa-84bb-7c3bf6d0eb2f
-- title:
--   LevyStochCalc source module: SourceProof_37464a1abdaa096cc46d9376
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eval_simple` comes from the `LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F001
import Definitions.Def_SourceProof_2554b195ead815ae5442020c
import Definitions.Def_SourceProof_e4a003adac246e81fe5cee0f
import Definitions.Def_SourceProof_f68e93dfb81b09358de9c4e9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple integrands as integrands of the `L²` Brownian Itô integral

A simple integrand is uniformly bounded in both variables, jointly measurable, square-integrable
on every time window and, when its coefficients are adapted to a filtration, progressively
measurable, so it is an admissible integrand for the `L²` Itô integral in its own right; the two
elementary integrals of adapted simple integrands obey the Itô isometry for their difference at
an intermediate time, and the `L²` Itô integral of a simple integrand agrees almost everywhere
with its elementary integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section EvalSimple

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (hm : Measurable (Function.uncurry fun ω s => G.eval s ω))
  (hp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in

theorem _root_.Prove2MeSourceProof.h_37464a1abdaa096cc46d9376 {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t
      =ᵐ[P] simpleIntegral W G t := by
  classical
  have hIn : ∀ n : ℕ, Measurable
      (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t) := by
    intro n
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIG : Measurable (LevyStochCalc.Brownian.Ito.simpleIntegral W G t) := by
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      (G.ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hSI : Measurable
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t) :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ (fun ω s => G.eval s ω) hm
      hp hq t).mono (ℱ.le t)).measurable
  -- the master integrals converge to the elementary integral of `G`
  have hA : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
        - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    refine (_root_.Prove2MeSourceProof.h_f68e93dfb81b09358de9c4e9 (t := t) ℱ (fun ω s => G.eval s ω) hm hp hq).congr
      fun n => ?_
    rw [LevyStochCalc.Brownian.Ito.simpleIntegral_diff_isometry_of_adapted W ℱ hℱ _ G
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ (fun ω s => G.eval s ω) hm hp hq n) h_adapt ht]
    refine lintegral_congr fun ω =>
      MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    rw [← nnnorm_neg, neg_sub]
  -- and to the `L²` Itô integral
  have hconv : ∀ g : Ω → ℝ, MeasureTheory.eLpNorm g 2 P * MeasureTheory.eLpNorm g 2 P
      = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro g
    rw [← LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  have hB : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    have h := _root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq ht
    have h2 := ENNReal.Tendsto.mul h (Or.inr (by simp)) h (Or.inr (by simp))
    simpa [hconv] using h2
  -- squeeze
  have hle : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
      hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ 0 := by
    have hlim : Filter.Tendsto (fun n => 2 * ((∫⁻ ω,
        (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
            hq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
            hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P))
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := 2) (hB.add hA) (Or.inr (by simp))
      simpa using this
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    calc ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
          hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * ((‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm
              hp hq n) t ω - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => G.eval s ω) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2
            + (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
              hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hrw : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
                hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω
              = -(LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
                  hq n) t ω - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω)
                  hm hp hq t ω)
                + (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
                  hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) := by ring
          rw [hrw]
          refine le_trans (_root_.Prove2MeSourceProof.h_e4a003adac246e81fe5cee0f _ _) ?_
          rw [nnnorm_neg]
      _ = 2 * ((∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm
              hp hq n) t ω - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => G.eval s ω) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
            + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
              hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
          have hm2 : AEMeasurable (fun ω => (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ
              (fun ω s => G.eval s ω) hm hp hq n) t ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
                  hq t ω‖₊ : ℝ≥0∞) ^ 2) P :=
            ((((hIn n).sub hSI).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.aemeasurable
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hm2]
  have hzero : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm
      hp hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 :=
    le_antisymm hle bot_le
  have hmeas : Measurable fun ω => (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => G.eval s ω) hm hp hq t ω
        - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((hSI.sub hIG).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hzero] with ω hω
  have h0 : (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t ω
      - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  simpa [sub_eq_zero] using h0
end EvalSimple

end LevyStochCalc.Brownian.Ito


