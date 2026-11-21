-- Prove2me | Definitions.Def_SourceProof_f7873a967b51c0099c698616
-- name    : SourceProof_f7873a967b51c0099c698616
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:49:40.367731+00:00
-- url     : https://prove2.me/theorems/3cd2857e-74ab-41c8-a085-88a176d26f23
-- title:
--   LevyStochCalc source module: SourceProof_f7873a967b51c0099c698616
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst` comes from the `LevyStochCalc.Brownian.ItoAlgebraAssociativity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_SourceProof_2554b195ead815ae5442020c
import Definitions.Def_SourceProof_e4a003adac246e81fe5cee0f
import Definitions.Def_SourceProof_f68e93dfb81b09358de9c4e9
import Definitions.Def_SourceProof_f876f8c69608bcdca53a63e6

open private eLpNorm_mul_le_of_bound from Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Associativity and locality of the `L²` Brownian Itô integral

Summing the increments of the `L²` Itô integral of a process `H` against the coefficients of a
simple integrand `G` gives the `L²` Itô integral of the product `G · H`; specialising to the step
integrands `1_{(a, b]}` identifies the `L²` Itô integral of an integrand restricted to `(a, b]`
with the increment of the integral of the unrestricted integrand across `(a, b]`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section Associativity

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in

theorem _root_.Prove2MeSourceProof.h_f7873a967b51c0099c698616 {t : ℝ} (ht : 0 < t) :
    G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
        hmm hmp hmq t := by
  classical
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  choose Th Q hQadapt hQeval hQint using fun n : ℕ =>
    _root_.Prove2MeSourceProof.h_f876f8c69608bcdca53a63e6 W ℱ G (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) h_adapt
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H hm hp hq n)
  choose Mb hMb using G.ξ_bounded
  -- measurability bookkeeping
  have hMmeas : ∀ u : ℝ, Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u) :=
    fun u => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq u).mono
      (ℱ.le u)).measurable
  have hInmeas : ∀ (n : ℕ) (u : ℝ),
      Measurable (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) u) := by
    intro n u
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hQmeas : ∀ n : ℕ, Measurable (LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t) := by
    intro n
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIAmeas : Measurable (G.integralAgainst
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t) := by
    unfold LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst
    exact Finset.measurable_sum _ fun i _ =>
      (G.ξ_measurable i).mul ((hMmeas _).sub (hMmeas _))
  have hconv : ∀ g : Ω → ℝ, MeasureTheory.eLpNorm g 2 P * MeasureTheory.eLpNorm g 2 P
      = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro g
    rw [← LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  -- (d) the product elementary integrals converge to the `L²` integral of `G.eval · H`
  have hd : Filter.Tendsto (fun n => ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    have hbd : ∀ s ω, (‖G.eval s ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
      intro s ω
      calc (‖G.eval s ω‖₊ : ℝ≥0∞)
          = ENNReal.ofReal ‖G.eval s ω‖ := by
            rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
        _ ≤ ENNReal.ofReal B :=
            ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).le.trans (hB s ω))
    have hne : ENNReal.ofReal B ^ 2 ≠ ⊤ := (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
    have hkey : ∀ n, ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
            hmm hmp hmq t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal B ^ 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P := by
      intro n
      rw [LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (Q n) (hQadapt n)
        (fun ω s => G.eval s ω * H ω s) hmm hmp hmq ht,
        ← MeasureTheory.lintegral_const_mul' _ _ hne]
      refine lintegral_mono fun ω => ?_
      rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
      refine lintegral_mono fun s => ?_
      have hrw : (Q n).eval s ω - G.eval s ω * H ω s
          = G.eval s ω * -(H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).eval s ω) := by
        rw [hQeval n s ω]; ring
      rw [hrw, nnnorm_mul, nnnorm_neg, ENNReal.coe_mul, mul_pow]
      gcongr
      exact hbd s ω
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Filter.Eventually.of_forall fun n => bot_le) (Filter.Eventually.of_forall hkey)
    have hml := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B ^ 2)
      (_root_.Prove2MeSourceProof.h_f68e93dfb81b09358de9c4e9 (t := t) ℱ H hm hp hq) (Or.inr hne)
    simpa using hml
  -- (e) the product elementary integrals converge to the integral against the `L²` integral
  have hu_nn : ∀ i : Fin G.N, 0 ≤ min (G.partition i.succ) t :=
    fun i => le_min (G.partition_nonneg _) ht.le
  have hu_nn' : ∀ i : Fin G.N, 0 ≤ min (G.partition i.castSucc) t :=
    fun i => le_min (G.partition_nonneg _) ht.le
  have hstep : ∀ n : ℕ, (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω)
      = ∑ i : Fin G.N,
        ((fun ω => G.ξ i ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n)
            (min (G.partition i.succ) t) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω))
        - (fun ω => G.ξ i ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n)
            (min (G.partition i.castSucc) t) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
              (min (G.partition i.castSucc) t) ω))) := by
    intro n
    funext ω
    simp only [Finset.sum_apply, Pi.sub_apply]
    rw [← hQint n t ω]
    unfold LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound : ∀ n : ℕ, MeasureTheory.eLpNorm (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω) 2 P
      ≤ ∑ i : Fin G.N, ((‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.succ) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω) 2 P
        + (‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.castSucc) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                (min (G.partition i.castSucc) t) ω) 2 P) := by
    intro n
    have haesm : ∀ (i : Fin G.N) (u : ℝ), MeasureTheory.AEStronglyMeasurable
        (fun ω => G.ξ i ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) u ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) P :=
      fun i u => ((G.ξ_measurable i).mul ((hInmeas n u).sub (hMmeas u))).aestronglyMeasurable
    rw [hstep n]
    refine le_trans (MeasureTheory.eLpNorm_sum_le
      (fun i _ => (haesm i _).sub (haesm i _)) (by norm_num)) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (MeasureTheory.eLpNorm_sub_le (haesm i _) (haesm i _) (by norm_num)) ?_
    exact add_le_add (eLpNorm_mul_le_of_bound (hMb i)) (eLpNorm_mul_le_of_bound (hMb i))
  have hlim : Filter.Tendsto (fun n : ℕ =>
      ∑ i : Fin G.N, ((‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.succ) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω) 2 P
        + (‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.castSucc) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                (min (G.partition i.castSucc) t) ω) 2 P)) Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ≥0∞) = ∑ _i : Fin G.N, (0 : ℝ≥0∞) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun i _ => ?_
    have h1 := ENNReal.Tendsto.const_mul (a := (‖Mb i‖₊ : ℝ≥0∞))
      (_root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c W ℱ hℱ H hm hp hq (hu_nn i)) (Or.inr ENNReal.coe_ne_top)
    have h2 := ENNReal.Tendsto.const_mul (a := (‖Mb i‖₊ : ℝ≥0∞))
      (_root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c W ℱ hℱ H hm hp hq (hu_nn' i)) (Or.inr ENNReal.coe_ne_top)
    simpa using h1.add h2
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω =>
      LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
        - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω) 2 P)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hbound)
  have he : Filter.Tendsto (fun n => ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    have h2 := ENNReal.Tendsto.mul heL (Or.inr (by simp)) heL (Or.inr (by simp))
    simpa [hconv] using h2
  -- squeeze the two limits together
  have hle : ∫⁻ ω,
      (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P ≤ 0 := by
    have hlim2 : Filter.Tendsto (fun n => 2 * ((∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
          - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
            : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
              hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)) Filter.atTop (nhds 0) := by
      have h3 := ENNReal.Tendsto.const_mul (a := 2) (he.add hd) (Or.inr (by simp))
      simpa using h3
    refine ge_of_tendsto hlim2 (Filter.Eventually.of_forall fun n => ?_)
    have hm2 : AEMeasurable (fun ω => (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
        - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
          : ℝ≥0∞) ^ 2) P :=
      ((((hQmeas n).sub hIAmeas).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.aemeasurable
    calc ∫⁻ ω, (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
              hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * ((‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
                : ℝ≥0∞) ^ 2
            + (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                  hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hrw : G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                    hmm hmp hmq t ω
              = -(LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
                    - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω)
                + (LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
                    - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                        hmm hmp hmq t ω) := by ring
          rw [hrw]
          refine le_trans (_root_.Prove2MeSourceProof.h_e4a003adac246e81fe5cee0f _ _) ?_
          rw [nnnorm_neg]
      _ = 2 * ((∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
                : ℝ≥0∞) ^ 2 ∂P)
            + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                  hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hm2]
  have hzero : ∫⁻ ω,
      (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P = 0 := le_antisymm hle bot_le
  have hSIm : Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => G.eval s ω * H ω s) hmm hmp hmq t) :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
      hmm hmp hmq t).mono (ℱ.le t)).measurable
  have hmeas : Measurable fun ω =>
      (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
            hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((hIAmeas.sub hSIm).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hzero] with ω hω
  have h0 : (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  simpa [sub_eq_zero] using h0
end Associativity

end LevyStochCalc.Brownian.Ito


