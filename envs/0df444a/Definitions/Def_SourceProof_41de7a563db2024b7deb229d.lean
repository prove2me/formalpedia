-- Prove2me | Definitions.Def_SourceProof_41de7a563db2024b7deb229d
-- name    : SourceProof_41de7a563db2024b7deb229d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:13:11.330176+00:00
-- url     : https://prove2.me/theorems/f152a434-0e51-4c95-b0bf-902ed5c39fc5
-- title:
--   LevyStochCalc source module: SourceProof_41de7a563db2024b7deb229d
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le_Ioc` comes from the `LevyStochCalc.Brownian.ItoIncrementMomentBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_3148dc49c4c32cf6b40c23ee
import Definitions.Def_SourceProof_7cac29e97200b3ccba83a5fa
import Definitions.Def_SourceProof_a7edd00a4084ca3841211aa5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of an increment of the Itô integral

The fourth moment of `∫_a^b H dW` for an integrand bounded by `C` is at most
`(6 + c)·C⁴·(b − a)²`, with `c` the fourth moment of the standard Gaussian, the second moment is
at most `C²·(b − a)`, and interpolating between the two by `2λ|y|³ ≤ λ²y² + y⁴` at `λ = √(b − a)`
bounds the third absolute moment. The fourth-moment bound is the per-tile variance budget of
`LevyStochCalc.Brownian.Ito.SimplePredictable.varClock` applied to simple approximants of
`1_{(a, b]}·H` that themselves vanish off `(a, b]`.

## Main statements

* `lintegral_stochasticIntegralBrownian_pow_four_le_Ioc` — the fourth-moment bound for an
  integrand supported in `(a, b]`.
* `lintegral_stochasticIntegralBrownian_sub_pow_four_le` —
  `𝔼|∫_a^b H dW|⁴ ≤ (6 + c)·C⁴·(b − a)²` for an integrand bounded by `C`.
* `lintegral_stochasticIntegralBrownian_sub_sq_le` — `𝔼|∫_a^b H dW|² ≤ C²·(b − a)`.
* `integral_abs_sub_pow_three_le` —
  `𝔼|∫_a^b H dW|³ ≤ ((C² + (6 + c)C⁴)/2)·(b − a)·√(b − a)`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section IncrementBound

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_41de7a563db2024b7deb229d
    (F : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry F))
    (hp : Probability.ProgressivelyMeasurable ℱ F)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ ω s, |F ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ ω s, s ∉ Set.Ioc a b → F ω s = 0) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
  classical
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  choose G0 hG0adapt hG0within using fun n : ℕ =>
    LevyStochCalc.Brownian.Ito.exists_adaptedSimple_within ℱ F hm hp hb (hq b hb)
      (show (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ from ENNReal.inv_pos.mpr
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))
  have hGadapt : ∀ n, ∀ i : Fin ((G0 n).truncate C).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (((G0 n).truncate C).partition i.castSucc)) (((G0 n).truncate C).ξ i) :=
    fun n => LevyStochCalc.Brownian.Ito.SimplePredictable.truncate_adapt ℱ (G0 n) C (hG0adapt n)
  have hGbdd : ∀ n, ∀ (i : Fin ((G0 n).truncate C).N) (ω : Ω),
      |((G0 n).truncate C).ξ i ω| ≤ C := fun n i ω => (G0 n).abs_truncate_xi_le hC0 i ω
  choose T3 Q hQadapt hQeval hQxi using fun n : ℕ =>
    _root_.Prove2MeSourceProof.h_a7edd00a4084ca3841211aa5 W ℱ ((G0 n).truncate C) (hGadapt n) hC0
      (hGbdd n) ha hab
  -- the restricted approximants are bounded by `C` and vanish off `(a, b]`
  have hQC : ∀ (n : ℕ) (j : Fin (Q n).N) (ω : Ω), |(Q n).ξ j ω| ≤ C := by
    intro n j ω
    refine (hQxi n j ω).trans ?_
    by_cases h : a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b
    · rw [if_pos h]
    · rw [if_neg h]; exact hC0
  have hQz : ∀ (n : ℕ) (j : Fin (Q n).N) (ω : Ω),
      ¬(a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b) → (Q n).ξ j ω = 0 := by
    intro n j ω h
    have := (hQxi n j ω).trans (le_of_eq (if_neg h))
    exact abs_nonpos_iff.mp this
  -- their elementary integrals at `b` are the ones the variance budget bounds
  have hQsimp : ∀ (n : ℕ) (ω : Ω),
      LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω = LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) (T3 n) ω :=
    fun n ω => (Q n).simpleIntegral_eq_of_support W (hQz n) le_rfl ω
  have hQbound : ∀ n : ℕ, ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
    intro n
    simp_rw [hQsimp n]
    refine le_trans ((Q n).lintegral_simpleIntegral_pow_four_le_varClock W ℱ hℱ (hQadapt n)
      hC0 (hQC n) (c := fun j => if a ≤ (Q n).partition j.castSucc
        ∧ (Q n).partition j.succ ≤ b then C else 0) (hQxi n)) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hV := (_root_.Prove2MeSourceProof.h_7cac29e97200b3ccba83a5fa (a := a) (b := b) (C := C) (Q n)) hab.le
    have hV0 := (Q n).varClock_nonneg
      (fun j => if a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b then C else 0)
      (Q n).N
    have hcg : (0 : ℝ) ≤ 6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment := by
      linarith [LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg]
    have hsq : (Q n).varClock
        (fun j => if a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b then C else 0)
        (Q n).N ^ 2 ≤ (C ^ 2 * (b - a)) ^ 2 := by
      nlinarith [hV, hV0]
    calc (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (Q n).varClock
            (fun j => if a ≤ (Q n).partition j.castSucc
              ∧ (Q n).partition j.succ ≤ b then C else 0) (Q n).N ^ 2
        ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 2 * (b - a)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hcg
      _ = (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by ring
  -- the restricted approximants still approximate `F`
  have hQwithin : ∀ n : ℕ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(Q n).eval s ω - F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    refine le_trans ?_ (hG0within n).le
    refine lintegral_mono fun ω => lintegral_mono fun s => ?_
    have hle : ‖(Q n).eval s ω - F ω s‖₊ ≤ ‖F ω s - (G0 n).eval s ω‖₊ := by
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm, Real.norm_eq_abs]
      have hstep : |(Q n).eval s ω - F ω s|
          ≤ |((G0 n).truncate C).eval s ω - F ω s| := by
        rw [hQeval n s ω]
        by_cases hs : s ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem hs]
          simp
        · rw [Set.indicator_of_notMem hs, zero_mul, hsupp ω s hs]
          simp
      refine hstep.trans ?_
      rw [(G0 n).truncate_eval hC0 s ω, abs_sub_comm (F ω s)]
      exact _root_.Prove2MeSourceProof.h_3148dc49c4c32cf6b40c23ee hC0 (hCF ω s)
    exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr hle) 2
  have htol : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
    refine h.congr fun n => ?_
    simp [Nat.cast_add_one]
  have hsq : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htol
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall fun n => ?_)
    rw [LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (Q n) (hQadapt n) F hm hp hq hb]
    exact hQwithin n
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω) 2 P) Filter.atTop (nhds 0) := by
    have hrw : ∀ n, MeasureTheory.eLpNorm
        (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω) 2 P
        = (∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
              ^ ((2 : ℝ))⁻¹ := by
      intro n
      rw [← LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq]
      exact (ENNReal.rpow_rpow_inv (by norm_num) _).symm
    simp_rw [hrw]
    have h := (ENNReal.continuous_rpow_const (y := ((2 : ℝ))⁻¹)).tendsto 0 |>.comp hsq
    simpa [Function.comp_def,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < ((2 : ℝ))⁻¹)] using h
  have hmeasG : ∀ n, Measurable (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω) := by
    intro n
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hmeasSI : Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b) :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ F hm hp hq b).mono (ℱ.le b)).measurable
  have hTIM : MeasureTheory.TendstoInMeasure P
      (fun n ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω) Filter.atTop
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun n => (hmeasG n).aestronglyMeasurable) hmeasSI.aestronglyMeasurable heL
  obtain ⟨ns, -, hns_ae⟩ := hTIM.exists_seq_tendsto_ae
  have hcont : Continuous fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4 := by
    have hfun : (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4)
        = fun x : ℝ => ((‖x‖₊ ^ 4 : ℝ≥0) : ℝ≥0∞) := by
      funext x; rw [ENNReal.coe_pow]
    rw [hfun]
    exact ENNReal.continuous_coe.comp (continuous_nnnorm.pow 4)
  have hfatou : ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ Filter.liminf (fun k => ∫⁻ ω,
        (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q (ns k)) b ω‖₊ : ℝ≥0∞) ^ 4 ∂P) Filter.atTop := by
    have h1 : ∀ᵐ ω ∂P,
        (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4
        = Filter.liminf (fun k =>
            (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q (ns k)) b ω‖₊ : ℝ≥0∞) ^ 4) Filter.atTop := by
      filter_upwards [hns_ae] with ω hω
      exact ((hcont.tendsto _).comp hω).liminf_eq.symm
    rw [lintegral_congr_ae h1]
    exact lintegral_liminf_le fun k => (hcont.measurable.comp (hmeasG (ns k)))
  exact hfatou.trans (Filter.liminf_le_of_frequently_le
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun k => hQbound (ns k))))
end IncrementBound

section ThirdMoment

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ThirdMoment

end LevyStochCalc.Brownian.Ito


