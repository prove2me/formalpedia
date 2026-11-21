-- Prove2me | Definitions.Def_SourceProof_2ce5e97adb181ad2712fdce6
-- name    : SourceProof_2ce5e97adb181ad2712fdce6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:10:25.663686+00:00
-- url     : https://prove2.me/theorems/bac11830-e5a5-4c42-9709-328cd1fcc862
-- title:
--   LevyStochCalc source module: SourceProof_2ce5e97adb181ad2712fdce6
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_diagonal` comes from the `LevyStochCalc.Brownian.ItoSimpleMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Filtered_F001
import Definitions.Def_LevyStochCalc_Brownian_Filtered_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the terms of the elementary Brownian integral

For an adapted simple predictable integrand the diagonal term satisfies
`E[(ξ_i · ΔW_i) ^ 2] = (t_{i+1} - t_i) · E[ξ_i ^ 2]`, where
`ΔW_i = W_{t_{i+1}} - W_{t_i}`, since `ΔW_i` is independent of `ℱ_{t_i}` and centred Gaussian
with variance `t_{i+1} - t_i`, while for `i < j` the off-diagonal term vanishes,
`E[(ξ_i · ΔW_i) · (ξ_j · ΔW_j)] = 0`. Both rest on the integrability of the squared increments
and of the cross products.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_2ce5e97adb181ad2712fdce6
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N)
    (h_part_nn : 0 ≤ H.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω,
      (‖H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  set s : ℝ := H.partition i.castSucc with hs_def
  set t : ℝ := H.partition i.succ with ht_def
  set ΔW : Ω → ℝ := fun ω => W.W t ω - W.W s ω with hΔW_def
  set ξ : Ω → ℝ := H.ξ i with hξ_def
  have hst : s < t := H.partition_strictMono Fin.castSucc_lt_succ
  have h_ξ_meas : Measurable ξ := H.ξ_measurable i
  have h_ΔW_meas : Measurable ΔW := (W.measurable_eval t).sub (W.measurable_eval s)
  -- Step 1: Show IndepFun ξ ΔW.
  -- By h_adapt, σ(ξ) ⊆ F_s. By joint_increment_independent, F_s ⊥ σ(ΔW).
  -- So σ(ξ) ⊥ σ(ΔW), i.e., IndepFun ξ ΔW.
  have h_indep_F_ΔW := hℱ.indep h_part_nn hst
  have h_ξ_comap_le : MeasurableSpace.comap ξ inferInstance ≤ ℱ s :=
    h_adapt.measurable.comap_le
  have h_indep_ξ_ΔW : ProbabilityTheory.IndepFun ξ ΔW P := by
    -- Indep σ(ξ) σ(ΔW) P, using h_indep_F_ΔW and σ(ξ) ⊆ F_s.
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : MeasurableSet[ℱ s] u := h_ξ_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW
    exact h_indep_F_ΔW u v hu_F hv
  -- Step 2: Compose with norm² to get IndepFun on ENNReal.
  have h_nn_meas : Measurable (fun x : ℝ => (‖x‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_indep_norm_sq :
      ProbabilityTheory.IndepFun
        (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2)
        (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) P := by
    have := h_indep_ξ_ΔW.comp h_nn_meas h_nn_meas
    simpa [Function.comp_def] using this
  -- Step 3: ‖ξ · ΔW‖₊² = ‖ξ‖₊² · ‖ΔW‖₊² pointwise.
  have h_norm_mul : ∀ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)^2
      = (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2 := by
    intro ω
    rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)
        = (‖ξ ω‖₊ : ℝ≥0∞) * (‖ΔW ω‖₊ : ℝ≥0∞) from by
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)
          = ((‖ξ ω * ΔW ω‖₊ : ℝ≥0) : ℝ≥0∞) from rfl]
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0)
          = ‖ξ ω‖₊ * ‖ΔW ω‖₊ from nnnorm_mul _ _]
      push_cast; rfl]
    ring
  -- Step 4: Apply lintegral_mul for IndepFun.
  rw [show (∫⁻ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P from
    MeasureTheory.lintegral_congr h_norm_mul]
  rw [show (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2)
      = (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2)
        * (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) from rfl]
  have h_ξ_norm_sq_meas : Measurable (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_ΔW_norm_sq_meas : Measurable (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      h_ξ_norm_sq_meas h_ΔW_norm_sq_meas h_indep_norm_sq]
  -- Step 5: Compute ∫⁻ ‖ΔW‖₊² ∂P = ENNReal.ofReal(t - s).
  have h_ΔW_sq_int : ∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P
      = ENNReal.ofReal (t - s) := by
    -- Pushforward to gaussianReal:
    -- ∫⁻ ω, ‖ΔW‖₊² ∂P = ∫⁻ x, ‖x‖₊² ∂(P.map ΔW)
    --   = ∫⁻ x, ‖x‖₊² ∂(gaussianReal 0 ⟨t-s, _⟩)
    rw [show (∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P)
        = ∫⁻ x, (‖x‖₊ : ℝ≥0∞)^2 ∂(P.map ΔW) from
      (MeasureTheory.lintegral_map h_nn_meas h_ΔW_meas).symm]
    rw [W.increment_gaussian h_part_nn hst]
    -- ∫⁻ x, ‖x‖₊² ∂(gaussianReal 0 v) = ENNReal.ofReal v.
    -- Via ENNReal.ofReal of ∫ x², which equals v by gaussianReal_second_moment.
    have h_int_sq : MeasureTheory.Integrable (fun x : ℝ => x^2)
        (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) := by
      have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
          (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :=
        ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := (⟨t - s, by linarith⟩ : NNReal)) 2
      have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
      convert h using 1
      ext x
      change x^2 = ‖x‖^2
      rw [Real.norm_eq_abs, sq_abs]
    have h_nn_sq : 0 ≤ᵐ[ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩]
        fun x : ℝ => x^2 := by
      filter_upwards with x
      positivity
    have h_norm_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := by
      intro x
      rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from
            ofReal_norm x |>.symm]
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show (∫⁻ x, (‖x‖₊ : ℝ≥0∞)^2 ∂(ProbabilityTheory.gaussianReal 0
                ⟨t - s, by linarith⟩))
        = ∫⁻ x, ENNReal.ofReal (x^2) ∂(ProbabilityTheory.gaussianReal 0
                ⟨t - s, by linarith⟩) from
      MeasureTheory.lintegral_congr (fun x => h_norm_eq x)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sq h_nn_sq]
    rw [LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨t - s, by linarith⟩]
    rfl
  rw [h_ΔW_sq_int]
  ring
end LevyStochCalc.Brownian.Ito


