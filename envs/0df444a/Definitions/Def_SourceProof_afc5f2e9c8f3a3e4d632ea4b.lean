-- Prove2me | Definitions.Def_SourceProof_afc5f2e9c8f3a3e4d632ea4b
-- name    : SourceProof_afc5f2e9c8f3a3e4d632ea4b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:17:12.683156+00:00
-- url     : https://prove2.me/theorems/e6a6238f-d789-46b2-9a00-4a0b25ea5f8b
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.Picard.integral_sq_le_mul_integral_sq_on_Icc
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_Setting_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki norm, the process space `S²`, and the drift step of Picard iteration

The Bielecki-weighted `L²` norm `‖X‖_{β,T} = sup_{t ∈ [0,T]} e^{-βt} (𝔼‖X_t‖²)^{1/2}` of a
process on `[0, T]`, the space `SBoundedProcess` of jointly measurable, progressively measurable,
almost surely càdlàg processes of finite norm at weight `0`, and the freeze of such a process at
the horizon, which leaves the norm unchanged and is `L²`-bounded at every later time.  The drift
component `picardStep_drift` of the Picard map is defined here, with its per-component difference
identities, its `L¹` Lipschitz bound, the Cauchy-Schwarz bound `(∫_0^t f)² ≤ t ∫_0^t f²` on a
window, and the per-component `L²` Lipschitz bound that follows from them.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace SBoundedProcess

end SBoundedProcess

omit [MeasurableSpace Ω] [MeasurableSpace E] in

theorem _root_.Prove2MeSourceProof.h_afc5f2e9c8f3a3e4d632ea4b
    (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf_nn : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)), 0 ≤ f s)
    (hf_L2 : MeasureTheory.MemLp f 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    (∫ s in Set.Icc (0 : ℝ) t, f s) ^ 2
      ≤ t * ∫ s in Set.Icc (0 : ℝ) t, (f s) ^ 2 := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)
  -- Constant function 1 ∈ L²(μ) since μ is finite.
  have h_one_L2 : MeasureTheory.MemLp (1 : ℝ → ℝ) 2 μ := MeasureTheory.memLp_const 1
  have h_one_nn : (0 : ℝ → ℝ) ≤ᵐ[μ] 1 :=
    Filter.Eventually.of_forall (fun _ => zero_le_one)
  have h2c : Real.HolderConjugate 2 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  -- Convert MemLp 2 to MemLp (ENNReal.ofReal 2) for Hölder API.
  have hf_L2' : MeasureTheory.MemLp f (ENNReal.ofReal 2) μ := by
    rwa [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by norm_num]
  have h_one_L2' : MeasureTheory.MemLp (1 : ℝ → ℝ) (ENNReal.ofReal 2) μ := by
    rwa [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by norm_num]
  -- Hölder: ∫ f · 1 ≤ (∫ f²)^(1/2) · (∫ 1²)^(1/2).
  have h_holder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := 2) (q := 2) h2c hf_nn h_one_nn hf_L2' h_one_L2'
  -- LHS simplification: ∫ f · 1 = ∫ f.
  have h_lhs_eq : ∫ a, f a * (1 : ℝ → ℝ) a ∂μ = ∫ a, f a ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    change f a * (1 : ℝ → ℝ) a = f a
    rw [Pi.one_apply, mul_one]
  -- ∫ 1² = ∫ 1 = t.
  have h_one_sq_eq_one :
      ∫ a, ((1 : ℝ → ℝ) a) ^ 2 ∂μ = ∫ _a : ℝ, (1 : ℝ) ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    change ((1 : ℝ → ℝ) a) ^ 2 = (1 : ℝ)
    rw [Pi.one_apply, one_pow]
  have h_one_int : ∫ _a : ℝ, (1 : ℝ) ∂μ = t := by
    rw [MeasureTheory.integral_const]
    change (μ Set.univ).toReal • (1 : ℝ) = t
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ht, smul_eq_mul, mul_one]
  have h_int_one_sq_eq_t : ∫ a, ((1 : ℝ → ℝ) a) ^ 2 ∂μ = t :=
    h_one_sq_eq_one.trans h_one_int
  rw [h_lhs_eq] at h_holder
  -- h_holder : ∫ f ≤ (∫ f²)^(1/2) · (∫ 1²)^(1/2).
  -- The `1 a ^ 2` in h_holder doesn't syntactically match my h_int_one_sq_eq_t LHS
  -- (Lean's elaboration of Pi.one_apply differs). Use calc directly with both.
  -- h_holder uses `^ (2 : ℝ)` (real exponent from HolderConjugate). Convert.
  have h_rpow_two_eq_sq : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have h_f_sq_conv : ∫ a, f a ^ (2 : ℝ) ∂μ = ∫ a, (f a) ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a =>
      h_rpow_two_eq_sq (f a))
  have h_one_sq_conv : ∫ a, ((1 : ℝ → ℝ) a) ^ (2 : ℝ) ∂μ =
      ∫ a, ((1 : ℝ → ℝ) a) ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a =>
      h_rpow_two_eq_sq _)
  have h_holder' : (∫ a, f a ∂μ) ≤
      (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) := by
    have h_step1 : (∫ a, f a ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) =
        (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by rw [h_f_sq_conv]
    have h_step2 : (∫ a, ((1 : ℝ → ℝ) a) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) =
        t ^ ((1 : ℝ) / 2) := by
      rw [h_one_sq_conv, h_int_one_sq_eq_t]
    calc (∫ a, f a ∂μ)
        ≤ (∫ a, f a ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
            (∫ a, ((1 : ℝ → ℝ) a) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := h_holder
      _ = (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) := by
            rw [h_step1, h_step2]
  clear h_holder
  have h_LHS_nn : 0 ≤ ∫ a, f a ∂μ := MeasureTheory.integral_nonneg_of_ae hf_nn
  have h_sq_int_nn : 0 ≤ ∫ a, (f a) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg_of_ae <| by
      filter_upwards [hf_nn] with s _ using sq_nonneg _
  have h_squared := mul_self_le_mul_self h_LHS_nn h_holder'
  have h_rpow_half_sq : ∀ a : ℝ, 0 ≤ a → a ^ ((1 : ℝ) / 2) * a ^ ((1 : ℝ) / 2) = a := by
    intro a ha
    rw [← Real.rpow_add_of_nonneg ha
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  calc (∫ a, f a ∂μ) ^ 2
      = (∫ a, f a ∂μ) * (∫ a, f a ∂μ) := by ring
    _ ≤ ((∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2)) *
        ((∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2)) := h_squared
    _ = ((∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) *
        (t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2)) := by ring
    _ = (∫ a, (f a) ^ 2 ∂μ) * t := by
        rw [h_rpow_half_sq _ h_sq_int_nn, h_rpow_half_sq _ ht]
    _ = t * ∫ a, (f a) ^ 2 ∂μ := by ring
end LevyStochCalc.Ito.Picard


