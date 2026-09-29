-- Prove2me | solution 1 for AutomorphicForm.exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/48b954bf-d7ae-54d3-a759-46e395b1ac54

import Mathlib
import Theorems.Thm_MeasureTheory_tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz

set_option autoImplicit false

open MeasureTheory Filter Topology Complex
open scoped Real FourierTransform

namespace R4PackV5

theorem tendsto_integral_mul_exp_mul_I (D : ℝ → ℂ) (σ : ℝ) (hσ : σ ≠ 0) :
    Tendsto (fun R : ℝ => ∫ t : ℝ, D t * cexp ((σ * R * t : ℝ) * I)) atTop (𝓝 0) := by
  have hRL := Real.tendsto_integral_exp_smul_cocompact D
  have hlin : Tendsto (fun R : ℝ => -(σ * R) / (2 * π)) atTop (cocompact ℝ) := by
    rcases lt_or_gt_of_ne hσ with hneg | hpos
    · have h1 : Tendsto (fun R : ℝ => -(σ * R) / (2 * π)) atTop atTop := by
        have : Tendsto (fun R : ℝ => (-σ / (2 * π)) * R) atTop atTop :=
          Tendsto.const_mul_atTop (by apply div_pos (by linarith) (by positivity)) tendsto_id
        exact this.congr fun R => by ring
      exact h1.mono_right atTop_le_cocompact
    · have h1 : Tendsto (fun R : ℝ => -(σ * R) / (2 * π)) atTop atBot := by
        have : Tendsto (fun R : ℝ => (-σ / (2 * π)) * R) atTop atBot :=
          Tendsto.const_mul_atTop_of_neg (by
            apply div_neg_of_neg_of_pos (by linarith) (by positivity)) tendsto_id
        exact this.congr fun R => by ring
      exact h1.mono_right atBot_le_cocompact
  refine (hRL.comp hlin).congr fun R => ?_
  simp only [Function.comp_apply]
  congr 1
  funext t
  rw [Circle.smul_def, Real.fourierChar_apply, mul_comm (D t)]
  congr 2
  push_cast
  field_simp

theorem integrable_mul_exp_mul_I {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ) :
    Integrable fun t : ℝ => f t * cexp ((a * t : ℝ) * I) :=
  hf.mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun t => by rw [norm_exp_ofReal_mul_I])

theorem tendsto_integral_mul_cos {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun R : ℝ => ∫ t : ℝ, f t * ((Real.cos (2 * R * t) : ℝ) : ℂ)) atTop (𝓝 0) := by
  have h1 := tendsto_integral_mul_exp_mul_I f 2 two_ne_zero
  have h2 := tendsto_integral_mul_exp_mul_I f (-2) (by norm_num)
  have h := (h1.add h2).const_mul (1 / 2 : ℂ)
  rw [add_zero, mul_zero] at h
  refine h.congr fun R => ?_
  rw [← integral_add (integrable_mul_exp_mul_I hf (2 * R)) ?_, ← integral_const_mul]
  · congr 1
    funext t
    rw [Complex.ofReal_cos, ← mul_add, ← mul_assoc, mul_comm (1 / 2 : ℂ), mul_assoc]
    congr 1
    rw [Complex.cos]
    push_cast
    ring_nf
  · have := integrable_mul_exp_mul_I hf (-2 * R)
    exact this

theorem tendsto_integral_mul_sin {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun R : ℝ => ∫ t : ℝ, f t * ((Real.sin (2 * R * t) : ℝ) : ℂ)) atTop (𝓝 0) := by
  have h1 := tendsto_integral_mul_exp_mul_I f 2 two_ne_zero
  have h2 := tendsto_integral_mul_exp_mul_I f (-2) (by norm_num)
  have h := (h2.sub h1).const_mul (I / 2 : ℂ)
  rw [sub_zero, mul_zero] at h
  refine h.congr fun R => ?_
  rw [← integral_sub ?_ (integrable_mul_exp_mul_I hf (2 * R)), ← integral_const_mul]
  · congr 1
    funext t
    rw [Complex.ofReal_sin, ← mul_sub, ← mul_assoc, mul_comm (I / 2 : ℂ), mul_assoc]
    congr 1
    rw [Complex.sin]
    push_cast
    ring_nf
  · have := integrable_mul_exp_mul_I hf (-2 * R)
    exact this

noncomputable def ψ (t : ℝ) : ℂ := cexp (-(π : ℂ) * (t : ℂ) ^ 2)

theorem ψ_zero : ψ 0 = 1 := by simp [ψ]

theorem continuous_ψ : Continuous ψ := by unfold ψ; fun_prop

theorem norm_ψ (t : ℝ) : ‖ψ t‖ = Real.exp (-π * t ^ 2) := by
  unfold ψ
  rw [Complex.norm_exp]
  congr 1
  have : (-(π : ℂ) * (t : ℂ) ^ 2) = ((-π * t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

theorem integrable_ψ : Integrable ψ := by
  unfold ψ
  exact integrable_cexp_neg_mul_sq (by simp [Real.pi_pos])

theorem integral_norm_ψ : ∫ t, ‖ψ t‖ = 1 := by
  simp_rw [norm_ψ]
  rw [integral_gaussian, div_self Real.pi_pos.ne', Real.sqrt_one]

theorem integrable_fourier_ψ : Integrable (𝓕 ψ) := by
  have hψ : ψ = fun x : ℝ => cexp (-π * (1 : ℂ) * (x : ℂ) ^ 2) := by
    funext x; simp [ψ]
  rw [hψ, fourier_gaussian_pi (by simp)]
  have : (fun t : ℝ => 1 / (1 : ℂ) ^ (1 / 2 : ℂ) * cexp (-π / 1 * (t : ℂ) ^ 2)) =
      fun t : ℝ => cexp (-(π : ℂ) * (t : ℂ) ^ 2) := by
    funext t; simp
  rw [this]
  exact integrable_cexp_neg_mul_sq (by simp [Real.pi_pos])

theorem norm_one_sub_ψ_le {t : ℝ} (ht : |t| ≤ 1) : ‖1 - ψ t‖ ≤ π * |t| := by
  have hψr : ψ t = ((Real.exp (-π * t ^ 2) : ℝ) : ℂ) := by
    unfold ψ; push_cast; ring_nf
  rw [hψr, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h1 : Real.exp (-π * t ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, sq_nonneg t]
  have h2 : 1 - Real.exp (-π * t ^ 2) ≤ π * t ^ 2 := by
    have := Real.add_one_le_exp (-π * t ^ 2); linarith
  have h3 : π * t ^ 2 ≤ π * |t| := by
    have : t ^ 2 = |t| * |t| := by rw [← sq_abs]; ring
    rw [this]
    have h0 : 0 ≤ |t| := abs_nonneg t
    have h4 : |t| * |t| ≤ |t| * 1 := mul_le_mul_of_nonneg_left ht h0
    rw [mul_one] at h4
    exact mul_le_mul_of_nonneg_left h4 Real.pi_pos.le
  rw [abs_of_nonneg (by linarith)]
  linarith

noncomputable def osc (R t : ℝ) : ℂ := ((Real.sin (2 * R * t) / (2 * t) : ℝ) : ℂ)

theorem norm_osc_le (R t : ℝ) : ‖osc R t‖ ≤ |R| := by
  unfold osc
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases ht : t = 0
  · simp [ht]
  · rw [abs_div, div_le_iff₀ (by positivity)]
    calc |Real.sin (2 * R * t)| ≤ |2 * R * t| := Real.abs_sin_le_abs
      _ = |R| * |2 * t| := by rw [abs_mul, abs_mul, abs_mul]; ring

theorem measurable_osc (R : ℝ) : Measurable (osc R) := by
  unfold osc
  exact Complex.measurable_ofReal.comp
    ((Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)).div
      (measurable_const.mul measurable_id))

noncomputable def Dfac (R : ℝ) : ℂ := ∫ t : ℝ, ψ t * osc R t

theorem tendsto_Dfac : Tendsto Dfac atTop (𝓝 ((π : ℂ) / 2)) := by
  have hA := MeasureTheory.tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral ψ
    integrable_ψ integrable_fourier_ψ continuous_ψ.continuousAt
  rw [ψ_zero, mul_one] at hA
  have h2 : Tendsto (fun R : ℝ => 2 * R) atTop atTop := tendsto_id.const_mul_atTop two_pos
  have h := (hA.comp h2).const_mul (1 / 2 : ℂ)
  rw [show (1 / 2 : ℂ) * π = π / 2 by ring] at h
  refine h.congr fun R => ?_
  simp only [Function.comp_apply, Dfac]
  rw [← integral_const_mul]
  congr 1
  funext t
  unfold osc
  rw [mul_comm (ψ t), ← mul_assoc]
  congr 1
  push_cast
  ring

theorem eventually_norm_Dfac_le : ∀ᶠ R in atTop, ‖Dfac R‖ ≤ 3 := by
  have h := tendsto_Dfac.norm
  have hlt : ‖(π : ℂ) / 2‖ < 3 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    linarith [Real.pi_lt_four]
  filter_upwards [h.eventually (Iio_mem_nhds hlt)] with R hR using hR.le

section OnePair

variable {n : ℕ}

noncomputable def pS (P a : Fin n → Fin n → ℝ → ℂ) (t : ℝ) : ℂ := ∑ i, ∑ j, a i j t * P i j t

noncomputable def qS (Q a : Fin n → Fin n → ℝ → ℂ) (t : ℝ) : ℂ := ∑ i, ∑ j, a i j t * Q i j t

noncomputable def Gp (U V a : Fin n → Fin n → ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ i, ∑ j, a i j t * (U i j t + V i j t)

noncomputable def Gm (U V a : Fin n → Fin n → ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ i, ∑ j, a i j t * (U i j t - V i j t)

noncomputable def μm (U V a : Fin n → Fin n → ℝ → ℂ) (γ : ℝ → ℂ) (t : ℝ) : ℂ :=
  γ t * Gm U V a t / (2 * I * (t : ℂ))

noncomputable def ρ (U V a : Fin n → Fin n → ℝ → ℂ) (γ : ℝ → ℂ) (t : ℝ) : ℂ :=
  (γ t * Gp U V a t - γ 0 * Gp U V a 0 * ψ t) / (2 * (t : ℂ))

variable {P Q U V a : Fin n → Fin n → ℝ → ℂ}
variable (hPc : ∀ i j t, P i j t = P i j 0)
  (hQc : ∀ i j, Continuous (Q i j)) (hUc : ∀ i j, Continuous (U i j)) (hVc : ∀ i j, Continuous (V i j))
  (hac : ∀ i j, Continuous (a i j)) (hai : ∀ i j, Integrable (a i j))
  (haQ : ∀ i j, Integrable (fun t => a i j t * Q i j t))
  (haU : ∀ i j, Integrable (fun t => a i j t * U i j t))
  (haV : ∀ i j, Integrable (fun t => a i j t * V i j t))
  {Le : ℝ}
  (hL1 : ∑ i, ∑ j, ∫ t : ℝ, (‖a i j t‖ * (1 + ‖P i j t‖) + ‖a i j t * Q i j t‖ +
        ‖a i j t * U i j t‖ + ‖a i j t * V i j t‖) ≤ Le)
  (hL0 : ∑ i, ∑ j, ‖a i j 0‖ * (‖U i j 0‖ + ‖V i j 0‖) ≤ Le)
  (hLip : ∀ t : ℝ, |t| ≤ 1 →
      (∑ i, ∑ j, ‖a i j t * (U i j t + V i j t) - a i j 0 * (U i j 0 + V i j 0)‖) ≤ Le * |t| ∧
      (∑ i, ∑ j, ‖a i j t * (U i j t - V i j t)‖) ≤ Le * |t|)
  {γ : ℝ → ℂ} (hγc : Continuous γ) {B C : ℝ} (hγB : ∀ t, ‖γ t‖ ≤ B)
  (hγC : ∀ t, ‖γ t - γ 0‖ ≤ C * |t|)

include hPc hai in
theorem integrable_aP (i j : Fin n) : Integrable (fun t => a i j t * P i j t) := by
  have : (fun t => a i j t * P i j t) = fun t => a i j t * P i j 0 := by
    funext t; rw [hPc i j t]
  rw [this]
  exact (hai i j).mul_const _

include hPc hai in
theorem integrable_pS : Integrable (pS P a) := by
  unfold pS
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => integrable_aP hPc hai i j

include haQ in
theorem integrable_qS : Integrable (qS Q a) := by
  unfold qS
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => haQ i j

include haU haV in
theorem integrable_Gp : Integrable (Gp U V a) := by
  unfold Gp
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  simp_rw [mul_add]
  exact (haU i j).add (haV i j)

include haU haV in
theorem integrable_Gm : Integrable (Gm U V a) := by
  unfold Gm
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  simp_rw [mul_sub]
  exact (haU i j).sub (haV i j)

include hUc hVc hac in
theorem continuous_Gp : Continuous (Gp U V a) := by
  unfold Gp; fun_prop

include hUc hVc hac in
theorem continuous_Gm : Continuous (Gm U V a) := by
  unfold Gm; fun_prop

include hPc hai haQ haU haV in

theorem integrable_entry (i j : Fin n) :
    Integrable (fun t : ℝ => ‖a i j t‖ * (1 + ‖P i j t‖) + ‖a i j t * Q i j t‖ +
        ‖a i j t * U i j t‖ + ‖a i j t * V i j t‖) := by
  have h1 : Integrable (fun t : ℝ => ‖a i j t‖ * (1 + ‖P i j t‖)) := by
    have : (fun t : ℝ => ‖a i j t‖ * (1 + ‖P i j t‖)) = fun t => ‖a i j t‖ * (1 + ‖P i j 0‖) := by
      funext t; rw [hPc i j t]
    rw [this]
    exact (hai i j).norm.mul_const _
  exact ((h1.add (haQ i j).norm).add (haU i j).norm).add (haV i j).norm

private theorem sum_le_of_le {f g : Fin n → Fin n → ℝ} (h : ∀ i j, f i j ≤ g i j) :
    ∑ i, ∑ j, f i j ≤ ∑ i, ∑ j, g i j :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j

include hPc hai haQ haU haV hL1 in
theorem integral_norm_pS_le : ∫ t, ‖pS P a t‖ ≤ Le := by
  have hint : ∀ i j, Integrable (fun t => ‖a i j t * P i j t‖) := fun i j =>
    (integrable_aP hPc hai i j).norm
  calc ∫ t, ‖pS P a t‖ ≤ ∫ t, ∑ i, ∑ j, ‖a i j t * P i j t‖ := by
        refine integral_mono (integrable_pS hPc hai).norm
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j) fun t => ?_
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ = ∑ i, ∑ j, ∫ t, ‖a i j t * P i j t‖ := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j
    _ ≤ _ := by
        refine (sum_le_of_le fun i j => ?_).trans hL1
        refine integral_mono (hint i j) (integrable_entry hPc hai haQ haU haV i j) fun t => ?_
        have h0 : 0 ≤ ‖a i j t * Q i j t‖ + ‖a i j t * U i j t‖ + ‖a i j t * V i j t‖ := by positivity
        calc ‖a i j t * P i j t‖ = ‖a i j t‖ * ‖P i j t‖ := norm_mul _ _
          _ ≤ ‖a i j t‖ * (1 + ‖P i j t‖) := by
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); linarith [norm_nonneg (P i j t)]
          _ ≤ _ := by linarith

include hPc hai haQ haU haV hL1 in
theorem integral_norm_qS_le : ∫ t, ‖qS Q a t‖ ≤ Le := by
  have hint : ∀ i j, Integrable (fun t => ‖a i j t * Q i j t‖) := fun i j => (haQ i j).norm
  calc ∫ t, ‖qS Q a t‖ ≤ ∫ t, ∑ i, ∑ j, ‖a i j t * Q i j t‖ := by
        refine integral_mono (integrable_qS haQ).norm
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j) fun t => ?_
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ = ∑ i, ∑ j, ∫ t, ‖a i j t * Q i j t‖ := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j
    _ ≤ _ := by
        refine (sum_le_of_le fun i j => ?_).trans hL1
        refine integral_mono (hint i j) (integrable_entry hPc hai haQ haU haV i j) fun t => ?_
        have h0 : 0 ≤ ‖a i j t‖ * (1 + ‖P i j t‖) + ‖a i j t * U i j t‖ + ‖a i j t * V i j t‖ := by
          positivity
        linarith

include hPc hai haQ haU haV hL1 in
theorem integral_norm_Gp_le : ∫ t, ‖Gp U V a t‖ ≤ Le := by
  have hint : ∀ i j, Integrable (fun t => ‖a i j t * U i j t‖ + ‖a i j t * V i j t‖) := fun i j =>
    (haU i j).norm.add (haV i j).norm
  calc ∫ t, ‖Gp U V a t‖ ≤ ∫ t, ∑ i, ∑ j, (‖a i j t * U i j t‖ + ‖a i j t * V i j t‖) := by
        refine integral_mono (integrable_Gp haU haV).norm
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j) fun t => ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => ?_))
        rw [mul_add]; exact norm_add_le _ _
    _ = ∑ i, ∑ j, ∫ t, (‖a i j t * U i j t‖ + ‖a i j t * V i j t‖) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j
    _ ≤ _ := by
        refine (sum_le_of_le fun i j => ?_).trans hL1
        refine integral_mono (hint i j) (integrable_entry hPc hai haQ haU haV i j) fun t => ?_
        have h0 : 0 ≤ ‖a i j t‖ * (1 + ‖P i j t‖) + ‖a i j t * Q i j t‖ := by positivity
        linarith

include hPc hai haQ haU haV hL1 in
theorem integral_norm_Gm_le : ∫ t, ‖Gm U V a t‖ ≤ Le := by
  have hint : ∀ i j, Integrable (fun t => ‖a i j t * U i j t‖ + ‖a i j t * V i j t‖) := fun i j =>
    (haU i j).norm.add (haV i j).norm
  calc ∫ t, ‖Gm U V a t‖ ≤ ∫ t, ∑ i, ∑ j, (‖a i j t * U i j t‖ + ‖a i j t * V i j t‖) := by
        refine integral_mono (integrable_Gm haU haV).norm
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j) fun t => ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => ?_))
        rw [mul_sub]; exact norm_sub_le _ _
    _ = ∑ i, ∑ j, ∫ t, (‖a i j t * U i j t‖ + ‖a i j t * V i j t‖) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j
    _ ≤ _ := by
        refine (sum_le_of_le fun i j => ?_).trans hL1
        refine integral_mono (hint i j) (integrable_entry hPc hai haQ haU haV i j) fun t => ?_
        have h0 : 0 ≤ ‖a i j t‖ * (1 + ‖P i j t‖) + ‖a i j t * Q i j t‖ := by positivity
        linarith

include hL0 in
theorem norm_Gp_zero_le : ‖Gp U V a 0‖ ≤ Le := by
  unfold Gp
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => ?_)).trans hL0)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)

include hLip in
theorem norm_Gp_sub_le {t : ℝ} (ht : |t| ≤ 1) : ‖Gp U V a t - Gp U V a 0‖ ≤ Le * |t| := by
  unfold Gp
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans (hLip t ht).1)
  rw [← Finset.sum_sub_distrib]
  exact norm_sum_le _ _

include hLip in
theorem norm_Gm_le {t : ℝ} (ht : |t| ≤ 1) : ‖Gm U V a t‖ ≤ Le * |t| := by
  unfold Gm
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => norm_sum_le _ _).trans (hLip t ht).2)

include hL0 in
theorem Le_nonneg : 0 ≤ Le :=
  le_trans (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity) hL0

include hγB in
theorem B_nonneg : 0 ≤ B := (norm_nonneg _).trans (hγB 0)

include hUc hVc hac haU haV hPc hai haQ hL1 hL0 hLip hγc hγB in
theorem integrable_μm_and : Integrable (μm U V a γ) ∧
    ∫ t, ‖μm U V a γ t‖ ≤ 3 / 2 * B * Le := by
  have hB := B_nonneg hγB
  have hLe := Le_nonneg hL0

  set bd : ℝ → ℝ := fun t => Set.indicator (Set.Icc (-1) 1) (fun _ => B * Le / 2) t +
    B * ‖Gm U V a t‖ / 2 with hbd
  have hbdi : Integrable bd := by
    refine Integrable.add ?_ (((integrable_Gm haU haV).norm.const_mul B).div_const 2)
    exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hmeas : AEStronglyMeasurable (μm U V a γ) volume := by
    unfold μm
    refine ((hγc.mul (continuous_Gm hUc hVc hac)).measurable.div ?_).aestronglyMeasurable
    fun_prop
  have hle : ∀ t, ‖μm U V a γ t‖ ≤ bd t := by
    intro t
    unfold μm
    by_cases ht0 : t = 0
    · subst ht0
      simp only [hbd, Complex.ofReal_zero, mul_zero, div_zero, norm_zero]
      have : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by simp
      rw [Set.indicator_of_mem this]
      positivity
    have h2t : ‖(2 * I * (t : ℂ))‖ = 2 * |t| := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [norm_div, h2t, norm_mul]
    by_cases ht : |t| ≤ 1
    · have hmem : t ∈ Set.Icc (-1 : ℝ) 1 := by
        rw [Set.mem_Icc]; exact abs_le.mp ht
      rw [hbd]; dsimp only; rw [Set.indicator_of_mem hmem]
      have h1 : ‖γ t‖ * ‖Gm U V a t‖ / (2 * |t|) ≤ B * Le / 2 := by
        rw [div_le_iff₀ (by positivity)]
        calc ‖γ t‖ * ‖Gm U V a t‖ ≤ B * (Le * |t|) :=
              mul_le_mul (hγB t) (norm_Gm_le hLip ht) (norm_nonneg _) hB
          _ = B * Le / 2 * (2 * |t|) := by ring
      have h2 : 0 ≤ B * ‖Gm U V a t‖ / 2 := by positivity
      linarith
    · push Not at ht
      rw [hbd]; dsimp only
      rw [Set.indicator_of_notMem (by rw [Set.mem_Icc, ← abs_le]; exact not_le.mpr ht), zero_add,
        div_le_iff₀ (by positivity)]
      calc ‖γ t‖ * ‖Gm U V a t‖ ≤ B * ‖Gm U V a t‖ :=
            mul_le_mul_of_nonneg_right (hγB t) (norm_nonneg _)
        _ = B * ‖Gm U V a t‖ / 2 * (2 * 1) := by ring
        _ ≤ B * ‖Gm U V a t‖ / 2 * (2 * |t|) := by gcongr
  refine ⟨hbdi.mono' hmeas (ae_of_all _ hle), ?_⟩
  calc ∫ t, ‖μm U V a γ t‖ ≤ ∫ t, bd t := integral_mono_of_nonneg
        (ae_of_all _ fun t => norm_nonneg _) hbdi (ae_of_all _ hle)
    _ = (∫ t, Set.indicator (Set.Icc (-1) 1) (fun _ => B * Le / 2) t) +
          ∫ t, B * ‖Gm U V a t‖ / 2 := integral_add
        ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
        (((integrable_Gm haU haV).norm.const_mul B).div_const 2)
    _ ≤ B * Le + B * Le / 2 := by
        gcongr
        · rw [integral_indicator measurableSet_Icc, setIntegral_const]
          simp only [Real.volume_real_Icc, smul_eq_mul]
          norm_num
          nlinarith
        · simp_rw [div_eq_mul_inv]
          rw [integral_mul_const, integral_const_mul]
          have := integral_norm_Gm_le hPc hai haQ haU haV hL1
          nlinarith
    _ = 3 / 2 * B * Le := by ring

include hUc hVc hac haU haV hPc hai haQ hL1 hL0 hLip hγc hγB hγC in
theorem integrable_ρ_and : Integrable (ρ U V a γ) ∧
    ∫ t, ‖ρ U V a γ t‖ ≤ (6 * B + C) * Le := by
  have hB := B_nonneg hγB
  have hLe := Le_nonneg hL0
  have hC : 0 ≤ C := by
    have := hγC 1; simp only [abs_one, mul_one] at this; exact (norm_nonneg _).trans this
  have hG0 := norm_Gp_zero_le hL0
  set F0 : ℂ := γ 0 * Gp U V a 0 with hF0
  have hF0n : ‖F0‖ ≤ B * Le := by
    rw [hF0, norm_mul]; exact mul_le_mul (hγB 0) hG0 (norm_nonneg _) hB

  set K₁ : ℝ := ((1 + π) * B + C) * Le / 2 with hK₁
  set bd : ℝ → ℝ := fun t => Set.indicator (Set.Icc (-1) 1) (fun _ => K₁) t +
    (B * ‖Gp U V a t‖ + B * Le * ‖ψ t‖) / 2 with hbd
  have hbdi : Integrable bd := by
    refine Integrable.add ?_ ((((integrable_Gp haU haV).norm.const_mul B).add
      (integrable_ψ.norm.const_mul (B * Le))).div_const 2)
    exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hmeas : AEStronglyMeasurable (ρ U V a γ) volume := by
    unfold ρ
    refine (((hγc.mul (continuous_Gp hUc hVc hac)).sub
      (continuous_const.mul continuous_ψ)).measurable.div ?_).aestronglyMeasurable
    fun_prop
  have hle : ∀ t, ‖ρ U V a γ t‖ ≤ bd t := by
    intro t
    unfold ρ
    have hnn2 : 0 ≤ (B * ‖Gp U V a t‖ + B * Le * ‖ψ t‖) / 2 := by positivity
    have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
    by_cases ht0 : t = 0
    · subst ht0
      simp only [hbd, Complex.ofReal_zero, mul_zero, div_zero, norm_zero]
      have : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by simp
      rw [Set.indicator_of_mem this]
      positivity
    have h2t : ‖(2 * (t : ℂ))‖ = 2 * |t| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [norm_div, h2t]
    by_cases ht : |t| ≤ 1
    · have hmem : t ∈ Set.Icc (-1 : ℝ) 1 := by rw [Set.mem_Icc]; exact abs_le.mp ht
      rw [hbd]; dsimp only; rw [Set.indicator_of_mem hmem]

      have hsplit : γ t * Gp U V a t - F0 * ψ t =
          γ t * (Gp U V a t - Gp U V a 0) + (γ t - γ 0) * Gp U V a 0 + F0 * (1 - ψ t) := by
        rw [hF0]; ring
      have hnum : ‖γ t * Gp U V a t - F0 * ψ t‖ ≤ ((1 + π) * B + C) * Le * |t| := by
        rw [hsplit]
        refine (norm_add₃_le).trans ?_
        rw [norm_mul, norm_mul, norm_mul]
        calc ‖γ t‖ * ‖Gp U V a t - Gp U V a 0‖ + ‖γ t - γ 0‖ * ‖Gp U V a 0‖ + ‖F0‖ * ‖1 - ψ t‖
            ≤ B * (Le * |t|) + C * |t| * Le + B * Le * (π * |t|) := by
              gcongr
              · exact hγB t
              · exact norm_Gp_sub_le hLip ht
              · exact hγC t
              · exact norm_one_sub_ψ_le ht
          _ = ((1 + π) * B + C) * Le * |t| := by ring
      have h1 : ‖γ t * Gp U V a t - F0 * ψ t‖ / (2 * |t|) ≤ K₁ := by
        rw [div_le_iff₀ (by positivity), hK₁]
        calc ‖γ t * Gp U V a t - F0 * ψ t‖ ≤ ((1 + π) * B + C) * Le * |t| := hnum
          _ = ((1 + π) * B + C) * Le / 2 * (2 * |t|) := by ring
      linarith
    · push Not at ht
      rw [hbd]; dsimp only
      rw [Set.indicator_of_notMem (by rw [Set.mem_Icc, ← abs_le]; exact not_le.mpr ht), zero_add,
        div_le_iff₀ (by positivity)]
      calc ‖γ t * Gp U V a t - F0 * ψ t‖ ≤ ‖γ t‖ * ‖Gp U V a t‖ + ‖F0‖ * ‖ψ t‖ := by
            refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
        _ ≤ B * ‖Gp U V a t‖ + B * Le * ‖ψ t‖ := by
            gcongr
            exact hγB t
        _ = (B * ‖Gp U V a t‖ + B * Le * ‖ψ t‖) / 2 * (2 * 1) := by ring
        _ ≤ (B * ‖Gp U V a t‖ + B * Le * ‖ψ t‖) / 2 * (2 * |t|) := by gcongr
  refine ⟨hbdi.mono' hmeas (ae_of_all _ hle), ?_⟩
  calc ∫ t, ‖ρ U V a γ t‖ ≤ ∫ t, bd t := integral_mono_of_nonneg
        (ae_of_all _ fun t => norm_nonneg _) hbdi (ae_of_all _ hle)
    _ = (∫ t, Set.indicator (Set.Icc (-1) 1) (fun _ => K₁) t) +
          ∫ t, (B * ‖Gp U V a t‖ + B * Le * ‖ψ t‖) / 2 := integral_add
        ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
        ((((integrable_Gp haU haV).norm.const_mul B).add
          (integrable_ψ.norm.const_mul (B * Le))).div_const 2)
    _ ≤ 2 * K₁ + (B * Le + B * Le * 1) / 2 := by
        gcongr
        · rw [integral_indicator measurableSet_Icc, setIntegral_const]
          simp only [Real.volume_real_Icc, smul_eq_mul]
          norm_num
        · simp_rw [div_eq_mul_inv]
          rw [integral_mul_const, integral_add (((integrable_Gp haU haV).norm.const_mul B))
            (integrable_ψ.norm.const_mul (B * Le)), integral_const_mul, integral_const_mul,
            integral_norm_ψ]
          have := integral_norm_Gp_le hPc hai haQ haU haV hL1
          have h2 : B * ∫ t, ‖Gp U V a t‖ ≤ B * Le := mul_le_mul_of_nonneg_left this hB
          nlinarith
    _ = ((1 + π) * B + C) * Le + B * Le := by rw [hK₁]; ring
    _ ≤ (6 * B + C) * Le := by
        have : (1 + π) * B ≤ 5 * B := by nlinarith [Real.pi_lt_four]
        nlinarith

noncomputable def cosC (R t : ℝ) : ℂ := ((Real.cos (2 * R * t) : ℝ) : ℂ)

noncomputable def sinC (R t : ℝ) : ℂ := ((Real.sin (2 * R * t) : ℝ) : ℂ)

theorem norm_cosC_le (R t : ℝ) : ‖cosC R t‖ ≤ 1 := by
  unfold cosC; rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _

theorem norm_sinC_le (R t : ℝ) : ‖sinC R t‖ ≤ 1 := by
  unfold sinC; rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _

theorem continuous_cosC (R : ℝ) : Continuous (cosC R) := by unfold cosC; fun_prop
theorem continuous_sinC (R : ℝ) : Continuous (sinC R) := by unfold sinC; fun_prop

theorem exp_pos_eq (R t : ℝ) :
    cexp (2 * I * (R : ℂ) * (t : ℂ)) = cosC R t + sinC R t * I := by
  rw [show 2 * I * (R : ℂ) * (t : ℂ) = ((2 * R * t : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, cosC, sinC, Complex.ofReal_cos, Complex.ofReal_sin]

theorem exp_neg_eq (R t : ℝ) :
    cexp (-(2 * I * (R : ℂ) * (t : ℂ))) = cosC R t - sinC R t * I := by
  rw [show -(2 * I * (R : ℂ) * (t : ℂ)) = ((-(2 * R * t) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, cosC, sinC, Complex.ofReal_cos, Complex.ofReal_sin]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

theorem osc_eq (R t : ℝ) : osc R t = sinC R t / (2 * (t : ℂ)) := by
  unfold osc sinC; push_cast; rfl

theorem sinC_mul_I_div (R t : ℝ) : sinC R t * I / (2 * I * (t : ℂ)) = osc R t := by
  unfold sinC osc
  by_cases ht : t = 0
  · subst ht; simp
  · have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    push_cast
    field_simp

theorem summand_eq (γt c Pc Qc Uc Vc ac : ℂ) (R t : ℝ) :
    (γt * ac) * (c * (Pc * (2 * (R : ℂ)) - Qc
      + Uc * cexp (2 * I * (R : ℂ) * (t : ℂ)) / (2 * I * (t : ℂ))
      - Vc * cexp (-(2 * I * (R : ℂ) * (t : ℂ))) / (2 * I * (t : ℂ)))) =
    c * (2 * (R : ℂ)) * (γt * (ac * Pc)) - c * (γt * (ac * Qc))
      + c * (γt / (2 * I * (t : ℂ)) * cosC R t) * (ac * (Uc - Vc))
      + c * (γt * osc R t) * (ac * (Uc + Vc)) := by
  rw [exp_pos_eq, exp_neg_eq, ← sinC_mul_I_div]
  ring

theorem integrand_eq (P Q U V a : Fin n → Fin n → ℝ → ℂ) (γ : ℝ → ℂ) (c : ℂ) (R t : ℝ) :
    ∑ i, ∑ j, (γ t * a i j t) * (c * (P i j t * (2 * (R : ℂ)) - Q i j t
      + U i j t * cexp (2 * I * (R : ℂ) * (t : ℂ)) / (2 * I * (t : ℂ))
      - V i j t * cexp (-(2 * I * (R : ℂ) * (t : ℂ))) / (2 * I * (t : ℂ)))) =
    c * (2 * (R : ℂ)) * (γ t * pS P a t) - c * (γ t * qS Q a t)
      + c * (μm U V a γ t * cosC R t) + c * (γ t * Gp U V a t * osc R t) := by
  unfold pS qS μm Gm Gp
  simp_rw [summand_eq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

noncomputable def rest (Q U V a : Fin n → Fin n → ℝ → ℂ) (γ : ℝ → ℂ) (R : ℝ) : ℂ :=
  -(∫ t, γ t * qS Q a t) + (∫ t, μm U V a γ t * cosC R t)
    + (γ 0 * Gp U V a 0 * Dfac R + ∫ t, ρ U V a γ t * sinC R t)

include hPc hUc hVc hac hai haQ haU haV hL1 hL0 hLip hγc hγB hγC in

theorem integral_pair_eq (c : ℂ) (R : ℝ) :
    ∫ t, ∑ i, ∑ j, (γ t * a i j t) * (c * (P i j t * (2 * (R : ℂ)) - Q i j t
      + U i j t * cexp (2 * I * (R : ℂ) * (t : ℂ)) / (2 * I * (t : ℂ))
      - V i j t * cexp (-(2 * I * (R : ℂ) * (t : ℂ))) / (2 * I * (t : ℂ)))) =
    c * (2 * (R : ℂ)) * (∫ t, γ t * pS P a t) + c * rest Q U V a γ R := by
  have hB := B_nonneg hγB
  have hγm : AEStronglyMeasurable γ volume := hγc.aestronglyMeasurable
  have h1 : Integrable (fun t => γ t * pS P a t) :=
    (integrable_pS hPc hai).bdd_mul hγm (ae_of_all _ hγB)
  have h2 : Integrable (fun t => γ t * qS Q a t) :=
    (integrable_qS haQ).bdd_mul hγm (ae_of_all _ hγB)
  have h3 : Integrable (fun t => μm U V a γ t * cosC R t) :=
    (integrable_μm_and hPc hUc hVc hac hai haQ haU haV hL1 hL0 hLip hγc hγB).1.mul_bdd
      (continuous_cosC R).aestronglyMeasurable (ae_of_all _ (norm_cosC_le R))
  have h4 : Integrable (fun t => γ t * Gp U V a t * osc R t) :=
    ((integrable_Gp haU haV).bdd_mul hγm (ae_of_all _ hγB)).mul_bdd
      (measurable_osc R).aestronglyMeasurable (ae_of_all _ (norm_osc_le R))
  have h5 : Integrable (fun t => ρ U V a γ t * sinC R t) :=
    (integrable_ρ_and hPc hUc hVc hac hai haQ haU haV hL1 hL0 hLip hγc hγB hγC).1.mul_bdd
      (continuous_sinC R).aestronglyMeasurable (ae_of_all _ (norm_sinC_le R))
  have h6 : Integrable (fun t => ψ t * osc R t) :=
    integrable_ψ.mul_bdd (measurable_osc R).aestronglyMeasurable (ae_of_all _ (norm_osc_le R))

  have hD : ∫ t, γ t * Gp U V a t * osc R t =
      γ 0 * Gp U V a 0 * Dfac R + ∫ t, ρ U V a γ t * sinC R t := by
    have hpt : ∀ t, γ t * Gp U V a t * osc R t =
        γ 0 * Gp U V a 0 * (ψ t * osc R t) + ρ U V a γ t * sinC R t := by
      intro t
      unfold ρ
      rw [osc_eq]
      ring
    simp_rw [hpt]
    rw [integral_add (h6.const_mul _) h5, integral_const_mul]
    rfl
  simp_rw [integrand_eq]
  have i1 : Integrable (fun t => c * (2 * (R : ℂ)) * (γ t * pS P a t)) := h1.const_mul _
  have i2 : Integrable (fun t => c * (γ t * qS Q a t)) := h2.const_mul _
  have i3 : Integrable (fun t => c * (μm U V a γ t * cosC R t)) := h3.const_mul _
  have i4 : Integrable (fun t => c * (γ t * Gp U V a t * osc R t)) := h4.const_mul _
  have i12 : Integrable (fun t => c * (2 * (R : ℂ)) * (γ t * pS P a t) - c * (γ t * qS Q a t)) :=
    i1.sub i2
  have i123 : Integrable (fun t => c * (2 * (R : ℂ)) * (γ t * pS P a t) - c * (γ t * qS Q a t) +
      c * (μm U V a γ t * cosC R t)) := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_sub i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, hD]
  unfold rest
  ring

include hPc hUc hVc hac hai haQ haU haV hL1 hL0 hLip hγc hγB hγC in

theorem norm_rest_le {R : ℝ} (hR : ‖Dfac R‖ ≤ 3) :
    ‖rest Q U V a γ R‖ ≤ (12 * B + C) * Le := by
  have hB := B_nonneg hγB
  have hLe := Le_nonneg hL0
  have hγm : AEStronglyMeasurable γ volume := hγc.aestronglyMeasurable
  have hμ := integrable_μm_and hPc hUc hVc hac hai haQ haU haV hL1 hL0 hLip hγc hγB
  have hρ := integrable_ρ_and hPc hUc hVc hac hai haQ haU haV hL1 hL0 hLip hγc hγB hγC
  have hC : 0 ≤ C := by
    have := hγC 1; simp only [abs_one, mul_one] at this; exact (norm_nonneg _).trans this

  have e1 : ‖∫ t, γ t * qS Q a t‖ ≤ B * Le := by
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ t, ‖γ t * qS Q a t‖ ≤ ∫ t, B * ‖qS Q a t‖ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
            ((integrable_qS haQ).norm.const_mul B) (ae_of_all _ fun t => ?_)
          dsimp only
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hγB t) (norm_nonneg _)
      _ ≤ B * Le := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_norm_qS_le hPc hai haQ haU haV hL1) hB
  have e2 : ‖∫ t, μm U V a γ t * cosC R t‖ ≤ 3 / 2 * B * Le := by
    refine (norm_integral_le_integral_norm _).trans (le_trans ?_ hμ.2)
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hμ.1.norm
      (ae_of_all _ fun t => ?_)
    dsimp only
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_cosC_le R t) (norm_nonneg _)).trans (by rw [mul_one])
  have e3 : ‖γ 0 * Gp U V a 0 * Dfac R‖ ≤ B * Le * 3 := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hγB 0) (norm_Gp_zero_le hL0) (norm_nonneg _) hB) hR
      (norm_nonneg _) (by positivity)
  have e4 : ‖∫ t, ρ U V a γ t * sinC R t‖ ≤ (6 * B + C) * Le := by
    refine (norm_integral_le_integral_norm _).trans (le_trans ?_ hρ.2)
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hρ.1.norm
      (ae_of_all _ fun t => ?_)
    dsimp only
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_sinC_le R t) (norm_nonneg _)).trans (by rw [mul_one])
  unfold rest
  calc _ ≤ ‖-∫ t, γ t * qS Q a t‖ + ‖∫ t, μm U V a γ t * cosC R t‖
        + (‖γ 0 * Gp U V a 0 * Dfac R‖ + ‖∫ t, ρ U V a γ t * sinC R t‖) :=
        norm_add₃_le.trans (by gcongr; exact norm_add_le _ _)
    _ ≤ B * Le + 3 / 2 * B * Le + (B * Le * 3 + (6 * B + C) * Le) := by
        rw [norm_neg]; gcongr
    _ ≤ (12 * B + C) * Le := by nlinarith

include hPc hUc hVc hac hai haQ haU haV hL1 hL0 hLip hγc hγB hγC in

theorem tendsto_rest :
    Tendsto (rest Q U V a γ) atTop
      (𝓝 (-(∫ t, γ t * qS Q a t) + γ 0 * Gp U V a 0 * (π / 2))) := by
  have hμ := integrable_μm_and hPc hUc hVc hac hai haQ haU haV hL1 hL0 hLip hγc hγB
  have hρ := integrable_ρ_and hPc hUc hVc hac hai haQ haU haV hL1 hL0 hLip hγc hγB hγC
  have h1 : Tendsto (fun R => ∫ t, μm U V a γ t * cosC R t) atTop (𝓝 0) :=
    tendsto_integral_mul_cos hμ.1
  have h2 : Tendsto (fun R => ∫ t, ρ U V a γ t * sinC R t) atTop (𝓝 0) :=
    tendsto_integral_mul_sin hρ.1
  have h3 : Tendsto (fun R => γ 0 * Gp U V a 0 * Dfac R) atTop (𝓝 (γ 0 * Gp U V a 0 * (π / 2))) :=
    tendsto_Dfac.const_mul _
  have := ((tendsto_const_nhds (x := -(∫ t, γ t * qS Q a t))).add h1).add (h3.add h2)
  simp at this
  exact this

end OnePair

section Functional

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

omit [CompactSpace X] in
theorem integrable_comp_mul (g : C(X, ℂ)) {κv : ℝ → X} (hκ : Continuous κv) {w : ℝ → ℂ}
    (hw : Integrable w) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) :
    Integrable fun t => g (κv t) * w t :=
  hw.bdd_mul (g.continuous.comp hκ).aestronglyMeasurable (ae_of_all _ fun _ => hM _)

omit [CompactSpace X] in
theorem norm_integral_comp_mul_le (g : C(X, ℂ)) (κv : ℝ → X) {w : ℝ → ℂ} (hw : Integrable w)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, ‖g x‖ ≤ M) {Lw : ℝ} (hL : ∫ t, ‖w t‖ ≤ Lw) :
    ‖∫ t, g (κv t) * w t‖ ≤ M * Lw := by
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ t, ‖g (κv t) * w t‖ ≤ ∫ t, M * ‖w t‖ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hw.norm.const_mul M)
          (ae_of_all _ fun t => ?_)
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    _ ≤ M * Lw := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hL hM0

theorem exists_clm (κv : ι → ℝ → X) (hκ : ∀ e, Continuous (κv e)) (w : ι → ℝ → ℂ)
    (hw : ∀ e, Integrable (w e)) (L : ι → ℝ) (hL : Summable L) (hwL : ∀ e, ∫ t, ‖w e t‖ ≤ L e) :
    ∃ Λ : C(X, ℂ) →L[ℂ] ℂ, ∀ g, Λ g = ∑' e, ∫ t, g (κv e t) * w e t := by
  have hb : ∀ (g : C(X, ℂ)) e, ‖∫ t, g (κv e t) * w e t‖ ≤ ‖g‖ * L e := fun g e =>
    norm_integral_comp_mul_le g (κv e) (hw e) (norm_nonneg g) (fun x => g.norm_coe_le_norm x) (hwL e)
  have hs : ∀ g : C(X, ℂ), Summable fun e => ∫ t, g (κv e t) * w e t := fun g =>
    Summable.of_norm_bounded (hL.mul_left ‖g‖) (hb g)
  have hi : ∀ (g : C(X, ℂ)) e, Integrable fun t => g (κv e t) * w e t := fun g e =>
    integrable_comp_mul g (hκ e) (hw e) (fun x => g.norm_coe_le_norm x)
  let Λ₀ : C(X, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∑' e, ∫ t, g (κv e t) * w e t
      map_add' := fun g₁ g₂ => by
        simp only [ContinuousMap.add_apply, add_mul]
        rw [← (hs g₁).tsum_add (hs g₂)]
        exact tsum_congr fun e => integral_add (hi g₁ e) (hi g₂ e)
      map_smul' := fun r g => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        rw [← tsum_mul_left]
        exact tsum_congr fun e => integral_const_mul _ _ }
  refine ⟨Λ₀.mkContinuous (∑' e, L e) fun g => ?_, fun g => rfl⟩
  rw [mul_comm, ← tsum_mul_left]
  exact tsum_of_norm_bounded (hL.mul_left ‖g‖).hasSum (hb g)

theorem small_on_cylinders {Vι : Type*} {Xs : Set (Vι → ℂ × ℂ)} [CompactSpace Xs]
    (τ : ι → ℝ → (Vι → ℂ × ℂ)) (hτX : ∀ e t, τ e t ∈ Xs) (T : Finset Vι) (hT : T.Nonempty)
    (hτc : ∀ e, ∀ v ∈ T, Continuous fun t => τ e t v)
    (hnull : ∀ e, ∀ v ∈ T, ∀ w : ℂ × ℂ, volume {t | τ e t v = w} = 0)
    (w : ι → ℝ → ℂ) (hw : ∀ e, Integrable (w e)) (L : ι → ℝ) (hL : Summable L)
    (hwL : ∀ e, ∫ t, ‖w e t‖ ≤ L e)
    (Λ : C(Xs, ℂ) →L[ℂ] ℂ) (hΛ : ∀ g, Λ g = ∑' e, ∫ t, g ⟨τ e t, hτX e t⟩ * w e t)
    (τ₀ : Vι → ℂ × ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Vι → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ₀ v ∈ U v) ∧
      ∀ g : C(Xs, ℂ), (∀ y : Xs, (∃ v ∈ T, (y : Vι → ℂ × ℂ) v ∉ U v) → g y = 0) →
        (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε := by
  classical

  obtain ⟨E₀, hE₀⟩ :=
    ((tendsto_tsum_compl_atTop_zero L).eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨v₀, hv₀⟩ := hT

  let S : ι → ℕ → Set ℝ := fun e k => {t | ∀ v ∈ T, τ e t v ∈ Metric.ball (τ₀ v) (1 / ((k : ℝ) + 1))}
  have hSm : ∀ e k, MeasurableSet (S e k) := by
    intro e k
    have : S e k = ⋂ v ∈ T, (fun t => τ e t v) ⁻¹' Metric.ball (τ₀ v) (1 / ((k : ℝ) + 1)) := by
      ext t; simp [S]
    rw [this]
    exact (isOpen_biInter_finset fun v hv => (Metric.isOpen_ball.preimage (hτc e v hv))).measurableSet
  have hSa : ∀ e, Antitone (S e) := by
    intro e k k' hkk' t ht v hv
    have h1 : (1 : ℝ) / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hkk')
    exact Metric.ball_subset_ball h1 (ht v hv)
  have hSnull : ∀ e, volume (⋂ k, S e k) = 0 := by
    intro e
    refine measure_mono_null (fun t ht => ?_) (hnull e v₀ hv₀ (τ₀ v₀))
    simp only [Set.mem_iInter] at ht
    simp only [Set.mem_setOf_eq]
    by_contra hne
    have hpos : 0 < dist (τ e t v₀) (τ₀ v₀) := dist_pos.mpr hne
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    exact absurd (Metric.mem_ball.mp (ht k v₀ hv₀)) (not_lt.mpr hk.le)
  have hlim : ∀ e, Tendsto (fun k => ∫ t in S e k, ‖w e t‖) atTop (𝓝 0) := by
    intro e
    have := tendsto_setIntegral_of_antitone (μ := volume) (f := fun t => ‖w e t‖) (hSm e) (hSa e)
      ⟨0, (hw e).norm.integrableOn⟩
    rwa [setIntegral_measure_zero _ (hSnull e)] at this
  set δ : ℝ := ε / (2 * ((E₀.card : ℝ) + 1)) with hδ
  have hδp : 0 < δ := by rw [hδ]; positivity
  have hev : ∀ᶠ k in atTop, ∀ e ∈ E₀, ∫ t in S e k, ‖w e t‖ < δ := by
    rw [Finset.eventually_all]
    exact fun e _ => (hlim e).eventually (gt_mem_nhds hδp)
  obtain ⟨k₀, hk₀⟩ := hev.exists
  refine ⟨fun v => Metric.ball (τ₀ v) (1 / ((k₀ : ℝ) + 1)), fun v _ =>
    ⟨Metric.isOpen_ball, Metric.mem_ball_self (by positivity)⟩, fun g hg0 hg1 => ?_⟩

  have hXe : ∀ e, ‖∫ t, g ⟨τ e t, hτX e t⟩ * w e t‖ ≤ L e := fun e => by
    have := norm_integral_comp_mul_le g (fun t => (⟨τ e t, hτX e t⟩ : Xs)) (hw e) zero_le_one hg1 (hwL e)
    rwa [one_mul] at this
  have hXe' : ∀ e ∈ E₀, ‖∫ t, g ⟨τ e t, hτX e t⟩ * w e t‖ ≤ δ := by
    intro e he
    have hz : ∀ t, t ∉ S e k₀ → g ⟨τ e t, hτX e t⟩ * w e t = 0 := by
      intro t ht
      simp only [S, Set.mem_setOf_eq, not_forall] at ht
      obtain ⟨v, hv, hnot⟩ := ht
      rw [hg0 _ ⟨v, hv, hnot⟩, zero_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine (norm_integral_le_integral_norm _).trans (le_trans ?_ (hk₀ e he).le)
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hw e).norm.integrableOn
      (ae_of_all _ fun t => ?_)
    dsimp only
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hg1 _) (norm_nonneg _)).trans (by rw [one_mul])
  have hsX : Summable fun e => ‖∫ t, g ⟨τ e t, hτX e t⟩ * w e t‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hXe hL
  rw [hΛ g]
  calc ‖∑' e, ∫ t, g ⟨τ e t, hτX e t⟩ * w e t‖ ≤ ∑' e, ‖∫ t, g ⟨τ e t, hτX e t⟩ * w e t‖ :=
        norm_tsum_le_tsum_norm hsX
    _ = ∑ e ∈ E₀, ‖∫ t, g ⟨τ e t, hτX e t⟩ * w e t‖ +
          ∑' e : {x // x ∉ E₀}, ‖∫ t, g ⟨τ e t, hτX e t⟩ * w e t‖ :=
        (hsX.sum_add_tsum_subtype_compl E₀).symm
    _ ≤ ∑ e ∈ E₀, δ + ∑' e : {x // x ∉ E₀}, L e := by
        exact add_le_add (Finset.sum_le_sum fun e he => hXe' e he)
          (Summable.tsum_le_tsum (fun e : {x // x ∉ E₀} => hXe e) (hsX.subtype _) (hL.subtype _))
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add_of_le_of_lt _ hE₀
        rw [Finset.sum_const, nsmul_eq_mul, hδ]
        rw [show (E₀.card : ℝ) * (ε / (2 * ((E₀.card : ℝ) + 1))) =
          ε / 2 * ((E₀.card : ℝ) / ((E₀.card : ℝ) + 1)) by field_simp]
        have : (E₀.card : ℝ) / ((E₀.card : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        nlinarith
    _ = ε := by ring

theorem exists_enum {ιc : Type*} [Countable ιc] {Y : Type*} (y₀ : Y) (pt : ιc → Y) (m : ιc → ℂ)
    (hm : Summable fun e => ‖m e‖) :
    ∃ (tabs : ℕ → Y) (cs : ℕ → ℂ), (Summable fun n => ‖cs n‖) ∧
      (∀ n, cs n ≠ 0 → ∃ e, cs n = m e ∧ tabs n = pt e) ∧
      ∀ G : Y → ℂ, (∑' n, cs n * G (tabs n)) = ∑' e, m e * G (pt e) := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ιc
  refine ⟨Function.extend f pt (fun _ => y₀), Function.extend f m 0, ?_, fun n hn => ?_, fun G => ?_⟩
  · have : (fun n => ‖Function.extend f m 0 n‖) = Function.extend f (fun e => ‖m e‖) 0 := by
      funext n
      by_cases h : ∃ e, f e = n
      · obtain ⟨e, rfl⟩ := h; rw [hf.extend_apply, hf.extend_apply]
      · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]; simp
    rw [this]
    exact (summable_extend_zero hf).mpr hm
  · by_cases h : ∃ e, f e = n
    · obtain ⟨e, rfl⟩ := h
      exact ⟨e, by rw [hf.extend_apply], by rw [hf.extend_apply]⟩
    · exact absurd (by rw [Function.extend_apply' _ _ _ h]; rfl) hn
  · have : (fun n => Function.extend f m 0 n * G (Function.extend f pt (fun _ => y₀) n)) =
        Function.extend f (fun e => m e * G (pt e)) 0 := by
      funext n
      by_cases h : ∃ e, f e = n
      · obtain ⟨e, rfl⟩ := h; rw [hf.extend_apply, hf.extend_apply, hf.extend_apply]
      · simp only [Function.extend_apply' _ _ _ h, Pi.zero_apply, zero_mul]
    rw [this]
    exact tsum_extend_zero hf _

end Functional

section ProdBounds

theorem norm_pow_sub_pow_le (x y : ℂ) {M : ℝ} (hM : 1 ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (k : ℕ) :
    ‖x ^ k - y ^ k‖ ≤ k * M ^ k * ‖x - y‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hM0 : 0 ≤ M := by linarith
    have hsplit : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have hyk : ‖y‖ ^ k ≤ M ^ k := pow_le_pow_left₀ (norm_nonneg _) hy k
    have hMk : M ^ k ≤ M ^ (k + 1) := pow_le_pow_right₀ hM (Nat.le_succ k)
    have hxy := norm_nonneg (x - y)
    calc ‖x‖ * ‖x ^ k - y ^ k‖ + ‖x - y‖ * ‖y‖ ^ k
        ≤ M * (k * M ^ k * ‖x - y‖) + ‖x - y‖ * M ^ k := by gcongr
      _ = (k * M ^ (k + 1) + M ^ k) * ‖x - y‖ := by ring
      _ ≤ (k * M ^ (k + 1) + M ^ (k + 1)) * ‖x - y‖ := by gcongr
      _ = ((k + 1 : ℕ) : ℝ) * M ^ (k + 1) * ‖x - y‖ := by push_cast; ring

theorem prod_bounds {ιv Pm : Type*} [DecidableEq ιv] (T : Finset ιv) (f : ιv → Pm → ℝ → ℂ)
    (hb : ∀ v ∈ T, ∃ b, ∀ p t, ‖f v p t‖ ≤ b)
    (hl : ∀ v ∈ T, ∃ d, ∀ p t, ‖f v p t - f v p 0‖ ≤ d * |t|) :
    (∃ b, 0 ≤ b ∧ ∀ p t, ‖∏ v ∈ T, f v p t‖ ≤ b) ∧
      (∃ d, ∀ p t, ‖∏ v ∈ T, f v p t - ∏ v ∈ T, f v p 0‖ ≤ d * |t|) := by
  induction T using Finset.induction_on with
  | empty => exact ⟨⟨1, zero_le_one, fun p t => by simp⟩, ⟨0, fun p t => by simp⟩⟩
  | insert v T hv ih =>
    obtain ⟨⟨bT, hbT0, hbT⟩, ⟨dT, hdT⟩⟩ := ih (fun u hu => hb u (Finset.mem_insert_of_mem hu))
      (fun u hu => hl u (Finset.mem_insert_of_mem hu))
    obtain ⟨bv, hbv⟩ := hb v (Finset.mem_insert_self v T)
    obtain ⟨dv, hdv⟩ := hl v (Finset.mem_insert_self v T)
    refine ⟨⟨max bv 0 * bT, by positivity, fun p t => ?_⟩, ⟨max bv 0 * dT + dv * bT, fun p t => ?_⟩⟩
    · rw [Finset.prod_insert hv, norm_mul]
      exact mul_le_mul ((hbv p t).trans (le_max_left _ _)) (hbT p t) (norm_nonneg _) (le_max_right _ _)
    · rw [Finset.prod_insert hv, Finset.prod_insert hv]
      have hsplit : f v p t * ∏ u ∈ T, f u p t - f v p 0 * ∏ u ∈ T, f u p 0 =
          f v p t * (∏ u ∈ T, f u p t - ∏ u ∈ T, f u p 0) + (f v p t - f v p 0) * ∏ u ∈ T, f u p 0 := by
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have hdT0 : 0 ≤ dT * |t| := by
        have := (norm_nonneg _).trans (hdT p t); exact this
      calc ‖f v p t‖ * ‖∏ u ∈ T, f u p t - ∏ u ∈ T, f u p 0‖ + ‖f v p t - f v p 0‖ * ‖∏ u ∈ T, f u p 0‖
          ≤ max bv 0 * (dT * |t|) + dv * |t| * bT :=
            add_le_add (mul_le_mul ((hbv p t).trans (le_max_left _ _)) (hdT p t) (norm_nonneg _)
              (le_max_right _ _)) (mul_le_mul (hdv p t) (hbT p 0) (norm_nonneg _)
              ((norm_nonneg _).trans (hdv p t)))
        _ = (max bv 0 * dT + dv * bT) * |t| := by ring

end ProdBounds

section Curves

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

local notation "cN" => AutomorphicForm.HeckeEigensystem.cNorm

noncomputable def qv (v : HeightOneSpectrum (𝓞 K)) : ℕ := Ideal.absNorm v.asIdeal

theorem one_lt_qv (v : HeightOneSpectrum (𝓞 K)) : 1 < qv v := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  unfold qv; omega

theorem cN_eq (v : HeightOneSpectrum (𝓞 K)) : cN v = ((qv v : ℕ) : ℂ) := rfl

theorem cN_ne_zero' (v : HeightOneSpectrum (𝓞 K)) : cN v ≠ 0 :=
  AutomorphicForm.HeckeEigensystem.cNorm_ne_zero v

theorem norm_cN_cpow (v : HeightOneSpectrum (𝓞 K)) (z : ℂ) : ‖cN v ^ z‖ = (qv v : ℝ) ^ z.re := by
  rw [cN_eq]; exact Complex.norm_natCast_cpow_of_pos (by have := one_lt_qv v; omega) z

theorem norm_cN_cpow_of_re (v : HeightOneSpectrum (𝓞 K)) {z : ℂ} (hz : z.re = 0) : ‖cN v ^ z‖ = 1 := by
  rw [norm_cN_cpow, hz, Real.rpow_zero]

theorem norm_cN_cpow_half_le (v : HeightOneSpectrum (𝓞 K)) : ‖cN v ^ ((1 / 2 : ℝ) : ℂ)‖ ≤ (qv v : ℝ) := by
  rw [norm_cN_cpow, Complex.ofReal_re]
  have h1 : (1 : ℝ) ≤ qv v := by exact_mod_cast (one_lt_qv v).le
  calc (qv v : ℝ) ^ (1 / 2 : ℝ) ≤ (qv v : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = qv v := Real.rpow_one _

theorem log_qv_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < Real.log (qv v) :=
  Real.log_pos (by exact_mod_cast one_lt_qv v)

theorem cN_cpow_mul_I (v : HeightOneSpectrum (𝓞 K)) (t : ℝ) :
    cN v ^ ((t : ℂ) * I) = cexp (I * ((t * Real.log (qv v) : ℝ) : ℂ)) := by
  rw [cN_eq, Complex.cpow_def_of_ne_zero (by exact_mod_cast (show qv v ≠ 0 by
    have := one_lt_qv v; omega)), ← Complex.natCast_log]
  push_cast; ring_nf

theorem cN_cpow_neg_mul_I (v : HeightOneSpectrum (𝓞 K)) (t : ℝ) :
    cN v ^ (-((t : ℂ) * I)) = cexp (I * (((-t) * Real.log (qv v) : ℝ) : ℂ)) := by
  rw [show -((t : ℂ) * I) = (((-t : ℝ)) : ℂ) * I by push_cast; ring, cN_cpow_mul_I]

theorem norm_cN_cpow_mul_I_sub_one_le (v : HeightOneSpectrum (𝓞 K)) (t : ℝ) :
    ‖cN v ^ ((t : ℂ) * I) - 1‖ ≤ Real.log (qv v) * |t| := by
  rw [cN_cpow_mul_I]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (log_qv_pos v), mul_comm]

theorem norm_cN_cpow_neg_mul_I_sub_one_le (v : HeightOneSpectrum (𝓞 K)) (t : ℝ) :
    ‖cN v ^ (-((t : ℂ) * I)) - 1‖ ≤ Real.log (qv v) * |t| := by
  rw [cN_cpow_neg_mul_I]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (log_qv_pos v), mul_comm]

theorem countable_exp_levelset {lam : ℝ} (hlam : lam ≠ 0) (z₀ : ℂ) :
    Set.Countable {t : ℝ | cexp (I * ((t * lam : ℝ) : ℂ)) = z₀} := by
  by_cases hex : ∃ t₂ : ℝ, cexp (I * ((t₂ * lam : ℝ) : ℂ)) = z₀
  · obtain ⟨t₂, ht₂⟩ := hex
    refine (Set.countable_range fun n : ℤ => t₂ + n * (2 * π / lam)).mono fun t ht => ?_
    simp only [Set.mem_setOf_eq] at ht
    rw [← ht₂, Complex.exp_eq_exp_iff_exists_int] at ht
    obtain ⟨n, hn⟩ := ht
    have h' : ((t * lam : ℝ) : ℂ) = ((t₂ * lam + n * (2 * π) : ℝ) : ℂ) := by
      apply mul_left_cancel₀ I_ne_zero
      rw [hn]; push_cast; ring
    have h'' := Complex.ofReal_injective h'
    refine ⟨n, ?_⟩
    field_simp
    linarith
  · have : {t : ℝ | cexp (I * ((t * lam : ℝ) : ℂ)) = z₀} = ∅ :=
      Set.eq_empty_of_forall_notMem fun t ht => hex ⟨t, ht⟩
    rw [this]; exact Set.countable_empty

theorem countable_levelset (v : HeightOneSpectrum (𝓞 K)) (A B w : ℂ) (hB : B ≠ 0) :
    Set.Countable {t : ℝ | A * cN v ^ (-((t : ℂ) * I)) + B * cN v ^ ((t : ℂ) * I) = w} := by
  set lq : ℝ := Real.log (qv v) with hlq
  have hlq0 : lq ≠ 0 := (log_qv_pos v).ne'

  have hz : ∀ t : ℝ, cN v ^ ((t : ℂ) * I) = cexp (I * ((t * lq : ℝ) : ℂ)) := fun t => cN_cpow_mul_I v t
  have hzi : ∀ t : ℝ, cN v ^ (-((t : ℂ) * I)) = (cexp (I * ((t * lq : ℝ) : ℂ)))⁻¹ := by
    intro t; rw [Complex.cpow_neg, hz]
  by_cases hex : ∃ t₁ : ℝ, A * cN v ^ (-((t₁ : ℂ) * I)) + B * cN v ^ ((t₁ : ℂ) * I) = w
  · obtain ⟨t₁, ht₁⟩ := hex
    set z₁ : ℂ := cexp (I * ((t₁ * lq : ℝ) : ℂ)) with hz₁
    set z₂ : ℂ := w / B - z₁ with hz₂
    have hquad : ∀ z : ℂ, z ≠ 0 → A * z⁻¹ + B * z = w → B * z ^ 2 - w * z + A = 0 := by
      intro z hz0 h
      have := congrArg (· * z) h
      simp only [add_mul, inv_mul_cancel_right₀ hz0] at this
      linear_combination this
    have e2 : B * z₁ ^ 2 - w * z₁ + A = 0 := by
      have h1 := ht₁
      rw [hzi, hz] at h1
      exact hquad z₁ (Complex.exp_ne_zero _) h1
    have key : ∀ t : ℝ, A * cN v ^ (-((t : ℂ) * I)) + B * cN v ^ ((t : ℂ) * I) = w →
        cexp (I * ((t * lq : ℝ) : ℂ)) = z₁ ∨ cexp (I * ((t * lq : ℝ) : ℂ)) = z₂ := by
      intro t ht
      rw [hz, hzi] at ht
      have e1 := hquad _ (Complex.exp_ne_zero _) ht
      set z := cexp (I * ((t * lq : ℝ) : ℂ))
      have hfac : (z - z₁) * (B * (z + z₁) - w) = 0 := by linear_combination e1 - e2
      rcases mul_eq_zero.mp hfac with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · right
        rw [hz₂, eq_sub_iff_add_eq, eq_div_iff hB]
        linear_combination h
    refine ((countable_exp_levelset hlq0 z₁).union (countable_exp_levelset hlq0 z₂)).mono ?_
    intro t ht
    exact key t ht
  · have : {t : ℝ | A * cN v ^ (-((t : ℂ) * I)) + B * cN v ^ ((t : ℂ) * I) = w} = ∅ :=
      Set.eq_empty_of_forall_notMem fun t ht => hex ⟨t, ht⟩
    rw [this]; exact Set.countable_empty

noncomputable def coord1 (v : HeightOneSpectrum (𝓞 K)) (A B : ℂ) (t : ℝ) : ℂ :=
  cN v ^ ((1 / 2 : ℝ) : ℂ) * (A * cN v ^ (-((t : ℂ) * I)) + B * cN v ^ ((t : ℂ) * I))

theorem continuous_coord1 (v : HeightOneSpectrum (𝓞 K)) (A B : ℂ) : Continuous (coord1 v A B) := by
  unfold coord1
  have h1 : Continuous fun t : ℝ => cN v ^ ((t : ℂ) * I) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (cN_ne_zero' v))
  have h2 : Continuous fun t : ℝ => cN v ^ (-((t : ℂ) * I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (cN_ne_zero' v))
  exact continuous_const.mul ((continuous_const.mul h2).add (continuous_const.mul h1))

theorem volume_coord1_fibre (v : HeightOneSpectrum (𝓞 K)) (A B : ℂ) (hB : B ≠ 0) (w : ℂ) :
    volume {t : ℝ | coord1 v A B t = w} = 0 := by
  have hc : cN v ^ ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [← norm_pos_iff, norm_cN_cpow]
    exact Real.rpow_pos_of_pos (by have := one_lt_qv v; positivity) _
  have hset : {t : ℝ | coord1 v A B t = w} =
      {t : ℝ | A * cN v ^ (-((t : ℂ) * I)) + B * cN v ^ ((t : ℂ) * I) = w / cN v ^ ((1 / 2 : ℝ) : ℂ)} := by
    ext t
    simp only [Set.mem_setOf_eq, coord1]
    rw [eq_div_iff hc, mul_comm]
  rw [hset]
  exact (countable_levelset v A B _ hB).measure_zero volume

noncomputable def fac (v : HeightOneSpectrum (𝓞 K)) (k j : ℕ) (A B : ℂ) (t : ℝ) : ℂ :=
  coord1 v A B t ^ k * ((cN v)⁻¹ * (cN v * A * B)) ^ j

theorem fac_bounds (v : HeightOneSpectrum (𝓞 K)) (k j : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    (∀ A B : ℂ, ‖A‖ ≤ M → ‖B‖ ≤ M → ∀ t,
      ‖fac v k j A B t‖ ≤ (2 * (qv v : ℝ) * M) ^ k * (M * M) ^ j) ∧
    (∀ A B : ℂ, ‖A‖ ≤ M → ‖B‖ ≤ M → ∀ t,
      ‖fac v k j A B t - fac v k j A B 0‖ ≤
        (k * (2 * (qv v : ℝ) * M) ^ k * (2 * (qv v : ℝ) * M * Real.log (qv v)) * (M * M) ^ j) * |t|) := by
  have hq1 : (1 : ℝ) ≤ qv v := by exact_mod_cast (one_lt_qv v).le
  have hM0 : 0 ≤ M := by linarith
  have hAB : ∀ A B : ℂ, ‖A‖ ≤ M → ‖B‖ ≤ M → ‖(cN v)⁻¹ * (cN v * A * B)‖ ≤ M * M := by
    intro A B hA hB
    rw [show (cN v)⁻¹ * (cN v * A * B) = A * B by field_simp [cN_ne_zero' v], norm_mul]
    exact mul_le_mul hA hB (norm_nonneg _) hM0
  have hc1 : ∀ A B : ℂ, ‖A‖ ≤ M → ‖B‖ ≤ M → ∀ t, ‖coord1 v A B t‖ ≤ 2 * (qv v : ℝ) * M := by
    intro A B hA hB t
    unfold coord1
    rw [norm_mul]
    calc ‖cN v ^ ((1 / 2 : ℝ) : ℂ)‖ * ‖A * cN v ^ (-((t : ℂ) * I)) + B * cN v ^ ((t : ℂ) * I)‖
        ≤ (qv v : ℝ) * (M + M) := by
          refine mul_le_mul (norm_cN_cpow_half_le v) ((norm_add_le _ _).trans ?_) (norm_nonneg _)
            (by positivity)
          rw [norm_mul, norm_mul, norm_cN_cpow_of_re v (by simp), norm_cN_cpow_of_re v (by simp),
            mul_one, mul_one]
          exact add_le_add hA hB
      _ = 2 * (qv v : ℝ) * M := by ring
  have hMx : 1 ≤ 2 * (qv v : ℝ) * M := by nlinarith
  refine ⟨fun A B hA hB t => ?_, fun A B hA hB t => ?_⟩
  · unfold fac
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hc1 A B hA hB t) k)
      (pow_le_pow_left₀ (norm_nonneg _) (hAB A B hA hB) j) (by positivity) (by positivity)
  · unfold fac
    rw [← sub_mul, norm_mul, norm_pow]
    have hdiff : ‖coord1 v A B t - coord1 v A B 0‖ ≤ 2 * (qv v : ℝ) * M * Real.log (qv v) * |t| := by
      unfold coord1
      rw [← mul_sub, norm_mul]
      have h0 : A * cN v ^ (-((t : ℂ) * I)) + B * cN v ^ ((t : ℂ) * I) -
          (A * cN v ^ (-(((0 : ℝ) : ℂ) * I)) + B * cN v ^ (((0 : ℝ) : ℂ) * I)) =
          A * (cN v ^ (-((t : ℂ) * I)) - 1) + B * (cN v ^ ((t : ℂ) * I) - 1) := by
        simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero]; ring
      rw [h0]
      calc ‖cN v ^ ((1 / 2 : ℝ) : ℂ)‖ * ‖A * (cN v ^ (-((t : ℂ) * I)) - 1) + B * (cN v ^ ((t : ℂ) * I) - 1)‖
          ≤ (qv v : ℝ) * (M * (Real.log (qv v) * |t|) + M * (Real.log (qv v) * |t|)) := by
            refine mul_le_mul (norm_cN_cpow_half_le v) ((norm_add_le _ _).trans ?_) (norm_nonneg _)
              (by positivity)
            rw [norm_mul, norm_mul]
            exact add_le_add (mul_le_mul hA (norm_cN_cpow_neg_mul_I_sub_one_le v t) (norm_nonneg _) hM0)
              (mul_le_mul hB (norm_cN_cpow_mul_I_sub_one_le v t) (norm_nonneg _) hM0)
        _ = 2 * (qv v : ℝ) * M * Real.log (qv v) * |t| := by ring
    calc ‖coord1 v A B t ^ k - coord1 v A B 0 ^ k‖ * ‖(cN v)⁻¹ * (cN v * A * B)‖ ^ j
        ≤ (k * (2 * (qv v : ℝ) * M) ^ k * (2 * (qv v : ℝ) * M * Real.log (qv v) * |t|)) * (M * M) ^ j := by
          refine mul_le_mul ((norm_pow_sub_pow_le _ _ hMx (hc1 A B hA hB t) (hc1 A B hA hB 0) k).trans
            ?_) (pow_le_pow_left₀ (norm_nonneg _) (hAB A B hA hB) j) (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = _ := by ring

end Curves

end R4PackV5

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option linter.unusedVariables false in
open R4PackV5 Filter Topology Complex in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (X : Set (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (hXc : IsCompact X) (hX0 : X.Nonempty)
    (ιE : Type) [Countable ιE] (nE : ιE → ℕ)
    (A B : ιE → HeightOneSpectrum (𝓞 K) → ℂ) (hA : ∀ e v, A e v ≠ 0) (hB : ∀ e v, B e v ≠ 0)
    (M₀ : HeightOneSpectrum (𝓞 K) → ℝ) (hAM : ∀ e v, ‖A e v‖ ≤ M₀ v) (hBM : ∀ e v, ‖B e v‖ ≤ M₀ v)
    (τ : ιE → ℝ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ))
    (hτ : ∀ (e : ιE) (t : ℝ) (v : HeightOneSpectrum (𝓞 K)), v ∉ SK →
      τ e t v = ((AutomorphicForm.HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
          (A e v * (AutomorphicForm.HeckeEigensystem.cNorm v) ^ (-((t : ℂ) * Complex.I)) + B e v * (AutomorphicForm.HeckeEigensystem.cNorm v) ^ ((t : ℂ) * Complex.I)),
        (AutomorphicForm.HeckeEigensystem.cNorm v) * A e v * B e v))
    (hτS : ∀ (e : ιE) (t : ℝ) (v : HeightOneSpectrum (𝓞 K)), v ∈ SK → τ e t v = 0)
    (hτX : ∀ e t, τ e t ∈ X)
    (κ c : ℂ)
    (P Q U V a : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ)
    (hPc : ∀ e i j t, P e i j t = P e i j 0)
    (hQc : ∀ e i j, Continuous (Q e i j)) (hUc : ∀ e i j, Continuous (U e i j)) (hVc : ∀ e i j, Continuous (V e i j))
    (hac : ∀ e i j, Continuous (a e i j)) (hai : ∀ e i j, Integrable (a e i j))
    (haQ : ∀ e i j, Integrable (fun t => a e i j t * Q e i j t))
    (haU : ∀ e i j, Integrable (fun t => a e i j t * U e i j t))
    (haV : ∀ e i j, Integrable (fun t => a e i j t * V e i j t))
    (hUV0 : ∀ e i j, U e i j 0 = V e i j 0)
    (L : ιE → ℝ) (hL : Summable L)
    (hL1 : ∀ e, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
        ∫ t : ℝ, (‖a e i j t‖ * (1 + ‖P e i j t‖) + ‖a e i j t * Q e i j t‖ +
          ‖a e i j t * U e i j t‖ + ‖a e i j t * V e i j t‖) ≤ L e)
    (hL0 : ∀ e, ∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j 0‖ * (‖U e i j 0‖ + ‖V e i j 0‖) ≤ L e)
    (hLip : ∀ (e : ιE) (t : ℝ), |t| ≤ 1 →
        (∑ i : Fin (nE e), ∑ j : Fin (nE e),
          ‖a e i j t * (U e i j t + V e i j t) - a e i j 0 * (U e i j 0 + V e i j 0)‖) ≤ L e * |t| ∧
        (∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j t * (U e i j t - V e i j t)‖) ≤ L e * |t|) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 → ∃ e : ιE, 0 < nE e ∧ tabs n = τ e 0) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
      ∃ s : C(X, ℂ) →L[ℂ] ℂ,
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ),
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).1 ^ ks v *
            ((AutomorphicForm.HeckeEigensystem.cNorm v)⁻¹ *
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).2) ^ js v) →
      ∀ (I : ℝ → ℂ) (R₀ : ℝ),
        (∀ R : ℝ, R₀ ≤ R →
          I R = κ * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
            (g ⟨τ e t, hτX e t⟩ * a e i j t) *
              (c * ( P e i j t * (2 * (R : ℂ))
                    - Q e i j t
                    + U e i j t * Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
                    - V e i j t * Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ)) ))) →
        Filter.Tendsto (fun R : ℝ => I R - (R : ℂ) * s g) Filter.atTop
          (nhds ((∑' n, cs n * g ⟨tabs n, htabs n⟩) + Λ g)) := by
  classical
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hXc
  obtain ⟨x₀, hx₀⟩ := hX0
  have hLnn : ∀ e, 0 ≤ L e := fun e => Le_nonneg (hL0 e)

  have hτcont : ∀ e, Continuous (τ e) := by
    intro e
    refine continuous_pi fun v => ?_
    by_cases hv : v ∈ SK
    · have h : (fun t => τ e t v) = fun _ => 0 := funext fun t => hτS e t v hv
      rw [h]; exact continuous_const
    · have h : (fun t => τ e t v) = fun t =>
          (coord1 v (A e v) (B e v) t, AutomorphicForm.HeckeEigensystem.cNorm v * A e v * B e v) :=
        funext fun t => hτ e t v hv
      rw [h]
      exact (continuous_coord1 v _ _).prodMk continuous_const
  have hcurve : ∀ e, Continuous fun t => (⟨τ e t, hτX e t⟩ : X) := fun e =>
    (hτcont e).subtype_mk _

  set m : ιE → ℂ := fun e => κ * c * (π / 2) * Gp (U e) (V e) (a e) 0 with hm
  have hmb : ∀ e, ‖m e‖ ≤ ‖κ * c * (π / 2)‖ * L e := fun e => by
    rw [hm]; dsimp only; rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_Gp_zero_le (hL0 e)) (norm_nonneg _)
  have hms : Summable fun e => ‖m e‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmb (hL.mul_left _)
  obtain ⟨tabs, cs, hcs, hat, hsumcs⟩ :=
    exists_enum (⟨x₀, hx₀⟩ : X) (fun e => (⟨τ e 0, hτX e 0⟩ : X)) m hms
  refine ⟨fun n => (tabs n : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), fun n => (tabs n).2, cs, hcs, ?_, ?_⟩
  · intro n hn
    obtain ⟨e, hce, hte⟩ := hat n hn
    refine ⟨e, Nat.pos_of_ne_zero fun h0 => hn ?_, by dsimp only; rw [hte]⟩
    rw [hce, hm]
    dsimp only
    have hG : Gp (U e) (V e) (a e) 0 = 0 := by
      unfold Gp
      have : IsEmpty (Fin (nE e)) := by rw [h0]; infer_instance
      simp
    rw [hG, mul_zero]
  intro T hTS hT2
  have hT0 : T.Nonempty := Finset.card_pos.mp (by omega)
  have hTv : ∀ v ∈ T, v ∉ SK := fun v hv hvS => Finset.disjoint_left.mp hTS hv hvS

  have hqi : ∀ e, Integrable fun t => -(κ * c) * qS (Q e) (a e) t := fun e =>
    (integrable_qS (haQ e)).const_mul _
  have hqL : ∀ e, ∫ t, ‖-(κ * c) * qS (Q e) (a e) t‖ ≤ ‖κ * c‖ * L e := fun e => by
    have h : (fun t => ‖-(κ * c) * qS (Q e) (a e) t‖) = fun t => ‖κ * c‖ * ‖qS (Q e) (a e) t‖ := by
      funext t; rw [norm_mul, norm_neg]
    rw [h, integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_norm_qS_le (hPc e) (hai e) (haQ e) (haU e) (haV e) (hL1 e)) (norm_nonneg _)
  obtain ⟨Λ, hΛ⟩ := exists_clm (X := X) (fun e t => (⟨τ e t, hτX e t⟩ : X)) hcurve
    (fun e t => -(κ * c) * qS (Q e) (a e) t) hqi (fun e => ‖κ * c‖ * L e) (hL.mul_left _) hqL
  refine ⟨Λ, fun τ₀ ε hε => ?_, ?_⟩
  · refine small_on_cylinders τ hτX T hT0 (fun e v _ => (continuous_apply v).comp (hτcont e))
      (fun e v hv w => ?_) _ hqi _ (hL.mul_left _) hqL Λ hΛ τ₀ ε hε
    refine measure_mono_null (fun t (ht : τ e t v = w) => ?_)
      (volume_coord1_fibre v (A e v) (B e v) (hB e v) w.1)
    show coord1 v (A e v) (B e v) t = w.1
    rw [← ht, hτ e t v (hTv v hv)]
    rfl

  have hpi : ∀ e, Integrable fun t => 2 * κ * c * pS (P e) (a e) t := fun e =>
    (integrable_pS (hPc e) (hai e)).const_mul _
  have hpL : ∀ e, ∫ t, ‖2 * κ * c * pS (P e) (a e) t‖ ≤ ‖2 * κ * c‖ * L e := fun e => by
    have h : (fun t => ‖2 * κ * c * pS (P e) (a e) t‖) = fun t => ‖2 * κ * c‖ * ‖pS (P e) (a e) t‖ := by
      funext t; rw [norm_mul]
    rw [h, integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_norm_pS_le (hPc e) (hai e) (haQ e) (haU e) (haV e) (hL1 e)) (norm_nonneg _)
  obtain ⟨s, hs⟩ := exists_clm (X := X) (fun e t => (⟨τ e t, hτX e t⟩ : X)) hcurve
    (fun e t => 2 * κ * c * pS (P e) (a e) t) hpi (fun e => ‖2 * κ * c‖ * L e) (hL.mul_left _) hpL
  refine ⟨s, ?_⟩
  intro ks js g hg I R₀ hI

  set γ : ιE → ℝ → ℂ := fun e t => g ⟨τ e t, hτX e t⟩ with hγdef
  have hγc : ∀ e, Continuous (γ e) := fun e => g.continuous.comp (hcurve e)
  have hγB : ∀ e t, ‖γ e t‖ ≤ ‖g‖ := fun e t => g.norm_coe_le_norm _
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, ∀ e t, ‖γ e t - γ e 0‖ ≤ Cm * |t| := by
    set M : ℝ := max 1 (T.sup' hT0 M₀) with hM
    have hM1 : 1 ≤ M := le_max_left _ _
    have hMv : ∀ v ∈ T, M₀ v ≤ M := fun v hv => (Finset.le_sup' M₀ hv).trans (le_max_right _ _)
    have hfac : ∀ e t, γ e t = ∏ v ∈ T, fac v (ks v) (js v) (A e v) (B e v) t := by
      intro e t
      rw [hγdef]; dsimp only; rw [hg]
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [show ((⟨τ e t, hτX e t⟩ : X) : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v = τ e t v from rfl,
        hτ e t v (hTv v hv)]
      rfl
    obtain ⟨-, d, hd⟩ := prod_bounds T (fun v (e : ιE) t => fac v (ks v) (js v) (A e v) (B e v) t)
      (fun v hv => ⟨_, fun e t => (fac_bounds v (ks v) (js v) hM1).1 (A e v) (B e v)
        ((hAM e v).trans (hMv v hv)) ((hBM e v).trans (hMv v hv)) t⟩)
      (fun v hv => ⟨_, fun e t => (fac_bounds v (ks v) (js v) hM1).2 (A e v) (B e v)
        ((hAM e v).trans (hMv v hv)) ((hBM e v).trans (hMv v hv)) t⟩)
    exact ⟨d, fun e t => by rw [hfac e t, hfac e 0]; exact hd e t⟩

  have hJ : ∀ (e : ιE) (R : ℝ), (∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
      (g ⟨τ e t, hτX e t⟩ * a e i j t) *
        (c * ( P e i j t * (2 * (R : ℂ))
              - Q e i j t
              + U e i j t * Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
              - V e i j t * Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ)) ))) =
      c * (2 * (R : ℂ)) * (∫ t, γ e t * pS (P e) (a e) t) + c * rest (Q e) (U e) (V e) (a e) (γ e) R :=
    fun e R => integral_pair_eq (hPc e) (hUc e) (hVc e) (hac e) (hai e) (haQ e) (haU e) (haV e) (hL1 e)
      (hL0 e) (hLip e) (hγc e) (hγB e) (hCm e) c R
  have hbd : ∀ (e : ιE) (R : ℝ), ‖Dfac R‖ ≤ 3 →
      ‖rest (Q e) (U e) (V e) (a e) (γ e) R‖ ≤ (12 * ‖g‖ + Cm) * L e :=
    fun e R hR => norm_rest_le (hPc e) (hUc e) (hVc e) (hac e) (hai e) (haQ e) (haU e) (haV e) (hL1 e)
      (hL0 e) (hLip e) (hγc e) (hγB e) (hCm e) hR
  have hlim : ∀ e : ιE, Tendsto (rest (Q e) (U e) (V e) (a e) (γ e)) atTop
      (𝓝 (-(∫ t, γ e t * qS (Q e) (a e) t) + γ e 0 * Gp (U e) (V e) (a e) 0 * (π / 2))) :=
    fun e => tendsto_rest (hPc e) (hUc e) (hVc e) (hac e) (hai e) (haQ e) (haU e) (haV e) (hL1 e)
      (hL0 e) (hLip e) (hγc e) (hγB e) (hCm e)

  set Y : ℝ → ιE → ℂ := fun R e => κ * (c * rest (Q e) (U e) (V e) (a e) (γ e) R) with hY
  set Ylim : ιE → ℂ := fun e =>
    κ * (c * (-(∫ t, γ e t * qS (Q e) (a e) t) + γ e 0 * Gp (U e) (V e) (a e) 0 * (π / 2))) with hYlim
  have hYb : ∀ R, ‖Dfac R‖ ≤ 3 → ∀ e, ‖Y R e‖ ≤ ‖κ‖ * ‖c‖ * ((12 * ‖g‖ + Cm) * L e) := by
    intro R hR e
    rw [hY]; dsimp only
    rw [norm_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbd e R hR) (norm_nonneg _))
      (norm_nonneg _)
  have hTann : Tendsto (fun R => ∑' e, Y R e) atTop (𝓝 (∑' e, Ylim e)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun e => ‖κ‖ * ‖c‖ * ((12 * ‖g‖ + Cm) * L e))
      (((hL.mul_left (12 * ‖g‖ + Cm)).mul_left (‖κ‖ * ‖c‖)))
      (fun e => ((hlim e).const_mul c).const_mul κ) ?_
    filter_upwards [eventually_norm_Dfac_le] with R hR using hYb R hR

  have hev : ∀ᶠ R in atTop, (∑' e, Y R e) = I R - (R : ℂ) * s g := by
    filter_upwards [eventually_ge_atTop R₀, eventually_norm_Dfac_le] with R hR hD
    rw [hI R hR, hs g]
    set Xf : ιE → ℂ := fun e => κ * (c * (2 * (R : ℂ)) * ∫ t, γ e t * pS (P e) (a e) t) with hXf
    have h1 : κ * (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
        (g ⟨τ e t, hτX e t⟩ * a e i j t) *
          (c * ( P e i j t * (2 * (R : ℂ))
                - Q e i j t
                + U e i j t * Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
                - V e i j t * Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ)) ))) =
        ∑' e, (Xf e + Y R e) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun e => ?_
      rw [hJ e R, hXf, hY]
      ring
    have h2 : (R : ℂ) * ∑' e, ∫ t, g ⟨τ e t, hτX e t⟩ * (2 * κ * c * pS (P e) (a e) t) = ∑' e, Xf e := by
      rw [← tsum_mul_left]
      refine tsum_congr fun e => ?_
      rw [hXf]; dsimp only
      rw [show (∫ t, g ⟨τ e t, hτX e t⟩ * (2 * κ * c * pS (P e) (a e) t)) =
        2 * κ * c * ∫ t, γ e t * pS (P e) (a e) t by
          rw [← integral_const_mul]; exact integral_congr_ae (ae_of_all _ fun t => by ring)]
      ring
    have hXs : Summable Xf := by
      refine Summable.of_norm_bounded (hL.mul_left (‖κ‖ * (‖c * (2 * (R : ℂ))‖ * ‖g‖))) fun e => ?_
      rw [hXf]; dsimp only
      rw [norm_mul, norm_mul, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (norm_nonneg _)
      exact norm_integral_comp_mul_le g _ (integrable_pS (hPc e) (hai e)) (norm_nonneg g)
        (fun x => g.norm_coe_le_norm x) (integral_norm_pS_le (hPc e) (hai e) (haQ e) (haU e) (haV e) (hL1 e))
    have hYs : Summable (Y R) :=
      Summable.of_norm_bounded (((hL.mul_left (12 * ‖g‖ + Cm)).mul_left (‖κ‖ * ‖c‖))) (hYb R hD)
    rw [h1, h2, hXs.tsum_add hYs]
    ring

  have hA1 : Summable fun e => m e * g ⟨τ e 0, hτX e 0⟩ := by
    refine Summable.of_norm_bounded (hms.mul_right ‖g‖) fun e => ?_
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _)
  have hA2 : Summable fun e => ∫ t, g ⟨τ e t, hτX e t⟩ * (-(κ * c) * qS (Q e) (a e) t) := by
    refine Summable.of_norm_bounded (hL.mul_left (‖g‖ * ‖κ * c‖)) fun e => ?_
    rw [mul_assoc]
    exact norm_integral_comp_mul_le g _ (hqi e) (norm_nonneg g) (fun x => g.norm_coe_le_norm x) (hqL e)
  have hlimval : (∑' n, cs n * g ⟨(tabs n : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), (tabs n).2⟩) + Λ g =
      ∑' e, Ylim e := by
    have hG : (∑' n, cs n * g ⟨(tabs n : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), (tabs n).2⟩) =
        ∑' e, m e * g ⟨τ e 0, hτX e 0⟩ := hsumcs g
    rw [hG, hΛ g, ← hA1.tsum_add hA2]
    refine tsum_congr fun e => ?_
    rw [show (∫ t, g ⟨τ e t, hτX e t⟩ * (-(κ * c) * qS (Q e) (a e) t)) =
      -(κ * c) * ∫ t, γ e t * qS (Q e) (a e) t by
        rw [← integral_const_mul]; exact integral_congr_ae (ae_of_all _ fun t => by ring)]
    rw [hYlim, hm]
    dsimp only
    ring
  rw [hlimval]
  exact hTann.congr' hev

end S_AutomorphicForm_exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz
end P2MW
export P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz (solution)
