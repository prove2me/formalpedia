-- Prove2me | solution 1 for Arxiv2205_09234.fourier_metric_derivative_order
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:14:55.06207+00:00
-- url     : https://prove2.me/submissions/680aaaf5-38bd-4420-b03b-3d9ba10d7d6b

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology SchwartzMap
open scoped FourierTransform ContDiff

namespace S77FM
open Arxiv2205_09234

noncomputable def cpx (g : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℂ) where
  toFun := fun t => (g t : ℂ)
  smooth' := Complex.ofRealCLM.contDiff.comp (g.smooth ⊤)
  decay' := fun k n => by
    obtain ⟨C, hC⟩ := g.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun t => (g t : ℂ)) = Complex.ofRealLI ∘ g := rfl
    rw [e, LinearIsometry.norm_iteratedFDeriv_comp_left _ ((g.smooth ⊤).contDiffAt)
      (by exact_mod_cast le_top)]
    exact hC x

@[simp] lemma cpx_apply (g : 𝓢(ℝ, ℝ)) (t : ℝ) : cpx g t = (g t : ℂ) := rfl

lemma iter_ofReal (n : ℕ) : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g →
    iteratedDeriv n (fun t => (g t : ℂ)) = fun t => ((iteratedDeriv n g t : ℝ) : ℂ) := by
  induction n with
  | zero => intro g _; simp
  | succ k ih =>
    intro g hg
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hd : deriv (fun t => (g t : ℂ)) = fun t => ((deriv g t : ℝ) : ℂ) := by
      funext t
      exact ((hg.differentiable (by simp)).differentiableAt.hasDerivAt.ofReal_comp).deriv
    rw [hd]
    exact ih (deriv g) (contDiff_infty_iff_deriv.1 hg).2

lemma iterD (k : ℕ) : ∀ F : 𝓢(ℝ, ℂ), ⇑((derivCLM ℝ ℂ)^[k] F) = iteratedDeriv k F := by
  induction k with
  | zero => intro F; simp
  | succ k ih =>
    intro F
    rw [Function.iterate_succ_apply, ih, iteratedDeriv_succ']
    congr 1

lemma angF_eq (d : 𝓢(ℝ, ℝ)) (w : ℝ) :
    angFourier d w = 𝓕 (⇑(cpx d)) (w / (2 * Real.pi)) := by
  rw [angFourier, Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext t
  rw [smul_eq_mul, cpx_apply, mul_comm]
  congr 2
  push_cast
  field_simp

end S77FM

open Arxiv2205_09234 S77FM in
theorem solution (dm dobs : SchwartzMap ℝ ℝ) (n : ℕ) :
    fourierMetric 2 (2 * (n : ℝ)) dm dobs ^ 2 =
      2 * Real.pi * ∫ t : ℝ, (iteratedDeriv n (fun s => dm s - dobs s) t) ^ 2 := by
  set F : 𝓢(ℝ, ℂ) := cpx dm - cpx dobs with hF
  have hFc : (⇑F) = fun t => (((fun s => dm s - dobs s) t : ℝ) : ℂ) := by
    funext t; simp [hF]
  have hg : ContDiff ℝ ∞ (fun s => dm s - dobs s) := (dm.smooth ⊤).sub (dobs.smooth ⊤)
  have hiter : iteratedDeriv n ⇑F = fun t => ((iteratedDeriv n (fun s => dm s - dobs s) t : ℝ) : ℂ) := by
    rw [hFc]; exact iter_ofReal n _ hg
  set D := (derivCLM ℝ ℂ)^[n] F with hD
  have hDc : ⇑D = iteratedDeriv n ⇑F := iterD n F
  -- Fourier of derivative
  have hFD : ∀ ξ, 𝓕 (⇑D) ξ = (2 * Real.pi * Complex.I * ξ) ^ n • 𝓕 (⇑F) ξ := by
    intro ξ
    rw [hDc]
    have := Real.fourier_iteratedDeriv (f := ⇑F) (N := ⊤) (n := n) (F.smooth ⊤)
      (fun k _ => by rw [← iterD k F]; exact ((derivCLM ℝ ℂ)^[k] F).integrable) le_top
    rw [this]
  have hdiff : ∀ w, angFourier dm w - angFourier dobs w = 𝓕 (⇑F) (w / (2 * Real.pi)) := by
    intro w
    rw [angF_eq, angF_eq, hF, ← fourier_coe, ← fourier_coe, ← fourier_coe]
    simp only [← fourierTransformCLM_apply ℂ, map_sub, SchwartzMap.sub_apply]
  have hint : ∀ w : ℝ, |w| ^ (2 * (n : ℝ)) * ‖angFourier dm w - angFourier dobs w‖ ^ (2:ℝ)
      = ‖𝓕 (⇑D) (w / (2 * Real.pi))‖ ^ 2 := by
    intro w
    rw [hdiff, hFD, norm_smul, mul_pow, norm_pow]
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have : ‖(2 * Real.pi * Complex.I * ((w / (2 * Real.pi) : ℝ) : ℂ))‖ = |w| := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, norm_mul]
      simp [abs_div, abs_of_pos hpi]
      field_simp
    rw [this, show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      Real.rpow_two, ← pow_mul, mul_comm n 2]
  have hmain : ∫ w : ℝ, |w| ^ (2 * (n : ℝ)) * ‖angFourier dm w - angFourier dobs w‖ ^ (2:ℝ)
      = 2 * Real.pi * ∫ t : ℝ, (iteratedDeriv n (fun s => dm s - dobs s) t) ^ 2 := by
    simp_rw [hint]
    rw [Measure.integral_comp_div (fun ξ => ‖𝓕 (⇑D) ξ‖ ^ 2) (2 * Real.pi), ← fourier_coe,
      integral_norm_sq_fourier, hDc, hiter]
    simp [abs_of_pos Real.pi_pos]
  have hnn : 0 ≤ ∫ w : ℝ, |w| ^ (2 * (n : ℝ)) * ‖angFourier dm w - angFourier dobs w‖ ^ (2:ℝ) := by
    rw [hmain]; positivity
  unfold fourierMetric
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num
  simp_rw [Real.rpow_two] at hmain
  exact hmain
