-- Prove2me | solution 1 for AutomorphicForm.LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/afe2e3a4-9749-547b-9e42-3abb6d4d864d

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg

set_option autoImplicit false

noncomputable section

namespace M4aP2DGK
namespace ArchComplexMoments

open MeasureTheory Set Complex Filter
open scoped ComplexConjugate

private def W (t : ℂ) (z : ℂ) : ℂ := ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-t)

private def M (a : ℕ) (t : ℂ) : ℂ := ∫ z : ℂ, z ^ a * conj z ^ a * W t z

private theorem one_add_norm_sq_pos (z : ℂ) : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity

private theorem baseC_ne_zero (z : ℂ) : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (one_add_norm_sq_pos z).ne'

private theorem continuous_W (t : ℂ) : Continuous (W t) := by
  unfold W
  refine Continuous.cpow (Complex.continuous_ofReal.comp (continuous_const.add (continuous_norm.pow 2)))
    continuous_const ?_
  intro z
  exact Complex.ofReal_mem_slitPlane.mpr (one_add_norm_sq_pos z)

private theorem norm_W (t : ℂ) (z : ℂ) : ‖W t z‖ = (1 + ‖z‖ ^ 2) ^ (-t.re) := by
  unfold W
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (one_add_norm_sq_pos z)]
  simp

private theorem conj_ofReal_mul_exp (r θ : ℝ) :
    conj ((r : ℂ) * cexp ((θ : ℂ) * I)) = (r : ℂ) * cexp (-((θ : ℂ) * I)) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    mul_neg]

private theorem angular_eq_zero {a b : ℕ} (hab : a ≠ b) :
    ∫ θ in Ioo (-Real.pi) Real.pi, cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b = 0 := by
  set c : ℂ := ((a : ℂ) - b) * I with hc_def
  have hc : c ≠ 0 := by
    refine mul_ne_zero (sub_ne_zero.mpr ?_) Complex.I_ne_zero
    exact_mod_cast hab
  have hpt : ∀ θ : ℝ, cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b = cexp (c * θ) := by
    intro θ
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [hc_def]
    ring
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  calc ∫ θ in Ioo (-Real.pi) Real.pi, cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b
      = ∫ θ in Ioo (-Real.pi) Real.pi, cexp (c * θ) :=
        setIntegral_congr_fun measurableSet_Ioo fun θ _ => hpt θ
    _ = ∫ θ in Ioc (-Real.pi) Real.pi, cexp (c * θ) := (integral_Ioc_eq_integral_Ioo).symm
    _ = ∫ θ in (-Real.pi)..Real.pi, cexp (c * θ) := (intervalIntegral.integral_of_le hle).symm
    _ = (cexp (c * Real.pi) - cexp (c * (-Real.pi : ℝ))) / c := integral_exp_mul_complex hc
    _ = 0 := by
        have hper : c * (Real.pi : ℂ) = c * ((-Real.pi : ℝ) : ℂ) + (((a : ℤ) - b : ℤ) : ℂ) * (2 * Real.pi * I) := by
          rw [hc_def]
          push_cast
          ring
        rw [hper, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, sub_self, zero_div]

private theorem integral_eq_zero_of_ne (a b : ℕ) (t : ℂ) (hab : a ≠ b) :
    ∫ z : ℂ, z ^ a * conj z ^ b * W t z = 0 := by
  have hEq : EqOn
      (fun p : ℝ × ℝ => p.1 • ((Complex.polarCoord.symm p) ^ a * conj (Complex.polarCoord.symm p) ^ b
        * W t (Complex.polarCoord.symm p)))
      (fun p : ℝ × ℝ => ((p.1 : ℂ) * (p.1 : ℂ) ^ (a + b) * ((1 + p.1 ^ 2 : ℝ) : ℂ) ^ (-t))
        * (cexp ((p.2 : ℂ) * I) ^ a * cexp (-((p.2 : ℂ) * I)) ^ b))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    intro p _
    simp only []
    unfold W
    rw [Complex.norm_polarCoord_symm, sq_abs, Complex.polarCoord_symm_apply, Complex.ofReal_cos,
      Complex.ofReal_sin, ← Complex.exp_mul_I, conj_ofReal_mul_exp, mul_pow, mul_pow, Complex.real_smul,
      pow_add]
    ring
  have hprod : (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ((p.1 : ℂ) * (p.1 : ℂ) ^ (a + b) * ((1 + p.1 ^ 2 : ℝ) : ℂ) ^ (-t))
          * (cexp ((p.2 : ℂ) * I) ^ a * cexp (-((p.2 : ℂ) * I)) ^ b) ∂((volume : Measure ℝ).prod volume))
      = (∫ r in Ioi (0 : ℝ), (r : ℂ) * (r : ℂ) ^ (a + b) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-t))
          * ∫ θ in Ioo (-Real.pi) Real.pi, cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b :=
    setIntegral_prod_mul (fun r : ℝ => (r : ℂ) * (r : ℂ) ^ (a + b) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-t))
      (fun θ : ℝ => cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b) (Ioi (0 : ℝ)) (Ioo (-Real.pi) Real.pi)
  calc ∫ z : ℂ, z ^ a * conj z ^ b * W t z
      = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • ((Complex.polarCoord.symm p) ^ a * conj (Complex.polarCoord.symm p) ^ b
            * W t (Complex.polarCoord.symm p)) :=
        (Complex.integral_comp_polarCoord_symm (fun z : ℂ => z ^ a * conj z ^ b * W t z)).symm
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ((p.1 : ℂ) * (p.1 : ℂ) ^ (a + b) * ((1 + p.1 ^ 2 : ℝ) : ℂ) ^ (-t))
            * (cexp ((p.2 : ℂ) * I) ^ a * cexp (-((p.2 : ℂ) * I)) ^ b)
            ∂((volume : Measure ℝ).prod volume) := by
        rw [Measure.volume_eq_prod]
        exact setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hEq
    _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * (r : ℂ) ^ (a + b) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-t))
          * ∫ θ in Ioo (-Real.pi) Real.pi, cexp ((θ : ℂ) * I) ^ a * cexp (-((θ : ℂ) * I)) ^ b := hprod
    _ = 0 := by rw [angular_eq_zero hab, mul_zero]

private theorem norm_moment (a : ℕ) (t : ℂ) (z : ℂ) :
    ‖z ^ a * conj z ^ a * W t z‖ = (‖z‖ ^ 2) ^ a * (1 + ‖z‖ ^ 2) ^ (-t.re) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_W, ← pow_mul, ← pow_add]
  congr 1
  ring

private theorem continuous_moment (a b : ℕ) (t : ℂ) : Continuous fun z : ℂ => z ^ a * conj z ^ b * W t z :=
  ((continuous_id.pow a).mul (Complex.continuous_conj.pow b)).mul (continuous_W t)

private theorem integrable_moment (a : ℕ) {t : ℂ} (ht : (a : ℝ) + 1 < t.re) :
    Integrable (fun z : ℂ => z ^ a * conj z ^ a * W t z) := by
  have hr : (Module.finrank ℝ ℂ : ℝ) < 2 * (t.re - a) := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hr).mono' (continuous_moment a a t).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [norm_moment]
  have hpos := one_add_norm_sq_pos z
  have h1 : (‖z‖ ^ 2) ^ a ≤ (1 + ‖z‖ ^ 2) ^ a :=
    pow_le_pow_left₀ (sq_nonneg _) (by linarith [sq_nonneg ‖z‖]) a
  have h2 : (0 : ℝ) ≤ (1 + ‖z‖ ^ 2) ^ (-t.re) := Real.rpow_nonneg hpos.le _
  calc (‖z‖ ^ 2) ^ a * (1 + ‖z‖ ^ 2) ^ (-t.re)
      ≤ (1 + ‖z‖ ^ 2) ^ a * (1 + ‖z‖ ^ 2) ^ (-t.re) := mul_le_mul_of_nonneg_right h1 h2
    _ = (1 + ‖z‖ ^ 2) ^ (-(2 * (t.re - a)) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
        congr 1
        ring

private theorem moment_succ_pointwise (a : ℕ) (t : ℂ) (z : ℂ) :
    z ^ (a + 1) * conj z ^ (a + 1) * W t z = z ^ a * conj z ^ a * W (t - 1) z - z ^ a * conj z ^ a * W t z := by
  have hW : W (t - 1) z = W t z * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
    unfold W
    rw [show (-(t - 1) : ℂ) = -t + 1 by ring, Complex.cpow_add _ _ (baseC_ne_zero z), Complex.cpow_one]
  have hzz : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hb : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) = 1 + ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, Complex.ofReal_one]
  rw [hW, hb, pow_succ, pow_succ]
  calc z ^ a * z * (conj z ^ a * conj z) * W t z
      = z ^ a * conj z ^ a * W t z * (z * conj z) := by ring
    _ = z ^ a * conj z ^ a * W t z * ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [hzz]
    _ = z ^ a * conj z ^ a * (W t z * (1 + ((‖z‖ ^ 2 : ℝ) : ℂ))) - z ^ a * conj z ^ a * W t z := by ring

private theorem moment_succ (a : ℕ) {t : ℂ} (ht : (a : ℝ) + 2 < t.re) : M (a + 1) t = M a (t - 1) - M a t := by
  have h1 : Integrable (fun z : ℂ => z ^ a * conj z ^ a * W (t - 1) z) := by
    refine integrable_moment a ?_
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have h2 : Integrable (fun z : ℂ => z ^ a * conj z ^ a * W t z) := integrable_moment a (by linarith)
  unfold M
  rw [← integral_sub h1 h2]
  exact integral_congr_ae (Eventually.of_forall fun z => moment_succ_pointwise a t z)

private theorem moment_zero {t : ℂ} (ht : 1 < t.re) : M 0 t = (Real.pi : ℂ) / (t - 1) := by
  have hs : 0 < ((t - 1) / 2).re := by
    have e : ((t - 1) / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) * (t - 1) := by
      push_cast
      ring
    rw [e, Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
    linarith
  have h := AutomorphicForm.LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div ((t - 1) / 2) hs
  have e1 : (2 * ((t - 1) / 2) + 1 : ℂ) = t := by ring
  have e2 : (2 * ((t - 1) / 2) : ℂ) = t - 1 := by ring
  rw [e1, e2] at h
  unfold M W
  simp only [pow_zero, one_mul]
  exact h

private theorem closed_form (a : ℕ) :
    ∀ {t : ℂ}, (a : ℝ) + 1 < t.re →
      M a t = (Real.pi : ℂ) * (a.factorial : ℂ) * Complex.Gamma (t - 1 - a) / Complex.Gamma t := by
  induction a with
  | zero =>
      intro t ht
      push_cast at ht
      have ht1 : 1 < t.re := by linarith
      have hne : t - 1 ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
        linarith
      have hGt : Complex.Gamma t = (t - 1) * Complex.Gamma (t - 1) := by
        have h := Complex.Gamma_add_one (t - 1) hne
        rw [sub_add_cancel] at h
        exact h
      have hG1 : Complex.Gamma (t - 1) ≠ 0 := by
        refine Complex.Gamma_ne_zero_of_re_pos ?_
        rw [Complex.sub_re, Complex.one_re]
        linarith
      rw [moment_zero ht1]
      simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, sub_zero, mul_one]
      rw [hGt]
      field_simp
  | succ a ih =>
      intro t ht
      push_cast at ht
      have hrec := moment_succ a (t := t) (by linarith)
      have ih1 := ih (t := t - 1) (by rw [Complex.sub_re, Complex.one_re]; linarith)
      have ih2 := ih (t := t) (by linarith)
      have hne1 : t - 1 ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
        linarith
      have hne2 : t - 2 - (a : ℂ) ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        rw [Complex.sub_re, Complex.sub_re, Complex.natCast_re, Complex.zero_re] at this
        norm_num at this
        linarith
      have hGt : Complex.Gamma t = (t - 1) * Complex.Gamma (t - 1) := by
        have h := Complex.Gamma_add_one (t - 1) hne1
        rw [sub_add_cancel] at h
        exact h
      have hGa : Complex.Gamma (t - 1 - a) = (t - 2 - a) * Complex.Gamma (t - 2 - a) := by
        have h := Complex.Gamma_add_one (t - 2 - a) hne2
        rw [show (t - 2 - (a : ℂ) + 1) = t - 1 - a by ring] at h
        exact h
      have hG1 : Complex.Gamma (t - 1) ≠ 0 := by
        refine Complex.Gamma_ne_zero_of_re_pos ?_
        rw [Complex.sub_re, Complex.one_re]
        linarith
      have e1 : Complex.Gamma (t - 1 - 1 - (a : ℂ)) = Complex.Gamma (t - 2 - a) := by
        congr 1
        ring
      have e2 : Complex.Gamma (t - 1 - ((a + 1 : ℕ) : ℂ)) = Complex.Gamma (t - 2 - a) := by
        congr 1
        push_cast
        ring
      rw [hrec, ih1, ih2, e1, e2, hGa, hGt, Nat.factorial_succ]
      push_cast
      field_simp
      ring

private theorem main (a b : ℕ) (t : ℂ) (ht : ((a : ℝ) + b) / 2 + 1 < t.re) :
    ∫ z : ℂ, z ^ a * (starRingEnd ℂ z) ^ b * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-t)
      = if a = b then (Real.pi : ℂ) * (a.factorial : ℂ) * Complex.Gamma (t - 1 - a) / Complex.Gamma t
        else 0 := by
  split_ifs with hab
  · subst hab
    have ht' : (a : ℝ) + 1 < t.re := by linarith
    exact closed_form a ht'
  · exact integral_eq_zero_of_ne a b t hab

end M4aP2DGK.ArchComplexMoments

end

theorem solution
    (a b : ℕ) (t : ℂ) (ht : ((a : ℝ) + b) / 2 + 1 < t.re) :
    ∫ z : ℂ, z ^ a * (starRingEnd ℂ z) ^ b * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-t)
      = if a = b then (Real.pi : ℂ) * (a.factorial : ℂ) * Complex.Gamma (t - 1 - a) / Complex.Gamma t
        else 0 :=
  M4aP2DGK.ArchComplexMoments.main a b t ht

end S_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
end P2MW
export P2MW.S_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg (solution)
