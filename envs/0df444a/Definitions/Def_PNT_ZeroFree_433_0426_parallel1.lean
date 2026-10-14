-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0426_parallel1
-- name    : PNT_ZeroFree_433_0426_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:24:43.199201+00:00
-- url     : https://prove2.me/theorems/0fbed9c7-8d9c-4132-91b9-65550b0043c8
-- title:
--   Zero-free region foundations: ContinuationContour, ContinuationPolynomialContour [0426_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.ContinuationContour
--   - OAI.NumberTheory.DirichletL.ContinuationPolynomialContour
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ContinuationContour.lean#L12-L107
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ContinuationPolynomialContour.lean#L11-L77

import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Definitions.Def_PNT_ZeroFree_433_0147
import Definitions.Def_PNT_ZeroFree_433_0149
import Definitions.Def_PNT_ZeroFree_433_0345_parallel1
import Definitions.Def_PNT_ZeroFree_433_0377_parallel1
import Definitions.Def_PNT_ZeroFree_433_0419_parallel1
import Definitions.Def_PNT_ZeroFree_433_0475_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ContinuationContour.lean#L12-L107
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ContinuationPolynomialContour.lean#L11-L77
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.ContinuationContour
section
namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation

theorem vertical_integral_eq_of_horizontal_vanish (F : ℂ → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (ha : Integrable (fun y : ℝ => F ((a : ℂ) + y * I)))
    (hb : Integrable (fun y : ℝ => F ((b : ℂ) + y * I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I))
      atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + T * I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, F ((a : ℂ) + y * I)) = ∫ y : ℝ, F ((b : ℂ) + y * I) := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I)) -
      (∫ x : ℝ in a..b, F ((x : ℂ) + T * I)) +
      I * (∫ y : ℝ in -T..T, F ((b : ℂ) + y * I)) -
      I * (∫ y : ℝ in -T..T, F ((a : ℂ) + y * I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn F
      ((a : ℂ) + (-T) * I) ((b : ℂ) + T * I) (hhol.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      have hzre := hz.1
      simpa [uIcc_of_le hab] using hzre
  have hlim := ((hbot.sub htop).add
    ((intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id).const_mul I)).sub
    ((intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).const_mul I)
  have hzero : (0 : ℂ) - 0 + I * (∫ y : ℝ, F ((b : ℂ) + y * I)) -
      I * (∫ y : ℝ, F ((a : ℂ) + y * I)) = 0 :=
    tendsto_nhds_unique hlim (by simpa only [id_eq, hrect] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0)))
  have heq : I * (∫ y : ℝ, F ((b : ℂ) + y * I)) =
      I * (∫ y : ℝ, F ((a : ℂ) + y * I)) := by simpa using sub_eq_zero.mp hzero
  exact (mul_left_cancel₀ I_ne_zero heq).symm

theorem horizontal_integral_tendsto_zero (F : ℂ → ℂ) (a b C : ℝ)
    (hbound : ∀ x ∈ Set.uIcc a b, ∀ y : ℝ,
      ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-(y ^ 2))) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + T * I)) atTop (𝓝 0) := by
  have hnorm (T : ℝ) : ‖∫ x : ℝ in a..b, F ((x : ℂ) + T * I)‖ ≤
      C * Real.exp (-(T ^ 2)) * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hbound x (uIoc_subset_uIcc hx) T)
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by decide)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hnorm
    (by simpa using (hexp.const_mul C).mul_const |b-a|)

theorem integrable_of_gaussian_bound (f : ℝ → ℂ) (C : ℝ)
    (hmeas : AEStronglyMeasurable f) (hbound : ∀ y, ‖f y‖ ≤ C * Real.exp (-(y ^ 2))) :
    Integrable f := by
  have hg : Integrable (fun y : ℝ => C * Real.exp (-(y ^ 2))) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul C
  exact hg.mono' hmeas (ae_of_all _ hbound)

theorem vertical_integral_eq_of_gaussian_bound (F : ℂ → ℂ) {a b C : ℝ}
    (hab : a ≤ b) (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ,
      ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-(y ^ 2))) :
    (∫ y : ℝ, F ((a : ℂ) + y * I)) = ∫ y : ℝ, F ((b : ℂ) + y * I) := by
  have hc (x : ℝ) (hx : x ∈ Icc a b) : Continuous (fun y : ℝ => F ((x : ℂ) + y * I)) :=
    hhol.continuousOn.comp_continuous (by fun_prop) (by intro y; simpa using hx)
  apply vertical_integral_eq_of_horizontal_vanish F hab hhol
    (integrable_of_gaussian_bound _ C (hc a ⟨le_rfl, hab⟩).aestronglyMeasurable
      (hbound a ⟨le_rfl, hab⟩))
    (integrable_of_gaussian_bound _ C (hc b ⟨hab, le_rfl⟩).aestronglyMeasurable
      (hbound b ⟨hab, le_rfl⟩))
  · have h := horizontal_integral_tendsto_zero (fun s => F ((s.re : ℂ) - s.im * I)) a b C ?_
    · simpa [sub_eq_add_neg, neg_mul] using h
    · intro x hx y
      simpa [sub_eq_add_neg, neg_mul] using hbound x (by simpa [uIcc_of_le hab] using hx) (-y)
  · exact horizontal_integral_tendsto_zero F a b C
      (by simpa [uIcc_of_le hab] using hbound)

def gaussianContourIntegrand (G : ℂ → ℂ) (c Z : ℝ) (s : ℂ) : ℂ :=
  (Z : ℂ) ^ (s + (c : ℂ)) * Complex.exp ((s - 5 / 6) ^ 2) * G s

theorem norm_gaussianContourIntegrand (G : ℂ → ℂ) (c x y : ℝ) {Z : ℝ}
    (hZ : 0 < Z) :
    ‖gaussianContourIntegrand G c Z ((x : ℂ) + y * I)‖ =
      Z ^ (x + c) * Real.exp ((x - 5 / 6) ^ 2) *
        ‖G ((x : ℂ) + y * I)‖ * Real.exp (-(y ^ 2)) := by
  unfold gaussianContourIntegrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_exp]
  have hre : ((((x : ℂ) + y * I) - 5 / 6) ^ 2).re = (x - 5 / 6) ^ 2 - y ^ 2 := by
    simp [pow_two]
  rw [hre, Real.exp_sub]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, zero_mul, sub_self,
    add_zero, Real.exp_neg]
  ring

theorem gaussianContourIntegrand_differentiableOn {G : ℂ → ℂ} {U : Set ℂ}
    (hG : DifferentiableOn ℂ G U) (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    DifferentiableOn ℂ (gaussianContourIntegrand G c Z) U := by
  apply DifferentiableOn.mul _ hG
  apply DifferentiableOn.mul
  · exact ((differentiable_id.add_const (c : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).differentiableOn
  · exact (((differentiable_id.sub_const (5 / 6 : ℂ)).pow 2).cexp).differentiableOn

end SevenEighths.Continuation

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.ContinuationPolynomialContour
section
namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation

def polynomialGaussian (n : ℕ) (y : ℝ) : ℝ :=
  (1+|y|^n)*Real.exp (-(y^2))

theorem polynomialGaussian_nonneg (n : ℕ) (y : ℝ) : 0 ≤ polynomialGaussian n y := by
  unfold polynomialGaussian
  positivity

theorem polynomialGaussian_even (n : ℕ) (y : ℝ) :
    polynomialGaussian n (-y) = polynomialGaussian n y := by
  simp [polynomialGaussian]

theorem polynomialGaussian_integrable (n : ℕ) : Integrable (polynomialGaussian n) := by
  have hp := (integrable_rpow_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ)<1) (show (-1 : ℝ)<(n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])).norm
  have hg := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have he : (fun y : ℝ => ‖y^(n : ℝ)*Real.exp (-1*y^2)‖) =
      fun y : ℝ => |y|^n*Real.exp (-(y^2)) := by
    funext y
    simp [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [he] at hp
  convert! hg.add hp using 1
  funext y
  simp [polynomialGaussian, add_mul]

theorem polynomialGaussian_tendsto (n : ℕ) :
    Tendsto (polynomialGaussian n) atTop (𝓝 0) := by
  have hp := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (by norm_num : (0 : ℝ)<1) (n : ℝ)
  rw [cocompact_eq_atBot_atTop] at hp
  have hp' := hp.mono_left le_sup_right
  have hg : Tendsto (fun y : ℝ => Real.exp (-(y^2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by decide)))
  change Tendsto (fun y : ℝ => (1+|y|^n)*Real.exp (-(y^2))) atTop (𝓝 0)
  simpa [Real.rpow_natCast, add_mul] using hg.add hp'

theorem vertical_integral_eq_of_even_envelope (F : ℂ → ℂ) {a b C : ℝ}
    (E : ℝ → ℝ) (hE : Integrable E) (heven : ∀ y, E (-y)=E y)
    (hlim : Tendsto E atTop (𝓝 0)) (hab : a ≤ b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, ‖F ((x : ℂ)+y*I)‖ ≤ C*E y) :
    (∫ y : ℝ, F ((a : ℂ)+y*I)) = ∫ y : ℝ, F ((b : ℂ)+y*I) := by
  have hc (x : ℝ) (hx : x ∈ Icc a b) : Continuous (fun y : ℝ => F ((x : ℂ)+y*I)) :=
    hhol.continuousOn.comp_continuous (by fun_prop) (by intro y; simpa using hx)
  have hint (x : ℝ) (hx : x ∈ Icc a b) : Integrable (fun y : ℝ => F ((x : ℂ)+y*I)) :=
    (hE.const_mul C).mono' (hc x hx).aestronglyMeasurable (ae_of_all _ (hbound x hx))
  have hhorizontal (sgn : ℝ) (heq : ∀ y, E (sgn*y)=E y) :
      Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ)+(sgn*T)*I)) atTop (𝓝 0) := by
    have hnorm (T : ℝ) : ‖∫ x : ℝ in a..b, F ((x : ℂ)+(sgn*T)*I)‖ ≤ C*E T*|b-a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      simpa only [heq, Complex.ofReal_mul] using hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) (sgn*T)
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hnorm
      (by simpa using (hlim.const_mul C).mul_const |b-a|)
  apply vertical_integral_eq_of_horizontal_vanish F hab hhol
    (hint a ⟨le_rfl,hab⟩) (hint b ⟨hab,le_rfl⟩)
  · simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul] using hhorizontal (-1) (by simpa only [neg_one_mul] using heven)
  · simpa only [Complex.ofReal_one, one_mul] using hhorizontal 1 (by simp)

theorem vertical_integral_eq_of_polynomial_gaussian_bound (F : ℂ → ℂ)
    {a b C : ℝ} (n : ℕ) (hab : a ≤ b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ,
      ‖F ((x : ℂ)+y*I)‖ ≤ C*polynomialGaussian n y) :
    (∫ y : ℝ, F ((a : ℂ)+y*I)) = ∫ y : ℝ, F ((b : ℂ)+y*I) :=
  vertical_integral_eq_of_even_envelope F _ (polynomialGaussian_integrable n)
    (polynomialGaussian_even n) (polynomialGaussian_tendsto n) hab hhol hbound

end SevenEighths.Continuation

end

end OAI

end


