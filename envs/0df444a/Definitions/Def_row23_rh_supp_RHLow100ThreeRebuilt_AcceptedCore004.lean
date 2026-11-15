-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore004
-- name    : row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore004
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:07:15.652443+00:00
-- url     : https://prove2.me/theorems/f9bf45a2-4c6a-4feb-9e8f-3e48c147da36
-- title:
--   Row 23 RH support: RHLow100ThreeRebuilt.AcceptedCore004
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore003
/-
Compact certificate adaptation of sometik179's height-14–100 proof,
Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03).
The theta/Mellin attribution to Gabewhigham is retained in the source.
Large records are reconstructed by ordinary Lean definitions. The original
kernel validators still establish every numerical certificate condition.
-/
import Definitions.Def_row23_rh_supp_RHLow100ThetaReplacement
import Theorems.Thm_TaoFivePrimes_rh14to100_moments_enclosed
import Definitions.Def_row23_rh_supp_RHLow100TranslationReplacement
import Definitions.Def_row23_rh_supp_RHLow100BernsteinReplacement
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.GCongr

/- Ordinary finite arithmetic definitions extracted from sometik179's
height-14–100 certificate, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a.
Theta/Mellin attribution to Gabewhigham is retained. No certificate assertion
or RH theorem is supplied in this definition interface. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false


/- Source module: KernelTail. -/
section Height100Module10

open Real MeasureTheory Set HurwitzZeta HurwitzKernelBounds

namespace TaoZetaBounds

lemma F_nat_zero_shift (a : ℝ) {t : ℝ} (ht : 0 < t) :
    F_nat 0 a t = exp (-π * a ^ 2 * t) + F_nat 0 (a + 1) t := by
  rw [F_nat, (summable_f_nat 0 a ht).tsum_eq_zero_add]
  simp only [f_nat, Nat.cast_zero, zero_add, pow_zero, one_mul]
  congr 1
  unfold F_nat
  apply tsum_congr
  intro n
  simp only [f_nat, pow_zero, one_mul, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

end TaoZetaBounds

end Height100Module10

/- Source module: PolynomialTail. -/
section Height100Module11

open Real MeasureTheory Set Filter
open scoped Topology

namespace TaoZetaBounds

lemma exp_neg_nat_pi_le (n : ℕ) : exp (-(n : ℝ) * π) ≤  (1 / 23 : ℝ)^n := by
  have he : -(n : ℝ) * π = n * (-π) := by ring
  rw [he, exp_nat_mul]
  exact pow_le_pow_left₀ (exp_nonneg _) ZetaSix.exp_neg_pi_le_23 n

end TaoZetaBounds

end Height100Module11

/- Source module: GeneralThetaTail. -/
section Height100Module12

open Real MeasureTheory Set Filter Finset HurwitzZeta HurwitzKernelBounds

namespace CertifiedZetaQuadrature
open TaoZetaBounds

lemma polynomial_exp_majorant_general (m : ℕ) (A c t : ℝ) (hA : 0 < A) (ht : 0 < t) :
    t ^ m * exp (-c * t) ≤ 
      (A ^ m * exp (-m)) * exp (-(c - m / A) * t) := by
  have hl := log_le_sub_one_of_pos (div_pos ht hA)
  rw [log_div ht.ne' hA.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg m : (0:ℝ)≤ m)
  have hle : (m:ℝ) * log t - c * t ≤  m * log A - m - (c - m / A) * t := by
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith
  have et : exp ((m:ℝ) * log t) = t ^ m := by
    rw [exp_nat_mul, exp_log ht]
  have ea : exp ((m:ℝ) * log A) = A ^ m := by
    rw [exp_nat_mul, exp_log hA]
  calc
    t ^ m * exp (-c * t) = exp ((m:ℝ) * log t - c * t) := by
      rw [sub_eq_add_neg, exp_add, et]; congr 1; ring
    _ ≤  exp (m * log A - m - (c - m / A) * t) := exp_le_exp.mpr hle
    _ = (A ^ m * exp (-m)) * exp (-(c - m / A) * t) := by
      rw [sub_eq_add_neg, exp_add, sub_eq_add_neg, exp_add, ea]
      congr 1
      ring

lemma polynomial_exp_tail_general (m : ℕ) (A c : ℝ) (hA : 0 < A) (hd : 0 < c - m / A) :
    IntegrableOn (fun t : ℝ => t ^ m * exp (-c * t)) (Ioi A) ∧
    (∫ t in Ioi A, t ^ m * exp (-c * t)) ≤ 
      A ^ m * exp (-c * A) / (c - m / A) := by
  let d := c - m / A
  have hd0 : 0 < d := hd
  have hg : IntegrableOn
      (fun t : ℝ => (A ^ m * exp (-m)) * exp (-d * t)) (Ioi A) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd0) A).const_mul _
  have hi : IntegrableOn (fun t : ℝ => t ^ m * exp (-c * t)) (Ioi A) := by
    apply hg.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0< t := hA.trans ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact polynomial_exp_majorant_general m A c t hA (hA.trans ht)
  refine ⟨hi, ?_⟩
  have hb := integral_mono_ae hi hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact polynomial_exp_majorant_general m A c t hA (hA.trans ht))
  refine hb.trans_eq ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hd0)]
  have he : -(m:ℝ) + -d * A = -c * A := by dsimp [d]; field_simp; ring
  calc
    A ^ m * exp (-(m:ℝ)) * (-exp (-d * A) / -d) =
        A ^ m * (exp (-m) * exp (-d * A)) / d := by ring
    _ = A ^ m * exp (-c * A) / d := by rw [← exp_add, he]

lemma kernel_finite_remainder_eq (N : ℕ) {t : ℝ} (ht : 0< t) :
    evenKernel 0 t-1-2*(∑ n ∈ range N, exp (-π*(n+1:ℝ)^2*t)) =
      2*F_nat 0 (N+1) t := by
  induction N with
  | zero =>
    have hF : F_int 0 0 t = F_nat 0 0 t + F_nat 0 1 t := by
      simpa only [QuotientAddGroup.mk_zero, sub_zero] using
        F_int_eq_of_mem_Icc 0 (by simp : (0:ℝ) ∈ Set.Icc 0 1) ht
    rw [ZetaSix.evenKernel_zero_eq_F_int ht,hF,F_nat_zero_shift 0 ht]
    simp
    ring
  | succ N ih =>
    rw [sum_range_succ]
    calc
      _ = (evenKernel 0 t-1-2*(∑ n ∈ range N, exp (-π*(n+1:ℝ)^2*t))) -
          2*exp (-π*(N+1:ℝ)^2*t) := by ring
      _ = 2*F_nat 0 (N+1) t - 2*exp (-π*(N+1:ℝ)^2*t) := by rw [ih]
      _ = _ := by rw [F_nat_zero_shift (N+1) ht]; push_cast; ring

lemma kernel_finite_remainder_bound (N : ℕ) {t : ℝ} (ht : 1≤ t) :
    |evenKernel 0 t-1-2*(∑ n ∈ range N, exp (-π*(n+1:ℝ)^2*t))| ≤ 
      (21/10:ℝ)*exp (-π*(N+1:ℝ)^2*t) := by
  rw [kernel_finite_remainder_eq N (by linarith), abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hb := F_nat_zero_le (a := (N+1:ℝ)) (by positivity) (by linarith : 0< t)
  rw [Real.norm_eq_abs] at hb
  have he : exp (-π*t)≤ 1/23 :=
    (exp_le_exp.mpr (by nlinarith [pi_pos])).trans ZetaSix.exp_neg_pi_le_23
  have hd : 0<1-exp (-π*t) := by linarith
  calc
    2*|F_nat 0 (N+1) t| ≤  2*(exp (-π*(N+1:ℝ)^2*t)/(1-exp (-π*t))) := by gcongr
    _ ≤  _ := by
      rw [← mul_div_assoc, div_le_iff₀ hd]
      nlinarith [exp_pos (-π*(N+1:ℝ)^2*t)]

lemma theta_eight_moment_tail :
    (21/10:ℝ)*(∫ t in Ioi (1:ℝ), t^64*exp (-81*π*t)) ≤  1/10^100 := by
  have hb := (polynomial_exp_tail_general 64 1 (81*π) (by norm_num)
    (by nlinarith [pi_gt_three])).2
  have hn : exp (-81*π)≤ (1/23:ℝ)^81 := by simpa using exp_neg_nat_pi_le 81
  calc
    _ ≤  (21/10:ℝ)*(exp (-81*π)/(81*π-64)) := by simpa using mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤ 21/10)
    _ ≤  (21/10:ℝ)*((1/23:ℝ)^81/179) := by gcongr; nlinarith [pi_gt_three]
    _ ≤  1/10^100 := by norm_num

lemma large_moment_tail :
    (21/10:ℝ)*(∫ t in Ioi (400:ℝ), t^64*exp (-π*t)) ≤  1/10^100 := by
  have hb := (polynomial_exp_tail_general 64 400 π (by norm_num)
    (by nlinarith [pi_gt_three])).2
  norm_num only [Nat.cast_ofNat] at hb
  have hn : exp (-π*400)≤ (1/23:ℝ)^(400:ℕ) := by
    rw [show -π*400=-(400:ℝ)*π by ring]
    exact exp_neg_nat_pi_le 400
  calc
    _ ≤  (21/10:ℝ)*((400:ℝ)^(64:ℕ)*exp (-π*400)/(π-64/400)) := by
      have hh := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤ 21/10)
      convert! hh using 1
      norm_num
    _ ≤  (21/10:ℝ)*((400:ℝ)^(64:ℕ)*(1/23:ℝ)^(400:ℕ)/(71/25)) := by gcongr; nlinarith [pi_gt_three]
    _ ≤  1/10^100 := by
      rw [show (400:ℕ)=200+200 by rfl, pow_add]
      norm_num

end CertifiedZetaQuadrature

end Height100Module12

/- Source module: ExponentialKernelBound. -/
section Height100Module13

open Complex Finset Metric

namespace CertifiedZetaQuadrature

noncomputable def thetaTruncation (z : ℂ) : ℂ :=
  ∑ n ∈ range 8, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

noncomputable def kernelMoment (τ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4) * ((8*z)^k/(k.factorial:ℂ)) *
    Complex.exp (I*(τ:ℂ)*z) * thetaTruncation z

end CertifiedZetaQuadrature

end Height100Module13

/- Source module: TwistedCutoff. -/
section Height100Module14

open Real MeasureTheory Set Filter HurwitzZeta
namespace CertifiedZetaQuadrature

noncomputable def phase (τ t : ℝ) : ℂ := Complex.exp (Complex.I*(τ:ℂ)*(log t:ℂ))
noncomputable def twistedRaw (a : ℕ) (τ : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (momentWeight a k t*(evenKernel 0 t-1):ℝ)*phase τ t
noncomputable def twistedFinite (a : ℕ) (τ : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (2*momentWeight a k t*(∑ n ∈ Finset.range 8, exp (-π*(n+1:ℝ)^2*t)):ℝ)*phase τ t

lemma norm_phase (τ t : ℝ) : ‖phase τ t‖=1 := by
  simp [phase,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

lemma momentWeight_nonneg (a k : ℕ) {t : ℝ} (ht : 1≤ t) : 0≤ momentWeight a k t := by
  have hl := log_nonneg ht
  unfold momentWeight
  positivity

lemma momentWeight_bound (a k : ℕ) (ha : a≤ 64) {t : ℝ} (ht : 1≤ t) :
    momentWeight a k t≤ t^64 := by
  have ht0 : 0< t := by linarith
  have hl := log_nonneg ht
  have hp := pow_div_factorial_le_exp (a*log t) (by positivity) k
  rw [exp_nat_mul,exp_log ht0] at hp
  have hr : t^(-3/4:ℝ)≤ 1 := rpow_le_one_of_one_le_of_nonpos ht (by norm_num)
  have hta : t^a≤ t^64 := pow_le_pow_right₀ ht ha
  unfold momentWeight
  rw [mul_div_assoc]
  calc
    _ ≤  t^(-3/4:ℝ)*t^a := by gcongr
    _ ≤  t^a := by nlinarith [pow_nonneg ht0.le a]
    _ ≤  _ := hta

lemma momentWeight_continuousOn (a k : ℕ) : ContinuousOn (momentWeight a k) (Ici 1) := by
  intro t ht
  have ht0 : t≠0 := by linarith [show 1≤ t from ht]
  apply ContinuousAt.continuousWithinAt
  unfold momentWeight
  exact (((continuousAt_id.rpow_const (Or.inl ht0)).mul
    ((continuousAt_const.mul (Real.continuousAt_log ht0)).pow k)).div_const _)

lemma phase_continuousOn (τ : ℝ) : ContinuousOn (phase τ) (Ici 1) := by
  intro t ht
  have ht0 : t≠0 := by linarith [show 1≤ t from ht]
  have hl := Real.continuousAt_log ht0
  apply ContinuousAt.continuousWithinAt
  unfold phase
  fun_prop

lemma twistedRaw_continuousOn (a : ℕ) (τ : ℝ) (k : ℕ) :
    ContinuousOn (twistedRaw a τ k) (Ici 1) := by
  apply ContinuousOn.mul _ (phase_continuousOn τ)
  apply Complex.continuous_ofReal.comp_continuousOn
  apply (momentWeight_continuousOn a k).mul
  exact ((continuousOn_evenKernel 0).mono (fun t ht => by
    change 0< t; linarith [show 1≤ t from ht])).sub continuousOn_const

lemma twistedFinite_continuousOn (a : ℕ) (τ : ℝ) (k : ℕ) :
    ContinuousOn (twistedFinite a τ k) (Ici 1) := by
  apply ContinuousOn.mul _ (phase_continuousOn τ)
  apply Complex.continuous_ofReal.comp_continuousOn
  exact (continuousOn_const.mul (momentWeight_continuousOn a k)).mul (by fun_prop)

lemma norm_twistedRaw_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) {t : ℝ} (ht : 1≤ t) :
    ‖twistedRaw a τ k t‖≤ (21/10:ℝ)*(t^64*exp (-π*t)) := by
  rw [twistedRaw,norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_of_nonneg (momentWeight_nonneg a k ht)]
  calc
    _ ≤  t^64*((21/10:ℝ)*exp (-π*t)) := mul_le_mul (momentWeight_bound a k ha ht)
      (ZetaSix.abs_evenKernel_sub_one_le_of_one_le ht) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma norm_twisted_difference_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64)
    {t : ℝ} (ht : 1≤ t) :
    ‖twistedRaw a τ k t-twistedFinite a τ k t‖≤ (21/10:ℝ)*(t^64*exp (-81*π*t)) := by
  have he : twistedRaw a τ k t-twistedFinite a τ k t =
      ((momentWeight a k t*(evenKernel 0 t-1-2*(∑ n ∈ Finset.range 8,
        exp (-π*(n+1:ℝ)^2*t))):ℝ):ℂ)*phase τ t := by
    unfold twistedRaw twistedFinite
    push_cast
    ring
  rw [he,norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_of_nonneg (momentWeight_nonneg a k ht)]
  have hb := kernel_finite_remainder_bound 8 ht
  norm_num only [Nat.cast_ofNat] at hb
  have hexp : -π*81*t=-81*π*t := by ring
  rw [hexp] at hb
  calc
    _ ≤  t^64*((21/10:ℝ)*exp (-81*π*t)) := mul_le_mul (momentWeight_bound a k ha ht)
      hb (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma twistedRaw_integrable (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) :
    IntegrableOn (twistedRaw a τ k) (Ioi 1) := by
  have hg := ((ZetaSix.integrableOn_pow_mul_exp 64).mono_set
    (Ioi_subset_Ioi (show (0:ℝ)≤ 1 by norm_num))).const_mul (21/10:ℝ)
  apply hg.mono' (((twistedRaw_continuousOn a τ k).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_twistedRaw_bound a τ k ha ht.le

lemma integral_twisted_difference_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) (B : ℝ) :
    ‖∫ t in Ioc (1:ℝ) B, twistedRaw a τ k t-twistedFinite a τ k t‖ ≤  1/10^100 := by
  have hg : IntegrableOn (fun t : ℝ => (21/10:ℝ)*(t^64*exp (-81*π*t))) (Ioi 1) :=
    by
      simpa only [neg_mul,IntegrableOn] using ((polynomial_exp_tail_general 64 1 (81*π) (by norm_num)
        (by nlinarith [pi_gt_three])).1).const_mul (21/10:ℝ)
  have hb := norm_integral_le_of_norm_le
    (hg.mono_set (Ioc_subset_Ioi_self : Ioc (1:ℝ) B ⊆ Ioi 1)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact norm_twisted_difference_bound a τ k ha ht.1.le)
  have hm := setIntegral_mono_set hg
    (Filter.Eventually.of_forall (fun t => by positivity : ∀t:ℝ,0≤ (21/10:ℝ)*(t^64*exp (-81*π*t))))
    (Filter.Eventually.of_forall (Ioc_subset_Ioi_self : Ioc (1:ℝ) B ⊆ Ioi 1))
  apply hb.trans (hm.trans _)
  rw [integral_const_mul]
  exact theta_eight_moment_tail

lemma integral_twisted_tail_bound (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64)
    (B : ℝ) (hB : 400≤ B) :
    ‖∫ t in Ioi B, twistedRaw a τ k t‖≤ 1/10^100 := by
  have hg : IntegrableOn (fun t : ℝ => (21/10:ℝ)*(t^64*exp (-π*t))) (Ioi 400) :=
    ((polynomial_exp_tail_general 64 400 π (by norm_num)
      (by nlinarith [pi_gt_three])).1).const_mul _
  have hb := norm_integral_le_of_norm_le (hg.mono_set (Ioi_subset_Ioi hB)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_twistedRaw_bound a τ k ha (by linarith [show B< t from ht]))
  have hm := setIntegral_mono_set hg
    (Filter.Eventually.of_forall (fun t => by positivity : ∀t:ℝ,0≤ (21/10:ℝ)*(t^64*exp (-π*t))))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi hB))
  apply hb.trans (hm.trans _)
  rw [integral_const_mul]
  exact large_moment_tail

lemma twisted_cutoff (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) (B : ℝ) (hB : 400≤ B) :
    ‖(∫ t in Ioi (1:ℝ), twistedRaw a τ k t) -
      ∫ t in Ioc (1:ℝ) B, twistedFinite a τ k t‖≤ 2/10^100 := by
  have h1B : (1:ℝ)≤ B := by linarith
  have hr := twistedRaw_integrable a τ k ha
  have hf : IntegrableOn (twistedFinite a τ k) (Ioc (1:ℝ) B) :=
    (((twistedFinite_continuousOn a τ k).mono
      (Icc_subset_Ici_self : Icc (1:ℝ) B ⊆ Ici 1)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hs := setIntegral_union
    (show Disjoint (Ioc (1:ℝ) B) (Ioi B) from by simp [Set.disjoint_left]) measurableSet_Ioi
    (hr.mono_set Ioc_subset_Ioi_self) (hr.mono_set (Ioi_subset_Ioi h1B))
  rw [Ioc_union_Ioi_eq_Ioi h1B] at hs
  have he : (∫ t in Ioi (1:ℝ), twistedRaw a τ k t) - ∫ t in Ioc (1:ℝ) B, twistedFinite a τ k t =
      (∫ t in Ioc (1:ℝ) B, twistedRaw a τ k t-twistedFinite a τ k t)+
        ∫ t in Ioi B, twistedRaw a τ k t := by
    rw [integral_sub (hr.mono_set Ioc_subset_Ioi_self) hf]
    rw [hs]
    ring
  rw [he]
  have hdiff := integral_twisted_difference_bound a τ k ha B
  have htail := integral_twisted_tail_bound a τ k ha B hB
  exact (norm_add_le _ _).trans (by linarith)

end CertifiedZetaQuadrature

end Height100Module14

/- Source module: GlobalMomentQuadrature. -/
section Height100Module15

open Complex MeasureTheory Metric Set Finset
namespace CertifiedZetaQuadrature

noncomputable def globalKernelMoment (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4) * ((64*z)^k/(k.factorial:ℂ)) * thetaTruncation z

lemma globalKernelMoment_entire (k : ℕ) : Differentiable ℂ (globalKernelMoment k) := by
  unfold globalKernelMoment thetaTruncation
  fun_prop

end CertifiedZetaQuadrature

end Height100Module15

/- Source module: LogSubstitution. -/
section Height100Module16

open Real MeasureTheory Set Filter Finset
namespace CertifiedZetaQuadrature

noncomputable def transformedMoment (a : ℕ) (τ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4) * (((a:ℂ)*z)^k/(k.factorial:ℂ)) *
    Complex.exp (Complex.I*(τ:ℂ)*z) * thetaTruncation z

lemma exp_six_ge_four_hundred : (400:ℝ)≤ exp 6 := by
  have h1 : (2718/1000:ℝ)≤ exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤ 2718/1000) h1 6
  norm_num at hp
  linarith

lemma finite_theta_cast (u : ℝ) :
    ((∑ n ∈ range 8, exp (-π*(n+1:ℝ)^2*exp u):ℝ):ℂ)=thetaTruncation (u:ℂ) := by
  unfold thetaTruncation
  push_cast
  rfl

lemma weight_exp_identity (a k : ℕ) (u : ℝ) :
    exp u*momentWeight a k (exp u)=exp (u/4)*(a*u)^k/(k.factorial:ℝ) := by
  unfold momentWeight
  rw [log_exp,← Real.exp_mul]
  have he : u+u*(-3/4:ℝ)=u/4 := by ring
  calc
    _ = (exp u*exp (u*(-3/4)))*(a*u)^k/(k.factorial:ℝ) := by ring
    _ = _ := by rw [← exp_add,he]

lemma transformedMoment_point (a : ℕ) (τ : ℝ) (k : ℕ) (u : ℝ) :
    exp u • twistedFinite a τ k (exp u)=transformedMoment a τ k (u:ℂ) := by
  have hw := congrArg (fun x : ℝ => (x:ℂ)) (weight_exp_identity a k u)
  push_cast at hw
  rw [Complex.real_smul]
  unfold twistedFinite transformedMoment phase
  rw [log_exp]
  push_cast
  rw [← finite_theta_cast u]
  calc
    _ = 2*((exp u:ℂ)*(momentWeight a k (exp u):ℂ))*
        Complex.exp (Complex.I*(τ:ℂ)*(u:ℂ))*
        ((∑ n ∈ range 8, exp (-π*(n+1:ℝ)^2*exp u):ℝ):ℂ) := by push_cast; ring
    _ = _ := by rw [Complex.ofReal_exp,hw]; push_cast; ring

lemma transformedMoment_integral (a : ℕ) (τ : ℝ) (k : ℕ) :
    (∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ)) =
      ∫ t in Ioc (1:ℝ) (exp 6), twistedFinite a τ k t := by
  have he := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a:=0) (b:=6) (f:=exp) (f':=exp) (g:=twistedFinite a τ k)
    Real.continuous_exp.continuousOn (fun x _ => Real.hasDerivAt_exp x)
    (fun x _ => (Real.exp_pos x).le)
  simp only [Function.comp_apply,exp_zero] at he
  rw [intervalIntegral.integral_of_le (by linarith [exp_six_ge_four_hundred] : (1:ℝ)≤ exp 6)] at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro u _
  exact (transformedMoment_point a τ k u).symm

lemma twisted_cutoff_transformed (a : ℕ) (τ : ℝ) (k : ℕ) (ha : a≤ 64) :
    ‖(∫ t in Ioi (1:ℝ), twistedRaw a τ k t) -
      ∫ u in (0:ℝ)..6, transformedMoment a τ k (u:ℂ)‖ ≤  2/10^100 := by
  rw [transformedMoment_integral]
  exact twisted_cutoff a τ k ha (exp 6) exp_six_ge_four_hundred

lemma transformedMoment_sixtyfour (k : ℕ) (z : ℂ) :
    transformedMoment 64 0 k z=globalKernelMoment k z := by
  simp [transformedMoment,globalKernelMoment]

end CertifiedZetaQuadrature

end Height100Module16

/- Source module: WideStrip256. -/
section Height100Module17

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxRecDepth 10000

namespace TaoZetaWide256
open ZetaSix

noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤  1 then 21 / 10 * (t ^ (-130 : ℝ) * rexp (-π / t))
  else 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t))

lemma integrableOn_outer :
    IntegrableOn (fun t : ℝ => t ^ (128 : ℝ) * rexp (-π * t)) (Ioi 1) := by
  simpa only [Real.rpow_ofNat] using
    (ZetaSix.integrableOn_pow_mul_exp 128).mono_set (Ioi_subset_Ioi zero_le_one)

lemma outer_le :
    (∫ t in Ioi (1 : ℝ), t ^ (128 : ℝ) * rexp (-π * t)) ≤  ((10^155) : ℝ) / (21 / 10) := by
  have h := MeasureTheory.setIntegral_mono_set
    (ZetaSix.integrableOn_pow_mul_exp 128)
    (Filter.Eventually.of_forall (fun x : ℝ => by positivity :
      ∀ x : ℝ, 0 ≤  x ^ 128 * rexp (-π * x)))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi (show (0 : ℝ) ≤  1 by norm_num)))
  simp only [Real.rpow_ofNat] at *
  rw [ZetaSix.integral_pow_mul_exp] at h
  have hp : (3 : ℝ) ^ 129 ≤  π ^ 129 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 129
  have hpi : (0 : ℝ) < π ^ 129 := by positivity
  have hb : (Nat.factorial 128 : ℝ) / π ^ 129 ≤  (10^155) / (21 / 10) := by
    rw [div_le_iff₀ hpi]
    norm_num [Nat.factorial] at *
    nlinarith
  exact h.trans hb

/-- The kernel of the substituted integral: `u^{-1/2} e^{-π u}` cut off below `1`. -/
private noncomputable def gInd : ℝ → ℝ :=
  Set.indicator (Ioi 1) fun u => u ^ (128 : ℝ) * rexp (-π * u)

private lemma gInd_integrableOn : IntegrableOn gInd (Ioi (0 : ℝ)) := by
  rw [gInd]
  exact (integrableOn_outer.integrable_indicator measurableSet_Ioi).integrableOn

private lemma integral_gInd : (∫ y in Ioi (0 : ℝ), gInd y)
    = ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
  rw [gInd, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]
  norm_num

private lemma cov_ptwise (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))
      = (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-130 : ℝ) * rexp (-π / x)) x := by
  have hx0 : 0 < x := hx
  have hinv : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one]
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 : ℝ) < x⁻¹ := by rw [lt_inv_comm₀ (by norm_num) hx0]; simpa using h
    rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, h⟩), gInd, hinv,
      Set.indicator_of_mem (mem_Ioi.mpr h1)]
    have hd : -π * x⁻¹ = -π / x := by field_simp
    have hpow : (x⁻¹) ^ (128 : ℝ) = x ^ (-128 : ℝ) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_mul hx0.le]
      norm_num
    rw [hd, hpow, smul_eq_mul]
    have hxx : x ^ ((-1 : ℝ) - 1) * x ^ (-128 : ℝ) = x ^ (-130 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul, ← mul_assoc, hxx]
  · have h1 : x⁻¹ ≤  1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [Set.indicator_of_notMem (by simp; intro _; exact h), gInd, hinv,
      Set.indicator_of_notMem (by simp [not_lt.2 h1])]
    simp

lemma integrableOn_inner :
    IntegrableOn (fun x : ℝ => x ^ (-130 : ℝ) * rexp (-π / x)) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn
      (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))) (Ioi 0) :=
    (MeasureTheory.integrableOn_Ioi_comp_rpow_iff gInd (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      gInd_integrableOn
  have h2 : IntegrableOn
      ((Ioo (0 : ℝ) 1).indicator fun x => x ^ (-130 : ℝ) * rexp (-π / x)) (Ioi 0) :=
    h1.congr_fun cov_ptwise measurableSet_Ioi
  have h3 := (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mp h2
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at h3
  rw [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h3

lemma integral_inner : (∫ x in Ioc (0 : ℝ) 1, x ^ (-130 : ℝ) * rexp (-π / x))
    = ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
  have hcov := MeasureTheory.integral_comp_rpow_Ioi gInd (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_gInd] at hcov
  rw [setIntegral_congr_fun measurableSet_Ioi cov_ptwise] at hcov
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, Measure.restrict_restrict
    measurableSet_Ioo, show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at hcov
  rw [← MeasureTheory.Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact hcov

lemma integrableOn_maj_Ioc : IntegrableOn maj (Ioc (0 : ℝ) 1) := by
  have h : IntegrableOn (fun x : ℝ => 21 / 10 * (x ^ (-130 : ℝ) * rexp (-π / x)))
      (Ioc (0 : ℝ) 1) := integrableOn_inner.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp [maj, ht.2]

lemma integrableOn_maj_Ioi : IntegrableOn maj (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun t : ℝ => 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t)))
      (Ioi (1 : ℝ)) := integrableOn_outer.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp [maj, not_le.2 (mem_Ioi.mp ht)]

lemma integrableOn_maj : IntegrableOn maj (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact integrableOn_maj_Ioc.union integrableOn_maj_Ioi

lemma integral_maj_le : ∫ t in Ioi (0 : ℝ), maj t ≤  (2*10^155) := by
  have hsplit : ∫ t in Ioi (0 : ℝ), maj t
      = (∫ t in Ioc (0 : ℝ) 1, maj t) + ∫ t in Ioi (1 : ℝ), maj t := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      integrableOn_maj_Ioc integrableOn_maj_Ioi
  have h1 : ∫ t in Ioc (0 : ℝ) 1, maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun t : ℝ => 21 / 10 * (t ^ (-130 : ℝ) * rexp (-π / t)))
      (fun t ht => by simp [maj, ht.2]), integral_const_mul, integral_inner]
  have h2 : ∫ t in Ioi (1 : ℝ), maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (128 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t)))
      (fun t ht => by simp [maj, not_le.2 (mem_Ioi.mp ht)]), integral_const_mul]
  rw [hsplit, h1, h2]
  have hJ := outer_le
  linarith

lemma norm_integrand_le {s : ℂ} (h0 : -256 ≤  s.re) (h1 : s.re ≤  257) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s / 2 - 1) • P.f_modif t‖ ≤  maj t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (s / 2 - 1).re = s.re / 2 - 1 by simp]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hmaj : maj t = 21 / 10 * (t ^ (-130 : ℝ) * rexp (-π / t)) := by simp [maj, hlt.le]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_lt_one ht hlt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hcomb : t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t))
        = 21 / 10 * (t ^ (s.re / 2 - 3 / 2) * rexp (-π / t)) := by
      rw [show s.re / 2 - 3 / 2 = (s.re / 2 - 1) + (-(1 : ℝ) / 2) by ring, Real.rpow_add ht]
      ring
    rw [hcomb]
    have hexp : t ^ (s.re / 2 - 3 / 2) ≤  t ^ (-130 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π / t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (-130 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 3 / 2)]
  · have hm : maj (1 : ℝ) = 21 / 10 * ((1 : ℝ) ^ (-130 : ℝ) * rexp (-π / 1)) := if_pos le_rfl
    rw [hm, f_modif_one]
    simp only [norm_zero, mul_zero]
    positivity
  · have hmaj : maj t = 21 / 10 * (t ^ (128 : ℝ) * rexp (-π * t)) := by
      simp [maj, not_le.2 hgt]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * rexp (-π * t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_one_lt hgt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hexp : t ^ (s.re / 2 - 1) ≤  t ^ (128 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π * t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (128 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 1)]

/-- **Sharpened bound on the entire part of the completed zeta function.**
In the critical strip, `‖Λ₀ s‖ ≤  (10^155)`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h0 : -256 ≤  s.re) (h1 : s.re ≤  257) :
    ‖completedRiemannZeta₀ s‖ ≤  (10^155) := by
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef, norm_div, Complex.norm_ofNat]
  have hb : ‖mellin P.f_modif (s / 2)‖ ≤  ∫ t in Ioi (0 : ℝ), maj t := by
    rw [mellin]
    refine norm_integral_le_of_norm_le integrableOn_maj ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact norm_integrand_le h0 h1 ht
  have := hb.trans integral_maj_le
  linarith

end TaoZetaWide256

end Height100Module17


