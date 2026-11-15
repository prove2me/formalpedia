-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore006
-- name    : row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore006
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:14:25.992449+00:00
-- url     : https://prove2.me/theorems/2d3eed8d-40ef-4b56-8cc8-9077cbd465ef
-- title:
--   Row 23 RH support: RHLow100ThreeRebuilt.AcceptedCore006
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore005
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


/- Source module: GlobalMomentBridge. -/
section Height100Module25

open Complex MeasureTheory Set Finset
namespace CertifiedGlobalMoments
open CertifiedZetaQuadrature TaoZetaCertificate

noncomputable def scaledVariable (z : ℂ) : ℂ := (z-1/2)/128
noncomputable def polynomial (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ range 256, (b j:ℂ)*(scaledVariable z)^(2*j)
noncomputable def xiPolynomial (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  1/2+z*(z-1)/2*polynomial b z

lemma moment_complex (j : ℕ) :
    (moment j:ℂ)=∫ t in Ioi (1:ℝ), twistedRaw 64 0 (2*j) t := by
  unfold moment twistedRaw
  simp only [phase,ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,mul_one]
  exact (integral_complex_ofReal).symm

lemma moment_scaled_integral (j : ℕ) :
    (moment j:ℂ)=(64:ℂ)^(2*j)/((2*j).factorial:ℂ)*∫ t in Ioi (1:ℝ), outerIntegrand j t := by
  unfold moment outerIntegrand
  rw [← integral_complex_ofReal,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  unfold momentWeight
  push_cast
  rw [mul_pow]
  ring

lemma even_term (z : ℂ) (j : ℕ) :
    TaoZetaGlobal.taylorTerm z (2*j)=(moment j:ℂ)*(scaledVariable z)^(2*j) := by
  rw [TaoZetaGlobal.taylorTerm,even_derivative_moment_folded,moment_scaled_integral]
  simp only [smul_eq_mul,scaledVariable,div_pow]
  rw [show (128:ℂ)=64*2 by norm_num,mul_pow]
  have hf : ((2*j).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*j)
  field_simp

lemma odd_term (z : ℂ) (j : ℕ) : TaoZetaGlobal.taylorTerm z (2*j+1)=0 := by
  unfold TaoZetaGlobal.taylorTerm
  rw [odd_taylor_derivative_zero]
  simp

lemma sum_even_odd (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range (2*N), f n)=∑ j ∈ range N, (f (2*j)+f (2*j+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=2*N+1+1 by omega]
    simp only [sum_range_succ,ih]
    ring

lemma taylor_sum_eq (z : ℂ) :
    (∑ n ∈ range 512, TaoZetaGlobal.taylorTerm z n)=polynomial moment z := by
  rw [show 512=2*256 by norm_num,sum_even_odd]
  simp_rw [even_term,odd_term,add_zero]
  rfl

lemma polynomial_entire (b : ℕ → ℝ) : Differentiable ℂ (polynomial b) := by
  unfold polynomial scaledVariable
  fun_prop

lemma xiPolynomial_entire (b : ℕ → ℝ) : Differentiable ℂ (xiPolynomial b) := by
  have h := polynomial_entire b
  unfold xiPolynomial
  fun_prop

lemma scaledVariable_norm (z : ℂ) (hz : ‖z-1/2‖≤ 104) : ‖scaledVariable z‖≤ 13/16 := by
  rw [scaledVariable,norm_div]
  norm_num
  linarith

lemma polynomial_error (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ ε)
    (hb : ∀ j<256, |moment j-b j|≤ ε) (z : ℂ) (hz : ‖z-1/2‖≤ 104) :
    ‖polynomial moment z-polynomial b z‖≤ 3*ε := by
  have hv := scaledVariable_norm z hz
  have hgeo := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤ 169/256) (by norm_num : (169/256:ℝ)<1)
  have hs := sum_le_hasSum (range 256) (fun n _ => pow_nonneg (by norm_num : (0:ℝ)≤ 169/256) n) hgeo
  have he : polynomial moment z-polynomial b z =
      ∑ j ∈ range 256, ((moment j-b j:ℝ):ℂ)*(scaledVariable z)^(2*j) := by
    unfold polynomial
    simp_rw [ofReal_sub,sub_mul,sum_sub_distrib]
  rw [he]
  calc
    _ ≤  ∑ j ∈ range 256, ‖((moment j-b j:ℝ):ℂ)*(scaledVariable z)^(2*j)‖ := norm_sum_le _ _
    _ ≤  ε*∑ j ∈ range 256, (169/256:ℝ)^j := by
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow]
      have hp : ‖scaledVariable z‖^(2*j)≤ (169/256:ℝ)^j := by
        calc
          _ ≤  (13/16:ℝ)^(2*j) := pow_le_pow_left₀ (norm_nonneg _) hv _
          _ = _ := by rw [pow_mul]; norm_num
      exact mul_le_mul (hb j (mem_range.mp hj)) hp (by positivity) hε
    _ ≤  ε*(1-(169/256:ℝ))⁻¹ := mul_le_mul_of_nonneg_left hs hε
    _ ≤  3*ε := by norm_num; linarith

lemma completedZeta_error (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ ε)
    (hb : ∀ j<256, |moment j-b j|≤ ε) (z : ℂ) (hz : ‖z-1/2‖≤ 104) :
    ‖completedRiemannZeta₀ z-polynomial b z‖≤ 1/10^45+3*ε := by
  have ht := TaoZetaGlobal.norm_taylor_remainder_512 z hz
  rw [taylor_sum_eq] at ht
  have hp := polynomial_error b ε hε hb z hz
  have he : completedRiemannZeta₀ z-polynomial b z =
      (completedRiemannZeta₀ z-polynomial moment z)+(polynomial moment z-polynomial b z) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add ht hp)

lemma xi_error (b : ℕ → ℝ)
    (hb : ∀ j<256, |moment j-b j|≤ 1/10^46) (z : ℂ) (hz : ‖z-1/2‖≤ 104) :
    ‖CertifiedLocalXi.xi z-xiPolynomial b z‖≤ 1/10^41 := by
  have h0 : ‖z‖≤ 105 := by
    have h := norm_add_le (z-(1/2:ℂ)) (1/2:ℂ)
    rw [sub_add_cancel] at h
    norm_num at h
    linarith
  have h1 : ‖z-1‖≤ 105 := by
    have h := norm_sub_le (z-(1/2:ℂ)) (1/2:ℂ)
    rw [show z-(1/2:ℂ)-1/2=z-1 by ring] at h
    norm_num at h
    linarith
  have hp : ‖z*(z-1)/2‖≤ 6000 := by
    rw [norm_div,norm_mul]
    norm_num
    nlinarith [norm_nonneg z,norm_nonneg (z-1),mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  have he : CertifiedLocalXi.xi z-xiPolynomial b z=
      (z*(z-1)/2)*(completedRiemannZeta₀ z-polynomial b z) := by
    unfold CertifiedLocalXi.xi xiPolynomial
    ring
  rw [he,norm_mul]
  have hc := completedZeta_error b (1/10^46) (by positivity) hb z hz
  calc
    _ ≤  6000*((1/10^45)+3*(1/10^46:ℝ)) := mul_le_mul hp hc (norm_nonneg _) (by norm_num)
    _ ≤  _ := by norm_num

lemma local_coefficient_error (b : ℕ → ℝ)
    (hb : ∀ j<256, |moment j-b j|≤ 1/10^46) (T : ℝ) (hT : |T|≤ 100) (n : ℕ) :
    ‖CertifiedTaylorQuadrature.coefficient CertifiedLocalXi.xi (CertifiedLocalXi.center T) n-
      CertifiedTaylorQuadrature.coefficient (xiPolynomial b) (CertifiedLocalXi.center T) n‖≤ 1/10^41 := by
  have hs : ∀ z ∈ Metric.sphere (CertifiedLocalXi.center T) (1:ℝ),
      ‖CertifiedLocalXi.xi z-xiPolynomial b z‖≤ 1/10^41 := by
    intro z hz
    apply xi_error b hb
    have h := norm_add_le (z-CertifiedLocalXi.center T) (CertifiedLocalXi.center T-(1/2:ℂ))
    rw [sub_add_sub_cancel,mem_sphere_iff_norm.mp hz] at h
    have hc : ‖CertifiedLocalXi.center T-(1/2:ℂ)‖=|T| := by
      simp [CertifiedLocalXi.center,Real.norm_eq_abs]
    rw [hc] at h
    linarith
  have h := CertifiedComplexTaylor.coefficient_error CertifiedLocalXi.xi (xiPolynomial b)
    CertifiedLocalXi.xi_entire (xiPolynomial_entire b) (CertifiedLocalXi.center T) 1 (1/10^41)
    (by norm_num) hs n
  simpa using h

end CertifiedGlobalMoments

end Height100Module25

/- Source module: EvenPolynomialRecurrence. -/
section Height100Module26

open Complex Finset
namespace CertifiedEvenPolynomial

lemma recurrence_eval (E : ℕ → ℂ) (H : ℂ) (N : ℕ) (hE : E N=0) (z : ℂ) :
    (∑ j ∈ range (N+1),
      ((if j=0 then H else 0)-E j-(if j=0 then 0 else 4*E (j-1)))*z^(2*j)) =
      H-∑ j ∈ range N, E j*(z^(2*j)+4*z^(2*j+2)) := by
  have hconst : (∑ j ∈ range (N+1), (if j=0 then H else 0)*z^(2*j))=H := by
    rw [sum_range_succ']
    simp
  have hmain : (∑ j ∈ range (N+1), E j*z^(2*j))=∑ j ∈ range N, E j*z^(2*j) := by
    rw [sum_range_succ,hE,zero_mul,add_zero]
  have hshift : (∑ j ∈ range (N+1), (if j=0 then 0 else 4*E (j-1))*z^(2*j))=
      ∑ j ∈ range N, 4*E j*z^(2*j+2) := by
    rw [sum_range_succ']
    simp [Nat.mul_add]
  simp_rw [sub_mul]
  rw [sum_sub_distrib,sum_sub_distrib,hconst,hmain,hshift]
  rw [sub_sub,←sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro j hj
  ring

lemma dense_even_eval (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (∑ m ∈ range (2*N+1), (if m%2=0 then a (m/2) else 0)*z^m)=
      ∑ j ∈ range (N+1), a j*z^(2*j) := by
  have he := CertifiedGlobalMoments.sum_even_odd
    (fun m => (if m%2=0 then a (m/2) else 0)*z^m) (N+1)
  have hlen : 2*(N+1)=(2*N+1)+1 := by omega
  rw [hlen,sum_range_succ] at he
  simpa using he

end CertifiedEvenPolynomial

end Height100Module26

/- Source module: CauchyStability. -/
section Height100Module27

open Complex Metric Set
namespace CertifiedLocalXi

lemma deriv_bound_from_unit_ball (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (δ : ℝ)
    (hb : ∀ z, ‖z-c‖≤ 1 → ‖f z‖≤ δ) (z : ℂ) (hz : ‖z-c‖≤ 3/4) :
    ‖deriv f z‖≤ 4*δ := by
  have hcircle : ∀ w ∈ sphere z (1/4:ℝ), ‖f w‖≤ δ := by
    intro w hw
    apply hb
    calc
      ‖w-c‖ = ‖(w-z)+(z-c)‖ := by congr 1; ring
      _ ≤  ‖w-z‖+‖z-c‖ := norm_add_le _ _
      _ ≤  1 := by rw [mem_sphere_iff_norm.mp hw]; linarith
  have h := CertifiedTaylorQuadrature.coefficient_bound f hf z (1/4) δ (by norm_num) hcircle 1
  norm_num [CertifiedTaylorQuadrature.coefficient] at h
  linarith

lemma lipschitz_from_unit_ball (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (δ : ℝ)
    (hb : ∀ z, ‖z-c‖≤ 1 → ‖f z‖≤ δ) (z w : ℂ)
    (hz : ‖z-c‖≤ 3/4) (hw : ‖w-c‖≤ 3/4) :
    ‖f z-f w‖≤ 4*δ*‖z-w‖ := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hf x)
    (fun x hx => deriv_bound_from_unit_ball f hf c δ hb x (mem_closedBall_iff_norm.mp hx))
    (convex_closedBall c (3/4)) (mem_closedBall_iff_norm.mpr hw) (mem_closedBall_iff_norm.mpr hz)

lemma critical_projection_distance (z : ℂ) : ‖z-center z.im‖=|z.re-1/2| := by
  have he : z-center z.im=((z.re-1/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [center]
  rw [he,Complex.norm_real,Real.norm_eq_abs]

lemma critical_projection_in_ball (T : ℝ) (z : ℂ) :
    ‖center z.im-center T‖≤ ‖z-center T‖ := by
  have he : center z.im-center T=((z.im-T:ℝ):ℂ)*I := by unfold center; push_cast; ring
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  simpa [center] using Complex.abs_im_le_norm (z-center T)

lemma imaginary_error_from_critical_reality (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (T δ : ℝ) (hb : ∀ z, ‖z-center T‖≤ 1 → ‖f z‖≤ δ)
    (hcritical : ∀ y : ℝ, ‖center y-center T‖≤ 3/4 → (f (center y)).im=0)
    (z : ℂ) (hz : ‖z-center T‖≤ 3/4) :
    |(f z).im|≤ 4*δ*|z.re-1/2| := by
  have hw := (critical_projection_in_ball T z).trans hz
  have hl := lipschitz_from_unit_ball f hf (center T) δ hb z (center z.im) hz hw
  rw [critical_projection_distance] at hl
  have he : (f z).im=(f z-f (center z.im)).im := by
    rw [sub_im,hcritical z.im hw,sub_zero]
  rw [he]
  exact (Complex.abs_im_le_norm _).trans hl

end CertifiedLocalXi

end Height100Module27

/- Source module: LocalExclusion. -/
section Height100Module28

open Complex Metric
open scoped ComplexConjugate
namespace CertifiedLocalXi

lemma xi_critical_real (T : ℝ) : (xi (center T)).im=0 := by
  have hc : conj (center T)=1-center T := by
    apply Complex.ext <;> simp [center]
    ring
  have he := TaoZetaCertificate.completedZeta_conj (center T)
  rw [hc,completedRiemannZeta₀_one_sub] at he
  have hi := congrArg Complex.im he
  simp only [conj_im] at hi
  have hΛ : (completedRiemannZeta₀ (center T)).im=0 := by linarith
  have hf : (center T*(center T-1)/2).im=0 := by
    norm_num [center,mul_im]
    ring
  unfold xi
  simp [mul_im,hf,hΛ]

lemma rectangle_in_three_quarter_ball (T : ℝ) (z : ℂ)
    (hr0 : 0≤ z.re) (hr1 : z.re≤ 1) (hi : |z.im-T|≤ 1/2) :
    ‖z-center T‖≤ 3/4 := by
  have he : ‖z-center T‖^2=(z.re-1/2)^2+(z.im-T)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [center]
    ring
  have hr : (z.re-1/2)^2≤ 1/4 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  have him : (z.im-T)^2≤ 1/4 := by
    have h := abs_le.mp hi
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (sub_nonneg.mpr h.1)]
  nlinarith [norm_nonneg (z-center T)]

/-- A real-part certificate or a normalized imaginary-part certificate excludes a zero
away from the critical line; uniform approximation on the unit disk supplies both error bounds. -/
lemma nonzero_of_local_certificate (F P : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hP : Differentiable ℂ P) (T : ℝ)
    (happrox : ∀ z, ‖z-center T‖≤ 1 → ‖F z-P z‖≤ 1/100)
    (hcritical : ∀ y : ℝ, (F (center y)-P (center y)).im=0)
    (z : ℂ) (hr0 : 0≤ z.re) (hr1 : z.re≤ 1) (hi : |z.im-T|≤ 1/2)
    (hneq : z.re≠1/2)
    (hcertificate : 1≤ |(P z).re| ∨ |z.re-1/2|≤ |(P z).im|) : F z≠0 := by
  have hz := rectangle_in_three_quarter_ball T z hr0 hr1 hi
  have hz1 : ‖z-center T‖≤ 1 := by linarith
  intro hzero
  rcases hcertificate with hreal | himag
  · have h := happrox z hz1
    rw [hzero,zero_sub,norm_neg] at h
    have hc := (Complex.abs_re_le_norm (P z)).trans h
    linarith
  · have h := imaginary_error_from_critical_reality (fun w => F w-P w) (hF.sub hP)
      T (1/100) happrox (fun y _ => hcritical y) z hz
    rw [hzero,zero_sub,neg_im,abs_neg] at h
    have ha : 0 < |z.re-1/2| := abs_pos.mpr (sub_ne_zero.mpr hneq)
    linarith

end CertifiedLocalXi

end Height100Module28

/- Source module: RoundedLocalApproximation. -/
section Height100Module29

open Complex Finset
namespace CertifiedLocalXi

noncomputable def rotatedVariable (T : ℝ) (z : ℂ) : ℂ := -I*(z-center T)
noncomputable def rotatedPolynomial (b : ℕ → ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ range 32, (b n : ℂ)*rotatedVariable T z^n

lemma rotatedVariable_norm (T : ℝ) (z : ℂ) :
    ‖rotatedVariable T z‖=‖z-center T‖ := by
  simp [rotatedVariable]

lemma rotatedVariable_center (T y : ℝ) : rotatedVariable T (center y)=(y-T:ℝ) := by
  apply Complex.ext <;> simp [rotatedVariable,center,mul_re,mul_im]

lemma rotatedPolynomial_entire (b : ℕ → ℝ) (T : ℝ) :
    Differentiable ℂ (rotatedPolynomial b T) := by
  unfold rotatedPolynomial rotatedVariable
  fun_prop

lemma rotatedPolynomial_critical_real (b : ℕ → ℝ) (T y : ℝ) :
    (rotatedPolynomial b T (center y)).im=0 := by
  have he : rotatedPolynomial b T (center y) =
      ((∑ n ∈ range 32, b n*(y-T)^n : ℝ):ℂ) := by
    simp only [rotatedPolynomial,rotatedVariable_center,ofReal_sum,ofReal_mul,ofReal_pow]
  rw [he]
  exact Complex.ofReal_im _

lemma scaled_taylor_rotated (S T : ℝ) (z : ℂ) :
    (S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z=
      ∑ n ∈ range 32,
        ((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n)*
          rotatedVariable T z^n := by
  unfold CertifiedComplexTaylor.polynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have he : I*rotatedVariable T z=z-center T := by
    simp [rotatedVariable,← mul_assoc]
  rw [mul_assoc,← mul_pow,he]
  ring

lemma rounded_polynomial_error (S T : ℝ) (b : ℕ → ℝ)
    (hb : ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)‖
        ≤ 1/10^6)
    (z : ℂ) (hz : ‖z-center T‖≤ 1) :
    ‖(S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z-
      rotatedPolynomial b T z‖≤ 32/10^6 := by
  rw [scaled_taylor_rotated]
  unfold rotatedPolynomial
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤  ∑ n ∈ range 32,
      ‖((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ))*
        rotatedVariable T z^n‖ := by
      simpa only [sub_mul] using
        (norm_sum_le (s:=range 32) (f:=fun n =>
          ((S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n)*
            rotatedVariable T z^n-(b n:ℂ)*rotatedVariable T z^n))
    _ ≤  ∑ _n ∈ range 32, (1/10^6:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul,norm_pow]
      have hp : ‖rotatedVariable T z‖^n≤ 1 := by
        apply pow_le_one₀ (norm_nonneg _)
        simpa only [rotatedVariable_norm] using hz
      calc
        _ ≤  (1/10^6:ℝ)*1 := mul_le_mul (hb n (mem_range.mp hn)) hp
          (by positivity) (by positivity)
        _ = _ := by ring
    _ = _ := by norm_num

lemma rounded_xi_error (S T : ℝ) (hS0 : 0≤ S) (hS1 : S≤ 10^33)
    (hT : |T|≤ 100) (b : ℕ → ℝ)
    (hb : ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)‖
        ≤ 1/10^6)
    (z : ℂ) (hz : ‖z-center T‖≤ 1) :
    ‖(S:ℂ)*xi z-rotatedPolynomial b T z‖≤ 1/100 := by
  have he : (S:ℂ)*xi z-rotatedPolynomial b T z=
      (S:ℂ)*CertifiedComplexTaylor.remainder xi (center T) 32 z+
      ((S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z-
        rotatedPolynomial b T z) := by
    unfold CertifiedComplexTaylor.remainder
    ring
  rw [he]
  calc
    _ ≤  ‖(S:ℂ)*CertifiedComplexTaylor.remainder xi (center T) 32 z‖+
      ‖(S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z-
        rotatedPolynomial b T z‖ := norm_add_le _ _
    _ = S*‖CertifiedComplexTaylor.remainder xi (center T) 32 z‖+
      ‖(S:ℂ)*CertifiedComplexTaylor.polynomial xi (center T) 32 z-
        rotatedPolynomial b T z‖ := by simp [Real.norm_eq_abs,abs_of_nonneg hS0]
    _ ≤  (10^33:ℝ)*(1/10^36)+32/10^6 := by
      exact add_le_add (mul_le_mul hS1 (local_tail_norm T hT z hz)
        (norm_nonneg _) (by positivity)) (rounded_polynomial_error S T b hb z hz)
    _ ≤  _ := by norm_num

lemma xi_nonzero_of_rounded_certificate (S T : ℝ) (hS0 : 0≤ S) (hS1 : S≤ 10^33)
    (hT : |T|≤ 100) (b : ℕ → ℝ)
    (hb : ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)‖
        ≤ 1/10^6)
    (z : ℂ) (hr0 : 0≤ z.re) (hr1 : z.re≤ 1) (hi : |z.im-T|≤ 1/2)
    (hneq : z.re≠1/2)
    (hcertificate : 1≤ |(rotatedPolynomial b T z).re| ∨
      |z.re-1/2|≤ |(rotatedPolynomial b T z).im|) : xi z≠0 := by
  have h := nonzero_of_local_certificate (fun w => (S:ℂ)*xi w)
    (rotatedPolynomial b T) (xi_entire.const_mul _) (rotatedPolynomial_entire b T)
    T (rounded_xi_error S T hS0 hS1 hT b hb) (by
      intro y
      simp [mul_im,xi_critical_real,rotatedPolynomial_critical_real])
    z hr0 hr1 hi hneq hcertificate
  intro hz
  apply h
  simp [hz]

end CertifiedLocalXi

end Height100Module29

/- Source module: LocalSlabAssembly. -/
section Height100Module30

open Complex Finset
namespace CertifiedLocalXi

lemma local_coefficients_from_global (global : ℕ → ℝ)
    (hglobal : ∀ j<256, |CertifiedGlobalMoments.moment j-global j|≤ 1/10^46)
    (S T : ℝ) (hS0 : 0≤ S) (hS1 : S≤ 10^33) (hT : |T|≤ 100)
    (b : ℕ → ℝ)
    (hb : ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient
        (CertifiedGlobalMoments.xiPolynomial global) (center T) n*I^n-(b n:ℂ)‖≤ 1/10^7) :
    ∀ n<32,
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)‖≤ 1/10^6 := by
  intro n hn
  have h := CertifiedGlobalMoments.local_coefficient_error global hglobal T hT n
  have he : (S:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center T) n*I^n-(b n:ℂ)=
      (S:ℂ)*(CertifiedTaylorQuadrature.coefficient xi (center T) n-
        CertifiedTaylorQuadrature.coefficient (CertifiedGlobalMoments.xiPolynomial global)
          (center T) n)*I^n+
      ((S:ℂ)*CertifiedTaylorQuadrature.coefficient
        (CertifiedGlobalMoments.xiPolynomial global) (center T) n*I^n-(b n:ℂ)) := by ring
  rw [he]
  calc
    _ ≤  ‖(S:ℂ)*(CertifiedTaylorQuadrature.coefficient xi (center T) n-
        CertifiedTaylorQuadrature.coefficient (CertifiedGlobalMoments.xiPolynomial global)
          (center T) n)*I^n‖+
      ‖(S:ℂ)*CertifiedTaylorQuadrature.coefficient
        (CertifiedGlobalMoments.xiPolynomial global) (center T) n*I^n-(b n:ℂ)‖ := norm_add_le _ _
    _ ≤  (10^33:ℝ)*(1/10^41)+1/10^7 := by
      apply add_le_add _ (hb n hn)
      simp only [norm_mul,norm_pow,norm_I,one_pow,mul_one,norm_real,Real.norm_eq_abs,
        abs_of_nonneg hS0]
      exact mul_le_mul hS1 h (norm_nonneg _) (by positivity)
    _ ≤  _ := by norm_num

lemma xi_nonzero_implies_zeta {s : ℂ} (h0 : 0< s.re) (h1 : s.re<1)
    (hXi : xi s≠0) : riemannZeta s≠0 := by
  have hs0 : s≠0 := fun h => by simp [h] at h0
  have hs1 : s≠1 := fun h => by simp [h] at h1
  have h1s : (1:ℂ)-s≠0 := sub_ne_zero.mpr hs1.symm
  rw [riemannZeta_def_of_ne_zero hs0]
  intro hz
  rcases div_eq_zero_iff.mp hz with hz | hz
  · apply hXi
    have hh := completedRiemannZeta_eq s
    rw [hz] at hh
    have hsum : completedRiemannZeta₀ s=1/s+1/(1-s) := by linear_combination -hh
    unfold xi
    rw [hsum]
    field_simp
    ring
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 hz

noncomputable def slabCenter (i : Fin 86) : ℝ := 29/2+(i.val:ℝ)

lemma slabCenter_bound (i : Fin 86) : |slabCenter i|≤ 100 := by
  have hi : (i.val:ℝ)≤ 85 := by
    have h : i.val≤ 85 := by omega
    exact_mod_cast h
  have hi0 : (0 : ℝ) ≤  (i.val : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  unfold slabCenter
  constructor <;> linarith

lemma slabs_cover (t : ℝ) (ht0 : 14≤ t) (ht1 : t≤ 100) :
    ∃ i : Fin 86, |t-slabCenter i|≤ 1/2 := by
  by_cases he : t=100
  · refine ⟨⟨85,by norm_num⟩,?_⟩
    norm_num [slabCenter,he]
  · have hlt : t<100 := lt_of_le_of_ne ht1 he
    have hnonneg : 0≤ t-14 := by linarith
    have hi : Nat.floor (t-14)<86 := (Nat.floor_lt hnonneg).mpr (by norm_num; linarith)
    refine ⟨⟨Nat.floor (t-14),hi⟩,?_⟩
    have hlo := Nat.floor_le hnonneg
    have hup := Nat.lt_floor_add_one (t-14)
    rw [abs_le]
    unfold slabCenter
    constructor <;> dsimp <;> linarith

/-- The analytic root assembly. All finite coefficient and nonvanishing certificates
remain explicit hypotheses until they have been checked. -/
lemma rh_block_of_local_certificates
    (S : Fin 86 → ℝ) (b : Fin 86 → ℕ → ℝ)
    (hS0 : ∀ i, 0≤ S i) (hS1 : ∀ i, S i≤ 10^33)
    (hcoeff : ∀ i n, n<32 →
      ‖(S i:ℂ)*CertifiedTaylorQuadrature.coefficient xi (center (slabCenter i)) n*I^n-
        (b i n:ℂ)‖≤ 1/10^6)
    (hcert : ∀ i z, 0≤ z.re → z.re≤ 1 → |z.im-slabCenter i|≤ 1/2 →
      1≤ |(rotatedPolynomial (b i) (slabCenter i) z).re| ∨
      |z.re-1/2|≤ |(rotatedPolynomial (b i) (slabCenter i) z).im|)
    (s : ℂ) (hs : riemannZeta s=0) (h0 : 0< s.re) (h1 : s.re<1)
    (ha : 14≤ s.im) (hb : s.im≤ 10^2) : s.re=1/2 := by
  by_contra hneq
  obtain ⟨i,hi⟩ := slabs_cover s.im ha (by norm_num at hb ⊢; exact hb)
  have hxi := xi_nonzero_of_rounded_certificate (S i) (slabCenter i) (hS0 i) (hS1 i)
    (slabCenter_bound i) (b i) (hcoeff i) s h0.le h1.le hi hneq
    (hcert i s h0.le h1.le hi)
  exact xi_nonzero_implies_zeta h0 h1 hxi hs

lemma rh_block_of_global_certificates
    (global : ℕ → ℝ)
    (hglobal : ∀ j<256, |CertifiedGlobalMoments.moment j-global j|≤ 1/10^46)
    (S : Fin 86 → ℝ) (b : Fin 86 → ℕ → ℝ)
    (hS0 : ∀ i, 0≤ S i) (hS1 : ∀ i, S i≤ 10^33)
    (hcoeff : ∀ i n, n<32 →
      ‖(S i:ℂ)*CertifiedTaylorQuadrature.coefficient
        (CertifiedGlobalMoments.xiPolynomial global) (center (slabCenter i)) n*I^n-
        (b i n:ℂ)‖≤ 1/10^7)
    (hcert : ∀ i z, 0≤ z.re → z.re≤ 1 → |z.im-slabCenter i|≤ 1/2 →
      1≤ |(rotatedPolynomial (b i) (slabCenter i) z).re| ∨
      |z.re-1/2|≤ |(rotatedPolynomial (b i) (slabCenter i) z).im|)
    (s : ℂ) (hs : riemannZeta s=0) (h0 : 0< s.re) (h1 : s.re<1)
    (ha : 14≤ s.im) (hb : s.im≤ 10^2) : s.re=1/2 := by
  apply rh_block_of_local_certificates S b hS0 hS1 _ hcert s hs h0 h1 ha hb
  intro i
  exact local_coefficients_from_global global hglobal (S i) (slabCenter i)
    (hS0 i) (hS1 i) (slabCenter_bound i) (b i) (hcoeff i)

end CertifiedLocalXi

end Height100Module30

/- Source module: PolynomialTranslation. -/
section Height100Module31

open Complex Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature

lemma coefficient_affine (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c a : ℂ) (n : ℕ) :
    coefficient (fun z => f (c+a*z)) 0 n=a^n*coefficient f c n := by
  have hg : Differentiable ℂ (fun z => f (c+z)) := by fun_prop
  unfold coefficient
  rw [iteratedDeriv_comp_const_mul hg.contDiff,iteratedDeriv_comp_const_add]
  simp only [mul_zero,add_zero]
  ring

lemma coefficient_power (m n : ℕ) (c : ℂ) :
    coefficient (fun z : ℂ => z^m) c n=(m.choose n:ℂ)*c^(m-n) := by
  unfold coefficient
  rw [iteratedDeriv_pow,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

noncomputable def powerPolynomial (b : ℕ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ range N, (b m:ℂ)*z^m

noncomputable def translatedCoefficient (b : ℕ → ℝ) (N n : ℕ) (T : ℝ) : ℝ :=
  ∑ m ∈ range N, b m*(m.choose n:ℝ)*T^(m-n)

lemma coefficient_powerPolynomial (b : ℕ → ℝ) (N n : ℕ) (T : ℝ) :
    coefficient (powerPolynomial b N) T n=(translatedCoefficient b N n T:ℂ) := by
  unfold coefficient powerPolynomial translatedCoefficient
  rw [iteratedDeriv_fun_sum (fun m _ => by fun_prop),sum_div]
  simp only [ofReal_sum,ofReal_mul,ofReal_pow,ofReal_natCast]
  apply sum_congr rfl
  intro m hm
  rw [iteratedDeriv_const_mul_field]
  have h := coefficient_power m n (T:ℂ)
  unfold coefficient at h
  rw [mul_div_assoc,h]
  ring

end CertifiedPolynomialTranslation

end Height100Module31


