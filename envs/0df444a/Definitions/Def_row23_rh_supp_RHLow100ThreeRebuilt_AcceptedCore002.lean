-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore002
-- name    : row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore002
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:01:41.718193+00:00
-- url     : https://prove2.me/theorems/7387a978-a399-483d-8103-77ef4fd44e8c
-- title:
--   Row 23 RH support: RHLow100ThreeRebuilt.AcceptedCore002
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore001
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


section Height100Module95

namespace CertifiedLocalPolynomial
open Finset CertifiedLocalXi

end CertifiedLocalPolynomial

end Height100Module95

section Height100Module96

namespace CertifiedIntegerLocalPolynomial
open Finset

end CertifiedIntegerLocalPolynomial

end Height100Module96

section Height100Module97

open Finset
set_option autoImplicit false

namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module97

section Height100Module98

open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module98

section Height100Module99

namespace CertifiedLocalPolynomial
open Finset TaoZetaNumerics

end CertifiedLocalPolynomial

end Height100Module99

section Height100Module100

namespace CertifiedLocalPolynomial
open Finset CertifiedLocalXi

end CertifiedLocalPolynomial

end Height100Module100

section Height100Module101

open Finset
set_option autoImplicit false
set_option maxHeartbeats 0
namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module101

section Height100Module102

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial TaoZetaNumerics
open Finset

end CertifiedLocalBoxes

end Height100Module102

section Height100Module103

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedFastLocalBoxes

end Height100Module103

section Height100Module104

namespace CertifiedStreamingBernstein
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedStreamingBernstein

end Height100Module104

section Height100Module105

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein
open TaoZetaNumerics

end CertifiedStreamingLocalBoxes

end Height100Module105

section Height100Module106

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes
open CertifiedLocalPolynomial CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedFastLocalBoxes

end Height100Module106

section Height100Module107

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedLocalBoxes

end Height100Module107

section Height100Module108

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedFastLocalBoxes

end Height100Module108

section Height100Module109

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein

end CertifiedStreamingLocalBoxes

end Height100Module109

section Height100Module110

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes

end CertifiedStreamingLocalBoxes

end Height100Module110

section Height100Module111

namespace CertifiedStreamingLocalBoxes
open CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedStreamingLocalBoxes

end Height100Module111

section Height100Module112

namespace CertifiedHeight100
open CertifiedPolynomialTranslation CertifiedGlobalMoments CertifiedLocalXi

end CertifiedHeight100

end Height100Module112

section Height100Module113

set_option autoImplicit false
namespace TaoFivePrimes

end TaoFivePrimes

end Height100Module113


noncomputable def TaoFivePrimes_RH14To100MomentInterfaceV2 : Nat := 14

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/- Source module: PackedConvolution. -/
section Height100Module0

open Finset
namespace CertifiedPackedConvolution

noncomputable def coefficient : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x::_, 0 => x
  | _::xs, n+1 => coefficient xs n

noncomputable def addLists : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => (x+y)::addLists xs ys

noncomputable def convolution : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x::xs, ys => addLists (ys.map (x*·)) (0::convolution xs ys)

lemma coefficient_eq_getD (xs : List ℕ) (k : ℕ) : coefficient xs k=xs.getD k 0 := by
  induction xs generalizing k with
  | nil => simp [coefficient,List.getD]
  | cons x xs ih => cases k <;> simp [coefficient,List.getD,ih]

lemma coefficient_add (xs ys : List ℕ) (k : ℕ) :
    coefficient (addLists xs ys) k=coefficient xs k+coefficient ys k := by
  induction xs generalizing ys k with
  | nil => simp [addLists,coefficient]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists,coefficient]
    | cons y ys => cases k <;> simp [addLists,coefficient,ih]

lemma coefficient_map (a : ℕ) (xs : List ℕ) (k : ℕ) :
    coefficient (xs.map (a*·)) k=a*coefficient xs k := by
  induction xs generalizing k with
  | nil => simp [coefficient]
  | cons x xs ih => cases k <;> simp [coefficient,ih]

lemma ofDigits_add (B : ℕ) (xs ys : List ℕ) :
    Nat.ofDigits B (addLists xs ys)=Nat.ofDigits B xs+Nat.ofDigits B ys := by
  induction xs generalizing ys with
  | nil => simp [addLists]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists]
    | cons y ys => simp only [addLists,Nat.ofDigits_cons,ih]; ring

lemma ofDigits_map_mul (B a : ℕ) (xs : List ℕ) :
    Nat.ofDigits B (xs.map (a*·))=a*Nat.ofDigits B xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,Nat.ofDigits_cons,ih]; ring

lemma ofDigits_convolution (B : ℕ) (xs ys : List ℕ) :
    Nat.ofDigits B (convolution xs ys)=Nat.ofDigits B xs*Nat.ofDigits B ys := by
  induction xs with
  | nil => simp [convolution]
  | cons x xs ih =>
    rw [convolution,ofDigits_add,ofDigits_map_mul,Nat.ofDigits_cons,ih,Nat.ofDigits_cons]
    ring

lemma sum_convolution (xs ys : List ℕ) : (convolution xs ys).sum=xs.sum*ys.sum := by
  simpa only [Nat.ofDigits_one] using ofDigits_convolution 1 xs ys

lemma coefficient_convolution (xs ys : List ℕ) (k : ℕ) :
    coefficient (convolution xs ys) k=
      ∑ i ∈ range (k+1), coefficient xs i*coefficient ys (k-i) := by
  induction xs generalizing k with
  | nil => simp [convolution,coefficient]
  | cons x xs ih =>
    cases k with
    | zero => simp [convolution,coefficient_add,coefficient_map,coefficient]
    | succ k =>
      rw [convolution,coefficient_add,coefficient_map,coefficient,ih]
      conv_rhs => rw [sum_range_succ']
      simp only [coefficient,Nat.add_sub_add_right,Nat.sub_zero]
      rw [add_comm]

lemma member_le_sum (xs : List ℕ) (x : ℕ) (hx : x∈xs) : x≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · simp
    · have h := ih hx
      simp only [List.sum_cons]
      omega

lemma digit_ofDigits (B : ℕ) (hB : 0< B) (xs : List ℕ)
    (hsmall : ∀ x∈xs,x< B) (k : ℕ) :
    (Nat.ofDigits B xs/B^k)%B=coefficient xs k := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [coefficient]
    | cons x xs =>
      have hx := hsmall x List.mem_cons_self
      simp [Nat.ofDigits_cons,coefficient,Nat.add_mod,Nat.mod_eq_of_lt hx]
  | succ k ih =>
    rw [Nat.pow_succ',← Nat.div_div_eq_div_mul,
      Nat.ofDigits_div_eq_ofDigits_tail hB xs hsmall]
    rw [ih xs.tail (fun x hx => hsmall x (List.mem_of_mem_tail hx))]
    cases xs <;> simp [coefficient]

/-- One scalar no-carry check suffices for every convolution digit. -/
theorem packed_product_digit (B : ℕ) (hB : 0< B) (xs ys : List ℕ)
    (hcarry : xs.sum*ys.sum< B) (k : ℕ) :
    ((Nat.ofDigits B xs*Nat.ofDigits B ys)/B^k)%B =
      ∑ i ∈ range (k+1), xs.getD i 0*ys.getD (k-i) 0 := by
  rw [← ofDigits_convolution]
  have hs : ∀ x∈convolution xs ys,x< B := by
    intro x hx
    have h := member_le_sum (convolution xs ys) x hx
    rw [sum_convolution] at h
    exact h.trans_lt hcarry
  rw [digit_ofDigits B hB _ hs,coefficient_convolution]
  simp_rw [coefficient_eq_getD]

lemma encode_eq_ofDigits (bits : ℕ) (xs : List ℕ) :
    encode bits xs=Nat.ofDigits (2^bits) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [encode,Nat.ofDigits_cons,Nat.shiftLeft_eq',Nat.shiftLeft_eq,ih]; ring

/-- Binary-stride encoding has the same verified digit-extraction rule. -/
theorem shift_product_digit (bits : ℕ) (xs ys : List ℕ)
    (hcarry : xs.sum*ys.sum<2^bits) (k : ℕ) :
    ((encode bits xs*encode bits ys)/(2^bits)^k)%(2^bits) =
      ∑ i ∈ range (k+1), xs.getD i 0*ys.getD (k-i) 0 := by
  rw [encode_eq_ofDigits,encode_eq_ofDigits]
  exact packed_product_digit _ (by positivity) xs ys hcarry k

/-- Direct bit-shift extraction avoids constructing a large divisor in executable checks. -/
theorem shiftRight_product_digit (bits : ℕ) (xs ys : List ℕ)
    (hcarry : xs.sum*ys.sum<2^bits) (k : ℕ) :
    ((encode bits xs*encode bits ys) >>> (bits*k))%(2^bits) =
      ∑ i ∈ range (k+1), xs.getD i 0*ys.getD (k-i) 0 := by
  rw [Nat.shiftRight_eq_div_pow,pow_mul]
  exact shift_product_digit bits xs ys hcarry k

end CertifiedPackedConvolution

end Height100Module0

/- Source module: ScalarPanelIdentity. -/
section Height100Module1

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution

lemma sum_triangle {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → ℕ → R) :
    (∑ j ∈ range N, ∑ m ∈ range (j+1), f m (j-m)) =
      ∑ m ∈ range N, ∑ l ∈ range (N-m), f m l := by
  classical
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun x _ => ⟨x.2, x.1-x.2⟩)
  · intro x hx
    simp only [mem_sigma, mem_range] at hx ⊢
    omega
  · intro x hx y hy hxy
    simp only [mem_sigma, mem_range] at hx hy
    have h1 := congrArg Sigma.fst hxy
    have h2 := congrArg (fun z : Sigma (fun _ : ℕ => ℕ) => z.2) hxy
    apply Sigma.ext <;> simp_all
    omega
  · intro y hy
    simp only [mem_sigma, mem_range] at hy
    refine ⟨⟨y.1+y.2, y.1⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · simp
  · intro x hx
    rfl

/-- A truncated convolution can be integrated by first correlating the base
coefficients with the integration weights. -/
theorem integrated_convolution {R : Type*} [CommSemiring R]
    (N : ℕ) (a h w : ℕ → R) :
    (∑ j ∈ range N, (∑ m ∈ range (j+1), a m * h (j-m)) * w j) =
      ∑ m ∈ range N, a m * (∑ l ∈ range (N-m), h l * w (m+l)) := by
  simp_rw [sum_mul]
  calc
    (∑ j ∈ range N, ∑ m ∈ range (j+1), a m * h (j-m) * w j) =
        ∑ j ∈ range N, ∑ m ∈ range (j+1), a m * h (j-m) * w (m+(j-m)) := by
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro m hm
      congr 2
      have hmj : m≤ j := by simpa using mem_range.mp hm
      omega
    _ = ∑ m ∈ range N, ∑ l ∈ range (N-m), a m * h l * w (m+l) :=
      sum_triangle N (fun m l => a m * h l * w (m+l))
    _ = _ := by simp_rw [mul_sum, mul_assoc]

/-- The common base correlation is independent of the moment order. -/
noncomputable def correlation {R : Type*} [Semiring R] (N : ℕ) (h w : ℕ → R) (m : ℕ) : R :=
  ∑ l ∈ range (N-m), h l * w (m+l)

end CertifiedMomentConvolution

end Height100Module1

/- Source module: TaylorQuadrature. -/
section Height100Module2

open Complex MeasureTheory Finset Metric Set

namespace CertifiedTaylorQuadrature

noncomputable def coefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c / (n.factorial:ℂ)

noncomputable def polynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n * (x:ℂ)^n

noncomputable def panel (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n *
    (((h:ℂ)^(n+1)-(-h:ℂ)^(n+1))/(n+1))

lemma coefficient_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M : ℝ) (hR : 0< R) (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (n : ℕ) :
    ‖coefficient f c n‖ ≤  M/R^n := by
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    hf.diffContOnCl hb
  rw [coefficient, norm_div, Complex.norm_natCast]
  have hn : (0:ℝ)< n.factorial := by positivity
  apply (div_le_iff₀ hn).mpr
  calc
    ‖iteratedDeriv n f c‖ ≤  n.factorial*M/R^n := hd
    _ = M/R^n*n.factorial := by ring

lemma series_sum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (x : ℝ) :
    HasSum (fun n : ℕ => coefficient f c n*(x:ℂ)^n) (f (c+x)) := by
  have h := Complex.hasSum_taylorSeries_of_entire hf c (c+x)
  convert! h using 1
  ext n
  simp only [coefficient, add_sub_cancel_left, smul_eq_mul]
  ring

lemma point_error (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M h : ℝ) (hR : 0< R) (hM : 0≤ M) (hh : 0≤ h) (hhR : h< R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (N : ℕ) (x : ℝ) (hx : |x|≤ h) :
    ‖f (c+x)-polynomial f c N x‖ ≤  M*(h/R)^N/(1-h/R) := by
  have hq0 : 0≤ h/R := div_nonneg hh hR.le
  have hq1 : h/R<1 := (div_lt_one hR).mpr hhR
  have hs := series_sum f hf c x
  have he : f (c+x)-polynomial f c N x =
      ∑' n : ℕ, coefficient f c (n+N)*(x:ℂ)^(n+N) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    unfold polynomial
    apply sub_eq_iff_eq_add.mpr
    simpa [add_comm] using h.symm
  rw [he]
  have hgeo : HasSum (fun n : ℕ => (M*(h/R)^N)*(h/R)^n)
      ((M*(h/R)^N)*(1-h/R)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M*(h/R)^N)
  have hterms : ∀ n : ℕ, ‖coefficient f c (n+N)*(x:ℂ)^(n+N)‖ ≤  (M*(h/R)^N)*(h/R)^n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖coefficient f c (n+N)‖*|x|^(n+N) ≤  (M/R^(n+N))*h^(n+N) := by
        gcongr
        exact coefficient_bound f hf c R M hR hb (n+N)
      _ = (M*(h/R)^N)*(h/R)^n := by rw [div_pow, div_pow, pow_add, pow_add]; ring
  have ht := tsum_of_norm_bounded hgeo hterms
  simpa only [div_eq_mul_inv] using ht

lemma polynomial_integrable (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (polynomial f c N) volume a b := by
  apply Continuous.intervalIntegrable
  unfold polynomial
  fun_prop

lemma integral_polynomial (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) :
    (∫ x in -h..h, polynomial f c N x) = panel f c h N := by
  unfold polynomial panel
  rw [intervalIntegral.integral_finsetSum (fun n _ => (by
    apply Continuous.intervalIntegrable
    fun_prop))]
  apply sum_congr rfl
  intro n _
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [show (fun x : ℝ => (x:ℂ)^n) = (fun x : ℝ => ((x^n:ℝ):ℂ)) by ext x; push_cast; rfl,
    intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  rfl

/-- A complex analytic function can be integrated by a finite Taylor polynomial with a
geometric, arbitrarily high-order error bound. Every coefficient remains exact. -/
theorem panel_error (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M h : ℝ) (hR : 0< R) (hM : 0≤ M) (hh : 0≤ h) (hhR : h< R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (N : ℕ) :
    ‖(∫ x in -h..h, f (c+x))-panel f c h N‖ ≤ 
      2*h*M*(h/R)^N/(1-h/R) := by
  rw [← integral_polynomial]
  have hfint : IntervalIntegrable (fun x : ℝ => f (c+x)) volume (-h) h :=
    (hf.continuous.comp (by fun_prop)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hfint (polynomial_integrable f c N (-h) h)]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a:=-h) (b:=h)
    (f:=fun x : ℝ => f (c+x)-polynomial f c N x) (C:=M*(h/R)^N/(1-h/R)) (by
      intro x hx
      rw [uIoc_of_le (by linarith : -h≤ h)] at hx
      exact point_error f hf c R M h hR hM hh hhR hb N x
        (abs_le.mpr ⟨hx.1.le,hx.2⟩))
  have ha : |h-(-h)|=2*h := by rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]; ring
  rw [ha] at he
  convert he using 1
  ring

end CertifiedTaylorQuadrature

end Height100Module2

/- Source module: MomentJetIdentity. -/
section Height100Module3

set_option autoImplicit false
open Complex Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

lemma coefficient_mul (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (c : ℂ) (n : ℕ) :
    coefficient (fun z => f z * g z) c n =
      ∑ m ∈ range (n+1), coefficient f c m * coefficient g c (n-m) := by
  unfold coefficient
  rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hg.contDiff.contDiffAt, sum_div]
  apply sum_congr rfl
  intro m hm
  have hmn : m≤ n := by simpa using mem_range.mp hm
  rw [Nat.cast_choose ℂ hmn]
  have h0 : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  have h1 : (m.factorial:ℂ)≠0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((n-m).factorial:ℂ)≠0 := by exact_mod_cast (n-m).factorial_ne_zero
  field_simp

lemma power_moment_coefficient (a c : ℂ) (k m : ℕ) :
    coefficient (fun z => (a*z)^k / (k.factorial:ℂ)) c m =
      if m≤ k then a^k*c^(k-m)/(((k-m).factorial:ℂ)*m.factorial) else 0 := by
  have he : (fun z : ℂ => (a*z)^k/(k.factorial:ℂ)) =
      (fun z => (a^k/(k.factorial:ℂ))*z^k) := by ext z; simp [mul_pow]; ring
  rw [he, coefficient, iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  by_cases hmk : m≤ k
  · rw [if_pos hmk]
    have hf : ((k-m).factorial:ℂ)*(k.descFactorial m:ℂ) = k.factorial := by
      exact_mod_cast Nat.factorial_mul_descFactorial hmk
    have h0 : (k.factorial:ℂ)≠0 := by exact_mod_cast k.factorial_ne_zero
    have h1 : (m.factorial:ℂ)≠0 := by exact_mod_cast m.factorial_ne_zero
    have h2 : ((k-m).factorial:ℂ)≠0 := by exact_mod_cast (k-m).factorial_ne_zero
    field_simp
    linear_combination (a^k*c^(k-m))*hf
  · rw [if_neg hmk, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

noncomputable def scaledCoefficient (f : ℂ → ℂ) (c h : ℂ) (n : ℕ) : ℂ :=
  coefficient f c n * h^n

lemma scaled_power_moment_coefficient (a c h : ℂ) (k m : ℕ) :
    scaledCoefficient (fun z => (a*z)^k / (k.factorial:ℂ)) c h m =
      if m≤ k then (a*c)^(k-m)*(a*h)^m/(((k-m).factorial:ℂ)*m.factorial) else 0 := by
  rw [scaledCoefficient, power_moment_coefficient]
  by_cases hmk : m≤ k
  · rw [if_pos hmk, if_pos hmk]
    have hk : k = (k-m)+m := by omega
    conv_lhs => rw [hk]
    simp only [Nat.add_sub_cancel_right, pow_add, mul_pow]
    ring
  · simp [hmk]

lemma scaled_coefficient_mul (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (c h : ℂ) (n : ℕ) :
    scaledCoefficient (fun z => f z * g z) c h n =
      ∑ m ∈ range (n+1), scaledCoefficient f c h m * scaledCoefficient g c h (n-m) := by
  unfold scaledCoefficient
  rw [coefficient_mul f g hf hg, sum_mul]
  apply sum_congr rfl
  intro m hm
  have hmn : m≤ n := by simpa using mem_range.mp hm
  have hn : n=m+(n-m) := by omega
  conv_lhs => rw [hn]
  simp only [Nat.add_sub_cancel_left, pow_add]
  ring

noncomputable def integrationWeight (j : ℕ) : ℂ :=
  (1 - (-1:ℂ)^(j+1)) / (j+1)

lemma panel_eq_scaled (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) :
    panel f c h N = (h:ℂ) *
      ∑ j ∈ range N, scaledCoefficient f c h j * integrationWeight j := by
  unfold panel
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  unfold scaledCoefficient integrationWeight
  rw [show (-h:ℂ) = (-1:ℂ)*(h:ℂ) by ring, mul_pow, pow_succ]
  ring

lemma sum_restrict_swap {R : Type*} [AddCommMonoid R] (N k : ℕ) (f : ℕ → R) :
    (∑ m ∈ range N, if m≤ k then f m else 0) =
      ∑ m ∈ range (k+1), if m< N then f m else 0 := by
  classical
  rw [← sum_filter, ← sum_filter]
  congr 1
  ext m
  simp only [mem_filter, mem_range]
  omega

/-- All panel moments are a scalar convolution of a common correlation vector
and the exponential coefficients of the center. -/
theorem power_moment_panel (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a c : ℂ) (h : ℝ) (N k : ℕ) :
    panel (fun z => (a*z)^k / (k.factorial:ℂ) * f z) c h N =
      (h:ℂ) * ∑ m ∈ range (k+1),
        (if m< N then
          (a*(h:ℂ))^m/(m.factorial:ℂ) *
            correlation N (scaledCoefficient f c h) integrationWeight m
          else 0) * ((a*c)^(k-m)/((k-m).factorial:ℂ)) := by
  rw [panel_eq_scaled]
  congr 1
  have hp : Differentiable ℂ (fun z : ℂ => (a*z)^k / (k.factorial:ℂ)) := by fun_prop
  simp_rw [scaled_coefficient_mul _ _ hp hf,
    scaled_power_moment_coefficient]
  rw [integrated_convolution]
  simp only [correlation]
  simp_rw [ite_mul, zero_mul]
  rw [sum_restrict_swap]
  apply sum_congr rfl
  intro m hm
  by_cases hmn : m< N
  · simp only [if_pos hmn]
    ring
  · simp [hmn]

end CertifiedMomentConvolution

end Height100Module3


