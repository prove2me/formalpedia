-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore007
-- name    : row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore007
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:15:36.021912+00:00
-- url     : https://prove2.me/theorems/06e08f2e-1e70-4c2c-a8a4-756f6ed31415
-- title:
--   Row 23 RH support: RHLow100ThreeRebuilt.AcceptedCore007
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore006
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


/- Source module: GlobalPolynomialTranslation. -/
section Height100Module32

open Complex Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature CertifiedGlobalMoments

noncomputable def criticalMomentCoefficient (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  b j*(-1)^j/(128:ℝ)^(2*j)

noncomputable def criticalXiPolynomial (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  1/2-∑ j ∈ range 256, (criticalMomentCoefficient b j:ℂ)*(z^(2*j+2)/2+z^(2*j)/8)

lemma scaledVariable_critical (z : ℂ) : scaledVariable (1/2+I*z)=I*(z/128) := by
  unfold scaledVariable
  ring

lemma even_I_power (j : ℕ) : I^(2*j)=(-1:ℂ)^j := by rw [pow_mul,I_sq]

lemma global_critical_identity (b : ℕ → ℝ) (z : ℂ) :
    xiPolynomial b (1/2+I*z)=criticalXiPolynomial b z := by
  have hf : (1/2+I*z)*(1/2+I*z-1)/2=-(z^2/2+1/8) := by
    ring_nf
    rw [I_sq]
    ring
  unfold xiPolynomial criticalXiPolynomial CertifiedGlobalMoments.polynomial
  rw [hf,mul_sum,sub_eq_add_neg,←sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [scaledVariable_critical,mul_pow,even_I_power,div_pow]
  unfold criticalMomentCoefficient
  push_cast
  rw [pow_add]
  ring

lemma coefficient_const (a c : ℂ) (n : ℕ) :
    coefficient (fun _ : ℂ => a) c n=if n=0 then a else 0 := by
  unfold coefficient
  rw [iteratedDeriv_const]
  by_cases hn : n=0 <;> simp [hn]

noncomputable def localGlobalCoefficient (b : ℕ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  (if n=0 then 1/2 else 0)-∑ j ∈ range 256, criticalMomentCoefficient b j*
    ((Nat.choose (2*j+2) n:ℝ)*T^(2*j+2-n)/2+(Nat.choose (2*j) n:ℝ)*T^(2*j-n)/8)

lemma coefficient_criticalXi (b : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    coefficient (criticalXiPolynomial b) T n=(localGlobalCoefficient b T n:ℂ) := by
  have hf : ∀ j : ℕ, Differentiable ℂ (fun z : ℂ =>
      (criticalMomentCoefficient b j:ℂ)*(z^(2*j+2)/2+z^(2*j)/8)) := by intro j; fun_prop
  unfold criticalXiPolynomial coefficient
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),sub_div,
    iteratedDeriv_fun_sum (fun j _ => (hf j).contDiff.contDiffAt),sum_div]
  change coefficient (fun _ : ℂ => 1/2) T n-
    (∑ j ∈ range 256,
      coefficient (fun z : ℂ => (criticalMomentCoefficient b j:ℂ)*
        (z^(2*j+2)/2+z^(2*j)/8)) T n)=(localGlobalCoefficient b T n:ℂ)
  rw [coefficient_const]
  unfold localGlobalCoefficient
  push_cast
  apply congrArg₂ (· - ·)
  · split_ifs <;> norm_num
  · apply sum_congr rfl
    intro j hj
    unfold coefficient
    rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_div_const,iteratedDeriv_div_const]
    have h0 := coefficient_power (2*j+2) n (T:ℂ)
    have h1 := coefficient_power (2*j) n (T:ℂ)
    unfold coefficient at h0 h1
    calc
      _ = (criticalMomentCoefficient b j:ℂ)*
        ((iteratedDeriv n (fun z : ℂ => z^(2*j+2)) T/(n.factorial:ℂ))/2+
          (iteratedDeriv n (fun z : ℂ => z^(2*j)) T/(n.factorial:ℂ))/8) := by ring
      _ = _ := by rw [h0,h1]

lemma global_rotated_coefficient (b : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    coefficient (xiPolynomial b) (CertifiedLocalXi.center T) n*I^n=
      (localGlobalCoefficient b T n:ℂ) := by
  have he : (fun z : ℂ => xiPolynomial b (CertifiedLocalXi.center T+I*z))=
      (fun z : ℂ => criticalXiPolynomial b ((T:ℂ)+z)) := by
    funext z
    rw [←global_critical_identity]
    congr 1
    unfold CertifiedLocalXi.center
    ring
  have hh := congrArg (fun F : ℂ → ℂ => coefficient F 0 n) he
  rw [coefficient_affine _ (xiPolynomial_entire b)] at hh
  unfold coefficient at hh
  rw [iteratedDeriv_comp_const_add] at hh
  simp only [add_zero] at hh
  change I^n*coefficient (xiPolynomial b) (CertifiedLocalXi.center T) n=
    coefficient (criticalXiPolynomial b) T n at hh
  rw [coefficient_criticalXi] at hh
  simpa only [mul_comm] using hh

lemma global_rotated_error (global : ℕ → ℝ) (S T v ε : ℝ) (n : ℕ)
    (h : |S*localGlobalCoefficient global T n-v|≤ ε) :
    ‖(S:ℂ)*coefficient (xiPolynomial global) (CertifiedLocalXi.center T) n*I^n-(v:ℂ)‖≤ ε := by
  rw [mul_assoc,global_rotated_coefficient,←ofReal_mul,←ofReal_sub,norm_real,Real.norm_eq_abs]
  exact h

lemma rh_block_of_real_translation_certificates
    (global : ℕ → ℝ)
    (hglobal : ∀ j<256, |moment j-global j|≤ 1/10^46)
    (S : Fin 86 → ℝ) (b : Fin 86 → ℕ → ℝ)
    (hS0 : ∀ i, 0≤ S i) (hS1 : ∀ i, S i≤ 10^33)
    (hcoeff : ∀ i n, n<32 →
      |S i*localGlobalCoefficient global (CertifiedLocalXi.slabCenter i) n-b i n|≤ 1/10^7)
    (hcert : ∀ i z, 0≤ z.re → z.re≤ 1 → |z.im-CertifiedLocalXi.slabCenter i|≤ 1/2 →
      1≤ |(CertifiedLocalXi.rotatedPolynomial (b i) (CertifiedLocalXi.slabCenter i) z).re| ∨
      |z.re-1/2|≤ |(CertifiedLocalXi.rotatedPolynomial (b i) (CertifiedLocalXi.slabCenter i) z).im|)
    (s : ℂ) (hs : riemannZeta s=0) (h0 : 0< s.re) (h1 : s.re<1)
    (ha : 14≤ s.im) (hb : s.im≤ 10^2) : s.re=1/2 := by
  apply CertifiedLocalXi.rh_block_of_global_certificates global hglobal S b hS0 hS1 _
    hcert s hs h0 h1 ha hb
  intro i n hn
  exact global_rotated_error global (S i) (CertifiedLocalXi.slabCenter i) (b i n)
    (1/10^7) n (hcoeff i n hn)

end CertifiedPolynomialTranslation

end Height100Module32

/- Source module: DenseGlobalPolynomial. -/
section Height100Module33

set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

namespace CertifiedDenseGlobalPolynomial
open Complex Finset CertifiedPolynomialTranslation

noncomputable def halfDenominator : ℕ := 4*momentScale*128^510

noncomputable def scaledMoment (C : ℕ → ℤ) (j : ℕ) : ℤ :=
  if j<256 then (-1)^j*C j*(128:ℤ)^(510-2*j) else 0

noncomputable def evenCoefficient (C : ℕ → ℤ) (j : ℕ) : ℤ :=
  (if j=0 then (halfDenominator:ℤ) else 0)-scaledMoment C j-
    (if j=0 then 0 else 4*scaledMoment C (j-1))

noncomputable def coefficient (C : ℕ → ℤ) (m : ℕ) : ℤ :=
  if m%2=0 then evenCoefficient C (m/2) else 0

noncomputable def moments (C : ℕ → ℤ) (j : ℕ) : ℝ := (C j:ℝ)/momentScale
noncomputable def denseCoefficients (C : ℕ → ℤ) (m : ℕ) : ℝ :=
  (coefficient C m:ℝ)/denominator

lemma denominator_pos : 0< denominator := by unfold denominator momentScale; positivity
lemma denominator_half : denominator=2*halfDenominator := by
  unfold denominator halfDenominator
  ring

lemma scaled_moment_identity (C : ℕ → ℤ) (j : ℕ) (hj : j<256) :
    (denominator:ℂ)*(criticalMomentCoefficient (moments C) j:ℂ)=8*(scaledMoment C j:ℂ) := by
  have hj2 : 2*j≤ 510 := by omega
  have hp : (128:ℂ)^510=(128:ℂ)^(2*j)*(128:ℂ)^(510-2*j) := by
    rw [←pow_add,Nat.add_sub_of_le hj2]
  unfold denominator criticalMomentCoefficient moments scaledMoment
  rw [if_pos hj]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Complex.ofReal_div,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_intCast,Complex.ofReal_natCast,
    Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat,Int.cast_mul,Int.cast_pow,
    Int.cast_neg,Int.cast_one,Int.cast_ofNat]
  rw [hp]
  have hs : (momentScale:ℂ)≠0 := by
    exact_mod_cast (by unfold momentScale; positivity : momentScale≠0)
  field_simp

lemma integer_polynomial_identity (C : ℕ → ℤ) (z : ℂ) :
    (∑ m ∈ range 513, (coefficient C m:ℂ)*z^m)=
      (denominator:ℂ)*criticalXiPolynomial (moments C) z := by
  have he : ∀ j,
      (evenCoefficient C j:ℂ)=
        (if j=0 then (halfDenominator:ℂ) else 0)-(scaledMoment C j:ℂ)-
          (if j=0 then 0 else 4*(scaledMoment C (j-1):ℂ)) := by
    intro j
    unfold evenCoefficient
    by_cases hj : j=0
    · simp only [if_pos hj,Int.cast_sub,Int.cast_zero,Int.cast_natCast]
    · simp only [if_neg hj,Int.cast_sub,Int.cast_zero,Int.cast_mul,Int.cast_ofNat]
  have hc : ∀ m, (coefficient C m:ℂ)=if m%2=0 then (evenCoefficient C (m/2):ℂ) else 0 := by
    intro m
    unfold coefficient
    split_ifs <;> simp only [Int.cast_zero]
  simp_rw [hc]
  rw [show 513=2*256+1 by norm_num,
    CertifiedEvenPolynomial.dense_even_eval (fun j => (evenCoefficient C j:ℂ)) 256 z]
  simp_rw [he]
  rw [CertifiedEvenPolynomial.recurrence_eval _ _ 256 (by simp [scaledMoment])]
  unfold criticalXiPolynomial
  rw [mul_sub,mul_sum]
  have hh : (halfDenominator:ℂ)=(denominator:ℂ)*(1/2) := by
    rw [denominator_half]
    push_cast
    ring
  rw [hh]
  congr 1
  apply sum_congr rfl
  intro j hj
  have h := scaled_moment_identity C j (mem_range.mp hj)
  calc
    _ = (8*(scaledMoment C j:ℂ))*(z^(2*j+2)/2+z^(2*j)/8) := by ring
    _ = _ := by rw [←h]; ring

end CertifiedDenseGlobalPolynomial

end Height100Module33

/- Source module: FixedPointIntervals. -/
section Height100Module34

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedFixedPoint

noncomputable def Contains (S : ℕ) (b : Box) (x : ℝ) : Prop :=
  (b.lo:ℝ)/S ≤  x ∧ x ≤  (b.hi:ℝ)/S

noncomputable def oneBox (S : ℕ) : Box := ⟨S,S⟩
noncomputable def addBox (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩

lemma contains_nonneg {S : ℕ} {b : Box} {x : ℝ} (h : Contains S b x) : 0≤ x :=
  (by positivity : (0:ℝ)≤ b.lo/S).trans h.1

lemma quotient_bounds (m n : ℕ) (hn : 0< n) :
    ((m/n:ℕ):ℝ) ≤  (m:ℝ)/n ∧ (m:ℝ)/n ≤  ((m/n+1:ℕ):ℝ) := by
  refine ⟨Nat.cast_div_le, ?_⟩
  apply (div_le_iff₀ (by exact_mod_cast hn : (0:ℝ)< n)).mpr
  have h := (Nat.lt_mul_div_succ m hn).le
  exact_mod_cast (by simpa [Nat.mul_comm] using h)

lemma oneBox_sound {S : ℕ} (hS : 0< S) : Contains S (oneBox S) 1 := by
  have h : (S:ℝ)≠0 := by exact_mod_cast hS.ne'
  simp [Contains,oneBox,h]

lemma addBox_sound {S : ℕ} {a b : Box} {x y : ℝ}
    (ha : Contains S a x) (hb : Contains S b y) : Contains S (addBox a b) (x+y) := by
  constructor <;> dsimp [Contains,addBox] at *
  · push_cast
    rw [add_div]
    linarith [ha.1,hb.1]
  · push_cast
    rw [add_div]
    linarith [ha.2,hb.2]

lemma mulDivBox_sound {S d : ℕ} (hS : 0< S) (hd : 0< d)
    {a b : Box} {x y : ℝ} (ha : Contains S a x) (hb : Contains S b y) :
    Contains S (mulDivBox S d a b) (x*y/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  have hx := contains_nonneg ha
  have hy := contains_nonneg hb
  have hlo := (quotient_bounds (a.lo*b.lo) (S*d) (Nat.mul_pos hS hd)).1
  have hhi := (quotient_bounds (a.hi*b.hi) (S*d) (Nat.mul_pos hS hd)).2
  simp only [Nat.cast_mul] at hlo hhi
  constructor
  · calc
      _ ≤  (((a.lo:ℝ)*b.lo)/(S*d))/S := div_le_div_of_nonneg_right hlo hSr.le
      _ = ((a.lo:ℝ)/S*((b.lo:ℝ)/S))/d := by ring
      _ ≤  _ := by gcongr; exact ha.1; exact hb.1
  · calc
      _ ≤  ((a.hi:ℝ)/S*((b.hi:ℝ)/S))/d := by gcongr; exact ha.2; exact hb.2
      _ = (((a.hi:ℝ)*b.hi)/(S*d))/S := by ring
      _ ≤  _ := div_le_div_of_nonneg_right hhi hSr.le

/-- Fixed-point term recurrence, retaining both the current Taylor term and sum. -/
noncomputable def expTaylorRun (S : ℕ) (a : Box) : ℕ → Box × Box
  | 0 => (oneBox S,oneBox S)
  | n+1 =>
    let prev := expTaylorRun S a n
    let next := mulDivBox S (n+1) prev.1 a
    (next, addBox prev.2 next)

lemma expTaylorRun_sound {S : ℕ} (hS : 0< S) {a : Box} {x : ℝ}
    (ha : Contains S a x) (n : ℕ) :
    Contains S (expTaylorRun S a n).1 (x^n/(n.factorial:ℝ)) ∧
    Contains S (expTaylorRun S a n).2 (∑ k ∈ range (n+1),x^k/(k.factorial:ℝ)) := by
  induction n with
  | zero => simpa [expTaylorRun] using And.intro (oneBox_sound hS) (oneBox_sound hS)
  | succ n ih =>
    have ht := mulDivBox_sound hS (Nat.succ_pos n) ih.1 ha
    have he : (x^n/(n.factorial:ℝ))*x/((n+1:ℕ):ℝ) = x^(n+1)/((n+1).factorial:ℝ) := by
      rw [Nat.factorial_succ,pow_succ]
      push_cast
      field_simp
    rw [he] at ht
    refine ⟨ht, ?_⟩
    have hs := addBox_sound ih.2 ht
    simpa only [expTaylorRun,sum_range_succ] using hs

noncomputable def expBox (S : ℕ) (a : Box) (N : ℕ) : Box :=
  let b := (expTaylorRun S a N).2
  ⟨b.lo,b.hi+1⟩

lemma expBox_sound {S : ℕ} (hS : 0< S) {a : Box} {x : ℝ}
    (ha : Contains S a x) (hx1 : x≤ 1) (N : ℕ)
    (htail : ((N+2:ℕ):ℝ)/((N+1).factorial*(N+1)) ≤  1/(S:ℝ)) :
    Contains S (expBox S a N) (Real.exp x) := by
  have hx0 := contains_nonneg ha
  have hx : |x|≤ 1 := by rwa [abs_of_nonneg hx0]
  have hsum := (expTaylorRun_sound hS ha N).2
  have hl := Real.sum_le_exp_of_nonneg hx0 (N+1)
  have he := Real.exp_bound hx (Nat.succ_pos N)
  have hp : |x|^(N+1)≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hr : Real.exp x-(∑ k ∈ range (N+1),x^k/(k.factorial:ℝ))≤ 1/(S:ℝ) := by
    calc
      _ ≤  |Real.exp x-(∑ k ∈ range (N+1),x^k/(k.factorial:ℝ))| := le_abs_self _
      _ ≤  _ := he
      _ ≤  ((N+2:ℕ):ℝ)/((N+1).factorial*(N+1)) := by
        have hh := mul_le_of_le_one_left
          (by positivity : (0:ℝ)≤ ((N+2:ℕ):ℝ)/((N+1).factorial*(N+1))) hp
        simpa only [Nat.cast_succ,Nat.cast_add,Nat.cast_ofNat] using hh
      _ ≤  _ := htail
  constructor
  · exact hsum.1.trans hl
  · dsimp [expBox]
    push_cast
    rw [add_div]
    linarith [hsum.2]

noncomputable def inverseBox (S : ℕ) (a : Box) : Box :=
  ⟨S*S/a.hi,S*S/a.lo+1⟩

lemma inverseBox_sound {S : ℕ} (hS : 0< S) {a : Box} {x : ℝ}
    (ha : Contains S a x) (hl : 0< a.lo) : Contains S (inverseBox S a) (1/x) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hlr : (0:ℝ)< a.lo := by exact_mod_cast hl
  have hx : 0< x := (div_pos hlr hSr).trans_le ha.1
  have hh : 0< a.hi := by
    by_contra hh
    have hz : a.hi=0 := by omega
    have hhx := ha.2
    simp only [hz,Nat.cast_zero,zero_div] at hhx
    linarith
  have hhr : (0:ℝ)< a.hi := by exact_mod_cast hh
  have hlo := (quotient_bounds (S*S) a.hi hh).1
  have hhi := (quotient_bounds (S*S) a.lo hl).2
  simp only [Nat.cast_mul] at hlo hhi
  constructor
  · calc
      _ ≤  ((S:ℝ)*S/a.hi)/S := div_le_div_of_nonneg_right hlo hSr.le
      _ = 1/((a.hi:ℝ)/S) := by field_simp
      _ ≤  _ := one_div_le_one_div_of_le hx ha.2
  · calc
      _ ≤  1/((a.lo:ℝ)/S) := one_div_le_one_div_of_le (div_pos hlr hSr) ha.1
      _ = ((S:ℝ)*S/a.lo)/S := by field_simp
      _ ≤  _ := div_le_div_of_nonneg_right hhi hSr.le

lemma repeatedSquare_sound {S : ℕ} (hS : 0< S) (n : ℕ) {a : Box} {x : ℝ}
    (ha : Contains S a x) : Contains S (repeatedSquare S n a) (x^(2^n)) := by
  induction n generalizing a x with
  | zero => simpa [repeatedSquare] using ha
  | succ n ih =>
    have hs : Contains S (mulDivBox S 1 a a) (x^2) := by
      simpa [pow_two] using mulDivBox_sound hS (by decide : 0<1) ha ha
    have h := ih hs
    simpa [repeatedSquare,pow_succ,pow_mul,Nat.mul_comm] using h

noncomputable def rationalBox (S m d : ℕ) : Box := ⟨S*m/d,S*m/d+1⟩

lemma rationalBox_sound {S d : ℕ} (hS : 0< S) (hd : 0< d) (m : ℕ) :
    Contains S (rationalBox S m d) ((m:ℝ)/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  have h := quotient_bounds (S*m) d hd
  constructor
  · calc
      _ ≤  ((S*m:ℕ):ℝ)/d/S := div_le_div_of_nonneg_right h.1 hSr.le
      _ = (m:ℝ)/d := by push_cast; field_simp
  · calc
      (m:ℝ)/d = ((S*m:ℕ):ℝ)/d/S := by push_cast; field_simp
      _ ≤  _ := div_le_div_of_nonneg_right h.2 hSr.le

end CertifiedFixedPoint

end Height100Module34

/- Source module: FixedPointExp310. -/
section Height100Module35

set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
namespace CertifiedFixedPoint

noncomputable def expUnit310 (a : Box) : Box := expBox scale310 a 200

lemma expUnit310_sound {a : Box} {x : ℝ} (ha : Contains scale310 a x) (hx : x≤ 1) :
    Contains scale310 (expUnit310 a) (Real.exp x) := by
  apply expBox_sound (by norm_num [scale310]) ha hx 200
  norm_num [scale310,Nat.factorial]

end CertifiedFixedPoint

end Height100Module35

/- Source module: PointExponentials. -/
section Height100Module36

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

noncomputable def center (i : Fin 16) : ℝ := (6*i.val+3)/16

noncomputable def pointInput (i : Fin 16) : Box := rationalBox scale310 (6*i.val+3) 128
noncomputable def pointExp (i : Fin 16) : Box := expUnit310 (pointInput i)
noncomputable def pointExpValues : List Box := List.ofFn pointExp

theorem _root_.CertifiedThetaPoints.pointExpCache_correct : CertifiedThetaPoints.pointExpValues = CertifiedThetaPoints.pointExpCache :=
  Eq.refl CertifiedThetaPoints.pointExpCache

lemma cachedPointExp_eq (i : Fin 16) : cachedPointExp i = pointExp i := by
  rw [cachedPointExp,←pointExpCache_correct]
  simp only [pointExpValues,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos i.isLt,Option.getD_some]

lemma pointExp_sound (i : Fin 16) :
    Contains scale310 (cachedPointExp i) (Real.exp (center i/8)) := by
  rw [cachedPointExp_eq]
  have ha := rationalBox_sound (by norm_num [scale310] : 0< scale310)
    (by decide : 0<128) (6*i.val+3)
  have he : (((6*i.val+3:ℕ):ℝ)/128) = center i/8 := by
    simp [center]
    ring
  norm_num only [Nat.cast_ofNat] at ha
  rw [he] at ha
  apply expUnit310_sound ha
  have hi : (i.val:ℝ)<16 := by exact_mod_cast i.isLt
  unfold center
  linarith

end CertifiedThetaPoints

end Height100Module36

/- Source module: ArctanCertificate. -/
section Height100Module37

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators

namespace CertifiedHighPrecisionPi

noncomputable def atanSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (-1)^n*x^(2*n+1)/(2*n+1)

lemma atan_remainder (x : ℝ) (hx0 : 0≤ x) (hx1 : x<1) (N : ℕ) :
    |Real.arctan x - atanSum x N| ≤  x^(2*N+1)/(1-x^2) := by
  have hx : ‖x‖<1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hx0]
  have hs := Real.hasSum_arctan hx
  have htail : Real.arctan x - atanSum x N =
      ∑' n : ℕ, (-1)^(n+N)*x^(2*(n+N)+1)/(2*(n+N)+1) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    exact sub_eq_iff_eq_add.mpr (by simpa [atanSum,add_comm] using h.symm)
  rw [htail, ← Real.norm_eq_abs]
  have hq0 : 0≤ x^2 := sq_nonneg x
  have hq1 : x^2<1 := by nlinarith
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (x^(2*N+1))
  have he := tsum_of_norm_bounded hgeo (fun n : ℕ => by
    have hd : (1:ℝ)≤ 2*(n+N)+1 := by
      have hn : (0:ℝ)≤ n := Nat.cast_nonneg n
      have hN : (0:ℝ)≤ N := Nat.cast_nonneg N
      linarith
    calc
      ‖(-1:ℝ)^(n+N)*x^(2*(n+N)+1)/(2*(n+N)+1)‖ =
          x^(2*(n+N)+1)/(2*(n+N)+1) := by
        simp [norm_div,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_nonneg hx0,
          abs_of_nonneg (by positivity : (0:ℝ)≤ 2*(n+N)+1)]
      _ ≤  x^(2*(n+N)+1) := div_le_self (by positivity) hd
      _ = x^(2*N+1)*(x^2)^n := by
        rw [show 2*(n+N)+1=(2*N+1)+2*n by ring,pow_add,pow_mul])
  simpa only [div_eq_mul_inv] using he

noncomputable def rationalAtanSum (x : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ range N, (-1)^n*x^(2*n+1)/(2*n+1)

lemma rationalAtanSum_cast (x : ℚ) (N : ℕ) :
    (rationalAtanSum x N : ℝ) = atanSum x N := by
  simp [rationalAtanSum,atanSum]

noncomputable def machinApprox (N M : ℕ) : ℚ :=
  16*rationalAtanSum (1/5) N - 4*rationalAtanSum (1/239) M

lemma machin_error (N M : ℕ) :
    |Real.pi-(machinApprox N M:ℝ)| ≤ 
      16*((1/5:ℝ)^(2*N+1)/(1-(1/5:ℝ)^2)) +
        4*((1/239:ℝ)^(2*M+1)/(1-(1/239:ℝ)^2)) := by
  have h5 := atan_remainder (1/5) (by norm_num) (by norm_num) N
  have h239 := atan_remainder (1/239) (by norm_num) (by norm_num) M
  have hm : Real.pi = 16*Real.arctan (1/5)-4*Real.arctan (1/239) := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    norm_num at h
    linarith
  rw [hm,machinApprox]
  push_cast
  rw [rationalAtanSum_cast,rationalAtanSum_cast]
  calc
    _ = |16*(Real.arctan (1/5)-atanSum (1/5) N) -
        4*(Real.arctan (1/239)-atanSum (1/239) M)| := by congr 1; ring
    _ ≤  |16*(Real.arctan (1/5)-atanSum (1/5) N)| +
        |4*(Real.arctan (1/239)-atanSum (1/239) M)| := abs_sub _ _
    _ ≤  _ := by
      rw [abs_mul,abs_mul]
      norm_num at h5 h239 ⊢
      linarith

end CertifiedHighPrecisionPi

end Height100Module37

/- Source module: Pi310. -/
section Height100Module38

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option Elab.async false

namespace CertifiedHighPrecisionPi

lemma machin_error_320 : |Real.pi-(machinApprox 230 70:ℝ)|≤ 1/10^320 := by
  apply (machin_error 230 70).trans
  norm_num

lemma machin_lower_check : (piFloor310:ℚ)/10^310 + 1/10^320 ≤  machinApprox 230 70 := by
  decide +kernel

lemma machin_upper_check : machinApprox 230 70 + 1/10^320 ≤  (piFloor310+1:ℚ)/10^310 := by
  decide +kernel

theorem pi_enclosure_310 :
    (piFloor310:ℝ)/10^310 ≤  Real.pi ∧ Real.pi ≤  (piFloor310+1:ℝ)/10^310 := by
  have hl : (piFloor310:ℝ)/10^310 + 1/10^320 ≤  (machinApprox 230 70:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr machin_lower_check
    push_cast at h
    exact h
  have hu : (machinApprox 230 70:ℝ) + 1/10^320 ≤  (piFloor310+1:ℝ)/10^310 := by
    have h := (Rat.cast_le (K := ℝ)).mpr machin_upper_check
    push_cast at h
    exact h
  have he := abs_le.mp machin_error_320
  constructor <;> linarith

end CertifiedHighPrecisionPi

end Height100Module38

/- Source module: FixedPointTransforms. -/
section Height100Module39

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedFixedPoint

noncomputable def divideBox (d : ℕ) (a : Box) : Box := ⟨a.lo/d,a.hi/d+1⟩

lemma scaleBox_sound {S : ℕ} (m : ℕ) {a : Box} {x : ℝ}
    (ha : Contains S a x) : Contains S (scaleBox m a) ((m:ℝ)*x) := by
  constructor <;> dsimp [scaleBox]
  · push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ha.1 (Nat.cast_nonneg m)
  · push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ha.2 (Nat.cast_nonneg m)

lemma divideBox_sound {S d : ℕ} (hS : 0< S) (hd : 0< d)
    {a : Box} {x : ℝ} (ha : Contains S a x) :
    Contains S (divideBox d a) (x/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  constructor
  · calc
      _ ≤  ((a.lo:ℝ)/d)/S := div_le_div_of_nonneg_right (quotient_bounds a.lo d hd).1 hSr.le
      _ = ((a.lo:ℝ)/S)/d := by ring
      _ ≤  _ := div_le_div_of_nonneg_right ha.1 hdr.le
  · calc
      _ ≤  ((a.hi:ℝ)/S)/d := div_le_div_of_nonneg_right ha.2 hdr.le
      _ = ((a.hi:ℝ)/d)/S := by ring
      _ ≤  _ := div_le_div_of_nonneg_right (quotient_bounds a.hi d hd).2 hSr.le

lemma expTaylorRun_sum_lower (S : ℕ) (a : Box) (n : ℕ) :
    S≤ (expTaylorRun S a n).2.lo := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ih.trans (Nat.le_add_right _ _)

lemma expUnit310_lo_pos (a : Box) : 0<(expUnit310 a).lo := by
  have h := expTaylorRun_sum_lower scale310 a 200
  exact (by norm_num [scale310] : 0< scale310).trans_le h

noncomputable def expNegative310 (a : Box) : Box :=
  repeatedSquare scale310 10 (inverseBox scale310 (expUnit310 (divideBox 1024 a)))

lemma expNegative310_sound {a : Box} {x : ℝ}
    (ha : Contains scale310 a x) (hx : x≤ 1024) :
    Contains scale310 (expNegative310 a) (Real.exp (-x)) := by
  have hS : 0< scale310 := by norm_num [scale310]
  have hq := divideBox_sound hS (by decide : 0<1024) ha
  have he := expUnit310_sound hq (by norm_num; linarith)
  have hi := inverseBox_sound hS he (expUnit310_lo_pos _)
  have hp := repeatedSquare_sound hS 10 hi
  have hv : (1/Real.exp (x/1024))^(1024:ℕ) = Real.exp (-x) := by
    rw [one_div,←Real.exp_neg,←Real.exp_nat_mul]
    norm_num
    ring
  norm_num only [Nat.cast_ofNat] at hp
  simpa only [expNegative310,hv] using hp

end CertifiedFixedPoint

end Height100Module39


