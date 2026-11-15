-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore003
-- name    : row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore003
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:03:23.059394+00:00
-- url     : https://prove2.me/theorems/cddf34c9-b45b-44cf-9ce3-7881d61af987
-- title:
--   Row 23 RH support: RHLow100ThreeRebuilt.AcceptedCore003
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore002
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


/- Source module: ExponentialJetEnclosure. -/
section Height100Module4

open Complex Finset
namespace CertifiedExponentialJets
open CertifiedTaylorQuadrature CertifiedMomentConvolution

lemma coefficient_deriv (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coefficient (deriv f) c n=(n+1:ℂ)*coefficient f c (n+1) := by
  unfold coefficient
  rw [← iteratedDeriv_succ',Nat.factorial_succ]
  push_cast
  have h0 : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h1 : (n+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

lemma exp_coefficient_recurrence (g : ℂ → ℂ) (hg : Differentiable ℂ g) (c : ℂ) (n : ℕ) :
    (n+1:ℂ)*coefficient (fun z => Complex.exp (g z)) c (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*coefficient g c (k+1)*
        coefficient (fun z => Complex.exp (g z)) c (n-k) := by
  have hf : Differentiable ℂ (fun z => Complex.exp (g z)) := by fun_prop
  have he : deriv (fun z => Complex.exp (g z)) =
      (fun z => deriv g z*Complex.exp (g z)) := by
    funext z
    exact ((hg z).hasDerivAt.cexp).deriv.trans (mul_comm _ _)
  rw [← coefficient_deriv,he,coefficient_mul _ _ hg.deriv hf]
  simp_rw [coefficient_deriv]

lemma scaled_exp_coefficient_recurrence (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (c h : ℂ) (n : ℕ) :
    (n+1:ℂ)*scaledCoefficient (fun z => Complex.exp (g z)) c h (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*scaledCoefficient g c h (k+1)*
        scaledCoefficient (fun z => Complex.exp (g z)) c h (n-k) := by
  unfold scaledCoefficient
  rw [← mul_assoc,exp_coefficient_recurrence g hg c n,sum_mul]
  apply sum_congr rfl
  intro k hk
  have he : n+1=(k+1)+(n-k) := by have := mem_range.mp hk; omega
  conv_lhs => rw [he,pow_add]
  ring

lemma product_error (a b x y : ℂ) (r s : ℝ)
    (ha : ‖a-x‖≤ r) (hb : ‖b-y‖≤ s) :
    ‖a*b-x*y‖≤ ‖x‖*s+r*‖y‖+r*s := by
  have hr : 0≤ r := (norm_nonneg _).trans ha
  have hs : 0≤ s := (norm_nonneg _).trans hb
  have he : a*b-x*y=x*(b-y)+(a-x)*y+(a-x)*(b-y) := by ring
  rw [he]
  calc
    _ ≤  ‖x*(b-y)+(a-x)*y‖+‖(a-x)*(b-y)‖ := norm_add_le _ _
    _ ≤  (‖x*(b-y)‖+‖(a-x)*y‖)+‖(a-x)*(b-y)‖ := by gcongr; exact norm_add_le _ _
    _ = (‖x‖*‖b-y‖+‖a-x‖*‖y‖)+‖a-x‖*‖b-y‖ := by simp only [norm_mul]
    _ ≤  _ := by gcongr

noncomputable def residual (G F : ℕ → ℂ) (n : ℕ) : ℂ :=
  (n+1:ℂ)*F (n+1)-∑ k ∈ range (n+1), (k+1:ℂ)*G (k+1)*F (n-k)

noncomputable def errorSum (G F : ℕ → ℂ) (r s : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n+1), (k+1:ℝ)*
    (‖G (k+1)‖*s (n-k)+r (k+1)*‖F (n-k)‖+r (k+1)*s (n-k))

/- A finite ODE residual certificate proves every coefficient enclosure by induction.
The residual and its error bound are convolutions, so they support packed-integer verification. -/
theorem enclosure_of_recurrence (A F G C : ℕ → ℂ) (r s : ℕ → ℝ) (N : ℕ)
    (hrec : ∀ n : ℕ, (n+1:ℂ)*F (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*A (k+1)*F (n-k))
    (hG : ∀ j< N, ‖A j-G j‖≤ r j)
    (h0 : ‖F 0-C 0‖≤ s 0)
    (hcheck : ∀ n, n+1< N → ‖residual G C n‖+errorSum G C r s n≤ (n+1:ℝ)*s (n+1)) :
    ∀ n< N, ‖F n-C n‖≤ s n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => exact h0
    | succ n =>
      have hp (k : ℕ) (hk : k∈range (n+1)) :
          ‖A (k+1)*F (n-k)-G (k+1)*C (n-k)‖ ≤ 
            ‖G (k+1)‖*s (n-k)+r (k+1)*‖C (n-k)‖+r (k+1)*s (n-k) := by
        have hk' := mem_range.mp hk
        exact product_error _ _ _ _ _ _ (hG (k+1) (by omega))
          (ih (n-k) (by omega) (by omega))
      have he : (n+1:ℂ)*(F (n+1)-C (n+1)) =
          (∑ k ∈ range (n+1), (k+1:ℂ)*(A (k+1)*F (n-k)-G (k+1)*C (n-k))) - residual G C n := by
        unfold residual
        simp_rw [mul_sub,sum_sub_distrib]
        rw [hrec n]
        simp only [mul_assoc]
        ring
      have hm : (n+1:ℝ)*‖F (n+1)-C (n+1)‖≤ (n+1:ℝ)*s (n+1) := by
        calc
          _ = ‖(n+1:ℂ)*(F (n+1)-C (n+1))‖ := by rw [norm_mul]; norm_cast
          _ ≤  ‖∑ k ∈ range (n+1), (k+1:ℂ)*(A (k+1)*F (n-k)-G (k+1)*C (n-k))‖+
              ‖residual G C n‖ := by rw [he]; exact norm_sub_le _ _
          _ ≤  (∑ k ∈ range (n+1), ‖(k+1:ℂ)*(A (k+1)*F (n-k)-G (k+1)*C (n-k))‖)+
              ‖residual G C n‖ := by gcongr; exact norm_sum_le _ _
          _ ≤  errorSum G C r s n+‖residual G C n‖ := by
            gcongr
            unfold errorSum
            apply sum_le_sum
            intro k hk
            rw [norm_mul]
            have hc : ‖(k+1:ℂ)‖=(k+1:ℝ) := by norm_cast
            rw [hc]
            exact mul_le_mul_of_nonneg_left (hp k hk) (by positivity)
          _ ≤  _ := by linarith [hcheck n hn]
      have hpos : (0:ℝ)< n+1 := by positivity
      nlinarith

/- Specialized soundness for the Taylor jet of exp(g), with arbitrary complex panel scale. -/
end CertifiedExponentialJets

end Height100Module4

/- Source module: IntegerExponentialJet. -/
section Height100Module5

open Complex Finset
namespace CertifiedIntegerExponentialJets
open CertifiedMomentConvolution CertifiedExponentialJets

noncomputable def integerResidual (D : ℕ) (G C : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n+1:ℤ)*C (n+1)*D-∑ k ∈ range (n+1), (k+1:ℤ)*G (k+1)*C (n-k)

noncomputable def integerErrorSum (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (k+1:ℤ)*
    (|G (k+1)| *(s (n-k):ℤ)+(r (k+1):ℤ) * |C (n-k)|+(r (k+1):ℤ)*s (n-k))

noncomputable def fixedCenter (D : ℕ) (G : ℕ → ℤ) (n : ℕ) : ℂ := (G n:ℂ)/D
noncomputable def fixedRadius (D : ℕ) (r : ℕ → ℕ) (n : ℕ) : ℝ := (r n:ℝ)/D

lemma residual_scale (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (n : ℕ) :
    CertifiedExponentialJets.residual (fixedCenter D G) (fixedCenter D C) n =
      (integerResidual D G C n:ℂ)/(D:ℂ)^2 := by
  have hd : (D:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hs : (∑ k ∈ range (n+1), (k+1:ℂ)*((G (k+1):ℂ)/D)*((C (n-k):ℂ)/D)) =
      (∑ k ∈ range (n+1), (k+1:ℂ)*(G (k+1):ℂ)*(C (n-k):ℂ))/(D:ℂ)^2 := by
    rw [sum_div]
    apply sum_congr rfl
    intro k _
    field_simp
  unfold CertifiedExponentialJets.residual fixedCenter integerResidual
  push_cast
  rw [hs]
  field_simp

lemma errorSum_scale (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ) :
    errorSum (fixedCenter D G) (fixedCenter D C) (fixedRadius D r) (fixedRadius D s) n =
      (integerErrorSum G C r s n:ℝ)/(D:ℝ)^2 := by
  have hd : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  unfold errorSum fixedCenter fixedRadius integerErrorSum
  simp only [norm_div,Complex.norm_intCast,Complex.norm_natCast,
    Int.cast_sum,Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_abs]
  rw [sum_div]
  apply sum_congr rfl
  intro k _
  field_simp

lemma integer_check_sound (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ)
    (hc : |integerResidual D G C n|+integerErrorSum G C r s n≤ (n+1:ℤ)*s (n+1)*D) :
    ‖CertifiedExponentialJets.residual (fixedCenter D G) (fixedCenter D C) n‖+
      errorSum (fixedCenter D G) (fixedCenter D C) (fixedRadius D r) (fixedRadius D s) n ≤ 
      (n+1:ℝ)*fixedRadius D s (n+1) := by
  have hd : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hnum : |(integerResidual D G C n:ℝ)|+(integerErrorSum G C r s n:ℝ) ≤ 
      (n+1:ℝ)*(s (n+1):ℝ)*D := by exact_mod_cast hc
  rw [residual_scale D hD,errorSum_scale D hD,norm_div,norm_pow,
    Complex.norm_intCast,Complex.norm_natCast]
  calc
    _ = (|(integerResidual D G C n:ℝ)|+(integerErrorSum G C r s n:ℝ))/(D:ℝ)^2 := by ring
    _ ≤  ((n+1:ℝ)*(s (n+1):ℝ)*D)/(D:ℝ)^2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = _ := by unfold fixedRadius; field_simp

/- Integer residual certificates also apply to any sequence satisfying the same ODE,
including a constant multiple of exp(g). -/
theorem fixed_enclosure_of_recurrence (A F : ℕ → ℂ)
    (D : ℕ) (hD : 0< D) (G C : ℕ → ℤ) (r s : ℕ → ℕ) (N : ℕ)
    (hrec : ∀ n : ℕ, (n+1:ℂ)*F (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*A (k+1)*F (n-k))
    (hG : ∀ j< N, ‖A j-fixedCenter D G j‖≤ fixedRadius D r j)
    (h0 : ‖F 0-fixedCenter D C 0‖≤ fixedRadius D s 0)
    (hcheck : ∀ n : ℕ, n+1< N →
      |integerResidual D G C n|+integerErrorSum G C r s n≤ (n+1:ℤ)*s (n+1)*D) :
    ∀ n< N, ‖F n-fixedCenter D C n‖≤ fixedRadius D s n := by
  apply enclosure_of_recurrence A F (fixedCenter D G) (fixedCenter D C)
    (fixedRadius D r) (fixedRadius D s) N hrec hG h0
  intro n hn
  exact integer_check_sound D hD G C r s n (hcheck n hn)

/- Entirely integer residual checks certify scaled Taylor coefficients of exp(g).
Only the input coefficient and initial-value enclosures involve the analytic function. -/
end CertifiedIntegerExponentialJets

end Height100Module5

/- Source module: SignedODEConvolution. -/
section Height100Module6

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedSignedODEConvolution
open CertifiedIntegerExponentialJets

noncomputable def conv (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n+1), a k*b (n-k)

noncomputable def absDerivative (G : ℕ → ℤ) (k : ℕ) : ℕ := (k+1)*(G (k+1)).natAbs
noncomputable def radiusDerivative (r : ℕ → ℕ) (k : ℕ) : ℕ := (k+1)*r (k+1)

noncomputable def positive (C : ℕ → ℤ) (k : ℕ) : ℕ := (C k).toNat
noncomputable def negative (C : ℕ → ℤ) (k : ℕ) : ℕ := (-C k).toNat

lemma signed_product (G C : ℕ → ℤ) (n : ℕ)
    (hG : ∀ k, k≤ n → G (k+1)≤ 0) :
    (∑ k ∈ range (n+1), (k+1:ℤ)*G (k+1)*C (n-k)) =
      -(conv (absDerivative G) (positive C) n:ℤ) +
        (conv (absDerivative G) (negative C) n:ℤ) := by
  unfold conv absDerivative positive negative
  push_cast
  rw [←sum_neg_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  have hkg := hG k (by simpa using mem_range.mp hk)
  calc
    _ = (k+1:ℤ)*G (k+1)*((C (n-k)).toNat-((-C (n-k)).toNat:ℤ)) := by
      rw [Int.toNat_sub_toNat_neg]
    _ = _ := by rw [abs_of_nonpos hkg]; ring

lemma error_product (G C : ℕ → ℤ) (r s : ℕ → ℕ) (n : ℕ) :
    integerErrorSum G C r s n =
      (conv (absDerivative G) s n:ℤ) +
        (conv (radiusDerivative r) (fun j => (C j).natAbs+s j) n:ℤ) := by
  unfold integerErrorSum conv absDerivative radiusDerivative
  push_cast
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  ring

lemma residual_product (D : ℕ) (G C : ℕ → ℤ) (n : ℕ)
    (hG : ∀ k, k≤ n → G (k+1)≤ 0) :
    integerResidual D G C n = (n+1:ℤ)*C (n+1)*D +
      (conv (absDerivative G) (positive C) n:ℤ) -
        (conv (absDerivative G) (negative C) n:ℤ) := by
  rw [integerResidual,signed_product G C n hG]
  ring

/- Four nonnegative convolutions suffice for the complete signed ODE check
when the exponent's nonconstant Taylor coefficients are nonpositive. -/
theorem residual_check_of_convolutions (D : ℕ) (G C : ℕ → ℤ) (r s : ℕ → ℕ)
    (n cp cm es er : ℕ) (hG : ∀ k, k≤ n → G (k+1)≤ 0)
    (hp : cp=conv (absDerivative G) (positive C) n)
    (hm : cm=conv (absDerivative G) (negative C) n)
    (hes : es=conv (absDerivative G) s n)
    (her : er=conv (radiusDerivative r) (fun j => (C j).natAbs+s j) n)
    (hc : (((n+1:ℤ)*C (n+1)*D+(cp:ℤ)-(cm:ℤ)).natAbs+es+er)≤ (n+1)*s (n+1)*D) :
    |integerResidual D G C n|+integerErrorSum G C r s n≤ (n+1:ℤ)*s (n+1)*D := by
  rw [residual_product D G C n hG,error_product,←hp,←hm,←hes,←her]
  have hh : (((((n+1:ℤ)*C (n+1)*D+(cp:ℤ)-(cm:ℤ)).natAbs+es+er):ℕ):ℤ) ≤ 
      (((n+1)*s (n+1)*D:ℕ):ℤ) := by exact_mod_cast hc
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Int.natCast_natAbs,add_assoc] using hh

noncomputable def vector (N : ℕ) (f : ℕ → ℕ) : List ℕ := List.ofFn (fun j : Fin N => f j.val)
noncomputable def packed (bits N : ℕ) (a b : ℕ → ℕ) : ℕ :=
  CertifiedPackedConvolution.encode bits (vector N a) *
    CertifiedPackedConvolution.encode bits (vector N b)
noncomputable def digit (bits p k : ℕ) : ℕ := (p >>> (bits*k)) % (2^bits)

end CertifiedSignedODEConvolution

end Height100Module6

/- Source module: ListODEVectors. -/
section Height100Module7

set_option autoImplicit false
namespace CertifiedListODEVectors
open CertifiedSignedODEConvolution
open Finset
open scoped BigOperators

lemma getD_mapIdx_zero {α β : Type*} [Zero α] [Zero β]
    (l : List α) (f : ℕ → α → β) (hf : ∀ j,f j 0=0) (j : ℕ) :
    (l.mapIdx f).getD j 0=f j (l.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_mapIdx]
  cases l[j]? <;> simp [hf]

lemma getD_tail {α : Type*} (l : List α) (j : ℕ) (d : α) :
    l.tail.getD j d=l.getD (j+1) d := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_tail]

lemma absDerivativeList_getD (g : List ℤ) (j : ℕ) :
    (absDerivativeList g).getD j 0=(j+1)*(g.getD (j+1) 0).natAbs := by
  rw [absDerivativeList,←List.mapIdx_eq_zipIdx_map (l := g.tail)
    (f := fun k (x : ℤ) => (k+1)*x.natAbs),
    getD_mapIdx_zero _ _ (by intro k; simp),getD_tail]

lemma radiusDerivativeList_getD (r : List ℕ) (j : ℕ) :
    (radiusDerivativeList r).getD j 0=(j+1)*r.getD (j+1) 0 := by
  rw [radiusDerivativeList,←List.mapIdx_eq_zipIdx_map (l := r.tail)
    (f := fun k (x : ℕ) => (k+1)*x),
    getD_mapIdx_zero _ _ (by intro k; simp),getD_tail]

lemma positiveList_getD (f : List ℤ) (j : ℕ) :
    (positiveList f).getD j 0=(f.getD j 0).toNat := by
  exact List.getD_map f 0 Int.toNat

lemma negativeList_getD (f : List ℤ) (j : ℕ) :
    (negativeList f).getD j 0=(-f.getD j 0).toNat := by
  exact List.getD_map f 0 (fun x : ℤ => (-x).toNat)

lemma radiusFactorList_getD (f : List ℤ) (s : List ℕ) (h : f.length=s.length) (j : ℕ) :
    (radiusFactorList f s).getD j 0=(f.getD j 0).natAbs+s.getD j 0 := by
  induction f generalizing s j with
  | nil => cases s <;> simp_all [radiusFactorList]
  | cons x xs ih =>
    cases s with
    | nil => simp at h
    | cons y ys =>
      cases j with
      | zero => rfl
      | succ j => exact ih ys (by simpa using h) j

lemma list_all_nonpos (g : List ℤ) (h : g.all (fun x => decide (x≤ 0))=true) (j : ℕ) :
    g.getD j 0≤ 0 := by
  induction g generalizing j with
  | nil => simp
  | cons x xs ih =>
    simp only [List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at h
    cases j with
    | zero => exact h.1
    | succ j => exact ih h.2 j

lemma digit_lists (bits : ℕ) (xs ys : List ℕ) (a b : ℕ → ℕ) (n : ℕ)
    (hx : ∀ k≤ n,xs.getD k 0=a k) (hy : ∀ k≤ n,ys.getD k 0=b k)
    (hc : xs.sum*ys.sum<2^bits) :
    digit bits (CertifiedPackedConvolution.encode bits xs*CertifiedPackedConvolution.encode bits ys) n=
      conv a b n := by
  rw [digit,CertifiedPackedConvolution.shiftRight_product_digit bits xs ys hc]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  rw [hx k (by omega),hy (n-k) (by omega)]

lemma digit_truncate (bits p N k : ℕ) (hk : k< N) :
    digit bits (p % 2^(bits*N)) k = digit bits p k := by
  unfold digit
  rw [Nat.shiftRight_eq_div_pow,Nat.shiftRight_eq_div_pow,
    show bits*N=bits*k+bits*(N-k) by
      rw [←Nat.mul_add]; congr 1; omega,pow_add,
    Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  have he : bits*(N-k)=bits+bits*(N-k-1) := by
    calc
      _ = bits*(1+(N-k-1)) := by congr 1; omega
      _ = _ := by ring
  rw [he,pow_add]
  exact Nat.dvd_mul_right _ _

end CertifiedListODEVectors

end Height100Module7

/- Source module: PackedHorner. -/
section Height100Module8

set_option autoImplicit false
open Finset
namespace CertifiedPackedHorner
open CertifiedPackedConvolution

/-- Coefficients of a polynomial after a nonnegative affine substitution. -/
noncomputable def translated (b q : ℕ) : List ℕ → List ℕ
  | [] => []
  | a::as => addLists [a] (CertifiedPackedConvolution.convolution [b,q] (translated b q as))

lemma translated_evaluation (B b q : ℕ) (as : List ℕ) :
    Nat.ofDigits B (translated b q as)=Nat.ofDigits (b+q*B) as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [translated,ofDigits_add,ofDigits_convolution,ih]
    simp only [Nat.ofDigits_cons,Nat.ofDigits_nil]
    ring

lemma translated_sum (b q : ℕ) (as : List ℕ) :
    (translated b q as).sum=Nat.ofDigits (b+q) as := by
  simpa only [Nat.ofDigits_one,mul_one] using translated_evaluation 1 b q as

/-- Horner arithmetic reduced modulo a fixed window at every step. -/
noncomputable def modularHorner (a M : ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => (x+a*modularHorner a M xs)%M

lemma modularHorner_eq (a M : ℕ) (xs : List ℕ) :
    modularHorner a M xs=Nat.ofDigits a xs%M := by
  induction xs with
  | nil => simp [modularHorner]
  | cons x xs ih => simp only [modularHorner,ih,Nat.ofDigits_cons,Nat.add_mod,Nat.mul_mod,Nat.mod_mod]

/-- A single scalar carry bound certifies every digit of the affine Horner expansion. -/
theorem modularHorner_digit (bits N b q : ℕ) (xs : List ℕ)
    (hcarry : Nat.ofDigits (b+q) xs<2^bits) (k : ℕ) (hk : k< N) :
    ((modularHorner (b+q*2^bits) (2^(bits*N)) xs) >>> (bits*k))%2^bits=
      (translated b q xs).getD k 0 := by
  rw [modularHorner_eq]
  change CertifiedSignedODEConvolution.digit bits
    (Nat.ofDigits (b+q*2^bits) xs%2^(bits*N)) k=_
  rw [CertifiedListODEVectors.digit_truncate bits _ N k hk]
  unfold CertifiedSignedODEConvolution.digit
  rw [Nat.shiftRight_eq_div_pow,pow_mul,←translated_evaluation]
  rw [digit_ofDigits _ (by positivity),coefficient_eq_getD]
  intro x hx
  exact (member_le_sum _ _ hx).trans_lt ((translated_sum b q xs) ▸ hcarry)

lemma ofDigits_add_complex (z : ℂ) (xs ys : List ℕ) :
    Nat.ofDigits z (addLists xs ys)=Nat.ofDigits z xs+Nat.ofDigits z ys := by
  induction xs generalizing ys with
  | nil => simp [addLists,Nat.ofDigits]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addLists,Nat.ofDigits]
    | cons y ys => simp only [addLists,Nat.ofDigits,Nat.cast_add,ih]; ring

lemma ofDigits_map_complex (z : ℂ) (a : ℕ) (xs : List ℕ) :
    Nat.ofDigits z (xs.map (a*·))=(a:ℂ)*Nat.ofDigits z xs := by
  induction xs with
  | nil => simp [Nat.ofDigits]
  | cons x xs ih => simp only [List.map_cons,Nat.ofDigits,Nat.cast_mul,ih]; ring

lemma ofDigits_convolution_complex (z : ℂ) (xs ys : List ℕ) :
    Nat.ofDigits z (CertifiedPackedConvolution.convolution xs ys)=Nat.ofDigits z xs*Nat.ofDigits z ys := by
  induction xs with
  | nil => simp [CertifiedPackedConvolution.convolution,Nat.ofDigits]
  | cons x xs ih =>
    rw [CertifiedPackedConvolution.convolution,ofDigits_add_complex,ofDigits_map_complex]
    simp only [Nat.ofDigits,Nat.cast_zero,ih]
    ring

lemma translated_complex (z : ℂ) (b q : ℕ) (xs : List ℕ) :
    Nat.ofDigits z (translated b q xs)=Nat.ofDigits ((b:ℂ)+(q:ℂ)*z) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [translated,ofDigits_add_complex,ofDigits_convolution_complex,ih]
    simp only [Nat.ofDigits]
    ring

end CertifiedPackedHorner

namespace CertifiedPackedHorner
/-- Matching the recursive Nat forces the kernel to evaluate it once before the
small-multiple and shift branches reuse its literal value. -/
noncomputable def bitStep (bits b q mask x : ℕ) : ℕ → ℕ
  | 0 => x &&& mask
  | n+1 => (x+b*(n+1)+q*((n+1) <<< bits)) &&& mask

noncomputable def bitHorner (bits N b q : ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => bitStep bits b q ((1 <<< (bits*N))-1) x (bitHorner bits N b q xs)

lemma bitStep_eq (bits N b q x n : ℕ) :
    bitStep bits b q ((1 <<< (bits*N))-1) x n=
      (x+(b+q*2^bits)*n)%2^(bits*N) := by
  cases n <;>
    simp only [bitStep,Nat.shiftLeft_eq,one_mul,
      Nat.and_two_pow_sub_one_eq_mod,mul_zero,add_zero]
  congr 1
  ring

lemma bitHorner_eq (bits N b q : ℕ) (xs : List ℕ) :
    bitHorner bits N b q xs=modularHorner (b+q*2^bits) (2^(bits*N)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [bitHorner,bitStep_eq,ih,modularHorner]

lemma bitHorner_digit (bits N b q : ℕ) (xs : List ℕ)
    (hcarry : Nat.ofDigits (b+q) xs<2^bits) (k : ℕ) (hk : k< N) :
    ((bitHorner bits N b q xs) >>> (bits*k))%2^bits=(translated b q xs).getD k 0 := by
  rw [bitHorner_eq]
  exact modularHorner_digit bits N b q xs hcarry k hk
end CertifiedPackedHorner

end Height100Module8

/- Source module: ZetaSix. -/
section Height100Module9
/- Reused accepted theta-kernel and Mellin lemmas by @Gabewhigham.
Original accepted proof: https://prove2.me/submissions/7ab19408-190a-439f-81f8-63e983ebb00b
Published September6,2026. The unused height-six conclusion is omitted. -/

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real

namespace ZetaSix

/-- The Jacobi-theta functional-equation pair underlying Mathlib's completed zeta function. -/
noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0

/-! ### Bounds for the theta kernel -/

lemma evenKernel_zero_eq_F_int {t : ℝ} (ht : 0 < t) :
    evenKernel 0 t = HurwitzKernelBounds.F_int 0 0 t := by
  have h := (hasSum_int_evenKernel 0 ht).tsum_eq
  have h2 : HurwitzKernelBounds.F_int 0 ((0 : ℝ) : UnitAddCircle) t
      = ∑' n : ℤ, HurwitzKernelBounds.f_int 0 0 t n := by
    simp only [HurwitzKernelBounds.F_int, Function.Periodic.lift_coe]
  simp only [QuotientAddGroup.mk_zero] at h2 h
  rw [h2, ← h]
  simp [HurwitzKernelBounds.f_int]

/-- Explicit bound for the theta kernel: `|θ t - 1| ≤  2 e ^ (-π t) / (1 - e ^ (-π t))`. -/
lemma abs_evenKernel_zero_sub_one_le {t : ℝ} (ht : 0 < t) :
    |evenKernel 0 t - 1| ≤  2 * rexp (-π * t) / (1 - rexp (-π * t)) := by
  have h1 := HurwitzKernelBounds.F_nat_zero_zero_sub_le ht
  have h2 := HurwitzKernelBounds.F_nat_zero_le (a := 1) zero_le_one ht
  have h3 : HurwitzKernelBounds.F_int 0 ((0 : ℝ) : UnitAddCircle) t
      = HurwitzKernelBounds.F_nat 0 0 t + HurwitzKernelBounds.F_nat 0 (1 - 0) t :=
    HurwitzKernelBounds.F_int_eq_of_mem_Icc 0 (by simp) ht
  simp only [QuotientAddGroup.mk_zero, sub_zero] at h3
  simp only [Real.norm_eq_abs, one_pow, mul_one] at h1 h2
  rw [evenKernel_zero_eq_F_int ht, h3,
    show HurwitzKernelBounds.F_nat 0 0 t + HurwitzKernelBounds.F_nat 0 1 t - 1
      = (HurwitzKernelBounds.F_nat 0 0 t - 1) + HurwitzKernelBounds.F_nat 0 1 t from by ring]
  calc |_| ≤  |HurwitzKernelBounds.F_nat 0 0 t - 1| + |HurwitzKernelBounds.F_nat 0 1 t| :=
        abs_add_le _ _
    _ ≤  rexp (-π * t) / (1 - rexp (-π * t)) + rexp (-π * t) / (1 - rexp (-π * t)) :=
        add_le_add h1 h2
    _ = 2 * rexp (-π * t) / (1 - rexp (-π * t)) := by ring
/-- The theta functional equation in the form we need. -/
lemma evenKernel_eq_of_pos {t : ℝ} (h0 : 0 < t) :
    evenKernel 0 t = t ^ (-(1 : ℝ) / 2) * evenKernel 0 (1 / t) := by
  have h := evenKernel_functional_equation 0 t
  rw [← evenKernel_eq_cosKernel_of_zero] at h
  rw [h]
  congr 1
  rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul h0.le]
  norm_num

/-! ### The modified kernel appearing in the Mellin transform -/

lemma f_modif_of_one_lt {t : ℝ} (ht : 1 < t) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - 1 := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, ht, not_lt.2 ht.le, Set.indicator_of_notMem]

lemma f_modif_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, h0, h1, not_lt.2 h1.le]
  norm_num

lemma f_modif_one : P.f_modif 1 = 0 := by
  simp [P, WeakFEPair.f_modif]
/-! ### Numerical input: `e ^ π ≥  23` -/

lemma exp_pi_ge_23 : (23 : ℝ) ≤  rexp π := by
  have h1 : (0.7853 : ℝ) < π / 4 := by nlinarith [Real.pi_gt_d4]
  have hp : (0 : ℝ) < π / 4 := by positivity
  have h2 : (2.19 : ℝ) ≤  rexp (π / 4) := by
    have h := Real.sum_le_exp_of_nonneg (x := π / 4) hp.le 6
    simp [Finset.sum_range_succ, Nat.factorial] at h
    nlinarith [h1, pow_pos hp 2, pow_pos hp 3, pow_pos hp 4, pow_pos hp 5]
  have h3 : (rexp (π / 4)) ^ 4 = rexp π := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h4 : (2.19 : ℝ) ^ 4 ≤  (rexp (π / 4)) ^ 4 := by gcongr
  rw [← h3]; nlinarith [h4]

lemma exp_neg_pi_le_23 : rexp (-π) ≤  1 / 23 := by
  have h := exp_pi_ge_23
  have hprod : rexp (-π) * rexp π = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-π), Real.exp_pos π]
/-! ### The theta kernel with the sharper constant `21/10` -/

lemma abs_evenKernel_sub_one_le_of_one_le {t : ℝ} (ht : 1 ≤  t) :
    |evenKernel 0 t - 1| ≤  21 / 10 * rexp (-π * t) := by
  have hexp : rexp (-π * t) ≤  rexp (-π) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  have h23 : rexp (-π * t) ≤  1 / 23 := le_trans hexp exp_neg_pi_le_23
  have hpos : 0 < rexp (-π * t) := Real.exp_pos _
  have hd : (0 : ℝ) < 1 - rexp (-π * t) := by linarith
  refine (abs_evenKernel_zero_sub_one_le (by linarith)).trans ?_
  rw [div_le_iff₀ hd]
  nlinarith

lemma norm_f_modif_le_of_one_lt {t : ℝ} (ht : 1 < t) :
    ‖P.f_modif t‖ ≤  21 / 10 * rexp (-π * t) := by
  rw [f_modif_of_one_lt ht,
    show ((evenKernel 0 t : ℝ) : ℂ) - 1 = ((evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_evenKernel_sub_one_le_of_one_le ht.le

lemma norm_f_modif_le_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ‖P.f_modif t‖ ≤  21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t) := by
  have ht1 : (1 : ℝ) ≤  1 / t := by rw [le_div_iff₀ h0]; linarith
  have hrpow : (0 : ℝ) < t ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos h0 _
  rw [f_modif_of_lt_one h0 h1,
    show ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
      = ((evenKernel 0 t - t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, evenKernel_eq_of_pos h0,
    show t ^ (-(1 : ℝ) / 2) * evenKernel 0 (1 / t) - t ^ (-(1 : ℝ) / 2)
      = t ^ (-(1 : ℝ) / 2) * (evenKernel 0 (1 / t) - 1) from by ring,
    abs_mul, abs_of_pos hrpow, mul_comm (21 / 10 : ℝ), mul_assoc]
  have h := abs_evenKernel_sub_one_le_of_one_le ht1
  rw [show -π * (1 / t) = -π / t by ring] at h
  exact mul_le_mul_of_nonneg_left h hrpow.le

/-! ### The tail integral `J = ∫_1^∞ u^{-1/2} e^{-π u} du` -/

/-- `∫_0^∞ x^k e^{-π x} dx = k! / π^{k+1}`. -/
lemma integral_pow_mul_exp (k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ k * rexp (-π * x)) = (Nat.factorial k) / π ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := π) (by positivity)
    Real.pi_pos
  have hc : (∫ x in Ioi (0 : ℝ), x ^ ((k : ℝ) + 1 - 1) * rexp (-(π * x)))
      = ∫ x in Ioi (0 : ℝ), x ^ k * rexp (-π * x) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) by ring, Real.rpow_natCast]
    ring_nf
  rw [hc, Real.Gamma_nat_eq_factorial k,
    show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h
  rw [h, div_pow, one_pow]
  field_simp

/-- Translation of an integral over `(1,∞)` to one over `(0,∞)`. -/
lemma integral_Ioi_one_shift (g : ℝ → ℝ) :
    (∫ u in Ioi (1 : ℝ), g u) = ∫ x in Ioi (0 : ℝ), g (x + 1) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_add_right_eq_self (fun x => (Ioi (1 : ℝ)).indicator g x) 1]
  congr 1
  ext x
  by_cases h : (0 : ℝ) < x
  · rw [Set.indicator_of_mem (by simp; linarith : x + 1 ∈ Ioi (1 : ℝ)),
      Set.indicator_of_mem (by simpa using h)]
  · rw [Set.indicator_of_notMem (by simp; linarith [not_lt.1 h] : x + 1 ∉ Ioi (1 : ℝ)),
      Set.indicator_of_notMem (by simpa using h)]

lemma integrableOn_pow_mul_exp (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * rexp (-π * x)) (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => rexp (-y) * y ^ ((k : ℝ) + 1 - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by positivity)
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun y : ℝ => rexp (-y) * y ^ ((k : ℝ) + 1 - 1)) 0 Real.pi_pos).mpr (by simpa using hg)
  have hc : IntegrableOn
      (fun x : ℝ => (π ^ k)⁻¹ * (rexp (-(π * x)) * (π * x) ^ ((k : ℝ) + 1 - 1))) (Ioi 0) :=
    hs.const_mul _
  refine hc.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  dsimp only
  rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) by ring, Real.mul_rpow Real.pi_pos.le hx0.le,
    Real.rpow_natCast, Real.rpow_natCast]
  have hne : (π : ℝ) ^ k ≠ 0 := by positivity
  field_simp

end ZetaSix

end Height100Module9


