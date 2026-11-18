-- Prove2me | Definitions.Def_OAIQ368Chrom026
-- name    : OAIQ368Chrom026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:24:54.366768+00:00
-- url     : https://prove2.me/theorems/efcb68c1-a8a8-4f3d-be3b-739661ff5e72
-- title:
--   Definitions bundle OAIQ368Chrom026 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 274 declarations of OpenAI's Lean: 77 definitions, 2 inductive types or structures, 4 instances and 191 theorems. The definitions and types are `OAI.ElementaryPositivity.CenterCalculus.box`, `OAI.ElementaryPositivity.CenterCalculus.evalRat`, `OAI.ElementaryPositivity.CenterCalculus.fromRelative`, `OAI.ElementaryPositivity.CenterCalculus.lineSpecialization`, `OAI.ElementaryPositivity.CenterCalculus.mapLinear`, `OAI.ElementaryPositivity.CenterCalculus.ofTwo`, `OAI.ElementaryPositivity.CenterCalculus.relativePoint`, `OAI.ElementaryPositivity.CenterCalculus.toRelative`, `OAI.ElementaryPositivity.IndependentCenters.DiagonalDivides`, `OAI.ElementaryPositivity.IndependentCenters.diagonal`, `OAI.ElementaryPositivity.IndependentCenters.eval`, `OAI.ElementaryPositivity.IndependentCenters.minus`, `OAI.ElementaryPositivity.IndependentCenters.plus`, `OAI.ElementaryPositivity.IndependentCenters.substitute`, `OAI.ElementaryPositivity.LaurentAtInfinity.affinePolynomial`, `OAI.ElementaryPositivity.LinearDetection.additiveTensorFiltrationIdeal`, `OAI.ElementaryPositivity.LinearDetection.filtrationPiece`, `OAI.ElementaryPositivity.LinearDetection.middleEmbedding`, `OAI.ElementaryPositivity.LinearDetection.middleInsert`, `OAI.ElementaryPositivity.LinearDetection.retract`, `OAI.ElementaryPositivity.LinearDetection.testFiltration`, `OAI.ElementaryPositivity.LinearFiltration.Grade`, `OAI.ElementaryPositivity.LinearFiltration.TensorGrade`, `OAI.ElementaryPositivity.LinearFiltration.TensorGradePart`, `OAI.ElementaryPositivity.LinearFiltration.bilinear`, `OAI.ElementaryPositivity.LinearFiltration.bilinearRestrict`, `OAI.ElementaryPositivity.LinearFiltration.gradeProjection`, `OAI.ElementaryPositivity.LinearFiltration.map`, `OAI.ElementaryPositivity.LinearFiltration.mk`, `OAI.ElementaryPositivity.LinearFiltration.next`, `OAI.ElementaryPositivity.LinearFiltration.restrict`, `OAI.ElementaryPositivity.LinearFiltration.tensorGradeEquiv`, `OAI.ElementaryPositivity.LinearFiltration.tensorGradeInclusionW`, `OAI.ElementaryPositivity.LinearFiltration.tensorGradeProjectionW`, `OAI.ElementaryPositivity.LinearFiltration.tensorGradeSum`, `OAI.ElementaryPositivity.RawShuffle.RestrictionIndex`, `OAI.ElementaryPositivity.RawShuffle.RestrictionIndex.weight`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.braidingRatioUnit`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.mixedInverseKernelUnit`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationSeries` and 39 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_DHomogeneous`, `Chromatic_GradedAlgebra_DegreeSet`, `Chromatic_GradedAlgebra_Eval`, `Chromatic_GradedAlgebra_GradedBuilders`, `Chromatic_GradedAlgebra_LaurentAffineCancellation`, `Chromatic_GradedAlgebra_LaurentFilteredMultiplication`, `Chromatic_GradedAlgebra_LaurentInfinity`, `Chromatic_GradedAlgebra_LaurentProductNaturality`, `Chromatic_GradedAlgebra_RationalPolynomialDivisibility`, `Chromatic_Histories_KernelEvaluation`, `Chromatic_Histories_TwoLeafDiagonal`, `Chromatic_QuantumTorus_ProductUnitFiltration`, `Chromatic_Shuffle_AllPairDiagonal`, `Chromatic_Shuffle_BothTaylorB`, `Chromatic_Shuffle_CellTransferSeparation`, `Chromatic_Shuffle_Centers`, `Chromatic_Shuffle_ComponentB`, `Chromatic_Shuffle_CrossScalar`, `Chromatic_Shuffle_Degree`, `Chromatic_Shuffle_DegreeIdeals`, `Chromatic_Shuffle_DimensionEquivBTrans`, `Chromatic_Shuffle_DimensionEquivS`, `Chromatic_Shuffle_FourBraiding`, `Chromatic_Shuffle_Interaction`, `Chromatic_Shuffle_LaurentIdealCoefficients`, `Chromatic_Shuffle_LaurentKernel`, `Chromatic_Shuffle_ManyBlockDiagonal`, `Chromatic_Shuffle_ManyBlockPolynomiality`, `Chromatic_Shuffle_PointEvaluation`, `Chromatic_Shuffle_Regroup`, `Chromatic_Shuffle_Restriction`, `Chromatic_Shuffle_RestrictionB`, `Chromatic_Shuffle_SeparationCoefficients`, `Chromatic_Shuffle_TaylorSCoeffHomogeneous`, `Chromatic_Shuffle_TensorFiltration`, `Chromatic_Shuffle_TensorPolynomialBox`, `Chromatic_Shuffle_UnitalFiltration`, `Chromatic_Shuffle_UnitalTensorGradeInclusion`, `Chromatic_Walls_CenterLineNaturality`, `Chromatic_Walls_CenterLineSpecialization`, `Chromatic_Walls_EulerFiniteProduct`, `Chromatic_Walls_HNSpanning`, `Chromatic_Walls_LaurentLinearNaturality`, `Chromatic_Walls_LaurentPolynomialAction`, `Chromatic_Walls_LaurentScalarAction`, `Chromatic_Walls_LinearFiltrationBilinear`, `Chromatic_Walls_PolynomialCoeffLinear`, `Chromatic_Walls_RationalTensorDetection`, `Chromatic_Walls_Taylor`, `Chromatic_Walls_TensorAssociatedGrade`, `Chromatic_Walls_TensorFiltrationIdeals`, `Chromatic_Walls_TensorFiltrationInterchange`, `Chromatic_Walls_TensorMiddleFiltration`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom028`, `OAIQ368Chrom030`, `OAIQ368Chrom038` and `OAIQ368Chrom058`; the proofs of `OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized`, `OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor`, `OAI.ElementaryPositivity.RawShuffle.fourGrid_taylor_factor`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_cross`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second`, `OAI.ElementaryPositivity.RawShuffle.fourTaylor_column_product`, `OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation`, `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds` and `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom023

section
-- module Solutions.OAIQ368_CHROM.Compat
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `MvPolynomial.monomial_mul_monomial`; ours is `MvPolynomial.monomial_mul`. -/
theorem _root_.MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ}
    {a b : R} : MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_DegreeSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.Homogeneity
open MvPolynomial
variable {σ τ R : Type*} [CommRing R] {w : σ → ℤ}

lemma homogeneous_negative_eq_zero (p : MvPolynomial σ R) {m : ℤ}
    (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) m) (hm : m<0) : p=0 := by
  apply hp.eq_zero_of_no_monomials
  intro d heq
  have hnn : (0:ℤ) ≤ Finsupp.weight (fun _=>(1:ℤ)) d := by
    simp only [Finsupp.weight_apply,nsmul_eq_mul,mul_one,Finsupp.sum]
    positivity
  omega

end ElementaryPositivity.Homogeneity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Taylor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CommonTranslation

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

variable {A : Type*} [CommRing A] [Algebra ℚ A]

section Polynomials
open MvPolynomial
variable {α β : Type*}

lemma D_eq_sum [Fintype α] : D (α := α) = ∑ i : α, pderiv i := by
  classical
  apply MvPolynomial.derivation_ext
  intro i
  rw [show (∑ j : α, pderiv j) (X i) = ∑ j : α, pderiv j (X i) from by
    simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
      congrFun (map_sum Derivation.coeFnAddMonoidHom (fun j : α => pderiv j) Finset.univ) (X i)]
  simp [pderiv_X, Pi.single_apply]

end Polynomials

end ElementaryPositivity.CommonTranslation

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_DHomogeneous
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.map_taylorS _root_.OAI.ElementaryPositivity.RawShuffle.map_taylorSValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CommonTranslation
open MvPolynomial
open ElementaryPositivity.Homogeneity
variable {σ : Type*} [Fintype σ]

lemma D_homogeneous (p : MvPolynomial σ ℚ) (k : ℤ)
    (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) :
    (D p).IsWeightedHomogeneous (fun _=>(1:ℤ)) (k-1) := by
  classical
  rw [D_eq_sum]
  rw [show (∑ i : σ, pderiv i) p = ∑ i : σ,pderiv i p from by
    simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
      congrFun (map_sum Derivation.coeFnAddMonoidHom (fun i : σ=>pderiv i) Finset.univ) p]
  exact IsWeightedHomogeneous.sum _ _ _ (fun i _=>hp.pderiv (by omega))

lemma taylor_coeff_homogeneous (p : MvPolynomial σ ℚ) (k : ℤ)
    (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) (n : ℕ) :
    ((taylor p).coeff n).IsWeightedHomogeneous (fun _=>(1:ℤ)) (k-n) := by
  induction n generalizing p k with
  | zero => simpa using hp
  | succ n ih =>
    have h := congrArg (fun q : Polynomial (MvPolynomial σ ℚ)=>q.coeff n) (taylor_derivative p)
    rw [Polynomial.coeff_derivative] at h
    have hh := ih (D p) (k-1) (D_homogeneous p k hp)
    have hom : ((n+1 : ℕ) : MvPolynomial σ ℚ).IsWeightedHomogeneous (fun _=>(1:ℤ)) 0 := by
      simpa using isWeightedHomogeneous_C (fun _ : σ=>(1:ℤ)) ((n+1:ℕ):ℚ)
    have hn : ((n+1 : ℕ) : MvPolynomial σ ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hm : (((n+1:ℕ):MvPolynomial σ ℚ) * (taylor p).coeff (n+1)).IsWeightedHomogeneous
        (fun _=>(1:ℤ)) (k-1-n) := by
      rw [mul_comm,Nat.cast_add,Nat.cast_one,h]
      exact hh
    have result := Homogeneity.of_mul _ _ hom hn hm
    have he : k-1-(n:ℤ)-0 = k-((n+1:ℕ):ℤ) := by push_cast <;> ring
    rwa [he] at result

end ElementaryPositivity.CommonTranslation

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_Eval
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.IndependentCenters
variable {A : Type*} [CommRing A] [Algebra ℚ A]

noncomputable def eval (z w : ℚ) : Polynomial (Polynomial A) →+* A :=
  (Polynomial.evalRingHom (algebraMap ℚ A z)).comp
    (Polynomial.evalRingHom (algebraMap ℚ (Polynomial A) w))

noncomputable def substitute (r : Polynomial (Polynomial A)) :
    Polynomial (Polynomial A) →+* Polynomial (Polynomial A) :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C) r) Polynomial.X

omit [Algebra ℚ A] in
@[simp] lemma substitute_C_C (r : Polynomial (Polynomial A)) (a : A) :
    substitute r (Polynomial.C (Polynomial.C a))=Polynomial.C (Polynomial.C a) := by
  simp [substitute]

omit [Algebra ℚ A] in
@[simp] lemma substitute_C_X (r : Polynomial (Polynomial A)) :
    substitute r (Polynomial.C Polynomial.X)=r := by
  simp [substitute]

omit [Algebra ℚ A] in
@[simp] lemma substitute_X (r : Polynomial (Polynomial A)) :
    substitute r Polynomial.X=Polynomial.X := by
  simp [substitute]

@[simp] lemma eval_C_C (z w : ℚ) (a : A) :
    eval z w (Polynomial.C (Polynomial.C a))=a := by
  change ((Polynomial.C (Polynomial.C a)).eval _).eval _=a
  rw [Polynomial.eval_C,Polynomial.eval_C]

@[simp] lemma eval_C_X (z w : ℚ) :
    eval (A:=A) z w (Polynomial.C Polynomial.X)=algebraMap ℚ A z := by
  change ((Polynomial.C Polynomial.X).eval _).eval _=_
  rw [Polynomial.eval_C,Polynomial.eval_X]

@[simp] lemma eval_X (z w : ℚ) :
    eval (A:=A) z w Polynomial.X=algebraMap ℚ A w := by
  change ((Polynomial.X : Polynomial (Polynomial A)).eval _).eval _=_
  rw [Polynomial.eval_X,Polynomial.algebraMap_apply,Polynomial.eval_C]

noncomputable def plus : Polynomial (Polynomial A) →+* Polynomial (Polynomial A) :=
  substitute (Polynomial.C Polynomial.X+Polynomial.X)
noncomputable def minus : Polynomial (Polynomial A) →+* Polynomial (Polynomial A) :=
  substitute (Polynomial.C Polynomial.X-Polynomial.X)

omit [Algebra ℚ A] in
lemma minus_plus : (minus (A:=A)).comp plus=RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply,minus,plus]
    · simp [RingHom.comp_apply,minus,plus]
  · simp [RingHom.comp_apply,minus,plus]

omit [Algebra ℚ A] in
@[simp] lemma minus_plus_apply (p : Polynomial (Polynomial A)) : minus (plus p)=p :=
  RingHom.congr_fun minus_plus p

lemma eval_plus (z w : ℚ) (p : Polynomial (Polynomial A)) :
    eval z w (plus p)=eval (z+w) w p := by
  have h : (eval (A:=A) z w).comp plus=eval (z+w) w := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        simp [RingHom.comp_apply,plus]
      · simp [RingHom.comp_apply,plus]
    · simp [RingHom.comp_apply,plus]
  exact RingHom.congr_fun h p

omit [Algebra ℚ A] in
lemma diagonal_dvd_of_relative_dvd (p : Polynomial (Polynomial A)) (m : ℕ)
    (h : Polynomial.C (Polynomial.X^m) ∣ plus p) :
    (Polynomial.C Polynomial.X-Polynomial.X)^m ∣ p := by
  obtain ⟨q,hq⟩ := h
  refine ⟨minus q,?_⟩
  have hm := congrArg minus hq
  rw [minus_plus_apply,map_mul] at hm
  simpa only [map_pow,minus,substitute_C_X] using hm

noncomputable def diagonal : Polynomial (Polynomial A) :=
  Polynomial.X-Polynomial.C Polynomial.X

def DiagonalDivides (m : ℕ) (p : Polynomial (Polynomial A)) : Prop :=
  diagonal^m ∣ p

omit [Algebra ℚ A] in
lemma diagonalDivides_of_relative (p : Polynomial (Polynomial A)) (m : ℕ)
    (h : Polynomial.C (Polynomial.X^m) ∣ plus p) : DiagonalDivides m p := by
  let : CommRing (Polynomial A) := inferInstance
  let : CommRing (Polynomial (Polynomial A)) := inferInstance
  have hd:=diagonal_dvd_of_relative_dvd p m h
  have ha : diagonal (A:=A) ∣ Polynomial.C Polynomial.X-Polynomial.X := by
    refine ⟨-1,?_⟩
    simp only [diagonal,mul_neg,mul_one,neg_sub]
  exact (pow_dvd_pow_of_dvd ha m).trans hd

end ElementaryPositivity.IndependentCenters

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_GradedBuilders
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity

@[instance_reducible]
noncomputable def gradedMonoidOfLaws {J : Type*} [AddMonoid J] {A : J → Type*}
    [GradedMonoid.GMul A] [GradedMonoid.GOne A]
    (h₁ : ∀ x : GradedMonoid A,1*x=x)
    (h₂ : ∀ x : GradedMonoid A,x*1=x)
    (h₃ : ∀ x y z : GradedMonoid A,x*y*z=x*(y*z)) : GradedMonoid.GMonoid A where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul := h₁
  mul_one := h₂
  mul_assoc := h₃

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentInfinity
attribute [-simp] _root_.OAI.ElementaryPositivity.LaurentAtInfinity.mulPolynomialCoeff_apply _root_.OAI.ElementaryPositivity.LaurentAtInfinity.mulPolynomial_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R S : Type*} [CommRing R] [CommRing S]

lemma polynomial_map (f : R →+* S) (p : Polynomial R) :
    mapRing f (polynomial p)=polynomial (p.map f) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | monomial n r => simp [polynomial_monomial]

lemma polynomial_coeff (p : Polynomial R) (n : ℕ) :
    (polynomial p).coeff (-(n:ℤ))=p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,coeff_add,Polynomial.coeff_add,hp,hq]
  | monomial k r => simp [polynomial_monomial,coeff_single,Polynomial.coeff_monomial,eq_comm]

lemma polynomial_coeff_positive (p : Polynomial R) (n : ℤ) (hn : 0<n) :
    (polynomial p).coeff n=0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,coeff_add,hp,hq,add_zero]
  | monomial k r =>
    rw [polynomial_monomial,coeff_single,ite_eq_right]
    omega

end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentAffineCancellation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.LaurentAtInfinity.mulPolynomialCoeff_apply _root_.OAI.ElementaryPositivity.LaurentAtInfinity.mulPolynomial_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R]

noncomputable def affinePolynomial (c : R) : Polynomial R := Polynomial.C c-Polynomial.X

@[simp] lemma polynomial_affinePolynomial (c : R) :
    polynomial (affinePolynomial c)=(affineUnit c : LaurentSeries R) := by
  simp [affinePolynomial]

lemma affineUnit_zpow_cancel (c : R) (e : ℤ) :
    ((affineUnit c)^e : (LaurentSeries R)ˣ).val *
       polynomial ((affinePolynomial c)^(-e).toNat)=
       polynomial ((affinePolynomial c)^e.toNat) := by
  rw [map_pow,map_pow,polynomial_affinePolynomial]
  have hi : e+((-e).toNat : ℤ)=(e.toNat : ℤ) := by omega
  have h : (affineUnit c)^e*(affineUnit c)^(-e).toNat=(affineUnit c)^e.toNat := by
    rw [←zpow_natCast,←zpow_add,hi,zpow_natCast]
  exact congrArg Units.val h

end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentFilteredMultiplication
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma coeff_mul_mem_of_pair (F G H : Submodule ℚ R)
    (hFG : ∀ x∈F,∀ y∈G,x*y∈H) (f g : LaurentSeries R)
    (hf : ∀ k,f.coeff k∈F) (hg : ∀ k,g.coeff k∈G) (k : ℤ) :
    (f*g).coeff k∈H := by
  classical
  rw [coeff_mul]
  exact H.sum_mem (fun ij hij=>hFG _ (hf _) _ (hg _))
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentProductNaturality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
variable {R S : Type*} [CommRing R] [CommRing S]
lemma mapRing_mul_polynomial (f : R →+* S) (K : LaurentSeries R) (p : Polynomial R) :
    mapRing f (K*polynomial p)=mapRing f K*polynomial (p.map f) := by
  rw [map_mul,polynomial_map]
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalPolynomialDivisibility
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SymbolCoordinates
open MvPolynomial
variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

noncomputable def coefficientMap (l : A →ₗ[ℚ] ℚ) :
    MvPolynomial σ A →ₗ[ℚ] MvPolynomial σ ℚ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap l).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)

@[simp] lemma coeff_coefficientMap (l : A →ₗ[ℚ] ℚ) (f : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (coefficientMap l f).coeff m=l (f.coeff m) := rfl

lemma coefficientMap_scalar_mul (l : A →ₗ[ℚ] ℚ) (p : MvPolynomial σ ℚ) (f : MvPolynomial σ A) :
    coefficientMap l (MvPolynomial.map (algebraMap ℚ A) p * f) = p * coefficientMap l f := by
  classical
  ext m
  simp only [coeff_coefficientMap,coeff_mul,coeff_map,map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simpa [Algebra.smul_def,smul_eq_mul] using
    l.map_smul (p.coeff x.1) (f.coeff x.2)

variable {ι : Type*} (b : Module.Basis ι ℚ A)

noncomputable def coordinate (i : ι) : MvPolynomial σ A →ₗ[ℚ] MvPolynomial σ ℚ :=
  coefficientMap ((Finsupp.lapply i).comp b.repr.toLinearMap)

@[simp] lemma coeff_coordinate (i : ι) (f : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (coordinate b i f).coeff m=b.repr (f.coeff m) i := rfl

lemma coordinate_scalar_mul (i : ι) (p : MvPolynomial σ ℚ) (f : MvPolynomial σ A) :
    coordinate b i (MvPolynomial.map (algebraMap ℚ A) p * f) = p * coordinate b i f :=
  coefficientMap_scalar_mul _ _ _

noncomputable def coordinateSupport (f : MvPolynomial σ A) : Finset ι := by
  classical
  exact f.support.biUnion (fun m=>(b.repr (f.coeff m)).support)

lemma coordinate_support_subset (f : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (b.repr (f.coeff m)).support ⊆ coordinateSupport b f := by
  classical
  intro i hi
  by_cases hm : m∈f.support
  · exact Finset.mem_biUnion.mpr ⟨m,hm,hi⟩
  · have hzero:=notMem_support_iff.mp hm
    simp [hzero] at hi

lemma reconstruct (f : MvPolynomial σ A) :
    (∑ i ∈ coordinateSupport b f,C (b i)*MvPolynomial.map (algebraMap ℚ A) (coordinate b i f))=f := by
  classical
  ext m
  simp only [coeff_sum,coeff_C_mul,coeff_map,coeff_coordinate]
  calc
    (∑ i ∈ coordinateSupport b f,b i * algebraMap ℚ A (b.repr (f.coeff m) i)) =
        ∑ i ∈ (b.repr (f.coeff m)).support,b.repr (f.coeff m) i • b i := by
      simp only [Algebra.smul_def,mul_comm]
      exact (Finset.sum_subset (coordinate_support_subset b f m) (by
        intro i hi hni
        simp [Finsupp.notMem_support_iff.mp hni])).symm
    _ = f.coeff m := b.linearCombination_repr _

theorem scalar_dvd_iff (p : MvPolynomial σ ℚ) (f : MvPolynomial σ A) :
    MvPolynomial.map (algebraMap ℚ A) p ∣ f ↔ ∀ i,p ∣ coordinate b i f := by
  classical
  constructor
  · rintro ⟨g,rfl⟩ i
    rw [coordinate_scalar_mul]
    exact dvd_mul_right p _
  · intro h
    choose g hg using h
    refine ⟨∑ i ∈ coordinateSupport b f,C (b i)*MvPolynomial.map (algebraMap ℚ A) (g i),?_⟩
    calc
      f = ∑ i ∈ coordinateSupport b f,C (b i)*MvPolynomial.map (algebraMap ℚ A) (coordinate b i f) :=
        (reconstruct b f).symm
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hg i,map_mul]
        ring

end ElementaryPositivity.SymbolCoordinates

namespace ElementaryPositivity.CenterCalculus
open MvPolynomial ElementaryPositivity.SymbolCoordinates
variable {A σ : Type*} [CommRing A] [Algebra ℚ A]

theorem product_dvd_of_scalar_factors {κ : Type*} (s : Finset κ)
    (p : κ → MvPolynomial σ ℚ) (q : MvPolynomial σ A)
    (hrel : (s : Set κ).Pairwise (fun i j => IsRelPrime (p i) (p j)))
    (h : ∀ i∈s, map (algebraMap ℚ A) (p i) ∣ q) :
    map (algebraMap ℚ A) (∏ i∈s,p i) ∣ q := by
  let b := Module.Free.chooseBasis ℚ A
  apply (scalar_dvd_iff b _ q).mpr
  intro k
  apply Finset.prod_dvd_of_isRelPrime hrel
  intro i hi
  exact (scalar_dvd_iff b (p i) q).mp (h i hi) k

end ElementaryPositivity.CenterCalculus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LaurentKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
namespace SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma realize_inverseKernelUnit (a : I → I → ℕ) (d e : I → ℕ) :
    mapRing (R:=S d ⊗[ℚ] S e) (S:=MvPolynomial (CellVars d e) ℚ) (tensorValueAlg d e).toRingHom (inverseKernelUnit a d e).val=(rawInverseKernelUnit a d e).val := by
  exact realize_separateSeries d e (rawInverseKernelUnit a d e).val (fun σ=>
    congrArg Units.val (rawInverseKernelUnit_symmetric a d e σ))

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_RestrictionB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree

noncomputable def tensorMap (A C : (I → ℕ) → CommAlgCat.{u} ℚ)
    (f : ∀ d, A d →ₐ[ℚ] C d) : (T : SplitTree I) → tensor A T →ₐ[ℚ] tensor C T
  | .leaf d => f d
  | .node l r => Algebra.TensorProduct.map (tensorMap A C f l) (tensorMap A C f r)

noncomputable def rawFamily (d : I → ℕ) : CommAlgCat.{u} ℚ := CommAlgCat.of ℚ (S d)

noncomputable def rawRestriction : (T : SplitTree I) → S T.dim →ₐ[ℚ] tensor rawFamily T
  | .leaf d => AlgHom.id ℚ (S d)
  | .node l r => (Algebra.TensorProduct.map (rawRestriction l) (rawRestriction r)).comp
      (restrictTensorAlg (firstCut l.dim r.dim))

noncomputable def quotientMap (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (T : SplitTree I) :
    tensor rawFamily T →ₐ[ℚ] tensor (quotientFamily a μ) T :=
  tensorMap rawFamily (quotientFamily a μ) (quotientAlg a μ) T

lemma restrictionB_square (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (T : SplitTree I) (h : T.OnSlope c η θ) :
    (restrictionB a c η hc θ T h).comp (quotientAlg a (slope c η) T.dim) =
      (quotientMap a (slope c η) T).comp (rawRestriction T) := by
  induction T with
  | leaf d => rfl
  | node l r ihl ihr =>
    apply AlgHom.ext
    intro f
    change (Algebra.TensorProduct.map (restrictionB a c η hc θ l h.1)
      (restrictionB a c η hc θ r h.2))
      (quotientTensor a (slope c η) l.dim r.dim (restrictTensor (firstCut l.dim r.dim) f)) =
        (Algebra.TensorProduct.map (quotientMap a (slope c η) l) (quotientMap a (slope c η) r))
          ((Algebra.TensorProduct.map (rawRestriction l) (rawRestriction r))
            (restrictTensor (firstCut l.dim r.dim) f))
    generalize restrictTensor (firstCut l.dim r.dim) f = t
    induction t using OAI.tensorInductionOn with
    | tmul x y =>
      change restrictionB a c η hc θ l h.1 (quotientAlg a (slope c η) l.dim x) ⊗ₜ[ℚ]
          restrictionB a c η hc θ r h.2 (quotientAlg a (slope c η) r.dim y) =
        quotientMap a (slope c η) l (rawRestriction l x) ⊗ₜ[ℚ]
          quotientMap a (slope c η) r (rawRestriction r y)
      exact congrArg₂ (fun x y => x ⊗ₜ[ℚ] y)
        (AlgHom.congr_fun (ihl h.1) x) (AlgHom.congr_fun (ihr h.2) y)
    | add x y hx hy => simp only [map_add,hx,hy]

lemma restrictionB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (T : SplitTree I) (h : T.OnSlope c η θ) (f : S T.dim) :
    restrictionB a c η hc θ T h (quotientAlg a (slope c η) T.dim f) =
      quotientMap a (slope c η) T (rawRestriction T f) :=
  AlgHom.congr_fun (restrictionB_square a c η hc θ T h) f

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ComponentB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma componentB_negative (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (hk : k<0) (f : B a μ d) : componentB a μ d k f = 0 := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change (destabilizingSpace a μ d).mkQ (componentS d k f) = 0
    have hs : componentS d k f=0 := Subtype.ext
      (homogeneous_negative_eq_zero _ (componentS_homogeneous d k f) hk)
    rw [hs,map_zero]

theorem componentB_finite_decomposition (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (f : B a μ d) :
    ∃ s : Finset ℤ, (∀ k∉s,componentB a μ d k f=0) ∧
      (∑ k ∈ s,componentB a μ d k f)=f := by
  classical
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    refine ⟨degreeSet f.val,?_,?_⟩
    · intro k hk
      change (destabilizingSpace a μ d).mkQ (componentS d k f) = 0
      have hs : componentS d k f=0 := by
        apply Subtype.ext
        apply weightedHomogeneousComponent_eq_zero'
        intro x hx
        exact fun h=>hk (Finset.mem_image.mpr ⟨x,hx,h⟩)
      rw [hs,map_zero]
    · change (∑ k ∈ degreeSet f.val,(destabilizingSpace a μ d).mkQ (componentS d k f)) =
        (destabilizingSpace a μ d).mkQ f
      rw [← map_sum,sum_componentS]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TaylorSCoeffHomogeneous
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable instance degreesDecidableEq (T : SplitTree I) : DecidableEq T.Degrees := Classical.decEq _

omit [Fintype I] [DecidableEq I] in
lemma totalDegree_nonnegative (T : SplitTree I) (k : T.Degrees) (h : T.NonnegativeDegree k) :
    0≤T.totalDegree k := by
  induction T with
  | leaf d => exact h
  | node l r ihl ihr => exact add_nonneg (ihl k.1 h.1) (ihr k.2 h.2)

lemma componentTensor_negative (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (k : T.Degrees) (h : ¬T.NonnegativeDegree k) :
    componentTensor a μ T k=0 := by
  classical
  induction T with
  | leaf d =>
    apply LinearMap.ext
    intro f
    exact componentB_negative a μ d k (lt_of_not_ge h) f
  | node l r ihl ihr =>
    change TensorProduct.map (componentTensor a μ l k.1) (componentTensor a μ r k.2)=0
    by_cases hl : l.NonnegativeDegree k.1
    · have hr : ¬r.NonnegativeDegree k.2 := fun hr=>h ⟨hl,hr⟩
      rw [ihr k.2 hr,TensorProduct.map_zero_right]
    · rw [ihl k.1 hl,TensorProduct.map_zero_left]

theorem componentTensor_finite_decomposition (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (f : tensor (quotientFamily a μ) T) :
    ∃ s : Finset T.Degrees, (∀ k∉s,componentTensor a μ T k f=0) ∧
      (∑ k ∈ s,componentTensor a μ T k f)=f := by
  classical
  induction T with
  | leaf d => exact componentB_finite_decomposition a μ d f
  | node A B ihA ihB =>
    induction f using OAI.tensorInductionOn with
    | tmul x y =>
      obtain ⟨s,hs,he⟩ := ihA x
      obtain ⟨t,ht,hf⟩ := ihB y
      refine ⟨s×ˢt,?_,?_⟩
      · intro k hk
        change componentTensor a μ A k.1 x ⊗ₜ[ℚ] componentTensor a μ B k.2 y = 0
        by_cases hx : k.1∈s
        · have hy : k.2∉t := fun hy=>hk (Finset.mem_product.mpr ⟨hx,hy⟩)
          rw [ht _ hy,TensorProduct.tmul_zero]
        · rw [hs _ hx,TensorProduct.zero_tmul]
      · change (∑ k ∈ s×ˢt,componentTensor a μ A k.1 x ⊗ₜ[ℚ] componentTensor a μ B k.2 y)=x⊗ₜ[ℚ]y
        rw [Finset.sum_product]
        simp_rw [← TensorProduct.tmul_sum]
        rw [← TensorProduct.sum_tmul,he,hf]
    | add x y hx hy =>
      obtain ⟨s,hs,he⟩ := hx
      obtain ⟨t,ht,hf⟩ := hy
      refine ⟨s∪t,?_,?_⟩
      · intro k hk
        rw [map_add,hs k (fun h=>hk (Finset.mem_union_left t h)),
          ht k (fun h=>hk (Finset.mem_union_right s h)),add_zero]
      · simp only [map_add,Finset.sum_add_distrib]
        have hx : (∑ k ∈ s∪t,componentTensor a μ (.node A B) k x)=x := by
          exact (Finset.sum_subset Finset.subset_union_left
            (fun k hk hks=>hs k hks)).symm.trans he
        have hy : (∑ k ∈ s∪t,componentTensor a μ (.node A B) k y)=y := by
          exact (Finset.sum_subset Finset.subset_union_right
            (fun k hk hkt=>ht k hkt)).symm.trans hf
        rw [hx,hy]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Interaction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

def interaction (a : I → I → ℕ) (d e : I → ℕ) : ℤ :=
  ∑ i,∑ j,(a i j:ℤ)*d i*e j

omit [DecidableEq I] in
lemma interaction_nonnegative (a : I → I → ℕ) (d e : I → ℕ) : 0 ≤ interaction a d e := by
  exact Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)))

omit [DecidableEq I] in
lemma interaction_add (a : I → I → ℕ) (d e : I → ℕ) :
    interaction a (d+e) (d+e) = interaction a d d + interaction a d e +
      interaction a e d + interaction a e e := by
  simp only [interaction,Pi.add_apply,Nat.cast_add,mul_add,add_mul,Finset.sum_add_distrib]
  ring

omit [DecidableEq I] in
lemma eulerForm_lower (a : I → I → ℕ) (d : I → ℕ) : -interaction a d d≤eulerForm a d d := by
  have h : 0≤∑ i,(d i:ℤ)*d i := Finset.sum_nonneg (fun i _=>mul_self_nonneg _)
  change -interaction a d d≤(∑ i,(d i:ℤ)*d i)-interaction a d d
  omega

omit [DecidableEq I] in
lemma SplitTree.doubleShift_lower (a : I → I → ℕ) (T : SplitTree I) :
    -interaction a T.dim T.dim ≤ T.doubleShift a := by
  induction T with
  | leaf d => exact eulerForm_lower a d
  | node l r ihl ihr =>
    change -interaction a (l.dim+r.dim) (l.dim+r.dim)≤l.doubleShift a+r.doubleShift a
    rw [interaction_add]
    have h1 := interaction_nonnegative a l.dim r.dim
    have h2 := interaction_nonnegative a r.dim l.dim
    omega

theorem sourceFiltration_lower (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) :
    sourceFiltration a c η hc θ d (-interaction a d d)=⊤ := by
  classical
  apply top_unique
  intro f hf T hT hs hd k z hw
  have hn : ¬T.NonnegativeDegree k := by
    intro hh
    have ht := T.totalDegree_nonnegative k hh
    have hl := T.doubleShift_lower a
    rw [hd] at hl
    omega
  unfold restrictionTest
  rw [SplitTree.componentTensor_negative a _ T k hn]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialCoeffLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def polynomialMapLinear {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (l : R →ₗ[ℚ] S) : Polynomial R →ₗ[ℚ] Polynomial S where
  toFun p := Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange l l.map_zero))
  map_add' p q := by
    ext s
    exact l.map_add (p.coeff s) (q.coeff s)
  map_smul' r p := by
    ext s
    exact l.map_smul r (p.coeff s)

@[simp] lemma polynomialMapLinear_coeff {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (l : R →ₗ[ℚ] S) (p : Polynomial R) (n : ℕ) :
    (polynomialMapLinear l p).coeff n=l (p.coeff n) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_BothTaylorB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma polynomial_eq_of_rat_evals {A : Type*} [CommRing A] [Algebra ℚ A]
    (p q : Polynomial A) (h : ∀ t : ℚ,p.eval (algebraMap ℚ A t)=q.eval (algebraMap ℚ A t)) :
    p=q := by
  have hz : p-q=0 := by
    ext n
    have hn := ElementaryPositivity.CommonTranslation.polynomial_coeff_mem (⊥ : Submodule ℚ A)
      (p-q) (by intro t; simp [Polynomial.eval_sub,h t]) n
    simpa only [Submodule.mem_bot,Polynomial.coeff_zero] using hn
  exact sub_eq_zero.mp hz

lemma taylorB_eval (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : B a μ d) (t : ℚ) :
    (taylorB a μ d f).eval (algebraMap ℚ (B a μ d) t)=translationB a μ d t f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change (taylorB a μ d (quotientAlg a μ d f)).eval _ =
      quotientAlg a μ d (translationS d t f)
    rw [taylorB_mk,eval_map_rat,taylorS_eval]

@[simp] lemma polynomialMapLinear_monomial {A D : Type*} [CommRing A] [CommRing D]
    [Algebra ℚ A] [Algebra ℚ D] (l : A →ₗ[ℚ] D) (n : ℕ) (a : A) :
    polynomialMapLinear l (Polynomial.monomial n a)=Polynomial.monomial n (l a) := by
  ext m
  simp only [polynomialMapLinear_coeff,Polynomial.coeff_monomial]
  split_ifs <;> simp

lemma polynomialMapLinear_eval_rat {A D : Type*} [CommRing A] [CommRing D]
    [Algebra ℚ A] [Algebra ℚ D] (l : A →ₗ[ℚ] D) (p : Polynomial A) (t : ℚ) :
    (polynomialMapLinear l p).eval (algebraMap ℚ D t)=l (p.eval (algebraMap ℚ A t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Polynomial.eval_add,hp,hq]
  | monomial n a =>
    rw [polynomialMapLinear_monomial,Polynomial.eval_monomial,Polynomial.eval_monomial]
    rw [← map_pow,← map_pow,mul_comm (l a),mul_comm a,← Algebra.smul_def,← Algebra.smul_def,map_smul]

noncomputable def evalTwo {A : Type*} [CommRing A] [Algebra ℚ A]
    (p : Polynomial (Polynomial A)) (z w : ℚ) : A :=
  (p.eval (algebraMap ℚ (Polynomial A) w)).eval (algebraMap ℚ A z)

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma relativeTaylorB_eval (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d ⊗[ℚ] B a μ e) (z : ℚ) :
    (relativeTaylorB a μ d e x).eval (algebraMap ℚ (B a μ d ⊗[ℚ] B a μ e) z)=
      TensorProduct.map (translationB a μ d z) (LinearMap.id : B a μ e →ₗ[ℚ] B a μ e) x := by
  induction x using OAI.tensorInductionOn with
  | tmul f g =>
    change (Polynomial.map (Algebra.TensorProduct.includeLeft :
      B a μ d →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e).toRingHom (taylorB a μ d f) *
      Polynomial.C (1 ⊗ₜ[ℚ] g)).eval _ = _
    rw [Polynomial.eval_mul,eval_map_rat,taylorB_eval,Polynomial.eval_C]
    change (translationB a μ d z f ⊗ₜ[ℚ] 1)*(1 ⊗ₜ[ℚ] g)=_
    rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
    rfl
  | add x y hx hy => simp only [map_add,Polynomial.eval_add,hx,hy]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DimensionEquivS
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centerTranslation_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def dimensionEquivS {d e : I → ℕ} (h : d=e) : S d ≃ₐ[ℚ] S e := by
  subst e
  exact AlgEquiv.refl

omit [Fintype I] [DecidableEq I] in
lemma dimensionEquivS_val {d e : I → ℕ} (h : d=e) (f : S d) :
    (dimensionEquivS h f).val=rename (Equiv.sigmaCongrRight
      (fun i=>Equiv.cast (congrArg Fin (congrFun h i)))) f.val := by
  subst e
  change f.val=rename id f.val
  simp only [rename_id,AlgHom.id_apply]

@[reducible] def Vars : SplitTree I → Type u
  | .leaf d => Σ i,Fin (d i)
  | .node l r => l.Vars ⊕ r.Vars

noncomputable def varEquiv : (T : SplitTree I) → T.Vars ≃ (Σ i,Fin (T.dim i))
  | .leaf _ => Equiv.refl _
  | .node l r => (Equiv.sumCongr (varEquiv l) (varEquiv r)).trans
      (cutSplit (firstCut l.dim r.dim))

noncomputable def tensorValue : (T : SplitTree I) → tensor rawFamily T →ₐ[ℚ] MvPolynomial T.Vars ℚ
  | .leaf d => (symmetricSpace d).val
  | .node l r => (tensorEquivSum ℚ _ _ ℚ).toAlgHom.comp
      (Algebra.TensorProduct.map (tensorValue l) (tensorValue r))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma tensorValue_tmul (l r : SplitTree I) (x : tensor rawFamily l) (y : tensor rawFamily r) :
    tensorValue (.node l r) (x ⊗ₜ[ℚ] y)=
      rename Sum.inl (tensorValue l x)*rename Sum.inr (tensorValue r y) := by
  exact RawShuffle.tensorEquivSum_tmul _ _

omit [Fintype I] [DecidableEq I] in
lemma tensorValue_injective (T : SplitTree I) : Function.Injective (tensorValue T) := by
  induction T with
  | leaf d => exact Subtype.val_injective
  | node l r ihl ihr =>
    exact (tensorEquivSum ℚ _ _ ℚ).injective.comp
      (TensorProduct.map_injective_of_flat_flat (tensorValue l).toLinearMap
        (tensorValue r).toLinearMap ihl ihr)

lemma tensorValue_rawRestriction (T : SplitTree I) (f : S T.dim) :
    tensorValue T (rawRestriction T f)=rename T.varEquiv.symm f.val := by
  induction T with
  | leaf d =>
    change f.val=rename id f.val
    simp only [rename_id,AlgHom.id_apply]
  | node l r ihl ihr =>
    have h : ∀ x : S l.dim ⊗[ℚ] S r.dim,
        tensorValue (.node l r) (Algebra.TensorProduct.map (rawRestriction l) (rawRestriction r) x)=
          rename (Sum.map l.varEquiv.symm r.varEquiv.symm) (RawShuffle.tensorValue l.dim r.dim x) := by
      intro x
      induction x using OAI.tensorInductionOn with
      | tmul x y =>
        rw [Algebra.TensorProduct.map_tmul,tensorValue_tmul,ihl,ihr,
          RawShuffle.tensorValue_tmul,map_mul,rename_rename,rename_rename,rename_rename,rename_rename]
        rfl
      | add x y hx hy => simp only [map_add,hx,hy]
    change tensorValue (.node l r) (Algebra.TensorProduct.map (rawRestriction l) (rawRestriction r)
      (restrictTensor (firstCut l.dim r.dim) f)) = _
    rw [h,RawShuffle.tensorValue_restrictTensor,rename_rename]
    rfl

noncomputable def packFiberEquiv (d : I → ℕ) (i : I) :
    {x : (Σ j,Fin (d j)) // x.1=i} ≃ Fin (d i) where
  toFun x := x.property ▸ x.val.2
  invFun x := ⟨⟨i,x⟩,rfl⟩
  left_inv x := by
    rcases x with ⟨⟨j,x⟩,h⟩
    dsimp at h
    subst j
    rfl
  right_inv x := rfl

omit [Fintype I] [DecidableEq I] in
lemma pack_equiv_eq_packAction (d : I → ℕ) (e : Equiv.Perm (Σ i,Fin (d i)))
    (h : ∀ x,(e x).1=x.1) :
    ∃ σ : ∀ i,Equiv.Perm (Fin (d i)), ShufflePolynomiality.packAction (fun i=>Fin (d i)) σ=e := by
  let E : ∀ i,{x : (Σ j,Fin (d j)) // x.1=i} ≃ {x : (Σ j,Fin (d j)) // x.1=i} :=
    fun i => e.subtypeEquiv (by intro x; simp only [h x])
  let σ : ∀ i,Equiv.Perm (Fin (d i)) := fun i =>
    (packFiberEquiv d i).symm.trans ((E i).trans (packFiberEquiv d i))
  refine ⟨σ,?_⟩
  apply Equiv.ext
  rintro ⟨i,x⟩
  exact congrArg Subtype.val ((packFiberEquiv d i).symm_apply_apply
    (E i ⟨⟨i,x⟩,rfl⟩))

omit [Fintype I] [DecidableEq I] in
lemma rename_pack_preserving (d : I → ℕ) (e : Equiv.Perm (Σ i,Fin (d i)))
    (h : ∀ x,(e x).1=x.1) (f : S d) : rename e f.val=f.val := by
  obtain ⟨σ,rfl⟩ := pack_equiv_eq_packAction d e h
  exact f.property σ

lemma rawRestriction_regroup_permuted {T U : SplitTree I} (h : T.dim=U.dim)
    (e : T.Vars ≃ U.Vars) (σ : Equiv.Perm (Σ i,Fin (T.dim i)))
    (hσ : ∀ x,(σ x).1=x.1)
    (he : ∀ x, U.varEquiv (e x)=Equiv.sigmaCongrRight
      (fun i=>Equiv.cast (congrArg Fin (congrFun h i))) (σ (T.varEquiv x)))
    (f : S T.dim) :
    rename e (tensorValue T (rawRestriction T f))=
      tensorValue U (rawRestriction U (dimensionEquivS h f)) := by
  rw [tensorValue_rawRestriction,tensorValue_rawRestriction,dimensionEquivS_val,rename_rename]
  have hf := rename_pack_preserving T.dim σ hσ f
  conv_rhs => arg 2; rw [← hf]
  rw [rename_rename,rename_rename]
  congr 2
  funext x
  apply U.varEquiv.injective
  simp only [Function.comp_apply,he,Equiv.apply_symm_apply]

@[reducible] def packIndex : (T : SplitTree I) → T.Vars → I
  | .leaf _, x => x.1
  | .node l _, .inl x => l.packIndex x
  | .node _ r, .inr x => r.packIndex x

omit [Fintype I] [DecidableEq I] in
lemma varEquiv_fst (T : SplitTree I) (x : T.Vars) : (T.varEquiv x).1=T.packIndex x := by
  induction T with
  | leaf d => rfl
  | node l r ihl ihr =>
    cases x with
    | inl x => exact ihl x
    | inr x => exact ihr x

omit [Fintype I] [DecidableEq I] in
lemma varEquiv_symm_packIndex (T : SplitTree I) (x : Σ i,Fin (T.dim i)) :
    T.packIndex (T.varEquiv.symm x)=x.1 := by
  rw [← varEquiv_fst,Equiv.apply_symm_apply]

lemma rawRestriction_regroup_of_pack_preserving {T U : SplitTree I} (h : T.dim=U.dim)
    (e : T.Vars ≃ U.Vars) (he : ∀ x,U.packIndex (e x)=T.packIndex x)
    (f : S T.dim) :
    rename e (tensorValue T (rawRestriction T f))=
      tensorValue U (rawRestriction U (dimensionEquivS h f)) := by
  let C : (Σ i,Fin (T.dim i)) ≃ (Σ i,Fin (U.dim i)) :=
    Equiv.sigmaCongrRight (fun i=>Equiv.cast (congrArg Fin (congrFun h i)))
  let σ : Equiv.Perm (Σ i,Fin (T.dim i)) :=
    T.varEquiv.symm.trans (e.trans (U.varEquiv.trans C.symm))
  have hσ : ∀ x,(σ x).1=x.1 := by
    intro x
    change (U.varEquiv (e (T.varEquiv.symm x))).1=x.1
    rw [varEquiv_fst,he,varEquiv_symm_packIndex]
  apply rawRestriction_regroup_permuted h e σ hσ
  intro x
  change U.varEquiv (e x)=C (C.symm (U.varEquiv (e (T.varEquiv.symm (T.varEquiv x)))))
  rw [Equiv.symm_apply_apply,Equiv.apply_symm_apply]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Regroup
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

inductive Regroup : SplitTree I → SplitTree I → Type u
  | refl (T) : Regroup T T
  | assoc (T U V) : Regroup (.node (.node T U) V) (.node T (.node U V))
  | swap (T U) : Regroup (.node T U) (.node U T)
  | node {T U V W} : Regroup T U → Regroup V W → Regroup (.node T V) (.node U W)
  | trans {T U V} : Regroup T U → Regroup U V → Regroup T V

namespace Regroup
noncomputable def vars {T U : SplitTree I} : Regroup T U → T.Vars ≃ U.Vars
  | .refl _ => Equiv.refl _
  | .assoc _ _ _ => Equiv.sumAssoc _ _ _
  | .swap _ _ => Equiv.sumComm _ _
  | .node f g => Equiv.sumCongr f.vars g.vars
  | .trans f g => f.vars.trans g.vars

omit [Fintype I] [DecidableEq I] in
lemma pack {T U : SplitTree I} (e : Regroup T U) (x : T.Vars) :
    U.packIndex (e.vars x)=T.packIndex x := by
  induction e with
  | refl T => rfl
  | assoc T U V => rcases x with (x|x)|x <;> rfl
  | swap T U => cases x <;> rfl
  | node f g ihf ihg => cases x with
    | inl x => exact ihf x
    | inr x => exact ihg x
  | trans f g ihf ihg => exact (ihg (f.vars x)).trans (ihf x)

omit [Fintype I] [DecidableEq I] in
lemma dimension {T U : SplitTree I} (e : Regroup T U) : T.dim=U.dim := by
  induction e with
  | refl T => rfl
  | assoc T U V => exact add_assoc _ _ _
  | swap T U => exact add_comm _ _
  | node f g ihf ihg => exact congrArg₂ (·+·) ihf ihg
  | trans f g ihf ihg => exact ihf.trans ihg

noncomputable def equivalence (A : (I → ℕ) → CommAlgCat.{u} ℚ)
    {T U : SplitTree I} : Regroup T U → tensor A T ≃ₐ[ℚ] tensor A U
  | .refl _ => AlgEquiv.refl
  | .assoc T U V => Algebra.TensorProduct.assoc ℚ ℚ ℚ (tensor A T) (tensor A U) (tensor A V)
  | .swap T U => Algebra.TensorProduct.comm ℚ (tensor A T) (tensor A U)
  | .node f g => Algebra.TensorProduct.congr (f.equivalence A) (g.equivalence A)
  | .trans f g => (f.equivalence A).trans (g.equivalence A)

omit [Fintype I] [DecidableEq I] in
lemma tensorMap_natural (A C : (I → ℕ) → CommAlgCat.{u} ℚ) (f : ∀ d,A d →ₐ[ℚ] C d)
    {T U : SplitTree I} (e : Regroup T U) (x : tensor A T) :
    e.equivalence C (tensorMap A C f T x)=tensorMap A C f U (e.equivalence A x) := by
  induction e with
  | refl T => rfl
  | assoc T U V =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x z =>
      induction x using OAI.tensorInductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
      | tmul x y => rfl
  | swap T U =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y => rfl
  | node e g ihe ihg =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change e.equivalence C (tensorMap A C f _ x) ⊗ₜ[ℚ]
          g.equivalence C (tensorMap A C f _ y)=
        tensorMap A C f _ (e.equivalence A x) ⊗ₜ[ℚ]
          tensorMap A C f _ (g.equivalence A y)
      rw [ihe,ihg]
  | trans e g ihe ihg =>
    change g.equivalence C (e.equivalence C (tensorMap A C f _ x))=_
    rw [ihe,ihg]
    rfl

omit [Fintype I] [DecidableEq I] in
lemma tensorValue_natural {T U : SplitTree I} (e : Regroup T U) (x : tensor rawFamily T) :
    tensorValue U (e.equivalence rawFamily x)=rename e.vars (tensorValue T x) := by
  induction e with
  | refl T =>
    change tensorValue T x=rename id (tensorValue T x)
    simp only [rename_id,AlgHom.id_apply]
  | assoc T U V =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x z =>
      induction x using OAI.tensorInductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
      | tmul x y =>
        change tensorValue (.node T (.node U V)) (x ⊗ₜ[ℚ] (y ⊗ₜ[ℚ] z)) = _
        rw [tensorValue_tmul T (.node U V),tensorValue_tmul U V,
          tensorValue_tmul (.node T U) V,tensorValue_tmul T U]
        simp only [map_mul,rename_rename]
        exact (mul_assoc _ _ _).symm
  | swap T U =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change tensorValue (.node U T) (y ⊗ₜ[ℚ] x)=_
      rw [tensorValue_tmul U T,tensorValue_tmul T U]
      simp only [map_mul,rename_rename]
      exact mul_comm _ _
  | node e g ihe ihg =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change tensorValue (.node _ _) (e.equivalence rawFamily x ⊗ₜ[ℚ] g.equivalence rawFamily y)=_
      rw [tensorValue_tmul,ihe,ihg,tensorValue_tmul,map_mul,rename_rename,rename_rename,rename_rename,rename_rename]
      rfl
  | trans e g ihe ihg =>
    change tensorValue _ (g.equivalence rawFamily (e.equivalence rawFamily x))=_
    rw [ihg,ihe,rename_rename]
    rfl

lemma rawRestriction_natural {T U : SplitTree I} (e : Regroup T U) (f : S T.dim) :
    e.equivalence rawFamily (rawRestriction T f)=
      rawRestriction U (dimensionEquivS e.dimension f) := by
  apply tensorValue_injective U
  rw [tensorValue_natural]
  exact rawRestriction_regroup_of_pack_preserving e.dimension e.vars e.pack f

lemma dimensionEquivB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (h : d=e) (f : S d) :
    dimensionEquivB a μ h (quotientAlg a μ d f)=
      quotientAlg a μ e (dimensionEquivS h f) := by
  subst e
  rfl

lemma restrictionB_natural (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) :
    e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
        (restrictionB a c η hc θ T hT f)=
      restrictionB a c η hc θ U hU
        (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
        (restrictionB a c η hc θ T hT (quotientAlg a _ T.dim f))=
      restrictionB a c η hc θ U hU
        (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension (quotientAlg a _ T.dim f))
    rw [dimensionEquivB_mk,restrictionB_mk,restrictionB_mk]
    change e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
      (tensorMap rawFamily (quotientFamily a (SlopeArithmetic.slope c η))
        (quotientAlg a (SlopeArithmetic.slope c η)) T (rawRestriction T f))=_
    erw [tensorMap_natural]
    rw [rawRestriction_natural]
    rfl

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Centers
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma extendPolynomial_comp {A B C α β γ : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C]
    (f : A →ₐ[ℚ] B) (g : B →ₐ[ℚ] C) (j : α → β) (k : β → γ) (p : MvPolynomial α A) :
    extendPolynomial g k (extendPolynomial f j p)=extendPolynomial (g.comp f) (k∘j) p := by
  simp only [extendPolynomial,AlgHom.comp_apply,AlgHom.restrictScalars_apply,mapAlgHom_apply,
    map_rename,rename_rename,map_map]
  rfl

namespace Regroup
noncomputable def centers {T U : SplitTree I} : Regroup T U → T.Centers ≃ U.Centers
  | .refl _ => Equiv.refl _
  | .assoc _ _ _ => Equiv.sumAssoc _ _ _
  | .swap _ _ => Equiv.sumComm _ _
  | .node f g => Equiv.sumCongr f.centers g.centers
  | .trans f g => f.centers.trans g.centers

omit [Fintype I] [DecidableEq I] in
lemma centerTranslation_natural (A : (I → ℕ) → CommAlgCat.{u} ℚ)
    (τ : ∀ d,A d →ₐ[ℚ] Polynomial (A d)) {T U : SplitTree I}
    (e : Regroup T U) (x : tensor A T) :
    centerTranslation A τ U (e.equivalence A x)=
      extendPolynomial (e.equivalence A).toAlgHom e.centers (centerTranslation A τ T x) := by
  induction e with
  | refl T =>
    change centerTranslation A τ T x=
      rename id (map (RingHom.id _) (centerTranslation A τ T x))
    simp only [map_id,rename_id,AlgHom.id_apply]
  | assoc T U V =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x z =>
      induction x using OAI.tensorInductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
      | tmul x y =>
        change centerTranslation A τ (.node T (.node U V)) (x ⊗ₜ[ℚ] (y ⊗ₜ[ℚ] z))=_
        rw [centerTranslation_tmul A τ T (.node U V),centerTranslation_tmul A τ U V,
          centerTranslation_tmul A τ (.node T U) V,centerTranslation_tmul A τ T U]
        simp only [map_mul,extendPolynomial_comp]
        rw [mul_assoc]
        congr 1
  | swap T U =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change centerTranslation A τ (.node U T) (y ⊗ₜ[ℚ] x)=_
      rw [centerTranslation_tmul A τ U T,centerTranslation_tmul A τ T U,map_mul,
        extendPolynomial_comp,extendPolynomial_comp,mul_comm]
      congr 1
  | node e g ihe ihg =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change centerTranslation A τ (.node _ _) (e.equivalence A x ⊗ₜ[ℚ] g.equivalence A y)=_
      rw [centerTranslation_tmul,ihe,ihg,centerTranslation_tmul,map_mul,
        extendPolynomial_comp,extendPolynomial_comp,extendPolynomial_comp,extendPolynomial_comp]
      congr 1 <;> congr 2 <;> apply AlgHom.ext <;> intro t
      · change e.equivalence A t ⊗ₜ[ℚ] (1 : tensor A _) =
          e.equivalence A t ⊗ₜ[ℚ] g.equivalence A 1
        rw [map_one]
      · change (1 : tensor A _) ⊗ₜ[ℚ] g.equivalence A t =
          e.equivalence A 1 ⊗ₜ[ℚ] g.equivalence A t
        rw [map_one]
  | trans e g ihe ihg =>
    change centerTranslation A τ _ (g.equivalence A (e.equivalence A x))=_
    rw [ihg,ihe,extendPolynomial_comp]
    rfl

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

namespace ElementaryPositivity.RawShuffle.SplitTree.Regroup
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma centeredRestrictionB_natural (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) :
    centeredRestrictionB a c η hc θ U hU
        (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f)=
      extendPolynomial (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
        e.centers (centeredRestrictionB a c η hc θ T hT f) := by
  change centerTranslation _ _ U (restrictionB a c η hc θ U hU
    (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f))=_
  rw [← restrictionB_natural a c η hc θ e hT hU f]
  erw [centerTranslation_natural]
  rfl

lemma extendPolynomial_coeff {A C α β : Type*} [CommRing A] [CommRing C]
    [Algebra ℚ A] [Algebra ℚ C] (f : A →ₐ[ℚ] C) (e : α ≃ β)
    (p : MvPolynomial α A) (z : α →₀ ℕ) :
    (extendPolynomial f e p).coeff (z.mapDomain e)=f (p.coeff z) := by
  change (rename e (map f.toRingHom p)).coeff (z.mapDomain e)=_
  rw [coeff_rename_mapDomain e e.injective,coeff_map]
  rfl

lemma centeredRestrictionB_coeff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) (z : T.Centers →₀ ℕ) :
    (centeredRestrictionB a c η hc θ U hU
        (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f)).coeff (z.mapDomain e.centers)=
      e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
        ((centeredRestrictionB a c η hc θ T hT f).coeff z) := by
  rw [centeredRestrictionB_natural]
  exact extendPolynomial_coeff _ _ _ _

end ElementaryPositivity.RawShuffle.SplitTree.Regroup

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace Regroup
noncomputable def degrees {T U : SplitTree I} : Regroup T U → T.Degrees ≃ U.Degrees
  | .refl _ => Equiv.refl _
  | .assoc _ _ _ => Equiv.prodAssoc _ _ _
  | .swap _ _ => Equiv.prodComm _ _
  | .node f g => Equiv.prodCongr f.degrees g.degrees
  | .trans f g => f.degrees.trans g.degrees

omit [Fintype I] [DecidableEq I] in
lemma totalDegree {T U : SplitTree I} (e : Regroup T U) (k : T.Degrees) :
    U.totalDegree (e.degrees k)=T.totalDegree k := by
  induction e with
  | refl T => rfl
  | assoc T U V => exact (add_assoc _ _ _).symm
  | swap T U => exact add_comm _ _
  | node e f ihe ihf => exact congrArg₂ (·+·) (ihe k.1) (ihf k.2)
  | trans e f ihe ihf => exact (ihf (e.degrees k)).trans (ihe k)

omit [DecidableEq I] in
lemma doubleShift (a : I → I → ℕ) {T U : SplitTree I} (e : Regroup T U) :
    U.doubleShift a=T.doubleShift a := by
  induction e with
  | refl T => rfl
  | assoc T U V => exact (add_assoc _ _ _).symm
  | swap T U => exact add_comm _ _
  | node e f ihe ihf => exact congrArg₂ (·+·) ihe ihf
  | trans e f ihe ihf => exact ihf.trans ihe

omit [DecidableEq I] in
lemma onSlope (c η : I → ℝ) (θ : ℝ) {T U : SplitTree I} (e : Regroup T U) :
    T.OnSlope c η θ → U.OnSlope c η θ := by
  induction e with
  | refl T => exact id
  | assoc T U V => exact fun h=>⟨h.1.1,h.1.2,h.2⟩
  | swap T U => exact fun h=>⟨h.2,h.1⟩
  | node e f ihe ihf => exact fun h=>⟨ihe h.1,ihf h.2⟩
  | trans e f ihe ihf => exact ihf∘ihe

lemma componentTensor_natural (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {T U : SplitTree I} (e : Regroup T U) (k : T.Degrees)
    (x : tensor (quotientFamily a μ) T) :
    e.equivalence (quotientFamily a μ) (componentTensor a μ T k x)=
      componentTensor a μ U (e.degrees k) (e.equivalence (quotientFamily a μ) x) := by
  induction e with
  | refl T => rfl
  | assoc T U V =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x z =>
      induction x using OAI.tensorInductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
      | tmul x y => rfl
  | swap T U =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y => rfl
  | node e g ihe ihg =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
      change e.equivalence (quotientFamily a μ) (componentTensor a μ _ k.1 x) ⊗ₜ[ℚ]
          g.equivalence (quotientFamily a μ) (componentTensor a μ _ k.2 y)=
        componentTensor a μ _ (e.degrees k.1) (e.equivalence (quotientFamily a μ) x) ⊗ₜ[ℚ]
          componentTensor a μ _ (g.degrees k.2) (g.equivalence (quotientFamily a μ) y)
      rw [ihe,ihg]
  | trans e g ihe ihg =>
    change g.equivalence (quotientFamily a μ)
      (e.equivalence (quotientFamily a μ) (componentTensor a μ _ k x))=_
    rw [ihe,ihg]
    rfl

omit [Fintype I] [DecidableEq I] in
lemma append_ordered (T : SplitTree I) (hT : T.IsOrderedList)
    (U : SplitTree I) (hU : U.IsOrderedList) :
    ∃ V : SplitTree I,V.IsOrderedList ∧ Nonempty (Regroup (.node T U) V) := by
  induction T with
  | leaf d => exact ⟨.node (.leaf d) U,hU,⟨.refl _⟩⟩
  | node l r ihl ihr =>
    cases l with
    | node l₁ l₂ => exact False.elim hT
    | leaf d =>
      obtain ⟨V,hV,⟨e⟩⟩ := ihr hT
      exact ⟨.node (.leaf d) V,hV,⟨(Regroup.assoc _ _ _).trans (.node (.refl _) e)⟩⟩

omit [Fintype I] [DecidableEq I] in
lemma ordered_normalization (T : SplitTree I) :
    ∃ U : SplitTree I,U.IsOrderedList ∧ Nonempty (Regroup T U) := by
  induction T with
  | leaf d => exact ⟨.leaf d,True.intro,⟨.refl _⟩⟩
  | node l r ihl ihr =>
    obtain ⟨L,hL,⟨e⟩⟩ := ihl
    obtain ⟨R,hR,⟨f⟩⟩ := ihr
    obtain ⟨V,hV,⟨g⟩⟩ := append_ordered L hL R hR
    exact ⟨V,hV,⟨(Regroup.node e f).trans g⟩⟩

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DimensionEquivBTrans
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree.Regroup
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma dimensionEquivB_trans (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e f : I → ℕ} (h : d=e) (g : e=f) (x : B a μ d) :
    dimensionEquivB a μ g (dimensionEquivB a μ h x)=dimensionEquivB a μ (h.trans g) x := by
  subst e
  subst f
  rfl

lemma restrictionTest_natural (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d : I → ℕ} {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ) (hd : T.dim=d)
    (k : T.Degrees) (z : T.Centers →₀ ℕ) (f : B a (SlopeArithmetic.slope c η) d) :
    e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
        (restrictionTest a c η hc θ T hT hd k z f)=
      restrictionTest a c η hc θ U hU (e.dimension.symm.trans hd)
        (e.degrees k) (z.mapDomain e.centers) f := by
  change e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))
    (componentTensor a (SlopeArithmetic.slope c η) T k
      ((centeredRestrictionB a c η hc θ T hT
        (dimensionEquivB a (SlopeArithmetic.slope c η) hd.symm f)).coeff z))=_
  rw [componentTensor_natural,← centeredRestrictionB_coeff a c η hc θ e hT hU]
  rw [dimensionEquivB_trans]
  rfl

end ElementaryPositivity.RawShuffle.SplitTree.Regroup

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem sourceFiltration_allTrees (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d : I → ℕ} (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) (T : SplitTree I)
    (hs : T.OnSlope c η θ) (hd : T.dim=d) (k : T.Degrees) (z : T.Centers →₀ ℕ)
    (hw : 2*T.totalDegree k+T.doubleShift a<W) :
    restrictionTest a c η hc θ T hs hd k z f=0 := by
  obtain ⟨U,hU,⟨e⟩⟩ := SplitTree.Regroup.ordered_normalization T
  apply (e.equivalence (SplitTree.quotientFamily a (SlopeArithmetic.slope c η))).injective
  rw [map_zero,SplitTree.Regroup.restrictionTest_natural a c η hc θ e hs (e.onSlope c η θ hs)]
  apply hf U hU
  rw [e.totalDegree,e.doubleShift]
  exact hw

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNSpanning
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable {A : Type*} [Ring A] [Algebra ℚ A]
variable (c η : I → ℝ) (V : (I → ℕ) → Submodule ℚ A)
noncomputable def hnWordSpace (l : List (I → ℕ)) : Submodule ℚ A := (l.map V).prod
omit [Fintype I] in
@[simp] lemma hnWordSpace_nil : hnWordSpace V []=1 := rfl
omit [Fintype I] in
@[simp] lemma hnWordSpace_cons (d : I → ℕ) (l : List (I → ℕ)) :
    hnWordSpace V (d::l)=V d*hnWordSpace V l := rfl

end ElementaryPositivity.SlopeArithmetic

end
section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial

noncomputable def mapLinear {A B σ : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (l : A →ₗ[ℚ] B) :
    MvPolynomial σ A →ₗ[ℚ] MvPolynomial σ B where
  toFun p := AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).mapRange l l.map_zero)
  map_add' p q := by ext s; exact l.map_add (p.coeff s) (q.coeff s)
  map_smul' r p := by ext s; exact l.map_smul r (p.coeff s)

@[simp] lemma coeff_mapLinear {A B σ : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (l : A →ₗ[ℚ] B)
    (p : MvPolynomial σ A) (s : σ →₀ ℕ) :
    (mapLinear l p).coeff s = l (p.coeff s) := rfl

@[simp] lemma mapLinear_monomial {A B σ : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (l : A →ₗ[ℚ] B) (s : σ →₀ ℕ) (a : A) :
    mapLinear l (monomial s a) = monomial s (l a) := by
  classical
  ext t
  simp only [coeff_mapLinear,coeff_monomial]
  split_ifs <;> simp

noncomputable def evalRat {A σ : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → ℚ) : MvPolynomial σ A →ₐ[ℚ] A :=
  (aeval (fun i => algebraMap ℚ A (v i))).restrictScalars ℚ

@[simp] lemma evalRat_C {A σ : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → ℚ) (a : A) : evalRat v (C a) = a := by
  simp only [evalRat,AlgHom.restrictScalars_apply,aeval_C,Algebra.algebraMap_self,RingHom.id_apply]

@[simp] lemma evalRat_X {A σ : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → ℚ) (i : σ) : evalRat v (X i : MvPolynomial σ A) = algebraMap ℚ A (v i) := by
  simp only [evalRat,AlgHom.restrictScalars_apply,aeval_X]

@[simp] lemma evalRat_monomial {A σ : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → ℚ) (s : σ →₀ ℕ) (a : A) :
    evalRat v (monomial s a) = (s.prod fun i n => v i ^ n) • a := by
  simp only [evalRat,AlgHom.restrictScalars_apply,aeval_monomial,Algebra.algebraMap_self]
  simp only [RingHom.id_apply,Algebra.smul_def,Finsupp.prod,map_prod,map_pow]
  exact mul_comm _ _

lemma evalRat_mapLinear {A B σ : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (l : A →ₗ[ℚ] B)
    (p : MvPolynomial σ A) (v : σ → ℚ) :
    evalRat v (mapLinear l p) = l (evalRat v p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial s a => rw [mapLinear_monomial,evalRat_monomial,evalRat_monomial,map_smul]

theorem eq_of_evalRat {A σ : Type*} [CommRing A] [Algebra ℚ A]
    {p q : MvPolynomial σ A} (h : ∀ v : σ → ℚ, evalRat v p = evalRat v q) : p = q := by
  apply sub_eq_zero.mp
  have hzero : ∀ v : σ → ℚ, evalRat v (p-q)=0 := by
    intro v
    rw [map_sub,h v,sub_self]
  ext s
  simp only [MvPolynomial.coeff_zero, Finsupp.zero_apply]
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro l
  have hp : mapLinear l (p-q) = 0 := by
    apply MvPolynomial.funext
    intro v
    have ht := evalRat_mapLinear l (p-q) v
    rw [hzero,map_zero] at ht
    simpa only [evalRat,AlgHom.restrictScalars_apply,aeval_def,Algebra.algebraMap_self,
      RingHom.id_apply,coe_eval₂Hom,MvPolynomial.eval,eval₂_zero] using ht
  have he := congrArg (fun polynomial => MvPolynomial.coeff s polynomial) hp
  simpa only [coeff_mapLinear, MvPolynomial.coeff_zero, Finsupp.zero_apply] using he

end ElementaryPositivity.CenterCalculus

namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A α : Type*} [CommRing A]

noncomputable def toRelative : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A →ₐ[A]
    MvPolynomial (Unit ⊕ α) (Polynomial A) :=
  aeval (fun i => match i with
    | Sum.inl (Sum.inl _) => C Polynomial.X + X (Sum.inl ())
    | Sum.inl (Sum.inr _) => X (Sum.inl ())
    | Sum.inr i => X (Sum.inr i))

noncomputable def fromRelative : MvPolynomial (Unit ⊕ α) (Polynomial A) →+*
    MvPolynomial ((Unit ⊕ Unit) ⊕ α) A :=
  eval₂Hom (Polynomial.aeval (X (Sum.inl (Sum.inl ())) - X (Sum.inl (Sum.inr ())))).toRingHom
    (fun i => match i with
      | Sum.inl _ => X (Sum.inl (Sum.inr ()))
      | Sum.inr i => X (Sum.inr i))

@[simp] lemma toRelative_C (a : A) :
    toRelative (C a : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) = C (Polynomial.C a) := by
  simp [toRelative]

@[simp] lemma toRelative_first :
    toRelative (X (Sum.inl (Sum.inl ())) : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) =
      C Polynomial.X + X (Sum.inl ()) := by simp [toRelative]

@[simp] lemma toRelative_second :
    toRelative (X (Sum.inl (Sum.inr ())) : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) =
      X (Sum.inl ()) := by simp [toRelative]

@[simp] lemma toRelative_other (i : α) :
    toRelative (X (Sum.inr i) : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) = X (Sum.inr i) := by
  simp [toRelative]

@[simp] lemma fromRelative_C (p : Polynomial A) :
    fromRelative (C p : MvPolynomial (Unit ⊕ α) (Polynomial A)) =
      Polynomial.aeval (X (Sum.inl (Sum.inl ())) - X (Sum.inl (Sum.inr ()))) p := by
  simp [fromRelative]

@[simp] lemma fromRelative_common :
    fromRelative (X (Sum.inl ()) : MvPolynomial (Unit ⊕ α) (Polynomial A)) =
      X (Sum.inl (Sum.inr ())) := by simp [fromRelative]

@[simp] lemma fromRelative_other (i : α) :
    fromRelative (X (Sum.inr i) : MvPolynomial (Unit ⊕ α) (Polynomial A)) = X (Sum.inr i) := by
  simp [fromRelative]

@[simp] lemma fromRelative_toRelative (p : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) :
    fromRelative (toRelative p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [toRelative_C,fromRelative_C,Polynomial.aeval_C,algebraMap_eq]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    rw [map_mul,map_mul,hp]
    apply congrArg (p * ·)
    rcases i with (u | u) | i
    · cases u; simp
    · cases u; simp
    · simp

theorem diagonal_dvd_of_relative_coeff (p : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A)
    (n : ℕ) (h : ∀ z s, s < n → ((toRelative p).coeff z).coeff s = 0) :
    (X (Sum.inl (Sum.inl ())) - X (Sum.inl (Sum.inr ()))) ^ n ∣ p := by
  have hd : C (Polynomial.X ^ n) ∣ toRelative p := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro z
    exact Polynomial.X_pow_dvd_iff.mpr (h z)
  have he := map_dvd fromRelative hd
  simpa only [fromRelative_C,map_pow,Polynomial.aeval_X,
    fromRelative_toRelative] using he

def relativePoint (t : ℚ) (v : Unit ⊕ α → ℚ) : (Unit ⊕ Unit) ⊕ α → ℚ
  | Sum.inl (Sum.inl _) => t + v (Sum.inl ())
  | Sum.inl (Sum.inr _) => v (Sum.inl ())
  | Sum.inr i => v (Sum.inr i)

variable [Algebra ℚ A]

lemma polynomial_eval_rat_algebraMap (r t : ℚ) :
    Polynomial.eval (algebraMap ℚ A t) (algebraMap ℚ (Polynomial A) r) = algebraMap ℚ A r := by
  exact Polynomial.eval_C

lemma evalRat_toRelative (p : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A)
    (v : Unit ⊕ α → ℚ) (t : ℚ) :
    (evalRat v (toRelative p)).eval (algebraMap ℚ A t) = evalRat (relativePoint t v) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [toRelative_C,evalRat_C,Polynomial.eval_C,evalRat_C]
  | add p q hp hq => simp only [map_add,Polynomial.eval_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.eval_mul,hp]
    apply congrArg (evalRat (relativePoint t v) p * ·)
    rcases i with (u | u) | i
    · cases u
      simp only [toRelative_first,map_add,evalRat_C,evalRat_X,Polynomial.eval_add,
        Polynomial.eval_X,polynomial_eval_rat_algebraMap,relativePoint]
    · cases u
      simp only [toRelative_second,evalRat_X,polynomial_eval_rat_algebraMap,relativePoint]
    · simp only [toRelative_other,evalRat_X,polynomial_eval_rat_algebraMap,relativePoint]

end ElementaryPositivity.CenterCalculus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ManyBlockDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma evalRat_toMvPolynomial {A α : Type*} [CommRing A] [Algebra ℚ A]
    (i : α) (p : Polynomial A) (v : α → ℚ) :
    evalRat v (Polynomial.toMvPolynomial i p) = p.eval (algebraMap ℚ A (v i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Polynomial.eval_add,hp,hq]
  | monomial n a => simp [← Polynomial.C_mul_X_pow_eq_monomial]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_TwoLeafDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A : Type*} [CommRing A]

noncomputable def ofTwo : Polynomial (Polynomial A) →+* MvPolynomial (Unit ⊕ Unit) A :=
  Polynomial.eval₂RingHom (Polynomial.toMvPolynomial (Sum.inl ())).toRingHom (X (Sum.inr ()))

@[simp] lemma ofTwo_C (p : Polynomial A) : ofTwo (Polynomial.C p) =
    Polynomial.toMvPolynomial (Sum.inl ()) p := by simp [ofTwo]

@[simp] lemma ofTwo_X : ofTwo (Polynomial.X : Polynomial (Polynomial A)) = X (Sum.inr ()) := by
  simp [ofTwo]

variable [Algebra ℚ A]

lemma evalRat_ofTwo (p : Polynomial (Polynomial A)) (v : Unit ⊕ Unit → ℚ) :
    evalRat v (ofTwo p) = RawShuffle.evalTwo p (v (Sum.inl ())) (v (Sum.inr ())) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,RawShuffle.evalTwo,Polynomial.eval_add] at *; rw [hp,hq]
  | monomial n p =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul,map_pow,ofTwo_C,ofTwo_X,evalRat_X,
      RawShuffle.SplitTree.evalRat_toMvPolynomial,RawShuffle.evalTwo,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    rw [polynomial_eval_rat_algebraMap]

end ElementaryPositivity.CenterCalculus

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
universe u
variable {I : Type u}

def leafDimension : (T : SplitTree I) → T.Centers → I → ℕ
  | .leaf d, _ => d
  | .node l _, Sum.inl i => leafDimension l i
  | .node _ r, Sum.inr i => leafDimension r i

namespace Regroup

def assocInv (T U V : SplitTree I) : Regroup (.node T (.node U V)) (.node (.node T U) V) :=
  (Regroup.swap T (.node U V)).trans
    ((Regroup.node (Regroup.swap U V) (Regroup.refl T)).trans
      ((Regroup.assoc V U T).trans
        ((Regroup.swap V (.node U T)).trans
          (Regroup.node (Regroup.swap U T) (Regroup.refl V)))))

@[simp] lemma assocInv_centers_left (T U V : SplitTree I) (i : T.Centers) :
    (assocInv T U V).centers (Sum.inl i) = Sum.inl (Sum.inl i) := rfl

@[simp] lemma assocInv_centers_mid (T U V : SplitTree I) (i : U.Centers) :
    (assocInv T U V).centers (Sum.inr (Sum.inl i)) = Sum.inl (Sum.inr i) := rfl

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_AllPairDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
open ElementaryPositivity.RawShuffle.SplitTree
variable {A D α β : Type*} [CommRing A] [CommRing D] [Algebra ℚ A] [Algebra ℚ D]

lemma mapLinear_extendPolynomial (f : A →ₐ[ℚ] D) (e : α ≃ β)
    (l : A →ₗ[ℚ] A) (m : D →ₗ[ℚ] D) (h : ∀ x, m (f x) = f (l x))
    (p : MvPolynomial α A) :
    mapLinear m (extendPolynomial f e p) = extendPolynomial f e (mapLinear l p) := by
  ext z
  obtain ⟨z,rfl⟩ := Finsupp.mapDomain_surjective e.surjective z
  simp only [coeff_mapLinear,Regroup.extendPolynomial_coeff]
  exact h _

lemma extendPolynomial_symm (f : A ≃ₐ[ℚ] D) (e : α ≃ β) (p : MvPolynomial α A) :
    extendPolynomial f.symm.toAlgHom e.symm (extendPolynomial f.toAlgHom e p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [extendPolynomial_C,AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => simp only [map_mul,hp,extendPolynomial_X,Equiv.symm_apply_apply]

end ElementaryPositivity.CenterCalculus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ManyBlockPolynomiality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def componentFinsupp (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) : tensor (quotientFamily a μ) T →ₗ[ℚ]
      (T.Degrees →₀ tensor (quotientFamily a μ) T) where
  toFun x := Finsupp.ofSupportFinite (fun k=>componentTensor a μ T k x) (by
    obtain ⟨s,hs,_⟩ := componentTensor_finite_decomposition a μ T x
    apply s.finite_toSet.subset
    intro k hk
    by_contra hn
    exact hk (hs k hn))
  map_add' x y := by
    ext k
    change componentTensor a μ T k (x+y)=componentTensor a μ T k x+componentTensor a μ T k y
    exact map_add _ x y
  map_smul' r x := by
    ext k
    change componentTensor a μ T k (r • x)=r • componentTensor a μ T k x
    exact map_smul _ r x

@[simp] lemma componentFinsupp_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (x : tensor (quotientFamily a μ) T) (k : T.Degrees) :
    componentFinsupp a μ T x k = componentTensor a μ T k x := rfl

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DegreeIdeals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree
@[reducible] def addDegrees : (T : SplitTree I) → T.Degrees → T.Degrees → T.Degrees
  | .leaf _, i,j => i+j
  | .node l r, i,j => (l.addDegrees i.1 j.1,r.addDegrees i.2 j.2)

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Degree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree
@[reducible] def zeroDegrees : (T : SplitTree I) → T.Degrees
  | .leaf _ => 0
  | .node l r => (l.zeroDegrees,r.zeroDegrees)

noncomputable def degreeZeroTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) : tensor (quotientFamily a μ) T →ₐ[ℚ] tensor (quotientFamily a μ) T :=
  tensorMap (quotientFamily a μ) (quotientFamily a μ) (degreeZeroB a μ) T

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PointEvaluation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma constantCoeff_translation {α : Type*} (t : ℚ) (f : MvPolynomial α ℚ) :
    constantCoeff (translation t f)=eval (fun _=>t) f := by
  induction f using MvPolynomial.induction_on with
  | C q => simp only [translation_C,constantCoeff_C,eval_C]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => simp only [map_mul,translation_X,map_add,constantCoeff_X,
      constantCoeff_C,zero_add,hf,eval_X]

noncomputable def translationAlgB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (t : ℚ) : B a μ d →ₐ[ℚ] B a μ d :=
  (Polynomial.eval₂AlgHom (AlgHom.id ℚ (B a μ d)) (algebraMap ℚ (B a μ d) t)
    (fun _=>Commute.all _ _)).comp
    (taylorB a μ d)

lemma translationAlgB_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (t : ℚ) (f : B a μ d) :
    translationAlgB a μ d t f=translationB a μ d t f := by
  change Polynomial.eval₂ (RingHom.id _) (algebraMap ℚ (B a μ d) t) (taylorB a μ d f)=_
  rw [Polynomial.eval₂_id,taylorB_eval]

namespace SplitTree
@[reducible] def centerOfVar : (T : SplitTree I) → T.Vars → T.Centers
  | .leaf _, _ => ()
  | .node l _, .inl x => .inl (l.centerOfVar x)
  | .node _ r, .inr x => .inr (r.centerOfVar x)

noncomputable def translationAtAlgB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) :
    (T : SplitTree I) → (T.Centers → ℚ) →
      tensor (quotientFamily a μ) T →ₐ[ℚ] tensor (quotientFamily a μ) T
  | .leaf d, v => translationAlgB a μ d (v ())
  | .node l r, v => Algebra.TensorProduct.map
      (translationAtAlgB a μ l (v ∘ Sum.inl)) (translationAtAlgB a μ r (v ∘ Sum.inr))

lemma degreeZero_translate_quotient (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (v : T.Centers → ℚ) (x : tensor rawFamily T) :
    degreeZeroTensor a μ T (translationAtAlgB a μ T v (quotientMap a μ T x))=
      algebraMap ℚ (tensor (quotientFamily a μ) T)
        (eval (v ∘ T.centerOfVar) (tensorValue T x)) := by
  induction T with
  | leaf d =>
    change degreeZeroB a μ d (translationAlgB a μ d (v ()) (quotientAlg a μ d x))=_
    rw [translationAlgB_apply]
    change degreeZeroB a μ d (quotientAlg a μ d (translationS d (v ()) x))=_
    rw [degreeZeroB_mk]
    congr 1
    exact constantCoeff_translation (v ()) x.val
  | node l r hl hr =>
    induction x using OAI.tensorInductionOn with
    | tmul x y =>
      change degreeZeroTensor a μ l (translationAtAlgB a μ l (v ∘ Sum.inl) (quotientMap a μ l x))⊗ₜ[ℚ]
        degreeZeroTensor a μ r (translationAtAlgB a μ r (v ∘ Sum.inr) (quotientMap a μ r y))=_
      rw [hl,hr,tensorValue_tmul,map_mul,eval_rename,eval_rename]
      simp only [Function.comp_def,centerOfVar]
      simp only [Algebra.algebraMap_eq_smul_one,TensorProduct.smul_tmul,
        TensorProduct.tmul_smul,smul_smul,Algebra.TensorProduct.one_def,mul_comm]
    | add x y hx hy => simp only [map_add,hx,hy]

noncomputable def pointedRestrictionB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ) (v : T.Centers → ℚ) :
    B a (SlopeArithmetic.slope c η) T.dim →ₐ[ℚ] tensor (quotientFamily a (SlopeArithmetic.slope c η)) T :=
  (degreeZeroTensor a (SlopeArithmetic.slope c η) T).comp
    ((translationAtAlgB a (SlopeArithmetic.slope c η) T v).comp
      (restrictionB a c η hc θ T hT))

lemma pointedRestrictionB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ) (v : T.Centers → ℚ) (f : S T.dim) :
    pointedRestrictionB a c η hc θ T hT v (quotientAlg a (SlopeArithmetic.slope c η) T.dim f)=
      algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T)
        (eval (v ∘ T.centerOfVar ∘ T.varEquiv.symm) f.val) := by
  simp only [pointedRestrictionB,AlgHom.comp_apply,restrictionB_mk,
    degreeZero_translate_quotient,tensorValue_rawRestriction,eval_rename]
  rfl
end SplitTree
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

instance centersFintype : (T : SplitTree I) → Fintype T.Centers
  | .leaf _ => inferInstanceAs (Fintype Unit)
  | .node l r => by
    letI := centersFintype l
    letI := centersFintype r
    exact inferInstanceAs (Fintype (l.Centers ⊕ r.Centers))

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_KernelEvaluation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace SplitTree

noncomputable def leafVarsEquiv : (T : SplitTree I) →
    T.Vars ≃ (Σ z : T.Centers, Σ i, Fin (T.leafDimension z i))
  | .leaf d =>
    { toFun := fun x=>⟨(),x⟩
      invFun := fun x=>x.2
      left_inv := fun _=>rfl
      right_inv := fun ⟨z,x⟩=>by cases z; rfl }
  | .node l r =>
    (Equiv.sumCongr (leafVarsEquiv l) (leafVarsEquiv r)).trans
      (Equiv.sumSigmaDistrib (fun z : (SplitTree.node l r).Centers=>Σ i,Fin ((SplitTree.node l r).leafDimension z i))).symm

omit [Fintype I] [DecidableEq I] in
@[simp] lemma leafVarsEquiv_center (T : SplitTree I) (x : T.Vars) :
    (T.leafVarsEquiv x).1=T.centerOfVar x := by
  induction T with
  | leaf d => rfl
  | node l r hl hr => cases x with
    | inl x => exact congrArg Sum.inl (hl x)
    | inr x => exact congrArg Sum.inr (hr x)

omit [Fintype I] [DecidableEq I] in
@[simp] lemma leafVarsEquiv_pack (T : SplitTree I) (x : T.Vars) :
    (T.leafVarsEquiv x).2.1=T.packIndex x := by
  induction T with
  | leaf d => rfl
  | node l r hl hr => cases x with
    | inl x => exact hl x
    | inr x => exact hr x

noncomputable def pointedTensorRestriction (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim →ₐ[ℚ]
      tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R) :=
  Algebra.TensorProduct.map (pointedRestrictionB a c η hc θ L hL v)
    (pointedRestrictionB a c η hc θ R hR w)

noncomputable def crossPointEval (L R : SplitTree I) (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    MvPolynomial (CellVars L.dim R.dim) ℚ →+* ℚ :=
  eval (Sum.elim (v ∘ L.centerOfVar ∘ L.varEquiv.symm)
    (w ∘ R.centerOfVar ∘ R.varEquiv.symm))

lemma pointedTensorRestriction_quotient (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (x : S L.dim ⊗[ℚ] S R.dim) :
    pointedTensorRestriction a c η hc θ L R hL hR v w
      (Algebra.TensorProduct.map (quotientAlg a (SlopeArithmetic.slope c η) L.dim)
        (quotientAlg a (SlopeArithmetic.slope c η) R.dim) x)=
      algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R))
        (crossPointEval L R v w (RawShuffle.tensorValue L.dim R.dim x)) := by
  induction x using OAI.tensorInductionOn with
  | tmul x y =>
    simp only [pointedTensorRestriction,Algebra.TensorProduct.map_tmul,pointedRestrictionB_mk,
      RawShuffle.tensorValue_tmul,crossPointEval,map_mul,eval_rename]
    simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr]
    simp only [Algebra.algebraMap_eq_smul_one,TensorProduct.smul_tmul,
      TensorProduct.tmul_smul,smul_smul,Algebra.TensorProduct.one_def,mul_comm,
      mul_smul_comm,smul_smul,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  | add x y hx hy => simp only [map_add,hx,hy]
end SplitTree
end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity SplitTree
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma pointed_quotientInverseKernel (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    mapRing (pointedTensorRestriction a c η hc θ L R hL hR v w).toRingHom
      (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val =
    mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (mapRing (crossPointEval L R v w) (rawInverseKernelUnit a L.dim R.dim).val) := by
  apply HahnSeries.ext
  funext k
  change pointedTensorRestriction a c η hc θ L R hL hR v w
    (Algebra.TensorProduct.map (quotientAlg a (SlopeArithmetic.slope c η) L.dim)
      (quotientAlg a (SlopeArithmetic.slope c η) R.dim) ((inverseKernelUnit a L.dim R.dim).val.coeff k))=_
  rw [pointedTensorRestriction_quotient]
  have h:=congrArg (fun f : LaurentSeries (MvPolynomial (CellVars L.dim R.dim) ℚ)=>f.coeff k)
    (realize_inverseKernelUnit a L.dim R.dim)
  exact congrArg (fun f=>algebraMap ℚ _ (crossPointEval L R v w f)) h

lemma crossPointEval_inverseKernel (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    Units.map (mapRing (crossPointEval L R v w)).toMonoidHom
      (rawInverseKernelUnit a L.dim R.dim)=
      ∏ i, ∏ j, ∏ x : Fin (L.dim i), ∏ y : Fin (R.dim j),
        affineUnit (w (R.centerOfVar (R.varEquiv.symm ⟨j,y⟩))-
          v (L.centerOfVar (L.varEquiv.symm ⟨i,x⟩))) ^ inverseExponent a i j := by
  simp only [rawInverseKernelUnit,rawFactor,map_prod,map_zpow,affineUnit_map,
    crossPointEval,map_sub,eval_X,Sum.elim_inl,Sum.elim_inr,Function.comp_apply]
end ElementaryPositivity.RawShuffle.SeparationInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_EulerFiniteProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
variable {I M : Type*} [Fintype I] [DecidableEq I] [CommGroup M]
lemma prod_zpow_eq_zpow_sum {α : Type*} (s : Finset α) (f : α → ℤ) (m : M) :
    (∏ x∈s,m ^ f x)=m ^ ∑ x∈s,f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih => simp only [Finset.prod_insert hx,Finset.sum_insert hx,zpow_add,ih]

lemma inverseEuler_exponent (a : I → I → ℕ) (d e : I → ℕ) :
    (∑ i,∑ j, ((if i=j then 1 else 0)-(a i j:ℤ))*(d i:ℤ)*e j)=
      (∑ i,(d i:ℤ)*e i)-∑ i,∑ j,(a i j:ℤ)*d i*e j := by
  simp only [sub_mul,Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]

lemma inverseEuler_unit_product (a : I → I → ℕ) (d e : I → ℕ) (m : M) :
    (∏ i,∏ j,∏ _x : Fin (d i),∏ _y : Fin (e j),
      m ^ ((if i=j then 1 else 0)-(a i j:ℤ)))=
    m ^ ((∑ i,(d i:ℤ)*e i)-∑ i,∑ j,(a i j:ℤ)*d i*e j) := by
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp only [← zpow_natCast,← zpow_mul,prod_zpow_eq_zpow_sum]
  congr 1
  rw [← inverseEuler_exponent a d e]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossScalar
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma prod_packVariables {M : Type*} [CommMonoid M] (T : SplitTree I)
    (f : T.Centers → I → M) :
    (∏ i, ∏ x : Fin (T.dim i),f (T.centerOfVar (T.varEquiv.symm ⟨i,x⟩)) i)=
      ∏ z : T.Centers,∏ i,∏ _x : Fin (T.leafDimension z i),f z i := by
  classical
  have h:=Equiv.prod_comp (T.varEquiv.symm.trans T.leafVarsEquiv)
    (fun p : Σ z : T.Centers,Σ i,Fin (T.leafDimension z i)=>f p.1 p.2.1)
  simpa only [Fintype.prod_sigma,Equiv.trans_apply,leafVarsEquiv_center,
    leafVarsEquiv_pack,varEquiv_symm_packIndex] using h

noncomputable def scalarCrossKernel (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) : (LaurentSeries ℚ)ˣ :=
  ∏ z : L.Centers, ∏ t : R.Centers,
    affineUnit (w t-v z) ^ eulerForm a (L.leafDimension z) (R.leafDimension t)

lemma packProduct_eq_scalarCrossKernel (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    (∏ i, ∏ j, ∏ x : Fin (L.dim i), ∏ y : Fin (R.dim j),
      affineUnit (w (R.centerOfVar (R.varEquiv.symm ⟨j,y⟩))-
        v (L.centerOfVar (L.varEquiv.symm ⟨i,x⟩))) ^ SeparationInfinity.inverseExponent a i j)=
      scalarCrossKernel a L R v w := by
  classical
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.prod_comm]
  rw [prod_packVariables L (fun z i=>∏ j,∏ y : Fin (R.dim j),
    affineUnit (w (R.centerOfVar (R.varEquiv.symm ⟨j,y⟩))-v z) ^ SeparationInfinity.inverseExponent a i j)]
  conv_lhs =>
    arg 2
    ext z
    arg 2
    ext i
    arg 2
    ext x
    rw [prod_packVariables R (fun t j=>affineUnit (w t-v z)^SeparationInfinity.inverseExponent a i j)]
  unfold scalarCrossKernel
  apply Finset.prod_congr rfl
  intro z hz
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.prod_comm]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro t ht
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.prod_comm]
  exact ElementaryPositivity.inverseEuler_unit_product a (L.leafDimension z) (R.leafDimension t) _
end ElementaryPositivity.RawShuffle.SplitTree

namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity SplitTree
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
lemma crossPointEval_inverseKernel_scalar (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    Units.map (mapRing (crossPointEval L R v w)).toMonoidHom
      (rawInverseKernelUnit a L.dim R.dim)=scalarCrossKernel a L R v w := by
  rw [crossPointEval_inverseKernel,packProduct_eq_scalarCrossKernel]
end ElementaryPositivity.RawShuffle.SeparationInfinity

end
section
namespace ElementaryPositivity.CoefficientIdeals
open MvPolynomial
variable {R σ : Type*} [CommRing R]

lemma map_quotient_eq_zero_iff (J : Ideal R) (p : MvPolynomial σ R) :
    MvPolynomial.map (Ideal.Quotient.mk J) p=0 ↔ ∀ z,p.coeff z∈J := by
  constructor
  · intro hp z
    have h:=congrArg (fun polynomial=>MvPolynomial.coeff z polynomial) hp
    simpa only [coeff_map,MvPolynomial.coeff_zero,Finsupp.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem] using h
  · intro hp
    ext z
    simpa only [coeff_map,MvPolynomial.coeff_zero,Finsupp.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem] using hp z

lemma coeff_mul_mem (J : Ideal R) (p q : MvPolynomial σ R)
    (hp : ∀ z,p.coeff z∈J) (z : σ →₀ ℕ) : (p*q).coeff z∈J := by
  apply (map_quotient_eq_zero_iff J (p*q)).mp _ z
  rw [map_mul,(map_quotient_eq_zero_iff J p).mpr hp,zero_mul]

end ElementaryPositivity.CoefficientIdeals

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalTensorDetection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
universe u v w u' v' i j
variable {K : Type u} [Field K]
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
variable [Module K M] [Module K N]

lemma basisLeft_natural {N' : Type w} [AddCommGroup N'] [Module K N']
    {ι : Type i} [DecidableEq ι] (b : Module.Basis ι K M) (g : N →ₗ[K] N')
    (x : M ⊗[K] N) (k : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (TensorProduct.map LinearMap.id g x) k =
      g (TensorProduct.equivFinsuppOfBasisLeft b x k) := by
  induction x using OAI.tensorInductionOn with
  | tmul m n => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]

lemma basisRight_natural {M' : Type v} [AddCommGroup M'] [Module K M']
    {ι : Type i} [DecidableEq ι] (b : Module.Basis ι K N) (f : M →ₗ[K] M')
    (x : M ⊗[K] N) (k : ι) :
    TensorProduct.equivFinsuppOfBasisRight b (TensorProduct.map f LinearMap.id x) k =
      f (TensorProduct.equivFinsuppOfBasisRight b x k) := by
  induction x using OAI.tensorInductionOn with
  | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]

theorem tensor_right_detect {ι : Type i} {N' : ι → Type w}
    [∀ i, AddCommGroup (N' i)] [∀ i, Module K (N' i)]
    (g : ∀ i, N →ₗ[K] N' i)
    (hg : ∀ y, (∀ i, g i y=0) → y=0) (x : M ⊗[K] N)
    (hx : ∀ i, TensorProduct.map LinearMap.id (g i) x=0) : x=0 := by
  classical
  let b := Module.Free.chooseBasis K M
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext k
  apply hg
  intro i
  rw [← basisLeft_natural b (g i),hx i,map_zero,Finsupp.zero_apply]

theorem tensor_left_detect {ι : Type i} {M' : ι → Type v}
    [∀ i, AddCommGroup (M' i)] [∀ i, Module K (M' i)]
    (f : ∀ i, M →ₗ[K] M' i)
    (hf : ∀ x, (∀ i, f i x=0) → x=0) (x : M ⊗[K] N)
    (hx : ∀ i, TensorProduct.map (f i) LinearMap.id x=0) : x=0 := by
  classical
  let b := Module.Free.chooseBasis K N
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  rw [map_zero]
  ext k
  apply hf
  intro i
  rw [← basisRight_natural b (f i),hx i,map_zero,Finsupp.zero_apply]

theorem tensor_detect {ι : Type i} {κ : Type j} {M' : ι → Type v} {N' : κ → Type w}
    [∀ i, AddCommGroup (M' i)] [∀ i, Module K (M' i)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module K (N' j)]
    (f : ∀ i, M →ₗ[K] M' i) (g : ∀ j, N →ₗ[K] N' j)
    (hf : ∀ x, (∀ i, f i x=0) → x=0)
    (hg : ∀ y, (∀ j, g j y=0) → y=0)
    (x : M ⊗[K] N) (hx : ∀ i j, TensorProduct.map (f i) (g j) x=0) : x=0 := by
  apply tensor_left_detect f hf x
  intro i
  apply tensor_right_detect g hg (TensorProduct.map (f i) LinearMap.id x)
  intro j
  have hcomp : (TensorProduct.map LinearMap.id (g j)).comp
      (TensorProduct.map (f i) (LinearMap.id : N →ₗ[K] N)) =
      TensorProduct.map (f i) (g j) := by
    ext m n
    simp
  change ((TensorProduct.map LinearMap.id (g j)).comp
      (TensorProduct.map (f i) (LinearMap.id : N →ₗ[K] N))) x=0
  rw [hcomp,hx i j]

theorem tensor_map_zero_of_test_kernels
    {ι : Type i} {κ : Type j} {M' : ι → Type v} {N' : κ → Type w}
    [∀ i, AddCommGroup (M' i)] [∀ i, Module K (M' i)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module K (N' j)]
    (t : ∀ i, M →ₗ[K] M' i) (s : ∀ j, N →ₗ[K] N' j)
    (f : M →ₗ[K] M) (g : N →ₗ[K] N)
    (hf : (⨅ i, LinearMap.ker (t i)) ≤ LinearMap.ker f)
    (hg : (⨅ j, LinearMap.ker (s j)) ≤ LinearMap.ker g)
    (x : M ⊗[K] N) (hx : ∀ i j, TensorProduct.map (t i) (s j) x=0) :
    TensorProduct.map f g x=0 := by
  let P : Submodule K M := ⨅ i, LinearMap.ker (t i)
  let Q : Submodule K N := ⨅ j, LinearMap.ker (s j)
  let t' := fun i => P.liftQ (t i) (iInf_le _ i)
  let s' := fun j => Q.liftQ (s j) (iInf_le _ j)
  have ht : ∀ y, (∀ i, t' i y=0) → y=0 := by
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      apply (Submodule.Quotient.mk_eq_zero P).mpr
      simpa only [P,t',Submodule.mem_iInf,LinearMap.mem_ker,Submodule.liftQ_apply] using hy
  have hs : ∀ y, (∀ j, s' j y=0) → y=0 := by
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      apply (Submodule.Quotient.mk_eq_zero Q).mpr
      simpa only [Q,s',Submodule.mem_iInf,LinearMap.mem_ker,Submodule.liftQ_apply] using hy
  have hquot : TensorProduct.map P.mkQ Q.mkQ x=0 := by
    apply tensor_detect t' s' ht hs
    intro i j
    have hc : (TensorProduct.map (t' i) (s' j)).comp
        (TensorProduct.map P.mkQ Q.mkQ) = TensorProduct.map (t i) (s j) := by
      ext m n
      simp [t',s']
    change ((TensorProduct.map (t' i) (s' j)).comp
      (TensorProduct.map P.mkQ Q.mkQ)) x=0
    rw [hc,hx i j]
  have hc : (TensorProduct.map (P.liftQ f hf) (Q.liftQ g hg)).comp
      (TensorProduct.map P.mkQ Q.mkQ) = TensorProduct.map f g := by
    ext m n
    simp
  rw [← hc,LinearMap.comp_apply,hquot,map_zero]

end ElementaryPositivity.LinearDetection

end
section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
universe u v w i j
variable {K : Type u} [Field K]
variable {M : Type v} [AddCommGroup M] [Module K M]
variable {N : Type w} [AddCommGroup N] [Module K N]

noncomputable def retract (P : Submodule K M) : M →ₗ[K] M :=
  P.projection (Classical.choose P.exists_isCompl) (Classical.choose_spec P.exists_isCompl)

lemma retract_mem (P : Submodule K M) (x : M) : retract P x∈P :=
  P.projection_apply_mem _ x

lemma retract_eq_self (P : Submodule K M) {x : M} (hx : x∈P) : retract P x=x :=
  P.projection_apply_of_mem_left _ hx

lemma retract_top : retract (⊤ : Submodule K M)=LinearMap.id := by
  ext x
  exact retract_eq_self _ trivial

noncomputable def filtrationPiece (F : ℕ → Submodule K M) (n : ℕ) (i : Fin (n+1)) :
    M →ₗ[K] M :=
  if i.val<n then retract (F i.val)-retract (F (i.val+1)) else retract (F n)

lemma filtrationPiece_mem (F : ℕ → Submodule K M) (hF : Antitone F)
    (n : ℕ) (i : Fin (n+1)) (x : M) : filtrationPiece F n i x∈F i.val := by
  unfold filtrationPiece
  split_ifs with hi
  · exact (F i.val).sub_mem (retract_mem _ _) (hF (Nat.le_succ _) (retract_mem _ _))
  · have he : i.val=n := by omega
    rw [he]
    exact retract_mem _ _

lemma filtrationPiece_kernel (F : ℕ → Submodule K M) (hF : Antitone F)
    (n : ℕ) (i : Fin (n+1)) (hi : i.val<n) :
    F (i.val+1)≤LinearMap.ker (filtrationPiece F n i) := by
  intro x hx
  change filtrationPiece F n i x=0
  simp only [filtrationPiece,ite_eq_left hi,LinearMap.sub_apply]
  rw [retract_eq_self _ (hF (Nat.le_succ _) hx),retract_eq_self _ hx,sub_self]

lemma filtrationPiece_sum (F : ℕ → Submodule K M) (hF : F 0=⊤) (n : ℕ) :
    ∑ i : Fin (n+1),filtrationPiece F n i = LinearMap.id := by
  classical
  rw [Fin.sum_univ_castSucc]
  have hs : (∑ i : Fin n, filtrationPiece F n i.castSucc) =
      retract (F 0)-retract (F n) := by
    simp only [filtrationPiece,Fin.val_castSucc,Fin.is_lt,ite_true, if_true]
    change (∑ i : Fin n, (fun k : ℕ=>retract (F k)-retract (F (k+1))) i.val) = _
    exact (Fin.sum_univ_eq_sum_range (fun k=>retract (F k)-retract (F (k+1))) n).trans
      (Finset.sum_range_sub' (fun i=>retract (F i)) n)
  rw [hs]
  simp only [filtrationPiece,Fin.val_last,lt_self_iff_false,ite_false, if_false,sub_add_cancel,hF,retract_top]

lemma tensor_map_sum_left {α : Type*} (s : Finset α) (f : α → M →ₗ[K] M)
    (g : N →ₗ[K] N) :
    TensorProduct.map (∑ i∈s,f i) g = ∑ i∈s,TensorProduct.map (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [hi,TensorProduct.map_add_left,hs]

lemma tensor_map_sum_right {α : Type*} (s : Finset α) (f : M →ₗ[K] M)
    (g : α → N →ₗ[K] N) :
    TensorProduct.map f (∑ i∈s,g i) = ∑ i∈s,TensorProduct.map f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [hi,TensorProduct.map_add_right,hs]

lemma tensor_sum_pieces (F : ℕ → Submodule K M) (G : ℕ → Submodule K N)
    (hF : F 0=⊤) (hG : G 0=⊤) (n : ℕ) (x : M ⊗[K] N) :
    ∑ i : Fin (n+1), ∑ j : Fin (n+1),
      TensorProduct.map (filtrationPiece F n i) (filtrationPiece G n j) x = x := by
  have he : (∑ i : Fin (n+1),∑ j : Fin (n+1),
      TensorProduct.map (filtrationPiece F n i) (filtrationPiece G n j))=
      TensorProduct.map LinearMap.id LinearMap.id := by
    rw [← filtrationPiece_sum F hF n,← filtrationPiece_sum G hG n]
    rw [tensor_map_sum_left]
    apply Finset.sum_congr rfl
    intro i hi
    rw [tensor_map_sum_right]
  simpa only [LinearMap.sum_apply,TensorProduct.map_id,LinearMap.id_apply] using LinearMap.congr_fun he x

noncomputable def testFiltration {ι : Type i} {D : ι → Type v}
    [∀ i,AddCommGroup (D i)] [∀ i,Module K (D i)]
    (t : ∀ i,M →ₗ[K] D i) (wt : ι → ℤ) (W : ℤ) : Submodule K M :=
  ⨅ i, ⨅ (_ : wt i<W), LinearMap.ker (t i)

lemma mem_testFiltration {ι : Type i} {D : ι → Type v}
    [∀ i,AddCommGroup (D i)] [∀ i,Module K (D i)]
    (t : ∀ i,M →ₗ[K] D i) (wt : ι → ℤ) (W : ℤ) (x : M) :
    x∈testFiltration t wt W ↔ ∀ i,wt i<W → t i x=0 := by
  simp only [testFiltration,Submodule.mem_iInf,LinearMap.mem_ker]

lemma testFiltration_antitone {ι : Type i} {D : ι → Type v}
    [∀ i,AddCommGroup (D i)] [∀ i,Module K (D i)]
    (t : ∀ i,M →ₗ[K] D i) (wt : ι → ℤ) : Antitone (testFiltration t wt) := by
  intro u v huv x hx
  rw [mem_testFiltration] at hx ⊢
  exact fun i hi=>hx i (lt_of_lt_of_le hi huv)

lemma tmul_mem_additiveTensorFiltration (F : ℤ → Submodule K M)
    (G : ℤ → Submodule K N) {W u v : ℤ} (h : W≤u+v)
    {x : M} {y : N} (hx : x∈F u) (hy : y∈G v) :
    x⊗ₜ[K]y ∈ additiveTensorFiltration F G W :=
  Submodule.subset_span ⟨u,v,x,y,h,hx,hy,rfl⟩

lemma map_mem_additiveTensorFiltration (F : ℤ → Submodule K M)
    (G : ℤ → Submodule K N) {W u v : ℤ} (h : W≤u+v)
    (f : M →ₗ[K] M) (g : N →ₗ[K] N)
    (hf : ∀ x,f x∈F u) (hg : ∀ y,g y∈G v) (z : M⊗[K]N) :
    TensorProduct.map f g z ∈ additiveTensorFiltration F G W := by
  induction z using OAI.tensorInductionOn with
  | tmul x y => exact tmul_mem_additiveTensorFiltration F G h (hf x) (hg y)
  | add x y hx hy =>
    rw [map_add]
    exact (additiveTensorFiltration F G W).add_mem hx hy

theorem additiveTensorFiltration_iff_tests
    {ι : Type i} {κ : Type j} {D : ι → Type v} {E : κ → Type w}
    [∀ i,AddCommGroup (D i)] [∀ i,Module K (D i)]
    [∀ j,AddCommGroup (E j)] [∀ j,Module K (E j)]
    (t : ∀ i,M →ₗ[K] D i) (s : ∀ j,N →ₗ[K] E j)
    (wt : ι → ℤ) (ws : κ → ℤ) (L R : ℤ)
    (hL : testFiltration t wt L=⊤) (hR : testFiltration s ws R=⊤)
    (W : ℤ) (z : M⊗[K]N) :
    z∈additiveTensorFiltration (testFiltration t wt) (testFiltration s ws) W ↔
      ∀ i j, wt i+ws j<W → TensorProduct.map (t i) (s j) z=0 := by
  classical
  constructor
  · intro hz i j hij
    have hle : additiveTensorFiltration (testFiltration t wt) (testFiltration s ws) W ≤
        LinearMap.ker (TensorProduct.map (t i) (s j)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨u,v,x,y,huv,hx,hy,rfl⟩
      change TensorProduct.map (t i) (s j) (x⊗ₜ[K]y)=0
      rw [TensorProduct.map_tmul]
      by_cases hi : wt i<u
      · rw [(mem_testFiltration t wt u x).mp hx i hi,TensorProduct.zero_tmul]
      · have hj : ws j<v := by omega
        rw [(mem_testFiltration s ws v y).mp hy j hj,TensorProduct.tmul_zero]
    exact hle hz
  · intro hz
    by_cases hlow : W≤L+R
    · have hx : ∀ x : M,x∈testFiltration t wt L := by simp [hL]
      have hy : ∀ y : N,y∈testFiltration s ws R := by simp [hR]
      have h := map_mem_additiveTensorFiltration (testFiltration t wt) (testFiltration s ws)
        hlow LinearMap.id LinearMap.id hx hy z
      simpa only [TensorProduct.map_id,LinearMap.id_apply] using h
    let n : ℕ := (W-L-R).toNat
    have hn : (n : ℤ)=W-L-R := Int.toNat_of_nonneg (by omega)
    let F : ℕ → Submodule K M := fun i=>testFiltration t wt (L+i)
    let G : ℕ → Submodule K N := fun j=>testFiltration s ws (R+j)
    have hF : Antitone F := by
      intro i j hij
      exact testFiltration_antitone t wt (by omega)
    have hG : Antitone G := by
      intro i j hij
      exact testFiltration_antitone s ws (by omega)
    have hF0 : F 0=⊤ := by simpa only [F,Nat.cast_zero,add_zero] using hL
    have hG0 : G 0=⊤ := by simpa only [G,Nat.cast_zero,add_zero] using hR
    rw [← tensor_sum_pieces F G hF0 hG0 n z]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    by_cases hij : i.val+j.val<n
    · have hin : i.val<n := by omega
      have hjn : j.val<n := by omega
      have hiKer : (⨅ a : {a // wt a<L+(i.val : ℤ)+1}, LinearMap.ker (t a.val)) ≤
          LinearMap.ker (filtrationPiece F n i) := by
        intro x hx
        apply filtrationPiece_kernel F hF n i hin
        rw [mem_testFiltration]
        intro a ha
        exact (Submodule.mem_iInf _).mp hx ⟨a,by simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using ha⟩
      have hjKer : (⨅ b : {b // ws b<R+(j.val : ℤ)+1}, LinearMap.ker (s b.val)) ≤
          LinearMap.ker (filtrationPiece G n j) := by
        intro y hy
        apply filtrationPiece_kernel G hG n j hjn
        rw [mem_testFiltration]
        intro b hb
        exact (Submodule.mem_iInf _).mp hy ⟨b,by simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hb⟩
      have he : TensorProduct.map (filtrationPiece F n i) (filtrationPiece G n j) z=0 := by
        apply tensor_map_zero_of_test_kernels
          (fun a : {a // wt a<L+(i.val : ℤ)+1}=>t a.val)
          (fun b : {b // ws b<R+(j.val : ℤ)+1}=>s b.val)
          _ _ hiKer hjKer
        intro a b
        apply hz
        have ha := a.property
        have hb := b.property
        omega
      rw [he]
      exact Submodule.zero_mem _
    · apply map_mem_additiveTensorFiltration (testFiltration t wt) (testFiltration s ws)
        (u:=L+i.val) (v:=R+j.val) (by omega)
        (filtrationPiece F n i) (filtrationPiece G n j)
      · exact filtrationPiece_mem F hF n i
      · exact filtrationPiece_mem G hG n j

end ElementaryPositivity.LinearDetection

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.LinearDetection
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

structure RestrictionIndex (c η : I → ℝ) (θ : ℝ) (d : I → ℕ) where
  tree : SplitTree I
  ordered : tree.IsOrderedList
  onSlope : tree.OnSlope c η θ
  dimension : tree.dim=d
  degree : tree.Degrees
  center : tree.Centers →₀ ℕ

def RestrictionIndex.weight (a : I → I → ℕ) {c η : I → ℝ} {θ : ℝ} {d : I → ℕ}
    (j : RestrictionIndex c η θ d) : ℤ :=
  2*j.tree.totalDegree j.degree+j.tree.doubleShift a

noncomputable def indexedRestriction (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (j : RestrictionIndex c η θ d) :=
  restrictionTest a c η hc θ j.tree j.onSlope j.dimension j.degree j.center

lemma sourceFiltration_eq_testFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    sourceFiltration a c η hc θ d W = testFiltration (indexedRestriction a c η hc θ d)
      (RestrictionIndex.weight a) W := by
  ext f
  rw [mem_testFiltration]
  constructor
  · intro hf j hj
    exact hf j.tree j.ordered j.onSlope j.dimension j.degree j.center hj
  · intro hf T hT hs hd k z hw
    exact hf ⟨T,hT,hs,hd,k,z⟩ hw

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.IndependentCoefficientTensor
open MvPolynomial
variable {α β R : Type*} [CommRing R]

lemma sumElim_eq_iff (a c : α →₀ ℕ) (b d : β →₀ ℕ) :
    a.sumElim b=c.sumElim d ↔ a=c ∧ b=d := by
  constructor
  · intro h
    constructor
    · ext i; exact congrArg (fun f : α ⊕ β →₀ ℕ=>f (Sum.inl i)) h
    · ext i; exact congrArg (fun f : α ⊕ β →₀ ℕ=>f (Sum.inr i)) h
  · rintro ⟨rfl,rfl⟩; rfl

lemma coeff_independent_product (p : MvPolynomial α R) (q : MvPolynomial β R)
    (z : α →₀ ℕ) (w : β →₀ ℕ) :
    (rename Sum.inl p * rename Sum.inr q).coeff (z.sumElim w)=p.coeff z*q.coeff w := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp only [map_add,add_mul,MvPolynomial.coeff_add,Finsupp.add_apply,hp,hr]
  | monomial a c =>
    induction q using MvPolynomial.induction_on' with
    | add q r hq hr => simp only [map_add,mul_add,MvPolynomial.coeff_add,Finsupp.add_apply,hq,hr]
    | monomial b d =>
      rw [rename_monomial,rename_monomial,monomial_mul_monomial,←Finsupp.sumElim_eq_add]
      simp only [coeff_monomial,sumElim_eq_iff]
      by_cases ha : a=z <;> by_cases hb : b=w <;> simp [ha,hb]

end ElementaryPositivity.IndependentCoefficientTensor

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.IndependentCoefficientTensor
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace SplitTree

lemma centerTranslation_node_coeff (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T U : SplitTree I) (z : T.Centers →₀ ℕ) (w : U.Centers →₀ ℕ)
    (x : tensor (quotientFamily a μ) (.node T U)) :
    (centerTranslation (quotientFamily a μ) (taylorB a μ) (.node T U) x).coeff (z.sumElim w)=
      TensorProduct.map
        (((lcoeff _ z).restrictScalars ℚ).comp (centerTranslation (quotientFamily a μ) (taylorB a μ) T).toLinearMap)
        (((lcoeff _ w).restrictScalars ℚ).comp (centerTranslation (quotientFamily a μ) (taylorB a μ) U).toLinearMap) x := by
  induction x using OAI.tensorInductionOn with
  | tmul x y =>
    erw [centerTranslation_tmul]
    change
      (rename Sum.inl (map (Algebra.TensorProduct.includeLeft : tensor (quotientFamily a μ) T →ₐ[ℚ]
        tensor (quotientFamily a μ) T ⊗[ℚ] tensor (quotientFamily a μ) U).toRingHom
        (centerTranslation (quotientFamily a μ) (taylorB a μ) T x)) *
       rename Sum.inr (map (Algebra.TensorProduct.includeRight : tensor (quotientFamily a μ) U →ₐ[ℚ]
        tensor (quotientFamily a μ) T ⊗[ℚ] tensor (quotientFamily a μ) U).toRingHom
        (centerTranslation (quotientFamily a μ) (taylorB a μ) U y))).coeff (z.sumElim w)=_
    rw [coeff_independent_product,coeff_map,coeff_map]
    change (_⊗ₜ[ℚ]1)*(1⊗ₜ[ℚ]_)=_
    rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
    rfl
  | add x y hx hy => simp only [map_add,MvPolynomial.coeff_add,Finsupp.add_apply,hx,hy]

lemma restrictionTest_node (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (T U : SplitTree I) (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (k : T.Degrees) (l : U.Degrees) (z : T.Centers →₀ ℕ) (w : U.Centers →₀ ℕ)
    (f : B a (SlopeArithmetic.slope c η) (T.dim+U.dim)) :
    restrictionTest a c η hc θ (.node T U) ⟨hT,hU⟩ rfl (k,l) (z.sumElim w) f=
    TensorProduct.map (restrictionTest a c η hc θ T hT rfl k z)
      (restrictionTest a c η hc θ U hU rfl l w)
      (RawShuffle.restrictionB a c η hc ((slope_dim c η hc hT).trans (slope_dim c η hc hU).symm)
        (firstCut T.dim U.dim) f) := by
  change componentTensor a (SlopeArithmetic.slope c η) (.node T U) (k,l)
    ((centerTranslation _ _ (.node T U)
      (restrictionB a c η hc θ (.node T U) ⟨hT,hU⟩ f)).coeff (z.sumElim w))=_
  rw [centerTranslation_node_coeff]
  simp only [restrictionB,AlgHom.comp_apply]
  generalize RawShuffle.restrictionB a c η hc ((slope_dim c η hc hT).trans (slope_dim c η hc hU).symm) (firstCut T.dim U.dim) f=x
  induction x using OAI.tensorInductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]
end SplitTree

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LaurentIdealCoefficients
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
variable {R : Type*} [CommRing R]

lemma map_quotient_eq_zero_iff (J : Ideal R) (x : LaurentSeries R) :
    mapRing (Ideal.Quotient.mk J) x=0 ↔ ∀ k,x.coeff k∈J := by
  constructor
  · intro h k
    have he:=congrArg (fun f : LaurentSeries (R⧸J)=>f.coeff k) h
    simpa only [mapRing_coeff,HahnSeries.coeff_zero,Pi.zero_apply,Ideal.Quotient.eq_zero_iff_mem] using he
  · intro h
    apply HahnSeries.ext
    funext k
    simpa only [mapRing_coeff,HahnSeries.coeff_zero,Pi.zero_apply,Ideal.Quotient.eq_zero_iff_mem] using h k

lemma coeff_mul_mem (J : Ideal R) (x y : LaurentSeries R)
    (hx : ∀ k,x.coeff k∈J) (k : ℤ) : (x*y).coeff k∈J := by
  apply (map_quotient_eq_zero_iff J (x*y)).mp _ k
  rw [map_mul,(map_quotient_eq_zero_iff J x).mpr hx,zero_mul]

lemma polynomial_coeff_mem (J : Ideal R) (p : Polynomial R)
    (hp : ∀ n,p.coeff n∈J) (k : ℤ) : (polynomial p).coeff k∈J := by
  by_cases hk : k≤0
  · obtain ⟨n,hn⟩:=Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hk)
    have he : k=-(n:ℤ) := by omega
    rw [he,polynomial_coeff]
    exact hp n
  · rw [polynomial_coeff_positive p k (lt_of_not_ge hk)]
    exact J.zero_mem
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentPolynomialAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma mulPolynomialCoeff_mem (J : Ideal R) (k : LaurentSeries R) (j : ℤ) (p : Polynomial R)
    (hp : ∀ n,p.coeff n∈J) : mulPolynomialCoeff k j p∈J := by
  rw [mulPolynomialCoeff_apply,mul_comm]
  exact coeff_mul_mem J _ _ (polynomial_coeff_mem J p hp) _
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TensorFiltrationIdeals
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

lemma additiveTensorFiltration_mul_mem (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (hF : ∀ w x y,x∈F w → x*y∈F w) (hG : ∀ w x y,x∈G w → x*y∈G w)
    (W : ℤ) (x y : A⊗[K]B) (hx : x∈additiveTensorFiltration F G W) :
    x*y∈additiveTensorFiltration F G W := by
  have hgen {u v : ℤ} {a : A} {b : B} (hw : W≤u+v) (ha : a∈F u) (hb : b∈G v)
      (z : A⊗[K]B) : (a⊗ₜ[K]b)*z ∈ additiveTensorFiltration F G W := by
    induction z using OAI.tensorInductionOn with
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_additiveTensorFiltration F G hw (hF u a c ha) (hG v b d hb)
    | add z t hz ht =>
      rw [mul_add]
      exact (additiveTensorFiltration F G W).add_mem hz ht
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u,v,a,b,hw,ha,hb,rfl⟩:=hz
    exact hgen hw ha hb y
  | zero => simp only [zero_mul]; exact (additiveTensorFiltration F G W).zero_mem
  | add z t _ _ hz ht =>
    rw [add_mul]
    exact (additiveTensorFiltration F G W).add_mem hz ht
  | smul c z _ hz =>
    rw [smul_mul_assoc]
    exact (additiveTensorFiltration F G W).smul_mem c hz

noncomputable def additiveTensorFiltrationIdeal (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (hF : ∀ w x y,x∈F w → x*y∈F w) (hG : ∀ w x y,x∈G w → x*y∈G w)
    (W : ℤ) : Ideal (A⊗[K]B) where
  __ := (additiveTensorFiltration F G W).toAddSubmonoid
  smul_mem' c x hx := by
    change c*x∈additiveTensorFiltration F G W
    rw [mul_comm]
    exact additiveTensorFiltration_mul_mem F G hF hG W x c hx
end ElementaryPositivity.LinearDetection

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SeparationCoefficients
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace SeparationInfinity

noncomputable def separationSeries (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) :
    B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      LaurentSeries (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) :=
  (mulPolynomial (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) d e).val).comp
    (restrictionRelativeB a c η hc hs (firstCut d e)).toLinearMap

lemma separationCoefficient_eq_coeff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (j : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    separationCoefficient a c η hc hs j f = (separationSeries a c η hc hs f).coeff (-j) := rfl

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Restriction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CoefficientIdeals
variable {R : Type*} [CommRing R]
lemma polynomial_map_quotient_eq_zero_iff (J : Ideal R) (p : Polynomial R) :
    Polynomial.map (Ideal.Quotient.mk J) p=0 ↔ ∀ n,p.coeff n∈J := by
  constructor
  · intro hp n
    have h:=congrArg (fun p : Polynomial (R⧸J)=>p.coeff n) hp
    simpa only [Polynomial.coeff_map,Polynomial.coeff_zero,Ideal.Quotient.eq_zero_iff_mem] using h
  · intro hp
    ext n
    simpa only [Polynomial.coeff_map,Polynomial.coeff_zero,Ideal.Quotient.eq_zero_iff_mem] using hp n
end ElementaryPositivity.CoefficientIdeals

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentLinearNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
@[simp] lemma mapLinear_single (f : R →ₗ[ℚ] S) (n : ℤ) (r : R) :
    mapLinear f (single n r)=single n (f r) := by
  apply HahnSeries.ext
  funext k
  simp only [mapLinear_coeff,coeff_single]
  split_ifs <;> simp

lemma polynomial_mapLinear (f : R →ₗ[ℚ] S) (p : Polynomial R) :
    mapLinear f (polynomial p)=polynomial (RawShuffle.polynomialMapLinear f p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n r => rw [RawShuffle.polynomialMapLinear_monomial,polynomial_monomial,
      polynomial_monomial,mapLinear_single]
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CenterLineSpecialization
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A B σ : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

noncomputable def lineSpecialization (v h : σ → ℚ) : MvPolynomial σ A →+* Polynomial A :=
  eval₂Hom Polynomial.C (fun i=>Polynomial.C (algebraMap ℚ A (v i))+
    Polynomial.C (algebraMap ℚ A (h i))*Polynomial.X)

@[simp] lemma lineSpecialization_C (v h : σ → ℚ) (a : A) :
    lineSpecialization v h (C a)=Polynomial.C a := by
  simp only [lineSpecialization,eval₂Hom_C]
@[simp] lemma lineSpecialization_X (v h : σ → ℚ) (i : σ) :
    lineSpecialization (A:=A) v h (X i)=Polynomial.C (algebraMap ℚ A (v i))+
      Polynomial.C (algebraMap ℚ A (h i))*Polynomial.X := by
  simp only [lineSpecialization,coe_eval₂Hom,eval₂_X]

lemma lineSpecialization_eval (v h : σ → ℚ) (p : MvPolynomial σ A) (t : ℚ) :
    (lineSpecialization v h p).eval (algebraMap ℚ A t)=
      evalRat (fun i=>v i+h i*t) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [lineSpecialization_C,Polynomial.eval_C,evalRat_C]
  | add p q hp hq => simp only [map_add,Polynomial.eval_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.eval_mul,hp,lineSpecialization_X,evalRat_X,
      Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,map_add,map_mul]

lemma lineSpecialization_mapLinear (v h : σ → ℚ) (l : A →ₗ[ℚ] B)
    (p : MvPolynomial σ A) :
    lineSpecialization v h (mapLinear l p)=
      RawShuffle.polynomialMapLinear l (lineSpecialization v h p) := by
  apply RawShuffle.polynomial_eq_of_rat_evals
  intro t
  rw [lineSpecialization_eval,RawShuffle.polynomialMapLinear_eval_rat,
    lineSpecialization_eval,evalRat_mapLinear]
end ElementaryPositivity.CenterCalculus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellTransferSeparation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SeparationInfinity

noncomputable def mixedInverseKernelUnit (a b : I → I → ℕ)
    (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    (LaurentSeries (B a μ d⊗[ℚ] B a μ e))ˣ :=
  Units.map (mapRing (R:=S d⊗[ℚ]S e) (S:=B a μ d⊗[ℚ]B a μ e)
    (Algebra.TensorProduct.map (quotientAlg a μ d) (quotientAlg a μ e)).toRingHom).toMonoidHom
    (inverseKernelUnit b d e)

noncomputable def braidingRatioUnit (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e : I → ℕ) : (LaurentSeries (B a μ d⊗[ℚ]B a μ e))ˣ :=
  mixedInverseKernelUnit a a μ d e *
    (mixedInverseKernelUnit a (fun i j=>a j i) μ d e)⁻¹

end SeparationInfinity

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorPolynomialBox
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
open scoped TensorProduct
variable {α β A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

noncomputable def box (p : MvPolynomial α A) (q : MvPolynomial β B) :
    MvPolynomial (α ⊕ β) (A ⊗[ℚ] B) :=
  rename Sum.inl (map (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] B).toRingHom p) *
  rename Sum.inr (map (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A ⊗[ℚ] B).toRingHom q)

lemma coeff_box (p : MvPolynomial α A) (q : MvPolynomial β B)
    (z : α →₀ ℕ) (w : β →₀ ℕ) :
    (box p q).coeff (z.sumElim w) = p.coeff z ⊗ₜ[ℚ] q.coeff w := by
  rw [box,IndependentCoefficientTensor.coeff_independent_product,coeff_map,coeff_map]
  change (_ ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

end ElementaryPositivity.CenterCalculus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CenterLineNaturality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A B σ : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
lemma lineSpecialization_map (v h : σ → ℚ) (f : A →ₐ[ℚ] B) (p : MvPolynomial σ A) :
    lineSpecialization v h (map f.toRingHom p)=
      (lineSpecialization v h p).map f.toRingHom := by
  have hf (r : ℚ) : f.toRingHom (algebraMap ℚ A r)=algebraMap ℚ B r := f.commutes r
  induction p using MvPolynomial.induction_on with
  | C a => simp only [map_C,lineSpecialization_C,Polynomial.map_C]
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,map_X,lineSpecialization_X,Polynomial.map_add,Polynomial.map_mul,
      Polynomial.map_C,Polynomial.map_X,hf,hp]

lemma lineSpecialization_map_algebra (v h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    lineSpecialization (A:=A) v h (map (algebraMap ℚ A) p)=
      (lineSpecialization v h p).map (algebraMap ℚ A) :=
  lineSpecialization_map v h (Algebra.ofId ℚ A) p
end ElementaryPositivity.CenterCalculus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentScalarAction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma mapLinear_scalar_mul (f : R →ₗ[ℚ] R) (q : LaurentSeries ℚ) (p : LaurentSeries R) :
    mapLinear f (mapRing (algebraMap ℚ R) q*p)=
      mapRing (algebraMap ℚ R) q*mapLinear f p := by
  apply HahnSeries.ext
  funext k
  rw [mapLinear_coeff,coeff_mul,
    coeff_mul_right' p.isPWO_support (by
      intro n hn
      change f (p.coeff n)≠0 at hn
      exact fun h=>hn (h ▸ f.map_zero))]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  change f (algebraMap ℚ R (q.coeff ij.1)*p.coeff ij.2)=
    algebraMap ℚ R (q.coeff ij.1)*f (p.coeff ij.2)
  rw [←Algebra.smul_def,←Algebra.smul_def,f.map_smul]
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open HahnSeries SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance braidCoeffTensorS (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance

namespace SeparationInfinity
noncomputable local instance braidCoeffTensorSA_rb6af84_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance braidCoeffTensorB_rb6af84_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidCoeffTensorBA_rb6af84_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidCoeffTensorBM_rb6af84_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Module (B a μ d⊗[ℚ]B a μ e) (B a μ d⊗[ℚ]B a μ e) := Semiring.toModule
lemma inverseKernelUnit_zero_left (b : I → I → ℕ) (e : I → ℕ) :
    inverseKernelUnit b 0 e=1 := by
  apply Units.ext
  apply mapRing_injective (tensorValueAlg 0 e).toRingHom (tensorValue_injective 0 e)
  rw [realize_inverseKernelUnit,Units.val_one,map_one]
  simp only [rawInverseKernelUnit,Pi.zero_apply,Finset.univ_eq_empty,Finset.prod_empty,
    Finset.prod_const_one,Units.val_one]

lemma inverseKernelUnit_zero_right (b : I → I → ℕ) (d : I → ℕ) :
    inverseKernelUnit b d 0=1 := by
  apply Units.ext
  apply mapRing_injective (tensorValueAlg d 0).toRingHom (tensorValue_injective d 0)
  rw [realize_inverseKernelUnit,Units.val_one,map_one]
  simp only [rawInverseKernelUnit,Pi.zero_apply,Finset.univ_eq_empty,Finset.prod_empty,
    Finset.prod_const_one,Units.val_one]

end SeparationInfinity

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_ProductUnitFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma B_zero_eq_scalar (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (f : B a μ 0) :
    ∃ r : ℚ, f=r • (1 : B a μ 0) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    refine ⟨constantCoeff f.val,?_⟩
    change quotientAlg a μ 0 f=constantCoeff f.val • (1 : B a μ 0)
    have h:=congrArg (quotientAlg a μ 0) (S_zero_eq_scalar f)
    simpa only [map_smul,map_one] using h

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TensorFiltrationInterchange
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C D E F : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

lemma additiveTensorFiltration_antitone (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B) :
    Antitone (additiveTensorFiltration P Q) := by
  intro u v h
  apply Submodule.span_mono
  rintro x ⟨a,b,f,g,hab,hf,hg,rfl⟩
  exact ⟨a,b,f,g,le_trans h hab,hf,hg,rfl⟩

lemma tensor_map_mem_filtration (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (S : ℤ → Submodule K D)
    (f : A →ₗ[K] C) (g : B →ₗ[K] D)
    (hf : ∀ w x,x∈P w → f x∈R w) (hg : ∀ w y,y∈Q w → g y∈S w)
    (W : ℤ) (x : A⊗[K]B) (hx : x∈additiveTensorFiltration P Q W) :
    TensorProduct.map f g x∈additiveTensorFiltration R S W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,v,a,b,hw,ha,hb,rfl⟩:=hx
    rw [TensorProduct.map_tmul]
    exact tmul_mem_additiveTensorFiltration R S hw (hf u a ha) (hg v b hb)
  | zero => rw [map_zero]; exact (additiveTensorFiltration R S W).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (additiveTensorFiltration R S W).add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact (additiveTensorFiltration R S W).smul_mem r hx

lemma interchange_mem_filtration
    (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (S : ℤ → Submodule K D)
    (U V : ℤ) (x : A⊗[K]B) (y : C⊗[K]D)
    (hx : x∈additiveTensorFiltration P Q U) (hy : y∈additiveTensorFiltration R S V) :
    TensorProduct.tensorTensorTensorComm K A B C D (x⊗ₜ[K]y)∈
    additiveTensorFiltration (additiveTensorFiltration P R) (additiveTensorFiltration Q S) (U+V) := by
  let J:=additiveTensorFiltration (additiveTensorFiltration P R)
    (additiveTensorFiltration Q S) (U+V)
  let τ:=TensorProduct.tensorTensorTensorComm K A B C D
  change τ (x⊗ₜ[K]y)∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,v,a,b,hu,ha,hb,rfl⟩:=hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w,z,c,d,hv,hc,hd,rfl⟩:=hy
      change (a⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]d)∈J
      exact tmul_mem_additiveTensorFiltration _ _ (show U+V≤(u+w)+(v+z) by omega)
        (tmul_mem_additiveTensorFiltration P R (le_refl _) ha hc)
        (tmul_mem_additiveTensorFiltration Q S (le_refl _) hb hd)
    | zero => rw [TensorProduct.tmul_zero,τ.map_zero]; exact J.zero_mem
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add,τ.map_add]; exact J.add_mem hy hz
    | smul r y _ hy => rw [TensorProduct.tmul_smul,τ.map_smul]; exact J.smul_mem r hy
  | zero => rw [TensorProduct.zero_tmul,τ.map_zero]; exact J.zero_mem
  | add x z _ _ hx hz => rw [TensorProduct.add_tmul,τ.map_add]; exact J.add_mem hx hz
  | smul r x _ hx => rw [←TensorProduct.smul_tmul',τ.map_smul]; exact J.smul_mem r hx

lemma lift_mem_filtration (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (hR : Antitone R) (f : A →ₗ[K] B →ₗ[K] C)
    (hf : ∀ u v x y,x∈P u → y∈Q v → f x y∈R (u+v))
    (W : ℤ) (x : A⊗[K]B) (hx : x∈additiveTensorFiltration P Q W) :
    TensorProduct.lift f x∈R W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,v,a,b,hw,ha,hb,rfl⟩:=hx
    rw [TensorProduct.lift.tmul]
    exact hR hw (hf u v a b ha hb)
  | zero => rw [map_zero]; exact (R W).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (R W).add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact (R W).smul_mem r hx
end ElementaryPositivity.LinearDetection

end
section
namespace ElementaryPositivity.LinearFiltration
variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
noncomputable def next (F G : Submodule ℚ M) : Submodule ℚ F := G.comap F.subtype
def Grade (F G : Submodule ℚ M) := F ⧸ next F G
noncomputable instance instAddCommGroupGrade (F G : Submodule ℚ M) : AddCommGroup (Grade F G) :=
  inferInstanceAs (AddCommGroup (F ⧸ next F G))
noncomputable instance instModuleRatGrade (F G : Submodule ℚ M) : Module ℚ (Grade F G) :=
  inferInstanceAs (Module ℚ (F ⧸ next F G))
noncomputable def mk (F G : Submodule ℚ M) : F →ₗ[ℚ] Grade F G := (next F G).mkQ
noncomputable def restrict (F : Submodule ℚ M) (G : Submodule ℚ N)
    (f : M →ₗ[ℚ] N) (h : ∀ x∈F,f x∈G) : F →ₗ[ℚ] G :=
  (f.comp F.subtype).codRestrict G (fun x=>h x.val x.property)
noncomputable def map (F F' : Submodule ℚ M) (G G' : Submodule ℚ N)
    (f : M →ₗ[ℚ] N) (h : ∀ x∈F,f x∈G) (h' : ∀ x∈F',f x∈G') :
    Grade F F' →ₗ[ℚ] Grade G G' :=
  (next F F').liftQ ((next G G').mkQ.comp (restrict F G f h)) (by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h' x.val hx))
end ElementaryPositivity.LinearFiltration

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TensorMiddleFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C D : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]

noncomputable def middleInsert (a : A) (d : D) :
    C⊗[K]B →ₗ[K] (A⊗[K]C)⊗[K](B⊗[K]D) :=
  TensorProduct.map (TensorProduct.mk K A C a) ((TensorProduct.mk K B D).flip d)

end ElementaryPositivity.LinearDetection

end
section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C D : Type*} [Field K]
  [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]

noncomputable def middleEmbedding : C⊗[K]B →ₐ[K] (A⊗[K]C)⊗[K](B⊗[K]D) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeLeft

end ElementaryPositivity.LinearDetection

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourBraiding
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearDetection ElementaryPositivity.LaurentAtInfinity
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SeparationInfinity

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensor
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorA
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorM
lemma quotientInverseKernelUnit_zero_left (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (e : I → ℕ) :
    quotientInverseKernelUnit a μ 0 e=1 := by
  simp only [quotientInverseKernelUnit,inverseKernelUnit_zero_left,map_one]
lemma quotientInverseKernelUnit_zero_right (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    quotientInverseKernelUnit a μ d 0=1 := by
  simp only [quotientInverseKernelUnit,inverseKernelUnit_zero_right,map_one]

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LinearFiltrationBilinear
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M N P : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  [AddCommGroup P] [Module ℚ P]

noncomputable def bilinearRestrict (F : Submodule ℚ M) (G : Submodule ℚ N) (H : Submodule ℚ P)
    (μ : M →ₗ[ℚ] N →ₗ[ℚ] P) (h : ∀ x∈F,∀ y∈G,μ x y∈H) : F →ₗ[ℚ] G →ₗ[ℚ] H where
  toFun x := restrict G H (μ x.val) (h x.val x.property)
  map_add' x y := by ext z; exact μ.map_add₂ x.val y.val z.val
  map_smul' r x := by ext z; exact μ.map_smul₂ r x.val z.val

noncomputable def bilinear (F F' : Submodule ℚ M) (G G' : Submodule ℚ N)
    (H H' : Submodule ℚ P) (μ : M →ₗ[ℚ] N →ₗ[ℚ] P)
    (h : ∀ x∈F,∀ y∈G,μ x y∈H)
    (hl : ∀ x∈F',∀ y∈G,μ x y∈H') (hr : ∀ x∈F,∀ y∈G',μ x y∈H') :
    Grade F F' →ₗ[ℚ] Grade G G' →ₗ[ℚ] Grade H H' := by
  let μ₀:=bilinearRestrict F G H μ h
  let L : F →ₗ[ℚ] Grade G G' →ₗ[ℚ] Grade H H' :=
    { toFun x := (next G G').liftQ ((mk H H').comp (μ₀ x)) (by
        intro y hy
        exact (Submodule.Quotient.mk_eq_zero _).mpr (hr x.val x.property y.val hy))
      map_add' := by
        intro x y
        ext z
        induction z using Submodule.Quotient.induction_on with
        | H z => exact congrArg (mk H H') (μ₀.map_add₂ x y z)
      map_smul' := by
        intro r x
        ext z
        induction z using Submodule.Quotient.induction_on with
        | H z =>
          change mk H H' (μ₀ (r • x) z) = r • mk H H' (μ₀ x z)
          rw [μ₀.map_smul₂, map_smul] }
  exact (next F F').liftQ L (by
    intro x hx
    ext y
    induction y using Submodule.Quotient.induction_on with
    | H y => exact (Submodule.Quotient.mk_eq_zero _).mpr (hl x.val hx y.val y.property))

end ElementaryPositivity.LinearFiltration

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TensorAssociatedGrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
open LinearDetection
open scoped TensorProduct DirectSum
variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]

noncomputable def gradeProjection (F : ℤ → Submodule ℚ M) (u : ℤ) :
    M →ₗ[ℚ] Grade (F u) (F (u+1)) :=
  (mk _ _).comp ((retract (F u)).codRestrict _ (retract_mem _))

lemma gradeProjection_mem (F : ℤ → Submodule ℚ M) (u : ℤ) (x : F u) :
    gradeProjection F u x.val=mk (F u) (F (u+1)) x := by
  apply congrArg (mk _ _)
  apply Subtype.ext
  exact retract_eq_self _ x.property

lemma gradeProjection_zero (F : ℤ → Submodule ℚ M) (hF : Antitone F) (u v : ℤ)
    (huv : u<v) (x : M) (hx : x∈F v) : gradeProjection F u x=0 := by
  have hx' : x∈F u:=hF (le_of_lt huv) hx
  rw [gradeProjection_mem F u ⟨x,hx'⟩]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hF (by omega) hx)

abbrev TensorGrade (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N) (W : ℤ) :=
  Grade (additiveTensorFiltration F G W) (additiveTensorFiltration F G (W+1))

lemma tensorProjection_kills (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (u v : ℤ) :
    additiveTensorFiltration F G (u+v+1)≤
      LinearMap.ker (TensorProduct.map (gradeProjection F u) (gradeProjection G v)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,b,x,y,hab,hx,hy,rfl⟩
  change TensorProduct.map _ _ (x⊗ₜ[ℚ]y)=0
  rw [TensorProduct.map_tmul]
  by_cases ha : u<a
  · rw [gradeProjection_zero F hF u a ha x hx,TensorProduct.zero_tmul]
  · have hb : v<b:=by omega
    rw [gradeProjection_zero G hG v b hb y hy,TensorProduct.tmul_zero]

abbrev TensorGradePart (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N) (W u : ℤ) :=
  Grade (F u) (F (u+1)) ⊗[ℚ] Grade (G (W-u)) (G (W-u+1))

noncomputable def tensorGradeInclusionW (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W u : ℤ) : TensorGradePart F G W u →ₗ[ℚ] TensorGrade F G W :=
  TensorProduct.lift (bilinear (F u) (F (u+1)) (G (W-u)) (G (W-u+1))
    (additiveTensorFiltration F G W) (additiveTensorFiltration F G (W+1))
    (TensorProduct.mk ℚ M N)
    (fun _ hx _ hy=>tmul_mem_additiveTensorFiltration F G (by omega) hx hy)
    (fun _ hx _ hy=>tmul_mem_additiveTensorFiltration F G (by omega) hx hy)
    (fun _ hx _ hy=>tmul_mem_additiveTensorFiltration F G (by omega) hx hy))

lemma tensorGradeInclusionW_mk (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W u : ℤ) (x : F u) (y : G (W-u)) :
    tensorGradeInclusionW F G W u (mk _ _ x⊗ₜ[ℚ]mk _ _ y)=
      mk _ _ ⟨x.val⊗ₜ[ℚ]y.val,tmul_mem_additiveTensorFiltration F G (by omega) x.property y.property⟩ := rfl

noncomputable def tensorGradeProjectionW (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) :
    TensorGrade F G W →ₗ[ℚ] TensorGradePart F G W u :=
  (next _ _).liftQ ((TensorProduct.map (gradeProjection F u) (gradeProjection G (W-u))).comp
    (additiveTensorFiltration F G W).subtype) (by
      intro x hx
      apply tensorProjection_kills F G hF hG u (W-u)
      change x.val∈additiveTensorFiltration F G (W+1) at hx
      change x.val∈additiveTensorFiltration F G (u+(W-u)+1)
      simpa only [add_sub_cancel] using hx)

lemma tensorGradeProjectionW_mk (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) (x : additiveTensorFiltration F G W) :
    tensorGradeProjectionW F G hF hG W u (mk _ _ x)=
      TensorProduct.map (gradeProjection F u) (gradeProjection G (W-u)) x.val := rfl

lemma tensorGradeProjectionW_inclusion_self (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) :
    (tensorGradeProjectionW F G hF hG W u).comp (tensorGradeInclusionW F G W u)=LinearMap.id := by
  ext x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      change tensorGradeProjectionW F G hF hG W u
        (tensorGradeInclusionW F G W u (mk _ _ x⊗ₜ[ℚ]mk _ _ y))=mk _ _ x⊗ₜ[ℚ]mk _ _ y
      rw [tensorGradeInclusionW_mk,tensorGradeProjectionW_mk,TensorProduct.map_tmul,
        gradeProjection_mem,gradeProjection_mem]

lemma tensorGradeProjectionW_inclusion_ne (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u j : ℤ) (huj : u≠j) :
    (tensorGradeProjectionW F G hF hG W u).comp (tensorGradeInclusionW F G W j)=0 := by
  ext x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      change tensorGradeProjectionW F G hF hG W u
        (tensorGradeInclusionW F G W j (mk _ _ x⊗ₜ[ℚ]mk _ _ y))=0
      rw [tensorGradeInclusionW_mk,tensorGradeProjectionW_mk,TensorProduct.map_tmul]
      by_cases h : u<j
      · rw [gradeProjection_zero F hF u j h x.val x.property,TensorProduct.zero_tmul]
      · rw [gradeProjection_zero G hG (W-u) (W-j) (by omega) y.val y.property,TensorProduct.tmul_zero]

noncomputable def tensorGradeSum (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) : (⨁ u : ℤ,TensorGradePart F G W u) →ₗ[ℚ] TensorGrade F G W :=
  DirectSum.toModule ℚ ℤ _ (tensorGradeInclusionW F G W)

lemma tensorGradeProjectionW_sum (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) :
    (tensorGradeProjectionW F G hF hG W u).comp (tensorGradeSum F G W)=
      DirectSum.component ℚ ℤ (TensorGradePart F G W) u := by
  apply DirectSum.linearMap_ext
  intro j
  by_cases h : j=u
  · subst j
    apply LinearMap.ext
    intro x
    change tensorGradeProjectionW F G hF hG W u
      (tensorGradeSum F G W (DirectSum.lof ℚ ℤ _ u x))=_
    rw [tensorGradeSum,DirectSum.toModule_lof,LinearMap.comp_apply,DirectSum.component.lof_self]
    exact LinearMap.congr_fun (tensorGradeProjectionW_inclusion_self F G hF hG W u) x
  · apply LinearMap.ext
    intro x
    change tensorGradeProjectionW F G hF hG W u
      (tensorGradeSum F G W (DirectSum.lof ℚ ℤ _ j x))=_
    rw [tensorGradeSum,DirectSum.toModule_lof,LinearMap.comp_apply,DirectSum.component.of,dite_eq_right h]
    exact LinearMap.congr_fun (tensorGradeProjectionW_inclusion_ne F G hF hG W u j (Ne.symm h)) x

lemma tensorGradeSum_injective (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W : ℤ) : Function.Injective (tensorGradeSum F G W) := by
  intro x y hxy
  apply DirectSum.ext_component ℚ
  intro u
  rw [←tensorGradeProjectionW_sum F G hF hG W u]
  exact congrArg (tensorGradeProjectionW F G hF hG W u) hxy

lemma tensorGradeSum_surjective (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) : Function.Surjective (tensorGradeSum F G W) := by
  rw [←LinearMap.range_eq_top,eq_top_iff]
  intro x _
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change mk _ _ x∈LinearMap.range (tensorGradeSum F G W)
    have h : ∀ (z : M⊗[ℚ]N) (hz : z∈additiveTensorFiltration F G W),
        mk _ _ ⟨z,hz⟩∈LinearMap.range (tensorGradeSum F G W) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        rcases hz with ⟨u,v,x,y,hw,hx,hy,rfl⟩
        by_cases he : W=u+v
        · have hv : v=W-u:=by omega
          subst v
          refine ⟨DirectSum.lof ℚ ℤ _ u (mk _ _ ⟨x,hx⟩⊗ₜ[ℚ]mk _ _ ⟨y,hy⟩),?_⟩
          rw [tensorGradeSum,DirectSum.toModule_lof,tensorGradeInclusionW_mk]
        · have hz' : x⊗ₜ[ℚ]y∈additiveTensorFiltration F G (W+1):=
            tmul_mem_additiveTensorFiltration F G (by omega) hx hy
          have he : (mk _ _ ⟨x⊗ₜ[ℚ]y,tmul_mem_additiveTensorFiltration F G hw hx hy⟩ : TensorGrade F G W)=0 :=
            (Submodule.Quotient.mk_eq_zero _).mpr hz'
          rw [he]
          exact Submodule.zero_mem _
      | zero => exact Submodule.zero_mem _
      | add x y hx hy hix hiy =>
        exact (LinearMap.range (tensorGradeSum F G W)).add_mem hix hiy
      | smul r x hx hix => exact (LinearMap.range (tensorGradeSum F G W)).smul_mem r hix
    exact h x.val x.property

noncomputable def tensorGradeEquiv (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W : ℤ) :
    (⨁ u : ℤ,TensorGradePart F G W u) ≃ₗ[ℚ] TensorGrade F G W :=
  LinearEquiv.ofBijective (tensorGradeSum F G W)
    ⟨tensorGradeSum_injective F G hF hG W,tensorGradeSum_surjective F G W⟩

end ElementaryPositivity.LinearFiltration

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalTensorGradeInclusion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
open scoped TensorProduct DirectSum
variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]

lemma tensorGradeEquiv_lof (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) (x : TensorGradePart F G W u) :
    tensorGradeEquiv F G hF hG W (DirectSum.lof ℚ ℤ (TensorGradePart F G W) u x)=
      tensorGradeInclusionW F G W u x := by
  change DirectSum.toModule ℚ ℤ _ _ _=_
  rw [DirectSum.toModule_lof]

lemma tensorGradeEquiv_symm_inclusion (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) (x : TensorGradePart F G W u) :
    (tensorGradeEquiv F G hF hG W).symm (tensorGradeInclusionW F G W u x)=
      DirectSum.lof ℚ ℤ (TensorGradePart F G W) u x := by
  apply (tensorGradeEquiv F G hF hG W).injective
  rw [LinearEquiv.apply_symm_apply,tensorGradeEquiv_lof]

lemma tensorGrade_induction (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W : ℤ) (P : TensorGrade F G W → Prop)
    (hz : P 0) (ha : ∀ x y,P x → P y → P (x+y))
    (ht : ∀ u (x : Grade (F u) (F (u+1))) (y : Grade (G (W-u)) (G (W-u+1))),
      P (tensorGradeInclusionW F G W u (x⊗ₜ[ℚ]y))) (x : TensorGrade F G W) : P x := by
  obtain ⟨z,rfl⟩ := (tensorGradeEquiv F G hF hG W).surjective x
  induction z using DirectSum.induction_on with
  | zero => simpa only [map_zero] using hz
  | add x y hx hy => rw [map_add]; exact ha _ _ hx hy
  | of u z =>
    change P (tensorGradeEquiv F G hF hG W (DirectSum.lof ℚ ℤ (TensorGradePart F G W) u z))
    rw [tensorGradeEquiv_lof]
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => rw [map_add]; exact ha _ _ hx hy
    | tmul x y => exact ht u x y
end ElementaryPositivity.LinearFiltration

end

end OAI
end


