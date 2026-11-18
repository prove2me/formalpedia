-- Prove2me | Definitions.Def_OAIQ368Chrom030
-- name    : OAIQ368Chrom030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:32:49.758791+00:00
-- url     : https://prove2.me/theorems/295c1405-9804-4070-8374-cd8bf3c52830
-- title:
--   Definitions bundle OAIQ368Chrom030 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 12 definitions, 5 instances and 10 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.SplitTree.pairRelativeRefinement`, `OAI.ElementaryPositivity.RawShuffle.UnitalShuffle`, `OAI.ElementaryPositivity.RawShuffle.UnitalSourceGrade`, `OAI.ElementaryPositivity.RawShuffle.UnitalSourceTensorGrade`, `OAI.ElementaryPositivity.RawShuffle.bothLeading`, `OAI.ElementaryPositivity.RawShuffle.globalTensorGradeInclusion`, `OAI.ElementaryPositivity.RawShuffle.unitalComponent`, `OAI.ElementaryPositivity.RawShuffle.unitalGradeCast`, `OAI.ElementaryPositivity.RawShuffle.unitalGradeOne`, `OAI.ElementaryPositivity.RawShuffle.unitalSourceTensorGradeEquiv`, `OAI.ElementaryPositivity.RawShuffle.unitalTensorGradeCast`, `OAI.ElementaryPositivity.RawShuffle.unitalTensorGradeInclusionW`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_QuantumTorus_ProductUnitFiltration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/ProductUnitFiltration.lean), [`Chromatic_Shuffle_BothTaylorB`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/BothTaylorB.lean), [`Chromatic_Shuffle_GlobalTensorGradeProduct`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalTensorGradeProduct.lean), [`Chromatic_Shuffle_ManyBlockDiagonal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/ManyBlockDiagonal.lean), [`Chromatic_Shuffle_SignedTensorGradeProduct`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/SignedTensorGradeProduct.lean), [`Chromatic_Shuffle_UnitalGrade`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalGrade.lean), [`Chromatic_Shuffle_UnitalGradeAlgebra`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalGradeAlgebra.lean), [`Chromatic_Shuffle_UnitalShuffleCoproduct`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalShuffleCoproduct.lean), [`Chromatic_Shuffle_UnitalTensorGradeInclusion`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalTensorGradeInclusion.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom026` and `OAIQ368Chrom029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom031` and `OAIQ368Chrom034`; the proofs of `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds` and `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom026
import Definitions.Def_OAIQ368Chrom029

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

lemma bothTaylorB_eval (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d ⊗[ℚ] B a μ e) (z w : ℚ) :
    evalTwo (bothTaylorB a μ d e x) z w=
      TensorProduct.map (translationB a μ d z) (translationB a μ e w) x := by
  induction x using OAI.tensorInductionOn with
  | tmul f g =>
    change evalTwo
      (Polynomial.C (Polynomial.map (Algebra.TensorProduct.includeLeft :
        B a μ d →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e).toRingHom (taylorB a μ d f)) *
        Polynomial.map ((Polynomial.CAlgHom : (B a μ d ⊗[ℚ] B a μ e) →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e)).comp
          (Algebra.TensorProduct.includeRight : B a μ e →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e)).toRingHom
          (taylorB a μ e g)) z w = _
    simp only [evalTwo,Polynomial.eval_mul,Polynomial.eval_C,eval_map_rat,taylorB_eval,
      AlgHom.comp_apply,Polynomial.CAlgHom_apply,Polynomial.eval_C,TensorProduct.map_tmul]
    change (translationB a μ d z f ⊗ₜ[ℚ] 1)*(1 ⊗ₜ[ℚ] translationB a μ e w g)=_
    rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  | add x y hx hy => simp only [map_add,evalTwo,Polynomial.eval_add] at *; rw [hx,hy]

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def bothLeading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) : B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      Polynomial (Polynomial (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e)) :=
  (polynomialMapLinear (polynomialMapLinear (TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d p)
    (componentB a (SlopeArithmetic.slope c η) e q)))).comp
      ((bothTaylorB a (SlopeArithmetic.slope c η) d e).toLinearMap.comp
        (restrictionB a c η hc hs (firstCut d e)).toLinearMap)

lemma bothLeading_eval (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e)) (z w : ℚ) :
    evalTwo (bothLeading a c η hc hs p q f) z w =
      TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d p)
        (componentB a (SlopeArithmetic.slope c η) e q)
        (TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d z)
          (translationB a (SlopeArithmetic.slope c η) e w)
          (restrictionB a c η hc hs (firstCut d e) f)) := by
  simp only [bothLeading,LinearMap.comp_apply,AlgHom.toLinearMap_apply,evalTwo,
    polynomialMapLinear_eval_rat]
  rw [← evalTwo,bothTaylorB_eval]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ManyBlockDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
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

noncomputable def pairRelativeRefinement (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I) :
    tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T) →ₐ[ℚ]
      Polynomial (tensor (quotientFamily a (SlopeArithmetic.slope c η))
        (.node (.node (.leaf d) (.leaf e)) T)) :=
  polynomialOnLeft
    (D := tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf d) (.leaf e)))
    ((relativeTaylorB a (SlopeArithmetic.slope c η) d e).comp
      (RawShuffle.restrictionB a c η hc hs (firstCut d e)))

lemma pairRelativeRefinement_eval_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I) (g : B a (SlopeArithmetic.slope c η) (d+e))
    (h : tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) (t : ℚ) :
    (pairRelativeRefinement a c η hc hs T (g ⊗ₜ[ℚ] h)).eval (algebraMap ℚ _ t) =
      TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d t)
        (LinearMap.id : B a (SlopeArithmetic.slope c η) e →ₗ[ℚ] B a (SlopeArithmetic.slope c η) e)
        (RawShuffle.restrictionB a c η hc hs (firstCut d e) g) ⊗ₜ[ℚ] h := by
  erw [pairRelativeRefinement,polynomialOnLeft_eval_tmul]
  congr 1
  exact relativeTaylorB_eval a (SlopeArithmetic.slope c η) d e _ t

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_ProductUnitFiltration
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
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma shuffleBUnit_filtered_zero_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (hs : (0 : I → ℕ)=0 ∨ d=0 ∨ slope c η 0=slope c η d)
    (U V : ℤ) (f : B a (slope c η) 0) (g : B a (slope c η) d)
    (hf : f∈unitalSourceFiltration a c η hc θ 0 U)
    (hg : g∈unitalSourceFiltration a c η hc θ d V) :
    shuffleBUnit a c η hc 0 d hs f g∈unitalSourceFiltration a c η hc θ (0+d) (U+V) := by
  classical
  by_cases hu : U≤0
  · obtain ⟨r,rfl⟩:=B_zero_eq_scalar a (slope c η) f
    rw [map_smul,LinearMap.smul_apply,shuffleBUnit_one_left]
    exact (unitalSourceFiltration a c η hc θ (0+d) (U+V)).smul_mem r
      (unitalSourceFiltration_antitone a c η hc θ (0+d) (by omega)
        (castB_mem_unitalSourceFiltration a c η hc θ (zero_add d).symm V hg))
  · have hz : f=0 := by simpa only [unitalSourceFiltration,ite_eq_left rfl,ite_eq_right hu,ite_true, if_true,Submodule.mem_bot] using hf
    rw [hz,map_zero,LinearMap.zero_apply]
    exact Submodule.zero_mem _

lemma shuffleBUnit_filtered_zero_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (hs : d=0 ∨ (0 : I → ℕ)=0 ∨ slope c η d=slope c η 0)
    (U V : ℤ) (f : B a (slope c η) d) (g : B a (slope c η) 0)
    (hf : f∈unitalSourceFiltration a c η hc θ d U)
    (hg : g∈unitalSourceFiltration a c η hc θ 0 V) :
    shuffleBUnit a c η hc d 0 hs f g∈unitalSourceFiltration a c η hc θ (d+0) (U+V) := by
  classical
  by_cases hv : V≤0
  · obtain ⟨r,rfl⟩:=B_zero_eq_scalar a (slope c η) g
    rw [map_smul,shuffleBUnit_one_right]
    exact (unitalSourceFiltration a c η hc θ (d+0) (U+V)).smul_mem r
      (unitalSourceFiltration_antitone a c η hc θ (d+0) (by omega)
        (castB_mem_unitalSourceFiltration a c η hc θ (add_zero d).symm U hf))
  · have hz : g=0 := by simpa only [unitalSourceFiltration,ite_eq_left rfl,ite_eq_right hv,ite_true, if_true,Submodule.mem_bot] using hg
    rw [hz,map_zero]
    exact Submodule.zero_mem _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalGrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open SeparationInfinity
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

def UnitalSourceGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :=
  Grade (unitalSourceFiltration a c η hc θ d W) (unitalSourceFiltration a c η hc θ d (W+1))
noncomputable instance instAddCommGroupUnitalSourceGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : AddCommGroup (UnitalSourceGrade a c η hc θ d W) :=
  inferInstanceAs (AddCommGroup (Grade _ _))
noncomputable instance instModuleRatUnitalSourceGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Module ℚ (UnitalSourceGrade a c η hc θ d W) :=
  inferInstanceAs (Module ℚ (Grade _ _))

def UnitalSourceTensorGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :=
  Grade (unitalSourceTensorFiltration a c η hc θ d e W)
    (unitalSourceTensorFiltration a c η hc θ d e (W+1))
noncomputable instance instAddCommGroupUnitalSourceTensorGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) : AddCommGroup (UnitalSourceTensorGrade a c η hc θ d e W) :=
  inferInstanceAs (AddCommGroup (Grade _ _))
noncomputable instance instModuleRatUnitalSourceTensorGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) : Module ℚ (UnitalSourceTensorGrade a c η hc θ d e W) :=
  inferInstanceAs (Module ℚ (Grade _ _))

noncomputable def unitalSourceTensorGradeEquiv (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    (⨁ u : ℤ,UnitalSourceGrade a c η hc θ d u ⊗[ℚ]
      UnitalSourceGrade a c η hc θ e (W-u)) ≃ₗ[ℚ]
      UnitalSourceTensorGrade a c η hc θ d e W :=
  tensorGradeEquiv (unitalSourceFiltration a c η hc θ d) (unitalSourceFiltration a c η hc θ e)
    (unitalSourceFiltration_antitone a c η hc θ d) (unitalSourceFiltration_antitone a c η hc θ e) W

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalGradeAlgebra
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def unitalGradeCast (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e : I → ℕ} {U V : ℤ} (h : d=e) (k : U=V) :
    UnitalSourceGrade a c η hc θ d U ≃ₗ[ℚ] UnitalSourceGrade a c η hc θ e V := by
  subst e
  subst V
  exact LinearEquiv.refl _ _

lemma unitalGradeCast_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e : I → ℕ} {U V : ℤ} (h : d=e) (k : U=V)
    (f : unitalSourceFiltration a c η hc θ d U) :
    unitalGradeCast a c η hc θ h k (Submodule.Quotient.mk f)=
      (Submodule.Quotient.mk (unitalFiltrationCast a c η hc θ h k f) :
        UnitalSourceGrade a c η hc θ e V) := by
  subst e
  subst V
  rfl

noncomputable def unitalGradeOne (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) : UnitalSourceGrade a c η hc θ 0 0 :=
  Submodule.Quotient.mk ⟨1,by simp [unitalSourceFiltration_zero]⟩

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev unitalComponent (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (k : SlopeWeight c η hc θ) :=
  UnitalSourceGrade a c η hc θ k.1.val k.2

lemma unitalGradeCast_heq (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e : I → ℕ} {U V : ℤ} (h : d=e) (k : U=V)
    (f : UnitalSourceGrade a c η hc θ d U) :
    HEq (unitalGradeCast a c η hc θ h k f) f := by
  subst e
  subst V
  rfl

noncomputable instance componentGradedOne (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) : GradedMonoid.GOne (unitalComponent a c η hc θ) where
  one := unitalGradeOne a c η hc θ

abbrev UnitalShuffle (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) :=
  ⨁ k : SlopeWeight c η hc θ,unitalComponent a c η hc θ k

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SignedTensorGradeProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open DimensionSplit SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def unitalTensorGradeCast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e d' e' : I → ℕ} {U V : ℤ}
    (h : d=d') (k : e=e') (w : U=V) :
    UnitalSourceTensorGrade a c η hc θ d e U ≃ₗ[ℚ]
      UnitalSourceTensorGrade a c η hc θ d' e' V := by
  subst d'; subst e'; subst V
  exact LinearEquiv.refl _ _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalShuffleCoproduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open scoped TensorProduct DirectSum
open DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def globalTensorGradeInclusion (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W : ℤ) :
    UnitalSourceTensorGrade a c η hc θ d.val e.val W →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  (DirectSum.toModule ℚ ℤ
    (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)
    (fun u=>TensorProduct.map
      (DirectSum.lof ℚ (SlopeWeight c η hc θ) (unitalComponent a c η hc θ) (d,u))
      (DirectSum.lof ℚ (SlopeWeight c η hc θ) (unitalComponent a c η hc θ) (e,W-u)))).comp
    (unitalSourceTensorGradeEquiv a c η hc θ d.val e.val W).symm.toLinearMap

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalTensorGradeInclusion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def unitalTensorGradeInclusionW (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ) (W u : ℤ) :
    UnitalSourceGrade a c η hc θ d u ⊗[ℚ] UnitalSourceGrade a c η hc θ e (W-u) →ₗ[ℚ]
      UnitalSourceTensorGrade a c η hc θ d e W :=
  tensorGradeInclusionW (unitalSourceFiltration a c η hc θ d)
    (unitalSourceFiltration a c η hc θ e) W u

lemma unitalTensorGrade_induction (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ) (W : ℤ)
    (P : UnitalSourceTensorGrade a c η hc θ d e W → Prop)
    (hz : P 0) (ha : ∀ x y,P x → P y → P (x+y))
    (ht : ∀ u (x : UnitalSourceGrade a c η hc θ d u)
      (y : UnitalSourceGrade a c η hc θ e (W-u)),
      P (unitalTensorGradeInclusionW a c η hc θ d e W u (x⊗ₜ[ℚ]y)))
    (x : UnitalSourceTensorGrade a c η hc θ d e W) : P x :=
  tensorGrade_induction _ _ (unitalSourceFiltration_antitone a c η hc θ d)
    (unitalSourceFiltration_antitone a c η hc θ e) W P hz ha ht x

lemma globalTensorGradeInclusion_part (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W u : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val u)
    (y : UnitalSourceGrade a c η hc θ e.val (W-u)) :
    globalTensorGradeInclusion a c η hc θ d e W
      (unitalTensorGradeInclusionW a c η hc θ d.val e.val W u (x⊗ₜ[ℚ]y))=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,u) x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,W-u) y := by
  change DirectSum.toModule ℚ ℤ _ _ ((unitalSourceTensorGradeEquiv a c η hc θ d.val e.val W).symm
    (tensorGradeInclusionW _ _ W u (x⊗ₜ[ℚ]y)))=_
  rw [show (unitalSourceTensorGradeEquiv a c η hc θ d.val e.val W).symm
      (tensorGradeInclusionW _ _ W u (x⊗ₜ[ℚ]y))=
      DirectSum.lof ℚ ℤ _ u (x⊗ₜ[ℚ]y) from tensorGradeEquiv_symm_inclusion _ _ _ _ W u _]
  rw [DirectSum.toModule_lof]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTensorGradeProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma unitalLof_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e : slopeDimensions c η hc θ} {U V : ℤ}
    (h : d.val=e.val) (k : U=V) (x : UnitalSourceGrade a c η hc θ d.val U) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,V) (unitalGradeCast a c η hc θ h k x)=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,U) x := by
  have hd : d=e := Subtype.ext h
  subst e; subst V
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end


