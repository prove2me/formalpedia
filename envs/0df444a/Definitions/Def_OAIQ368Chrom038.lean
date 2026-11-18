-- Prove2me | Definitions.Def_OAIQ368Chrom038
-- name    : OAIQ368Chrom038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:27:14.723626+00:00
-- url     : https://prove2.me/theorems/a07a8712-51f7-4e27-8db1-7210f8a761ac
-- title:
--   Definitions bundle OAIQ368Chrom038 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 16 definitions, 1 inductive type or structure and 1 theorem. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.HNIndex`, `OAI.ElementaryPositivity.RawShuffle.HNTensor`, `OAI.ElementaryPositivity.RawShuffle.IsHNDetector`, `OAI.ElementaryPositivity.RawShuffle.clippedToOriginal`, `OAI.ElementaryPositivity.RawShuffle.consDetector`, `OAI.ElementaryPositivity.RawShuffle.fullShape`, `OAI.ElementaryPositivity.RawShuffle.headRestriction`, `OAI.ElementaryPositivity.RawShuffle.hnPolynomial`, `OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion`, `OAI.ElementaryPositivity.RawShuffle.quotientDetector`, `OAI.ElementaryPositivity.RawShuffle.rawClearedSeparation`, `OAI.ElementaryPositivity.RawShuffle.rawRelativeSeries`, `OAI.ElementaryPositivity.RawShuffle.singletonDetector`, `OAI.ElementaryPositivity.RawShuffle.zeroShape`, `OAI.ElementaryPositivity.SlopeArithmetic.HNOrdered`, `OAI.ElementaryPositivity.SlopeArithmetic.clippedSlope`, `OAI.ElementaryPositivity.SlopeArithmetic.hnKeyLT`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_CutoffGrid`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CutoffGrid.lean), [`Chromatic_Shuffle_HNDetectorBasics`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNDetectorBasics.lean), [`Chromatic_Shuffle_HNDiagonal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNDiagonal.lean), [`Chromatic_Shuffle_HNExpansion`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNExpansion.lean), [`Chromatic_Shuffle_HNIndependent`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNIndependent.lean), [`Chromatic_Shuffle_HNPolynomial`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNPolynomial.lean), [`Chromatic_Walls_HNGeometry`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/HNGeometry.lean), [`Chromatic_Walls_HNMatrixTriangular`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/HNMatrixTriangular.lean), [`Chromatic_Walls_HNRestrictionOrder`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/HNRestrictionOrder.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom026` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom054`; the statements `OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head` and `OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective`; the proofs of `OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head` and `OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom026

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNRestrictionOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ)
noncomputable def clippedSlope (θ : ℝ) (d : I → ℕ) : ℝ := max (slope c η d) θ
end ElementaryPositivity.SlopeArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ)

def HNOrdered (l : List (I → ℕ)) : Prop :=
  (∀ d∈l,d≠0) ∧ l.Pairwise (fun d e=>slope c η e < slope c η d)

end ElementaryPositivity.SlopeArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)
noncomputable def HNTensor : List (I → ℕ) → CommAlgCat.{u} ℚ
  | [] => CommAlgCat.of ℚ (S (0 : I → ℕ))
  | d::l => CommAlgCat.of ℚ (B a (slope c η) d⊗[ℚ]HNTensor l)

abbrev HNIndex (d : I → ℕ) := {l : List (I → ℕ) // l.sum=d ∧ HNOrdered c η l}
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorDistrib cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule

noncomputable def rawClearedSeparation (a : I → I → ℕ) (d e : I → ℕ) :
    S d⊗[ℚ]S e →ₗ[ℚ] LaurentSeries (S d⊗[ℚ]S e) :=
  (mulPolynomial (inverseKernelUnit a d e*(inverseKernelUnit (fun _ _ : I=>0) d e)⁻¹).val).comp
    (relativeTaylor d e).toLinearMap

noncomputable def rawRelativeSeries (d e : I → ℕ) (x : S d⊗[ℚ]S e) :
    LaurentSeries (S d⊗[ℚ]S e) := polynomial (relativeTaylor d e x)

end ElementaryPositivity.RawShuffle

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CutoffGrid
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA

noncomputable def headRestriction (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    S (d+e) →ₗ[ℚ] B a μ d⊗[ℚ]B a μ e :=
  ((coeff.linearMap (R:=ℚ) 0).comp
    ((mulPolynomial (mixedInverseKernelUnit a a μ d e).val).comp
      (relativeTaylorB a μ d e).toLinearMap)).comp
    ((quotientTensor a μ d e).toLinearMap.comp (restrictTensorAlg (firstCut d e)).toLinearMap)

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

noncomputable def fullShape (s : Pack (A:=A)) : CutShape s := fun i=>Fin.last (s i).card
noncomputable def zeroShape (s : Pack (A:=A)) : CutShape s := fun _=>0
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNPolynomial
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

noncomputable def hnPolynomial (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) :
    (l : List (I → ℕ)) → HNTensor a c η l →ₗ[ℚ] S l.sum
  | [] => LinearMap.id
  | d::l => (shuffleTensorLinear a d l.sum).comp (TensorProduct.map (σ d) (hnPolynomial σ l))

lemma clipped_destabilizingSpace_le (κ : ℝ) (d : I → ℕ) :
    destabilizingSpace a (clippedSlope c η κ) d ≤ destabilizingSpace a (slope c η) d := by
  apply Submodule.span_le.mpr
  rintro f ⟨u,v,h,x,y,hu,hv,hs,rfl⟩
  apply Submodule.subset_span
  refine ⟨u,v,h,x,y,hu,hv,?_,rfl⟩
  have H := (lt_max_iff.mp hs).resolve_right (not_lt_of_ge (le_max_right _ _))
  exact (le_max_left _ _).trans_lt H

noncomputable def clippedToOriginal (κ : ℝ) (d : I → ℕ) :
    B a (clippedSlope c η κ) d →ₗ[ℚ] B a (slope c η) d :=
  Submodule.mapQ _ _ LinearMap.id (clipped_destabilizingSpace_le a c η κ d)
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNMatrixTriangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ) (hc : ∀ i,0 < c i)
noncomputable def hnKeyLT (d e : I → ℕ) : Prop :=
  slope c η d < slope c η e ∨ slope c η d=slope c η e ∧ mass c d < mass c e
end ElementaryPositivity.SlopeArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNDetectorBasics
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

noncomputable def singletonDetector (d : I → ℕ) : S ([d].sum) →ₗ[ℚ] HNTensor a c η [d] :=
  (((TensorProduct.mk ℚ (B a (slope c η) d) (S (0 : I → ℕ))).flip 1).comp
    (quotientAlg a (slope c η) d).toLinearMap).comp (dimensionCast (add_zero d))
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

structure IsHNDetector (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l) : Prop where
  ideal : ∀ θ : ℝ,(∀ d∈l,slope c η d ≤ θ) → ∀ f : S l.sum,
    f∈destabilizingSpace a (clippedSlope c η θ) l.sum → D f=0
  diagonal : D.comp (hnPolynomial a c η σ l)=LinearMap.id
  off : ∀ (r : List (I → ℕ)),HNOrdered c η r → ∀ h : r.sum=l.sum,
    ¬List.Lex (hnKeyLT c η) r l → r≠l → ∀ x : HNTensor a c η r,
    D (castS h (hnPolynomial a c η σ r x))=0

noncomputable def quotientDetector (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l)
    (κ : ℝ) (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0) :
    B a (clippedSlope c η κ) l.sum →ₗ[ℚ] HNTensor a c η l :=
  (destabilizingSpace a (clippedSlope c η κ) l.sum).liftQ D (fun f hf=>hk f hf)

noncomputable def consDetector (d : I → ℕ) (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l)
    (κ : ℝ) (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0) :
    S (d::l).sum →ₗ[ℚ] HNTensor a c η (d::l) :=
  (TensorProduct.map (clippedToOriginal a c η κ d) (quotientDetector a c η l D κ hk)).comp
    (headRestriction a (clippedSlope c η κ) d l.sum)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNIndependent
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

noncomputable def hnPolynomialExpansion (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    (⨁ l : HNIndex c η d,HNTensor a c η l.val) →ₗ[ℚ] S d :=
  DirectSum.toModule ℚ _ _ (fun l=>(dimensionCast l.property.1).comp (hnPolynomial a c η σ l.val))

end ElementaryPositivity.RawShuffle

end

end OAI
end


