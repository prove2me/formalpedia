-- Prove2me | Definitions.Def_OAIQ368Chrom044
-- name    : OAIQ368Chrom044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:50:30.002889+00:00
-- url     : https://prove2.me/theorems/f433542c-55de-44f0-824d-9c999bf16541
-- title:
--   Definitions bundle OAIQ368Chrom044 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 4 definitions and 8 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.rightTripleBuild`, `OAI.ElementaryPositivity.RawShuffle.rightTripleEquiv`, `OAI.ElementaryPositivity.RawShuffle.rightTripleView`, `OAI.ElementaryPositivity.RawShuffle.sourceTensorGradeComm`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_GlobalSeriesEvaluation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalSeriesEvaluation.lean), [`Chromatic_Shuffle_GlobalTripleGradeInclusion`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalTripleGradeInclusion.lean), [`Chromatic_Shuffle_TensorSymbolSwap`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TensorSymbolSwap.lean), [`Chromatic_Shuffle_UnitalCoproductCoassociative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalCoproductCoassociative.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom039` and `OAIQ368Chrom040` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom045`; the statements `OAI_ElementaryPositivity_QuantumTorus_mutatedTransport_eq_path`, `OAI_ElementaryPositivity_QuantumTorus_polynomialSection_mutation`, `OAI_ElementaryPositivity_TriangularDynamics_triangularExpression_anchorSupported`, `OAI_ElementaryPositivity_TriangularDynamics_triangularLinear_theta` and `OAI_ElementaryPositivity_TriangularDynamics_triangularTheta_support`; the proofs of `OAI_ElementaryPositivity_QuantumTorus_mutatedTransport_eq_path`, `OAI_ElementaryPositivity_QuantumTorus_polynomialSection_mutation`, `OAI_ElementaryPositivity_TriangularDynamics_triangularExpression_anchorSupported`, `OAI_ElementaryPositivity_TriangularDynamics_triangularLinear_theta` and `OAI_ElementaryPositivity_TriangularDynamics_triangularTheta_support`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom039
import Definitions.Def_OAIQ368Chrom040

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorSymbolSwap
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open LinearFiltration
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cocommTensorBCommRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cocommTensorBAlgebra
lemma sourceGradeDimensionEquiv_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ) (f : sourceFiltration a c η hc θ d W) :
    sourceGradeDimensionEquiv a c η hc θ h W (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (filtrationDimensionEquiv a c η hc θ h W f) := by
  subst e
  rfl

noncomputable def sourceTensorGradeComm (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    SourceTensorAssociatedGrade a c η hc θ d e W →ₗ[ℚ] SourceTensorAssociatedGrade a c η hc θ e d W :=
  tensorGradeComm (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ e) W

lemma separationCoproduct_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ)
    (f : sourceFiltration a c η hc θ (d+e) W) :
    separationCoproduct a c η hc θ d e hs W (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (separationCoefficientRestricted a c η hc θ d e hs W 0 f) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalCoproductCoassociative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
  ElementaryPositivity.LinearFiltration SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] naturalTensorAdd naturalTensorModule pairAdd tripleAdd tripleFilterAdd

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalTripleRightAdd
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalTripleRightModule
lemma unitalSeparationConstant_eq_linear (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (d e : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (hde : slope c η d=slope c η e) :
    unitalSeparationConstant a c η hc d e hs=
      separationCoefficient a c η hc (d:=d) (e:=e) hde 0 := by
  apply LinearMap.ext
  intro x
  exact unitalSeparationConstant_eq a c η hc d e hs hde x

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTripleGradeInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

def rightTripleView (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ)
    (p : RightSlopeTriple c η hc θ d) : SlopeTriple c η hc θ d :=
  ⟨(left p.1.val,left p.2.val,right p.2.val),by
    exact ⟨by rw [add_assoc,left_add_right,left_add_right],p.1.property.1,p.2.property.1,p.2.property.2⟩⟩

omit [DecidableEq I] in
lemma rightTripleView_injective (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :
    Function.Injective (rightTripleView c η hc θ d) := by
  rintro ⟨s,t⟩ ⟨s',t'⟩ h
  have h1 : left s.val=left s'.val := congrArg (fun p=>p.val.1) h
  have h2 : left t.val=left t'.val := congrArg (fun p=>p.val.2.1) h
  have hs : s=s' := Subtype.ext (DimensionSplit.ext h1)
  subst s'
  have ht : t=t' := Subtype.ext (DimensionSplit.ext h2)
  subst t'
  rfl

omit [DecidableEq I] in
lemma rightTripleView_surjective (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :
    Function.Surjective (rightTripleView c η hc θ d) := by
  rintro ⟨⟨a,b,f⟩,hs,ha,hb,hf⟩
  have hs' : a+(b+f)=d := (add_assoc a b f).symm.trans hs
  let s : SlopeSplit c η hc θ d :=
    ⟨ofPair a (b+f) hs',by simpa only [left_ofPair,right_ofPair] using And.intro ha (hb.add hc hf)⟩
  have hr : b+f=right s.val := (right_ofPair a (b+f) hs').symm
  let t : SlopeSplit c η hc θ (right s.val) :=
    ⟨ofPair b f hr,by simpa only [left_ofPair,right_ofPair] using And.intro hb hf⟩
  refine ⟨⟨s,t⟩,?_⟩
  apply Subtype.ext
  change (left (ofPair a (b+f) hs'),left (ofPair b f hr),right (ofPair b f hr))=(a,b,f)
  simp only [left_ofPair,right_ofPair]

noncomputable def rightTripleEquiv (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :
    RightSlopeTriple c η hc θ d ≃ SlopeTriple c η hc θ d :=
  Equiv.ofBijective (rightTripleView c η hc θ d)
    ⟨rightTripleView_injective c η hc θ d,rightTripleView_surjective c η hc θ d⟩

def rightTripleBuild (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ)
    (p : SlopeTriple c η hc θ d) : RightSlopeTriple c η hc θ d :=
  ⟨⟨ofPair p.val.1 (p.val.2.1+p.val.2.2)
      ((add_assoc _ _ _).symm.trans p.property.1),
      by simpa only [left_ofPair,right_ofPair] using
        And.intro p.property.2.1 (p.property.2.2.1.add hc p.property.2.2.2)⟩,
    ⟨ofPair p.val.2.1 p.val.2.2 (by rw [right_ofPair]),
      by simpa only [left_ofPair,right_ofPair] using
        And.intro p.property.2.2.1 p.property.2.2.2⟩⟩

omit [DecidableEq I] in
lemma rightTripleView_build (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ)
    (p : SlopeTriple c η hc θ d) :
    rightTripleView c η hc θ d (rightTripleBuild c η hc θ d p)=p := by
  apply Subtype.ext
  simp only [rightTripleView,rightTripleBuild,left_ofPair,right_ofPair]

omit [DecidableEq I] in
lemma rightTripleBuild_view (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ)
    (p : RightSlopeTriple c η hc θ d) :
    rightTripleBuild c η hc θ d (rightTripleView c η hc θ d p)=p :=
  rightTripleView_injective c η hc θ d (rightTripleView_build c η hc θ d _)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalSeriesEvaluation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convVanishes_unit {A : Type*} [Ring A] [Algebra ℚ A]
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) : f.ofConv (globalUnit a c η hc θ)=0 :=
  hf (0,0) (by simp [dimensionSize]) (unitalGradeOne a c η hc θ)

end ElementaryPositivity.RawShuffle

end

end OAI
end


