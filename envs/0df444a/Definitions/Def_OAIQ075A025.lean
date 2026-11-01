-- Prove2me | Definitions.Def_OAIQ075A025
-- name    : OAIQ075A025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:22:42.038994+00:00
-- url     : https://prove2.me/theorems/3d2a0584-da6d-4a5a-a0e7-c0ab06f9d7eb
-- title:
--   Definitions bundle OAIQ075A025 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 3 definitions and 8 theorems. The definitions and types are `OAI.KadisonSimilarity.finiteOrbitGenerators`, `OAI.KadisonSimilarity.invariantStarRepresentation`, `OAI.KadisonSimilarity.tracialUltrapowerCompression`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonSimilarity_Representation_FiniteOrbitSubspace`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/FiniteOrbitSubspace.lean), [`KadisonSimilarity_Representation_NonseparableReduction`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/NonseparableReduction.lean), [`KadisonSimilarity_Representation_ProperlyInfiniteStructure`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/ProperlyInfiniteStructure.lean), [`KadisonSimilarity_Representation_SquareArrayPadding`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/SquareArrayPadding.lean), [`KadisonSimilarity_Tensor_MultiplicityClassification`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tensor/MultiplicityClassification.lean), [`KadisonSimilarity_Tracial_TracialUltrapowerActions`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialUltrapowerActions.lean).
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A013`, `OAIQ075A016` and `OAIQ075A017` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ075A029`; the statements `OAI_KadisonSimilarity_TracialCornerGeometry_exists_actual_spectral_test`, `OAI_KadisonSimilarity_concrete_repeated_propagation` and `OAI_KadisonSimilarity_normal_standard_embedding_of_normal_gns`; the proofs of `OAI_KadisonSimilarity_TracialCornerGeometry_exists_actual_spectral_test`, `OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests` and `OAI.KadisonSimilarity.similarityTheorem`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A013
import Definitions.Def_OAIQ075A016
import Definitions.Def_OAIQ075A017

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteOrbitSubspace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed invariant subspace generated by finitely many vectors is
finitely cyclic, and therefore its restricted representation is similar. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
theorem finiteOrbitSubspace_invariant (π : BoundedUnitalHom A H)
    {n : ℕ} (ξ : Fin n → H) (a : A) (x : H) (hx : x ∈ finiteOrbitSubspace π ξ) :
    π.1 a x ∈ finiteOrbitSubspace π ξ := by
  have hm : Set.MapsTo (π.1 a) (Set.range (finiteOrbitMap π ξ))
      (Set.range (finiteOrbitMap π ξ)) := by
    rintro y ⟨b, rfl⟩
    refine ⟨fun i => a * b i, ?_⟩
    simp only [finiteOrbitMap, LinearMap.coe_mk, AddHom.coe_mk, map_mul,
      mul_apply_eq_comp, map_sum]
  exact hm.closure (π.1 a).continuous hx

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
theorem mem_finiteOrbitSubspace (π : BoundedUnitalHom A H)
    {n : ℕ} (ξ : Fin n → H) (i : Fin n) : ξ i ∈ finiteOrbitSubspace π ξ := by
  apply (LinearMap.range (finiteOrbitMap π ξ)).le_topologicalClosure
  refine ⟨Pi.single i 1, ?_⟩
  simp [finiteOrbitMap, Pi.single_apply, apply_ite, ite_apply]

def finiteOrbitGenerators (π : BoundedUnitalHom A H) {n : ℕ} (ξ : Fin n → H) :
    Fin n → finiteOrbitSubspace π ξ := fun i => ⟨ξ i, mem_finiteOrbitSubspace π ξ i⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SquareArrayPadding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Zero padding of Hilbert arrays

The coordinate inclusion along an arbitrary finite injection is isometric.
Extension of an operator by zero consequently preserves scalar commutator
norms and the norms of their matrix amplifications. No dimension factor occurs.
-/

noncomputable section
namespace KadisonSimilarity

section MatrixIndices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

@[simp] theorem padOperatorMatrix_apply_image (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) (i j : Fin r) :
    padOperatorMatrix e X (e i) (e j) = X i j := by
  simp [padOperatorMatrix, e.injective.eq_iff, ite_and]

end MatrixIndices

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NonseparableReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_adjoint _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing separability from the uniform commutator estimate

Each operator-norm test involves finitely many matrix entries and finitely
many vectors. Their common reducing subspace is separable. We restrict the
actual C-star algebra generated by those entries, use the two-vector
Kaplansky specialization to reach its bicommutant, and recover the original
vector test by the isometric inclusion.
-/

noncomputable section
universe u
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restriction of an invariant star subalgebra to the closed subspace. -/
def invariantStarRepresentation (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (M : ClosedSubmodule ℂ H)
    (hM : ∀ a : B, ∀ x : H, x ∈ M → (a : H →L[ℂ] H) x ∈ M) :
    B →⋆ₐ[ℂ] (M →L[ℂ] M) where
  toFun a := (a : H →L[ℂ] H).restrict (hM a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    let : CompleteSpace M.toSubmodule := M.isClosed.completeSpace_coe
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : H) ((star a : H →L[ℂ] H) (x : H)) =
      inner ℂ y (((a : H →L[ℂ] H).restrict (hM a)).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem invariantStarRepresentation_apply
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) (M : ClosedSubmodule ℂ H)
    (hM : ∀ a : B, ∀ x : H, x ∈ M → (a : H →L[ℂ] H) x ∈ M)
    (a : B) (x : M) : (invariantStarRepresentation B M hM a x : H) = a.val x := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProperlyInfiniteStructure
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.concretePredual_separable _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.unitCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.unitCornerTrace_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.sourceCornerHom_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two orthogonal isometries yield every finite internal isometry row.
The concrete Banach predual supplies the structural existence theorem. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

attribute [local instance] OAI.KadisonSimilarity.infiniteStructureClosed
theorem internal_isometry_rows_of_no_finite_central_summand
    (hno : BoundedHochschild.KadisonRingrose.NoFiniteCentralSummand P.toStarSubalgebra) :
    HasInternalIsometryRows P := by
  obtain ⟨v, w, hv, hw, hvw⟩ :=
    BoundedHochschild.KadisonRingrose.exists_two_orthogonal_isometries
      (concretePredualEquiv P) hno
  intro n
  refine ⟨fun i => binaryIsometryFamily v w i.val, fun i j => ?_⟩
  simpa only [Fin.val_inj] using binaryIsometryFamily_orthogonal v w hv hw hvw i.val j.val

open BoundedHochschild.KadisonRingrose HochschildCorners
open scoped ComplexOrder

theorem no_finite_central_summand_of_infinite_factor
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (hinfinite : ¬ FiniteAlgebra P.toStarSubalgebra) :
    NoFiniteCentralSummand P.toStarSubalgebra := by
  have hex : ∃ a : P.toStarSubalgebra, star a * a = 1 ∧ a * star a ≠ 1 := by
    simpa only [FiniteAlgebra, not_forall, _root_.not_imp, exists_prop] using hinfinite
  obtain ⟨a, _, ha⟩ := hex
  let : Nontrivial P.toStarSubalgebra := nontrivial_of_ne (a * star a) 1 ha
  intro p hp hcentral hfinite
  rcases central_projection_zero_or_one hfactor p hp hcentral with hz | hunit
  · exact hz
  · subst p
    exfalso
    apply hinfinite
    intro b hb
    let bC : Corner (1 : P.toStarSubalgebra) hp := ⟨b, by
      change 1 * b = b ∧ b * 1 = b
      simp⟩
    have hbC : star bC * bC = 1 := Subtype.ext hb
    exact congrArg (fun c : Corner (1 : P.toStarSubalgebra) hp =>
      (c : P.toStarSubalgebra)) (hfinite bC hbC)

theorem internal_isometry_rows_of_infinite_factor
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (hinfinite : ¬ FiniteAlgebra P.toStarSubalgebra) : HasInternalIsometryRows P :=
  internal_isometry_rows_of_no_finite_central_summand P
    (no_finite_central_summand_of_infinite_factor P hfactor hinfinite)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_MultiplicityClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hilbert multiplicities in the invariant-intertwiner theorem

Scalar matrix coefficients in the multiplicity Hilbert space are genuine
bounded endpoint intertwiners. Tensor totality reconstructs the full operator
from these slices. Repeated-letter compressions provide the bounded operator
on the multiplicity space used in propagation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {G H K L : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

variable [CompleteSpace H] [CompleteSpace K]

omit [CompleteSpace H] in
/-- Elementary tensor coefficients separate vectors in the completed product. -/
theorem hilbertTensor_ext_inner_insert (z w : HilbertTensor G H)
    (h : ∀ a x, inner ℂ (hilbertTensorInsert a x) z =
      inner ℂ (hilbertTensorInsert a x) w) : z = w := by
  have heq : innerSL ℂ z = innerSL ℂ w := by
    apply continuousLinearMap_ext_hilbertTensorInsert
    intro a x
    change inner ℂ z (hilbertTensorInsert a x) = inner ℂ w (hilbertTensorInsert a x)
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (h a x)
  apply ext_inner_right ℂ
  intro v
  exact congrArg (fun A : HilbertTensor G H →L[ℂ] ℂ => A v) heq

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialUltrapowerActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded left-multiplier sequences reduce the tracial GNS subspace of
the Hilbert ultrapower. The compressed operator therefore inherits every
eventual coordinate commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower HochschildUltrapower
open scoped ENNReal Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- Compression of the constant Hilbert-ultrapower operator to the tracial
quotient's GNS space. No invariance of the original operator is needed. -/
def tracialUltrapowerCompression (T : τ.GNS →L[ℂ] τ.GNS) :
    (quotientTrace τ h1 ω htr).GNS →L[ℂ] (quotientTrace τ h1 ω htr).GNS :=
  (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap.adjoint.comp
    ((HilbertUltraproduct.map ω (boundedConstant T)).comp
      (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap)

end KadisonSimilarity

end

end OAI
end


