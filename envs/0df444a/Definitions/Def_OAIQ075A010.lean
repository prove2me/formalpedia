-- Prove2me | Definitions.Def_OAIQ075A010
-- name    : OAIQ075A010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:00:50.917653+00:00
-- url     : https://prove2.me/theorems/97a83fb4-51b4-4f79-bdac-132f53611781
-- title:
--   Definitions bundle OAIQ075A010 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 110 declarations of OpenAI's Lean: 38 definitions, 1 inductive type or structure, 6 instances and 65 theorems. The definitions and types are `OAI.KadisonSimilarity.ColumnBound`, `OAI.KadisonSimilarity.CommonCyclicHilbert`, `OAI.KadisonSimilarity.CompleteBound`, `OAI.KadisonSimilarity.ConcretePredual`, `OAI.KadisonSimilarity.CyclicColumnTests`, `OAI.KadisonSimilarity.CyclicDecompositionData`, `OAI.KadisonSimilarity.CyclicDecompositionData.Space`, `OAI.KadisonSimilarity.CyclicDecompositionData.generator`, `OAI.KadisonSimilarity.CyclicDecompositionData.representation`, `OAI.KadisonSimilarity.CyclicDecompositionData.summands`, `OAI.KadisonSimilarity.CyclicOrbitOrthogonal`, `OAI.KadisonSimilarity.CyclicSpectralSpace`, `OAI.KadisonSimilarity.DicksonTwoBound`, `OAI.KadisonSimilarity.DihedralSpectralArcInput`, `OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary`, `OAI.KadisonSimilarity.IsCompletelyBounded`, `OAI.KadisonSimilarity.OrthogonalCyclicFamily`, `OAI.KadisonSimilarity.RectangularCompleteBound`, `OAI.KadisonSimilarity.RowBound`, `OAI.KadisonSimilarity.columnAction`, `OAI.KadisonSimilarity.concretePredualEquiv`, `OAI.KadisonSimilarity.concretePredualLinearEquiv`, `OAI.KadisonSimilarity.conjugateMomentTail`, `OAI.KadisonSimilarity.constantCopies`, `OAI.KadisonSimilarity.cyclicCommonBaseMeasure`, `OAI.KadisonSimilarity.cyclicFamilySpan`, `OAI.KadisonSimilarity.denseFamilyIsometry`, `OAI.KadisonSimilarity.matrixSystemOfUnits`, `OAI.KadisonSimilarity.normalCoefficient`, `OAI.KadisonSimilarity.normalFunctionalSpace`, `OAI.KadisonSimilarity.operatorOfPredual`, `OAI.KadisonSimilarity.orbitGenerator`, `OAI.KadisonSimilarity.predualCoefficient`, `OAI.KadisonSimilarity.predualCoefficientBilinear`, `OAI.KadisonSimilarity.predualEvaluation`, `OAI.KadisonSimilarity.predualEvaluationIsometry`, `OAI.KadisonSimilarity.predualForm`, `OAI.KadisonSimilarity.transportedCornerUnitary`, `OAI.KadisonSimilarity.vonNeumannInnerDerivation`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonSimilarity_Derivation_CommonCyclicEmbedding`, `KadisonSimilarity_Derivation_CountableCyclicDecomposition`, `KadisonSimilarity_Derivation_CyclicColumnTests`, `KadisonSimilarity_Derivation_CyclicDecomposition`, `KadisonSimilarity_Derivation_CyclicDerivations`, `KadisonSimilarity_Derivation_CyclicSpectralSum`, `KadisonSimilarity_Derivation_RectangularDerivations`, `KadisonSimilarity_FreeProduct_EvenAlternatingWords`, `KadisonSimilarity_FreeProduct_HankelCommutator`, `KadisonSimilarity_FreeProduct_ScalarFreeMonotone`, `KadisonSimilarity_FreeProduct_SpectralArc`, `KadisonSimilarity_Representation_ConcretePredual`, `KadisonSimilarity_Representation_ConcretePredualDuality`, `KadisonSimilarity_Representation_ConcretePredualRestriction`, `KadisonSimilarity_Representation_DenseFamilyIsometry`, `KadisonSimilarity_Representation_DyadicCornerHom`, `KadisonSimilarity_Representation_FactorAssembly`, `KadisonSimilarity_Representation_OrthogonalColumns`, `KadisonSimilarity_Representation_ProjectionComparisonTransport`, `KadisonSimilarity_Representation_ProperlyInfiniteEstimate`, `KadisonSimilarity_Representation_SeparableConcretePredual`, `KadisonSimilarity_Similarity_CompletelyBounded`, `KadisonSimilarity_Similarity_CompletelyBoundedImplementation`, `KadisonSimilarity_Tensor_InvariantCycles`, `KadisonSimilarity_Tracial_ConcreteHalfProjection`, `KadisonSimilarity_Tracial_ConcreteProjectionComparison`, `KadisonSimilarity_Tracial_ConjugateMomentCriterion`, `KadisonSimilarity_Tracial_DenseMomentExtension`, `KadisonSimilarity_Tracial_FiniteFactorPresentation`, `KadisonSimilarity_Tracial_FullColumnTheorem`, `KadisonSimilarity_Tracial_IntegerMomentMaps`, `KadisonSimilarity_Tracial_MatrixExpectationIdentification`, `KadisonSimilarity_Tracial_MatrixTracialGNS`, `KadisonSimilarity_Tracial_MatrixUnitCoordinates`, `KadisonSimilarity_Tracial_RelativeMatrixQuantization`, `KadisonSimilarity_Tracial_SourceAllMoments`, `KadisonSimilarity_Tracial_SourceConstantMoments`, `KadisonSimilarity_Tracial_SourceCornerQuantization`, `KadisonSimilarity_Tracial_SourceMomentConstruction`, `KadisonSimilarity_Tracial_SourceQuotientMoments`, `KadisonSimilarity_Tracial_SourceWeakPowers`, `KadisonSimilarity_Tracial_TracialCornerTransport`, `KadisonSimilarity_Tracial_TracialFactorComparison`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A000`, `OAIQ075A002`, `OAIQ075A003`, `OAIQ075A004` and `OAIQ075A005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A014`, `OAIQ075A017` and `OAIQ075A018`; the statement `OAI.KadisonSimilarity.dicksonTwoBound_proved`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A000
import Definitions.Def_OAIQ075A002
import Definitions.Def_OAIQ075A003
import Definitions.Def_OAIQ075A004
import Definitions.Def_OAIQ075A005

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete matrix norms and complete boundedness

The matrix norm used here is `CStarMatrix`'s C-star norm. The representation
on finite Hilbert sums is shown to preserve that norm, connecting the concrete
commutator estimate with the usual notion of complete boundedness.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section CompletelyBounded

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A uniform bound on all square matrix amplifications, with the C-star
matrix norm on the domain and the Hilbert operator norm on the codomain. -/
def CompleteBound (f : A → (H →L[ℂ] H)) (C : ℝ) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (Fin n) (Fin n) A,
    ‖matrixOperator (X.map f)‖ ≤ C * ‖CStarMatrix.ofMatrix X‖

/-- Complete boundedness in terms of the concrete matrix norm. -/
def IsCompletelyBounded (f : A → (H →L[ℂ] H)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ CompleteBound f C

end CompletelyBounded

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_RectangularDerivations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangular derivations and the row/column estimate -/

noncomputable section
namespace KadisonSimilarity

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable [CompleteSpace F] [CompleteSpace K]

open scoped CStarAlgebra

section RowColumn

variable [PartialOrder A] [StarOrderedRing A]

/-- Uniform row-amplification bound with the rectangular C-star matrix norm. -/
def RowBound (f : A → (K →L[ℂ] F)) (C : ℝ) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (Fin 1) (Fin n) A,
    ‖rectangularMatrixOperator (X.map f)‖ ≤ C * ‖CStarMatrix.ofMatrix X‖

/-- Uniform column-amplification bound with the rectangular C-star matrix norm. -/
def ColumnBound (f : A → (K →L[ℂ] F)) (C : ℝ) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (Fin n) (Fin 1) A,
    ‖rectangularMatrixOperator (X.map f)‖ ≤ C * ‖CStarMatrix.ofMatrix X‖

/-- The norm-two specialization of Dickson (2014), Lemma 2.9, Eq. (19),
including its column form obtained by taking adjoints. -/
def DicksonTwoBound (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ π : BoundedUnitalHom A H, (∀ a, ‖π.1 a‖ ≤ 2 * ‖a‖) →
    RowBound π.1 (4 * Real.sqrt 2) ∧ ColumnBound π.1 (4 * Real.sqrt 2)

end RowColumn

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicDerivations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The cyclic-domain completely bounded estimate

Approximate cyclic column factorization and the column Leibniz identity
bound every finite matrix amplification of a derivation.
-/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology CStarAlgebra

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [PartialOrder A] [StarOrderedRing A]

/-- Application of an operator-valued column to a single vector. -/
def columnAction {n : ℕ} (f : A → (K →L[ℂ] F))
    (W : Matrix (Fin n) (Fin 1) A) (ζ : K) : HilbertCopies F n :=
  rectangularMatrixOperator (W.map f) (PiLp.single 2 0 ζ)

omit [CStarAlgebra A] [CompleteSpace F] [CompleteSpace K] [PartialOrder A]
  [StarOrderedRing A] in
@[simp] theorem columnAction_apply {n : ℕ} (f : A → (K →L[ℂ] F))
    (W : Matrix (Fin n) (Fin 1) A) (ζ : K) (i : Fin n) :
    columnAction f W ζ i = f (W i 0) ζ := by
  simp [columnAction]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompletelyBoundedImplementation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Implementation of completely bounded rectangular derivations -/

noncomputable section
namespace KadisonSimilarity

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [PartialOrder A] [StarOrderedRing A]

/-- A uniform square-matrix bound for an operator-valued map between two spaces. -/
def RectangularCompleteBound (δ : A → (K →L[ℂ] F)) (D : ℝ) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (Fin n) (Fin n) A,
    ‖rectangularMatrixOperator (X.map δ)‖ ≤ D * ‖CStarMatrix.ofMatrix X‖

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FullColumnTheorem
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The full-column implementation argument

The corner commutator is constructed here, corrected by the proved cyclic
implementation theorem, and extended through finite matrix coordinates with
exactly the same norm. Extension by zero and the tracial commutation theorem
then identify the resulting intertwiner as a right multiplier.

The finite-factor realization of the corner and its matrix coordinates remains
explicit geometric data; the full-column conclusion is not an input.
-/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

section ScalarMatrixUnits

variable {F K : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Commutation with the scalar matrix units forces one repeated diagonal
corner. Only the row of matrix units with target coordinate `i` is needed. -/
theorem eq_mapCopies_of_matrixUnit_intertwining {n : ℕ} (i : Fin n)
    (W : HilbertCopies K n →L[ℂ] HilbertCopies F n)
    (hW : ∀ j : Fin n, W.comp (copyMatrixUnit i j) = (copyMatrixUnit i j).comp W) :
    W = mapCopies (copyCorner i W) n := by
  ext x j
  have h := congrArg (fun T : HilbertCopies K n →L[ℂ] HilbertCopies F n => T x i) (hW j)
  simpa only [ContinuousLinearMap.comp_apply, copyMatrixUnit_apply,
    PiLp.single_eq_same, mapCopies_apply, copyCorner_apply] using h.symm

end ScalarMatrixUnits

section MatrixCoordinates

variable {P C H D F K : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace FullColumnCoordinates

variable {L : P →⋆ₐ[ℂ] (H →L[ℂ] H)} {Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D)}
  {ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)} {σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)} {n : ℕ}

@[simp] theorem extend_sub (c : FullColumnCoordinates L Lr ρ σ n)
    (S T : K →L[ℂ] F) : c.extend (S - T) = c.extend S - c.extend T := by
  ext x
  apply c.codomain.injective
  simp only [map_sub, extend_apply, mapCopies_sub, sub_apply]

end FullColumnCoordinates
end MatrixCoordinates

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every unital star representation is the orthogonal sum of cyclic reducing
representations. The family is constructed by Zorn's lemma. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem self_mem_orbitClosure (N : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    ξ ∈ orbitClosure N ξ := by
  apply (LinearMap.range (orbitLinearMap N ξ)).le_topologicalClosure
  exact ⟨1, by simp⟩

/-- Pairwise orthogonality of the full closed cyclic spaces. -/
def CyclicOrbitOrthogonal (N : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H) : Prop :=
  ∀ x ∈ orbitClosure N ξ, ∀ y ∈ orbitClosure N η, inner ℂ x y = 0

def OrthogonalCyclicFamily (N : StarSubalgebra ℂ (H →L[ℂ] H)) (S : Set H) : Prop :=
  (∀ ξ ∈ S, ξ ≠ 0) ∧ S.Pairwise (CyclicOrbitOrthogonal N)

def cyclicFamilySpan (N : StarSubalgebra ℂ (H →L[ℂ] H)) (S : Set H) : Submodule ℂ H :=
  Submodule.span ℂ (⋃ ξ ∈ S, (orbitClosure N ξ : Set H))

/-- A chosen maximal family, together with its proved density. -/
structure CyclicDecompositionData (N : StarSubalgebra ℂ (H →L[ℂ] H)) where
  generators : Set H
  nonzero : ∀ ξ ∈ generators, ξ ≠ 0
  orthogonal : generators.Pairwise (CyclicOrbitOrthogonal N)
  dense_span : (cyclicFamilySpan N generators).topologicalClosure = ⊤

namespace CyclicDecompositionData

variable {N : StarSubalgebra ℂ (H →L[ℂ] H)} (D : CyclicDecompositionData N)

abbrev Space (i : D.generators) : Type _ := ↥(orbitClosure N (i : H))

/-- The closed cyclic spaces, as an actual complete orthogonal family. -/
def summands : OrthogonalSummandDecomposition D.Space H where
  inclusion i := (orbitClosure N (i : H)).toSubmodule.subtypeₗᵢ
  orthogonal i j hij x y := by
    exact D.orthogonal i.property j.property (fun h => hij (Subtype.ext h))
      x x.property y y.property
  dense_span := by
    have hset : (⋃ i : D.generators,
        Set.range (orbitClosure N (i : H)).toSubmodule.subtypeₗᵢ) =
        ⋃ ξ ∈ D.generators, (orbitClosure N ξ : Set H) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_range, SetCoe.exists]
      constructor
      · rintro ⟨ξ, hξ, y, rfl⟩
        exact ⟨ξ, hξ, y.property⟩
      · rintro ⟨ξ, hξ, hx⟩
        exact ⟨ξ, hξ, ⟨x, hx⟩, rfl⟩
    change (Submodule.span ℂ _).topologicalClosure = ⊤
    rw [hset]
    exact D.dense_span

end CyclicDecompositionData

variable {A : Type*} [CStarAlgebra A]

def orbitGenerator (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : orbitClosure σ.range ξ :=
  ⟨ξ, self_mem_orbitClosure σ.range ξ⟩

namespace CyclicDecompositionData

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData σ.range)

/-- The star representation on each member of the Zorn family. -/
def representation (i : D.generators) : A →⋆ₐ[ℂ] (D.Space i →L[ℂ] D.Space i) :=
  orbitRepresentation σ (i : H)

def generator (i : D.generators) : D.Space i := orbitGenerator σ (i : H)

end CyclicDecompositionData

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CountableCyclicDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An orthogonal cyclic decomposition is countable on a separable Hilbert
space, as required for the normal standard-representation reduction. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  {N : StarSubalgebra ℂ (H →L[ℂ] H)}

namespace CyclicDecompositionData

/-- Normalized nonzero cyclic generators have disjoint open half-balls,
so separability makes the family countable. -/
theorem generators_countable (D : CyclicDecompositionData N) : Countable D.generators := by
  let v : D.generators → H := fun i => (‖(i : H)‖⁻¹ : ℂ) • (i : H)
  have hn (i : D.generators) : ‖v i‖ = 1 := by
    have hi := norm_ne_zero_iff.mpr (D.nonzero i i.property)
    simp only [v, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hi]
  have ho (i j : D.generators) (hij : i ≠ j) : inner ℂ (v i) (v j) = 0 := by
    have h := D.orthogonal i.property j.property (fun he => hij (Subtype.ext he))
      i (self_mem_orbitClosure N i) j (self_mem_orbitClosure N j)
    simp only [v, inner_smul_left, inner_smul_right, h, mul_zero]
  have hd (i j : D.generators) (hij : i ≠ j) : 1 ≤ dist (v i) (v j) := by
    have h := norm_sub_sq (𝕜 := ℂ) (v i) (v j)
    rw [hn i, hn j, ho i j hij] at h
    norm_num at h
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j)]
  exact Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (v i) (1 / 2))
    (fun i j hij => Metric.ball_disjoint_ball (by linarith [hd i j hij]))
    (fun _ => Metric.isOpen_ball) (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

end CyclicDecompositionData
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_OrthogonalColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite orthogonal word levels and their full-codomain errors. -/

noncomputable section
namespace KadisonSimilarity

open Finset ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable [CompleteSpace H] [CompleteSpace K]


/-- The block entries of the compressed operator are its coordinatewise
compressions along the word-level inclusions. -/
theorem sumColumns_compression {N : ℕ} (U : Fin N → H →L[ℂ] K) (T : K →L[ℂ] K) :
    (sumColumns U).adjoint.comp (T.comp (sumColumns U)) =
      matrixOperator (fun i j => (U i).adjoint.comp (T.comp (U j))) := by
  ext x i
  simp [sumColumns_apply, matrixOperator, map_sum]

/-- Adjoint and finite Hilbert amplification commute. -/
theorem adjoint_amplify (B : H →L[ℂ] H) (N : ℕ) :
    (amplify B N).adjoint = amplify B.adjoint N := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [adjoint_inner_right, PiLp.inner_apply, amplify_apply]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantCycles
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing centered singleton cycles

A fixed point contributes the trace of its matrix argument. Factorization
of the coordinate contraction shows that vanishing on
centered singleton tails does not require an additional invariant-theory input.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

noncomputable instance cycleMembersFintype (π : Equiv.Perm ι) (q : PermutationCycles π) :
    Fintype (CycleMembers π q) := Fintype.ofFinite _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixTracialGNS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized matrix traces and their actual GNS Hilbert spaces. The GNS
space of `M_n(A)` is identified with the square array of copies of the GNS
space of `A`; its algebra vectors have entries `n^(-1/2) V(a_ij)`. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

theorem normalizedMatrixTrace_one (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) :
    normalizedMatrixTrace τ n 1 = 1 := by
  simp [normalizedMatrixTrace_apply, h1, NeZero.ne n]

theorem normalizedMatrixTrace_tracial (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a))
    (X Y : CStarMatrix (Fin n) (Fin n) A) :
    normalizedMatrixTrace τ n (X * Y) = normalizedMatrixTrace τ n (Y * X) := by
  simp only [normalizedMatrixTrace_apply, CStarMatrix.mul_apply, map_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact htr _ _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicSpectralSum
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal cyclic decomposition of a commutative representation,
expressed as an actual Hilbert sum of scalar spectral L² spaces. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : Type*} [CommCStarAlgebra A]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable (D : CyclicDecompositionData π.range)

local instance spectralSumMeasurable_r81c299_1 : MeasurableSpace (WeakDual.characterSpace ℂ A) :=
  borel (WeakDual.characterSpace ℂ A)
local instance spectralSumBorel_r81c299_1 : BorelSpace (WeakDual.characterSpace ℂ A) := ⟨rfl⟩
abbrev CyclicSpectralSpace (i : D.generators) : Type _ :=
  Lp ℂ 2 (commutativeVectorMeasure π (i : H))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CommonCyclicEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embed the original separable Hilbert space into a single L² space by
placing its cyclic spectral coordinates over one finite dominating measure. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

local instance commonCyclicCountable : Countable D.generators := D.generators_countable

attribute [local instance] OAI.KadisonSimilarity.commonCyclicMeasurable
attribute [local instance] OAI.KadisonSimilarity.commonCyclicBorel
def cyclicCommonBaseMeasure : Measure (WeakDual.characterSpace ℂ A) :=
  commonSpectralMeasure (fun i : D.generators => commutativeVectorMeasure π (i : H))

abbrev CommonCyclicHilbert : Type _ :=
  Lp (ScalarHilbertCoordinates D.generators) 2 (cyclicCommonBaseMeasure π D)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProperlyInfiniteEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The properly infinite commutator estimate. Internal orthogonal isometries
supply the row, and Dickson supplies its actual commutator error bounds. -/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vonNeumannInnerDerivation (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    P →L[ℂ] (H →L[ℂ] H) :=
  cornerCommutator (vonNeumannRepresentation P) (vonNeumannRepresentation P) Y

@[simp] theorem vonNeumannInnerDerivation_apply (P : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) (a : P) : vonNeumannInnerDerivation P Y a = commutator Y (a : H →L[ℂ] H) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicColumnTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense cyclic orbits give the bounded column tests needed for the
matrix derivation estimate. The unit vector may vary with the test. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped ComplexOrder Topology

variable {A K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The approximation needed by the matrix estimate; the input vector may vary. -/
def CyclicColumnTests (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ n : ℕ, ∀ ξ : HilbertCopies K n, ‖ξ‖ = 1 → ∀ η : ℝ, 0 < η →
    ∃ ζ : K, ∃ W : Matrix (Fin n) (Fin 1) A,
      ‖ζ‖ = 1 ∧ ‖CStarMatrix.ofMatrix W‖ ≤ 2 ∧ ‖columnAction σ W ζ - ξ‖ < η

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_EvenAlternatingWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Under a tracial functional, vanishing of nonempty even alternating
centered words implies scalar freeness. The odd-word step rotates the last
letter next to the first, centers their product, and shortens the word. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R}

/-- The tracial cyclic reduction needed in the dihedral-corner argument.
The only trace identities used are linearity, normalization, and cyclicity. -/
theorem scalarFree_of_even_alternating
    (hτ : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (heven : ∀ side x xs, AlternatingCenteredWord τ P Q side (x :: xs) →
      (x :: xs).length % 2 = 0 → τ ((x :: xs).prod) = 0) :
    ScalarFree τ P Q := by
  have hall : ∀ w : List R, ∀ side, w ≠ [] →
      AlternatingCenteredWord τ P Q side w → τ w.prod = 0 := by
    intro w
    induction w using List.bidirectionalRec with
    | nil => intro _ hne; exact (hne rfl).elim
    | singleton a =>
      intro side _ hw
      cases hw with
      | cons _ hz _ => simpa using hz
    | cons_append a xs b ih =>
      intro side _ hw
      by_cases hp : (a :: (xs ++ [b])).length % 2 = 0
      · exact heven side a (xs ++ [b]) hw hp
      have hlength : (a :: xs).length % 2 = 0 := by
        simp only [List.length_cons, List.length_append, List.length_nil] at hp ⊢
        omega
      have hb : b ∈ (if side then P else Q) :=
        AlternatingCenteredWord.last_mem_of_even_prefix (a :: xs) b hw hlength
      cases hw with
      | cons ha _ ht =>
        have hmid : AlternatingCenteredWord τ P Q (!side) xs := ht.take_prefix
        have hne : xs ≠ [] := by
          intro hx
          subst xs
          simp at hp
        have hshort : τ xs.prod = 0 := ih (!side) hne hmid
        have hc : traceCentered τ (b * a) ∈ (if side then P else Q) :=
          traceCentered_mem τ _ ((if side then P else Q).mul_mem hb ha)
        have hcenter : τ (traceCentered τ (b * a) * xs.prod) = 0 := by
          have hword : AlternatingCenteredWord τ P Q side
              (traceCentered τ (b * a) :: xs) :=
            .cons hc (traceCentered_trace τ hτ _) hmid
          simpa only [List.prod_cons] using heven side _ xs hword hlength
        calc
          τ ((a :: (xs ++ [b])).prod) = τ ((a * xs.prod) * b) := by
            simp only [List.prod_cons, List.prod_append, List.prod_nil, mul_one, mul_assoc]
          _ = τ (b * (a * xs.prod)) := htr _ _
          _ = τ ((b * a) * xs.prod) := by rw [mul_assoc]
          _ = τ ((traceCentered τ (b * a) + τ (b * a) • 1) * xs.prod) := by
            rw [traceCentered_add]
          _ = 0 := by
            rw [add_mul, smul_mul_assoc, one_mul, map_add, map_smul,
              hcenter, hshort]
            simp
  intro side x xs hw
  exact hall (x :: xs) side (List.cons_ne_nil _ _) hw

/-- It suffices to test even cyclic words beginning in the first algebra;
tracial rotation supplies the opposite starting side. -/
theorem scalarFree_of_even_cyclic
    (hτ : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (heven : ∀ x xs, AlternatingCenteredWord τ P Q true (x :: xs) →
      (x :: xs).length % 2 = 0 → τ ((x :: xs).prod) = 0) :
    ScalarFree τ P Q := by
  apply scalarFree_of_even_alternating hτ htr
  intro side x xs hw hp
  cases side with
  | true => exact heven x xs hw hp
  | false =>
    cases hw with
    | cons hx hx0 ht =>
      have hodd : xs.length % 2 = 1 := by
        simp only [List.length_cons] at hp
        omega
      have hrot : AlternatingCenteredWord τ P Q true (xs ++ [x]) :=
        ht.append_of_odd_length xs x hodd hx hx0
      have hne : xs ≠ [] := by
        intro h
        simp [h] at hodd
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hv : τ ((y :: (ys ++ [x])).prod) = 0 := by
        apply heven y (ys ++ [x]) hrot
        simp only [List.length_cons, List.length_append, List.length_nil] at hp ⊢
        omega
      calc
        τ ((x :: y :: ys).prod) = τ ((y :: ys).prod * x) := by
          simp only [List.prod_cons]
          exact htr _ _
        _ = 0 := by
          simpa only [List.prod_cons, List.prod_append, List.prod_nil, mul_one,
            mul_assoc] using hv

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HankelCommutator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A finite Hankel matrix detects the base commutator

The constant-coordinate compression gives the tensor-product norm lower bound
needed by the paper without introducing any infinite matrix norm assumption.
-/

noncomputable section
namespace KadisonSimilarity

open Finset ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The unnormalized constant-coordinate inclusion. -/
def constantCopies (N : ℕ) : H →L[ℂ] HilbertCopies H N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℂ H))

omit [CompleteSpace H] in
@[simp] theorem constantCopies_apply (N : ℕ) (x : H) (i : Fin N) :
    constantCopies N x i = x := by simp [constantCopies]

@[simp] theorem constantCopies_adjoint_apply (N : ℕ) (x : HilbertCopies H N) :
    (constantCopies N).adjoint x = ∑ i : Fin N, x i := by
  apply ext_inner_left ℂ
  intro y
  simp only [adjoint_inner_right, PiLp.inner_apply, constantCopies_apply, inner_sum]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ScalarFreeMonotone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting either algebra preserves scalar freeness. -/

namespace KadisonSimilarity
variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  {τ : A →ₗ[ℂ] ℂ} {P Q P' Q' : StarSubalgebra ℂ A}

theorem ScalarFree.mono (hf : ScalarFree τ P' Q') (hP : P ≤ P') (hQ : Q ≤ Q') :
    ScalarFree τ P Q := by
  intro side x xs h
  exact hf side x xs (h.mono hP hQ)

end KadisonSimilarity

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SpectralArc
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded Borel spectral calculus input, specialized to the centered
arc of a Haar rotation in a finite dihedral von Neumann algebra. Blackadar,
Operator Algebras, I.6.2.4 and I.6.2.8, supply the calculus and commutation;
integration against its Haar spectral measure gives the stated moments.

The interface is local to the specified trace and algebra. Its intended
application has the normal finite trace and the von Neumann algebra generated
by the two symmetries. No existence assertion is made for an arbitrary C-star
subalgebra or an arbitrary linear functional. The corner estimates below are
proved from the spectral data, rather than included in the published input. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- The local bounded Borel functional calculus specialization. In its
application `C` is the dihedral von Neumann algebra and `τ` its normal trace. -/
def DihedralSpectralArcInput (τ : P →ₗ[ℂ] ℂ) (C : StarSubalgebra ℂ P)
    (w d : Pˣ) : Prop :=
  ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi → Nonempty (DihedralSpectralArc τ C w d θ)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConcretePredual
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Banach predual of a concrete von Neumann algebra, constructed as the
closed span of its vector functionals. The double commutant property makes
every bounded functional on this space evaluation at an algebra element. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

/-- A vector functional restricted to the concrete algebra. -/
def normalCoefficient (x y : H) : StrongDual ℂ M.toStarSubalgebra :=
  LinearMap.mkContinuous
    { toFun := fun a => inner ℂ y ((a : H →L[ℂ] H) x)
      map_add' := by intros; simp [inner_add_right]
      map_smul' := by intros; simp [inner_smul_right] }
    (‖x‖ * ‖y‖) (fun a => by
      calc
        ‖inner ℂ y ((a : H →L[ℂ] H) x)‖ ≤ ‖y‖ * ‖(a : H →L[ℂ] H) x‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖y‖ * (‖a‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left ((a : H →L[ℂ] H).le_opNorm x) (norm_nonneg y)
        _ = (‖x‖ * ‖y‖) * ‖a‖ := by ring)

@[simp] theorem normalCoefficient_apply (x y : H) (a : M.toStarSubalgebra) :
    normalCoefficient M x y a = inner ℂ y ((a : H →L[ℂ] H) x) := rfl

theorem normalCoefficient_norm_le (x y : H) :
    ‖normalCoefficient M x y‖ ≤ ‖x‖ * ‖y‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

/-- Normal functionals, with their operator-dual norm. -/
def normalFunctionalSpace : ClosedSubmodule ℂ (StrongDual ℂ M.toStarSubalgebra) :=
  (Submodule.span ℂ (Set.range fun xy : H × H => normalCoefficient M xy.1 xy.2)).closure

def ConcretePredual : Type _ := normalFunctionalSpace M

instance instNormedAddCommGroupConcretePredual : NormedAddCommGroup (ConcretePredual M) :=
  inferInstanceAs (NormedAddCommGroup (normalFunctionalSpace M))

instance instNormedSpaceComplexConcretePredual : NormedSpace ℂ (ConcretePredual M) :=
  inferInstanceAs (NormedSpace ℂ (normalFunctionalSpace M))

instance instCompleteSpaceConcretePredual : CompleteSpace (ConcretePredual M) :=
  inferInstanceAs (CompleteSpace (normalFunctionalSpace M))

instance instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra : CoeOut (ConcretePredual M) (StrongDual ℂ M.toStarSubalgebra) := ⟨Subtype.val⟩

def predualCoefficient (x y : H) : ConcretePredual M :=
  ⟨normalCoefficient M x y, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self (x, y)))⟩

@[simp] theorem predualCoefficient_apply (x y : H) (a : M.toStarSubalgebra) :
    (predualCoefficient M x y : StrongDual ℂ M.toStarSubalgebra) a =
      inner ℂ y ((a : H →L[ℂ] H) x) := rfl

theorem predualCoefficient_add_left (x y z : H) :
    predualCoefficient M (x + y) z = predualCoefficient M x z + predualCoefficient M y z := by
  apply Subtype.ext
  ext a
  change inner ℂ z ((a : H →L[ℂ] H) (x + y)) =
    inner ℂ z ((a : H →L[ℂ] H) x) + inner ℂ z ((a : H →L[ℂ] H) y)
  simp [inner_add_right]

theorem predualCoefficient_smul_left (c : ℂ) (x y : H) :
    predualCoefficient M (c • x) y = c • predualCoefficient M x y := by
  apply Subtype.ext
  ext a
  change inner ℂ y ((a : H →L[ℂ] H) (c • x)) =
    c * inner ℂ y ((a : H →L[ℂ] H) x)
  simp [inner_smul_right]

theorem predualCoefficient_add_right (x y z : H) :
    predualCoefficient M x (y + z) = predualCoefficient M x y + predualCoefficient M x z := by
  apply Subtype.ext
  ext a
  change inner ℂ (y + z) ((a : H →L[ℂ] H) x) =
    inner ℂ y ((a : H →L[ℂ] H) x) + inner ℂ z ((a : H →L[ℂ] H) x)
  simp [inner_add_left]

theorem predualCoefficient_smul_right (c : ℂ) (x y : H) :
    predualCoefficient M x (c • y) = star c • predualCoefficient M x y := by
  apply Subtype.ext
  ext a
  change inner ℂ (c • y) ((a : H →L[ℂ] H) x) =
    star c * inner ℂ y ((a : H →L[ℂ] H) x)
  simp [inner_smul_left, mul_comm]

theorem predualCoefficient_norm_le (x y : H) :
    ‖predualCoefficient M x y‖ ≤ ‖x‖ * ‖y‖ := normalCoefficient_norm_le M x y

def predualForm (F : StrongDual ℂ (ConcretePredual M)) (x y : H) : ℂ :=
  star (F (predualCoefficient M x y))

theorem predualForm_isOperatorForm (F : StrongDual ℂ (ConcretePredual M)) :
    IsOperatorForm (predualForm M F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y z
    simp [predualForm, predualCoefficient_add_left]
  · intro c x y
    simp [predualForm, predualCoefficient_smul_left]
  · intro x y z
    simp [predualForm, predualCoefficient_add_right]
  · intro c x y
    simp [predualForm, predualCoefficient_smul_right]

theorem predualForm_bound (F : StrongDual ℂ (ConcretePredual M)) (x y : H) :
    ‖predualForm M F x y‖ ≤ ‖F‖ * ‖x‖ * ‖y‖ := by
  rw [predualForm, norm_star]
  exact (F.le_opNorm _).trans (by
    calc
      ‖F‖ * ‖predualCoefficient M x y‖ ≤ ‖F‖ * (‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (predualCoefficient_norm_le M x y) (norm_nonneg F)
      _ = _ := by ring)

/-- Riesz reconstruction from a bounded functional on the vector predual. -/
def operatorOfPredual (F : StrongDual ℂ (ConcretePredual M)) : H →L[ℂ] H :=
  operatorOfForm (predualForm M F) (predualForm_isOperatorForm M F) ‖F‖
    (predualForm_bound M F)

@[simp] theorem operatorOfPredual_coefficient (F : StrongDual ℂ (ConcretePredual M))
    (x y : H) : inner ℂ y (operatorOfPredual M F x) = F (predualCoefficient M x y) := by
  rw [← inner_conj_symm, operatorOfPredual, operatorOfForm_inner]
  exact star_star _

/-- Commutant elements give identical vector functionals on the algebra. -/
theorem predualCoefficient_commutant (S : H →L[ℂ] H) (hS : S ∈ M.commutant)
    (x y : H) : predualCoefficient M (S x) y = predualCoefficient M x (S.adjoint y) := by
  apply Subtype.ext
  ext a
  change inner ℂ y ((a : H →L[ℂ] H) (S x)) =
    inner ℂ (S.adjoint y) ((a : H →L[ℂ] H) x)
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hS) a a.property
  exact congrArg (fun T : H →L[ℂ] H => inner ℂ y (T x)) hc

/-- Riesz reconstruction belongs to the original double commutant. -/
theorem operatorOfPredual_mem (F : StrongDual ℂ (ConcretePredual M)) :
    operatorOfPredual M F ∈ M := by
  apply (show M.commutant.commutant ≤ M from le_of_eq M.commutant_commutant)
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro S hS
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (S (operatorOfPredual M F x)) =
    inner ℂ y (operatorOfPredual M F (S x))
  rw [← ContinuousLinearMap.adjoint_inner_left, operatorOfPredual_coefficient,
    operatorOfPredual_coefficient, predualCoefficient_commutant M S hS]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConcretePredualDuality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric duality between the concrete vector predual and the original
von Neumann algebra. The conjugate-linear convention agrees with the
predual interface used by the finite normal trace construction. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

def predualEvaluation (a : M.toStarSubalgebra) : StrongDual ℂ (ConcretePredual M) :=
  LinearMap.mkContinuous
    { toFun := fun φ => (φ : StrongDual ℂ M.toStarSubalgebra) a
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    ‖a‖ (fun φ => by
      exact (φ : StrongDual ℂ M.toStarSubalgebra).le_opNorm a |>.trans_eq (mul_comm _ _))

@[simp] theorem predualEvaluation_apply (a : M.toStarSubalgebra) (φ : ConcretePredual M) :
    predualEvaluation M a φ = (φ : StrongDual ℂ M.toStarSubalgebra) a := rfl

theorem predualEvaluation_norm (a : M.toStarSubalgebra) :
    ‖predualEvaluation M a‖ = ‖a‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  · change ‖(a : H →L[ℂ] H)‖ ≤ ‖predualEvaluation M a‖
    apply norm_le_of_matrix_coefficients _ (norm_nonneg _)
    intro x y
    calc
      ‖inner ℂ y ((a : H →L[ℂ] H) x)‖ =
          ‖predualEvaluation M a (predualCoefficient M x y)‖ := rfl
      _ ≤ ‖predualEvaluation M a‖ * ‖predualCoefficient M x y‖ :=
        (predualEvaluation M a).le_opNorm _
      _ ≤ ‖predualEvaluation M a‖ * (‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (predualCoefficient_norm_le M x y) (norm_nonneg _)
      _ = _ := by ring

/-- Vector coefficients determine every continuous functional on the predual. -/
theorem predual_ext (F G : StrongDual ℂ (ConcretePredual M))
    (h : ∀ x y, F (predualCoefficient M x y) = G (predualCoefficient M x y)) : F = G := by
  obtain ⟨f, hf, _⟩ := exists_extension_norm_eq (normalFunctionalSpace M).toSubmodule F
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq (normalFunctionalSpace M).toSubmodule G
  have hspan : Submodule.span ℂ (Set.range fun xy : H × H => normalCoefficient M xy.1 xy.2) ≤
      (f - g).ker := by
    apply Submodule.span_le.mpr
    rintro φ ⟨⟨x, y⟩, rfl⟩
    change f (normalCoefficient M x y) - g (normalCoefficient M x y) = 0
    exact sub_eq_zero.mpr ((hf (predualCoefficient M x y)).trans
      ((h x y).trans (hg (predualCoefficient M x y)).symm))
  have hc := closure_minimal hspan (f - g).isClosed_ker
  apply ContinuousLinearMap.ext
  intro φ
  have hz := hc φ.property
  change f (φ : StrongDual ℂ M.toStarSubalgebra) -
    g (φ : StrongDual ℂ M.toStarSubalgebra) = 0 at hz
  exact (hf φ).symm.trans ((sub_eq_zero.mp hz).trans (hg φ))

theorem predualEvaluation_surjective : Function.Surjective (predualEvaluation M) := by
  intro F
  refine ⟨⟨operatorOfPredual M F, operatorOfPredual_mem M F⟩, ?_⟩
  apply predual_ext M
  intro x y
  exact operatorOfPredual_coefficient M F x y

def predualEvaluationIsometry : M.toStarSubalgebra →ₗᵢ[ℂ] StrongDual ℂ (ConcretePredual M) where
  toFun := predualEvaluation M
  map_add' := by
    intro a b
    ext φ
    exact (φ : StrongDual ℂ M.toStarSubalgebra).map_add a b
  map_smul' := by
    intro c a
    ext φ
    exact (φ : StrongDual ℂ M.toStarSubalgebra).map_smul c a
  norm_map' := predualEvaluation_norm M

def concretePredualLinearEquiv : StrongDual ℂ (ConcretePredual M) ≃ₗᵢ[ℂ] M.toStarSubalgebra :=
  (LinearIsometryEquiv.ofSurjective (predualEvaluationIsometry M)
    (predualEvaluation_surjective M)).symm

/-- The given concrete algebra is the conjugate dual of an actual Banach space. -/
def concretePredualEquiv : StrongDual ℂ (ConcretePredual M) ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra :=
  (concretePredualLinearEquiv M).trans (starₗᵢ ℂ)

@[simp] theorem concretePredualEquiv_symm_apply (a : M.toStarSubalgebra)
    (φ : ConcretePredual M) :
    (concretePredualEquiv M).symm a φ = (φ : StrongDual ℂ M.toStarSubalgebra) (star a) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixUnitCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedMatrixHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hilbert coordinates from a finite orthogonal family of corner inclusions

The two matrix-unit equations construct the coordinate unitaries used in the
full-column theorem. The action of an arbitrary operator is then its actual
matrix of corner compressions.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMap

variable {F H : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FiniteOrthogonalColumns

variable {n : ℕ} (U : FiniteOrthogonalColumns F H n)

/-- Orthogonality makes assembly an isometry. -/
theorem adjoint_assembly_comp_assembly :
    (sumColumns U.inclusion).adjoint.comp (sumColumns U.inclusion) =
      ContinuousLinearMap.id ℂ (HilbertCopies F n) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  change ((sumColumns U.inclusion).adjoint (sumColumns U.inclusion x)) i = x i
  rw [sumColumns_adjoint_apply, sumColumns_apply, map_sum]
  simp only [U.adjoint_inclusion_apply]
  simp

/-- Completeness of the family makes assembly onto the full Hilbert space. -/
theorem assembly_comp_adjoint_assembly :
    (sumColumns U.inclusion).comp (sumColumns U.inclusion).adjoint =
      ContinuousLinearMap.id ℂ H := by
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => T x) U.resolution
  simpa only [comp_apply, sum_apply, id_apply, sumColumns_apply,
    sumColumns_adjoint_apply] using h

/-- The coordinate unitary is constructed from the finite matrix-unit columns. -/
def unitary : HilbertCopies F n ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofLinearIsometry
    { toLinearMap := (sumColumns U.inclusion).toLinearMap
      norm_map' := (norm_map_iff_adjoint_comp_self _).mpr U.adjoint_assembly_comp_assembly }
    (sumColumns U.inclusion).adjoint.toLinearMap
    (congrArg ContinuousLinearMap.toLinearMap U.assembly_comp_adjoint_assembly)
    (congrArg ContinuousLinearMap.toLinearMap U.adjoint_assembly_comp_assembly)

@[simp] theorem unitary_apply (x : HilbertCopies F n) :
    U.unitary x = sumColumns U.inclusion x := rfl

@[simp] theorem unitary_symm_apply (x : H) :
    U.unitary.symm x = (sumColumns U.inclusion).adjoint x := rfl

@[simp] theorem unitary_single (i : Fin n) (x : F) :
    U.unitary (PiLp.single 2 i x) = U.inclusion i x := by
  simp only [unitary_apply, sumColumns_apply, PiLp.single_apply, apply_ite, map_zero]
  simp

/-- Arbitrary operators act in the constructed coordinates by their corner
compression matrix. -/
theorem coordinates_operator (T : H →L[ℂ] H) (x : H) :
    U.unitary.symm (T x) =
      matrixOperator (fun i j => (U.inclusion i).adjoint.comp (T.comp (U.inclusion j)))
        (U.unitary.symm x) := by
  rw [← sumColumns_compression]
  change (sumColumns U.inclusion).adjoint (T x) =
    (sumColumns U.inclusion).adjoint (T (U.unitary (U.unitary.symm x)))
  rw [U.unitary.apply_symm_apply]

end FiniteOrthogonalColumns

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteHalfProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small projection in an actual diffuse tracial von Neumann algebra
can be completed to trace one half.  The only projection-existence step
is the proved exact-trace subprojection theorem. -/

noncomputable section
namespace KadisonSimilarity

open UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

local instance instIsClosedContinuousLinearMapComplexIdCoeStarSubalgebra_solutions : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  Generator.Tracial.base_norm_closed M

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConcretePredualRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normality of a trace restricts to a concrete von Neumann subalgebra.
Restriction sends each vector functional to the same vector functional,
and therefore preserves their closed span. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder
open BoundedHochschild

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (hNM : N ≤ M)

@[simp] theorem normalRestriction_coefficient (x y : H) :
    normalRestriction hNM (normalCoefficient M x y) = normalCoefficient N x y := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DenseFamilyIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a map on a total family from its Gram matrix. This construction
allows the family to have linear relations. -/

noncomputable section
namespace KadisonSimilarity

variable {J E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The unique isometry sending a total family to a family with the same
Gram matrix, constructed through finitely supported linear combinations. -/
def denseFamilyIsometry (v : J → E) (w : J → F)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (h : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j)) : E →ₗᵢ[ℂ] F :=
  (Finsupp.linearCombination ℂ w).extendOfIsometry
    (denseRange_linearCombination v hv) (norm_linearCombination_eq v w h)

@[simp] theorem denseFamilyIsometry_apply (v : J → E) (w : J → F)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (h : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j)) (i : J) :
    denseFamilyIsometry v w hv h (v i) = w i := by
  have he := LinearMap.extendOfIsometry_eq (Finsupp.linearCombination ℂ w)
    (denseRange_linearCombination v hv) (norm_linearCombination_eq v w h)
    (Finsupp.single i 1)
  simpa only [denseFamilyIsometry, Finsupp.linearCombination_single, one_smul] using he

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DyadicCornerHom
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite dyadic spectral sums form contractive unital star
homomorphisms into the original corner. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped BigOperators CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}
  (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

local instance dyadicAlgebra_closed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  Generator.Tracial.base_norm_closed M

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner unitaries and completed half projections are transported along
the actual trace-preserving factor embedding. This retains their concrete
support projections inside the conjugated free copy. -/

noncomputable section
namespace KadisonSimilarity

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B)

def transportedCornerUnitary {e : A} {he : IsStarProjection e}
    (z : unitary (CStarCorner e he)) : unitary (CStarCorner (φ e) (he.map φ)) :=
  Unitary.map (StarMonoidHom.ofClass (cornerStarAlgHom φ e he)) z

theorem haarCornerPower_transport {e : A} {he : IsStarProjection e}
    (z : unitary (CStarCorner e he)) (k : ℤ) :
    haarCornerPower (transportedCornerUnitary φ z) k = φ (haarCornerPower z k) := by
  change ((((Unitary.map (StarMonoidHom.ofClass (cornerStarAlgHom φ e he)) z) ^ k :
    unitary (CStarCorner (φ e) (he.map φ))) : CStarCorner (φ e) (he.map φ)) : B) = _
  rw [← map_zpow]
  rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteProjectionComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact trace-comparison input used in the corner argument follows
from projection comparison in a concrete finite factor. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

local instance comparisonAlgebra_closed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  Generator.Tracial.base_norm_closed M

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProjectionComparisonTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection comparison is transported through the trace-preserving
normal-model coordinates used in the finite-factor application. -/

noncomputable section
namespace KadisonSimilarity

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem finiteFactorProjectionComparison_of_equiv (e : A ≃⋆ₐ[ℂ] B)
    (τA : A → ℝ) (τB : B → ℝ) (hτ : ∀ a, τB (e a) = τA a)
    (comparison : FiniteFactorProjectionComparison τB) :
    FiniteFactorProjectionComparison τA := by
  intro p q hp hq hpq
  obtain ⟨v, hv, hpv⟩ := comparison (e p) (e q) (hp.map e) (hq.map e)
    (by simpa only [hτ] using hpq)
  refine ⟨e.symm v, ?_, ?_⟩
  · have h := congrArg e.symm hv
    simpa only [map_mul, map_star, e.symm_apply_apply] using h
  · have h := congrArg e.symm hpv
    simpa only [map_mul, map_star, e.symm_apply_apply] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialFactorComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection comparison in the finite-matrix source follows from its
actual normal trace and dense full-matrix tower. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra ComplexOrder

namespace TracialCornerGeometry
variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

local instance normalFactor_closed (N : VonNeumannAlgebra H) :
    IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed N

end TracialCornerGeometry

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FactorAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three factor branches

The finite branch records only the fixed trace, matrix presentation, and
local published inputs used in the preceding application. The alternatives
are the structural factor classification; no alternative assumes an
operator estimate. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance instIsClosedContinuousLinearMapComplexIdCoeStarSubalgebra_solutions_2 (P : VonNeumannAlgebra H) :
    IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (P : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SeparableConcretePredual
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A separable concrete Hilbert space gives a separable Banach predual.
Only the norm-continuity of vector coefficients and their defining density
are used. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

def predualCoefficientBilinear : H →L[ℂ] H →L⋆[ℂ] ConcretePredual M :=
  (LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (predualCoefficient M)
    (predualCoefficient_add_left M) (predualCoefficient_smul_left M)
    (predualCoefficient_add_right M) (predualCoefficient_smul_right M)).mkContinuous₂ 1
      (fun x y => by
        change ‖predualCoefficient M x y‖ ≤ 1 * ‖x‖ * ‖y‖
        simpa only [one_mul] using predualCoefficient_norm_le M x y)

theorem predualCoefficient_continuous :
    Continuous (fun p : H × H => predualCoefficient M p.1 p.2) := by
  change Continuous (fun p : H × H => predualCoefficientBilinear M p.1 p.2)
  exact ((predualCoefficientBilinear M).flip.continuous.comp continuous_snd).clm_apply
    continuous_fst

theorem normalCoefficient_continuous :
    Continuous (fun p : H × H => normalCoefficient M p.1 p.2) := by
  exact (normalFunctionalSpace M).toSubmodule.subtypeL.continuous.comp
    (predualCoefficient_continuous M)

/-- The vector predual has a countable norm-dense subset whenever the
represented Hilbert space does. -/
instance concretePredual_separable [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.SeparableSpace (ConcretePredual M) := by
  have hs := TopologicalSpace.isSeparable_range (normalCoefficient_continuous M)
  have hc : TopologicalSpace.IsSeparable (normalFunctionalSpace M : Set
      (StrongDual ℂ M.toStarSubalgebra)) := hs.span.closure
  exact hc.separableSpace

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConjugateMomentCriterion
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer mixed moments imply freeness of a conjugated subalgebra. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching

variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

def conjugateMomentTail : List (B × B) → List (IntAtom B)
  | [] => [(-1, none)]
  | (a, b) :: v => (-1, some a) :: (1, some b) :: conjugateMomentTail v

omit [CStarAlgebra B] in
lemma conjugateMomentTail_admissible (v : List (B × B)) :
    admissibleIntTail (conjugateMomentTail v) := by
  induction v with
  | nil => exact ⟨by simp [conjugateMomentTail], by simp [conjugateMomentTail]⟩
  | cons p v ih => exact intTail_cons (intTail_cons ih 1 p.2) (-1) p.1

omit [CStarAlgebra B] in
lemma conjugateMomentTail_nonzero (v : List (B × B)) :
    ∀ b ∈ conjugateMomentTail v, b.1 ≠ 0 := by
  induction v with
  | nil => simp [conjugateMomentTail]
  | cons p v ih =>
    intro b hb
    simp only [conjugateMomentTail, List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · norm_num
    · norm_num
    · exact ih b hb

variable (σ : C →ₗ[ℂ] ℂ) (h1 : σ 1 = 1)
  (tr : ∀ a b, σ (a * b) = σ (b * a)) (φ : B →⋆ₐ[ℂ] C) (u : unitary C)

include tr in
lemma even_conjugate_blocks (xs : List C)
    (hw : AlternatingCenteredWord σ φ.range
      (((Unitary.conjStarAlgAut ℂ C u).toStarAlgHom).comp φ).range true xs)
    (he : xs.length % 2 = 0) :
    ∃ v : List (B × B), xs.prod =
      (v.map (conjugateMomentBlock (fun b => φ b - σ (φ b) • 1) u)).prod ∧
      xs.length = 2 * v.length := by
  induction xs using List.twoStepInduction with
  | nil => exact ⟨[], rfl, rfl⟩
  | singleton x => simp at he
  | cons_cons x y xs ih _ =>
    cases hw with
    | cons hx hx0 ht =>
      cases ht with
      | cons hy hy0 ht =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        have hb' : (u : C) * φ b * star (u : C) = y := hb
        have hta : σ (φ a) = 0 := ha ▸ hx0
        have htb : σ (φ b) = 0 := by
          rw [← trace_conjugation σ tr u, hb']
          exact hy0
        obtain ⟨v, hv, hn⟩ := ih (by simpa only [Bool.not_not] using ht) (by
          simp only [List.length_cons] at he
          omega)
        refine ⟨(a, b) :: v, ?_, ?_⟩
        · simp only [List.prod_cons, List.map_cons, conjugateMomentBlock, hta, htb,
            zero_smul, sub_zero, ← ha, ← hb', hv, mul_assoc]
          rfl
        · simp only [List.length_cons, hn]
          omega

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_DenseMomentExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension of mixed moments from trace-dense contractions to all contractions. -/

noncomputable section
namespace KadisonSimilarity
open BoundedHochschild HochschildRigidity HochschildPatching HochschildUltrapower Filter Topology
open scoped ComplexOrder

variable {B C I : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (τ : B →ₚ[ℂ] ℂ) (σ : C →ₚ[ℂ] ℂ) (hσ : σ 1 = 1)
  (trσ : ∀ a b, σ (a * b) = σ (b * a))
  (φ : B →⋆ₐ[ℂ] C) (hφ : ∀ b, σ (φ b) = τ b)

include hφ in
lemma gnsTendsto_tracePreserving {f : ℕ → B} {b : B}
    (h : GNSTendsto τ f atTop b) :
    GNSTendsto σ (fun j => φ (f j)) atTop (φ b) := by
  simpa only [GNSTendsto, ← map_sub φ, preGNS_norm_map_eq τ σ φ hφ] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite diffuse branch has a constructed normal trace and an actual
irreducible matrix source. Its sole remaining local input is Popa freeness. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open BoundedHochschild.KadisonRingrose
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

local instance finitePresentationClosed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (P : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_IntegerMomentMaps
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Naturality and coefficient reindexing for finite integer-power words. -/

namespace KadisonSimilarity
open HochschildPatching
variable {A B I J : Type*} [CStarAlgebra A] [CStarAlgebra B]

omit [CStarAlgebra A] [CStarAlgebra B] in
theorem admissibleIntTail_reindex (f : I → J) (l : List (IntAtom I))
    (hl : admissibleIntTail l) :
    admissibleIntTail (l.map (fun b => (b.1, b.2.map f))) := by
  refine ⟨fun h => hl.1 (List.map_eq_nil_iff.mp h), ?_⟩
  intro b hb
  rw [← List.map_dropLast] at hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact fun h => hl.2 c hc (Option.map_eq_none_iff.mp h)

end KadisonSimilarity

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixExpectationIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of finite matrix averaging with the constructed normal
conditional expectation, for the relative quantization argument. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

def matrixSystemOfUnits {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    {n : ℕ} (E : MatrixUnitSystem (Fin n) A) : HochschildMatrixSystems.MatrixSystem A n where
  entry := E.entry
  star_entry := E.star_entry
  entry_mul := E.mul_entry
  sum_diagonal := E.total

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H} (υ : TracialRepresentation M)

local instance matrixExpectationClosed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_RelativeMatrixQuantization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative finite matrix averaging in an irreducible inclusion. The matrix
systems stay in the prescribed source algebra throughout the refinement. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} [Nontrivial N.toStarSubalgebra]
  (υ : TracialRepresentation M) (hNM : N ≤ M)
  (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a * c = c * coordinateInclusion hNM a) →
    ∃ z : ℂ, c = z • 1)

local instance relativeMatrixAmbientClosed_r81c299_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
local instance relativeMatrixSourceClosed : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (N : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceCornerQuantization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local quantization inside every nonzero corner of the prescribed source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildCorners
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hNM : N ≤ M)

local instance sourceCornerAmbientClosed_r81c299_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
local instance sourceCornerSourceClosed : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (N : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceWeakPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak powers in a prescribed diffuse source, tested against ambient
coefficients. Conditional expectation moves only the coefficients. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hNM : N ≤ M)

local instance weakPowersSourceClosed : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (N : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceMomentConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Maximal partial unitaries for ambient moments, ordered inside the source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison HochschildPatching BoundedHochschild
open Filter Topology
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance momentSourceClosed : IsClosed (R.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (R : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceQuotientMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing ultrapower moments produced by a sequence of source unitaries. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance quotientMomentAmbientClosed_r81c299_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
local instance quotientMomentSourceClosed : IsClosed (R.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (R : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceAllMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All mixed words from a countable ambient family vanish for a sequence
of source unitaries in the tracial ultrapower. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance allMomentAmbientClosed_r81c299_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
local instance allMomentSourceClosed : IsClosed (R.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (R : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceConstantMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prescribed-source unitaries annihilate all centered constant mixed moments. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance constantMomentAmbientClosed_r81c299_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
local instance constantMomentSourceClosed : IsClosed (R.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (R : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end


