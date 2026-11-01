-- Prove2me | Definitions.Def_OAIQ075A023
-- name    : OAIQ075A023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:21:23.774617+00:00
-- url     : https://prove2.me/theorems/b56b2471-c521-4471-b614-feb183fffb90
-- title:
--   Definitions bundle OAIQ075A023 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 222 declarations of OpenAI's Lean: 79 definitions, 6 inductive types or structures, 4 instances and 133 theorems. The definitions and types are `OAI.KadisonSimilarity.CanonicalFreeCornerCoreInput`, `OAI.KadisonSimilarity.CanonicalFreeCornerInput`, `OAI.KadisonSimilarity.CanonicalSecondFrame`, `OAI.KadisonSimilarity.CenteredWordParameter`, `OAI.KadisonSimilarity.CentralDecompositionData`, `OAI.KadisonSimilarity.CrossMultiplicityMatrixCovariance`, `OAI.KadisonSimilarity.CrossMultiplicityMatrixCovariance.slice`, `OAI.KadisonSimilarity.ElementaryCreationFormulas`, `OAI.KadisonSimilarity.FiniteFactorFreeCornerInputs`, `OAI.KadisonSimilarity.FreeCreationParameter`, `OAI.KadisonSimilarity.LeadingWordParameter`, `OAI.KadisonSimilarity.MatrixGNSArray`, `OAI.KadisonSimilarity.MatrixWordCovariance`, `OAI.KadisonSimilarity.NestedTracialMatrices.nonemptyFinColumnFamily`, `OAI.KadisonSimilarity.Popa1995ConjugateFreenessInput`, `OAI.KadisonSimilarity.TracialCornerGeometry.LocalFreeCornerPublishedInputs`, `OAI.KadisonSimilarity.TracialCornerGeometry.MatrixConjugationExtensionInput`, `OAI.KadisonSimilarity.TracialCornerGeometry.chosenMatrixExtension`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeConjugatedFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeConjugatedParameter`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationUnitary`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeWordFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra`, `OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra`, `OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra`, `OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAction`, `OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism`, `OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace`, `OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn`, `OAI.KadisonSimilarity.amplifiedCommutantSet`, `OAI.KadisonSimilarity.amplifiedScalarRepresentation`, `OAI.KadisonSimilarity.canonicalGeneratedAlgebra` and 45 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_FiniteMoments`, `BoundedHochschild_MixedWords`, `KadisonSimilarity_FreeProduct_BaseCommutatorCompression`, `KadisonSimilarity_FreeProduct_CanonicalFreeCornerCore`, `KadisonSimilarity_FreeProduct_CanonicalFreeCornerEstimate`, `KadisonSimilarity_FreeProduct_FreeCreationOperators`, `KadisonSimilarity_FreeProduct_FreeLeadingWords`, `KadisonSimilarity_FreeProduct_FreeMatrixConjugation`, `KadisonSimilarity_FreeProduct_FreeMatrixConjugationUnitary`, `KadisonSimilarity_FreeProduct_FreeMatrixExtension`, `KadisonSimilarity_FreeProduct_FreeMatrixFactorAction`, `KadisonSimilarity_FreeProduct_FreePrefixIsometry`, `KadisonSimilarity_FreeProduct_FreeProductAutomorphisms`, `KadisonSimilarity_FreeProduct_FreeProductMatrixExtension`, `KadisonSimilarity_FreeProduct_FreeWordHilbert`, `KadisonSimilarity_FreeProduct_GeneratedWordDensity`, `KadisonSimilarity_FreeProduct_LocalFreeCornerInputs`, `KadisonSimilarity_FreeProduct_TracialSymmetryDilation`, `KadisonSimilarity_FreeProduct_TracialSymmetryExtraction`, `KadisonSimilarity_FreeProduct_TracialWordIsometry`, `KadisonSimilarity_FreeProduct_WordLevelClassification`, `KadisonSimilarity_Representation_CanonicalGeneratedModel`, `KadisonSimilarity_Representation_CentralDecomposition`, `KadisonSimilarity_Representation_ClosedFamilySpan`, `KadisonSimilarity_Representation_CountableAmplification`, `KadisonSimilarity_Representation_FiniteAmplificationReduction`, `KadisonSimilarity_Representation_GeneratedEmbeddings`, `KadisonSimilarity_Representation_KaplanskyGeneral`, `KadisonSimilarity_Tensor_EndpointClassification`, `KadisonSimilarity_Tensor_InvariantIntertwiners`, `KadisonSimilarity_Tensor_MultiplicityClassification`, `KadisonSimilarity_Tensor_TensorPacketDensity`, `KadisonSimilarity_Tracial_ConcreteMatrixTower`, `KadisonSimilarity_Tracial_ConjugateMomentCriterion`, `KadisonSimilarity_Tracial_FiniteFactorApplication`, `KadisonSimilarity_Tracial_GNSTracialGeometry`, `KadisonSimilarity_Tracial_GeneratedGNSModels`, `KadisonSimilarity_Tracial_GeneratedGNSRecovery`, `KadisonSimilarity_Tracial_MatrixArrayFlattening`, `KadisonSimilarity_Tracial_MatrixDiagonalEmbedding`, `KadisonSimilarity_Tracial_MatrixSmallCorner`, `KadisonSimilarity_Tracial_MatrixSubfactorTransfer`, `KadisonSimilarity_Tracial_MatrixTracialGNS`, `KadisonSimilarity_Tracial_MatrixUnitFamilies`, `KadisonSimilarity_Tracial_MatrixVonNeumannRange`, `KadisonSimilarity_Tracial_NormalTracialGeometry`, `KadisonSimilarity_Tracial_OppositeTracialGeometry`, `KadisonSimilarity_Tracial_PopaConjugatePosition`, `KadisonSimilarity_Tracial_TracialBaseGeometry`, `KadisonSimilarity_Tracial_TracialCreationCoordinates`, `KadisonSimilarity_Tracial_TracialEmbeddingTransport`, `KadisonSimilarity_Tracial_TracialGeometrySupport`, `KadisonSimilarity_Tracial_TracialL2Closure`, `KadisonSimilarity_Tracial_TracialSmallColumn`, `KadisonSimilarity_Tracial_TracialSubalgebraModels`, `KadisonSimilarity_Tracial_TracialUltrapowerHom`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A013`, `OAIQ075A015`, `OAIQ075A016` and `OAIQ075A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A027`, `OAIQ075A028`, `OAIQ075A029` and `OAIQ075A030`; the statements `OAI.KadisonSimilarity.TracialCornerGeometry.l2Generated_tracialExpectation`, `OAI.KadisonSimilarity.canonicalFreeFactorComparison`, `OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner` and `OAI.KadisonSimilarity.original_symmetry_bound_of_free_corner`; the proof of `OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A013
import Definitions.Def_OAIQ075A015
import Definitions.Def_OAIQ075A016
import Definitions.Def_OAIQ075A017

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MixedWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-word Taylor expansions, moment corners and patch coefficients. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]


variable {I : Type*} (F : I → M)
lemma norm_wordCoeff (hF : ∀ i, ‖F i‖ ≤ 1) (a : Option I) : ‖wordCoeff F a‖ ≤ 1 := by
  cases a with
  | none => exact IsStarProjection.norm_le (1 : M) (IsStarProjection.one M)
  | some i => exact hF i
end HochschildPatching

 

 

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison

variable {M : Type*} [CStarAlgebra M]
variable {I : Type*} (F : I → M)

variable [PartialOrder M] (τ : M →ₚ[ℂ] ℂ)
lemma trace_list_sum_bound (A : M) (l : List M) (c : ℝ)
    (h : ∀ x ∈ l, ‖τ (A*x)‖ ≤ c) : ‖τ (A*l.sum)‖ ≤ (l.length : ℝ)*c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.sum_cons,mul_add,map_add,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    exact (norm_add_le _ _).trans ((add_le_add (h x (List.mem_cons_self ..))
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))).trans_eq (add_comm _ _))

end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteMoments
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small unitary moments, reindexing and simultaneous moment sequences. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]
variable {I J : Type*} {K L : ℕ}

lemma wordCoeff_smul (F : I → M) (c : ℂ) (a : Option I) :
    wordCoeff (fun i => c • F i) a=c^coeffNumber a • wordCoeff F a := by
  cases a <;> simp [wordCoeff,coeffNumber]
end HochschildPatching

 

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantIntertwiners
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix realization of the invariant-intertwiner argument

Finite coefficient forms are constructed from explicit Hilbert-space matrix
realizations. Normalized Hilbert--Schmidt inner products supply the matrix-unit
norms, while left matrix actions supply endpoint transfer. The sole invariant
theory input remains finite-dimensional Schur--Weyl spanning.
-/

noncomputable section
namespace KadisonSimilarity

variable {E F α : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [Fintype α] [DecidableEq α]

variable {k l : ℕ}

/-- Isometric simultaneous-conjugation covariance on source and test words.
These are local actions on the realized tensor words, not coefficient formulas. -/
structure MatrixWordCovariance
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) where
  sourceAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F k →ₗᵢ[ℂ] EndpointTensor E F k
  testAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F l →ₗᵢ[ℂ] EndpointTensor E F l
  intertwine : ∀ u, Y.comp (sourceAction u).toContinuousLinearMap =
    (testAction u).toContinuousLinearMap.comp Y
  source_covariance : ∀ (u : Matrix.unitaryGroup α ℂ) (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord Ω (fun i => R.center ((u : Matrix α α ℂ) * v (some (Sum.inl i)) * star (u : Matrix α α ℂ))) =
      sourceAction u (endpointWord Ω (fun i => R.center (v (some (Sum.inl i)))))
  test_covariance : ∀ (u : Matrix.unitaryGroup α ℂ) (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord (R.full (star ((u : Matrix α α ℂ) * v none * star (u : Matrix α α ℂ))))
      (fun j => J (R.center ((u : Matrix α α ℂ) * v (some (Sum.inr j)) * star (u : Matrix α α ℂ)))) =
      testAction u (endpointWord (R.full (star (v none)))
        (fun j => J (R.center (v (some (Sum.inr j))))))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_BaseCommutatorCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression of commutators with base-algebra elements needs no invariance
hypothesis on the other operator. This also restores the original operator
after the free-product symmetrization. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- Faithfulness of the tracial algebra vectors makes left multiplication
faithful as an algebra representation. -/
theorem left_injective (hfaithful : Function.Injective G.vector) :
    Function.Injective G.left := by
  intro a b hab
  apply hfaithful
  have hv := congrArg (fun T : H →L[ℂ] H => T (G.vector 1)) hab
  simpa only [G.left_vector, mul_one] using hv

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Completed invariant intertwiners from matrix-stage geometry

Finite-dimensional Schur--Weyl spanning is the only invariant-theory input.
The remaining assumptions describe a nested dense tracial matrix realization,
its conjugation, and the operator's actual left and conjugation intertwinings.
The coefficient identity and completed permutation classification are derived.
-/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

def fullMatrixStage (R : ∀ s, MatrixHilbertStage (E := E) (F := F) (α := A s))
    (s : ℕ) : Set E := Set.range (R s).full

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_MultiplicityClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem tensorSlice_lift (T : H →L[ℂ] K) (b : G) :
    (tensorSlice b).comp (hilbertTensorLift T) = T.comp (tensorSlice b) := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  simp only [ContinuousLinearMap.comp_apply, hilbertTensorLift_insert, tensorSlice_insert, map_smul]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBaseGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed base algebra has its actual tracial Hilbert representation
inside the ambient one. Its left, right, and conjugation actions are compatible
with the canonical base inclusion. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

variable [IsClosed (A : Set P)]

/-- The tracial conjugation of the base is exactly the restriction of ambient
tracial conjugation, proved on the dense algebra vectors. -/
theorem baseGeometry_conjugation_coe (x : G.baseSpace A) :
    ((G.baseGeometry A).conjugation x : H) = G.conjugation (x : H) := by
  refine (G.baseVector_dense A).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change ((G.baseGeometry A).conjugation ((G.baseGeometry A).vector a) : H) =
    G.conjugation (G.vector (a : P))
  rw [TracialCornerGeometry.conjugation_vector, G.conjugation_vector]
  rfl

/-- Base right multiplication is the restriction of actual ambient right
multiplication. No independent commutation representation is assumed. -/
theorem baseGeometry_right_coe (a : A) (x : G.baseSpace A) :
    ((G.baseGeometry A).right a x : H) = G.right (a : P) (x : H) := by
  refine (G.baseVector_dense A).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  change ((G.baseGeometry A).right a ((G.baseGeometry A).vector b) : H) =
    G.right (a : P) (G.vector (b : P))
  rw [TracialCornerGeometry.right_vector, G.right_vector]
  rfl

/-- The completed base subspace is invariant under right multiplication by
its algebra, with membership derived from the constructed base geometry. -/
theorem baseSpace_right_invariant (a : A) (x : H) (hx : x ∈ G.baseSpace A) :
    G.right (a : P) x ∈ G.baseSpace A := by
  rw [← G.baseGeometry_right_coe A a (⟨x, hx⟩ : G.baseSpace A)]
  exact ((G.baseGeometry A).right a (⟨x, hx⟩ : G.baseSpace A)).property

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordLevelClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Different multiplicities and the orthogonal word-level decomposition

Source and target word levels have independent Hilbert multiplicity spaces.
Their scalar slices are bounded endpoint intertwiners, so unequal degrees
vanish by the completed endpoint classification.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {Gsource Gtarget H K : Type*}
  [NormedAddCommGroup Gsource] [InnerProductSpace ℂ Gsource]
  [NormedAddCommGroup Gtarget] [InnerProductSpace ℂ Gtarget]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Distinct source and target multiplicities do not affect the tensor
intertwining calculation. -/
theorem crossMultiplicitySlice_intertwines
    (Y : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K)
    (S : H →L[ℂ] H) (T : K →L[ℂ] K)
    (hY : Y.comp (hilbertTensorLift S) = (hilbertTensorLift T).comp Y)
    (a : Gsource) (b : Gtarget) :
    (crossMultiplicitySlice Y a b).comp S = T.comp (crossMultiplicitySlice Y a b) := by
  ext x
  have heq := congrArg (fun A : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K =>
    A (hilbertTensorInsert a x)) hY
  simp only [ContinuousLinearMap.comp_apply, hilbertTensorLift_insert] at heq
  change tensorSlice b (Y (hilbertTensorInsert a (S x))) =
    T (tensorSlice b (Y (hilbertTensorInsert a x)))
  rw [heq]
  exact congrArg (fun A : HilbertTensor Gtarget K →L[ℂ] K =>
    A (Y (hilbertTensorInsert a x))) (tensorSlice_lift T b)

section EndpointLevels

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {α : Type*} [Fintype α] [DecidableEq α] {k l : ℕ}

/-- Actual word covariance for an operator between independent multiplicity
spaces. The word formulas refer only to the common endpoint and tail factors. -/
structure CrossMultiplicityMatrixCovariance
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : HilbertTensor Gsource (EndpointTensor E F k) →L[ℂ]
      HilbertTensor Gtarget (EndpointTensor E F l)) where
  sourceAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F k →ₗᵢ[ℂ] EndpointTensor E F k
  testAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F l →ₗᵢ[ℂ] EndpointTensor E F l
  intertwine : ∀ u, Y.comp (hilbertTensorLift (sourceAction u).toContinuousLinearMap) =
    (hilbertTensorLift (testAction u).toContinuousLinearMap).comp Y
  source_covariance : ∀ (u : Matrix.unitaryGroup α ℂ)
      (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord Ω (fun i => R.center
      ((u : Matrix α α ℂ) * v (some (Sum.inl i)) * star (u : Matrix α α ℂ))) =
      sourceAction u (endpointWord Ω (fun i => R.center (v (some (Sum.inl i)))))
  test_covariance : ∀ (u : Matrix.unitaryGroup α ℂ)
      (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord (R.full (star
      ((u : Matrix α α ℂ) * v none * star (u : Matrix α α ℂ))))
      (fun j => J (R.center
        ((u : Matrix α α ℂ) * v (some (Sum.inr j)) * star (u : Matrix α α ℂ)))) =
      testAction u (endpointWord (R.full (star (v none)))
        (fun j => J (R.center (v (some (Sum.inr j))))))

/-- Actual covariance passes to a scalar cross-multiplicity slice. -/
def CrossMultiplicityMatrixCovariance.slice
    {R : MatrixHilbertStage (E := E) (F := F) (α := α)} {J : F →ₗᵢ⋆[ℂ] F}
    {Ω : E} {Y : HilbertTensor Gsource (EndpointTensor E F k) →L[ℂ]
      HilbertTensor Gtarget (EndpointTensor E F l)}
    (cov : CrossMultiplicityMatrixCovariance R J Ω Y) (a : Gsource) (b : Gtarget) :
    MatrixWordCovariance R J Ω (crossMultiplicitySlice Y a b) where
  sourceAction := cov.sourceAction
  testAction := cov.testAction
  intertwine u := crossMultiplicitySlice_intertwines Y _ _ (cov.intertwine u) a b
  source_covariance := cov.source_covariance
  test_covariance := cov.test_covariance

end EndpointLevels

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeWordHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Gram matrices of the regrouped free-product word vectors. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

theorem inner_tracialWordTensor (n : ℕ) (d e : D) (b f : A)
    (a a' : Fin n → A) (c c' : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (ha' : ∀ i, G.trace (a' i : P) = 0)
    (hc : ∀ i, G.trace (c i : P) = 0) (hc' : ∀ i, G.trace (c' i : P) = 0) :
    inner ℂ (tracialWordTensor G A D n d b a c ha hc)
      (tracialWordTensor G A D n e f a' c' ha' hc') =
      G.trace (star (d : P) * e) * G.trace (star (b : P) * f) *
        ((∏ i, G.trace (star (a i : P) * a' i)) *
          ∏ i, G.trace (star (c i : P) * c' i)) := by
  unfold tracialWordTensor
  refine (inner_hilbertTensorInsert (tracialMultiplicityWord G A n b a ha)
    (tracialMultiplicityWord G A n f a' ha') (tracialEndpointWord G D n d c hc)
    (tracialEndpointWord G D n e c' hc')).trans ?_
  unfold tracialMultiplicityWord tracialEndpointWord
  rw [inner_hilbertTensorInsert, inner_completedTensorWord, inner_endpointWord]
  have hA (x y : A) (hx : G.trace (x : P) = 0) (hy : G.trace (y : P) = 0) :
      inner ℂ (G.baseSymmetryLetter A x hx) (G.baseSymmetryLetter A y hy) =
        G.trace (star (x : P) * y) := G.baseVector_inner A x y
  have hD (x y : D) (hx : G.trace (x : P) = 0) (hy : G.trace (y : P) = 0) :
      inner ℂ (G.baseSymmetryLetter D x hx) (G.baseSymmetryLetter D y hy) =
        G.trace (star (x : P) * y) := G.baseVector_inner D x y
  simp only [hA, hD, G.baseVector_inner]
  ring

/-- Scalar freeness gives precisely the inner product of the actual tensors,
including both unrestricted endpoint factors. -/
theorem inner_reducedWord_eq_tensor (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (n : ℕ) (d e : D) (b f : A) (a a' : Fin n → A) (c c' : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (ha' : ∀ i, G.trace (a' i : P) = 0)
    (hc : ∀ i, G.trace (c i : P) = 0) (hc' : ∀ i, G.trace (c' i : P) = 0) :
    inner ℂ (G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
      (fun i => (c i : P)) * (b : P)))
      (G.vector ((e : P) * alternatingProduct (fun i => (a' i : P))
        (fun i => (c' i : P)) * (f : P))) =
      inner ℂ (tracialWordTensor G A D n d b a c ha hc)
        (tracialWordTensor G A D n e f a' c' ha' hc') := by
  rw [G.inner_vector, inner_tracialWordTensor]
  have hx := CenteredPairWord.of_pairWord (τ := G.trace)
    (fun i => (a i : P)) (fun i => (c i : P))
    (fun i => (a i).property) (fun i => (c i).property) ha hc
  have hy := CenteredPairWord.of_pairWord (τ := G.trace)
    (fun i => (a' i : P)) (fun i => (c' i : P))
    (fun i => (a' i).property) (fun i => (c' i).property) ha' hc'
  have h := hf.symm.trace_full_pairWords G.trace_star hτ G.tracial hx hy
    d.property e.property b.property f.property
  simpa only [prod_pairWord, alternatingProduct, centeredWordPairing_pairWord] using h

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
/-- Different numbers of centered pairs give orthogonal actual word vectors. -/
theorem inner_reducedWord_ne (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (n m : ℕ) (hnm : n ≠ m) (d e : D) (b f : A)
    (a : Fin n → A) (c : Fin n → D) (a' : Fin m → A) (c' : Fin m → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (ha' : ∀ i, G.trace (a' i : P) = 0)
    (hc : ∀ i, G.trace (c i : P) = 0) (hc' : ∀ i, G.trace (c' i : P) = 0) :
    inner ℂ (G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
      (fun i => (c i : P)) * (b : P)))
      (G.vector ((e : P) * alternatingProduct (fun i => (a' i : P))
        (fun i => (c' i : P)) * (f : P))) = 0 := by
  rw [G.inner_vector]
  have hx := CenteredPairWord.of_pairWord (τ := G.trace)
    (fun i => (a i : P)) (fun i => (c i : P))
    (fun i => (a i).property) (fun i => (c i).property) ha hc
  have hy := CenteredPairWord.of_pairWord (τ := G.trace)
    (fun i => (a' i : P)) (fun i => (c' i : P))
    (fun i => (a' i).property) (fun i => (c' i).property) ha' hc'
  have h := hf.symm.trace_full_pairWords G.trace_star hτ G.tracial hx hy
    d.property e.property b.property f.property
  have hz : centeredWordPairing G.trace (pairWord (fun i => (a i : P))
      (fun i => (c i : P))) (pairWord (fun i => (a' i : P))
      (fun i => (c' i : P))) = 0 :=
    centeredWordPairing_eq_zero_of_length_ne (by simp only [length_pairWord]; omega)
  rw [hz, mul_zero] at h
  simpa only [prod_pairWord, alternatingProduct] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorPacketDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense elementary tensor tests for bounded maps on regrouped word spaces. -/

noncomputable section
namespace KadisonSimilarity
open scoped TensorProduct

section TensorPackets

variable {X B E F K : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- Hilbert tensor totality needs only a normed codomain. -/
theorem continuousLinearMap_ext_hilbertTensorInsert_normed
    (f g : HilbertTensor X B →L[ℂ] K)
    (h : ∀ a b, f (hilbertTensorInsert a b) = g (hilbertTensorInsert a b)) : f = g := by
  refine ContinuousLinearMap.ext fun z => ?_
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq f.continuous g.continuous
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | tmul a b => exact h a b
    | add a b ha hb =>
      rw [UniformSpace.Completion.coe_add]
      erw [map_add, map_add]
      exact congrArg₂ (· + ·) ha hb

/-- One completed multiplicity word and one completed endpoint word. -/
def tensorPacket {n : ℕ} (p : ((Fin n → X) × B) × (E × (Fin n → F))) :
    HilbertTensor (HilbertTensor (CompletedTensorWord X n) B) (EndpointTensor E F n) :=
  hilbertTensorInsert (hilbertTensorInsert (completedTensorWord p.1.1) p.1.2)
    (endpointWord p.2.1 p.2.2)

/-- Dense alphabet vectors determine a map on completed tensor words. -/
theorem continuousLinearMap_ext_denseCompletedWords {DX : Type*} (vx : DX → X)
    (hx : DenseRange vx) {n : ℕ} (f g : CompletedTensorWord X n →L[ℂ] K)
    (h : ∀ a : Fin n → DX, f (completedTensorWord (fun i => vx (a i))) =
      g (completedTensorWord (fun i => vx (a i)))) : f = g := by
  have hd := DenseRange.piMap (fun _ : Fin n => hx)
  have heq := hd.equalizer (f.continuous.comp (continuous_completedTensorWord n))
    (g.continuous.comp (continuous_completedTensorWord n)) (funext h)
  apply continuousLinearMap_ext_completedTensorWords
  intro a
  exact congrFun heq a

/-- Dense base vectors and centered alphabets determine multiplicity maps. -/
theorem continuousLinearMap_ext_denseMultiplicityWords {DX DB : Type*}
    (vx : DX → X) (vb : DB → B) (hx : DenseRange vx) (hb : DenseRange vb) {n : ℕ}
    (f g : HilbertTensor (CompletedTensorWord X n) B →L[ℂ] K)
    (h : ∀ (a : Fin n → DX) (b : DB),
      f (hilbertTensorInsert (completedTensorWord (fun i => vx (a i))) (vb b)) =
      g (hilbertTensorInsert (completedTensorWord (fun i => vx (a i))) (vb b))) : f = g := by
  have ha (a : Fin n → DX) :
      f.comp (hilbertTensorInsert (completedTensorWord (fun i => vx (a i)))) =
        g.comp (hilbertTensorInsert (completedTensorWord (fun i => vx (a i)))) := by
    apply DFunLike.coe_injective
    exact hb.equalizer (by fun_prop) (by fun_prop) (funext (h a))
  apply continuousLinearMap_ext_hilbertTensorInsert_normed
  intro x b
  have heq : f.comp (hilbertTensorRightInsert b) = g.comp (hilbertTensorRightInsert b) := by
    apply continuousLinearMap_ext_denseCompletedWords vx hx
    intro a
    exact congrArg (fun L : B →L[ℂ] K => L b) (ha a)
  exact congrArg (fun L : CompletedTensorWord X n →L[ℂ] K => L x) heq

/-- Dense endpoint vectors and centered alphabets determine endpoint maps. -/
theorem continuousLinearMap_ext_denseEndpointWords {DE DF : Type*}
    (ve : DE → E) (vf : DF → F) (he : DenseRange ve) (hf : DenseRange vf) {n : ℕ}
    (f g : EndpointTensor E F n →L[ℂ] K)
    (h : ∀ (d : DE) (c : Fin n → DF),
      f (endpointWord (ve d) (fun i => vf (c i))) =
        g (endpointWord (ve d) (fun i => vf (c i)))) : f = g := by
  have hd (d : DE) : f.comp (endpointInsert (ve d)) = g.comp (endpointInsert (ve d)) := by
    apply continuousLinearMap_ext_denseCompletedWords vf hf
    intro c
    exact h d c
  apply continuousLinearMap_ext_endpointWords
  intro d c
  have heq : f.comp (hilbertTensorRightInsert (completedTensorWord c)) =
      g.comp (hilbertTensorRightInsert (completedTensorWord c)) := by
    apply DFunLike.coe_injective
    apply he.equalizer (by fun_prop) (by fun_prop)
    funext e
    exact congrArg (fun L : CompletedTensorWord F n →L[ℂ] K => L (completedTensorWord c)) (hd e)
  exact congrArg (fun L : E →L[ℂ] K => L d) heq

/-- Dense choices for each algebra letter suffice in the packet test. -/
theorem continuousLinearMap_ext_denseTensorPackets
    {DX DB DE DF : Type*} (vx : DX → X) (vb : DB → B) (ve : DE → E) (vf : DF → F)
    (hx : DenseRange vx) (hb : DenseRange vb) (he : DenseRange ve) (hf : DenseRange vf)
    {n : ℕ} (f g : HilbertTensor (HilbertTensor (CompletedTensorWord X n) B)
      (EndpointTensor E F n) →L[ℂ] K)
    (h : ∀ (a : Fin n → DX) (b : DB) (d : DE) (c : Fin n → DF),
      f (tensorPacket ((fun i => vx (a i), vb b), (ve d, fun i => vf (c i)))) =
        g (tensorPacket ((fun i => vx (a i), vb b), (ve d, fun i => vf (c i))))) : f = g := by
  have ha (a : Fin n → DX) (b : DB) :
      f.comp (hilbertTensorInsert (hilbertTensorInsert (completedTensorWord (fun i => vx (a i))) (vb b))) =
        g.comp (hilbertTensorInsert (hilbertTensorInsert (completedTensorWord (fun i => vx (a i))) (vb b))) := by
    apply continuousLinearMap_ext_denseEndpointWords ve vf he hf
    exact h a b
  apply continuousLinearMap_ext_hilbertTensorInsert_normed
  intro j e
  have hj : f.comp (hilbertTensorRightInsert e) = g.comp (hilbertTensorRightInsert e) := by
    apply continuousLinearMap_ext_denseMultiplicityWords vx vb hx hb
    intro a b
    exact congrArg (fun L : EndpointTensor E F n →L[ℂ] K => L e) (ha a b)
  exact congrArg (fun L : HilbertTensor (CompletedTensorWord X n) B →L[ℂ] K => L j) hj

end TensorPackets

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.embeddedMatrixStage_center _root_.OAI.KadisonSimilarity.embeddedMatrixStage_full _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the completed free-product word inclusions from the
proved Gram identities and totality of elementary tensors. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

def centeredLetterVector (a : CenteredTracialLetter G A) :
    centeredSubspace (G.baseVector A 1) := G.baseSymmetryLetter A a.1 a.2

theorem centeredLetterVector_dense (hτ : G.trace 1 = 1) :
    DenseRange (centeredLetterVector G A) := by
  have hd := denseRange_tracialCenter (G.baseVector A) (G.baseVector_dense A)
  apply hd.mono
  rintro x ⟨a, rfl⟩
  let b : A := a - G.trace (a : P) • 1
  have hb : G.trace (b : P) = 0 := by
    change G.trace ((a : P) - G.trace (a : P) • 1) = 0
    simp only [map_sub, map_smul, hτ, smul_eq_mul, mul_one, sub_self]
  refine ⟨⟨b, hb⟩, ?_⟩
  apply Subtype.ext
  change G.baseVector A b = (tracialCenter (G.baseVector A) a : G.baseSpace A)
  rw [coe_tracialCenter (G.baseGeometry A).trace (G.baseVector A)
    (G.baseVector_inner A) hτ]
  simp only [b, map_sub, map_smul, TracialCornerGeometry.baseGeometry_trace]

theorem tracialTensorFamily_dense (hτ : G.trace 1 = 1) (n : ℕ) :
    (Submodule.span ℂ (Set.range (tracialTensorFamily G A D n))).topologicalClosure = ⊤ := by
  apply dense_span_of_scalar_tests
  intro f hf
  apply continuousLinearMap_ext_denseTensorPackets (centeredLetterVector G A)
    (G.baseVector A) (G.baseVector D) (centeredLetterVector G D)
    (centeredLetterVector_dense G A hτ) (G.baseVector_dense A)
    (G.baseVector_dense D) (centeredLetterVector_dense G D hτ)
  intro a b d c
  exact hf ((a, b), (d, c))

theorem tracialFamilyGram (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (n : ℕ) (p q : TracialWordParameter G A D n) :
    inner ℂ (tracialAlgebraFamily G A D n p) (tracialAlgebraFamily G A D n q) =
      inner ℂ (tracialTensorFamily G A D n p) (tracialTensorFamily G A D n q) :=
  inner_reducedWord_eq_tensor G A D hτ hf n p.2.1 q.2.1 p.1.2 q.1.2
    (fun i => (p.1.1 i).1) (fun i => (q.1.1 i).1)
    (fun i => (p.2.2 i).1) (fun i => (q.2.2 i).1)
    (fun i => (p.1.1 i).2) (fun i => (q.1.1 i).2)
    (fun i => (p.2.2 i).2) (fun i => (q.2.2 i).2)

/-- The genuine isometric inclusion of one completed word level. -/
def tracialWordInclusion (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A) (n : ℕ) :
    MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n →ₗᵢ[ℂ] H :=
  denseFamilyIsometry (tracialTensorFamily G A D n) (tracialAlgebraFamily G A D n)
    (tracialTensorFamily_dense G A D hτ n) (tracialFamilyGram G A D hτ hf n)

@[simp] theorem tracialWordInclusion_family (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (n : ℕ) (p : TracialWordParameter G A D n) :
    tracialWordInclusion G A D hτ hf n (tracialTensorFamily G A D n p) =
      tracialAlgebraFamily G A D n p := by
  unfold tracialWordInclusion
  exact denseFamilyIsometry_apply (tracialTensorFamily G A D n)
    (tracialAlgebraFamily G A D n) (tracialTensorFamily_dense G A D hτ n)
    (tracialFamilyGram G A D hτ hf n) p

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ClosedFamilySpan
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual closed spans and elementary tensors of total families. -/

noncomputable section
namespace KadisonSimilarity

variable {I J E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem tensorFamily_total (v : I → E) (w : J → F)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (hw : (Submodule.span ℂ (Set.range w)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (fun p : I × J =>
      hilbertTensorInsert (v p.1) (w p.2)))).topologicalClosure = ⊤ := by
  apply dense_span_of_scalar_tests
  intro f hf
  have hi (i : I) : f.comp (hilbertTensorInsert (v i)) = 0 := by
    apply continuousLinearMap_eq_zero_of_total w hw
    intro j
    exact hf (i, j)
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro x y
  have hy : f.comp (hilbertTensorRightInsert y) = 0 := by
    apply continuousLinearMap_eq_zero_of_total v hv
    intro i
    exact congrArg (fun g => g y) (hi i)
  exact congrArg (fun g => g x) hy

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeLeadingWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered leading-word subspaces for the creation operators. Density of
all centered words follows by centering the two unrestricted endpoints. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

abbrev CenteredWordParameter (side : Bool) :=
  {xs : List P // AlternatingCenteredWord G.trace A D side xs}

abbrev LeadingWordParameter (side : Bool) :=
  {xs : CenteredWordParameter G A D side // xs.1 ≠ []}

def centeredWordFamily (side : Bool) (xs : CenteredWordParameter G A D side) : H :=
  G.vector xs.1.prod

def leadingWordFamily (side : Bool) (xs : LeadingWordParameter G A D side) : H :=
  G.vector xs.1.1.prod

abbrev centeredWordSpace (side : Bool) : ClosedSubmodule ℂ H :=
  closedFamilySpan (centeredWordFamily G A D side)

abbrev leadingWordSpace (side : Bool) : ClosedSubmodule ℂ H :=
  closedFamilySpan (leadingWordFamily G A D side)

theorem leadingWordSpace_le_centeredWordSpace (side : Bool) :
    (leadingWordSpace G A D side).toSubmodule ≤ (centeredWordSpace G A D side).toSubmodule := by
  apply closedFamilySpan_le
  intro xs
  exact (closedFamilyVector (centeredWordFamily G A D side) xs.1).property

def leadingIntoCentered (side : Bool) :
    leadingWordSpace G A D side →ₗᵢ[ℂ] centeredWordSpace G A D side where
  toLinearMap := Submodule.inclusion (leadingWordSpace_le_centeredWordSpace G A D side)
  norm_map' _ := rfl

@[simp] theorem leadingIntoCentered_coe (side : Bool) (x : leadingWordSpace G A D side) :
    (leadingIntoCentered G A D side x : H) = x := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreePrefixIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full first-factor letter tensored with opposite-factor words acts by
actual left multiplication. This constructs the head coordinates. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

def freeHeadTensor (p : D × CenteredWordParameter G A D true) :
    HilbertTensor (G.baseSpace D) (centeredWordSpace G A D true) :=
  hilbertTensorInsert (G.baseVector D p.1)
    (closedFamilyVector (centeredWordFamily G A D true) p.2)

def freeHeadVector (p : D × CenteredWordParameter G A D true) : H :=
  G.vector ((p.1 : P) * p.2.1.prod)

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem freeHeadTensor_total :
    (Submodule.span ℂ (Set.range (freeHeadTensor G A D))).topologicalClosure = ⊤ := by
  apply tensorFamily_total (G.baseVector D) (closedFamilyVector (centeredWordFamily G A D true))
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mp
      ((G.baseVector_dense D).mono (Submodule.subset_span))
  · exact closedFamilyVector_total _

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem freeHeadGram (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (p q : D × CenteredWordParameter G A D true) :
    inner ℂ (freeHeadVector G A D p) (freeHeadVector G A D q) =
      inner ℂ (freeHeadTensor G A D p) (freeHeadTensor G A D q) := by
  have ht : inner ℂ (freeHeadTensor G A D p) (freeHeadTensor G A D q) =
      G.trace (star (p.1 : P) * q.1) * G.trace (star p.2.1.prod * q.2.1.prod) := by
    exact (inner_hilbertTensorInsert _ _ _ _).trans
      (congrArg₂ (· * ·) (G.baseVector_inner D p.1 q.1) (G.inner_vector _ _))
  rw [ht, freeHeadVector, freeHeadVector, G.inner_vector]
  exact hf.trace_matching_heads G.trace_star hτ (side := false)
    p.1.property q.1.property p.2.2 q.2.2

def freeHeadIsometry (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D) :
    HilbertTensor (G.baseSpace D) (centeredWordSpace G A D true) →ₗᵢ[ℂ] H :=
  denseFamilyIsometry (freeHeadTensor G A D) (freeHeadVector G A D)
    (freeHeadTensor_total G A D) (freeHeadGram G A D hτ hf)

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
@[simp] theorem freeHeadIsometry_tensor (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) (p : D × CenteredWordParameter G A D true) :
    freeHeadIsometry G A D hτ hf (freeHeadTensor G A D p) = freeHeadVector G A D p := by
  unfold freeHeadIsometry
  exact denseFamilyIsometry_apply (freeHeadTensor G A D) (freeHeadVector G A D)
    (freeHeadTensor_total G A D) (freeHeadGram G A D hτ hf) p

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCreationOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.embeddedMatrixStage_center _root_.OAI.KadisonSimilarity.embeddedMatrixStage_full _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered-letter creation maps on the actual leading-word subspaces. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D B : StarSubalgebra ℂ P)
  [IsClosed (B : Set P)] (side : Bool) (hB : B = if side then A else D)

abbrev FreeCreationParameter := CenteredTracialLetter G B × CenteredWordParameter G A D (!side)

def freeCreationTensor (p : FreeCreationParameter G A D B side) :
    HilbertTensor (centeredSubspace (G.baseVector B 1)) (centeredWordSpace G A D (!side)) :=
  hilbertTensorInsert (centeredLetterVector G B p.1)
    (closedFamilyVector (centeredWordFamily G A D (!side)) p.2)

def freeCreationVector (p : FreeCreationParameter G A D B side) : H :=
  G.vector ((p.1.1 : P) * p.2.1.prod)

theorem freeCreationTensor_total (hτ : G.trace 1 = 1) :
    (Submodule.span ℂ (Set.range (freeCreationTensor G A D B side))).topologicalClosure = ⊤ := by
  apply tensorFamily_total (centeredLetterVector G B)
    (closedFamilyVector (centeredWordFamily G A D (!side)))
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mp
      ((centeredLetterVector_dense G B hτ).mono Submodule.subset_span)
  · exact closedFamilyVector_total _

include hB

theorem freeCreationGram (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (p q : FreeCreationParameter G A D B side) :
    inner ℂ (freeCreationVector G A D B side p) (freeCreationVector G A D B side q) =
      inner ℂ (freeCreationTensor G A D B side p) (freeCreationTensor G A D B side q) := by
  have hp : (p.1.1 : P) ∈ if side then A else D := by rw [← hB]; exact p.1.1.property
  have hq : (q.1.1 : P) ∈ if side then A else D := by rw [← hB]; exact q.1.1.property
  have ht : inner ℂ (freeCreationTensor G A D B side p) (freeCreationTensor G A D B side q) =
      G.trace (star (p.1.1 : P) * (q.1.1 : P)) *
        G.trace (star p.2.1.prod * q.2.1.prod) := by
    exact (inner_hilbertTensorInsert _ _ _ _).trans
      (congrArg₂ (· * ·) (G.baseVector_inner B p.1.1 q.1.1) (G.inner_vector _ _))
  rw [ht, freeCreationVector, freeCreationVector, G.inner_vector]
  exact hf.trace_matching_heads G.trace_star hτ hp hq p.2.2 q.2.2

def freeCreationIsometry (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D) :
    HilbertTensor (centeredSubspace (G.baseVector B 1))
      (centeredWordSpace G A D (!side)) →ₗᵢ[ℂ] H :=
  denseFamilyIsometry (freeCreationTensor G A D B side) (freeCreationVector G A D B side)
    (freeCreationTensor_total G A D B side hτ) (freeCreationGram G A D B side hB hτ hf)

@[simp] theorem freeCreationIsometry_tensor (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) (p : FreeCreationParameter G A D B side) :
    freeCreationIsometry G A D B side hB hτ hf (freeCreationTensor G A D B side p) =
      freeCreationVector G A D B side p := by
  unfold freeCreationIsometry
  exact denseFamilyIsometry_apply (freeCreationTensor G A D B side)
    (freeCreationVector G A D B side) (freeCreationTensor_total G A D B side hτ)
    (freeCreationGram G A D B side hB hτ hf) p

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialSymmetryDilation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered symmetry tests for contractions. The selfadjoint two-by-two
dilation has opposite diagonal entries, so its normalized trace vanishes
for every linear functional. Applying it to the selfadjoint off-diagonal
matrix of an arbitrary contraction yields a four-by-four symmetry with
the original contraction as one entry. This avoids any extra spectral
trace-equality hypothesis. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder Matrix
open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

/-- A centered four-by-four symmetry containing an arbitrary contraction.
The blocks use the existing selfadjoint off-diagonal contraction lemma. -/
def contractionSymmetryUnitary (a : A) (ha : ‖a‖ ≤ 1) : unitary (Mat (Mat A)) :=
  selfAdjointSymmetryUnitary (offdiag a (star a)) (offdiag_selfAdjoint a)
    (offdiag_norm_le_one a ha)

@[simp] theorem contractionSymmetryUnitary_entry (a : A) (ha : ‖a‖ ≤ 1) :
    (contractionSymmetryUnitary a ha : Mat (Mat A)) 0 1 0 1 = a := by
  change (selfAdjointSymmetryDilation (offdiag a (star a))) 0 1 0 1 = a
  rw [selfAdjointSymmetryDilation_entry]
  rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialSymmetryExtraction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered symmetry dilation is tested on actual finite Hilbert
arrays. Its original entry is recovered by coordinate insertion and
projection, both contractive. Thus no matrix-size factor enters the
commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

open HochschildMatrixDilation

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

/-- The four-by-four dilation acts on two successive two-coordinate sums. -/
def representedDoubleMatrix (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : Mat (Mat A)) :
    HilbertCopies (HilbertCopies H 2) 2 →L[ℂ] HilbertCopies (HilbertCopies H 2) 2 :=
  matrixOperator (fun i j => representedMatrix σ (S i j))

@[simp] theorem representedDoubleMatrix_apply (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : Mat (Mat A)) (x : HilbertCopies (HilbertCopies H 2) 2) (i k : Fin 2) :
    representedDoubleMatrix σ S x i k = ∑ j : Fin 2, ∑ l : Fin 2, σ (S i j k l) (x j l) := by
  simp [representedDoubleMatrix, representedMatrix, matrixOperator]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_KaplanskyGeneral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-by-two step from selfadjoint to arbitrary contractions. -/
noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The selfadjoint off-diagonal operator associated to a contraction. -/
def kaplanskyOffDiagonal (T : H →L[ℂ] H) : HilbertCopies H 2 →L[ℂ] HilbertCopies H 2 :=
  representedMatrix (StarAlgHom.id ℂ (H →L[ℂ] H)) (offdiag T (star T))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixVonNeumannRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete von Neumann algebra of finite operator matrices

The commutant of the diagonally amplified commutant consists exactly of
operator matrices with entries in the original von Neumann algebra. This
constructs the normal matrix realization used by spectral rounding.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded coordinate blocks, packaged as an actual matrix. -/
def matrixOfOperator {n : ℕ} (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) :
    Matrix (Fin n) (Fin n) (H →L[ℂ] H) :=
  Matrix.of (fun i j => matrixEntryCompression i j T)

omit [CompleteSpace H] in
@[simp] theorem matrixOfOperator_apply {n : ℕ}
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) (i j : Fin n) :
    matrixOfOperator T i j = matrixEntryCompression i j T := rfl

omit [CompleteSpace H] in
/-- Every finite operator array is recovered from its coordinate blocks. -/
theorem matrixOperator_entryCompressions {n : ℕ}
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) :
    matrixOperator (matrixOfOperator T) = T := by
  have hdecompose (x : HilbertCopies H n) :
      (∑ j : Fin n, PiLp.single 2 j (x j)) = x := by
    ext i
    simp
  ext x i
  change (matrixOperator (matrixOfOperator T) x) i = (T x) i
  rw [matrixOperator_apply]
  change (∑ j : Fin n, T (PiLp.single 2 j (x j)) i) = T x i
  have ht := congrArg ((PiLp.proj 2 (fun _ : Fin n => H) i).comp T) (hdecompose x)
  simpa only [map_sum, ContinuousLinearMap.comp_apply, PiLp.proj_apply] using ht

omit [CompleteSpace H] in
/-- A diagonal operator acts on a coordinate inclusion by the original operator. -/
theorem amplify_single {n : ℕ} (T : H →L[ℂ] H) (j : Fin n) (x : H) :
    amplify T n (PiLp.single 2 j x) = PiLp.single 2 j (T x) := by
  ext i
  by_cases hij : i = j
  · subst i
    simp only [amplify_apply, PiLp.single_eq_same]
  · simp only [amplify_apply, PiLp.single_apply, ite_eq_right hij, map_zero]

omit [CompleteSpace H] in
/-- Diagonal commutation is equivalent to commutation of every matrix entry. -/
theorem amplify_commutes_iff_entries {n : ℕ} (A : H →L[ℂ] H)
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) :
    amplify A n * T = T * amplify A n ↔
      ∀ i j, A * matrixEntryCompression i j T = matrixEntryCompression i j T * A := by
  constructor
  · intro h i j
    apply ContinuousLinearMap.ext
    intro x
    have hi := congrArg (fun S : HilbertCopies H n →L[ℂ] HilbertCopies H n =>
      S (PiLp.single 2 j x) i) h
    simpa only [mul_apply_eq_comp, amplify_apply, amplify_single,
      matrixEntryCompression_apply] using hi
  · intro h
    conv_lhs => rw [← matrixOperator_entryCompressions T]
    conv_rhs => rw [← matrixOperator_entryCompressions T]
    apply ContinuousLinearMap.ext
    intro x
    ext i
    change A ((matrixOperator (matrixOfOperator T) x) i) =
      (matrixOperator (matrixOfOperator T) (amplify A n x)) i
    simp only [matrixOperator_apply, matrixOfOperator_apply, map_sum, amplify_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun S : H →L[ℂ] H => S (x j)) (h i j)

/-- The diagonal copy of the commutant, viewed just as a set of operators. -/
def amplifiedCommutantSet (P : VonNeumannAlgebra H) (n : ℕ) :
    Set (HilbertCopies H n →L[ℂ] HilbertCopies H n) :=
  (fun T => amplify T n) '' (P.commutant : Set (H →L[ℂ] H))

/-- Finite matrices over `P`, constructed as an actual double-commutant algebra. -/
def matrixVonNeumann (P : VonNeumannAlgebra H) (n : ℕ) :
    VonNeumannAlgebra (HilbertCopies H n) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (amplifiedCommutantSet P n)
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (Set.centralizer (amplifiedCommutantSet P n ∪ star (amplifiedCommutantSet P n)))) = _
    exact Set.centralizer_centralizer_centralizer _

/-- The extra star tests in the centralizer are redundant for this set. -/
theorem mem_matrixVonNeumann_iff_commutes (P : VonNeumannAlgebra H) {n : ℕ}
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) :
    T ∈ matrixVonNeumann P n ↔ ∀ A ∈ P.commutant, amplify A n * T = T * amplify A n := by
  change T ∈ StarSubalgebra.centralizer ℂ (amplifiedCommutantSet P n) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h A hA
    exact (h (amplify A n) ⟨A, hA, rfl⟩).1
  · intro h B hB
    obtain ⟨A, hA, rfl⟩ := hB
    refine ⟨h A hA, ?_⟩
    simpa only [ContinuousLinearMap.star_eq_adjoint, adjoint_amplify] using h (star A) (star_mem hA)

/-- Membership is exactly entrywise membership in the original algebra. -/
theorem mem_matrixVonNeumann_iff_entries (P : VonNeumannAlgebra H) {n : ℕ}
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) :
    T ∈ matrixVonNeumann P n ↔ ∀ i j, matrixEntryCompression i j T ∈ P := by
  rw [mem_matrixVonNeumann_iff_commutes]
  simp only [amplify_commutes_iff_entries]
  constructor
  · intro h i j
    rw [← P.commutant_commutant]
    exact VonNeumannAlgebra.mem_commutant_iff.mpr (fun A hA => h A hA i j)
  · intro h A hA i j
    exact VonNeumannAlgebra.mem_commutant_iff.mp
      (show matrixEntryCompression i j T ∈ P.commutant.commutant by
        rw [P.commutant_commutant]
        exact h i j) A hA

/-- The usual matrix-operator action has exactly the same entrywise criterion. -/
theorem matrixOperator_mem_matrixVonNeumann_iff (P : VonNeumannAlgebra H) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    matrixOperator X ∈ matrixVonNeumann P n ↔ ∀ i j, X i j ∈ P := by
  rw [mem_matrixVonNeumann_iff_entries]
  simp only [matrixEntryCompression_matrixOperator]

section Represented
variable {A : Type*} [CStarAlgebra A]

/-- Scalar matrix units act as the coordinate matrix units. -/
theorem representedMatrixHom_single_one (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {n : ℕ} (i j : Fin n) :
    representedMatrixHom σ n (CStarMatrix.ofMatrix (Matrix.single i j (1 : A))) =
      copyMatrixUnit i j := by
  ext x k
  change (matrixOperator (Matrix.of (fun k l => σ ((CStarMatrix.ofMatrix
    (Matrix.single i j (1 : A))) k l))) x) k = (PiLp.single 2 i (x j) : HilbertCopies H n) k
  rw [matrixOperator_apply]
  by_cases hki : k = i
  · subst k
    rw [Finset.sum_eq_single j]
    · simp [Matrix.single_apply]
    · intro l _ hlj
      simp [Matrix.single_apply, Ne.symm hlj]
    · simp
  · simp [Matrix.single_apply, hki, Ne.symm hki, apply_ite]

/-- Constant diagonal matrices represent the diagonal amplification. -/
theorem representedMatrixHom_diagonal (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (n : ℕ) (a : A) :
    representedMatrixHom σ n (CStarMatrix.ofMatrix (Matrix.diagonal (fun _ : Fin n => a))) =
      amplify (σ a) n := by
  ext x i
  change (matrixOperator (Matrix.of (fun k l => σ ((CStarMatrix.ofMatrix
    (Matrix.diagonal (fun _ : Fin n => a))) k l))) x) i = (σ a) (x i)
  rw [matrixOperator_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Matrix.diagonal_apply, Ne.symm hji]
  · simp

/-- A matrix commutant element has one repeated diagonal block, which
commutes with the original represented algebra. -/
theorem matrixRange_commutant_is_diagonal
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ} [NeZero n]
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n)
    (hT : T ∈ Set.centralizer ((representedMatrixHom σ n).range :
      Set (HilbertCopies H n →L[ℂ] HilbertCopies H n))) :
    ∃ B : H →L[ℂ] H, T = amplify B n ∧
      B ∈ Set.centralizer (σ.range : Set (H →L[ℂ] H)) := by
  let i : Fin n := 0
  let B := copyCorner i T
  have hTi (j : Fin n) : T.comp (copyMatrixUnit i j) = (copyMatrixUnit i j).comp T := by
    have h := hT
      (representedMatrixHom σ n (CStarMatrix.ofMatrix (Matrix.single i j (1 : A))))
      ⟨_, rfl⟩
    rw [representedMatrixHom_single_one] at h
    exact h.symm
  have hdiag : T = amplify B n := eq_mapCopies_of_matrixUnit_intertwining i T hTi
  refine ⟨B, hdiag, ?_⟩
  rintro C ⟨a, rfl⟩
  have h := hT
    (representedMatrixHom σ n (CStarMatrix.ofMatrix (Matrix.diagonal (fun _ : Fin n => a))))
    ⟨_, rfl⟩
  rw [representedMatrixHom_diagonal] at h
  exact (amplify_commutes_iff_entries (σ a) T).mp h i i

/-- Every amplified scalar commutant element commutes with the represented
matrix algebra. -/
theorem amplify_mem_matrixRange_commutant
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) (B : H →L[ℂ] H)
    (hB : B ∈ Set.centralizer (σ.range : Set (H →L[ℂ] H))) :
    amplify B n ∈ Set.centralizer ((representedMatrixHom σ n).range :
      Set (HilbertCopies H n →L[ℂ] HilbertCopies H n)) := by
  rintro T ⟨X, rfl⟩
  apply Eq.symm
  apply (amplify_commutes_iff_entries B (representedMatrixHom σ n X)).mpr
  intro i j
  have he : matrixEntryCompression i j (representedMatrixHom σ n X) = σ (X i j) :=
    matrixEntryCompression_matrixOperator (Matrix.of (fun k l => σ (X k l))) i j
  rw [he]
  exact (hB (σ (X i j)) ⟨_, rfl⟩).symm

variable [PartialOrder A] [StarOrderedRing A]

/-- Finite matrices commute with passage to the represented bicommutant.
This supplies the actual matrix membership needed by Kaplansky density. -/
theorem representationVonNeumannAlgebra_matrix (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (n : ℕ) [NeZero n] :
    representationVonNeumannAlgebra (representedMatrixHom σ n) =
      matrixVonNeumann (representationVonNeumannAlgebra σ) n := by
  apply VonNeumannAlgebra.ext
  intro T
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra]
  constructor
  · intro hT
    apply (mem_matrixVonNeumann_iff_commutes _ T).mpr
    intro B hB
    exact hT (amplify B n) (amplify_mem_matrixRange_commutant σ n B
      ((mem_representation_commutant_iff σ B).mp hB))
  · intro hT S hS
    obtain ⟨B, rfl, hB⟩ := matrixRange_commutant_is_diagonal σ S hS
    exact (mem_matrixVonNeumann_iff_commutes _ T).mp hT B
      ((mem_representation_commutant_iff σ B).mpr hB)

/-- Entrywise bicommutant membership for an arbitrary represented algebra. -/
theorem matrixOperator_mem_representationVonNeumannAlgebra_iff
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    matrixOperator X ∈ representationVonNeumannAlgebra (representedMatrixHom σ n) ↔
      ∀ i j, X i j ∈ representationVonNeumannAlgebra σ := by
  rw [representationVonNeumannAlgebra_matrix, matrixOperator_mem_matrixVonNeumann_iff]


end Represented

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCreationCoordinates
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary reduced-word creation in the actual tracial base spaces.
The normalized symmetry and corner Haar vectors are constructed, so the
only word-model inputs are isometric tensor inclusions and their elementary
multiplication and range formulas. -/

noncomputable section
namespace KadisonSimilarity

/-- Elementary multiplication on two opposite reduced-word subspaces.
This record carries no normalization or complete-prefix assumption. -/
structure ElementaryCreationFormulas {EA ED H : Type*}
    [NormedAddCommGroup EA] [InnerProductSpace ℂ EA]
    [NormedAddCommGroup ED] [InnerProductSpace ℂ ED]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : H →L[ℂ] H) (X : ℕ → H →L[ℂ] H) (s : EA) (x : ℕ → ED)
    (DLead ALead : Submodule ℂ H) where
  createA : HilbertTensor EA DLead →ₗᵢ[ℂ] H
  createD : HilbertTensor ED ALead →ₗᵢ[ℂ] H
  createA_mem : ∀ w, createA w ∈ ALead
  createD_mem : ∀ w, createD w ∈ DLead
  actionA : ∀ y : DLead, S y = createA (hilbertTensorInsert s y)
  actionD : ∀ n (y : ALead), X n y = createD (hilbertTensorInsert (x n) y)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductMatrixExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise two-factor matrix-automorphism extension input. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

/-- The two-factor specialization of Blanchard--Dykema, *Embeddings of reduced
free products of operator algebras*, Pacific J. Math. 199 (2001), 1--19,
Theorem 3.7 (arXiv:math/9911012, p. 13). Applied to a tracial reduced free
product, the identity embedding on the base factor and matrix conjugation on
the other factor extend to a trace-preserving normal star homomorphism.

Only the algebraic extension and trace preservation are recorded here; no
unitary implementation, completed-word covariance, or operator estimate is
included. Normality is not needed for the L² construction. -/
def MatrixConjugationExtensionInput (A : StarSubalgebra ℂ P) : Prop :=
  ∀ v : Matrix.unitaryGroup α ℂ, ∃ Φ : P →⋆ₐ[ℂ] P,
    (∀ x, G.trace (Φ x) = G.trace x) ∧
    (∀ a : A, Φ (a : P) = (a : P)) ∧
    (∀ d : D, Φ (d : P) = (matrixConjugateLetter D ι v d : P))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductAutomorphisms
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixConjugateLetter_one_letter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixConjugateLetter_product _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixConjugateLetter_smul _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixConjugateLetter_sub _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixConjugationAut_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic extensions become actual automorphisms by tracial L² density.
The only extension input is the two-factor published embedding specialization. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

include G in
/-- A trace-preserving homomorphism is isometric on the tracial algebra vectors. -/
theorem hom_vector_norm (Φ : P →⋆ₐ[ℂ] P)
    (hΦ : ∀ a, G.trace (Φ a) = G.trace a) (a : P) :
    ‖G.vector (Φ a)‖ = ‖G.vector a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    G.inner_vector, G.inner_vector, ← map_star Φ, ← map_mul Φ, hΦ]

/-- The actual L² isometry of a trace-preserving ambient homomorphism. -/
def homIsometry (Φ : P →⋆ₐ[ℂ] P) (hΦ : ∀ a, G.trace (Φ a) = G.trace a) :
    H →ₗᵢ[ℂ] H :=
  (G.vector.comp Φ.toAlgHom.toLinearMap).extendOfIsometry G.dense_vector
    (G.hom_vector_norm Φ hΦ)

@[simp] theorem homIsometry_vector (Φ : P →⋆ₐ[ℂ] P)
    (hΦ : ∀ a, G.trace (Φ a) = G.trace a) (a : P) :
    G.homIsometry Φ hΦ (G.vector a) = G.vector (Φ a) :=
  LinearMap.extendOfIsometry_eq _ G.dense_vector (G.hom_vector_norm Φ hΦ) a

/-- Trace preservation turns tracial generation into uniqueness of ambient
extensions of the two factor maps. -/
theorem hom_eq_of_factor_eq (A D : StarSubalgebra ℂ P)
    (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
    (Φ Ψ : P →⋆ₐ[ℂ] P)
    (hΦ : ∀ a, G.trace (Φ a) = G.trace a)
    (hΨ : ∀ a, G.trace (Ψ a) = G.trace a)
    (hA : ∀ a : A, Φ (a : P) = Ψ (a : P))
    (hD : ∀ d : D, Φ (d : P) = Ψ (d : P)) : Φ = Ψ := by
  have hS : factorAlgebra A D ≤ StarAlgHom.equalizer Φ Ψ := by
    apply StarAlgebra.adjoin_le
    intro x hx
    rcases hx with hx | hx
    · exact hA ⟨x, hx⟩
    · exact hD ⟨x, hx⟩
  have heq (x : H) : G.homIsometry Φ hΦ x = G.homIsometry Ψ hΨ x := by
    refine hgen.induction_on x
      (isClosed_eq (G.homIsometry Φ hΦ).continuous (G.homIsometry Ψ hΨ).continuous) ?_
    intro a
    change G.homIsometry Φ hΦ (G.vector (a : P)) =
      G.homIsometry Ψ hΨ (G.vector (a : P))
    rw [G.homIsometry_vector, G.homIsometry_vector]
    exact congrArg G.vector (hS a.property)
  ext a
  apply hfaithful
  simpa only [G.homIsometry_vector] using heq (G.vector a)

variable (A D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D)
  (hgen : G.FactorsTraciallyGenerate A D)
  (hfaithful : Function.Injective G.vector)
  (hext : G.MatrixConjugationExtensionInput D ι A)

/-- A choice of the published algebraic extension, with no unitary or tensor
conclusion included in that input. -/
def chosenMatrixExtension (u : Matrix.unitaryGroup α ℂ) : P →⋆ₐ[ℂ] P :=
  Classical.choose (hext u)

theorem chosenMatrixExtension_trace (u : Matrix.unitaryGroup α ℂ) (a : P) :
    G.trace (G.chosenMatrixExtension A D ι hext u a) = G.trace a :=
  (Classical.choose_spec (hext u)).1 a

theorem chosenMatrixExtension_base (u : Matrix.unitaryGroup α ℂ) (a : A) :
    G.chosenMatrixExtension A D ι hext u (a : P) = (a : P) :=
  (Classical.choose_spec (hext u)).2.1 a

theorem chosenMatrixExtension_other (u : Matrix.unitaryGroup α ℂ) (d : D) :
    G.chosenMatrixExtension A D ι hext u (d : P) =
      (matrixConjugateLetter D ι u d : P) :=
  (Classical.choose_spec (hext u)).2.2 d

include hgen hfaithful in
/-- The inverse factor conjugations give inverse ambient homomorphisms by
tracial generation; no ambient automorphism existence is assumed. -/
theorem chosenMatrixExtension_inv_comp (u : Matrix.unitaryGroup α ℂ) :
    (G.chosenMatrixExtension A D ι hext u⁻¹).comp
      (G.chosenMatrixExtension A D ι hext u) = StarAlgHom.id ℂ P := by
  apply G.hom_eq_of_factor_eq A D hgen hfaithful
  · intro a
    exact (G.chosenMatrixExtension_trace A D ι hext u⁻¹ _).trans
      (G.chosenMatrixExtension_trace A D ι hext u a)
  · intro a
    rfl
  · intro a
    simp only [StarAlgHom.comp_apply, G.chosenMatrixExtension_base, StarAlgHom.coe_id, id_eq]
  · intro d
    simp only [StarAlgHom.comp_apply, G.chosenMatrixExtension_other,
      matrixConjugateLetter_inv, StarAlgHom.coe_id, id_eq]

/-- The actual ambient automorphism is derived from the two inverse published
factor embeddings. -/
def matrixExtensionAutomorphism (u : Matrix.unitaryGroup α ℂ) : P ≃⋆ₐ[ℂ] P :=
  StarAlgEquiv.ofStarAlgHom
    (G.chosenMatrixExtension A D ι hext u)
    (G.chosenMatrixExtension A D ι hext u⁻¹)
    (G.chosenMatrixExtension_inv_comp A D ι hgen hfaithful hext u)
    (by simpa only [inv_inv] using
      G.chosenMatrixExtension_inv_comp A D ι hgen hfaithful hext u⁻¹)

@[simp] theorem matrixExtensionAutomorphism_apply (u : Matrix.unitaryGroup α ℂ) (a : P) :
    G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u a =
      G.chosenMatrixExtension A D ι hext u a := rfl

@[simp] theorem matrixExtensionAutomorphism_trace (u : Matrix.unitaryGroup α ℂ) (a : P) :
    G.trace (G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u a) = G.trace a :=
  G.chosenMatrixExtension_trace A D ι hext u a

@[simp] theorem matrixExtensionAutomorphism_base (u : Matrix.unitaryGroup α ℂ) (a : A) :
    G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u (a : P) = (a : P) :=
  G.chosenMatrixExtension_base A D ι hext u a

@[simp] theorem matrixExtensionAutomorphism_other (u : Matrix.unitaryGroup α ℂ) (d : D) :
    G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u (d : P) =
      (matrixConjugateLetter D ι u d : P) :=
  G.chosenMatrixExtension_other A D ι hext u d

include hgen hfaithful in
theorem chosenMatrixExtension_one :
    G.chosenMatrixExtension A D ι hext 1 = StarAlgHom.id ℂ P := by
  apply G.hom_eq_of_factor_eq A D hgen hfaithful
  · exact G.chosenMatrixExtension_trace A D ι hext 1
  · intro a; rfl
  · intro a
    exact G.chosenMatrixExtension_base A D ι hext 1 a
  · intro d
    simpa only [matrixConjugateLetter_one, StarAlgHom.coe_id, id_eq] using
      G.chosenMatrixExtension_other A D ι hext 1 d

include hgen hfaithful in
theorem chosenMatrixExtension_mul (u v : Matrix.unitaryGroup α ℂ) :
    G.chosenMatrixExtension A D ι hext (u * v) =
      (G.chosenMatrixExtension A D ι hext u).comp
        (G.chosenMatrixExtension A D ι hext v) := by
  apply G.hom_eq_of_factor_eq A D hgen hfaithful
  · exact G.chosenMatrixExtension_trace A D ι hext (u * v)
  · intro a
    exact (G.chosenMatrixExtension_trace A D ι hext u _).trans
      (G.chosenMatrixExtension_trace A D ι hext v a)
  · intro a
    simp only [StarAlgHom.comp_apply, G.chosenMatrixExtension_base]
  · intro d
    simp only [StarAlgHom.comp_apply, G.chosenMatrixExtension_other,
      matrixConjugateLetter_mul]

/-- The ambient extensions form a genuine group action, by uniqueness on the
tracially dense generated algebra. -/
def matrixExtensionAction : Matrix.unitaryGroup α ℂ →* (P ≃⋆ₐ[ℂ] P) where
  toFun u := G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u
  map_one' := by
    apply DFunLike.ext
    intro a
    change G.chosenMatrixExtension A D ι hext 1 a = a
    exact congrArg (fun Φ : P →⋆ₐ[ℂ] P => Φ a)
      (G.chosenMatrixExtension_one A D ι hgen hfaithful hext)
  map_mul' u v := by
    apply DFunLike.ext
    intro a
    change G.chosenMatrixExtension A D ι hext (u * v) a =
      G.chosenMatrixExtension A D ι hext u (G.chosenMatrixExtension A D ι hext v a)
    exact congrArg (fun Φ : P →⋆ₐ[ℂ] P => Φ a)
      (G.chosenMatrixExtension_mul A D ι hgen hfaithful hext u v)

/-- The actual Hilbert-space unitary representation induced by the derived
free-product automorphisms. -/
def matrixExtensionUnitaryRepresentation :
    Matrix.unitaryGroup α ℂ →* unitary (H →L[ℂ] H) :=
  G.automorphismRepresentation (G.matrixExtensionAction A D ι hgen hfaithful hext)
    (fun u a => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u a)

@[simp] theorem matrixExtensionUnitaryRepresentation_vector
    (u : Matrix.unitaryGroup α ℂ) (a : P) :
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
        (G.vector a) =
      G.vector (G.chosenMatrixExtension A D ι hext u a) := by
  exact G.automorphismRepresentation_vector
    (G.matrixExtensionAction A D ι hgen hfaithful hext)
    (fun u a => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u a) u a

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_GeneratedWordDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary algebraic generation implies density of centered reduced words.
This is an algebraic centering argument, independent of freeness. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

open scoped Pointwise
open TracialCornerGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

theorem vector_mem_reducedWordSpan {x : P}
    (hx : x ∈ CenteredWordSpan.span G.trace A D) :
    G.vector x ∈ Submodule.span ℂ (reducedWordVectors G A D) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, d, b, a, c, ha, hc, rfl⟩ := hx
    exact Submodule.subset_span ⟨n, d, b, a, c, ha, hc, rfl⟩
  | zero => simpa only [map_zero] using (Submodule.span ℂ (reducedWordVectors G A D)).zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul r a _ ha => simpa only [map_smul] using Submodule.smul_mem _ r ha

/-- No additional density assumption on centered normal forms is needed once
the two ordinary factor algebras generate the tracial Hilbert space. -/
theorem reducedWordGenerated_of_factorsTraciallyGenerate (hτ : G.trace 1 = 1)
    (hgen : G.FactorsTraciallyGenerate A D) : ReducedWordGenerated G A D := by
  apply top_unique
  intro x _
  exact hgen.induction_on x (Submodule.isClosed_topologicalClosure _) (fun a =>
    Submodule.le_topologicalClosure _ (G.vector_mem_reducedWordSpan A D
      (CenteredWordSpan.generated_mem G.trace A D hτ a.property)))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSmallColumn
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small vectors in propagation are actual left compressions of the
completed base space. Scalar freeness gives their exact norm, first on
algebra vectors and then throughout the completion by density. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The actual small-column map is left multiplication by the projection,
restricted to the completed base Hilbert space. -/
def tracialSmallColumn (q : P) : G.baseSpace A →L[ℂ] H :=
  (G.left q).comp (G.baseInclusion A).toContinuousLinearMap

@[simp] theorem tracialSmallColumn_apply (q : P) (v : G.baseSpace A) :
    G.tracialSmallColumn A q v = G.left q (v : H) := rfl

@[simp] theorem tracialSmallColumn_vector (q : P) (b : A) :
    G.tracialSmallColumn A q (G.baseVector A b) = G.vector (q * (b : P)) :=
  G.left_vector q (b : P)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GNSTracialGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAlgebraVectors_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_adjoint _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tracial GNS representation supplies the Hilbert geometry
used in the free-corner argument. Trace-preserving homomorphisms induce
isometric embeddings which intertwine the concrete left actions. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The concrete tracial geometry is obtained directly from the GNS
construction, rather than assumed as separate representation data. -/
def gnsTracialGeometry (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) : TracialCornerGeometry A τ.GNS where
  trace := τ.toLinearMap
  vector := gnsTracialVector τ
  left := τ.gnsStarAlgHom
  inner_vector := gnsTracialVector_inner τ
  tracial := htr
  dense_vector := gnsTracialVector_dense τ
  left_vector := gnsTracialVector_left τ

@[simp] theorem gnsTracialGeometry_trace (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (a : A) :
    (gnsTracialGeometry τ htr).trace a = τ a := rfl

@[simp] theorem gnsTracialGeometry_vector (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (a : A) :
    (gnsTracialGeometry τ htr).vector a = gnsTracialVector τ a := rfl

@[simp] theorem gnsTracialGeometry_left (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (a : A) :
    (gnsTracialGeometry τ htr).left a = τ.gnsStarAlgHom a := rfl

theorem gnsTracialVector_injective (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0) :
    Function.Injective (gnsTracialVector τ) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hf
  rw [← gnsTracialVector_inner τ, map_sub, hab, sub_self, inner_zero_left]

section Hom

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] B)
  (hφ : ∀ a : A, τB (φ a) = τA a)

include hφ in
theorem gnsTracialHom_norm (a : A) :
    ‖gnsTracialVector τB (φ a)‖ = ‖gnsTracialVector τA a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    gnsTracialVector_inner, gnsTracialVector_inner, ← map_star φ, ← map_mul φ, hφ]

/-- The GNS isometry induced by a trace-preserving star homomorphism. -/
def gnsTracialHomIsometry : τA.GNS →ₗᵢ[ℂ] τB.GNS :=
  ((gnsTracialVector τB).comp φ.toAlgHom.toLinearMap).extendOfIsometry
    (gnsTracialVector_dense τA) (gnsTracialHom_norm τA τB φ hφ)

@[simp] theorem gnsTracialHomIsometry_vector (a : A) :
    gnsTracialHomIsometry τA τB φ hφ (gnsTracialVector τA a) =
      gnsTracialVector τB (φ a) :=
  LinearMap.extendOfIsometry_eq _ (gnsTracialVector_dense τA)
    (gnsTracialHom_norm τA τB φ hφ) a

end Hom

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialEmbeddingTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace-preserving embedding transports the completed tracial space,
the dense matrix tower, and its real orthonormal sequence to its actual
range. No normal-form or matrix-density assumption is added at the target. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {R P H : Type*} [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder R] [StarOrderedRing R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : R →ₚ[ℂ] ℂ) (G : TracialCornerGeometry P H)
  (φ : R →⋆ₐ[ℂ] P) (hφ : ∀ a, G.trace (φ a) = τ a)

include hφ in
theorem tracialRangeVector_norm (a : R) :
    ‖G.baseVector φ.range (φ.rangeRestrict a)‖ = ‖gnsTracialVector τ a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    G.baseVector_inner, gnsTracialVector_inner]
  change (G.trace (star (φ a) * φ a)).re = (τ (star a * a)).re
  rw [← map_star, ← map_mul, hφ]

/-- The completed trace-preserving map lands in the actual closed range space. -/
def tracialRangeIsometry : τ.GNS →ₗᵢ[ℂ] G.baseSpace φ.range :=
  ((G.baseVector φ.range).comp φ.rangeRestrict.toLinearMap).extendOfIsometry
    (gnsTracialVector_dense τ) (tracialRangeVector_norm τ G φ hφ)

@[simp] theorem tracialRangeIsometry_vector (a : R) :
    tracialRangeIsometry τ G φ hφ (gnsTracialVector τ a) =
      G.baseVector φ.range (φ.rangeRestrict a) :=
  LinearMap.extendOfIsometry_eq _ (gnsTracialVector_dense τ)
    (tracialRangeVector_norm τ G φ hφ) a

theorem tracialRangeIsometry_surjective :
    Function.Surjective (tracialRangeIsometry τ G φ hφ) := by
  intro x
  have hc : IsClosed (Set.range (tracialRangeIsometry τ G φ hφ)) :=
    (tracialRangeIsometry τ G φ hφ).isometry.isClosedEmbedding.isClosed_range
  change x ∈ Set.range (tracialRangeIsometry τ G φ hφ)
  refine (G.baseVector_dense φ.range).induction_on x hc ?_
  rintro ⟨a, b, rfl⟩
  exact ⟨gnsTracialVector τ b, tracialRangeIsometry_vector τ G φ hφ b⟩

variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
  [∀ n, Nonempty (I n)]

/-- A concrete matrix tower stays dense after a trace-preserving embedding. -/
def transportTracialMatrices
    (M : NestedTracialMatrices (A := I) τ.toLinearMap (gnsTracialVector τ)) :
    NestedTracialMatrices (A := I)
      (G.trace.comp φ.range.subtype.toLinearMap) (G.baseVector φ.range) where
  embedding n := φ.rangeRestrict.comp (M.embedding n)
  trace_embedding n a := by
    change G.trace (φ (M.embedding n a)) = _
    rw [hφ]
    exact M.trace_embedding n a
  inclusion := M.inclusion
  compatible n m h a := by
    change φ.rangeRestrict (M.embedding m (M.inclusion n m h a)) = _
    rw [M.compatible]
    rfl
  dense := by
    have hd := (tracialRangeIsometry_surjective τ G φ hφ).denseRange.dense_image
      (tracialRangeIsometry τ G φ hφ).continuous M.dense
    apply hd.mono
    rintro _ ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp hx with ⟨n, a, rfl⟩
    exact Set.mem_iUnion.mpr
      ⟨n, a, (tracialRangeIsometry_vector τ G φ hφ (M.embedding n a)).symm⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSubalgebraModels
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal algebra generated inside the ultrapower is represented on
its own tracial GNS space. Restriction of the positive trace and its exact
Hilbert-space identification require no further analytic input. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]

/-- The inclusion of the generated algebra induces its concrete GNS inclusion. -/
def restrictedTracialGNSInclusion :
    (restrictedPositiveTrace τ L).GNS →ₗᵢ[ℂ] τ.GNS :=
  gnsTracialHomIsometry (restrictedPositiveTrace τ L) τ L.subtype (fun _ => rfl)

@[simp] theorem restrictedTracialGNSInclusion_vector (a : L) :
    restrictedTracialGNSInclusion τ L (gnsTracialVector (restrictedPositiveTrace τ L) a) =
      gnsTracialVector τ (a : P) :=
  gnsTracialHomIsometry_vector (restrictedPositiveTrace τ L) τ L.subtype (fun _ => rfl) a

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GeneratedGNSModels
attribute [-instance] _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The algebra generated inside a tracial ambient algebra has its own
canonical GNS model. Ambient algebra-vector density gives native factor
generation, and scalar freeness and faithful vectors restrict directly. -/

noncomputable section
namespace KadisonSimilarity

open TracialCornerGeometry
open scoped ComplexOrder

variable {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (A D L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]

/-- Faithfulness of the ambient trace makes the native generated-algebra
GNS vectors injective. -/
theorem restrictedGNS_vector_injective
    (hf : ∀ a : P, τ (star a * a) = 0 → a = 0) :
    Function.Injective
      (gnsTracialGeometry (restrictedPositiveTrace τ L)
        (restrictedPositiveTrace_tracial τ L htr)).vector :=
  gnsTracialVector_injective (restrictedPositiveTrace τ L)
    (restrictedPositiveTrace_faithful τ L hf)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialL2Closure
attribute [-instance] _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded elements in the L² closure of a star subalgebra form an
actual norm-closed star subalgebra. Multiplication is obtained from the
commuting left and right tracial actions, rather than assumed as a property
of a proposed generated algebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

open scoped CStarAlgebra ComplexOrder

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- The algebra-vector map is norm continuous because it is the left
representation evaluated at the identity vector. -/
theorem vector_continuous : Continuous G.vector := by
  have he : G.vector = fun a => G.left a (G.vector 1) := by
    funext a
    rw [G.left_vector, mul_one]
  rw [he]
  exact (map_continuous G.left).clm_apply continuous_const

section ClosedSeed

variable (S : StarSubalgebra ℂ P) [hSclosed : IsClosed (S : Set P)]

/-- An element whose vector lies in the closed subspace preserves that
subspace under left multiplication, by right multiplication on dense
algebra vectors. -/
theorem left_preserves_baseSpace_of_vector_mem {x : P}
    (hx : G.vector x ∈ G.baseSpace S) (y : H) (hy : y ∈ G.baseSpace S) :
    G.left x y ∈ G.baseSpace S := by
  have h (z : G.baseSpace S) : G.left x (z : H) ∈ G.baseSpace S := by
    refine (G.baseVector_dense S).induction_on z
      ((G.baseSpace S).isClosed.preimage
        ((G.left x).continuous.comp continuous_subtype_val)) ?_
    intro a
    change G.left x (G.vector (a : P)) ∈ G.baseSpace S
    rw [G.left_vector, ← G.right_vector]
    exact G.baseSpace_right_invariant S a (G.vector x) hx
  exact h ⟨y, hy⟩

/-- The same closed subspace is preserved by tracial conjugation. -/
theorem conjugation_preserves_baseSpace (y : H) (hy : y ∈ G.baseSpace S) :
    G.conjugation y ∈ G.baseSpace S := by
  rw [← G.baseGeometry_conjugation_coe S (⟨y, hy⟩ : G.baseSpace S)]
  exact ((G.baseGeometry S).conjugation (⟨y, hy⟩ : G.baseSpace S)).property

/-- The actual bounded algebra lying in the L² closure of `S`. -/
def l2ClosureAlgebra : StarSubalgebra ℂ P where
  carrier := {x | G.vector x ∈ G.baseSpace S}
  zero_mem' := by
    change G.vector 0 ∈ (G.baseSpace S).toSubmodule
    rw [map_zero]
    exact (G.baseSpace S).toSubmodule.zero_mem
  add_mem' {x y} hx hy := by
    change G.vector (x + y) ∈ (G.baseSpace S).toSubmodule
    rw [map_add]
    exact (G.baseSpace S).toSubmodule.add_mem hx hy
  one_mem' := (G.baseVector S 1).property
  mul_mem' {x y} hx hy := by
    change G.vector (x * y) ∈ G.baseSpace S
    rw [← G.left_vector]
    exact G.left_preserves_baseSpace_of_vector_mem S hx (G.vector y) hy
  algebraMap_mem' c := by
    change G.vector (algebraMap ℂ P c) ∈ G.baseSpace S
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    exact (G.baseSpace S).smul_mem c (G.baseVector S 1).property
  star_mem' {x} hx := by
    change G.vector (star x) ∈ G.baseSpace S
    rw [← G.conjugation_vector]
    exact G.conjugation_preserves_baseSpace S (G.vector x) hx

include hSclosed in
@[simp] theorem mem_l2ClosureAlgebra (x : P) :
    x ∈ G.l2ClosureAlgebra S ↔ G.vector x ∈ G.baseSpace S := Iff.rfl

instance l2ClosureAlgebra_isClosed : IsClosed (G.l2ClosureAlgebra S : Set P) :=
  (G.baseSpace S).isClosed.preimage G.vector_continuous

include hSclosed in
/-- Every original algebra element lies in the constructed bounded closure. -/
theorem le_l2ClosureAlgebra : S ≤ G.l2ClosureAlgebra S := by
  intro x hx
  exact (G.baseVector S ⟨x, hx⟩).property

end ClosedSeed

/-- The bounded L²-generated algebra of an arbitrary star subalgebra,
constructed by first taking its norm closure. -/
def l2GeneratedAlgebra (S : StarSubalgebra ℂ P) : StarSubalgebra ℂ P := by
  have : IsClosed (S.topologicalClosure : Set P) := S.isClosed_topologicalClosure
  exact G.l2ClosureAlgebra S.topologicalClosure

instance l2GeneratedAlgebra_isClosed (S : StarSubalgebra ℂ P) :
    IsClosed (G.l2GeneratedAlgebra S : Set P) := by
  unfold l2GeneratedAlgebra
  infer_instance

/-- The original seed algebra is contained in its constructed L²-generated
algebra. -/
theorem le_l2GeneratedAlgebra (S : StarSubalgebra ℂ P) : S ≤ G.l2GeneratedAlgebra S := by
  have : IsClosed (S.topologicalClosure : Set P) := S.isClosed_topologicalClosure
  exact S.le_topologicalClosure.trans (G.le_l2ClosureAlgebra S.topologicalClosure)

/-- The concrete bounded algebra generated in L² by two prescribed factors. -/
def l2FactorAlgebra (A D : StarSubalgebra ℂ P) : StarSubalgebra ℂ P :=
  G.l2GeneratedAlgebra (factorAlgebra A D)

instance l2FactorAlgebra_isClosed (A D : StarSubalgebra ℂ P) :
    IsClosed (G.l2FactorAlgebra A D : Set P) :=
  G.l2GeneratedAlgebra_isClosed (factorAlgebra A D)

theorem left_le_l2FactorAlgebra (A D : StarSubalgebra ℂ P) : A ≤ G.l2FactorAlgebra A D := by
  intro a ha
  apply G.le_l2GeneratedAlgebra (factorAlgebra A D)
  exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ha)

theorem right_le_l2FactorAlgebra (A D : StarSubalgebra ℂ P) : D ≤ G.l2FactorAlgebra A D := by
  intro a ha
  apply G.le_l2GeneratedAlgebra (factorAlgebra A D)
  exact StarAlgebra.subset_adjoin ℂ _ (Or.inr ha)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixUnitFamilies
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite partial-isometry frames constructed from an actual unital matrix
star homomorphism. No frame-existence assumption is used. -/

noncomputable section
namespace KadisonSimilarity

variable {P α : Type*} [CStarAlgebra P] [Fintype α] [DecidableEq α]

section NestedMatrices

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  {τ : P →ₗ[ℂ] ℂ} {V : P →ₗ[ℂ] E}

/-- A nonempty stage gives the finite amplification frame without any
additional existence hypothesis. -/
def NestedTracialMatrices.nonemptyFinColumnFamily [∀ s, Nonempty (A s)]
    (M : NestedTracialMatrices (A := A) τ V) (s : ℕ) :
    TracialMatrixUnitColumnFamily τ (Fin (Fintype.card (A s))) :=
  M.finColumnFamily s (Classical.choice (inferInstance : Nonempty (A s)))

end NestedMatrices

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeMatrixConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix conjugation on the dense free-word family. Its scalar Gram
matrix is unchanged, so it extends to the actual tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

attribute [local irreducible] baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

def freeWordFamily (p : Σ n, TracialWordParameter G A D n) : H :=
  tracialAlgebraFamily G A D p.1 p.2

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem freeWordFamily_total (hgen : ReducedWordGenerated G A D) :
    (Submodule.span ℂ (Set.range (G.freeWordFamily A D))).topologicalClosure = ⊤ := by
  have heq : Set.range (G.freeWordFamily A D) = reducedWordVectors G A D := by
    ext x
    constructor
    · rintro ⟨⟨n, p⟩, rfl⟩
      exact ⟨n, p.2.1, p.1.2, (fun i => (p.1.1 i).1), (fun i => (p.2.2 i).1),
        (fun i => (p.1.1 i).2), (fun i => (p.2.2 i).2), rfl⟩
    · rintro ⟨n, d, b, a, c, ha, hc, rfl⟩
      exact ⟨⟨n, (((fun i => ⟨a i, ha i⟩), b), (d, fun i => ⟨c i, hc i⟩))⟩, rfl⟩
  rw [heq]
  exact hgen

def freeConjugatedParameter {n : ℕ} (p : TracialWordParameter G A D n) :
    TracialWordParameter G A D n :=
  (p.1, (matrixConjugateLetter D ι u p.2.1,
    fun i => ⟨matrixConjugateLetter D ι u (p.2.2 i).1,
      (G.trace_matrixConjugateLetter D ι u (p.2.2 i).1).trans (p.2.2 i).2⟩))

def freeConjugatedFamily (p : Σ n, TracialWordParameter G A D n) : H :=
  G.freeWordFamily A D ⟨p.1, G.freeConjugatedParameter A D ι u p.2⟩

theorem inner_freeWord_same (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (n : ℕ) (p q : TracialWordParameter G A D n) :
    inner ℂ (G.freeWordFamily A D ⟨n, p⟩) (G.freeWordFamily A D ⟨n, q⟩) =
      G.trace (star (p.2.1 : P) * q.2.1) * G.trace (star (p.1.2 : P) * q.1.2) *
        ((∏ i, G.trace (star ((p.1.1 i).1 : P) * (q.1.1 i).1)) *
          ∏ i, G.trace (star ((p.2.2 i).1 : P) * (q.2.2 i).1)) := by
  change inner ℂ (tracialAlgebraFamily G A D n p) (tracialAlgebraFamily G A D n q) = _
  rw [tracialFamilyGram G A D hτ hf n p q]
  exact inner_tracialWordTensor G A D n p.2.1 q.2.1 p.1.2 q.1.2
    (fun i => (p.1.1 i).1) (fun i => (q.1.1 i).1)
    (fun i => (p.2.2 i).1) (fun i => (q.2.2 i).1)
    (fun i => (p.1.1 i).2) (fun i => (q.1.1 i).2)
    (fun i => (p.2.2 i).2) (fun i => (q.2.2 i).2)

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem inner_freeWord_different (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (n m : ℕ) (hnm : n ≠ m)
    (p : TracialWordParameter G A D n) (q : TracialWordParameter G A D m) :
    inner ℂ (G.freeWordFamily A D ⟨n, p⟩) (G.freeWordFamily A D ⟨m, q⟩) = 0 :=
  inner_reducedWord_ne G A D hτ hf n m hnm p.2.1 q.2.1 p.1.2 q.1.2
    (fun i => (p.1.1 i).1) (fun i => (p.2.2 i).1)
    (fun i => (q.1.1 i).1) (fun i => (q.2.2 i).1)
    (fun i => (p.1.1 i).2) (fun i => (q.1.1 i).2)
    (fun i => (p.2.2 i).2) (fun i => (q.2.2 i).2)

omit [IsClosed (D : Set P)] in
theorem trace_conjugated_pair (d e : D) :
    G.trace (star (matrixConjugateLetter D ι u d : P) *
      (matrixConjugateLetter D ι u e : P)) = G.trace (star (d : P) * e) := by
  have h : matrixConjugateLetter D ι u (star d * e) =
      star (matrixConjugateLetter D ι u d) * matrixConjugateLetter D ι u e :=
    (map_mul (matrixConjugationAut D ι u) (star d) e).trans
      (congrArg (fun a : D => a * matrixConjugateLetter D ι u e)
        (map_star (matrixConjugationAut D ι u) d))
  rw [← show (matrixConjugateLetter D ι u (star d * e) : P) =
    star (matrixConjugateLetter D ι u d : P) *
      (matrixConjugateLetter D ι u e : P) from congrArg Subtype.val h]
  exact G.trace_matrixConjugateLetter D ι u (star d * e)

theorem freeConjugatedFamily_gram (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (p q : Σ n, TracialWordParameter G A D n) :
    inner ℂ (G.freeConjugatedFamily A D ι u p) (G.freeConjugatedFamily A D ι u q) =
      inner ℂ (G.freeWordFamily A D p) (G.freeWordFamily A D q) := by
  obtain ⟨n, p⟩ := p
  obtain ⟨m, q⟩ := q
  unfold freeConjugatedFamily
  by_cases hnm : n = m
  · subst m
    rw [G.inner_freeWord_same A D hτ hf, G.inner_freeWord_same A D hτ hf]
    simp only [freeConjugatedParameter, G.trace_conjugated_pair D ι u]
  · rw [G.inner_freeWord_different A D hτ hf n m hnm,
      G.inner_freeWord_different A D hτ hf n m hnm]

def freeMatrixConjugationIsometry (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D) : H →ₗᵢ[ℂ] H :=
  denseFamilyIsometry (G.freeWordFamily A D) (G.freeConjugatedFamily A D ι u)
    (G.freeWordFamily_total A D hgen) (G.freeConjugatedFamily_gram A D ι u hτ hf)

@[simp] theorem freeMatrixConjugationIsometry_family (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D)
    (p : Σ n, TracialWordParameter G A D n) :
    G.freeMatrixConjugationIsometry A D ι u hτ hf hgen (G.freeWordFamily A D p) =
      G.freeConjugatedFamily A D ι u p :=
  denseFamilyIsometry_apply _ _ _ _ p

theorem freeMatrixConjugationIsometry_word (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D)
    (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    G.freeMatrixConjugationIsometry A D ι u hτ hf hgen
      (G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
        (fun i => (c i : P)) * (b : P))) =
      G.vector ((matrixConjugateLetter D ι u d : P) *
        alternatingProduct (fun i => (a i : P))
          (fun i => (matrixConjugateLetter D ι u (c i) : P)) * (b : P)) :=
  G.freeMatrixConjugationIsometry_family A D ι u hτ hf hgen
    ⟨n, (((fun i => ⟨a i, ha i⟩), b), (d, fun i => ⟨c i, hc i⟩))⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeMatrixFactorAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free-word isometry fixes the base algebra and intertwines left
multiplication by the matrix factor. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (hgen : ReducedWordGenerated G A D)

local notation "W" => G.freeMatrixConjugationIsometry A D ι u hτ hf hgen

@[simp] theorem freeMatrixConjugationIsometry_base (a : A) :
    W (G.vector (a : P)) = G.vector (a : P) := by
  simpa only [alternatingProduct_zero, matrixConjugateLetter_one_letter,
    OneMemClass.coe_one, one_mul, mul_one] using
    G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen 0 1 a
      Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

@[simp] theorem freeMatrixConjugationIsometry_one : W (G.vector 1) = G.vector 1 :=
  G.freeMatrixConjugationIsometry_base A D ι u hτ hf hgen 1

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeMatrixConjugationUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse matrix conjugations on the actual free word Hilbert space. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

attribute [local irreducible] baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (hgen : ReducedWordGenerated G A D)

theorem freeMatrixConjugationIsometry_inverse (x : H) :
    G.freeMatrixConjugationIsometry A D ι u⁻¹ hτ hf hgen
      (G.freeMatrixConjugationIsometry A D ι u hτ hf hgen x) = x := by
  let W := G.freeMatrixConjugationIsometry A D ι u hτ hf hgen
  let V := G.freeMatrixConjugationIsometry A D ι u⁻¹ hτ hf hgen
  let F : H →L[ℂ] H := V.toContinuousLinearMap.comp W.toContinuousLinearMap -
    ContinuousLinearMap.id ℂ H
  have hF : F = 0 := continuousLinearMap_eq_zero_of_total (G.freeWordFamily A D)
    (G.freeWordFamily_total A D hgen) F (by
      rintro ⟨n, p⟩
      let a : Fin n → A := fun i => (p.1.1 i).1
      let c : Fin n → D := fun i => (p.2.2 i).1
      have ha : ∀ i, G.trace (a i : P) = 0 := fun i => (p.1.1 i).2
      have hc : ∀ i, G.trace (c i : P) = 0 := fun i => (p.2.2 i).2
      have hW := G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen
        n p.2.1 p.1.2 a c ha hc
      have hV := G.freeMatrixConjugationIsometry_word A D ι u⁻¹ hτ hf hgen
        n (matrixConjugateLetter D ι u p.2.1) p.1.2 a
        (fun i => matrixConjugateLetter D ι u (c i)) ha
        (fun i => (G.trace_matrixConjugateLetter D ι u (c i)).trans (hc i))
      have hVW := (congrArg V hW).trans hV
      simp only [matrixConjugateLetter_inv] at hVW
      change V (W (G.freeWordFamily A D ⟨n, p⟩)) - G.freeWordFamily A D ⟨n, p⟩ = 0
      exact sub_eq_zero.mpr hVW)
  have hx := congrArg (fun T : H →L[ℂ] H => T x) hF
  change V (W x) - x = 0 at hx
  exact sub_eq_zero.mp hx

def freeMatrixConjugationUnitary : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (G.freeMatrixConjugationIsometry A D ι u hτ hf hgen)
    (fun x => ⟨G.freeMatrixConjugationIsometry A D ι u⁻¹ hτ hf hgen x, by
      simpa only [inv_inv] using
        G.freeMatrixConjugationIsometry_inverse A D ι u⁻¹ hτ hf hgen x⟩)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_NormalTracialGeometry
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A tracial Hilbert geometry with faithful normal left range supplies the
concrete vector-trace model used in the discharged tracial inputs. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem trace_eq_vectorTrace (a : A) :
    vectorTrace (G.vector 1) (G.left a) = G.trace a := by
  rw [vectorTrace_apply, G.left_vector, mul_one, G.inner_vector, star_one, one_mul]

theorem norm_identityVector (h1 : G.trace 1 = 1) : ‖G.vector 1‖ = 1 := by
  have h := G.inner_vector 1 1
  rw [star_one, one_mul, h1] at h
  have hn : ‖G.vector 1‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h]
    rfl
  nlinarith [norm_nonneg (G.vector 1)]

def normalTracialRepresentation (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) : TracialRepresentation M := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  refine {
    vector := G.vector 1
    norm_vector := G.norm_identityVector h1
    cyclic := ?_
    separating := ?_
  }
  · intro S T
    obtain ⟨a, rfl⟩ := e.surjective S
    obtain ⟨b, rfl⟩ := e.surjective T
    change inner ℂ (G.vector 1) (G.left a (G.left b (G.vector 1))) =
      inner ℂ (G.vector 1) (G.left b (G.left a (G.vector 1)))
    simp only [G.left_vector, mul_one, G.inner_vector, star_one, one_mul]
    exact G.tracial a b
  · intro T hT
    obtain ⟨a, rfl⟩ := e.surjective T
    have ha : G.vector a = 0 := by
      change G.left a (G.vector 1) = 0 at hT
      simpa only [G.left_vector, mul_one] using hT
    have haz : a = 0 := hf (ha.trans (map_zero G.vector).symm)
    rw [haz, map_zero]

@[simp] theorem normalTracialRepresentation_vector (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) :
    (G.normalTracialRepresentation h1 hf M hrange).vector = G.vector 1 := rfl

@[simp] theorem normalTracialRepresentation_trace (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) (a : A) :
    (G.normalTracialRepresentation h1 hf M hrange).trace
      (equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange a) = G.trace a := by
  change vectorTrace (G.vector 1) (G.left a) = G.trace a
  exact G.trace_eq_vectorTrace a

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeMatrixExtension
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix-factor automorphism extends to the actual normal tracial
algebra by conjugating its left representation with the free-word unitary. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (h1 : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (hgen : G.FactorsTraciallyGenerate A D)

def freeMatrixExtensionUnitary : H ≃ₗᵢ[ℂ] H :=
  G.freeMatrixConjugationUnitary A D ι u h1 hf
    (G.reducedWordGenerated_of_factorsTraciallyGenerate A D h1 hgen)

local notation "U" => G.freeMatrixExtensionUnitary A D ι u h1 hf hgen

@[simp] theorem freeMatrixExtensionUnitary_one : U (G.vector 1) = G.vector 1 :=
  G.freeMatrixConjugationIsometry_one A D ι u h1 hf
    (G.reducedWordGenerated_of_factorsTraciallyGenerate A D h1 hgen)

def freeMatrixExtensionRepresentation : P →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (U).conjStarAlgEquiv.toStarAlgHom.comp G.left

@[simp] theorem freeMatrixExtensionRepresentation_apply (x : P) :
    G.freeMatrixExtensionRepresentation A D ι u h1 hf hgen x =
      (U).conjStarAlgEquiv (G.left x) := rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_OppositeTracialGeometry
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Right multiplication is the left representation of the opposite algebra.
This transfers the proved bounded-ball normality criterion to its actual range. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

def rightRepresentation : Pᵐᵒᵖ →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun a := G.right (MulOpposite.unop a)
  map_zero' := by
    ext ξ
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    simp only [MulOpposite.unop_zero, right_vector, mul_zero, map_zero,
      zero_apply]
  map_one' := by
    ext ξ
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    simp only [MulOpposite.unop_one, right_vector, mul_one, one_apply_eq_self]
  map_add' a b := by
    ext ξ
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro c
    simp only [MulOpposite.unop_add, right_vector, mul_add, map_add,
      add_apply]
  map_mul' a b := G.right_mul (MulOpposite.unop b) (MulOpposite.unop a)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, MulOpposite.unop_smul, MulOpposite.unop_one]
    change G.right (z • (1 : P)) = z • (1 : H →L[ℂ] H)
    ext ξ
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    simp only [right_vector, mul_smul_comm, mul_one, map_smul,
      smul_apply, one_apply_eq_self]
  map_star' a := (G.right_adjoint (MulOpposite.unop a)).symm

@[simp] theorem rightRepresentation_apply (a : Pᵐᵒᵖ) :
    G.rightRepresentation a = G.right (MulOpposite.unop a) := rfl

def oppositeGeometry : TracialCornerGeometry Pᵐᵒᵖ H where
  trace := G.trace.comp (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap
  vector := G.vector.comp (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap
  left := G.rightRepresentation
  inner_vector a b := by
    change inner ℂ (G.vector (MulOpposite.unop a)) (G.vector (MulOpposite.unop b)) =
      G.trace (MulOpposite.unop b * star (MulOpposite.unop a))
    rw [G.inner_vector, G.tracial]
  tracial a b := G.tracial (MulOpposite.unop b) (MulOpposite.unop a)
  dense_vector := by
    intro ξ
    have hrange : Set.range (G.vector.comp (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap) =
        Set.range G.vector := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨MulOpposite.unop a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨MulOpposite.op a, rfl⟩
    change ξ ∈ closure (Set.range (G.vector.comp (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap))
    rw [hrange]
    exact G.dense_vector ξ
  left_vector a b := G.right_vector (MulOpposite.unop b) (MulOpposite.unop a)

@[simp] theorem oppositeGeometry_vector (a : Pᵐᵒᵖ) :
    G.oppositeGeometry.vector a = G.vector (MulOpposite.unop a) := rfl

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialGeometrySupport
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal tracial geometry supplies the propagation support input.
Positivity of its trace follows directly from the Hilbert inner product. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

section Ordered
variable [PartialOrder A] [StarOrderedRing A]

def positiveTrace : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ G.trace (fun a ha => by
    obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    rw [← G.inner_vector]
    exact Complex.nonneg_iff.mpr ⟨inner_self_nonneg (𝕜 := ℂ) (x := G.vector b), (inner_self_im (𝕜 := ℂ) (G.vector b)).symm⟩)

@[simp] theorem positiveTrace_apply (a : A) : G.positiveTrace a = G.trace a := rfl

end Ordered

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_LocalFreeCornerInputs
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact remaining published premises for one local free-product
application. Every field concerns the underlying tracial algebras or their
standard Hilbert models; none is an estimate for the operator being tested.
The generated algebras, frame, reflection and ordinary word density
provide the geometric data. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

universe u v

variable {P : Type u} [CStarAlgebra P]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  {b : ℝ} (Q : SmallFreeCornerData (G.baseGeometry D).trace b)
  (s : A) (hssq : s * s = 1)
  (hτ : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)

/-- Published local ingredients, specialized to the chosen small corner
and test symmetry. The applicability to the actual finite normal free
product is kept explicit in the finite-factor assembly. -/
structure LocalFreeCornerPublishedInputs : Prop where
  /-- Blackadar III.1.1.11: finite-factor projection comparison. -/
  comparison : FiniteFactorProjectionComparison (fun a => (G.trace a).re)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_GeneratedEmbeddings
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual copies of the two factors inside their generated algebra.
The range identifications align the GNS recovery operator with the factor
generation, freeness, and matrix tower used by the local theorem. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]

variable [PartialOrder R] [StarOrderedRing R]
  (τR : R →ₚ[ℂ] ℂ) (ψ : R →⋆ₐ[ℂ] P) (hψ : ∀ r, ψ r ∈ L)
  (htrace : ∀ r, τ (ψ r) = τR r)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

include htrace in
omit [StarOrderedRing R] in
theorem generatedEmbedding_preserves_trace :
    ∀ r, (gnsTracialGeometry (restrictedPositiveTrace τ L)
      (restrictedPositiveTrace_tracial τ L htr)).trace (ψ.codRestrict L hψ r) = τR r :=
  htrace

/-- The matrix tower lives on the same native GNS space as the recovered
operator, and on the exact range of the embedded free factor. -/
def generatedEmbeddingMatrices
    (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR)) :=
  transportTracialMatrices τR
    (gnsTracialGeometry (restrictedPositiveTrace τ L)
      (restrictedPositiveTrace_tracial τ L htr))
    (ψ.codRestrict L hψ) (generatedEmbedding_preserves_trace τ htr L τR ψ hψ htrace) M

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CanonicalGeneratedModel
attribute [-instance] _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual generated algebra for two embedded tracial factors. Its
containment, generation, freeness and matrix tower follow from the concrete
embeddings; there is no separately chosen generated-algebra model. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)

def canonicalGeneratedAlgebra : StarSubalgebra ℂ P :=
  (gnsTracialGeometry τ htr).l2FactorAlgebra φ.range ψ.range

instance canonicalGeneratedAlgebra_isClosed :
    IsClosed (canonicalGeneratedAlgebra τ htr φ ψ : Set P) :=
  inferInstanceAs (IsClosed
    ((gnsTracialGeometry τ htr).l2FactorAlgebra φ.range ψ.range : Set P))

theorem canonicalGenerated_first_mem (a : A) :
    φ a ∈ canonicalGeneratedAlgebra τ htr φ ψ :=
  (gnsTracialGeometry τ htr).left_le_l2FactorAlgebra φ.range ψ.range ⟨a, rfl⟩

theorem canonicalGenerated_second_mem (r : R) :
    ψ r ∈ canonicalGeneratedAlgebra τ htr φ ψ :=
  (gnsTracialGeometry τ htr).right_le_l2FactorAlgebra φ.range ψ.range ⟨r, rfl⟩

def canonicalGeneratedFirst : A →⋆ₐ[ℂ] canonicalGeneratedAlgebra τ htr φ ψ :=
  φ.codRestrict (canonicalGeneratedAlgebra τ htr φ ψ)
    (canonicalGenerated_first_mem τ htr φ ψ)

def canonicalGeneratedSecond : R →⋆ₐ[ℂ] canonicalGeneratedAlgebra τ htr φ ψ :=
  ψ.codRestrict (canonicalGeneratedAlgebra τ htr φ ψ)
    (canonicalGenerated_second_mem τ htr φ ψ)

def canonicalGeneratedTrace :=
  restrictedPositiveTrace τ (canonicalGeneratedAlgebra τ htr φ ψ)

def canonicalGeneratedGeometry :=
  gnsTracialGeometry (canonicalGeneratedTrace τ htr φ ψ)
    (restrictedPositiveTrace_tracial τ (canonicalGeneratedAlgebra τ htr φ ψ) htr)

theorem canonicalGenerated_faithful
    (hf : ∀ a : P, τ (star a * a) = 0 → a = 0) :
    Function.Injective (canonicalGeneratedGeometry τ htr φ ψ).vector :=
  restrictedGNS_vector_injective τ htr (canonicalGeneratedAlgebra τ htr φ ψ) hf

variable [PartialOrder R] [StarOrderedRing R]
  (τR : R →ₚ[ℂ] ℂ) (hψτ : ∀ r, τ (ψ r) = τR r)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

/-- The source matrix tower is transported into this exact generated model. -/
def canonicalGeneratedMatrices
    (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR)) :=
  generatedEmbeddingMatrices τ htr (canonicalGeneratedAlgebra τ htr φ ψ) τR ψ
    (canonicalGenerated_second_mem τ htr φ ψ) hψτ M

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GeneratedGNSRecovery
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recovery through an intermediate generated algebra. The free-corner
argument is carried out on that algebra's own GNS space; its compression
still recovers the original operator with no change in the bound. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A P : Type*} [CStarAlgebra A] [CStarAlgebra P]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder P] [StarOrderedRing P]
  (τA : A →ₚ[ℂ] ℂ) (τP : P →ₚ[ℂ] ℂ)
  (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]
  (φ : A →⋆ₐ[ℂ] P) (hmem : ∀ a, φ a ∈ L) (hφ : ∀ a, τP (φ a) = τA a)

include hφ in
omit [StarOrderedRing A] in
theorem restrictedHom_preserves_trace :
    ∀ a, restrictedPositiveTrace τP L (φ.codRestrict L hmem a) = τA a := hφ

/-- The source embeds in the intermediate algebra's GNS space. -/
def generatedGNSInclusion : τA.GNS →ₗᵢ[ℂ] (restrictedPositiveTrace τP L).GNS :=
  gnsTracialHomIsometry τA (restrictedPositiveTrace τP L) (φ.codRestrict L hmem)
    (restrictedHom_preserves_trace τA τP L φ hmem hφ)

@[simp] theorem generatedGNSInclusion_vector (a : A) :
    generatedGNSInclusion τA τP L φ hmem hφ (gnsTracialVector τA a) =
      gnsTracialVector (restrictedPositiveTrace τP L) (φ.codRestrict L hmem a) :=
  gnsTracialHomIsometry_vector τA (restrictedPositiveTrace τP L) (φ.codRestrict L hmem)
    (restrictedHom_preserves_trace τA τP L φ hmem hφ) a

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CanonicalFreeCornerCore
attribute [-instance] _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical free-corner estimate for a positive tracial algebra.
The estimate is expressed through the generated algebra and its
compressed tracial representation. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)
  (hφ : Function.Injective φ) (hψ : Function.Injective ψ)

local notation "L" => canonicalGeneratedAlgebra τ htr φ ψ
local notation "G" => canonicalGeneratedGeometry τ htr φ ψ
local notation "A₀" => StarAlgHom.range (canonicalGeneratedFirst τ htr φ ψ)
local notation "D₀" => StarAlgHom.range (canonicalGeneratedSecond τ htr φ ψ)

include hφ in
omit [PartialOrder R] [StarOrderedRing R] in
theorem canonicalFirstRange_closed : IsClosed (A₀ : Set L) :=
  codRestrict_range_isClosed L φ (canonicalGenerated_first_mem τ htr φ ψ)
    (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosed_range
include hψ in
omit [PartialOrder R] [StarOrderedRing R] in
theorem canonicalSecondRange_closed : IsClosed (D₀ : Set L) :=
  codRestrict_range_isClosed L ψ (canonicalGenerated_second_mem τ htr φ ψ)
    (NonUnitalStarAlgHom.isometry ψ hψ).isClosedEmbedding.isClosed_range

variable [IsClosed ((canonicalGeneratedFirst τ htr φ ψ).range :
    Set (canonicalGeneratedAlgebra τ htr φ ψ))]
  [IsClosed ((canonicalGeneratedSecond τ htr φ ψ).range :
    Set (canonicalGeneratedAlgebra τ htr φ ψ))]

variable (τR : R →ₚ[ℂ] ℂ) (hψτ : ∀ r, τ (ψ r) = τR r)

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))
  (h1 : τ 1 = 1) (hfτ : ∀ a : P, τ (star a * a) = 0 → a = 0)

local notation "M₀" => canonicalGeneratedMatrices τ htr φ ψ τR hψτ M

/-- The exact local structural input, with the native trace and faithfulness
proofs supplied by the canonical generated model. -/
abbrev CanonicalFreeCornerCoreInput {b : ℝ}
    (_Q : SmallFreeCornerData ((G).baseGeometry D₀).trace b)
    (_x : A) (_hxsq : _x * _x = 1) : Prop :=
  let _matrices := M₀
  let _faithful := canonicalGenerated_faithful τ htr φ ψ hfτ
  (G).LocalFreeCornerPublishedInputs

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixTracialGNS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.generatedGNSInclusion_vector _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.restrictedTracialGNSInclusion_vector _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- Square arrays use the ordinary Hilbert sum norm in both coordinates. -/
abbrev MatrixGNSArray (τ : A →ₚ[ℂ] ℂ) (n : ℕ) :=
  HilbertCopies (HilbertCopies τ.GNS n) n

/-- The unscaled array of represented matrix entries. -/
def matrixGNSArrayLinear (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    CStarMatrix (Fin n) (Fin n) A →ₗ[ℂ] MatrixGNSArray τ n where
  toFun X := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => gnsTracialVector τ (X i j)))
  map_add' X Y := by
    ext i j
    simp only [PiLp.add_apply, CStarMatrix.add_apply, map_add]
  map_smul' c X := by
    ext i j
    simp only [PiLp.smul_apply, CStarMatrix.smul_apply, map_smul,
      RingHom.id_apply]

@[simp] theorem matrixGNSArrayLinear_apply (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) (i j : Fin n) :
    matrixGNSArrayLinear τ n X i j = gnsTracialVector τ (X i j) := rfl

/-- Normalized represented matrix vectors. -/
def matrixGNSVector (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    CStarMatrix (Fin n) (Fin n) A →ₗ[ℂ] MatrixGNSArray τ n :=
  (matrixGNSScale n : ℂ) • matrixGNSArrayLinear τ n

@[simp] theorem matrixGNSVector_apply (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) (i j : Fin n) :
    matrixGNSVector τ n X i j = (matrixGNSScale n : ℂ) • gnsTracialVector τ (X i j) := rfl

theorem matrixGNSVector_inner (τ : A →ₚ[ℂ] ℂ)
    (X Y : CStarMatrix (Fin n) (Fin n) A) :
    inner ℂ (matrixGNSVector τ n X) (matrixGNSVector τ n Y) =
      normalizedMatrixTrace τ n (star X * Y) := by
  have hc : (matrixGNSScale n : ℂ) * starRingEnd ℂ (matrixGNSScale n : ℂ) =
      (n : ℂ)⁻¹ := by
    rw [Complex.conj_ofReal]
    have hr : matrixGNSScale n * matrixGNSScale n = (n : ℝ)⁻¹ := by
      simpa only [pow_two] using (matrixGNSScale_sq (n := n))
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast] using
      congrArg (fun r : ℝ => (r : ℂ)) hr
  rw [normalizedMatrixTrace_star_mul]
  simp only [matrixGNSVector, LinearMap.smul_apply, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, hc]
  congr 1
  simp only [PiLp.inner_apply, matrixGNSArrayLinear_apply, gnsTracialVector_inner]

theorem matrixGNSVector_norm (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖matrixGNSVector τ n X‖ = ‖gnsTracialVector (normalizedMatrixTrace τ n) X‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    matrixGNSVector_inner, gnsTracialVector_inner]

/-- The completed matrix GNS space embeds isometrically in its entry array. -/
def matrixGNSIsometry (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    (normalizedMatrixTrace τ n).GNS →ₗᵢ[ℂ] MatrixGNSArray τ n :=
  (matrixGNSVector τ n).extendOfIsometry
    (gnsTracialVector_dense (normalizedMatrixTrace τ n)) (matrixGNSVector_norm τ)

@[simp] theorem matrixGNSIsometry_vector (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    matrixGNSIsometry τ n (gnsTracialVector (normalizedMatrixTrace τ n) X) =
      matrixGNSVector τ n X :=
  LinearMap.extendOfIsometry_eq _ (gnsTracialVector_dense (normalizedMatrixTrace τ n))
    (matrixGNSVector_norm τ) X

theorem matrixGNSArrayLinear_dense (τ : A →ₚ[ℂ] ℂ) :
    DenseRange (matrixGNSArrayLinear τ n) := by
  have hrow := denseRange_hilbert_entries (J := Fin n)
    (gnsTracialVector τ) (gnsTracialVector_dense τ)
  have harr := denseRange_hilbert_entries (J := Fin n)
    (fun x : Fin n → A => WithLp.toLp 2 (fun j => gnsTracialVector τ (x j))) hrow
  apply harr.mono
  rintro _ ⟨X, rfl⟩
  exact ⟨CStarMatrix.ofMatrix X, rfl⟩

theorem matrixGNSVector_dense (τ : A →ₚ[ℂ] ℂ) : DenseRange (matrixGNSVector τ n) := by
  have hc : (matrixGNSScale n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (matrixGNSScale_pos (n := n)).ne'
  apply (matrixGNSArrayLinear_dense (n := n) τ).mono
  rintro _ ⟨X, rfl⟩
  refine ⟨(matrixGNSScale n : ℂ)⁻¹ • X, ?_⟩
  change (matrixGNSScale n : ℂ) •
    matrixGNSArrayLinear τ n ((matrixGNSScale n : ℂ)⁻¹ • X) = matrixGNSArrayLinear τ n X
  rw [map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem matrixGNSIsometry_surjective (τ : A →ₚ[ℂ] ℂ) :
    Function.Surjective (matrixGNSIsometry τ n) := by
  have hd : DenseRange (matrixGNSIsometry τ n) := by
    apply (matrixGNSVector_dense (n := n) τ).mono
    rintro _ ⟨X, rfl⟩
    exact ⟨gnsTracialVector (normalizedMatrixTrace τ n) X, matrixGNSIsometry_vector τ X⟩
  intro x
  have hx := hd x
  rw [(matrixGNSIsometry τ n).isometry.isClosedEmbedding.isClosed_range.closure_eq] at hx
  exact hx

/-- The completed normalized matrix GNS space is exactly the square Hilbert array. -/
def matrixGNSUnitary (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    (normalizedMatrixTrace τ n).GNS ≃ₗᵢ[ℂ] MatrixGNSArray τ n :=
  LinearIsometryEquiv.ofSurjective (matrixGNSIsometry τ n) (matrixGNSIsometry_surjective τ)

@[simp] theorem matrixGNSUnitary_vector (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) (i j : Fin n) :
    matrixGNSUnitary τ n (gnsTracialVector (normalizedMatrixTrace τ n) X) i j =
      (matrixGNSScale n : ℂ) • gnsTracialVector τ (X i j) := by
  change matrixGNSIsometry τ n (gnsTracialVector (normalizedMatrixTrace τ n) X) i j = _
  rw [matrixGNSIsometry_vector, matrixGNSVector_apply]

/-- The ordinary matrix action on the row coordinate, with a standard copy
in each column coordinate. -/
def matrixLeftArray (τ : A →ₚ[ℂ] ℂ) (X : CStarMatrix (Fin n) (Fin n) A) :
    MatrixGNSArray τ n →L[ℂ] MatrixGNSArray τ n :=
  matrixOperator (fun i k => amplify (τ.gnsStarAlgHom (X i k)) n)

omit [NeZero n] in
@[simp] theorem matrixLeftArray_apply (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) (ξ : MatrixGNSArray τ n) (i j : Fin n) :
    matrixLeftArray τ X ξ i j = ∑ k : Fin n, τ.gnsStarAlgHom (X i k) (ξ k j) := by
  simp [matrixLeftArray, matrixOperator, amplify]

theorem matrixGNSVector_mul (τ : A →ₚ[ℂ] ℂ)
    (X Y : CStarMatrix (Fin n) (Fin n) A) :
    matrixGNSVector τ n (X * Y) = matrixLeftArray τ X (matrixGNSVector τ n Y) := by
  ext i j
  simp only [matrixGNSVector_apply, matrixLeftArray_apply, CStarMatrix.mul_apply,
    map_sum, map_smul, gnsTracialVector_left, Finset.smul_sum]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixArrayFlattening
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening nested matrix and Hilbert-array coordinates -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

section HilbertFlattening

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Flatten two finite Hilbert sums in the same order as block matrices. -/
def hilbertArrayFlatten (p q : ℕ) :
    HilbertCopies (HilbertCopies H q) p ≃ₗᵢ[ℂ] HilbertCopies H (p * q) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : Fin p) (_ : Fin q) => H)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H
      ((Equiv.sigmaEquivProd (Fin p) (Fin q)).trans finProdFinEquiv))

@[simp] theorem hilbertArrayFlatten_apply (p q : ℕ)
    (x : HilbertCopies (HilbertCopies H q) p) (i : Fin p) (j : Fin q) :
    hilbertArrayFlatten p q x (finProdFinEquiv (i, j)) = x i j := by
  change x ((finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm
      (finProdFinEquiv (i, j))).1
    ((finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm
      (finProdFinEquiv (i, j))).2 = x i j
  rw [Equiv.symm_apply_apply]

/-- Three nested finite Hilbert sums, in the same order as triple block matrices. -/
def hilbertTripleFlatten (p q t : ℕ) :
    HilbertCopies (HilbertCopies (HilbertCopies H t) q) p ≃ₗᵢ[ℂ]
      HilbertCopies H (p * (q * t)) :=
  (LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : Fin p => hilbertArrayFlatten (H := H) q t)).trans
    (hilbertArrayFlatten (H := H) p (q * t))

@[simp] theorem hilbertTripleFlatten_apply (p q t : ℕ)
    (x : HilbertCopies (HilbertCopies (HilbertCopies H t) q) p)
    (i : Fin p) (j : Fin q) (a : Fin t) :
    hilbertTripleFlatten p q t x
      (finProdFinEquiv (i, finProdFinEquiv (j, a))) = x i j a := by
  simp [hilbertTripleFlatten]

/-- The Hilbert-space change of coordinates for the four-by-four dilation. -/
def hilbertFourfoldFlatten (n : ℕ) :
    HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2 ≃ₗᵢ[ℂ]
      HilbertCopies H (4 * n) :=
  (hilbertTripleFlatten 2 2 n).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H
      (finCongr (by omega : 2 * (2 * n) = 4 * n)))

@[simp] theorem hilbertFourfoldFlatten_apply (n : ℕ)
    (x : HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2)
    (i j : Fin 2) (a : Fin n) :
    hilbertFourfoldFlatten n x (fourfoldIndexEquiv n (i, (j, a))) = x i j a := by
  simp [hilbertFourfoldFlatten, fourfoldIndexEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

end HilbertFlattening

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteAmplificationReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite amplification is reduced to centered symmetry tests on square Hilbert
arrays. The operator replacement and its symmetry bound remain explicit local
hypotheses; the padding, dilation, coordinate change, and perturbation losses
are all proved here.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual diagonal amplification of a star representation. -/
def amplifiedScalarRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) :
    A →⋆ₐ[ℂ] (HilbertCopies H n →L[ℂ] HilbertCopies H n) where
  toFun a := amplify (σ a) n
  map_zero' := by ext x i; simp [amplify_apply]
  map_one' := by ext x i; simp [amplify_apply]
  map_add' a b := by ext x i; simp [amplify_apply]
  map_mul' a b := by ext x i; simp [amplify_apply, mul_apply_eq_comp]
  commutes' c := by
    ext x i
    simp [amplify_apply, Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    change amplify (σ (star a)) n = (amplify (σ a) n).adjoint
    rw [adjoint_amplify, map_star, ContinuousLinearMap.star_eq_adjoint]

@[simp] theorem amplifiedScalarRepresentation_apply
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) (a : A) :
    amplifiedScalarRepresentation σ n a = amplify (σ a) n := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixSmallCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished scalar matrix corner has the original algebra's
commutator estimate on a finite standard multiplicity. The proof uses
actual coordinate insertion/projection and then transports the estimate
to the normalized matrix GNS space. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Place one operator in a diagonal coordinate of a Hilbert array. -/
def coordinateCornerOperator {n : ℕ} (i : Fin n) (T : H →L[ℂ] H) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  (copyInsert i).comp (T.comp (PiLp.proj 2 (fun _ : Fin n => H) i))

@[simp] theorem coordinateCornerOperator_apply {n : ℕ} (i : Fin n) (T : H →L[ℂ] H)
    (ξ : HilbertCopies H n) :
    coordinateCornerOperator i T ξ = PiLp.single 2 i (T (ξ i)) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixSubfactorTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix amplification of an included subfactor acts entrywise.
Commutation with the original subfactor therefore gives commutation with
the full matrix subfactor on the square array of standard copies. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) {n : ℕ}

theorem normalizedMatrixTrace_entryHom
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] [NeZero n]
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    normalizedMatrixTrace τB n (matrixEntryHom φ X) = normalizedMatrixTrace τA n X := by
  simp only [normalizedMatrixTrace_apply, matrixEntryHom_apply, hφ]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixDiagonalEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed diffuse matrix-generated factor is embedded diagonally in
its finite matrix amplifications. The normalized trace is unchanged. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] (n : ℕ)

variable [NeZero n]

variable [PartialOrder A] [StarOrderedRing A]

@[simp] theorem normalizedMatrixTrace_diagonal (τ : A →ₚ[ℂ] ℂ) (a : A) :
    normalizedMatrixTrace τ n (matrixDiagonalHom n a) = τ a := by
  rw [normalizedMatrixTrace_apply]
  simp only [matrixDiagonalHom_diagonal, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne n))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialUltrapowerHom
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.HochschildUltrapower.quotientUnitary_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace-preserving homomorphisms induce homomorphisms of the actual
tracial quotients. In particular this realizes Q^ω inside P^ω. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower TracialUltrapower Filter
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

include hφ in
theorem boundedSequenceStarHom_null (x : ℕ →ᵇ A) (hx : x ∈ ideal τA hA ω trA) :
    boundedSequenceStarHom φ x ∈ ideal τB hB ω trB := by
  apply (mem_nullSubmodule _ _ _).mpr
  have hn (i : ℕ) : ‖τB.toPreGNS (φ (x i))‖ = ‖τA.toPreGNS (x i)‖ := by
    simpa only [gnsTracialVector_apply, UniformSpace.Completion.norm_coe] using
      gnsTracialHom_norm τA τB φ hφ (x i)
  have hx' : Tendsto (fun i => ‖τA.toPreGNS (x i)‖) (ω : Filter ℕ) (𝓝 0) :=
    (mem_nullSubmodule _ _ x).mp hx
  change Tendsto (fun i => ‖τB.toPreGNS (φ (x i))‖) (ω : Filter ℕ) (𝓝 0)
  simpa only [hn] using hx'

/-- The induced star homomorphism of tracial ultrapowers. -/
def tracialUltrapowerMap : Ultrapower τA hA ω trA →⋆ₐ[ℂ] Ultrapower τB hB ω trB where
  toAlgHom := Ideal.Quotient.liftₐ (ideal τA hA ω trA)
    ((quotientHom τB hB ω trB).comp (boundedSequenceStarHom φ)).toAlgHom (by
      intro x hx
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr
        (boundedSequenceStarHom_null τA τB hA hB ω trA trB φ hφ x hx))
  map_star' x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact map_star ((quotientHom τB hB ω trB).comp (boundedSequenceStarHom φ)) a

@[simp] theorem tracialUltrapowerMap_mk (x : ℕ →ᵇ A) :
    tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ (quotientHom τA hA ω trA x) =
      quotientHom τB hB ω trB (boundedSequenceStarHom φ x) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_PopaConjugatePosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugacy form of Popa's free-position construction: a unitary in
an irreducibly included subfactor's tracial ultrapower conjugates a prescribed
constant subfactor to a copy free from the ambient constant algebra.
The conjugating unitary remains in the prescribed subfactor ultrapower, and
trace preservation transports the matrix presentation to its conjugated copy.
-/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

/-- The prescribed subfactor is embedded as constants, conjugated inside A^ω,
then included in B^ω. Thus membership in the prescribed ultrapower is retained. -/
def conjugatedConstantEmbedding (ρ : R →⋆ₐ[ℂ] A)
    (u : unitary (Ultrapower τA hA ω trA)) : R →⋆ₐ[ℂ] Ultrapower τB hB ω trB :=
  (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ).comp
    ((Unitary.conjStarAlgAut ℂ (Ultrapower τA hA ω trA) u).toStarAlgHom.comp
      ((constant τA hA ω trA).comp ρ))

/-- Local published specialization for a fixed irreducible inclusion of
separable II₁ factors A⊂B and a fixed separable subfactor ρ(R)⊂A.
The two free algebras are concrete ranges, rather than unspecified copies. -/
def Popa1995ConjugateFreenessInput
    (_hω : (ω : Filter ℕ) ≤ Filter.cofinite) (ρ : R →⋆ₐ[ℂ] A) : Prop :=
  ∃ u : unitary (Ultrapower τA hA ω trA),
    ScalarFree (quotientTrace τB hB ω trB).toLinearMap
      (constant τB hB ω trB).range
      (conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ u).range

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CanonicalFreeCornerEstimate
attribute [-instance] _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original operator is recovered after applying the local free-corner
argument in the actual generated GNS model. All generation, faithfulness,
and compression requirements are proved here; the remaining local hypotheses
are the explicitly cited published structural inputs. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open TracialCornerGeometry
open scoped ComplexOrder

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder R] [StarOrderedRing R]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ) (τR : R →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "τQ" => quotientTrace τB hB ω trB
local notation "trQ" => quotientTrace_tracial τB hB ω trB
local notation "ι" => constant τB hB ω trB

variable (ψ : R →⋆ₐ[ℂ] Ultrapower τB hB ω trB)
  (hψτ : ∀ r, quotientTrace τB hB ω trB (ψ r) = τR r)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  (hψ : Function.Injective ψ)

local notation "L" => canonicalGeneratedAlgebra τQ trQ ι ψ
local notation "G" => canonicalGeneratedGeometry τQ trQ ι ψ
local notation "D₀" => StarAlgHom.range (canonicalGeneratedSecond τQ trQ ι ψ)

/-- The chosen closed-range proof is included inside this data type. -/
def CanonicalSecondFrame (b : ℝ) : Type _ := by
  letI : IsClosed (D₀ : Set L) := canonicalSecondRange_closed τQ trQ ι ψ hψ
  exact SmallFreeCornerData ((G).baseGeometry D₀).trace b

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

/-- Published local data on the exact canonical free-product model. -/
abbrev CanonicalFreeCornerInput {b : ℝ}
    (Q : CanonicalSecondFrame τB hB ω trB ψ hψ b)
    (x : B) (hxsq : x * x = 1) : Prop := by
  letI : IsClosed (D₀ : Set L) := canonicalSecondRange_closed τQ trQ ι ψ hψ
  letI : IsClosed (StarAlgHom.range (canonicalGeneratedFirst τQ trQ ι ψ) : Set L) :=
    canonicalFirstRange_closed τQ trQ ι ψ (constant_injective τB hB ω trB hfB)
  exact CanonicalFreeCornerCoreInput (τ := τQ) (htr := trQ) (φ := ι) (ψ := ψ)
    (τR := τR) (hψτ := hψτ) (M := M)
    (hfτ := quotientTrace_faithful τB hB ω trB) Q x hxsq

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite standard multiplicities exhaust the countable standard
representation.  The first-coordinate projections and all intertwining
identities below are constructed on the actual Hilbert direct sum. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMap
open scoped ENNReal Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

/-- Insert the first `n` coordinates, with zero in every later coordinate. -/
def firstCopiesInclusion (n : ℕ) : HilbertCopies H n →L[ℂ] CountableCopies H :=
  sumColumns (fun i : Fin n => lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 i.val)

omit [CompleteSpace H] in
@[simp] theorem firstCopiesInclusion_apply (n : ℕ) (x : HilbertCopies H n) :
    firstCopiesInclusion n x = ∑ i : Fin n, lp.single 2 i.val (x i) :=
  sumColumns_apply _ _

@[simp] theorem firstCopiesInclusion_adjoint_apply (n : ℕ)
    (x : CountableCopies H) (i : Fin n) : (firstCopiesInclusion n).adjoint x i = x i.val := by
  rw [firstCopiesInclusion, sumColumns_adjoint_apply]
  apply ext_inner_left ℂ
  intro y
  rw [adjoint_inner_right]
  exact lp.inner_single_left _ _ _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorApplication
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-factor application of the free-corner argument

The local hypotheses below specify the actual increasing-matrix inclusion,
its normal represented closure, and the published projection and free-product
inputs. The commutator estimates combine Haar averaging, the free-corner
theorem, and the exact
finite and countable amplification transfers.
-/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder Topology

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hR : τR 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trR : ∀ a b : R, τR (a * b) = τR (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (ρ : R →⋆ₐ[ℂ] B) (hρτ : ∀ a, τB (ρ a) = τR a)
  (hfR : ∀ a : R, τR (star a * a) = 0 → a = 0)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

variable (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

/-- Exact remaining structural inputs for the fixed finite-factor application.
Only the free position remains explicit. Stage commutation, source and
generated-factor comparison, rounding and diffuse corners are constructed
from the faithful normal traces and the dense matrix tower. -/
structure FiniteFactorFreeCornerInputs : Prop where
  free_position : ∀ (n : ℕ) [NeZero n],
    Popa1995ConjugateFreenessInput
      (normalizedMatrixTrace τR n) (normalizedMatrixTrace τB n)
      (normalizedMatrixTrace_one τR hR) (normalizedMatrixTrace_one τB hB)
      ω (normalizedMatrixTrace_tracial τR trR) (normalizedMatrixTrace_tracial τB trB)
      (matrixEntryHom ρ) (normalizedMatrixTrace_entryHom τR τB ρ hρτ)
      hω (matrixDiagonalHom n)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CentralDecomposition
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Central decomposition and the uniform separable estimate

The direct-integral input records only representatives of decomposable
operators, their almost-everywhere algebra operations, the scalar and matrix
norm formulas, and countably many dense contraction sections. These are the
specializations of Blackadar, III.1.6.1–4 and III.5.1.10–15 used here (with
Kaplansky density, I.9.1.3, for the contraction tests). Representatives need
satisfy algebraic identities only almost everywhere for each fixed pair.

The scalar fiber bounds, their common conull set, the factor estimates, and
the final perturbation estimate are proved below.
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter ContinuousLinearMapWOT
open scoped Topology

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type u) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

/-- The exact direct-integral identities needed for one separable algebra.
No commutator estimate is a field of this structure. -/
structure CentralDecompositionData (P : VonNeumannAlgebra H) where
  algebra : ∀ a, VonNeumannAlgebra (K a)
  fiber : (vonNeumannCenter P).commutant.toStarSubalgebra → ∀ a, K a →L[ℂ] K a
  map_sub : ∀ x y, ∀ᵐ a ∂μ, fiber (x - y) a = fiber x a - fiber y a
  map_mul : ∀ x y, ∀ᵐ a ∂μ, fiber (x * y) a = fiber x a * fiber y a
  mem : ∀ x : P.toStarSubalgebra, ∀ᵐ a ∂μ,
    fiber (centerCommutantInclusion P x) a ∈ algebra a
  norm_le_iff : ∀ (x : (vonNeumannCenter P).commutant.toStarSubalgebra) (c : ℝ), 0 ≤ c →
    (‖(x : H →L[ℂ] H)‖ ≤ c ↔ ∀ᵐ a ∂μ, ‖fiber x a‖ ≤ c)
  matrix_norm_le_iff : ∀ (n : ℕ)
    (X : Matrix (Fin n) (Fin n) (vonNeumannCenter P).commutant.toStarSubalgebra)
    (c : ℝ), 0 ≤ c →
    (‖matrixOperator (fun i j => (X i j : H →L[ℂ] H))‖ ≤ c ↔
      ∀ᵐ a ∂μ, ‖matrixOperator (fun i j => fiber (X i j) a)‖ ≤ c)
  test : ℕ → P.toStarSubalgebra
  test_norm : ∀ j, ‖(test j : H →L[ℂ] H)‖ ≤ 1
  test_dense : ∀ᵐ a ∂μ, ∀ T : K a →L[ℂ] K a,
    T ∈ algebra a → ‖T‖ ≤ 1 →
    ofCLM T ∈ closure (Set.range fun j =>
      ofCLM (fiber (centerCommutantInclusion P (test j)) a))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteMatrixTower
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate maps for the actual increasing matrix stages. These maps
retain the concrete operators and their normalized traces. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N : VonNeumannAlgebra H}

def concreteStageEquiv [Nontrivial N.toStarSubalgebra] (F : FiniteMatrixStage N) :
    Matrix (Fin F.size) (Fin F.size) ℂ ≃⋆ₐ[ℂ] F.units.concreteAlgebra := by
  letI : Nonempty (Fin F.size) := ⟨⟨0, F.positive⟩⟩
  exact StarAlgEquiv.ofInjective F.units.concreteHom
    (Subtype.val_injective.comp F.units.injective)

@[simp] theorem concreteStageEquiv_apply [Nontrivial N.toStarSubalgebra]
    (F : FiniteMatrixStage N) (a : Matrix (Fin F.size) (Fin F.size) ℂ) :
    ((concreteStageEquiv F a : F.units.concreteAlgebra) : H →L[ℂ] H) =
      F.units.concreteHom a := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConjugateMomentCriterion
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

omit [CStarAlgebra B] in
lemma conjugateMomentTail_eval (F : B → C) (u : unitary C) (v : List (B × B)) :
    ((conjugateMomentTail v).map (fun b => ((u ^ b.1 : unitary C) : C) * wordCoeff F b.2)).prod =
      star (u : C) * (v.map (conjugateMomentBlock F u)).prod := by
  induction v with
  | nil => simp [conjugateMomentTail, wordCoeff, ← Unitary.star_eq_inv]
  | cons p v ih =>
    simp only [conjugateMomentTail, List.map_cons, List.prod_cons, wordCoeff_some,
      zpow_neg_one, zpow_one, ← Unitary.star_eq_inv, Unitary.coe_star, ih,
      conjugateMomentBlock, mul_assoc]

end KadisonSimilarity

end

end OAI
end


