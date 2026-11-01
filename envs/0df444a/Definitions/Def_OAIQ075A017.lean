-- Prove2me | Definitions.Def_OAIQ075A017
-- name    : OAIQ075A017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:14:55.264903+00:00
-- url     : https://prove2.me/theorems/4e658361-a7b7-47e5-91d1-1c9697bd66c5
-- title:
--   Definitions bundle OAIQ075A017 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 115 declarations of OpenAI's Lean: 43 definitions, 2 inductive types or structures, 2 instances and 68 theorems. The definitions and types are `OAI.KadisonSimilarity.NormalFiniteTrace`, `OAI.KadisonSimilarity.PaulsenSimilarityInput`, `OAI.KadisonSimilarity.PublishedDerivationInputs`, `OAI.KadisonSimilarity.SourcePartialUnitary.map`, `OAI.KadisonSimilarity.ThielDiffuseCornerHaarInput`, `OAI.KadisonSimilarity.algebraSequenceVector`, `OAI.KadisonSimilarity.algebraSequenceVectorLinear`, `OAI.KadisonSimilarity.commonCentralField`, `OAI.KadisonSimilarity.commonCommutantField`, `OAI.KadisonSimilarity.commonFieldCompression`, `OAI.KadisonSimilarity.commonScalarRepresentation`, `OAI.KadisonSimilarity.concreteTraceLinear`, `OAI.KadisonSimilarity.copyEmbedding`, `OAI.KadisonSimilarity.copyRestriction`, `OAI.KadisonSimilarity.crossPairingOperator`, `OAI.KadisonSimilarity.cyclicCommonEmbedding`, `OAI.KadisonSimilarity.cyclicCommonEmbeddingData`, `OAI.KadisonSimilarity.cyclicCommonFamily`, `OAI.KadisonSimilarity.cyclicCommonFamilyData`, `OAI.KadisonSimilarity.cyclicDecompositionData`, `OAI.KadisonSimilarity.cyclicDensityIsometry`, `OAI.KadisonSimilarity.cyclicDensityIsometryData`, `OAI.KadisonSimilarity.cyclicGraph`, `OAI.KadisonSimilarity.cyclicSpectralSummands`, `OAI.KadisonSimilarity.endpointCompression`, `OAI.KadisonSimilarity.endpointMatchingClassEquiv`, `OAI.KadisonSimilarity.endpointMatchingEquiv`, `OAI.KadisonSimilarity.endpointTailMatching`, `OAI.KadisonSimilarity.endpointTracialCoefficient`, `OAI.KadisonSimilarity.finiteOrbitMap`, `OAI.KadisonSimilarity.finiteOrbitSubspace`, `OAI.KadisonSimilarity.fullColumnCoordinatesOfColumns`, `OAI.KadisonSimilarity.linearMatrixTrace`, `OAI.KadisonSimilarity.pairRepresentation`, `OAI.KadisonSimilarity.partialIsometryColumns`, `OAI.KadisonSimilarity.predualRestriction`, `OAI.KadisonSimilarity.quotientGNSVector`, `OAI.KadisonSimilarity.quotientPreGNSIsometry`, `OAI.KadisonSimilarity.realTupleOrbitMap`, `OAI.KadisonSimilarity.selfAdjointSymmetryDilation` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonSimilarity_Derivation_CommonCyclicEmbedding`, `KadisonSimilarity_Derivation_CommonCyclicIntertwining`, `KadisonSimilarity_Derivation_CyclicDecomposition`, `KadisonSimilarity_Derivation_CyclicGraphEmbedding`, `KadisonSimilarity_Derivation_CyclicSpectralSum`, `KadisonSimilarity_Derivation_FinalDerivations`, `KadisonSimilarity_FreeProduct_CommonFieldCompression`, `KadisonSimilarity_FreeProduct_SmallFreeCornerData`, `KadisonSimilarity_FreeProduct_TracialSymmetryDilation`, `KadisonSimilarity_Representation_CommonCentralData`, `KadisonSimilarity_Representation_CommonCommutantFields`, `KadisonSimilarity_Representation_CommonSpectralCommutant`, `KadisonSimilarity_Representation_ConcretePredualRestriction`, `KadisonSimilarity_Representation_CountableProjectionJoin`, `KadisonSimilarity_Representation_FiniteOrbitSubspace`, `KadisonSimilarity_Representation_FiniteTypeIStructure`, `KadisonSimilarity_Representation_KaplanskySelfAdjoint`, `KadisonSimilarity_Representation_ProperlyInfiniteStructure`, `KadisonSimilarity_Representation_SelfAdjointStrongDensity`, `KadisonSimilarity_Representation_SquareArrayPadding`, `KadisonSimilarity_Similarity_CompletelyBounded`, `KadisonSimilarity_Tensor_EndpointDensity`, `KadisonSimilarity_Tensor_EndpointPairings`, `KadisonSimilarity_Tensor_EndpointTensors`, `KadisonSimilarity_Tensor_TensorClassification`, `KadisonSimilarity_Tracial_BoundedMatrixHom`, `KadisonSimilarity_Tracial_ConcreteHalfProjection`, `KadisonSimilarity_Tracial_CornerTraceScaling`, `KadisonSimilarity_Tracial_DenseMomentExtension`, `KadisonSimilarity_Tracial_FiniteFactorPresentation`, `KadisonSimilarity_Tracial_FiniteFactorTrace`, `KadisonSimilarity_Tracial_IsometricMatrixExtension`, `KadisonSimilarity_Tracial_MatrixCornerFrames`, `KadisonSimilarity_Tracial_MatrixStageGrowth`, `KadisonSimilarity_Tracial_MatrixUnitCoordinates`, `KadisonSimilarity_Tracial_RelativeMatrixQuantization`, `KadisonSimilarity_Tracial_SourceCornerQuantization`, `KadisonSimilarity_Tracial_SourcePartialUnitaries`, `KadisonSimilarity_Tracial_SourceQuotientMoments`, `KadisonSimilarity_Tracial_TracialCornerTransport`, `KadisonSimilarity_Tracial_TracialMomentContinuity`, `KadisonSimilarity_Tracial_TracialUltrapowerGNS`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A007`, `OAIQ075A008`, `OAIQ075A009`, `OAIQ075A010`, `OAIQ075A011` and `OAIQ075A012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A023`, `OAIQ075A024` and `OAIQ075A025`; the statements `OAI.KadisonSimilarity.ae_common_projection_rankOne_mem`, `OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv` and `OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable`; the proof of `OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A007
import Definitions.Def_OAIQ075A008
import Definitions.Def_OAIQ075A009
import Definitions.Def_OAIQ075A010
import Definitions.Def_OAIQ075A011
import Definitions.Def_OAIQ075A012

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- The quantitative published Paulsen input, specialized to a single
bounded unital homomorphism. Paulsen, *Completely bounded homomorphisms of
operator algebras* (1984), p. 226. It is an explicit hypothesis interface. -/
def PaulsenSimilarityInput (π : BoundedUnitalHom A H) : Prop :=
  ∀ C : ℝ, 0 ≤ C → CompleteBound π.1 C →
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ C ∧
      ∀ a : A, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))

end CompletelyBounded

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem cyclicOrbitOrthogonal_symm (N : StarSubalgebra ℂ (H →L[ℂ] H)) {ξ η : H}
    (h : CyclicOrbitOrthogonal N ξ η) : CyclicOrbitOrthogonal N η ξ := by
  intro x hx y hy
  exact inner_eq_zero_symm.mp (h y hy x hx)

theorem orbitClosure_le_cyclicFamilySpan (N : StarSubalgebra ℂ (H →L[ℂ] H))
    {S : Set H} {ξ : H} (hξ : ξ ∈ S) : (orbitClosure N ξ).toSubmodule ≤ cyclicFamilySpan N S := by
  intro x hx
  apply Submodule.subset_span
  exact Set.mem_iUnion.mpr ⟨ξ, Set.mem_iUnion.mpr ⟨hξ, hx⟩⟩

theorem exists_maximal_orthogonalCyclicFamily (N : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ∃ S : Set H, Maximal (OrthogonalCyclicFamily N) S := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c, ?_, ?_⟩
  · constructor
    · intro ξ hξ
      obtain ⟨S, hS, hξ⟩ := Set.mem_sUnion.mp hξ
      exact (hc hS).1 ξ hξ
    · exact hchain.pairwise_sUnion.mpr (fun S hS => (hc hS).2)
  · intro S hS
    exact Set.subset_sUnion_of_mem hS

/-- Maximality forces density: any nonzero vector in the orthogonal
complement would supply an additional orthogonal cyclic summand. -/
theorem maximal_orthogonalCyclicFamily_dense
    (N : StarSubalgebra ℂ (H →L[ℂ] H)) {S : Set H}
    (hS : Maximal (OrthogonalCyclicFamily N) S) :
    (cyclicFamilySpan N S).topologicalClosure = ⊤ := by
  classical
  let M := (cyclicFamilySpan N S).closure
  change M.toSubmodule = ⊤
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro ξ hξ
  change ξ = 0
  by_contra hne
  have hξold (η : H) (hη : η ∈ S) :
      ξ ∈ (orbitClosure N η).toSubmodule.orthogonal := by
    apply Submodule.orthogonal_le (show (orbitClosure N η).toSubmodule ≤ M.toSubmodule from
      (orbitClosure_le_cyclicFamilySpan N hη).trans (Submodule.le_topologicalClosure _))
    exact hξ
  have hnew (η : H) (hη : η ∈ S) : CyclicOrbitOrthogonal N ξ η := by
    intro x hx y hy
    exact inner_eq_zero_symm.mp (orbitClosure_le_orthogonal N ξ η (hξold η hη) hx y hy)
  have hnot : ξ ∉ S := by
    intro hmem
    exact hne (inner_self_eq_zero.mp (hnew ξ hmem ξ (self_mem_orbitClosure N ξ)
      ξ (self_mem_orbitClosure N ξ)))
  have hins : OrthogonalCyclicFamily N (insert ξ S) := by
    constructor
    · intro η hη
      rcases Set.mem_insert_iff.mp hη with rfl | hη
      · exact hne
      · exact hS.prop.1 η hη
    · intro η hη ζ hζ hηζ
      rcases Set.mem_insert_iff.mp hη with hηeq | hηS
      · rcases Set.mem_insert_iff.mp hζ with hζeq | hζS
        · exact (hηζ (hηeq.trans hζeq.symm)).elim
        · simpa only [hηeq] using hnew ζ hζS
      · rcases Set.mem_insert_iff.mp hζ with hζeq | hζS
        · simpa only [hζeq] using cyclicOrbitOrthogonal_symm N (hnew η hηS)
        · exact hS.prop.2 hηS hζS hηζ
  have heq : S = insert ξ S := hS.eq_of_subset hins (Set.subset_insert ξ S)
  exact hnot (heq.symm ▸ Set.mem_insert ξ S)

def cyclicDecompositionData (N : StarSubalgebra ℂ (H →L[ℂ] H)) : CyclicDecompositionData N := by
  let S := (exists_maximal_orthogonalCyclicFamily N).choose
  have hS := (exists_maximal_orthogonalCyclicFamily N).choose_spec
  exact ⟨S, hS.prop.1, hS.prop.2, maximal_orthogonalCyclicFamily_dense N hS⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialSymmetryDilation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- The normalized two-by-two matrix extension of a linear functional. -/
def linearMatrixTrace (τ : A →ₗ[ℂ] ℂ) : Mat A →ₗ[ℂ] ℂ where
  toFun X := (τ (X 0 0) + τ (X 1 1)) / 2
  map_add' X Y := by simp only [CStarMatrix.add_apply, map_add]; ring
  map_smul' c X := by
    simp only [CStarMatrix.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem linearMatrixTrace_apply (τ : A →ₗ[ℂ] ℂ) (X : Mat A) :
    linearMatrixTrace τ X = (τ (X 0 0) + τ (X 1 1)) / 2 := rfl

variable [PartialOrder A] [StarOrderedRing A]

attribute [local instance] OAI.KadisonSimilarity.instNonUnitalContinuousFunctionalCalculusRealIsSelfAdjoint_solutions
attribute [local instance] OAI.KadisonSimilarity.instNonnegSpectrumClassReal_solutions
/-- The two-by-two symmetry associated to a selfadjoint contraction. -/
def selfAdjointSymmetryDilation (a : A) : Mat A :=
  diag (CFC.sqrt (1 - a ^ 2)) (-CFC.sqrt (1 - a ^ 2)) + offdiag a a

@[simp] theorem selfAdjointSymmetryDilation_entry (a : A) :
    selfAdjointSymmetryDilation a 0 1 = a := by
  simp [selfAdjointSymmetryDilation, diag, offdiag]

theorem selfAdjointSymmetryDilation_star (a : A) (ha : IsSelfAdjoint a) :
    star (selfAdjointSymmetryDilation a) = selfAdjointSymmetryDilation a := by
  have hr := (CFC.sqrt_nonneg (1 - a ^ 2)).isSelfAdjoint.star_eq
  simp only [selfAdjointSymmetryDilation, star_add, star_diag, star_offdiag,
    star_neg, hr, ha.star_eq]

theorem selfAdjointSymmetryDilation_sq (a : A) (ha : IsSelfAdjoint a) (hn : ‖a‖ ≤ 1) :
    selfAdjointSymmetryDilation a * selfAdjointSymmetryDilation a = 1 := by
  have hr := CFC.sqrt_mul_sqrt_self (1 - a ^ 2) (selfAdjoint_defect_nonneg a ha hn)
  have hc := (selfAdjoint_defect_sqrt_commutes a).eq
  simp only [pow_two] at hr hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [selfAdjointSymmetryDilation, CStarMatrix.mul_apply, Fin.sum_univ_two,
      diag, offdiag, hr, hc, pow_two]

/-- The symmetry as an actual unitary, with no existence assumption. -/
def selfAdjointSymmetryUnitary (a : A) (ha : IsSelfAdjoint a) (hn : ‖a‖ ≤ 1) :
    unitary (Mat A) :=
  ⟨selfAdjointSymmetryDilation a, by
    rw [Unitary.mem_iff]
    simp only [selfAdjointSymmetryDilation_star a ha, selfAdjointSymmetryDilation_sq a ha hn,
      and_self]⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SquareArrayPadding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

theorem copyEmbeddingMap_apply_of_not_mem (e : Fin r ↪ Fin m)
    (x : HilbertCopies H r) (j : Fin m) (hj : j ∉ Set.range e) :
    copyEmbeddingMap e x j = 0 := by
  have hji (i : Fin r) : j ≠ e i := by
    intro h
    exact hj ⟨i, h.symm⟩
  simp [copyEmbeddingMap, hji]

@[simp] theorem norm_copyEmbeddingMap (e : Fin r ↪ Fin m) (x : HilbertCopies H r) :
    ‖copyEmbeddingMap e x‖ = ‖x‖ := by
  have hs : ‖copyEmbeddingMap e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    calc
      ∑ j : Fin m, ‖copyEmbeddingMap e x j‖ ^ 2 =
          ∑ j ∈ Finset.univ.map e, ‖copyEmbeddingMap e x j‖ ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        have hj' : j ∉ Set.range e := by
          rintro ⟨i, rfl⟩
          exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        rw [copyEmbeddingMap_apply_of_not_mem e x j hj']
        simp
      _ = ∑ i : Fin r, ‖x i‖ ^ 2 := by
        simp only [Finset.sum_map, copyEmbeddingMap_apply_image]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

/-- Zero extension, now bundled as a linear isometry. -/
def copyEmbedding (e : Fin r ↪ Fin m) :
    HilbertCopies H r →ₗᵢ[ℂ] HilbertCopies H m where
  toLinearMap := (copyEmbeddingMap e).toLinearMap
  norm_map' := norm_copyEmbeddingMap e

@[simp] theorem copyEmbedding_toContinuousLinearMap (e : Fin r ↪ Fin m) :
    (copyEmbedding (H := H) e).toContinuousLinearMap = copyEmbeddingMap e := rfl

/-- Restriction to the coordinates in the image of the injection. -/
def copyRestriction (e : Fin r ↪ Fin m) :
    HilbertCopies H m →L[ℂ] HilbertCopies H r :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => PiLp.proj 2 (fun _ : Fin m => H) (e i))

@[simp] theorem copyRestriction_apply (e : Fin r ↪ Fin m)
    (x : HilbertCopies H m) (i : Fin r) : copyRestriction e x i = x (e i) := by
  simp [copyRestriction]

@[simp] theorem copyRestriction_copyEmbedding (e : Fin r ↪ Fin m) :
    (copyRestriction (H := H) e).comp (copyEmbeddingMap e) =
      ContinuousLinearMap.id ℂ (HilbertCopies H r) := by
  ext x i
  simp

end Coordinates

section MatrixMultiplicities

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

theorem mapCopies_comp_eq {E F K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (S : F →L[ℂ] K) (T : E →L[ℂ] F) (n : ℕ) :
    mapCopies (S.comp T) n = (mapCopies S n).comp (mapCopies T n) := by
  ext x i
  simp

@[simp] theorem mapCopies_id_eq (n : ℕ) :
    mapCopies (ContinuousLinearMap.id ℂ H) n =
      ContinuousLinearMap.id ℂ (HilbertCopies H n) := by
  ext x i
  simp

end MatrixMultiplicities

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From finite-stage pairings to permutation operators

The operator classification follows from the finite-stage coefficient
identity, using density, same-side-pair elimination, and completed tensor
permutations. The finite-stage identity remains a separately stated prerequisite.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The explicit finite sum of the operators indexed by cross pairings. -/
def crossPairingOperator {n : ℕ}
    (c : PerfectMatching (Fin n ⊕ Fin n) → ℂ) :
    CompletedTensorWord E n →L[ℂ] CompletedTensorWord E n :=
  ∑ P : {P : PerfectMatching (Fin n ⊕ Fin n) // IsCrossPairing P.1},
    c P.1 • (completedTensorPermutation
      (crossPairingEquiv P.1.1 P.1.2.1 P.2)).toContinuousLinearMap

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointTensors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Completed tensor words with an unrestricted first endpoint

The endpoint and the centered tail may live in different Hilbert spaces.
Their completed tensor product has total elementary words and carries
the operators `I ⊗ A` and endpoint slices.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Endpoint words are total in the completed endpoint tensor product. -/
theorem endpointWord_mem_closed_submodule {n : ℕ}
    (S : Submodule ℂ (EndpointTensor E F n)) (hclosed : IsClosed (S : Set (EndpointTensor E F n)))
    (hword : ∀ d x, endpointWord d x ∈ S) (z : EndpointTensor E F n) : z ∈ S := by
  unfold EndpointTensor HilbertTensor at *
  have hpair (d : E) (w : CompletedTensorWord F n) : endpointInsert d w ∈ S := by
    let T : Submodule ℂ (CompletedTensorWord F n) := S.comap (endpointInsert (F := F) (n := n) d).toLinearMap
    apply completedTensorWord_mem_closed_submodule T
      (hclosed.preimage (endpointInsert d).continuous) (hword d) w
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | tmul d w => exact hpair d w
    | add x y hx hy =>
      change ((x + y : E ⊗[ℂ] CompletedTensorWord F n) : EndpointTensor E F n) ∈ S
      rw [UniformSpace.Completion.coe_add]
      exact S.add_mem hx hy

/-- Continuous linear maps on endpoint words are determined by elementary words. -/
theorem continuousLinearMap_ext_endpointWords {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] {n : ℕ}
    (f g : EndpointTensor E F n →L[ℂ] G)
    (hword : ∀ d x, f (endpointWord d x) = g (endpointWord d x)) : f = g := by
  let S : Submodule ℂ (EndpointTensor E F n) := (f - g).ker
  have hmem (z : EndpointTensor E F n) : z ∈ S := by
    apply endpointWord_mem_closed_submodule S (f - g).isClosed_ker ?_ z
    intro d x
    exact sub_eq_zero.mpr (hword d x)
  ext z
  exact sub_eq_zero.mp (hmem z)

variable {E' F' : Type*}
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- Compress the endpoint of a bounded operator to the chosen trace vector. -/
def endpointCompression {k l : ℕ} (Ω : E)
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) :
    CompletedTensorWord F k →L[ℂ] CompletedTensorWord F l :=
  (tensorSlice Ω).comp (Y.comp (endpointInsert Ω))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointPairings
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.crossPairingEquiv_left _root_.OAI.KadisonSimilarity.crossPairingEquiv_right _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorization of matrix contractions along pairs

This is the finite combinatorial bridge between the cycle expansion and the
bilinear pairing polynomials: each two-cycle contributes exactly one trace of
a product. The normalization uses the actual number of matching orbits.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

omit [DecidableEq ι] in
/-- The orbit of an involution consists of the point and its partner, allowing
also the fixed-point case used for the endpoint. -/
theorem sameCycle_involutive_iff (π : Equiv.Perm ι) (hπ : Function.Involutive π)
    (i j : ι) : π.SameCycle i j ↔ j = i ∨ j = π i := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h
      · exact Or.inr (congrArg π h)
      · exact Or.inl ((congrArg π h).trans (hπ i))
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, by simp⟩

/-- The endpoint supplies one additional singleton orbit. -/
def endpointMatchingClassEquiv (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) :
    Option (MatchingRepresentatives rank P) ≃ PermutationCycles (endpointMatching P) :=
  Equiv.ofBijective (fun i => (⟦Option.map Subtype.val i⟧ :
    PermutationCycles (endpointMatching P))) (by
    constructor
    · intro i j hij
      let u : Option (MatchingRepresentatives rank P) → Option ι := Option.map Subtype.val
      change (⟦u i⟧ : PermutationCycles (endpointMatching P)) = ⟦u j⟧ at hij
      have hc := (sameCycle_involutive_iff (endpointMatching P)
        (endpointMatching_involutive P) (u i) (u j)).mp (Quotient.exact hij)
      cases i with
      | none =>
        cases j with
        | none => rfl
        | some j => rcases hc with h | h <;> cases h
      | some i =>
        cases j with
        | none => rcases hc with h | h <;> cases h
        | some j =>
          rcases hc with h | h
          · exact congrArg some (Subtype.ext (Option.some.inj h).symm)
          · have heq : j.val = P.1 i.val := Option.some.inj h
            have hi := i.property
            have hj := j.property
            rw [heq, P.2.1] at hj
            omega
    · intro q
      induction q using Quotient.inductionOn with
      | h i =>
        cases i with
        | none => exact ⟨none, rfl⟩
        | some i =>
          by_cases hi : rank i < rank (P.1 i)
          · exact ⟨some ⟨i, hi⟩, rfl⟩
          · have hne := matching_rank_ne rank hrank P i
            have hpi : rank (P.1 i) < rank (P.1 (P.1 i)) := by rw [P.2.1]; omega
            refine ⟨some ⟨P.1 i, hpi⟩, Quotient.sound ?_⟩
            apply (sameCycle_involutive_iff (endpointMatching P)
              (endpointMatching_involutive P) _ _).mpr
            exact Or.inr (congrArg some (P.2.1 i).symm))

/-- Remove the distinguished fixed endpoint from a surviving permutation. -/
def endpointTailMatching (π : Equiv.Perm (Option ι)) (hπ : EndpointPairing π none) :
    PerfectMatching ι :=
  ⟨π.removeNone, by
    have hs (i : ι) : some (π.removeNone i) = π (some i) :=
      π.removeNone_some (optionPerm_some π hπ.1 i)
    constructor
    · intro i
      apply Option.some.inj
      calc
        some (π.removeNone (π.removeNone i)) = π (some (π.removeNone i)) := hs _
        _ = π (π (some i)) := congrArg π (hs i)
        _ = some i := hπ.2.1 _
    · intro i hi
      have hfix : π (some i) = some i := (hs i).symm.trans (congrArg some hi)
      exact Option.some_ne_none i (hπ.2.2 (some i) hfix)⟩

omit [Fintype ι] [DecidableEq ι] in
theorem endpointMatching_tail (π : Equiv.Perm (Option ι)) (hπ : EndpointPairing π none) :
    endpointMatching (endpointTailMatching π hπ) = π := by
  apply Equiv.ext
  intro i
  cases i with
  | none => exact hπ.1.symm
  | some i => exact π.removeNone_some (optionPerm_some π hπ.1 i)

/-- Surviving permutations are in bijection with tail matchings. -/
def endpointMatchingEquiv : PerfectMatching ι ≃
    {π : Equiv.Perm (Option ι) // EndpointPairing π none} :=
  Equiv.ofBijective (fun P => ⟨endpointMatching P, endpointMatching_isEndpointPairing P⟩) (by
    constructor
    · intro P Q heq
      apply Subtype.ext
      apply Equiv.ext
      intro i
      exact Option.some.inj (congrArg (fun π => π.val (some i)) heq)
    · intro π
      exact ⟨endpointTailMatching π.val π.property, Subtype.ext (endpointMatching_tail _ _)⟩)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem endpointMatchingEquiv_apply (P : PerfectMatching ι) :
    (endpointMatchingEquiv P).val = endpointMatching P := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicSpectralSum
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

attribute [local instance] OAI.KadisonSimilarity.spectralSumMeasurable
local instance spectralSumBorel_r86f838_1 : BorelSpace (WeakDual.characterSpace ℂ A) := ⟨rfl⟩
def cyclicSpectralSummands : OrthogonalSummandDecomposition (CyclicSpectralSpace π D) H where
  inclusion i := commutativeCyclicIsometry π (i : H)
  orthogonal i j hij x y := by
    apply D.orthogonal i.property j.property (fun h => hij (Subtype.ext h))
    · have hx := Set.mem_range_self (f := commutativeCyclicIsometry π (i : H)) x
      rw [cyclic_spectral_range π] at hx
      exact hx
    · have hy := Set.mem_range_self (f := commutativeCyclicIsometry π (j : H)) y
      rw [cyclic_spectral_range π] at hy
      exact hy
  dense_span := by
    change (Submodule.span ℂ (⋃ i : D.generators,
      Set.range (commutativeCyclicIsometry π (i : H)))).topologicalClosure = ⊤
    have hs : (⋃ i : D.generators,
        Set.range (commutativeCyclicIsometry π (i : H))) =
        ⋃ ξ ∈ D.generators, (orbitClosure π.range ξ : Set H) := by
      simp only [cyclic_spectral_range π, Set.iUnion_coe_set]
    rw [hs]
    exact D.dense_span

theorem cyclicSpectral_isHilbertSum : IsHilbertSum ℂ (CyclicSpectralSpace π D)
    (cyclicSpectralSummands π D).inclusion := by
  apply IsHilbertSum.mk (cyclicSpectralSummands π D).orthogonal
  have heq : (⨆ i, LinearMap.range ((cyclicSpectralSummands π D).inclusion i).toLinearMap) =
      Submodule.span ℂ (⋃ i, Set.range ((cyclicSpectralSummands π D).inclusion i)) := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      rintro x ⟨y, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, y, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      intro x hx
      obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
      exact Submodule.mem_iSup_of_mem i ⟨y, rfl⟩
  rw [heq, (cyclicSpectralSummands π D).dense_span]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CommonCyclicEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

attribute [local instance] OAI.KadisonSimilarity.commonCyclicMeasurable
attribute [local instance] OAI.KadisonSimilarity.commonCyclicBorel
attribute [local instance] OAI.KadisonSimilarity.commonCyclicCountable
instance cyclicCommonBaseMeasure_finite : IsFiniteMeasure (cyclicCommonBaseMeasure π D) :=
  inferInstanceAs (IsFiniteMeasure (commonSpectralMeasure
    (fun i : D.generators => commutativeVectorMeasure π (i : H))))

instance cyclicCommonBaseMeasure_regular [TopologicalSpace.SeparableSpace A] :
    (cyclicCommonBaseMeasure π D).Regular := by
  let : TopologicalSpace.MetrizableSpace (WeakDual.characterSpace ℂ A) :=
    characterSpace_metrizable A
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def cyclicDensityIsometryData (i : D.generators) :
    {J : CyclicSpectralSpace π D i →ₗᵢ[ℂ] Lp ℂ 2 (cyclicCommonBaseMeasure π D) //
      ∀ (f : C(WeakDual.characterSpace ℂ A, ℂ)) (ξ : CyclicSpectralSpace π D i),
        J (continuousL2Mul (commutativeVectorMeasure π (i : H)) f ξ) =
          continuousL2Mul (cyclicCommonBaseMeasure π D) f (J ξ)} :=
  spectralDensityIntertwinerData (cyclicCommonBaseMeasure π D)
    (commutativeVectorMeasure π (i : H))
    (squareRootDensity (cyclicCommonBaseMeasure π D) (commutativeVectorMeasure π (i : H)))
    (squareRootDensity_measurable _ _)
    (squareRootDensity_memLp _ _ (component_absolutelyContinuous_common
      (fun j : D.generators => commutativeVectorMeasure π (j : H)) i))
    (squaredDensityMeasure_eq _ _ (component_absolutelyContinuous_common
      (fun j : D.generators => commutativeVectorMeasure π (j : H)) i))

def cyclicDensityIsometry (i : D.generators) : CyclicSpectralSpace π D i →ₗᵢ[ℂ]
    Lp ℂ 2 (cyclicCommonBaseMeasure π D) := (cyclicDensityIsometryData π D i).val

attribute [irreducible] cyclicDensityIsometryData cyclicDensityIsometry

def cyclicCommonFamilyData (i : D.generators) :
    {J : CyclicSpectralSpace π D i →ₗᵢ[ℂ] CommonCyclicHilbert π D //
      ∀ (f : C(WeakDual.characterSpace ℂ A, ℂ)) (ξ : CyclicSpectralSpace π D i),
        J (continuousL2Mul (commutativeVectorMeasure π (i : H)) f ξ) =
          VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) f (J ξ)} := by
  classical
  exact coordinateIntertwinerData (cyclicCommonBaseMeasure π D)
    (commutativeVectorMeasure π (i : H)) (scalarCoordinateIsometry i)
    (cyclicDensityIsometryData π D i)

def cyclicCommonFamily (i : D.generators) : CyclicSpectralSpace π D i →ₗᵢ[ℂ]
    CommonCyclicHilbert π D := (cyclicCommonFamilyData π D i).val

theorem cyclicCommonFamily_orthogonal : OrthogonalFamily ℂ (CyclicSpectralSpace π D)
    (cyclicCommonFamily π D) := by
  classical
  change OrthogonalFamily ℂ _ (fun i =>
    (l2CoordinateIsometry (cyclicCommonBaseMeasure π D) i).comp
      (cyclicDensityIsometryData π D i).val)
  exact orthogonalFamily_comp_isometries _ (l2Coordinate_orthogonal _)
    (fun i => (cyclicDensityIsometryData π D i).val)

opaque cyclicCommonEmbeddingData :
    {J : H →ₗᵢ[ℂ] CommonCyclicHilbert π D //
      ∀ (i : D.generators) (ξ : CyclicSpectralSpace π D i),
        J ((cyclicSpectralSummands π D).inclusion i ξ) = cyclicCommonFamily π D i ξ} :=
  hilbertSumTransportWithComponents (cyclicSpectralSummands π D).inclusion
    (cyclicSpectral_isHilbertSum π D) (cyclicCommonFamily π D)
    (cyclicCommonFamily_orthogonal π D)

def cyclicCommonEmbedding : H →ₗᵢ[ℂ] CommonCyclicHilbert π D :=
  (cyclicCommonEmbeddingData π D).val

theorem cyclicCommonEmbedding_component (i : D.generators) (ξ : CyclicSpectralSpace π D i) :
    cyclicCommonEmbedding π D ((cyclicSpectralSummands π D).inclusion i ξ) =
      cyclicCommonFamily π D i ξ :=
  (cyclicCommonEmbeddingData π D).property i ξ

attribute [irreducible] cyclicCommonFamilyData cyclicCommonFamily cyclicCommonEmbedding

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CommonCyclicIntertwining
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common scalar spectral embedding intertwines the original abelian
representation with actual scalar multiplication. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

theorem cyclicCommonFamily_intertwines (i : D.generators)
    (f : C(WeakDual.characterSpace ℂ A, ℂ)) (ξ : CyclicSpectralSpace π D i) :
    cyclicCommonFamily π D i (continuousL2Mul (commutativeVectorMeasure π (i : H)) f ξ) =
      VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) f (cyclicCommonFamily π D i ξ) := by
  unfold cyclicCommonFamily
  exact (cyclicCommonFamilyData π D i).property f ξ

theorem cyclicCommonEmbedding_intertwines (a : A) (x : H) :
    cyclicCommonEmbedding π D (π a x) =
      VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) (gelfandStarTransform A a)
        (cyclicCommonEmbedding π D x) := by
  have hdense : Dense (Submodule.span ℂ
      (⋃ i, Set.range ((cyclicSpectralSummands π D).inclusion i)) : Set H) := by
    intro y
    change y ∈ (Submodule.span ℂ
      (⋃ i, Set.range ((cyclicSpectralSummands π D).inclusion i))).topologicalClosure
    rw [(cyclicSpectralSummands π D).dense_span]
    trivial
  have hS (i : D.generators) (ξ : CyclicSpectralSpace π D i) :
      π a ((cyclicSpectralSummands π D).inclusion i ξ) =
        (cyclicSpectralSummands π D).inclusion i
          (continuousL2Mul (commutativeVectorMeasure π (i : H)) (gelfandStarTransform A a) ξ) := by
    change π a (commutativeCyclicIsometry π (i : H) ξ) =
      commutativeCyclicIsometry π (i : H)
        (continuousL2Mul (commutativeVectorMeasure π (i : H)) (gelfandStarTransform A a) ξ)
    exact (commutativeCyclicIsometry_intertwines π (i : H) a ξ).symm
  have hsubset : (Submodule.span ℂ
      (⋃ i, Set.range ((cyclicSpectralSummands π D).inclusion i)) : Set H) ⊆
      {y | cyclicCommonEmbedding π D (π a y) =
        VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) (gelfandStarTransform A a)
          (cyclicCommonEmbedding π D y)} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, ξ, rfl⟩ := Set.mem_iUnion.mp hy
        change cyclicCommonEmbedding π D (π a ((cyclicSpectralSummands π D).inclusion i ξ)) = _
        rw [hS, cyclicCommonEmbedding_component, cyclicCommonEmbedding_component]
        exact cyclicCommonFamily_intertwines π D i (gelfandStarTransform A a) ξ
    | zero => simp
    | add y z _ _ hy hz =>
        simp only [Set.mem_ofPred_eq] at hy hz ⊢
        simp only [map_add, hy, hz]
    | smul c y _ hy =>
        simp only [Set.mem_ofPred_eq] at hy ⊢
        simp only [map_smul, hy]
  have hclosed : IsClosed {y | cyclicCommonEmbedding π D (π a y) =
      VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) (gelfandStarTransform A a)
        (cyclicCommonEmbedding π D y)} :=
    isClosed_eq ((cyclicCommonEmbedding π D).continuous.comp (π a).continuous)
      ((VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D)
        (gelfandStarTransform A a)).continuous.comp (cyclicCommonEmbedding π D).continuous)
  exact closure_minimal hsubset hclosed (hdense x)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicGraphEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closable cyclic orbit map gives an isometric subrepresentation. The
closed graph is itself a cyclic reducing representation, and its two
coordinate maps yield the embedding by polar decomposition. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Direct sum of two star representations, with the Hilbert product norm. -/
def pairRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    A →⋆ₐ[ℂ] (RectangularSum H K →L[ℂ] RectangularSum H K) where
  toAlgHom := (rectangularRepresentation σ ρ 0 (by simp)).1
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ y (rectangularTriangular (σ (star a)) 0 (ρ (star a)) x) =
      inner ℂ y ((rectangularTriangular (σ a) 0 (ρ a)).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ y.fst (rectangularTriangular (σ (star a)) 0 (ρ (star a)) x).fst +
        inner ℂ y.snd (rectangularTriangular (σ (star a)) 0 (ρ (star a)) x).snd =
      inner ℂ (rectangularTriangular (σ a) 0 (ρ a) y).fst x.fst +
        inner ℂ (rectangularTriangular (σ a) 0 (ρ a) y).snd x.snd
    simp only [rectangularTriangular_fst,
      rectangularTriangular_snd, zero_apply, add_zero, map_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

@[simp] theorem pairRepresentation_fst (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : A) (x : RectangularSum H K) :
    (pairRepresentation σ ρ a x).fst = σ a x.fst := by
  change (rectangularTriangular (σ a) 0 (ρ a) x).fst = _
  simp only [rectangularTriangular_fst, zero_apply, add_zero]

@[simp] theorem pairRepresentation_snd (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : A) (x : RectangularSum H K) :
    (pairRepresentation σ ρ a x).snd = ρ a x.snd :=
  rectangularTriangular_snd _ _ _ _

/-- The closed cyclic graph of the orbit map `σ(a)Ω ↦ ρ(a)ξ`. -/
def cyclicGraph (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : H) (ξ : K) :=
  orbitClosure (pairRepresentation σ ρ).range (WithLp.toLp 2 (Ω, ξ))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SelfAdjointStrongDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selfadjoint strong density in the bicommutant. The real orbit is tested
against its orthogonal complement; adjoints only occur in scalar products. -/
noncomputable section
namespace KadisonSimilarity
open Filter ContinuousLinearMap
open scoped Topology BigOperators

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype ι]

def realTupleOrbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : Generator.FiniteHilbert ι H) : S →ₗ[ℝ] Generator.FiniteHilbert ι H where
  toFun a := Generator.diagonalOperator (symmetrize a.val) x
  map_add' a b := by
    apply PiLp.ext
    intro i
    change (1 / 2 : ℝ) • (((a : H →L[ℂ] H) + b + star ((a : H →L[ℂ] H) + b)) (x i)) = _
    simp only [star_add, add_apply, smul_apply, PiLp.add_apply,
      Generator.diagonalOperator_apply, symmetrize]
    module
  map_smul' c a := by
    apply PiLp.ext
    intro i
    change (1 / 2 : ℝ) • (((c • (a : H →L[ℂ] H)) + star (c • (a : H →L[ℂ] H))) (x i)) =
      c • ((1 / 2 : ℝ) • (((a : H →L[ℂ] H) + star (a : H →L[ℂ] H)) (x i)))
    simp only [star_smul, star_trivial, smul_apply, add_apply]
    module

/-- Simultaneous approximation of a selfadjoint bicommutant element by
selfadjoint elements of the original star algebra, without a norm bound. -/
theorem selfAdjoint_bicommutant_tuple_mem_closure
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hTs : IsSelfAdjoint T) (x : Generator.FiniteHilbert ι H) :
    Generator.diagonalOperator T x ∈ (realTupleOrbitMap S x).range.topologicalClosure := by
  classical
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro y hy
  obtain ⟨a, ha⟩ := Generator.bicommutant_exists_strong_net S T hT
  have hlim (i : ι) : Tendsto
      (fun d => inner ℝ (symmetrize (a d).val (x i)) (y i)) atTop
      (𝓝 (inner ℝ (T (x i)) (y i))) := by
    have h₁ := (ha (x i)).inner (𝕜 := ℝ) (tendsto_const_nhds (x := y i))
    have h₂ := (tendsto_const_nhds (x := x i)).inner (𝕜 := ℝ) (ha (y i))
    have hadj (A : H →L[ℂ] H) :
        inner ℝ (star A (x i)) (y i) = inner ℝ (x i) (A (y i)) := by
      simp only [real_inner_eq_re_inner (𝕜 := ℂ), star_eq_adjoint,
        adjoint_inner_left]
    have htadj : inner ℝ (x i) (T (y i)) = inner ℝ (T (x i)) (y i) := by
      rw [← hadj, hTs.star_eq]
    have hlim := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul (h₁.add h₂)
    convert hlim using 1
    · funext d
      simp only [symmetrize, smul_apply, add_apply, real_inner_smul_left,
        inner_add_left, hadj]
    · congr 1
      rw [htadj]
      ring
  have hsum : Tendsto
      (fun d : Finset H × ℕ => ∑ i, inner ℝ (symmetrize (a d).val (x i)) (y i))
      atTop (𝓝 (∑ i, inner ℝ (T (x i)) (y i))) :=
    tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  have hz (d : Finset H × ℕ) :
      (∑ i, inner ℝ (symmetrize (a d).val (x i)) (y i)) = 0 := by
    have hh := (Submodule.mem_orthogonal _ _).mp hy _
      (show realTupleOrbitMap S x (a d) ∈ (realTupleOrbitMap S x).range from ⟨a d, rfl⟩)
    simpa only [PiLp.inner_apply, realTupleOrbitMap, LinearMap.coe_mk,
      AddHom.coe_mk, Generator.diagonalOperator_apply] using hh
  have heq : (∑ i, inner ℝ (T (x i)) (y i)) = 0 :=
    tendsto_nhds_unique hsum (by simpa only [hz] using tendsto_const_nhds)
  rw [real_inner_comm, PiLp.inner_apply]
  simpa only [Generator.diagonalOperator_apply] using heq

/-- Finite-vector version of selfadjoint strong density. -/
theorem selfAdjoint_bicommutant_finite_approximation
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hTs : IsSelfAdjoint T) (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : S, IsSelfAdjoint a.val ∧ ∀ x ∈ s, ‖T x - a.val x‖ < ε := by
  classical
  let x : Generator.FiniteHilbert s H := WithLp.toLp 2 (fun i : s => i.val)
  have h := selfAdjoint_bicommutant_tuple_mem_closure S T hT hTs x
  obtain ⟨z, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp h ε hε
  refine ⟨⟨symmetrize a.val, S.smul_mem (S.add_mem a.property
    (S.star_mem' a.property)) _⟩, symmetrize_selfAdjoint _, ?_⟩
  intro y hy
  have hb := PiLp.norm_apply_le
    (Generator.diagonalOperator T x - realTupleOrbitMap S x a) (⟨y, hy⟩ : s)
  exact hb.trans_lt (by simpa only [dist_eq_norm] using ha)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_KaplanskySelfAdjoint
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selfadjoint unit ball of the source algebra is strongly dense in
the selfadjoint unit ball of the represented bicommutant. -/
noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact source norm control, on any finite family of test vectors. -/
theorem selfAdjoint_kaplansky_approximation
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ representationVonNeumannAlgebra σ) (hTs : IsSelfAdjoint T)
    (hTn : ‖T‖ ≤ 1) (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧ ∀ x ∈ s, ‖σ a x - T x‖ < ε := by
  classical
  let P := representationVonNeumannAlgebra σ
  let D := kaplanskyPreimage T
  have hD : IsSelfAdjoint D := kaplanskyPreimage_selfAdjoint T
  have hDP : D ∈ P := by
    apply kaplanskyPreimage_mem P.toStarSubalgebra _ T hT
    change IsClosed P.carrier
    rw [← P.centralizer_centralizer']
    exact Set.isClosed_centralizer _
  have hDb : D ∈ Set.centralizer (Set.centralizer (σ.range : Set (H →L[ℂ] H))) := by
    simpa only [P, ← SetLike.mem_coe, coe_representationVonNeumannAlgebra] using hDP
  let s' : Finset H := s.image (fun x => kaplanskyReciprocal D x) ∪
    s.image (fun x => D (kaplanskyReciprocal D x))
  obtain ⟨b, hb, happrox⟩ := selfAdjoint_bicommutant_finite_approximation
    σ.range D hDb hD s' (ε / 4) (by positivity)
  obtain ⟨a, ha, hab⟩ := lift_selfAdjoint_range σ b hb
  refine ⟨kaplanskyTransform a, ?_, kaplanskyTransform_norm_le a ha, ?_⟩
  · rw [kaplanskyTransform_eq_cfc a ha]
    exact cfc_predicate _ a
  · intro x hx
    have h₁ : ‖(b.val - D) (kaplanskyReciprocal D x)‖ < ε / 4 := by
      simpa only [sub_apply, norm_sub_rev] using
        happrox _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    have h₂ : ‖(b.val - D) (D (kaplanskyReciprocal D x))‖ < ε / 4 := by
      simpa only [sub_apply, norm_sub_rev] using
        happrox _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    rw [map_kaplanskyTransform σ a ha, hab, ← kaplanskyTransform_preimage T hTs hTn]
    have he : kaplanskyTransform b.val x - kaplanskyTransform D x =
        (2 : ℝ) • ((b.val * kaplanskyReciprocal b.val - D * kaplanskyReciprocal D) x) := by
      simp only [kaplanskyTransform, smul_apply, sub_apply, smul_sub]
    rw [he, norm_smul]
    have hbound := kaplanskyReciprocal_difference_apply_le b.val D hb hD x
    rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_FinalDerivations
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The passage from the uniform commutator bound to similarity through
cyclic summands and their finite-column implementers. -/

noncomputable section
namespace KadisonSimilarity

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Approximate cyclic column factorization for every cyclic representation. -/
structure PublishedDerivationInputs (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] : Prop where
  columns : ∀ (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)),
    CyclicStarRepresentation σ → CyclicColumnTests σ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonSpectralCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The represented abelian commutant embeds isometrically in the actual
commutant of measurable scalar localizations on a single L² space. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

def commonScalarRepresentation :
    A →⋆ₐ[ℂ] (CommonCyclicHilbert π D →L[ℂ] CommonCyclicHilbert π D) :=
  (VectorL2.continuousRepresentation (H := ScalarHilbertCoordinates D.generators)
    (cyclicCommonBaseMeasure π D)).comp (gelfandStarTransform A).toStarAlgHom

omit [TopologicalSpace.SeparableSpace A] in
theorem commonScalarRepresentation_apply (a : A) :
    commonScalarRepresentation π D a =
      VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) (gelfandStarTransform A a) := rfl

attribute [irreducible] commonScalarRepresentation

omit [TopologicalSpace.SeparableSpace A] in
theorem commonScalarRepresentation_intertwines (a : A) (x : H) :
    cyclicCommonEmbedding π D (π a x) =
      commonScalarRepresentation π D a (cyclicCommonEmbedding π D x) := by
  rw [commonScalarRepresentation_apply]
  exact cyclicCommonEmbedding_intertwines π D a x

omit [TopologicalSpace.SeparableSpace A] in
theorem commonScalarRepresentation_adjoint_intertwines (a : A)
    (y : CommonCyclicHilbert π D) :
    π a ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y) =
      (cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint
        (commonScalarRepresentation π D a y) := by
  have hJs (x : H) : (cyclicCommonEmbedding π D) ((π a).adjoint x) = ((commonScalarRepresentation π D) a).adjoint ((cyclicCommonEmbedding π D) x) := by
    have h := commonScalarRepresentation_intertwines π D (star a) x
    simpa only [map_star, ContinuousLinearMap.star_eq_adjoint] using h
  apply ext_inner_left ℂ
  intro x
  calc
    inner ℂ x (π a ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y)) =
        inner ℂ ((π a).adjoint x) ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y) :=
      (ContinuousLinearMap.adjoint_inner_left (π a) _ _).symm
    _ = inner ℂ ((cyclicCommonEmbedding π D) ((π a).adjoint x)) y :=
      ContinuousLinearMap.adjoint_inner_right (cyclicCommonEmbedding π D).toContinuousLinearMap _ _
    _ = inner ℂ (((commonScalarRepresentation π D) a).adjoint ((cyclicCommonEmbedding π D) x)) y :=
      congrArg (fun z : CommonCyclicHilbert π D => inner ℂ z y) (hJs x)
    _ = inner ℂ ((cyclicCommonEmbedding π D) x) ((commonScalarRepresentation π D) a y) :=
      ContinuousLinearMap.adjoint_inner_left ((commonScalarRepresentation π D) a) _ _
    _ = inner ℂ x ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint ((commonScalarRepresentation π D) a y)) :=
      (ContinuousLinearMap.adjoint_inner_right (cyclicCommonEmbedding π D).toContinuousLinearMap _ _).symm

omit [TopologicalSpace.SeparableSpace A] in
theorem commonExtension_commutes_representation
    (T : H →L[ℂ] H) (hT : ∀ a, T * π a = π a * T) (a : A) :
    isometricExtension (cyclicCommonEmbedding π D) T * commonScalarRepresentation π D a =
      commonScalarRepresentation π D a * isometricExtension (cyclicCommonEmbedding π D) T := by
  have hJ (x : H) : (cyclicCommonEmbedding π D) (π a x) = (commonScalarRepresentation π D) a ((cyclicCommonEmbedding π D) x) :=
    commonScalarRepresentation_intertwines π D a x
  have ha := commonScalarRepresentation_adjoint_intertwines π D a
  have hTa (x : H) : T (π a x) = π a (T x) :=
    congrArg (fun L : H →L[ℂ] H => L x) (hT a)
  have he : isometricExtension (cyclicCommonEmbedding π D) T * (commonScalarRepresentation π D) a = (commonScalarRepresentation π D) a * isometricExtension (cyclicCommonEmbedding π D) T := by
    apply ContinuousLinearMap.ext
    intro y
    change (cyclicCommonEmbedding π D) (T ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint ((commonScalarRepresentation π D) a y))) =
      (commonScalarRepresentation π D) a ((cyclicCommonEmbedding π D) (T ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y)))
    exact (congrArg (fun z : H => (cyclicCommonEmbedding π D) (T z)) (ha y).symm).trans
      ((congrArg (cyclicCommonEmbedding π D) (hTa ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y))).trans
        (hJ (T ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y))))
  exact he

omit [TopologicalSpace.SeparableSpace A] in
theorem commonExtension_commutes_continuous
    (T : H →L[ℂ] H) (hT : ∀ a, T * π a = π a * T)
    (f : C(WeakDual.characterSpace ℂ A, ℂ)) :
    isometricExtension (cyclicCommonEmbedding π D) T *
        VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) f =
      VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) f *
        isometricExtension (cyclicCommonEmbedding π D) T := by
  have h := commonExtension_commutes_representation π D T hT ((gelfandStarTransform A).symm f)
  simpa only [commonScalarRepresentation_apply, StarAlgEquiv.apply_symm_apply] using h

theorem commonExtension_commutes_localizations
    (T : H →L[ℂ] H) (hT : ∀ a, T * π a = π a * T)
    (s : Set (WeakDual.characterSpace ℂ A)) (hs : MeasurableSet s) :
    isometricExtension (cyclicCommonEmbedding π D) T *
        l2Localization (cyclicCommonBaseMeasure π D) s hs =
      l2Localization (cyclicCommonBaseMeasure π D) s hs *
        isometricExtension (cyclicCommonEmbedding π D) T :=
  commutes_localizations_of_continuous (cyclicCommonBaseMeasure π D) _
    (commonExtension_commutes_continuous π D T hT) s hs

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CommonFieldCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compressing an actual measurable field in the common spectral model
returns an operator in the original abelian commutant. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- The original operator obtained by compressing the reconstructed field. -/
def commonFieldCompression
    (R : WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators)
    (hmeas : ∀ v, AEStronglyMeasurable (fun x => R x v) (cyclicCommonBaseMeasure π D))
    (C : ℝ) (hbound : ∀ᵐ x ∂cyclicCommonBaseMeasure π D, ‖R x‖ ≤ C) : H →L[ℂ] H :=
  ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint.comp
    (boundedFieldOperator (cyclicCommonBaseMeasure π D) R hmeas C hbound)).comp
      (cyclicCommonEmbedding π D).toContinuousLinearMap

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Density for unrestricted endpoints and centered tensor letters

The two endpoint variables and the finitely many centered letters have different
ambient Hilbert spaces. Nested dense matrix stages nevertheless give a common
stage, so their continuous coefficient identities extend together.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct
universe u

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def endpointTracialCoefficient {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) (J : F → F)
    (v : EndpointLetters E F k l) : ℂ :=
  inner ℂ (endpointWord (v.1 true) (fun j => J (v.2 (.inr j))))
    (Y (endpointWord (v.1 false) (fun i => v.2 (.inl i))))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteHalfProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.NaimarkZFC.gns_apply_coe
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

attribute [local instance] OAI.KadisonSimilarity.instIsClosedContinuousLinearMapComplexIdCoeStarSubalgebra_solutions
/-- The vector trace bundled only as the linear map needed by the
half-projection construction. -/
def concreteTraceLinear (τ : TracialRepresentation M) : M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun := τ.trace
  map_add' a b := inner_add_right _ _ _
  map_smul' c a := by
    change inner ℂ τ.vector (c • (a : H →L[ℂ] H) τ.vector) =
      c • inner ℂ τ.vector ((a : H →L[ℂ] H) τ.vector)
    exact inner_smul_right _ _ _

@[simp] theorem concreteTraceLinear_apply (τ : TracialRepresentation M)
    (a : M.toStarSubalgebra) : concreteTraceLinear τ a = τ.trace a := rfl

@[simp] theorem concreteTraceLinear_one (τ : TracialRepresentation M) :
    concreteTraceLinear τ 1 = 1 := τ.trace_one

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixUnitCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

section Representations

variable {P C D K : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Realize the full-column coordinates from the actual corner inclusion
operators and their common matrix of algebra entries. -/
def fullColumnCoordinatesOfColumns
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (U : FiniteOrthogonalColumns F H n) (V : FiniteOrthogonalColumns K D n)
    (entry : P → Matrix (Fin n) (Fin n) C)
    (hU : ∀ a i j, ρ (entry a i j) =
      (U.inclusion i).adjoint.comp ((L a).comp (U.inclusion j)))
    (hV : ∀ a i j, σ (entry a i j) =
      (V.inclusion i).adjoint.comp ((Lr a).comp (V.inclusion j))) :
    FullColumnCoordinates L Lr ρ σ n where
  domain := V.unitary.symm
  codomain := U.unitary.symm
  entry := entry
  domain_action := by
    intro a x
    simpa only [hV] using V.coordinates_operator (Lr a) x
  codomain_action := by
    intro a x
    simpa only [hU] using U.coordinates_operator (L a) x

end Representations
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixCornerFrames
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite family of partial isometries with common initial projection
constructs the actual Hilbert coordinate frame of a corner. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The columns are multiplication by the partial isometries after the
isometric inclusion of the initial corner. -/
def partialIsometryColumns (L : P →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : P) (he : IsStarProjection e) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1)
    (I : F →ₗᵢ[ℂ] H)
    (hI : I.toContinuousLinearMap.comp I.toContinuousLinearMap.adjoint = L e) :
    FiniteOrthogonalColumns F H n where
  inclusion i := (L (v i)).comp I.toContinuousLinearMap
  adjoint_comp i j := by
    simp only [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc (L (star (v i))), ← ContinuousLinearMap.mul_def,
      ← map_mul, hv]
    split_ifs with hij
    · rw [← hI]
      simp only [← ContinuousLinearMap.comp_assoc, I.adjoint_comp_self,
        ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    · simp
  resolution := by
    have hu (i : Fin n) : v i * e = v i :=
      mul_initial_projection e (v i) he (by simpa using hv i i)
    have hterm (i : Fin n) :
        ((L (v i)).comp I.toContinuousLinearMap).comp
          ((L (v i)).comp I.toContinuousLinearMap).adjoint = L (v i * star (v i)) := by
      rw [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
      change ((L (v i)).comp I.toContinuousLinearMap).comp
        (I.toContinuousLinearMap.adjoint.comp (L (star (v i)))) = _
      rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc I.toContinuousLinearMap,
        hI]
      change L (v i) * (L e * L (star (v i))) = _
      rw [← map_mul, ← map_mul, ← mul_assoc, hu]
    simp_rw [hterm]
    rw [← map_sum, hsum, map_one]
    rfl

/-- The matrix entries of the represented algebra are the algebraic corner
compressions by the same partial isometries. -/
theorem partialIsometryColumns_entry
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : P) (he : IsStarProjection e)
    {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) (I : F →ₗᵢ[ℂ] H)
    (hI : I.toContinuousLinearMap.comp I.toContinuousLinearMap.adjoint = L e)
    (a : P) (i j : Fin n) :
    ((partialIsometryColumns L e he v hv hsum I hI).inclusion i).adjoint.comp
      ((L a).comp ((partialIsometryColumns L e he v hv hsum I hI).inclusion j)) =
      I.toContinuousLinearMap.adjoint.comp
        ((L (star (v i) * a * v j)).comp I.toContinuousLinearMap) := by
  change ((L (v i)).comp I.toContinuousLinearMap).adjoint.comp
    ((L a).comp ((L (v j)).comp I.toContinuousLinearMap)) = _
  rw [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  simp only [map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem HaarCornerMoments.transport
    (τA : A →ₗ[ℂ] ℂ) (τB : B →ₗ[ℂ] ℂ) (hφ : ∀ x, τB (φ x) = τA x)
    {e : A} {he : IsStarProjection e} (z : unitary (CStarCorner e he)) {t : ℝ}
    (hz : HaarCornerMoments τA z t) :
    HaarCornerMoments τB (transportedCornerUnitary φ z) t := by
  intro k hk
  rw [haarCornerPower_transport, hφ]
  exact hz k hk

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SmallFreeCornerData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small projection, its full matrix frame, the containing half
projection, and the Haar unitary all belong to the same corner. The matrix
frame is constructed from the tower. Only trace cutting and the local Haar
existence statement are required for the two remaining choices. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

section Concrete

open UltrapowerBridge

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] {N : VonNeumannAlgebra K}

attribute [local instance] OAI.KadisonSimilarity.instIsClosedContinuousLinearMapComplexIdCoeStarSubalgebra_solutions_1
/-- The local specialization of H. Thiel, *Diffuse traces and Haar
unitaries*, arXiv:2009.06940v3, Proposition 7.2 and the following paragraph
(printed p.20). A nonzero corner of a diffuse von Neumann algebra is diffuse;
its normalized normal trace has a Haar unitary. The ambient trace is used
here, since multiplying its vanishing moments by the normalization gives
exactly `HaarCornerMoments`. This is an explicit conditional input. -/
def ThielDiffuseCornerHaarInput (τ : TracialRepresentation N) : Prop :=
  ∀ (q : N.toStarSubalgebra) (hq : IsStarProjection q),
    0 < (τ.trace q).re →
      ∃ z : unitary (CStarCorner q hq),
        ∀ k : ℤ, k ≠ 0 → τ.trace (haarCornerPower z k) = 0

end Concrete
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_IsometricMatrixExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.KadisonSimilarity.unitalizedExtension_inr _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric extension by zero preserves every finite operator-matrix norm. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

theorem norm_matrix_isometricExtension {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    ‖matrixOperator (fun i j => isometricExtension J (X i j))‖ = ‖matrixOperator X‖ := by
  let L := mapCopies J.toContinuousLinearMap n
  let R := mapCopies J.toContinuousLinearMap.adjoint n
  have hL : ‖L‖ ≤ 1 := (norm_mapCopies_le _ _).trans J.norm_toContinuousLinearMap_le
  have hR : ‖R‖ ≤ 1 := (norm_mapCopies_le _ _).trans (by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using J.norm_toContinuousLinearMap_le)
  have hRL : R.comp L = ContinuousLinearMap.id ℂ (HilbertCopies H n) := by
    dsimp [R, L]
    rw [← mapCopies_comp_eq, J.adjoint_comp_self]
    exact mapCopies_id_eq n
  have hext : L.comp ((matrixOperator X).comp R) =
      matrixOperator (fun i j => isometricExtension J (X i j)) := by
    apply ContinuousLinearMap.ext
    intro x
    ext i
    change J (matrixOperator X (mapCopies J.toContinuousLinearMap.adjoint n x) i) = _
    rw [matrixOperator_apply (H := H) X
      (mapCopies J.toContinuousLinearMap.adjoint n x) i, map_sum]
    simpa only [isometricExtension, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, mapCopies_apply] using
      (matrixOperator_apply (H := K) (fun i j => isometricExtension J (X i j)) x i).symm
  rw [← hext]
  exact norm_split_extension L R hL hR hRL _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonCommutantFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every member of the original abelian commutant has an actual operator
field over the common spectral measure. The construction retains its norm
and its algebraic operations almost everywhere. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

variable {A H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

def commonCommutantField
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra) :
    WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators :=
  diagonalField (cyclicCommonBaseMeasure π D)
    (isometricExtension (cyclicCommonEmbedding π D) T)
    (commonExtension_commutes_localizations π D T (commutant_commutes_representation π T))

theorem commonCommutantField_action
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra)
    (f : CommonCyclicHilbert π D) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      isometricExtension (cyclicCommonEmbedding π D) T f x = commonCommutantField π D T x (f x) :=
  diagonalField_action (cyclicCommonBaseMeasure π D) _ _ f

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialUltrapowerGNS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.HochschildUltrapower.quotientUnitary_coe _root_.OAI.KadisonSimilarity.grothendieckFamilyLinear_apply _root_.OAI.KadisonSimilarity.grothendieckFamilyMap_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The GNS space of the tracial quotient embeds isometrically in the
Hilbert ultrapower. This is the bounded-algebra-sequence subspace used
in the finite-factor transfer. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower HochschildUltrapower TracialUltrapower
open scoped ENNReal Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- A bounded algebra sequence, viewed as a bounded family of GNS vectors. -/
def algebraSequenceVector (x : ℕ →ᵇ A) :
    UltraPreHilbert (fun _ : ℕ => τ.GNS) ω :=
  (⟨fun i => (τ.toPreGNS (x i) : τ.GNS), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨i, rfl⟩
    simpa only [UniformSpace.Completion.norm_coe] using
      (HochschildRigidity.preGNS_norm_le τ h1 (x i)).trans (x.norm_coe_le_norm i)⟩⟩ :
    lp (fun _ : ℕ => τ.GNS) ∞)

/-- Algebra sequences act linearly on the bounded-vector subspace. -/
def algebraSequenceVectorLinear : (ℕ →ᵇ A) →ₗ[ℂ]
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω where
  toFun x := (algebraSequenceVector τ h1 ω x :
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω)
  map_add' x y := by
    rw [← UniformSpace.Completion.coe_add]
    congr 1
    apply Subtype.ext
    funext i
    change (τ.toPreGNS ((x + y) i) : τ.GNS) =
      (τ.toPreGNS (x i) : τ.GNS) + (τ.toPreGNS (y i) : τ.GNS)
    simp only [BoundedContinuousFunction.add_apply, map_add, UniformSpace.Completion.coe_add]
  map_smul' c x := by
    rw [← UniformSpace.Completion.coe_smul]
    congr 1
    apply Subtype.ext
    funext i
    change (τ.toPreGNS ((c • x) i) : τ.GNS) = c • (τ.toPreGNS (x i) : τ.GNS)
    simp only [BoundedContinuousFunction.smul_apply, map_smul, UniformSpace.Completion.coe_smul]

theorem algebraSequenceVector_norm (x : ℕ →ᵇ A) :
    ‖algebraSequenceVectorLinear τ h1 ω x‖ =
      sequenceTwoNorm (TracialUltrapower.traceHilbertMap τ h1) ω x := by
  change ‖(algebraSequenceVector τ h1 ω x :
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω)‖ = _
  rw [UniformSpace.Completion.norm_coe]
  apply tendsto_nhds_unique (UltraPreHilbert.norm_tendsto ω _)
  simpa only [algebraSequenceVector, UltraPreHilbert.family,
    UniformSpace.Completion.norm_coe, TracialUltrapower.traceHilbertMap_apply] using
    tendsto_sequenceTwoNorm (TracialUltrapower.traceHilbertMap τ h1) ω x

theorem algebraSequenceVector_null (x : ℕ →ᵇ A)
    (hx : x ∈ ideal τ h1 ω htr) : algebraSequenceVectorLinear τ h1 ω x = 0 := by
  apply norm_eq_zero.mp
  rw [algebraSequenceVector_norm]
  apply tendsto_nhds_unique (tendsto_sequenceTwoNorm _ _ x)
  exact (mem_nullSubmodule _ _ x).mp hx

/-- The algebra-sequence map factors through the actual tracial quotient. -/
def quotientGNSVector : Ultrapower τ h1 ω htr →ₗ[ℂ]
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω :=
  (nullSubmodule (TracialUltrapower.traceHilbertMap τ h1).toLinearMap
    (ω : Filter ℕ)).liftQ (algebraSequenceVectorLinear τ h1 ω)
      (fun x hx => algebraSequenceVector_null τ h1 ω htr x hx)

@[simp] theorem quotientGNSVector_mk (x : ℕ →ᵇ A) :
    quotientGNSVector τ h1 ω htr (quotientHom τ h1 ω htr x) =
      algebraSequenceVectorLinear τ h1 ω x := rfl

/-- The tracial quotient's Hilbert norm is the ultralimit Hilbert norm. -/
def quotientPreGNSIsometry : (quotientTrace τ h1 ω htr).PreGNS →ₗᵢ[ℂ]
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω where
  toLinearMap := (quotientGNSVector τ h1 ω htr).comp
    (quotientTrace τ h1 ω htr).ofPreGNS.toLinearMap
  norm_map' x := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
      ((quotientTrace τ h1 ω htr).ofPreGNS x)
    change ‖quotientGNSVector τ h1 ω htr
      ((quotientTrace τ h1 ω htr).ofPreGNS x)‖ = ‖x‖
    have hx : x = (quotientTrace τ h1 ω htr).toPreGNS
        (quotientHom τ h1 ω htr a) := by
      apply (quotientTrace τ h1 ω htr).ofPreGNS.injective
      exact ha.symm
    rw [hx, PositiveLinearMap.ofPreGNS_toPreGNS, quotientGNSVector_mk,
      algebraSequenceVector_norm, quotientTrace_preGNS_norm]
    rfl

/-- The closed GNS subspace of the Hilbert ultrapower, constructed by completion. -/
def tracialUltrapowerGNSInclusion : (quotientTrace τ h1 ω htr).GNS →ₗᵢ[ℂ]
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω where
  toLinearMap := (quotientPreGNSIsometry τ h1 ω htr).toContinuousLinearMap.fromCompletion
    |>.toLinearMap
  norm_map' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      change ‖(quotientPreGNSIsometry τ h1 ω htr).toContinuousLinearMap.fromCompletion
        (x : (quotientTrace τ h1 ω htr).GNS)‖ = ‖(x : (quotientTrace τ h1 ω htr).GNS)‖
      rw [ContinuousLinearMap.fromCompletion_apply_coe, UniformSpace.Completion.norm_coe]
      exact (quotientPreGNSIsometry τ h1 ω htr).norm_map x

@[simp] theorem tracialUltrapowerGNSInclusion_mk (x : ℕ →ᵇ A) :
    tracialUltrapowerGNSInclusion τ h1 ω htr
      ((quotientTrace τ h1 ω htr).toPreGNS (quotientHom τ h1 ω htr x)) =
      algebraSequenceVectorLinear τ h1 ω x :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableProjectionJoin
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable projection joins with the trace bound inherited from finite
unions. Only the concrete faithful vector trace is used for the limit. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance countableJoin_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonCentralData
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common spectral model supplies the actual central-decomposition
data for a weakly generating separable source. Factoriality is proved
separately using the joint source. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

universe u
variable {A H : Type u} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- All operators commuting with the center acquire fields in the single
common spectral model. -/
def commonCentralField (P : VonNeumannAlgebra H)
    (hcentral : starSubalgebraCommutant π.range = (vonNeumannCenter P).commutant)
    (T : (vonNeumannCenter P).commutant.toStarSubalgebra) :
    WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators :=
  commonCommutantField π D ⟨T.val, by rw [hcentral]; exact T.property⟩

theorem commonCentralField_action (P : VonNeumannAlgebra H)
    (hcentral : starSubalgebraCommutant π.range = (vonNeumannCenter P).commutant)
    (T : (vonNeumannCenter P).commutant.toStarSubalgebra) (f : CommonCyclicHilbert π D) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      isometricExtension (cyclicCommonEmbedding π D) T f x =
        commonCentralField π D P hcentral T x (f x) :=
  commonCommutantField_action π D
    ⟨T.val, by rw [hcentral]; exact T.property⟩ f

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConcretePredualRestriction
attribute [-instance] _root_.OAI.KadisonSimilarity.concretePredual_separable _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem normalRestriction_mem (φ : StrongDual ℂ M.toStarSubalgebra)
    (hφ : φ ∈ normalFunctionalSpace M) :
    normalRestriction hNM φ ∈ normalFunctionalSpace N := by
  have hspan : Submodule.span ℂ (Set.range fun xy : H × H => normalCoefficient M xy.1 xy.2) ≤
      (normalFunctionalSpace N).toSubmodule.comap (normalRestriction hNM).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change normalRestriction hNM (normalCoefficient M x y) ∈ normalFunctionalSpace N
    rw [normalRestriction_coefficient]
    exact (predualCoefficient N x y).property
  exact closure_minimal hspan
    ((normalFunctionalSpace N).isClosed.preimage (normalRestriction hNM).continuous) hφ

def predualRestriction : ConcretePredual M →L[ℂ] ConcretePredual N :=
  (((normalRestriction hNM).comp (normalFunctionalSpace M).toSubmodule.subtypeL).codRestrict
    (normalFunctionalSpace N).toSubmodule (fun φ => normalRestriction_mem hNM φ φ.property))

@[simp] theorem predualRestriction_apply (φ : ConcretePredual M) (a : N.toStarSubalgebra) :
    (predualRestriction hNM φ : StrongDual ℂ N.toStarSubalgebra) a =
      (φ : StrongDual ℂ M.toStarSubalgebra) (StarSubalgebra.inclusion hNM a) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_BoundedMatrixHom
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite matrix amplification of a bounded homomorphism. A finite
generating family becomes one cyclic vector for this amplification. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteOrbitMap (π : BoundedUnitalHom A H) {n : ℕ} (ξ : Fin n → H) :
    (Fin n → A) →ₗ[ℂ] H where
  toFun a := ∑ i, π.1 (a i) (ξ i)
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteOrbitSubspace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

def finiteOrbitSubspace (π : BoundedUnitalHom A H) {n : ℕ} (ξ : Fin n → H) :
    ClosedSubmodule ℂ H := (LinearMap.range (finiteOrbitMap π ξ)).closure

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProperlyInfiniteStructure
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

local instance infiniteStructureClosed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (P : Set (H →L[ℂ] H))
  infer_instance

open BoundedHochschild.KadisonRingrose HochschildCorners
open scoped ComplexOrder

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorTrace
attribute [-instance] _root_.OAI.KadisonSimilarity.concretePredual_separable _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.normalRestriction_apply _root_.OAI.KadisonSimilarity.normalRestriction_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Faithful normal tracial states on concrete finite factors. The only
structural assumptions are finiteness and a scalar center. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder
open BoundedHochschild BoundedHochschild.KadisonRingrose

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

def vectorPositiveFunctional (ξ : H) : M.toStarSubalgebra →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (normalCoefficient M ξ ξ).toLinearMap (fun a ha => by
    have hp : (a : H →L[ℂ] H).IsPositive :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mp ha
    exact hp.inner_nonneg_right ξ)

@[simp] theorem vectorPositiveFunctional_apply (ξ : H) (a : M.toStarSubalgebra) :
    vectorPositiveFunctional M ξ a = inner ℂ ξ ((a : H →L[ℂ] H) ξ) := rfl

theorem vectorPositiveFunctional_normal (ξ : H) :
    TraceInPredual (concretePredualEquiv M) (vectorPositiveFunctional M ξ) := by
  refine ⟨predualCoefficient M ξ ξ, fun a => ?_⟩
  rw [concretePredualEquiv_symm_apply, predualCoefficient_apply,
    vectorPositiveFunctional_apply]
  calc
    inner ℂ ξ ((a : H →L[ℂ] H) ξ) =
        inner ℂ ((a : H →L[ℂ] H).adjoint ξ) ξ :=
      (ContinuousLinearMap.adjoint_inner_left (a : H →L[ℂ] H) ξ ξ).symm
    _ = _ := (inner_conj_symm (𝕜 := ℂ) _ _).symm

theorem vectorPositiveFunctional_one (ξ : H) (hξ : ‖ξ‖ = 1) :
    vectorPositiveFunctional M ξ 1 = 1 := by
  rw [vectorPositiveFunctional_apply]
  change inner ℂ ξ ξ = 1
  rw [inner_self_eq_norm_sq_to_K, hξ]
  norm_num

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteTypeIStructure
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite factor with a nonzero abelian projection is a full matrix algebra.
The homogeneous central piece is the unit because the center is scalar. -/

noncomputable section
namespace KadisonSimilarity

open BoundedHochschild.KadisonRingrose HochschildCorners HochschildMatrixSystems
open scoped ComplexOrder

def unitCornerEquiv {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (hp : IsStarProjection (1 : A)) : Corner 1 hp ≃⋆ₐ[ℂ] A where
  toFun a := a.val
  invFun a := ⟨a, by change 1 * a = a ∧ a * 1 = a; simp⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem matrixSystem_surjective_of_abelian_diagonal
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hfactor : ∀ a : A, (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ A c)
    {n : ℕ} (E : MatrixSystem A n) (i : Fin n)
    (hi : FinitePathMain.AbelianProjection (E.entry i i)) :
    Function.Surjective (matrixUnitsOfSystem E).hom := by
  intro x
  have hcomm := E.commutant_commutative_of_abelian_diagonal i hi
  have hcoeff (j k : Fin n) : ∃ c : ℂ, E.coefficient j k x = c • (1 : A) := by
    obtain ⟨c, hc⟩ := hfactor (E.coefficient j k x)
      (E.commutant_central hcomm ⟨_, E.coefficient_mem j k x⟩)
    exact ⟨c, by simpa only [Algebra.algebraMap_eq_smul_one] using hc⟩
  choose c hc using hcoeff
  refine ⟨Matrix.of c, ?_⟩
  change (∑ j, ∑ k, c j k • E.entry j k) = x
  rw [← E.reconstruct x]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hc, mul_smul_comm, mul_one]

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

local instance finiteTypeIStructureClosed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (P : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_CornerTraceScaling
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Undo normalization of a corner trace in the two inequalities used by patching. -/

noncomputable section
namespace KadisonSimilarity
open HochschildCorners
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (p : A) (hp : IsStarProjection p) (τ : A →ₚ[ℂ] ℂ) (ht : 0 < (τ p).re)

include ht

theorem original_trace_lt_of_corner {q : Corner p hp} {η : ℝ}
    (h : (cornerTrace p hp τ q).re < η / (τ p).re) : (τ (q : A)).re < η := by
  rw [HochschildQuantization.corner_trace_re] at h
  have hh := mul_lt_mul_of_pos_left h ht
  simpa only [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul,
    mul_div_cancel₀ _ ht.ne'] using hh

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMomentContinuity
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the mixed moments on operator-norm bounded sets. -/

noncomputable section
namespace KadisonSimilarity

open BoundedHochschild HochschildPatching HochschildUltrapower Filter Topology
open scoped ComplexOrder

variable {B I J : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
  (tr : ∀ a b, τ (a * b) = τ (b * a))

include h1 in
lemma gnsTendsto_centered {f : J → B} {l : Filter J} {b : B}
    (h : GNSTendsto τ f l b) :
    GNSTendsto τ (fun j => f j - τ (f j) • 1) l (b - τ b • 1) := by
  have ht := trace_tendsto_of_gns τ h1 h
  have hs : GNSTendsto τ (fun j => τ (f j) • 1) l (τ b • 1) := by
    have hh := ((ht.sub_const (τ b)).norm).mul_const ‖τ.toPreGNS 1‖
    simpa only [GNSTendsto, ← sub_smul, map_smul, norm_smul, sub_self,
      norm_zero, zero_mul] using hh
  exact h.sub τ hs

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_DenseMomentExtension
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

include hσ in
lemma norm_centered_contraction (c : C) (hc : ‖c‖ ≤ 1) :
    ‖c - σ c • 1‖ ≤ 2 := by
  have h := norm_centered_half σ hσ c hc
  rw [norm_smul] at h
  norm_num at h
  linarith

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixStageGrowth
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full finite matrix stage has a minimal diagonal projection. This
is the obstruction to a diffuse generated algebra stabilizing at a stage. -/

noncomputable section
namespace KadisonSimilarity

open Generator

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_diagonal_no_proper_subprojection (E : MatrixUnitSystem ι A)
    (o : ι) (q : A) (hmem : q ∈ E.algebra) (hq : IsStarProjection q)
    (hpq : E.entry o o * q = q) (hqp : q * E.entry o o = q) :
    q = 0 ∨ q = E.entry o o := by
  change ∃ a, E.hom a = q at hmem
  obtain ⟨a, rfl⟩ := hmem
  have he : E.hom a = a o o • E.entry o o := by
    calc
      E.hom a = E.entry o o * E.hom a * E.entry o o := by rw [hpq, hqp]
      _ = a o o • E.entry o o := E.sandwich a o o o
  have hp : E.entry o o * E.entry o o = E.entry o o := by
    simpa only [ite_true] using E.mul_entry o o o o
  have hid := hq.isIdempotentElem.eq
  rw [he] at hid
  have hc : a o o * a o o = a o o :=
    (smul_left_injective ℂ (E.diagonal_ne_zero o)) (by
      simpa only [smul_mul_smul, hp] using hid)
  have hmul : a o o * (a o o - 1) = 0 := by
    rw [mul_sub, mul_one, hc, sub_self]
  rcases mul_eq_zero.mp hmul with hz | ho
  · left
    rw [he, hz, zero_smul]
  · right
    rw [he, sub_eq_zero.mp ho, one_smul]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorPresentation
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

attribute [local instance] OAI.KadisonSimilarity.finitePresentationClosed
/-- The constructed normalized faithful normal trace. -/
structure NormalFiniteTrace where
  trace : P.toStarSubalgebra →ₚ[ℂ] ℂ
  normal_predual : BoundedHochschild.TraceInPredual (concretePredualEquiv P) trace
  one : trace 1 = 1
  tracial : ∀ a b, trace (a * b) = trace (b * a)
  faithful : ∀ a, trace (star a * a) = 0 → a = 0

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_RelativeMatrixQuantization
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem map_matrix_rankOne {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {n : ℕ} (E : MatrixUnitSystem (Fin n) A) (φ : A →⋆ₐ[ℂ] B)
    (g : Fin n → ZMod 3) :
    φ ((matrixSystemOfUnits E).rankOne g) =
      (matrixSystemOfUnits (E.map φ)).rankOne g := by
  simp only [HochschildMatrixSystems.MatrixSystem.rankOne,
    HochschildMatrixSystems.MatrixSystem.scalarMatrix, map_sum, map_smul]
  rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceCornerQuantization
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

section CornerHom
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The original inclusion restricted to matching corners. -/
def sourceCornerHom (φ : A →⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p) :
    Corner p hp →⋆ₐ[ℂ] Corner (φ p) (hp.map φ) where
  toFun x := ⟨φ (x : A), by
    constructor
    · rw [← map_mul, x.property.1]
    · rw [← map_mul, x.property.2]⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_one' := Subtype.ext rfl
  map_add' x y := Subtype.ext (map_add φ (x : A) (y : A))
  map_mul' x y := Subtype.ext (map_mul φ (x : A) (y : A))
  map_star' x := Subtype.ext (map_star φ (x : A))
  commutes' c := Subtype.ext (by
    change φ (c • p) = c • φ p
    exact map_smul φ c p)

@[simp] theorem sourceCornerHom_coe (φ : A →⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p)
    (x : Corner p hp) : (sourceCornerHom φ p hp x : B) = φ (x : A) := rfl

end CornerHom

universe u

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourcePartialUnitaries
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial unitaries remain in the source while their moments are evaluated
in the ambient algebra. -/

noncomputable section
namespace KadisonSimilarity

open HochschildComparison HochschildPatching BoundedHochschild
open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

namespace SourcePartialUnitary
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Apply the given inclusion to a partial unitary. -/
def map (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) : PartialUnitary B :=
  ⟨⟨φ (v : A), by
    rw [← map_star, ← map_mul, ← map_mul, v.val.mul_star_mul]⟩, by
    change φ (v : A) * star (φ (v : A)) = star (φ (v : A)) * φ (v : A)
    rw [← map_star, ← map_mul, ← map_mul, v.mul_star_self_eq_support,
      v.star_mul_self_eq_support]⟩

@[simp] theorem coe_map (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) :
    (map φ v : B) = φ (v : A) := rfl

@[simp] theorem support_map (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) :
    (map φ v).support = φ v.support := by
  change star (φ (v : A)) * φ (v : A) = φ (star (v : A) * (v : A))
  rw [map_mul, map_star]

@[simp] theorem map_zero (φ : A →⋆ₐ[ℂ] B) : map φ 0 = 0 :=
  PartialUnitary.ext (show φ (0 : A) = (0 : B) from _root_.map_zero φ)

@[simp] theorem power_map (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) (k : Bool × ℕ) :
    (map φ v).power k = φ (v.power k) := by
  dsimp only [PartialUnitary.power]
  split <;> simp only [coe_map, map_pow, map_star]

theorem map_orthogonalSum (φ : A →⋆ₐ[ℂ] B) (v w : PartialUnitary A)
    (h : v.support * w.support = 0) :
    map φ (v.orthogonalSum w h) =
      (map φ v).orthogonalSum (map φ w) (by rw [support_map, support_map, ← map_mul, h, _root_.map_zero]) := by
  apply PartialUnitary.ext
  simp only [coe_map, PartialUnitary.coe_orthogonalSum, map_add]

end SourcePartialUnitary

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceQuotientMoments
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

lemma source_map_asPartialUnitary {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (u : unitary A) :
    SourcePartialUnitary.map φ (asPartialUnitary u) = asPartialUnitary (mapUnitary φ u) := by
  apply HochschildComparison.PartialUnitary.ext
  rfl

end KadisonSimilarity

end

end OAI
end


