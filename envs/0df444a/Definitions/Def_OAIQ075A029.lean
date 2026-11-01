-- Prove2me | Definitions.Def_OAIQ075A029
-- name    : OAIQ075A029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:38:00.563774+00:00
-- url     : https://prove2.me/theorems/8ded19a5-0f14-4dcd-bafe-86cf47117207
-- title:
--   Definitions bundle OAIQ075A029 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 91 declarations of OpenAI's Lean: 38 definitions, 1 instance and 52 theorems. The definitions and types are `OAI.KadisonSimilarity.TracialCornerGeometry.baseMatrixWordAction`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeCornerMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeCornerMultiplicityNormedFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra`, `OAI.KadisonSimilarity.TracialCornerGeometry.haarMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.haarMultiplicityNormedFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.haarRepeatedWordInclusion`, `OAI.KadisonSimilarity.TracialCornerGeometry.halfCornerGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.matrixStageUnitaryInclusion`, `OAI.KadisonSimilarity.TracialCornerGeometry.smallFrameCompressionInput`, `OAI.KadisonSimilarity.TracialCornerGeometry.traceCornerElements`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialEmbeddedMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialEmbeddedMultiplicityNormedFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixLeftRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryOperator`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryRepresentation`, `OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagationData`, `OAI.KadisonSimilarity.TracialWordFormula.automorphismMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialWordFormula.automorphismMultiplicityNormedFamily`, `OAI.KadisonSimilarity.canonicalGeneratedOperator`, `OAI.KadisonSimilarity.canonicalGeneratedRealSequence`, `OAI.KadisonSimilarity.centeredFreeWordSpan`, `OAI.KadisonSimilarity.centeredFreeWordVectors`, `OAI.KadisonSimilarity.commonFirstFiberScalarCenter`, `OAI.KadisonSimilarity.constantTracialGNSInclusion`, `OAI.KadisonSimilarity.firstCopiesIsometry`, `OAI.KadisonSimilarity.freeCompressionHead`, `OAI.KadisonSimilarity.freeHeadEquiv`, `OAI.KadisonSimilarity.freeTracialHeadCoordinates`, `OAI.KadisonSimilarity.generatedEmbeddingRealSequence`, `OAI.KadisonSimilarity.generatedGNSCompression`, `OAI.KadisonSimilarity.globalRestrictionFiberEquiv`, `OAI.KadisonSimilarity.hilbertTensorMapIsometry`, `OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv`, `OAI.KadisonSimilarity.projectionFiberEquivOfEq`, `OAI.KadisonSimilarity.tracialMatrixWordCovariance`, `OAI.KadisonSimilarity.transportRealTracialSequence`, `OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonSimilarity_Derivation_DiagonalMatrixNorm`, `KadisonSimilarity_FreeProduct_CompressionProjectionTransport`, `KadisonSimilarity_FreeProduct_CompressionSetup`, `KadisonSimilarity_FreeProduct_EmbeddedWordActions`, `KadisonSimilarity_FreeProduct_FreeCompressionDischarge`, `KadisonSimilarity_FreeProduct_FreeCornerApplication`, `KadisonSimilarity_FreeProduct_FreeCreationDischarge`, `KadisonSimilarity_FreeProduct_FreeHeadCoordinates`, `KadisonSimilarity_FreeProduct_FreeLeadingWords`, `KadisonSimilarity_FreeProduct_FreeMatrixBaseAction`, `KadisonSimilarity_FreeProduct_FreeMatrixExtension`, `KadisonSimilarity_FreeProduct_FreeMatrixFactorAction`, `KadisonSimilarity_FreeProduct_FreePrefixIsometry`, `KadisonSimilarity_FreeProduct_GeneratedDihedralAlgebras`, `KadisonSimilarity_FreeProduct_LeadingWordGeometry`, `KadisonSimilarity_FreeProduct_ReducedWordAutomorphisms`, `KadisonSimilarity_FreeProduct_TracialAutomorphismWords`, `KadisonSimilarity_FreeProduct_TracialEmbeddedWordStructure`, `KadisonSimilarity_FreeProduct_TracialFreeCornerEstimate`, `KadisonSimilarity_FreeProduct_TracialHaarWordColumns`, `KadisonSimilarity_FreeProduct_TracialRepeatedWords`, `KadisonSimilarity_Representation_CanonicalGeneratedModel`, `KadisonSimilarity_Representation_CanonicalGeneratedOperators`, `KadisonSimilarity_Representation_CommonFiberFactors`, `KadisonSimilarity_Representation_CompressedFieldNorm`, `KadisonSimilarity_Representation_CountableAmplification`, `KadisonSimilarity_Representation_GeneratedEmbeddings`, `KadisonSimilarity_Representation_GlobalFiberRestriction`, `KadisonSimilarity_Representation_JointFiberRestriction`, `KadisonSimilarity_Representation_ProjectionCentralData`, `KadisonSimilarity_Representation_ProjectionFieldReduction`, `KadisonSimilarity_Tracial_GeneratedGNSRecovery`, `KadisonSimilarity_Tracial_TracialEmbeddingTransport`, `KadisonSimilarity_Tracial_TracialHeadCoordinates`, `KadisonSimilarity_Tracial_TracialMatrixCovariance`, `KadisonSimilarity_Tracial_TracialMatrixSymmetrization`, `KadisonSimilarity_Tracial_TracialSpectralNorm`, `KadisonSimilarity_Tracial_TracialUltrapowerConstants`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A023`, `OAIQ075A024` and `OAIQ075A025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A033` and `OAIQ075A034`; the statements `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words`, `OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_from_local_models`, `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models`, `OAI.KadisonSimilarity.TracialCornerGeometry.generated_dihedral_spectralInput`, `OAI.KadisonSimilarity.TracialCornerGeometry.norm_spectral_arc_compression`, `OAI_KadisonSimilarity_TracialCornerGeometry_tracialMatrixUnitaryRepresentation_inclusion`, `OAI_KadisonSimilarity_TracialCornerGeometry_tracial_word_level_ranges`, `OAI.KadisonSimilarity.ae_common_fiber_scalar_center` and `OAI.KadisonSimilarity.canonical_free_corner_bound`; the proofs of `OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_from_local_models`, `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models`, `OAI.KadisonSimilarity.TracialCornerGeometry.norm_spectral_arc_compression`, `OAI_KadisonSimilarity_TracialCornerGeometry_tracialMatrixUnitaryRepresentation_inclusion`, `OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs`, `OAI.KadisonSimilarity.canonical_free_corner_bound` and `OAI_KadisonSimilarity_concrete_repeated_propagation`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A023
import Definitions.Def_OAIQ075A024
import Definitions.Def_OAIQ075A025

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_DiagonalMatrixNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix norms of the reconstructed diagonal representations

Finite L² sums are identified isometrically with tuple-valued L². The
actual matrix action is pointwise under this identification, so its norm is
exactly the essential supremum of the fiber matrix norms.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
/-- The transported finite matrix acts pointwise by the corresponding
matrix of the actual scalar fields. -/
theorem l2_matrix_action {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (R : Ω → Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hR : ∀ (i j : Fin n) (f : Lp H 2 μ),
      ∀ᵐ a ∂μ, X i j f a = R a i j (f a))
    (f : Lp (HilbertCopies H n) 2 μ) :
    ∀ᵐ a ∂μ, (l2FiniteCopiesEquiv (H := H) μ n).conjStarAlgEquiv (matrixOperator X) f a =
      matrixOperator (R a) (f a) := by
  let U := l2FiniteCopiesEquiv (H := H) μ n
  let x := U.symm f
  have hsums : ∀ᵐ a ∂μ, ∀ i : Fin n,
      (∑ j : Fin n, X i j (x j)) a = ∑ j : Fin n, X i j (x j) a :=
    eventually_countable_forall.mpr fun i =>
      (Lp.coeFn_finsetSum Finset.univ (fun j => X i j (x j))).mono fun a ha => by
        simpa only [Finset.sum_apply] using ha
  have hentries : ∀ᵐ a ∂μ, ∀ i j : Fin n, X i j (x j) a = R a i j (x j a) :=
    eventually_countable_forall.mpr fun i => eventually_countable_forall.mpr fun j => hR i j (x j)
  filter_upwards [l2FiniteCopiesEquiv_ae μ (matrixOperator X x),
    l2FiniteCopiesEquiv_ae μ x, hsums, hentries] with a hout hx hsum he
  ext i
  change U (matrixOperator X x) a i = _
  rw [hout i, matrixOperator_apply, hsum i, matrixOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [he i j]
  have hj : f a j = x j a := by simpa only [x, U, LinearIsometryEquiv.apply_symm_apply] using hx j
  rw [hj]

set_option synthInstance.maxHeartbeats 200000 in
/-- Matrix norms are preserved exactly by the actual pointwise fields. -/
theorem diagonal_matrix_norm_iff {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (R : Ω → Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hR : ∀ (i j : Fin n) (f : Lp H 2 μ),
      ∀ᵐ a ∂μ, X i j f a = R a i j (f a)) (C : ℝ) (hC : 0 ≤ C) :
    ‖matrixOperator X‖ ≤ C ↔ ∀ᵐ a ∂μ, ‖matrixOperator (R a)‖ ≤ C := by
  have hnorm : ‖(l2FiniteCopiesEquiv (H := H) μ n).conjStarAlgEquiv (matrixOperator X)‖ =
      ‖matrixOperator X‖ :=
    NonUnitalStarAlgHom.norm_map (l2FiniteCopiesEquiv (H := H) μ n).conjStarAlgEquiv
      (l2FiniteCopiesEquiv (H := H) μ n).conjStarAlgEquiv.injective _
  rw [← hnorm]
  exact pointwise_field_norm_iff μ _ _ (l2_matrix_action μ X R hR) C hC

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeLeadingWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
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

def centeredFreeWordVectors : Set H := {v | ∃ (side : Bool) (xs : List P),
  AlternatingCenteredWord G.trace A D side xs ∧ v = G.vector xs.prod}

def centeredFreeWordSpan : Submodule ℂ H :=
  Submodule.span ℂ (centeredFreeWordVectors G A D)

theorem centered_word_mem_span {side : Bool} {xs : List P}
    (hxs : AlternatingCenteredWord G.trace A D side xs) :
    G.vector xs.prod ∈ centeredFreeWordSpan G A D :=
  Submodule.subset_span ⟨side, xs, hxs, rfl⟩

theorem full_pairWord_mem_span (hτ : G.trace 1 = 1) {xs : List P}
    (hxs : CenteredPairWord G.trace A D xs) (d : D) (b : A) :
    G.vector ((d : P) * xs.prod * (b : P)) ∈ centeredFreeWordSpan G A D := by
  let d₀ := traceCentered G.trace (d : P)
  let b₀ := traceCentered G.trace (b : P)
  have hd := traceCentered_mem G.trace D d.property
  have hb := traceCentered_mem G.trace A b.property
  have hd0 := traceCentered_trace G.trace hτ (d : P)
  have hb0 := traceCentered_trace G.trace hτ (b : P)
  have h1 : G.vector (d₀ * xs.prod * b₀) ∈ centeredFreeWordSpan G A D := by
    have hx := centered_word_mem_span G A D
      (AlternatingCenteredWord.cons (side := false) hd hd0 (hxs.alternating_append hb hb0))
    simpa only [List.prod_cons, List.prod_append, List.prod_singleton,
      List.prod_nil, mul_one, mul_assoc] using hx
  have h2 : G.vector (d₀ * xs.prod) ∈ centeredFreeWordSpan G A D := by
    exact centered_word_mem_span G A D (.cons (side := false) hd hd0 hxs.alternating)
  have h3 : G.vector (xs.prod * b₀) ∈ centeredFreeWordSpan G A D := by
    simpa only [List.prod_append, List.prod_singleton] using
      centered_word_mem_span G A D (hxs.alternating_append hb hb0)
  have h4 := centered_word_mem_span G A D hxs.alternating
  have he : (d : P) * xs.prod * (b : P) =
      d₀ * xs.prod * b₀ + G.trace (b : P) • (d₀ * xs.prod) +
        G.trace (d : P) • (xs.prod * b₀) +
          (G.trace (d : P) * G.trace (b : P)) • xs.prod := by
    calc
      _ = (d₀ + G.trace (d : P) • 1) * xs.prod *
          (b₀ + G.trace (b : P) • 1) := by
        dsimp [d₀, b₀]
        rw [traceCentered_add, traceCentered_add]
      _ = _ := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
          mul_one, smul_add, smul_smul, mul_comm (G.trace (b : P)) (G.trace (d : P))]
        abel
  rw [he, map_add, map_add, map_add, map_smul, map_smul, map_smul]
  exact (centeredFreeWordSpan G A D).add_mem
    ((centeredFreeWordSpan G A D).add_mem
      ((centeredFreeWordSpan G A D).add_mem h1
        ((centeredFreeWordSpan G A D).smul_mem _ h2))
      ((centeredFreeWordSpan G A D).smul_mem _ h3))
    ((centeredFreeWordSpan G A D).smul_mem _ h4)

theorem centeredFreeWordSpan_dense (hτ : G.trace 1 = 1)
    (hgen : ReducedWordGenerated G A D) :
    (centeredFreeWordSpan G A D).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨n, d, b, a, c, ha, hc, rfl⟩
  change G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
    (fun i => (c i : P)) * (b : P)) ∈ centeredFreeWordSpan G A D
  have hp := CenteredPairWord.of_pairWord (τ := G.trace)
    (fun i => (a i : P)) (fun i => (c i : P))
    (fun i => (a i).property) (fun i => (c i).property) ha hc
  simpa only [prod_pairWord, alternatingProduct] using full_pairWord_mem_span G A D hτ hp d b

theorem inner_leading_opposite_word (hf : ScalarFree G.trace A D)
    (side : Bool) (xs : LeadingWordParameter G A D side)
    (ys : CenteredWordParameter G A D (!side)) :
    inner ℂ (leadingWordFamily G A D side xs) (centeredWordFamily G A D (!side) ys) = 0 := by
  rw [leadingWordFamily, centeredWordFamily, G.inner_vector]
  exact hf.trace_opposite_words G.trace_star xs.1.2 ys.2 (Or.inl xs.2)

theorem inner_leading_opposite_space (hf : ScalarFree G.trace A D) (side : Bool)
    (x : leadingWordSpace G A D side) (y : centeredWordSpace G A D (!side)) :
    inner ℂ (x : H) (y : H) = 0 :=
  closedFamilySpan_inner_zero (leadingWordFamily G A D side)
    (centeredWordFamily G A D (!side)) (inner_leading_opposite_word G A D hf side) x y

theorem vacuum_mem_centeredWordSpace (side : Bool) :
    G.vector 1 ∈ centeredWordSpace G A D side := by
  have h := (closedFamilyVector (centeredWordFamily G A D side)
    ⟨[], .nil side⟩).property
  exact h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreePrefixIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem freeHeadIsometry_left (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (d : D) (y : centeredWordSpace G A D true) :
    freeHeadIsometry G A D hτ hf (hilbertTensorInsert (G.baseVector D d) y) =
      G.left (d : P) (y : H) := by
  let f := (freeHeadIsometry G A D hτ hf).toContinuousLinearMap.comp
    (hilbertTensorInsert (G.baseVector D d)) -
      (G.left (d : P)).comp (centeredWordSpace G A D true).subtypeL
  have he : f = 0 := continuousLinearMap_eq_zero_of_total
    (closedFamilyVector (centeredWordFamily G A D true)) (closedFamilyVector_total _) f (by
      intro xs
      change freeHeadIsometry G A D hτ hf (freeHeadTensor G A D (d, xs)) -
        G.left (d : P) (G.vector xs.1.prod) = 0
      rw [freeHeadIsometry_tensor, freeHeadVector, G.left_vector, sub_self])
  exact sub_eq_zero.mp (congrArg (fun f => f y) he)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialHeadCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional projection in propagation, constructed from the tracial
head of the reduced-word decomposition and actual corner Haar powers. -/

noncomputable section
namespace KadisonSimilarity

variable {D P E H F : Type*} [CStarAlgebra D] [CStarAlgebra P]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace TracialHeadCoordinates

variable {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)

variable [W.vacuum.HasOrthogonalProjection]

/-- The exceptional component after a left letter is the tensor slice against
its adjoint applied to the trace vector. -/
theorem vacuum_slice (hτ : GD.trace 1 = 1) (d : D) (z : H) :
    W.vacuum.starProjection (G.left (ι d) z) =
      W.unitary.symm (hilbertTensorInsert (GD.vector 1)
        (tensorSlice (GD.vector (star d)) (W.unitary z))) := by
  have hΩ := norm_tracialTraceVector GD.trace GD.vector GD.inner_vector hτ
  let := vacuumSubspace_hasOrthogonalProjection (F := F) (GD.vector 1) hΩ
  have h := vacuum_slice_in_coordinates W.unitary (GD.vector 1) W.vacuum
    (G.left (ι d)) (GD.left d)
    (tracialVacuumSubspace_projection_coordinates W.unitary (GD.vector 1) hΩ)
    (W.left_head d) z
  simpa only [GD.left_adjoint_traceVector] using h

end TracialHeadCoordinates
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeHeadCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Surjectivity and left-action covariance of the first-factor tensor map. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem centered_word_mem_freeHead_range (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) {side : Bool} {xs : List P}
    (hxs : AlternatingCenteredWord G.trace A D side xs) :
    G.vector xs.prod ∈ Set.range (freeHeadIsometry G A D hτ hf) := by
  have ht (ys : CenteredWordParameter G A D true) :
      G.vector ys.1.prod ∈ Set.range (freeHeadIsometry G A D hτ hf) := by
    refine ⟨freeHeadTensor G A D (1, ys), ?_⟩
    rw [freeHeadIsometry_tensor, freeHeadVector, OneMemClass.coe_one, one_mul]
  cases side with
  | true => exact ht ⟨xs, hxs⟩
  | false =>
    cases hxs with
    | nil => exact ht ⟨[], .nil true⟩
    | @cons _ d ys hd _ hys =>
      refine ⟨freeHeadTensor G A D (⟨d, hd⟩, ⟨ys, hys⟩), ?_⟩
      exact freeHeadIsometry_tensor G A D hτ hf _

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem freeHeadIsometry_surjective (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) (hgen : ReducedWordGenerated G A D) :
    Function.Surjective (freeHeadIsometry G A D hτ hf) := by
  let S := (freeHeadIsometry G A D hτ hf).toLinearMap.range
  have hs : centeredFreeWordSpan G A D ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨side, xs, hxs, rfl⟩
    exact centered_word_mem_freeHead_range G A D hτ hf hxs
  have hc : IsClosed (S : Set H) :=
    (freeHeadIsometry G A D hτ hf).isometry.isClosedEmbedding.isClosed_range
  have ht := (centeredFreeWordSpan G A D).topologicalClosure_minimal hs hc
  rw [centeredFreeWordSpan_dense G A D hτ hgen] at ht
  intro x
  exact ht (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ H))

def freeHeadEquiv (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (hgen : ReducedWordGenerated G A D) :
    HilbertTensor (G.baseSpace D) (centeredWordSpace G A D true) ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (freeHeadIsometry G A D hτ hf)
    (freeHeadIsometry_surjective G A D hτ hf hgen)

omit [IsClosed (A : Set P)] in
theorem freeHeadIsometry_covariance (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (d : D) (z : HilbertTensor (G.baseSpace D) (centeredWordSpace G A D true)) :
    freeHeadIsometry G A D hτ hf (tensorHeadAction ((G.baseGeometry D).left d) z) =
      G.left (d : P) (freeHeadIsometry G A D hτ hf z) := by
  let f := (freeHeadIsometry G A D hτ hf).toContinuousLinearMap.comp
      (tensorHeadAction ((G.baseGeometry D).left d)) -
    (G.left (d : P)).comp (freeHeadIsometry G A D hτ hf).toContinuousLinearMap
  have he : f = 0 := continuousLinearMap_eq_zero_of_total (freeHeadTensor G A D)
    (freeHeadTensor_total G A D) f (by
      rintro ⟨e, xs⟩
      change freeHeadIsometry G A D hτ hf
          (tensorHeadAction ((G.baseGeometry D).left d) (freeHeadTensor G A D (e, xs))) -
        G.left (d : P) (freeHeadIsometry G A D hτ hf (freeHeadTensor G A D (e, xs))) = 0
      unfold freeHeadTensor
      rw [tensorHeadAction_insert]
      have hde : (G.baseGeometry D).left d (G.baseVector D e) = G.baseVector D (d * e) :=
        (G.baseGeometry D).left_vector d e
      rw [hde]
      change freeHeadIsometry G A D hτ hf (freeHeadTensor G A D (d * e, xs)) -
        G.left (d : P) (freeHeadIsometry G A D hτ hf (freeHeadTensor G A D (e, xs))) = 0
      rw [freeHeadIsometry_tensor, freeHeadIsometry_tensor, freeHeadVector,
        freeHeadVector, G.left_vector]
      change G.vector (((d : P) * (e : P)) * xs.1.prod) -
        G.vector ((d : P) * ((e : P) * xs.1.prod)) = 0
      rw [mul_assoc, sub_self])
  exact sub_eq_zero.mp (congrArg (fun f => f z) he)

/-- The raw head coordinates of the reduced product, with their actual
left multiplication action. -/
def freeTracialHeadCoordinates (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (hgen : ReducedWordGenerated G A D) :
    TracialHeadCoordinates (G.baseGeometry D) G D.subtype (centeredWordSpace G A D true) where
  unitary := (freeHeadEquiv G A D hτ hf hgen).symm
  left_head d z := by
    apply (freeHeadEquiv G A D hτ hf hgen).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    have hc := freeHeadIsometry_covariance G A D hτ hf d
      ((freeHeadEquiv G A D hτ hf hgen).symm z)
    have hi : freeHeadIsometry G A D hτ hf
        ((freeHeadEquiv G A D hτ hf hgen).symm z) = z :=
      (freeHeadEquiv G A D hτ hf hgen).apply_symm_apply z
    rw [hi] at hc
    exact hc.symm

omit [IsClosed (A : Set P)] in
theorem freeTracialHeadCoordinates_vacuum (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) (hgen : ReducedWordGenerated G A D) :
    (freeTracialHeadCoordinates G A D hτ hf hgen).vacuum =
      (centeredWordSpace G A D true).toSubmodule := by
  have he (y : centeredWordSpace G A D true) :
      freeHeadEquiv G A D hτ hf hgen (hilbertTensorInsert (G.baseVector D 1) y) = (y : H) := by
    exact (freeHeadIsometry_left G A D hτ hf 1 y).trans (by
      simp only [OneMemClass.coe_one, map_one, ContinuousLinearMap.one_def,
        ContinuousLinearMap.id_apply])
  change (vacuumSubspace (G.baseVector D 1)).map
    (freeHeadEquiv G A D hτ hf hgen).toLinearIsometry.toLinearMap = _
  ext x
  constructor
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    change freeHeadEquiv G A D hτ hf hgen
      (hilbertTensorInsert (G.baseVector D 1) y) ∈ centeredWordSpace G A D true
    rw [he]
    exact y.property
  · intro hx
    refine ⟨hilbertTensorInsert (G.baseVector D 1) ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    exact he ⟨x, hx⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_LeadingWordGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complement of the words starting in one factor consists exactly of
the nonempty words starting in the other factor. -/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

theorem centeredFreeWordSpan_le_sides (side : Bool) :
    centeredFreeWordSpan G A D ≤ (centeredWordSpace G A D side).toSubmodule ⊔
      (leadingWordSpace G A D (!side)).toSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, xs, hxs, rfl⟩
  by_cases h : s = side
  · subst s
    exact Submodule.mem_sup_left (closedFamilyVector (centeredWordFamily G A D side)
      ⟨xs, hxs⟩).property
  · have he : s = !side := by cases s <;> cases side <;> simp_all
    subst s
    by_cases hn : xs = []
    · subst xs
      exact Submodule.mem_sup_left (vacuum_mem_centeredWordSpace G A D side)
    · exact Submodule.mem_sup_right (closedFamilyVector (leadingWordFamily G A D (!side))
        ⟨⟨xs, hxs⟩, hn⟩).property

theorem centeredWordSpace_orthogonal (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) (hgen : ReducedWordGenerated G A D) (side : Bool) :
    (centeredWordSpace G A D side).toSubmoduleᗮ = (leadingWordSpace G A D (!side)).toSubmodule := by
  apply orthogonal_eq_of_dense_sup
  · intro x y
    cases side <;> exact inner_eq_zero_symm.mp (inner_leading_opposite_space G A D hf _ y x)
  · apply top_unique
    rw [← centeredFreeWordSpan_dense G A D hτ hgen]
    exact Submodule.topologicalClosure_mono (centeredFreeWordSpan_le_sides G A D side)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialRepeatedWords
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realize the abstract propagation data by actual tracial left multipliers.
The remaining word data are elementary reduced-word multiplication and
isometry identities; the scaled support and vanishing coefficient are proved. -/

noncomputable section
namespace KadisonSimilarity

variable {D P E H F B V : Type*} [CStarAlgebra D] [CStarAlgebra P]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)
  [W.vacuum.HasOrthogonalProjection]
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq)) (a : ℝ)
  (Y : H →L[ℂ] H) (B₀ : B →L[ℂ] B) (Bₖ : V →L[ℂ] V)

namespace TracialRepeatedWordRealization

variable {W z a Y B₀ Bₖ}
  (R : TracialRepeatedWordRealization W z a Y B₀ Bₖ)

/-- The full abstract propagation data are derived from the raw word
realization and the actual corner Haar unitary. -/
def propagationData (hτ : GD.trace 1 = 1) (ha : 0 < a)
    (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a) :
    RepeatedLetterWords (E := E) (F := F) Y B₀ Bₖ W.vacuum a where
  repeatVector := R.repeatVector
  word := R.word
  small := R.small
  small_norm := R.small_norm
  level_zero := R.level_zero
  level_repeated := R.level_repeated
  support := G.left (ι q)
  support_small := R.support_small
  letter n := G.left (ι (haarCornerLetter z a n))
  letter_scale n := G.embedded_left_scaled_initial ι _ q _
    (star_haarCornerLetter_mul_self z ha.le n)
  wordPrefix n := G.left (R.prefixElement n)
  word_factor := R.word_factor
  prefix_isometry := R.prefix_isometry
  prefix_bound := R.prefix_bound
  prefix_bound_le := R.prefix_bound_le
  tensor_coordinates := W.unitary.toContinuousLinearEquiv.toContinuousLinearMap
  vacuum_insert := W.unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (hilbertTensorInsert (GD.vector 1))
  adjoint_letters n := GD.vector (star (haarCornerLetter z a n))
  adjoint_letters_orthonormal := GD.haarCornerLetter_adjoint_orthonormal z ha htrace hhaar
  vacuum_slice _ y := W.vacuum_slice hτ _ y

end TracialRepeatedWordRealization
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCreationDischarge
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two elementary creation maps in the published interface, constructed
on the actual tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

section TensorMap
variable {E F K L : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

def hilbertTensorMapIsometry (f : E →ₗᵢ[ℂ] K) (g : F →ₗᵢ[ℂ] L) :
    HilbertTensor E F →ₗᵢ[ℂ] HilbertTensor K L := (TensorProduct.mapIsometry f g).completion

@[simp] theorem hilbertTensorMapIsometry_insert (f : E →ₗᵢ[ℂ] K) (g : F →ₗᵢ[ℂ] L)
    (x : E) (y : F) : hilbertTensorMapIsometry f g (hilbertTensorInsert x y) =
      hilbertTensorInsert (f x) (g y) := by
  change (TensorProduct.mapIsometry f g).completion
    ((x ⊗ₜ[ℂ] y : E ⊗[ℂ] F) : UniformSpace.Completion (E ⊗[ℂ] F)) = _
  rw [LinearIsometry.completion_apply_coe, TensorProduct.mapIsometry_apply,
    TensorProduct.map_tmul]
  rfl

end TensorMap

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ReducedWordAutomorphisms
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense reduced words provide the tracial generation needed to turn
published factor embeddings into actual free-product automorphisms. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

/-- The ordinary reduced-word density supplies the tracial algebraic generation;
no separate factor-generation hypothesis is required for automorphism extension. -/
theorem factorsTraciallyGenerate_of_reducedWordGenerated
    (hgen : ReducedWordGenerated G A D) : G.FactorsTraciallyGenerate A D := by
  let V : factorAlgebra A D →ₗ[ℂ] H :=
    G.vector.comp (factorAlgebra A D).subtype.toLinearMap
  have hspan : Submodule.span ℂ (reducedWordVectors G A D) ≤ V.range := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨n, d, b, a, c, _ha, _hc, rfl⟩ := hx
    refine ⟨⟨_, reducedWord_mem_factorAlgebra A D n d b a c⟩, rfl⟩
  have htop : V.range.topologicalClosure = ⊤ := by
    apply top_unique
    have h := Submodule.topologicalClosure_mono hspan
    rw [hgen] at h
    exact h
  change DenseRange V
  apply dense_iff_closure_eq.mpr
  change (V.range.topologicalClosure : Set H) = Set.univ
  rw [htop]
  rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CompressionSetup
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite head coordinates and the tail projection for compression. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

theorem reducedWordGenerated_swap (hτ : G.trace 1 = 1) (hgen : ReducedWordGenerated G A D) :
    ReducedWordGenerated G D A := by
  apply G.reducedWordGenerated_of_factorsTraciallyGenerate D A hτ
  have hg := G.factorsTraciallyGenerate_of_reducedWordGenerated A D hgen
  have he : TracialCornerGeometry.factorAlgebra D A = TracialCornerGeometry.factorAlgebra A D := by
    unfold TracialCornerGeometry.factorAlgebra
    rw [Set.union_comm]
  change DenseRange (G.vector.comp (TracialCornerGeometry.factorAlgebra D A).subtype.toLinearMap)
  rw [he]
  exact hg

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CompressionProjectionTransport
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal inclusion projections in the head tensor coordinates. -/

noncomputable section
namespace KadisonSimilarity

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace E] in
/-- Factoring the inclusion through the vacuum insertion gives the exact
first-letter projection used in the compression model. -/
theorem firstLetterProjection_of_inclusion
    (Ω : E) (j : F →ₗᵢ[ℂ] K) (v : F →ₗᵢ[ℂ] HilbertTensor E K)
    (hv : v.toContinuousLinearMap = (hilbertTensorInsert Ω).comp j.toContinuousLinearMap) :
    firstLetterProjection Ω (isometryRangeProjection j) = isometryRangeProjection v := by
  simp only [isometryRangeProjection]
  rw [hv, ContinuousLinearMap.adjoint_comp]
  simp only [firstLetterProjection, ContinuousLinearMap.comp_assoc]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixCovariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual matrix-conjugation actions on tracial tensor words

The conjugation action is constructed from the represented unitary and the
tracial conjugation. Its action on completed tensor words is obtained by genuine
tensor-product isometries.
-/

noncomputable section
namespace KadisonSimilarity
open scoped TensorProduct

universe u v
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {R : Type v} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [CompleteSpace E] {α : Type*} [Fintype α] [DecidableEq α]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] R)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a)) (hdense : DenseRange V)

include hleft in
theorem tracialUnitaryConjugation_commutes (u : Matrix.unitaryGroup α ℂ) (x : E) :
    tracialConjugation τ V hinner htrace hdense
      (tracialUnitaryConjugation τ V L ι hinner htrace hdense u x) =
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u
      (tracialConjugation τ V hinner htrace hdense x) := by
  refine hdense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  simp only [tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense,
    tracialConjugation_apply_vector, star_mul, star_star, mul_assoc]

theorem centeredUnitaryConjugation_commutes (u : Matrix.unitaryGroup α ℂ)
    (x : centeredSubspace (V 1)) :
    centeredTracialConjugation τ V hinner htrace hdense
      (centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u x) =
    centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u
      (centeredTracialConjugation τ V hinner htrace hdense x) := by
  apply Subtype.ext
  exact tracialUnitaryConjugation_commutes τ V L ι hinner hleft htrace hdense u x

/-- The constructed conjugation action carries actual centered matrix vectors
to the centered vectors of their matrix conjugates. -/
theorem centeredUnitaryConjugation_center (hτ : τ 1 = 1) (u : Matrix.unitaryGroup α ℂ)
    (a : Matrix α α ℂ) :
    centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u
      (tracialCenter V (ι a)) =
      tracialCenter V (ι ((u : Matrix α α ℂ) * a * star (u : Matrix α α ℂ))) := by
  apply Subtype.ext
  change tracialUnitaryConjugation τ V L ι hinner htrace hdense u
    (tracialCenter V (ι a) : E) = _
  rw [coe_tracialCenter τ V hinner hτ, coe_tracialCenter τ V hinner hτ]
  rw [map_sub, map_smul,
    tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense,
    tracialUnitaryConjugation_traceVector τ V L ι hinner hleft htrace hdense]
  simp only [map_mul, map_star]
  rw [trace_matrix_conjugation τ ι htrace]

include hleft in
theorem tracialUnitaryConjugation_star_matrix (u : Matrix.unitaryGroup α ℂ)
    (a : Matrix α α ℂ) :
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u (V (ι (star a))) =
      V (ι (star ((u : Matrix α α ℂ) * a * star (u : Matrix α α ℂ)))) := by
  rw [tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense]
  simp only [map_star, map_mul, star_mul, star_star, mul_assoc]

/-- Actual matrix-unitary intertwining supplies the word covariance used by the
finite invariant theory. The source and test word formulas are proved here. -/
def tracialMatrixWordCovariance (hτ : τ 1 = 1)
    (hι : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a)
    {k l : ℕ} (Y : EndpointTensor E (centeredSubspace (V 1)) k →L[ℂ]
      EndpointTensor E (centeredSubspace (V 1)) l)
    (hY : ∀ u, Y.comp
      (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u k).toContinuousLinearMap =
      (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u l).toContinuousLinearMap.comp Y) :
    MatrixWordCovariance (tracialMatrixStage τ V L ι hinner hleft hι)
      (centeredTracialConjugation τ V hinner htrace hdense) (V 1) Y where
  sourceAction u := tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u k
  testAction u := tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u l
  intertwine := hY
  source_covariance u v := by
    change endpointWord (V 1) (fun i => tracialCenter V
      (ι ((u : Matrix α α ℂ) * v (some (Sum.inl i)) * star (u : Matrix α α ℂ)))) = _
    rw [tracialMatrixWordAction, endpointTensorIsometry_apply,
      tracialUnitaryConjugation_traceVector τ V L ι hinner hleft htrace hdense]
    apply congrArg (endpointWord (V 1))
    funext i
    exact (centeredUnitaryConjugation_center τ V L ι hinner hleft htrace hdense hτ u _).symm
  test_covariance u v := by
    change endpointWord
      (V (ι (star ((u : Matrix α α ℂ) * v none * star (u : Matrix α α ℂ)))))
      (fun j => centeredTracialConjugation τ V hinner htrace hdense (tracialCenter V
        (ι ((u : Matrix α α ℂ) * v (some (Sum.inr j)) * star (u : Matrix α α ℂ))))) = _
    rw [tracialMatrixWordAction, endpointTensorIsometry_apply]
    apply congrArg₂ (fun d (x : Fin l → centeredSubspace (V 1)) => endpointWord d x)
    · exact (tracialUnitaryConjugation_star_matrix τ V L ι hinner hleft htrace hdense u _).symm
    · funext j
      rw [← centeredUnitaryConjugation_center τ V L ι hinner hleft htrace hdense hτ]
      exact centeredUnitaryConjugation_commutes τ V L ι hinner hleft htrace hdense u _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_EmbeddedWordActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensorMapIsometry_insert _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual embedded matrix actions supply the action record used by the
invariant-word classification. Adjoint covariance follows from the represented
star and inverse laws, and the source/test formulas from tracial word covariance. -/

noncomputable section
namespace KadisonSimilarity

section TensorAdjoints
variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem hilbertTensorLift_adjoint (T : K →L[ℂ] K) :
    (hilbertTensorLift (G := F) T).adjoint = hilbertTensorLift T.adjoint := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  apply hilbertTensor_ext_inner_insert
  intro b y
  simp only [ContinuousLinearMap.adjoint_inner_right, hilbertTensorLift_insert,
    inner_hilbertTensorInsert]

theorem endpointHeadAction_adjoint {n : ℕ} (p : E →L[ℂ] E) :
    (endpointHeadAction (F := F) (n := n) p).adjoint = endpointHeadAction p.adjoint := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro d x
  apply hilbertTensor_ext_inner_insert
  intro c y
  change inner ℂ (endpointInsert c y)
      ((endpointHeadAction p).adjoint (endpointInsert d x)) =
    inner ℂ (endpointInsert c y) (endpointHeadAction p.adjoint (endpointInsert d x))
  rw [ContinuousLinearMap.adjoint_inner_right, endpointHeadAction_insert,
    endpointHeadAction_insert, inner_endpointInsert, inner_endpointInsert,
    ContinuousLinearMap.adjoint_inner_right]

end TensorAdjoints

section TracialInverses
universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {α : Type*} [Fintype α] [DecidableEq α]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] R)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a)) (hdense : DenseRange V)

include hleft in
/-- Inverse matrix conjugations cancel on the entire tracial Hilbert space,
by their algebraic action on its dense represented vectors. -/
theorem tracialUnitaryConjugation_mul_inv (u : Matrix.unitaryGroup α ℂ) (x : E) :
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u
      (tracialUnitaryConjugation τ V L ι hinner htrace hdense u⁻¹ x) = x := by
  refine hdense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  rw [tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense,
    tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense]
  have hinv : ι (↑u⁻¹ : Matrix α α ℂ) = star (ι (u : Matrix α α ℂ)) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, map_star]
  have hunit : ι (u : Matrix α α ℂ) * star (ι (u : Matrix α α ℂ)) = 1 := by
    have hu : (u : Matrix α α ℂ) * star (u : Matrix α α ℂ) = 1 := u.property.2
    rw [← map_star, ← map_mul, hu, map_one]
  rw [hinv, star_star]
  congr 1
  calc
    ι (u : Matrix α α ℂ) * (star (ι (u : Matrix α α ℂ)) * a *
        ι (u : Matrix α α ℂ)) * star (ι (u : Matrix α α ℂ)) =
      (ι (u : Matrix α α ℂ) * star (ι (u : Matrix α α ℂ))) * a *
        (ι (u : Matrix α α ℂ) * star (ι (u : Matrix α α ℂ))) := by noncomm_ring
    _ = a := by rw [hunit, one_mul, mul_one]

theorem centeredUnitaryConjugation_mul_inv (u : Matrix.unitaryGroup α ℂ)
    (x : centeredSubspace (V 1)) :
    centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u
      (centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u⁻¹ x) = x := by
  apply Subtype.ext
  exact tracialUnitaryConjugation_mul_inv τ V L ι hinner hleft htrace hdense u x

/-- The inverse word action is obtained by inverting the actual matrix unitary. -/
theorem tracialMatrixWordAction_mul_inv (u : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u n).toContinuousLinearMap.comp
      (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u⁻¹ n).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ (EndpointTensor E (centeredSubspace (V 1)) n) := by
  apply continuousLinearMap_ext_endpointWords
  intro d x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    LinearIsometry.coe_toContinuousLinearMap,
    tracialMatrixWordAction, endpointTensorIsometry_apply,
    tracialUnitaryConjugation_mul_inv τ V L ι hinner hleft htrace hdense,
    centeredUnitaryConjugation_mul_inv τ V L ι hinner hleft htrace hdense]

/-- The adjoint action on completed words is the inverse matrix action. -/
theorem tracialMatrixWordAction_adjoint (u : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u n).toContinuousLinearMap.adjoint =
      (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u⁻¹ n).toContinuousLinearMap := by
  let W := tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u n
  let Z := tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u⁻¹ n
  have hW : W.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ _ := W.adjoint_comp_self
  have hZ : W.toContinuousLinearMap.comp Z.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ _ :=
    tracialMatrixWordAction_mul_inv τ V L ι hinner hleft htrace hdense u n
  change W.toContinuousLinearMap.adjoint = Z.toContinuousLinearMap
  calc
    W.toContinuousLinearMap.adjoint =
        W.toContinuousLinearMap.adjoint.comp (ContinuousLinearMap.id ℂ _) := by simp
    _ = W.toContinuousLinearMap.adjoint.comp (W.toContinuousLinearMap.comp Z.toContinuousLinearMap) := by rw [hZ]
    _ = (W.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap).comp Z.toContinuousLinearMap :=
      (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = Z.toContinuousLinearMap := by rw [hW, ContinuousLinearMap.id_comp]

end TracialInverses

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCompressionDischarge
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-letter compression model on the concrete reduced product. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

def freeCompressionHead (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (hgen : ReducedWordGenerated G A D) :
    TracialHeadCoordinates (G.baseGeometry A) G A.subtype (centeredWordSpace G D A true) :=
  freeTracialHeadCoordinates G D A hτ hf (reducedWordGenerated_swap G A D hτ hgen)

omit [IsClosed (D : Set P)] in
theorem freeCompressionAfterInclusion (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (hgen : ReducedWordGenerated G A D) :
    ((freeCompressionHead G A D hτ hf hgen).unitary.toLinearIsometry.comp
      (leadingWordSpace G D A true).toSubmodule.subtypeₗᵢ).toContinuousLinearMap =
      (hilbertTensorInsert (G.baseVector A 1)).comp
        (leadingIntoCentered G D A true).toContinuousLinearMap := by
  ext x
  change (freeCompressionHead G A D hτ hf hgen).unitary (x : H) =
    hilbertTensorInsert (G.baseVector A 1) (leadingIntoCentered G D A true x)
  apply (freeHeadEquiv G D A hτ hf (reducedWordGenerated_swap G A D hτ hgen)).injective
  change (freeHeadEquiv G D A hτ hf (reducedWordGenerated_swap G A D hτ hgen))
      ((freeHeadEquiv G D A hτ hf (reducedWordGenerated_swap G A D hτ hgen)).symm (x : H)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  symm
  exact (freeHeadIsometry_left G D A hτ hf 1 (leadingIntoCentered G D A true x)).trans (by
    simp only [OneMemClass.coe_one, map_one, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply, leadingIntoCentered_coe])

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialAutomorphismWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix-unitary word formula is derived from the algebraic product
formula and the actual implementation of a trace-preserving automorphism. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

/-- The genuine endpoint action on the tracial Hilbert space of the other factor. -/
def baseMatrixWordAction (n : ℕ) :
    EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n →ₗᵢ[ℂ]
      EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n :=
  tracialMatrixWordAction (G.baseGeometry D).trace (G.baseGeometry D).vector
    (G.baseGeometry D).left ι (G.baseGeometry D).inner_vector
    (G.baseGeometry D).left_vector (G.baseGeometry D).tracial
    (G.baseGeometry D).dense_vector u n

end TracialCornerGeometry

namespace TracialWordFormula

open TracialCornerGeometry

variable {G : TracialCornerGeometry P H} {A D : StarSubalgebra ℂ P}
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (θ : P ≃⋆ₐ[ℂ] P) (hθ : ∀ x, G.trace (θ x) = G.trace x)
  (hA : ∀ a : A, θ (a : P) = (a : P))
  (hD : ∀ d : D, θ (d : P) = (matrixConjugateLetter D ι u d : P))

local instance automorphismMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

local instance automorphismMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

end TracialWordFormula
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialEmbeddedWordStructure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tracial free-product actions instantiate finite-stage word
classification. Both head covariance and matrix-unitary covariance follow
from the ordinary reduced-word formula. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ s, Fintype (I s)] [∀ s, DecidableEq (I s)]
  [∀ s, Nonempty (I s)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)

/-- The matrix stage acts by actual ambient left multiplication. -/
def tracialMatrixLeftRepresentation (s : ℕ) : Matrix (I s) (I s) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  G.left.comp (D.subtype.comp (M.embedding s))

variable (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ s, G.MatrixConjugationExtensionInput D (M.embedding s) A)

/-- The finite matrix group acts by its constructed free-product automorphisms. -/
def tracialMatrixUnitaryRepresentation (s : ℕ) :
    Matrix.unitaryGroup (I s) ℂ →* unitary (H →L[ℂ] H) :=
  G.matrixExtensionUnitaryRepresentation A D (M.embedding s) hgen hfaithful (hext s)

variable (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (I s) : ℝ)) Filter.atTop Filter.atTop)

local instance tracialEmbeddedMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance
local instance tracialEmbeddedMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialHaarWordColumns
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Haar test columns used in propagation are actual reduced-word
inclusions. Their isometry and product formula follow from the word model
and the normalized corner Haar letters. -/

noncomputable section
namespace KadisonSimilarity

universe u v

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

local instance haarMultiplicityNormedFamily :
    ∀ k, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) k) :=
  fun _ => inferInstance

local instance haarMultiplicityInnerFamily :
    ∀ k, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) k) :=
  fun _ => inferInstance

variable (hτ : G.trace 1 = 1)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)

/-- Unit vacuum endpoint and unit centered Haar letters give isometric
columns at every word degree. -/
def haarRepeatedWordInclusion (k n : ℕ) : WordMultiplicity (G.baseVector A 1) k →ₗᵢ[ℂ] H :=
  repeatedWordInclusion U k (LinearIsometry.id :
    WordMultiplicity (G.baseVector A 1) k →ₗᵢ[ℂ] WordMultiplicity (G.baseVector A 1) k)
    (G.baseVector D 1) (G.baseHaarLetter D z ha htrace hhaar n)
    (G.norm_baseVector_one D hτ) (G.norm_baseHaarLetter D z ha htrace hhaar n)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialFreeCornerEstimate
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tracial word model supplies both errors in the Fourier
compression argument. The only remaining Fourier hypotheses below concern
the spectral test operator itself; level preservation and propagation are
derived from the matrix symmetries and the cited published inputs. -/

noncomputable section
namespace KadisonSimilarity

universe u v

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

namespace TracialCornerGeometry

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)
  (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)

local instance freeCornerMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance
local instance freeCornerMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact groups in free-product symmetrization are the actual matrix
unitary groups. Their compatibility follows from the nested matrix embeddings
and uniqueness of the trace-preserving extension on the two factors. -/

noncomputable section
namespace KadisonSimilarity

namespace TracialCornerGeometry

open MeasureTheory TopologicalSpace
open scoped Topology CStarAlgebra ComplexOrder

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)

/-- A nested matrix star embedding maps the compact unitary groups. -/
def matrixStageUnitaryInclusion (i j : ℕ) (h : i ≤ j) :
    Matrix.unitaryGroup (I i) ℂ →* Matrix.unitaryGroup (I j) ℂ :=
  (Unitary.map (StarMonoidHom.ofClass (M.inclusion i j h))).toMonoidHom

/-- Forgetting the unitary subtype gives the group homomorphism consumed
by the weak Haar integral. -/
def tracialMatrixUnitaryOperator (j : ℕ) :
    Matrix.unitaryGroup (I j) ℂ →* (H →L[ℂ] H) :=
  (unitary (H →L[ℂ] H)).subtype.comp
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j)

/-- The test elements supported by a projection of the selected trace. -/
def traceCornerElements (t : ℝ) : Set P :=
  {x | ∃ (e : P) (_ : IsStarProjection e), e ∈ D ∧ G.trace e = (t : ℂ) ∧
    e * x = x ∧ x * e = x}

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSpectralNorm
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.dihedralHalfProjection_projectionReflection _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow spectral arc has the required small norm in the original
algebra. Its creation model is applied on the closed algebra generated by
the two corner factors, with the normalized restricted trace. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (C D : StarSubalgebra ℂ P)
  [IsClosed (C : Set P)] [IsClosed (D : Set P)]
  (w d : Pˣ) (hp : IsStarProjection (dihedralHalfProjection d))
  (hpC : dihedralHalfProjection d ∈ C) (hpD : dihedralHalfProjection d ∈ D)
  (htp : G.trace (dihedralHalfProjection d) = (1 / 2 : ℂ))

/-- This is the ordinary normalized corner geometry before restriction to
the algebra generated by its two free factors. -/
def halfCornerGeometry :
    TracialCornerGeometry (CStarCorner (dihedralHalfProjection d) hp)
      (G.corner (dihedralHalfProjection d) (dihedralHalfProjection d)) :=
  G.normalizedCornerGeometry (dihedralHalfProjection d) hp (by norm_num : 0 < (1 / 2 : ℝ))
    (by simpa using htp)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialEmbeddingTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
  [∀ n, Nonempty (I n)]

/-- The real trace-orthonormal sequence is transported algebraically. -/
def transportRealTracialSequence (S : RealTracialSequence τ.toLinearMap) :
    RealTracialSequence (G.trace.comp φ.range.subtype.toLinearMap) where
  vector n := φ.rangeRestrict (S.vector n)
  trace_zero n := by change G.trace (φ (S.vector n)) = 0; rw [hφ]; exact S.trace_zero n
  selfadjoint n := by rw [← map_star, S.selfadjoint]
  inner n m := by
    change G.trace (star (φ (S.vector n)) * φ (S.vector m)) = _
    rw [← map_star, ← map_mul, hφ]
    exact S.inner n m

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialUltrapowerConstants
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both ultrapower constructions preserve the original constant Hilbert
space exactly. Compression back to that space recovers the original operator. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower NuclearUltrapower
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- The trace-preserving constant inclusion gives the actual GNS inclusion. -/
def constantTracialGNSInclusion : τ.GNS →ₗᵢ[ℂ] (quotientTrace τ h1 ω htr).GNS :=
  gnsTracialHomIsometry τ (quotientTrace τ h1 ω htr) (constant τ h1 ω htr)
    (quotientTrace_constant τ h1 ω htr)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_GeneratedDihedralAlgebras
attribute [-instance] _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two auxiliary algebras in the spectral test are the actual bounded
L² closures of their algebraic generators. Their inclusions and the density
premises in the free-corner theorem follow from this construction. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- The finite dihedral von Neumann algebra, expressed through its bounded
L² closure; no normal-form density is imposed as an extra premise. -/
def generatedDihedralAlgebra (d s : P) : StarSubalgebra ℂ P :=
  G.l2GeneratedAlgebra (StarAlgebra.adjoin ℂ ({d, s} : Set P))

instance generatedDihedralAlgebra_isClosed (d s : P) :
    IsClosed (G.generatedDihedralAlgebra d s : Set P) :=
  G.l2GeneratedAlgebra_isClosed _

theorem first_mem_generatedDihedralAlgebra (d s : P) :
    d ∈ G.generatedDihedralAlgebra d s :=
  G.le_l2GeneratedAlgebra _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert d _))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCornerApplication
attribute [-instance] _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the proved free-corner theorem using the chosen matrix frame,
its containing half projection, and the actual L²-generated test algebras.
All ordinary generation and support identities are derived here. -/

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
  (s : A) (hsstar : star s = s) (hssq : s * s = 1)

local notation "d" => Q.half.reflection
local notation "dU" => symmetryUnit (d : P)
  (congrArg (fun x : D => (x : P)) Q.half.reflection_square)
local notation "p" => dihedralHalfProjection dU
local notation "hp" => symmetryHalfProjectionProof d Q.half.reflection_star
  Q.half.reflection_square
local notation "C" => G.generatedDihedralAlgebra (d : P) (s : P)
local notation "K" => StarSubalgebra.topologicalClosure (factorAlgebra
  (CStarCorner.subalgebra p hp D
    (symmetryHalfProjection_mem D d Q.half.reflection_square Q.half.reflection.property))
  (CStarCorner.subalgebra p hp C
    (symmetryHalfProjection_mem C d Q.half.reflection_square
      (G.first_mem_generatedDihedralAlgebra (d : P) (s : P)))))

local instance smallFrameCorner_isClosed : IsClosed (K : Set (CStarCorner p hp)) :=
  StarSubalgebra.isClosed_topologicalClosure _

/-- The elementary compression model on the actual half corner. -/
def smallFrameCompressionInput (hτ : G.trace 1 = 1) : Prop :=
  RicardXuCompressionInput
    ((G.halfCornerGeometry dU hp (trace_dihedralHalfProjection G.trace hτ
      dU (Q.half.reflection_trace hτ))).baseGeometry K)
    ((CStarCorner.subalgebra p hp D
      (symmetryHalfProjection_mem D d Q.half.reflection_square Q.half.reflection.property)).comap (K).subtype)
    ((CStarCorner.subalgebra p hp C
      (symmetryHalfProjection_mem C d Q.half.reflection_square
        (G.first_mem_generatedDihedralAlgebra (d : P) (s : P)))).comap (K).subtype)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeMatrixFactorAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem freeMatrixConjugationIsometry_other_word (x : D)
    (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    W (G.left (x : P) (G.vector ((d : P) *
      alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P)))) =
    G.left (matrixConjugateLetter D ι u x : P)
      (W (G.vector ((d : P) *
        alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P)))) := by
  rw [G.left_vector, G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen n d b a c ha hc,
    G.left_vector]
  have h := G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen
    n (x * d) b a c ha hc
  simpa only [MulMemClass.coe_mul, matrixConjugateLetter_product, mul_assoc] using h

theorem freeMatrixConjugationIsometry_other (x : D) :
    (W).toContinuousLinearMap.comp (G.left (x : P)) =
      (G.left (matrixConjugateLetter D ι u x : P)).comp (W).toContinuousLinearMap := by
  apply sub_eq_zero.mp
  apply continuousLinearMap_eq_zero_of_total (G.freeWordFamily A D)
    (G.freeWordFamily_total A D hgen)
  rintro ⟨n, p⟩
  change W (G.left (x : P) (G.freeWordFamily A D ⟨n, p⟩)) -
    G.left (matrixConjugateLetter D ι u x : P) (W (G.freeWordFamily A D ⟨n, p⟩)) = 0
  exact sub_eq_zero.mpr (G.freeMatrixConjugationIsometry_other_word A D ι u hτ hf hgen
    x n p.2.1 p.1.2 (fun i => (p.1.1 i).1) (fun i => (p.2.2 i).1)
    (fun i => (p.1.1 i).2) (fun i => (p.2.2 i).2))

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeMatrixBaseAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centering the first two letters proves covariance for the base factor. -/

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
local notation "θ" => matrixConjugateLetter D ι u

theorem freeMatrix_base_product (n : ℕ) (x : A) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    W (G.vector ((x : P) * (d : P) *
      (alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P)))) =
    G.vector ((x : P) * (θ d : P) *
      (alternatingProduct (fun i => (a i : P)) (fun i => (θ (c i) : P)) * (b : P))) := by
  induction n using Nat.strong_induction_on generalizing x d b with
  | h n ih =>
    let x₀ : A := x - G.trace (x : P) • 1
    let d₀ : D := d - G.trace (d : P) • 1
    have hx₀ : G.trace (x₀ : P) = 0 := by
      change G.trace ((x : P) - G.trace (x : P) • (1 : P)) = 0
      simp only [map_sub, map_smul, hτ, smul_eq_mul, mul_one, sub_self]
    have hd₀ : G.trace (d₀ : P) = 0 := by
      change G.trace ((d : P) - G.trace (d : P) • (1 : P)) = 0
      simp only [map_sub, map_smul, hτ, smul_eq_mul, mul_one, sub_self]
    let w := alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P)
    let w' := alternatingProduct (fun i => (a i : P)) (fun i => (θ (c i) : P)) * (b : P)
    have hxd : W (G.vector ((x₀ : P) * (d₀ : P) * w)) =
        G.vector ((x₀ : P) * (θ d₀ : P) * w') := by
      simpa only [alternatingProduct_cons, OneMemClass.coe_one, one_mul,
        matrixConjugateLetter_one_letter, Fin.cons_zero, Fin.cons_succ, w, w', mul_assoc] using
        G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen (n + 1) 1 b
          (Fin.cons x₀ a) (Fin.cons d₀ c)
          (fun i => Fin.cases hx₀ ha i) (fun i => Fin.cases hd₀ hc i)
    have hdw : W (G.vector ((d₀ : P) * w)) = G.vector ((θ d₀ : P) * w') := by
      simpa only [w, w', mul_assoc] using
        G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen n d₀ b a c ha hc
    have hxw : W (G.vector ((x : P) * w)) = G.vector ((x : P) * w') := by
      cases n with
      | zero =>
        simpa only [w, w', alternatingProduct_zero, one_mul, MulMemClass.coe_mul] using
          G.freeMatrixConjugationIsometry_base A D ι u hτ hf hgen (x * b)
      | succ m =>
        have h := ih m (Nat.lt_succ_self m) (x * a 0) (c 0) b
          (fun i => a i.succ) (fun i => c i.succ)
          (fun i => ha i.succ) (fun i => hc i.succ)
        simpa only [w, w', alternatingProduct_cons, MulMemClass.coe_mul, mul_assoc] using h
    have heq : (x : P) * (d : P) * w =
        (x₀ : P) * (d₀ : P) * w + G.trace (x : P) • ((d₀ : P) * w) +
          G.trace (d : P) • ((x : P) * w) := by
      change (x : P) * (d : P) * w =
        ((x : P) - G.trace (x : P) • 1) * ((d : P) - G.trace (d : P) • 1) * w +
        G.trace (x : P) • (((d : P) - G.trace (d : P) • 1) * w) +
        G.trace (d : P) • ((x : P) * w)
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    have hd₀eq : (θ d₀ : P) = (θ d : P) - G.trace (d : P) • 1 := by
      dsimp only [d₀]
      rw [matrixConjugateLetter_sub, matrixConjugateLetter_smul,
        matrixConjugateLetter_one_letter]
      rfl
    have heq' : (x : P) * (θ d : P) * w' =
        (x₀ : P) * (θ d₀ : P) * w' + G.trace (x : P) • ((θ d₀ : P) * w') +
          G.trace (d : P) • ((x : P) * w') := by
      rw [hd₀eq]
      change (x : P) * (θ d : P) * w' =
        ((x : P) - G.trace (x : P) • 1) * ((θ d : P) - G.trace (d : P) • 1) * w' +
        G.trace (x : P) • (((θ d : P) - G.trace (d : P) • 1) * w') +
        G.trace (d : P) • ((x : P) * w')
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    change W (G.vector ((x : P) * (d : P) * w)) = G.vector ((x : P) * (θ d : P) * w')
    rw [heq, map_add, map_add, map_smul, map_smul, map_add, map_add, map_smul, map_smul,
      hxd, hdw, hxw]
    rw [heq', map_add, map_add, map_smul, map_smul]

theorem freeMatrixConjugationIsometry_base_left (x : A) :
    (W).toContinuousLinearMap.comp (G.left (x : P)) =
      (G.left (x : P)).comp (W).toContinuousLinearMap := by
  apply sub_eq_zero.mp
  apply continuousLinearMap_eq_zero_of_total (G.freeWordFamily A D)
    (G.freeWordFamily_total A D hgen)
  rintro ⟨n, p⟩
  change W (G.left (x : P) (G.freeWordFamily A D ⟨n, p⟩)) -
    G.left (x : P) (W (G.freeWordFamily A D ⟨n, p⟩)) = 0
  apply sub_eq_zero.mpr
  change W (G.left (x : P) (tracialAlgebraFamily G A D n p)) =
    G.left (x : P) (W (tracialAlgebraFamily G A D n p))
  unfold tracialAlgebraFamily
  rw [G.left_vector, G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen
    n p.2.1 p.1.2 (fun i => (p.1.1 i).1) (fun i => (p.2.2 i).1)
    (fun i => (p.1.1 i).2) (fun i => (p.2.2 i).2), G.left_vector]
  simpa only [mul_assoc] using
    G.freeMatrix_base_product A D ι u hτ hf hgen n x p.2.1 p.1.2
      (fun i => (p.1.1 i).1) (fun i => (p.2.2 i).1)
      (fun i => (p.1.1 i).2) (fun i => (p.2.2 i).2)

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeMatrixExtension
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

local notation "U" => G.freeMatrixExtensionUnitary A D ι u h1 hf hgen

theorem freeMatrixExtensionUnitary_base (a : A) :
    (U).conjStarAlgEquiv (G.left (a : P)) = G.left (a : P) := by
  apply conjugate_eq_of_intertwining
  exact G.freeMatrixConjugationIsometry_base_left A D ι u h1 hf
    (G.reducedWordGenerated_of_factorsTraciallyGenerate A D h1 hgen) a

theorem freeMatrixExtensionUnitary_other (d : D) :
    (U).conjStarAlgEquiv (G.left (d : P)) =
      G.left (matrixConjugateLetter D ι u d : P) := by
  apply conjugate_eq_of_intertwining
  exact G.freeMatrixConjugationIsometry_other A D ι u h1 hf
    (G.reducedWordGenerated_of_factorsTraciallyGenerate A D h1 hgen) d

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_GeneratedEmbeddings
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

def generatedEmbeddingRealSequence (S : RealTracialSequence τR.toLinearMap) :=
  transportRealTracialSequence τR
    (gnsTracialGeometry (restrictedPositiveTrace τ L)
      (restrictedPositiveTrace_tracial τ L htr))
    (ψ.codRestrict L hψ) (generatedEmbedding_preserves_trace τ htr L τR ψ hψ htrace) S

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CanonicalGeneratedModel
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable [PartialOrder R] [StarOrderedRing R]
  (τR : R →ₚ[ℂ] ℂ) (hψτ : ∀ r, τ (ψ r) = τR r)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

def canonicalGeneratedRealSequence (S : RealTracialSequence τR.toLinearMap) :=
  generatedEmbeddingRealSequence τ htr (canonicalGeneratedAlgebra τ htr φ ψ) τR ψ
    (canonicalGenerated_second_mem τ htr φ ψ) hψτ S

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GeneratedGNSRecovery
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- Compress an ambient operator to the intermediate generated algebra. -/
def generatedGNSCompression (S : τP.GNS →L[ℂ] τP.GNS) :
    (restrictedPositiveTrace τP L).GNS →L[ℂ] (restrictedPositiveTrace τP L).GNS :=
  (restrictedTracialGNSInclusion τP L).toContinuousLinearMap.adjoint.comp
    (S.comp (restrictedTracialGNSInclusion τP L).toContinuousLinearMap)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CanonicalGeneratedOperators
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Operator transfer to the constructed generated algebra. These results
use the exact factor embeddings of the canonical model. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)

def canonicalGeneratedOperator (S : τ.GNS →L[ℂ] τ.GNS) :=
  generatedGNSCompression τ (canonicalGeneratedAlgebra τ htr φ ψ) S

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

theorem firstCopiesInclusion_adjoint_self (n : ℕ) :
    (firstCopiesInclusion (H := H) n).adjoint.comp (firstCopiesInclusion n) =
      ContinuousLinearMap.id ℂ (HilbertCopies H n) := by
  ext x i
  simp only [comp_apply, firstCopiesInclusion_adjoint_apply, firstCopiesInclusion_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply, id_apply]
  simp only [Fin.val_inj]
  simp

/-- The coordinate insertion preserves the Hilbert norm. -/
def firstCopiesIsometry (n : ℕ) : HilbertCopies H n →ₗᵢ[ℂ] CountableCopies H where
  toLinearMap := (firstCopiesInclusion n).toLinearMap
  norm_map' := (norm_map_iff_adjoint_comp_self _).mpr
    (firstCopiesInclusion_adjoint_self n)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProjectionFieldReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_adjoint _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerInto_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightTransferBack_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightTransferMap_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightTransfer_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing operator fields to their projection fibers

Each orthogonal projection has an actual closed Hilbert range. Compression
of a supported operator to this range preserves its norm and action. These
constructions are pointwise, so they apply to every fixed operator field;
no simultaneous representation law on an uncountable algebra is required.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The same supported restriction preserves every finite operator-matrix
norm; the coordinate inclusions and retractions remain contractive. -/
theorem norm_matrix_projectionFiberCompression
    (p : H →L[ℂ] H) (hp : IsStarProjection p) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hleft : ∀ i j, p * X i j = X i j) (hright : ∀ i j, X i j * p = X i j) :
    ‖matrixOperator (fun i j => projectionFiberCompression p hp (X i j))‖ =
      ‖matrixOperator X‖ := by
  let J := mapCopies (projectionFiberInclusion p hp).toContinuousLinearMap n
  let R := mapCopies (projectionFiberRetraction p hp) n
  have hJ : ‖J‖ ≤ 1 := (norm_mapCopies_le _ _).trans
    (projectionFiberInclusion p hp).norm_toContinuousLinearMap_le
  have hR : ‖R‖ ≤ 1 := (norm_mapCopies_le _ _).trans
    (norm_projectionFiberRetraction_le p hp)
  have hRJ : R.comp J = ContinuousLinearMap.id ℂ (HilbertCopies (projectionFiber p hp) n) := by
    dsimp [R, J]
    rw [← mapCopies_comp_eq, projectionFiberRetraction_inclusion, mapCopies_id_eq]
  have hext : J.comp
      ((matrixOperator (fun i j => projectionFiberCompression p hp (X i j))).comp R) =
        matrixOperator X := by
    apply ContinuousLinearMap.ext
    intro x
    ext i
    change ((projectionFiberInclusion p hp).toContinuousLinearMap
      ((matrixOperator (fun i j => projectionFiberCompression p hp (X i j)))
        (mapCopies (projectionFiberRetraction p hp) n x) i)) = _
    rw [matrixOperator_apply (H := projectionFiber p hp)
      (fun i j => projectionFiberCompression p hp (X i j))
      (mapCopies (projectionFiberRetraction p hp) n x) i, map_sum]
    rw [matrixOperator_apply (H := H) X x i]
    apply Finset.sum_congr rfl
    intro j _
    rw [mapCopies_apply]
    change p (X i j (p (x j))) = X i j (x j)
    have h := congrArg (fun T : H →L[ℂ] H => T (p (x j))) (hleft i j)
    have h' := congrArg (fun T : H →L[ℂ] H => T (x j)) (hright i j)
    exact h.trans h'
  have h := norm_split_extension J R hJ hR hRJ
    (matrixOperator (fun i j => projectionFiberCompression p hp (X i j)))
  rw [hext] at h
  exact h.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CompressedFieldNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar and matrix norms after restricting actual zero-extension
fields to the fibers of the range projection. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {H F Ω : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  (J : H →ₗᵢ[ℂ] Lp F 2 μ)
  (p : Ω → F →L[ℂ] F) (hp : ∀ x, IsStarProjection (p x))
  (hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J 1 f x = p x (f x))

include hP

theorem matrix_norm_le_iff_compressed_field {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (R : Matrix (Fin n) (Fin n) (Ω → F →L[ℂ] F))
    (hR : ∀ i j (f : Lp F 2 μ), ∀ᵐ x ∂μ,
      isometricExtension J (T i j) f x = R i j x (f x))
    (C : ℝ) (hC : 0 ≤ C) :
    ‖matrixOperator T‖ ≤ C ↔ ∀ᵐ x ∂μ,
      ‖matrixOperator (fun i j => projectionFiberCompression (p x) (hp x) (R i j x))‖ ≤ C := by
  have hn := diagonal_matrix_norm_iff μ (fun i j => isometricExtension J (T i j))
    (fun x i j => R i j x) hR C hC
  rw [norm_matrix_isometricExtension] at hn
  have hl : ∀ᵐ x ∂μ, ∀ i j, p x * R i j x = R i j x :=
    eventually_countable_forall.mpr fun i => eventually_countable_forall.mpr fun j =>
      ae_isometric_field_left_support μ J p hP (T i j) (R i j) (hR i j)
  have hr : ∀ᵐ x ∂μ, ∀ i j, R i j x * p x = R i j x :=
    eventually_countable_forall.mpr fun i => eventually_countable_forall.mpr fun j =>
      ae_isometric_field_right_support μ J p hP (T i j) (R i j) (hR i j)
  have hc : ∀ᵐ x ∂μ,
      ‖matrixOperator (fun i j => projectionFiberCompression (p x) (hp x) (R i j x))‖ =
        ‖matrixOperator (fun i j => R i j x)‖ := by
    filter_upwards [hl, hr] with x hleft hright
    exact norm_matrix_projectionFiberCompression (p x) (hp x) (fun i j => R i j x) hleft hright
  constructor
  · intro h
    filter_upwards [hn.mp h, hc] with x hx he
    exact he.le.trans hx
  · intro h
    apply hn.mpr
    filter_upwards [h, hc] with x hx he
    exact he.symm.le.trans hx

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProjectionCentralData
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Central-decomposition data from actual projection fields

The construction uses the original measure space. On the null complement
of the genuine unitized representations, the original algebra acts by
zero and its unit range is the zero Hilbert space. Algebraic laws, norm
formulas, von Neumann membership and countable contraction tests are all
derived from the actual L² action identities.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

universe u

variable {Ω F H : Type u} [MeasurableSpace Ω]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [MeasurableSpace Ω] in
theorem conull_projection_membership {A : Type u} [CStarAlgebra A]
    (s : Set Ω) (ρ : ∀ _x : s, Unitization ℂ A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (x : s) (Q : F →L[ℂ] F)
    (hQ : projectionFiberCompression (unitizationProjection (ρ x))
      (unitizationProjection_isStarProjection (ρ x)) Q ∈
        representationVonNeumannAlgebra (unitizationRangeRepresentation (ρ x))) :
    projectionFiberCompression
      (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
      (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x))
      Q ∈ representationVonNeumannAlgebra
        (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)) := by
  classical
  have hmap : zeroExtendNonunitalRepresentation s ρ x =
      (ρ x).toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A) := by
    unfold zeroExtendNonunitalRepresentation
    exact dite_eq_left x.property
  let membership : (A →⋆ₙₐ[ℂ] (F →L[ℂ] F)) → Prop := fun τ =>
    projectionFiberCompression (nonunitalUnitProjection τ)
      (nonunitalUnitProjection_isStarProjection τ) Q ∈
        representationVonNeumannAlgebra (nonunitalRangeRepresentation τ)
  change membership (zeroExtendNonunitalRepresentation s ρ x)
  rw [hmap]
  exact hQ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_JointFiberRestriction
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting a joint unitized representation

A unital inclusion preserves the old-unit projection. Thus restricting
a joint unitized representation to one source preserves its actual Hilbert
range, and the range representations agree after the canonical identity
isometry between the two equal projection ranges.
-/

noncomputable section
namespace KadisonSimilarity

variable {B S F : Type*} [CStarAlgebra B] [CStarAlgebra S]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Equal projections have the identity isometry between their ranges. -/
def projectionFiberEquivOfEq (p q : F →L[ℂ] F)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p = q) :
    projectionFiber p hp ≃ₗᵢ[ℂ] projectionFiber q hq :=
  LinearIsometryEquiv.ofEq (projectionFiber p hp).toSubmodule
    (projectionFiber q hq).toSubmodule (by subst q; rfl)

@[simp] theorem projectionFiberEquivOfEq_coe (p q : F →L[ℂ] F)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p = q)
    (v : projectionFiber p hp) :
    (projectionFiberEquivOfEq p q hp hq h v : F) = v := rfl

/-- Restriction preserves the range Hilbert space up to its canonical
identity-on-vectors isometry. -/
def unitizationRestrictionFiberEquiv (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) :
    projectionFiber (unitizationProjection (unitizationRestrict φ ρ))
        (unitizationProjection_isStarProjection (unitizationRestrict φ ρ)) ≃ₗᵢ[ℂ]
      projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ) :=
  projectionFiberEquivOfEq _ _ _ _ (unitizationRestrict_projection φ ρ)

@[simp] theorem unitizationRestrictionFiberEquiv_coe (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F))
    (v : projectionFiber (unitizationProjection (unitizationRestrict φ ρ))
      (unitizationProjection_isStarProjection (unitizationRestrict φ ρ))) :
    (unitizationRestrictionFiberEquiv φ ρ v : F) = v := rfl

@[simp] theorem unitizationRestrictionFiberEquiv_symm_coe (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F))
    (v : projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ)) :
    ((unitizationRestrictionFiberEquiv φ ρ).symm v : F) = v := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_GlobalFiberRestriction
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and zero extension of range representations

The old-unit projection is unchanged by restriction along a unital map,
even when the represented map is nonunital. Restriction commutes with
zero extension from a conull base, so the canonical range identifications
are available at every base point, including the zero fibers.
-/

noncomputable section
namespace KadisonSimilarity

variable {B S F : Type*} [CStarAlgebra B] [CStarAlgebra S]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def nonunitalRestrictionFiberEquiv (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F)) :
    projectionFiber (nonunitalUnitProjection (τ.comp φ.toNonUnitalStarAlgHom))
        (nonunitalUnitProjection_isStarProjection (τ.comp φ.toNonUnitalStarAlgHom)) ≃ₗᵢ[ℂ]
      projectionFiber (nonunitalUnitProjection τ) (nonunitalUnitProjection_isStarProjection τ) :=
  projectionFiberEquivOfEq _ _ _ _ (nonunitalRestrict_projection φ τ)

@[simp] theorem nonunitalRestrictionFiberEquiv_coe (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F))
    (v : projectionFiber (nonunitalUnitProjection (τ.comp φ.toNonUnitalStarAlgHom))
      (nonunitalUnitProjection_isStarProjection (τ.comp φ.toNonUnitalStarAlgHom))) :
    (nonunitalRestrictionFiberEquiv φ τ v : F) = v := rfl

@[simp] theorem nonunitalRestrictionFiberEquiv_symm_coe (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F))
    (v : projectionFiber (nonunitalUnitProjection τ) (nonunitalUnitProjection_isStarProjection τ)) :
    ((nonunitalRestrictionFiberEquiv φ τ).symm v : F) = v := rfl

variable {Ω : Type*} (s : Set Ω)
    (φ : B →⋆ₐ[ℂ] S) (ρ : ∀ _x : s, Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F))

/-- Zero extension is functorial for restriction of the original algebra. -/
theorem zeroExtend_unitizationRestrict (x : Ω) :
    zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x =
      (zeroExtendNonunitalRepresentation s ρ x).comp φ.toNonUnitalStarAlgHom := by
  classical
  ext b
  simp only [NonUnitalStarAlgHom.comp_apply, zeroExtendNonunitalRepresentation_apply]
  by_cases hx : x ∈ s
  · simp only [zeroExtendOperatorField, dite_eq_left hx, unitizationRestrict_inr,
      StarAlgHom.coe_toNonUnitalStarAlgHom]
  · simp only [zeroExtendOperatorField, dite_eq_right hx]

theorem globalRestriction_projection (x : Ω) :
    nonunitalUnitProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x) =
      nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x) := by
  rw [zeroExtend_unitizationRestrict, nonunitalRestrict_projection]

/-- The actual zero-extended fibers of the restricted and joint
representations are identified by the identity on ambient vectors. -/
def globalRestrictionFiberEquiv (x : Ω) :
    projectionFiber
        (nonunitalUnitProjection
          (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))
        (nonunitalUnitProjection_isStarProjection
          (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x)) ≃ₗᵢ[ℂ]
      projectionFiber (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
        (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) :=
  projectionFiberEquivOfEq _ _ _ _ (globalRestriction_projection s φ ρ x)

@[simp] theorem globalRestrictionFiberEquiv_coe (x : Ω)
    (v : projectionFiber
      (nonunitalUnitProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))
      (nonunitalUnitProjection_isStarProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))) :
    (globalRestrictionFiberEquiv s φ ρ x v : F) = v := rfl

@[simp] theorem globalRestrictionFiberEquiv_symm_coe (x : Ω)
    (v : projectionFiber (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
      (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x))) :
    ((globalRestrictionFiberEquiv s φ ρ x).symm v : F) = v := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonFiberFactors
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common joint source gives factor fibers for the first algebra,
using countably many compressed constant rank-one tests. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

universe u
variable {A H : Type u} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- The von Neumann algebra of the first source's range fiber at `x` has scalar center. -/
abbrev commonFirstFiberScalarCenter
    (B C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (B : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (s : Set (WeakDual.characterSpace ℂ A))
    (ρ : ∀ _x : s, Unitization ℂ (jointCStarSource B C) →⋆ₐ[ℂ]
      (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
    (x : WeakDual.characterSpace ℂ A) : Prop :=
  ∀ a : (representationVonNeumannAlgebra (nonunitalRangeRepresentation
    (zeroExtendNonunitalRepresentation s
      (fun y => unitizationRestrict
        (StarSubalgebra.inclusion (le_jointCStarSource_left B C)) (ρ y)) x))).toStarSubalgebra,
    (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c

end KadisonSimilarity

end

end OAI
end


