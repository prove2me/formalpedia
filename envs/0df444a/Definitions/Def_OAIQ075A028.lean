-- Prove2me | Definitions.Def_OAIQ075A028
-- name    : OAIQ075A028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:28:16.649455+00:00
-- url     : https://prove2.me/theorems/31641cf9-125b-4e98-bcbc-1dd9c65b13fa
-- title:
--   Definitions bundle OAIQ075A028 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 74 declarations of OpenAI's Lean: 13 definitions, 1 inductive type or structure and 60 theorems. The definitions and types are `OAI.KadisonSimilarity.MatrixFreeCornerLocalInput`, `OAI.KadisonSimilarity.MultiplicityMatrixCovariance.slice`, `OAI.KadisonSimilarity.ReducedWordCreationModel.tracialCreationFormulas`, `OAI.KadisonSimilarity.TracialCornerGeometry.TraceCornerBound`, `OAI.KadisonSimilarity.TracialCornerGeometry.assembledMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.assembledMultiplicityNormedFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra`, `OAI.KadisonSimilarity.TracialCornerGeometry.leftCommutant`, `OAI.KadisonSimilarity.TracialCreationFormulas`, `OAI.KadisonSimilarity.TracialMatrixTower`, `OAI.KadisonSimilarity.canonicalGeneratedSmallFrame`, `OAI.KadisonSimilarity.canonicalSmallFrameCore`, `OAI.KadisonSimilarity.matrixConjugatedEmbedding`, `OAI.KadisonSimilarity.tracialInclusionIsometry`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonSimilarity_FreeProduct_CanonicalFreeCornerCore`, `KadisonSimilarity_FreeProduct_CanonicalFreeCornerEstimate`, `KadisonSimilarity_FreeProduct_ConstantConjugateFreeness`, `KadisonSimilarity_FreeProduct_GeneratedDihedralAlgebras`, `KadisonSimilarity_FreeProduct_MatrixFreeCornerApplication`, `KadisonSimilarity_FreeProduct_MatrixSourceFreeness`, `KadisonSimilarity_FreeProduct_PublishedWordCreation`, `KadisonSimilarity_FreeProduct_TracialFreeCornerTheorem`, `KadisonSimilarity_Representation_AmplifiedNormalRange`, `KadisonSimilarity_Representation_KaplanskyDischarge`, `KadisonSimilarity_Representation_KaplanskyGeneral`, `KadisonSimilarity_Tensor_EndpointClassification`, `KadisonSimilarity_Tensor_MultiplicityClassification`, `KadisonSimilarity_Tracial_DenseMomentExtension`, `KadisonSimilarity_Tracial_GNSSeparableTransport`, `KadisonSimilarity_Tracial_GNSVectorDensity`, `KadisonSimilarity_Tracial_IntegerMomentMaps`, `KadisonSimilarity_Tracial_IntegerMomentScaling`, `KadisonSimilarity_Tracial_MatrixDiagonalEmbedding`, `KadisonSimilarity_Tracial_MatrixDiffuseSource`, `KadisonSimilarity_Tracial_MatrixGNSNormality`, `KadisonSimilarity_Tracial_MatrixPopaPosition`, `KadisonSimilarity_Tracial_MatrixRelativeCommutant`, `KadisonSimilarity_Tracial_MatrixTracialGNS`, `KadisonSimilarity_Tracial_MatrixVonNeumannRange`, `KadisonSimilarity_Tracial_PopaConjugatePosition`, `KadisonSimilarity_Tracial_PredualGNSNormality`, `KadisonSimilarity_Tracial_PredualGNSSeparable`, `KadisonSimilarity_Tracial_SmallTraceFrames`, `KadisonSimilarity_Tracial_SourceUltrapowerInclusion`, `KadisonSimilarity_Tracial_TraceDenseContractions`, `KadisonSimilarity_Tracial_TracialBoundedBalls`, `KadisonSimilarity_Tracial_TracialCommutantTrace`, `KadisonSimilarity_Tracial_TracialCreationCoordinates`, `KadisonSimilarity_Tracial_TracialInclusionNormality`, `KadisonSimilarity_Tracial_TracialMatrixSymmetrization`, `KadisonSimilarity_Tracial_TracialMatrixTower`, `KadisonSimilarity_Tracial_TracialMomentContinuity`, `KadisonSimilarity_Tracial_TracialNormalityCriterion`, `KadisonSimilarity_Tracial_TracialUltrapowerHom`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A021`, `OAIQ075A022`, `OAIQ075A023` and `OAIQ075A024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A032`, `OAIQ075A033` and `OAIQ075A034`; the statements `OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_from_local_models`, `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs`, `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models` and `OAI.KadisonSimilarity.canonical_free_corner_bound`; the proofs of `OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_from_local_models`, `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models`, `OAI.KadisonSimilarity.canonical_free_corner_bound`, `OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests` and `OAI.KadisonSimilarity.similarityTheorem`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A021
import Definitions.Def_OAIQ075A022
import Definitions.Def_OAIQ075A023
import Definitions.Def_OAIQ075A024

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- Local tracial realization data for the nested matrix stages. In particular,
there is no invariant coefficient formula or intertwiner classification here. -/
structure TracialMatrixTower where
  stage : ∀ s, MatrixHilbertStage (E := E) (F := F) (α := A s)
  traceVector : E
  norm_traceVector : ‖traceVector‖ = 1
  unit_realization : ∀ s, (stage s).full 1 = traceVector
  conjugation : F →ₗᵢ⋆[ℂ] F
  conjugation_involutive : Function.Involutive conjugation
  pairing : F →L[ℂ] F →L[ℂ] ℂ
  pairing_conjugation : ∀ x y, pairing x (conjugation y) = inner ℂ y x
  pairing_matrix : ∀ s a b, Matrix.trace a = 0 → Matrix.trace b = 0 →
    pairing ((stage s).center a) ((stage s).center b) =
      (Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace (a * b)
  inclusion : ∀ s, Matrix (A 0) (A 0) ℂ →⋆ₐ[ℂ] Matrix (A s) (A s) ℂ
  full_compatible : ∀ s a, (stage s).full (inclusion s a) = (stage 0).full a
  center_compatible : ∀ s a, (stage s).center (inclusion s a) = (stage 0).center a
  transition : ∀ s t, s ≤ t → Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] Matrix (A t) (A t) ℂ
  full_transition : ∀ s t h a, (stage t).full (transition s t h a) = (stage s).full a
  center_transition : ∀ s t h a, (stage t).center (transition s t h a) = (stage s).center a
  full_mono : Monotone (fullMatrixStage stage)
  center_mono : Monotone (centeredMatrixStage stage)
  full_dense : Dense (⋃ s, fullMatrixStage stage s)
  center_dense : Dense (⋃ s, centeredMatrixStage stage s)
  size_tendsto : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop
  realOrthonormal : ℕ → F
  realOrthonormal_orthonormal : Orthonormal ℂ realOrthonormal
  realOrthonormal_fixed : ∀ n, conjugation (realOrthonormal n) = realOrthonormal n

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

omit [CompleteSpace H] in
/-- Lifted intertwining implies the scalar slice intertwining. -/
theorem multiplicitySlice_intertwines
    (Y : HilbertTensor G H →L[ℂ] HilbertTensor G K)
    (S : H →L[ℂ] H) (T : K →L[ℂ] K)
    (hY : Y.comp (hilbertTensorLift S) = (hilbertTensorLift T).comp Y) (a b : G) :
    (multiplicitySlice Y a b).comp S = T.comp (multiplicitySlice Y a b) := by
  ext x
  have heq := congrArg (fun A : HilbertTensor G H →L[ℂ] HilbertTensor G K =>
    A (hilbertTensorInsert a x)) hY
  simp only [ContinuousLinearMap.comp_apply, hilbertTensorLift_insert] at heq
  change tensorSlice b (Y (hilbertTensorInsert a (S x))) =
    T (tensorSlice b (Y (hilbertTensorInsert a x)))
  rw [heq]
  exact congrArg (fun A : HilbertTensor G K →L[ℂ] K => A (Y (hilbertTensorInsert a x)))
    (tensorSlice_lift T b)

variable [CompleteSpace G]

section EndpointMultiplicity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {α : Type*} [Fintype α] [DecidableEq α] {k l : ℕ}

/-- Taking a scalar multiplicity coefficient preserves actual word covariance. -/
def MultiplicityMatrixCovariance.slice
    {R : MatrixHilbertStage (E := E) (F := F) (α := α)} {J : F →ₗᵢ⋆[ℂ] F}
    {Ω : E} {Y : HilbertTensor G (EndpointTensor E F k) →L[ℂ]
      HilbertTensor G (EndpointTensor E F l)}
    (cov : MultiplicityMatrixCovariance R J Ω Y) (a b : G) :
    MatrixWordCovariance R J Ω (multiplicitySlice Y a b) where
  sourceAction := cov.sourceAction
  testAction := cov.testAction
  intertwine u := multiplicitySlice_intertwines Y _ _ (cov.intertwine u) a b
  source_covariance := cov.source_covariance
  test_covariance := cov.test_covariance

end EndpointMultiplicity

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_KaplanskyGeneral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- A matrix-bicommutant membership bridge is the only algebraic fact needed
by the two-by-two contraction argument. -/
theorem kaplansky_contraction_of_offDiagonal_mem
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (hmem : kaplanskyOffDiagonal T ∈
      representationVonNeumannAlgebra (representedMatrixHom σ 2))
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ x ∈ s, ‖σ a x - T x‖ < ε := by
  classical
  have hsa : IsSelfAdjoint (kaplanskyOffDiagonal T) :=
    (offdiag_selfAdjoint T).map (representedMatrixHom (StarAlgHom.id ℂ (H →L[ℂ] H)) 2)
  have hnorm : ‖kaplanskyOffDiagonal T‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le
      (representedMatrixHom (StarAlgHom.id ℂ (H →L[ℂ] H)) 2) _).trans
        (offdiag_norm_le_one T hT)
  let s' : Finset (HilbertCopies H 2) := s.image (PiLp.single 2 (1 : Fin 2))
  obtain ⟨X, -, hX, happrox⟩ := selfAdjoint_kaplansky_approximation
    (representedMatrixHom σ 2) (kaplanskyOffDiagonal T) hmem hsa hnorm s' ε hε
  refine ⟨X 0 1, CStarMatrix.norm_entry_le_norm.trans hX, ?_⟩
  intro x hx
  have happ := happrox (PiLp.single 2 (1 : Fin 2) x)
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hcoordinate := PiLp.norm_apply_le
    (representedMatrixHom σ 2 X (PiLp.single 2 (1 : Fin 2) x) -
      kaplanskyOffDiagonal T (PiLp.single 2 (1 : Fin 2) x)) (0 : Fin 2)
  have he : (representedMatrixHom σ 2 X (PiLp.single 2 (1 : Fin 2) x) -
      kaplanskyOffDiagonal T (PiLp.single 2 (1 : Fin 2) x)) 0 = σ (X 0 1) x - T x := by
    let M₁ : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H) := Matrix.of (fun i j => σ (X i j))
    let M₂ : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H) :=
      Matrix.of (fun i j => (StarAlgHom.id ℂ (H →L[ℂ] H)) (offdiag T (star T) i j))
    change (matrixEntryCompression 0 1 (matrixOperator M₁)) x -
      (matrixEntryCompression 0 1 (matrixOperator M₂)) x = _
    rw [matrixEntryCompression_matrixOperator M₁, matrixEntryCompression_matrixOperator M₂]
    rfl
  rw [he] at hcoordinate
  exact hcoordinate.trans_lt happ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixVonNeumannRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

section Represented
variable {A : Type*} [CStarAlgebra A]

/-- A normal represented range has its actual matrix von Neumann range. -/
theorem representedMatrixHom_range (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (P : VonNeumannAlgebra H) (hσ : σ.range = P.toStarSubalgebra) (n : ℕ) :
    (representedMatrixHom σ n).range = (matrixVonNeumann P n).toStarSubalgebra := by
  classical
  apply SetLike.ext
  intro T
  constructor
  · rintro ⟨X, rfl⟩
    apply (matrixOperator_mem_matrixVonNeumann_iff P (fun i j => σ (X i j))).mpr
    intro i j
    change σ (X i j) ∈ P.toStarSubalgebra
    rw [← hσ]
    exact ⟨X i j, rfl⟩
  · intro hT
    have he (i j : Fin n) : ∃ a : A, σ a = matrixEntryCompression i j T := by
      have hm := (mem_matrixVonNeumann_iff_entries P T).mp hT i j
      change matrixEntryCompression i j T ∈ P.toStarSubalgebra at hm
      rw [← hσ] at hm
      exact hm
    choose a ha using he
    let X : Matrix (Fin n) (Fin n) A := Matrix.of a
    refine ⟨CStarMatrix.ofMatrix X, ?_⟩
    change matrixOperator (fun i j => σ (X i j)) = T
    have hX : (fun i j => σ (X i j)) = (fun i j => matrixEntryCompression i j T) := by
      funext i j
      exact ha i j
    rw [hX]
    exact matrixOperator_entryCompressions T


end Represented

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_KaplanskyDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-vector Kaplansky density with an exact source norm bound. -/
noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Ordered
variable [PartialOrder A] [StarOrderedRing A]

/-- Off-diagonal selfadjoint dilation preserves membership in the matrix
bicommutant of the original representation. -/
theorem kaplanskyOffDiagonal_mem (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) :
    kaplanskyOffDiagonal T ∈ representationVonNeumannAlgebra (representedMatrixHom σ 2) := by
  let M : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H) :=
    Matrix.of (fun i j => (StarAlgHom.id ℂ (H →L[ℂ] H)) (offdiag T (star T) i j))
  change matrixOperator M ∈ _
  apply (matrixOperator_mem_representationVonNeumannAlgebra_iff σ M).mpr
  intro i j
  fin_cases i <;> fin_cases j
  · exact (representationVonNeumannAlgebra σ).zero_mem
  · exact hT
  · exact star_mem hT
  · exact (representationVonNeumannAlgebra σ).zero_mem

/-- The unit ball of the source algebra is strongly dense in the unit ball
of the represented bicommutant, tested on any finite family of vectors. -/
theorem kaplansky_contraction_approximation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) (hn : ‖T‖ ≤ 1)
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ x ∈ s, ‖σ a x - T x‖ < ε :=
  kaplansky_contraction_of_offDiagonal_mem σ T hn (kaplanskyOffDiagonal_mem σ T hT) s ε hε

/-- Scaling the unit-ball statement retains the exact norm of the target. -/
theorem kaplansky_finite_approximation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, ‖a‖ ≤ ‖T‖ ∧ ∀ x ∈ s, ‖σ a x - T x‖ < ε := by
  by_cases hzero : T = 0
  · subst T
    refine ⟨0, by simp, ?_⟩
    intro x _
    simpa using hε
  let d : ℝ := ‖T‖
  have hd : 0 < d := norm_pos_iff.mpr hzero
  let D : H →L[ℂ] H := d⁻¹ • T
  have hD : D ∈ representationVonNeumannAlgebra σ := by
    change d⁻¹ • T ∈ _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact (representationVonNeumannAlgebra σ).toStarSubalgebra.smul_mem hT _
  have hDn : ‖D‖ ≤ 1 := by
    rw [show D = d⁻¹ • T from rfl, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd]
    change d⁻¹ * d ≤ 1
    rw [inv_mul_cancel₀ (ne_of_gt hd)]
  obtain ⟨a, ha, happrox⟩ := kaplansky_contraction_approximation σ D hD hDn s
    (ε / d) (div_pos hε hd)
  refine ⟨d • a, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg hd.le]
    exact (mul_le_mul_of_nonneg_left ha hd.le).trans_eq (mul_one d)
  · intro x hx
    have hscale : σ (d • a) = d • σ a := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
      rfl
    have hrecover : d • D = T := by
      dsimp [D]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hd), one_smul]
    have hTx : T x = d • D x := congrArg (fun R : H →L[ℂ] H => R x) hrecover.symm
    rw [hscale, smul_apply, hTx, ← smul_sub, norm_smul, Real.norm_of_nonneg hd.le]
    calc
      d * ‖σ a x - D x‖ < d * (ε / d) := mul_lt_mul_of_pos_left (happrox x hx) hd
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hd)

end Ordered

/-- Two-vector Kaplansky approximation, using the canonical spectral order
on the matrix C-star algebra. -/
theorem twoVectorKaplanskyInput (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    TwoVectorKaplanskyInput σ (representationVonNeumannAlgebra σ) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  classical
  intro T hT x y ε hε
  obtain ⟨a, ha, happrox⟩ := kaplansky_finite_approximation σ T hT {x, y} ε hε
  exact ⟨a, ha.trans (le_add_of_nonneg_right hε.le),
    (happrox x (by simp)).le, (happrox y (by simp)).le⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCreationCoordinates
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable {P H F : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (W : TracialHeadCoordinates (G.baseGeometry D) G D.subtype F)
  [W.vacuum.HasOrthogonalProjection]
  (s : A) (hzero : G.trace (s : P) = 0)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)

/-- The standard free-product model supplies these elementary word
identities. All letters and tensor factors are the actual centered tracial
base spaces; no complete-prefix estimate is part of the data. -/
abbrev TracialCreationFormulas (ALead : Submodule ℂ H) :=
  ElementaryCreationFormulas (G.left (s : P))
    (fun n => G.left ((haarCornerLetter z a n : D) : P))
    (G.baseSymmetryLetter A s hzero) (G.baseHaarLetter D z ha htrace hhaar)
    W.vacuumᗮ ALead

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_PublishedWordCreation
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary creation part of the published reduced free-product model.

Ricard--Xu, J. reine angew. Math. 599 (2006), Section 1, pp. 2--3,
and Lemma 2.3: prepending a centered letter to a word from the opposite
factor is the Hilbert tensor insertion. This interface has only those raw
word maps; prefix isometry and propagation are derived separately. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

namespace ReducedWordCreationModel

variable {G A D} (W : ReducedWordCreationModel G A D)

/-- The normalized Haar letters are among the centered algebra letters in
the published model, so the raw propagation formulas need no new hypothesis. -/
def tracialCreationFormulas
    (s : A) (hs : G.trace (s : P) = 0)
    {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
    {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
    (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a) :
    TracialCreationFormulas G A D W.head s hs z ha htrace hhaar W.aLead.toSubmodule where
  createA := W.createA
  createD := W.createD
  createA_mem := W.createA_mem
  createD_mem := W.createD_mem
  actionA := W.actionA s hs
  actionD n y := by
    have htraceD : (G.baseGeometry D).trace q = (a : ℂ) := by
      simpa only [G.baseGeometry_trace D] using htrace
    have hz := haarCornerLetter_trace_zero (G.baseGeometry D).trace z ha htraceD hhaar n
    exact W.actionD (haarCornerLetter z a n) hz y

end ReducedWordCreationModel

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixTower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tracial matrix towers from actual embedded matrix algebras

The matrix-stage geometry is constructed from nested trace-preserving matrix
embeddings in a tracial Hilbert representation. Density of centered trace-zero
stages is derived by orthogonal projection from density of the full stages.
-/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

variable (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (M : NestedTracialMatrices (A := A) τ V)

omit [∀ s, Nonempty (A s)] in
theorem embeddedMatrixStage_full_mono :
    Monotone (fullMatrixStage (embeddedMatrixStage τ V L hinner hleft M)) := by
  intro s t h x hx
  obtain ⟨a, rfl⟩ := hx
  refine ⟨M.inclusion s t h a, ?_⟩
  simp only [embeddedMatrixStage_full, M.compatible]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- The original manuscript hypothesis is uniform over all projections of
the selected trace in the other free factor. -/
def TraceCornerBound (T : H →L[ℂ] H) (t ε : ℝ) : Prop :=
  ∀ (e : P) (he : IsStarProjection e), e ∈ D → G.trace e = (t : ℂ) →
    ∀ x : CStarCorner e he, ‖commutator T (G.left (x : P))‖ ≤ ε * ‖x‖

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialFreeCornerTheorem
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tracial free-corner argument assembled from the actual word model,
matrix symmetrization, and spectral test. All propagation, Fourier-matrix,
operator-norm, and averaging conclusions are derived from the local inputs.
Only the underlying local model and the specified published inputs remain. -/

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

local instance assembledMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance
local instance assembledMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_GeneratedDihedralAlgebras
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- The auxiliary algebra generated by the second factor and the test
symmetry. -/
def generatedTestAlgebra (D : StarSubalgebra ℂ P) (s : P) : StarSubalgebra ℂ P :=
  G.l2GeneratedAlgebra (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {s}))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SmallTraceFrames
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An unbounded matrix tower supplies the small corner and its complete
finite partial-isometry frame used in the free-corner argument. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  {τ : P →ₗ[ℂ] ℂ} {V : P →ₗ[ℂ] H}

omit [CompleteSpace H] in
/-- The corner may be chosen below any positive prescribed trace bound.
Its matrix-unit column resolves the identity, so no frame existence is an
additional hypothesis. -/
theorem NestedTracialMatrices.exists_small_trace_frame
    (M : NestedTracialMatrices (A := I) τ V)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {s : ℝ} (hs : 0 < s) :
    ∃ (n : ℕ) (_hn : 0 < n) (t : ℝ), 0 < t ∧ t < s ∧
      ∃ F : TracialMatrixUnitColumnFamily τ (Fin n), τ F.corner = (t : ℂ) := by
  have hevent : ∀ᶠ j in Filter.atTop, 1 / s < (Fintype.card (I j) : ℝ) :=
    hsize.eventually (Filter.eventually_gt_atTop (1 / s))
  obtain ⟨j, hj⟩ := hevent.exists
  let n := Fintype.card (I j)
  have hn : 0 < n := Fintype.card_pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨n, hn, 1 / (n : ℝ), one_div_pos.mpr hnR, ?_,
    M.nonemptyFinColumnFamily j, ?_⟩
  · exact (div_lt_iff₀ hnR).mpr (by
      have h := (div_lt_iff₀ hs).mp hj
      simpa only [mul_comm] using h)
  · simpa only [Fintype.card_fin, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast] using (M.nonemptyFinColumnFamily j).trace_corner

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialNormalityCriterion
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed bounded trace-vector sets identify the represented bicommutant
with the original tracial algebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem normal_range_of_closed_trace_balls
    (hclosed : ∀ C : ℝ, IsClosed (G.vector '' Metric.closedBall (0 : A) C)) :
    G.left.range = (representationVonNeumannAlgebra G.left).toStarSubalgebra := by
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    exact mem_representationVonNeumannAlgebra G.left a
  · intro hT
    have hv : T (G.vector 1) ∈ G.vector '' Metric.closedBall (0 : A) (‖T‖ + 1) := by
      apply (hclosed _).closure_subset
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      let δ := min (ε / 2) 1
      have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
      obtain ⟨a, ha, happrox, _⟩ := twoVectorKaplanskyInput G.left T hT
        (G.vector 1) (G.vector 1) δ hδ
      refine ⟨G.vector a, ⟨a, ?_, rfl⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using
          ha.trans (add_le_add le_rfl (min_le_right (ε / 2) 1))
      · rw [dist_eq_norm, norm_sub_rev, ← mul_one a, ← G.left_vector]
        exact happrox.trans_lt ((min_le_left (ε / 2) 1).trans_lt (by linarith))
    obtain ⟨a, _, ha⟩ := hv
    refine ⟨a, ?_⟩
    ext x
    refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro b
    have hTc : T ∈ Set.centralizer (Set.centralizer (Set.range G.left)) := by
      change T ∈ representationVonNeumannAlgebra G.left at hT
      rwa [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
    have hc : G.right b * T = T * G.right b := hTc (G.right b) (by
      rintro _ ⟨c, rfl⟩
      exact (G.right_left c b).symm)
    have hcv := congrArg (fun R : H →L[ℂ] H => R (G.vector 1)) hc
    change G.right b (T (G.vector 1)) = T (G.right b (G.vector 1)) at hcv
    rw [G.right_vector, one_mul, ← ha, G.right_vector] at hcv
    exact (G.left_vector a b).trans hcv

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBoundedBalls
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed trace-vector balls persist in the bounded L²-generated algebra.
This proves normality on its own cyclic Hilbert space, not only on the
ambient representation space. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem trace_balls_closed_of_normal_range
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra) (C : ℝ) :
    IsClosed (G.vector '' Metric.closedBall (0 : A) C) := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  let τ := G.normalTracialRepresentation h1 hf M hrange
  have hv (a : A) : (e a : H →L[ℂ] H) τ.vector = G.vector a := by
    change G.left a (G.vector 1) = G.vector a
    rw [G.left_vector, mul_one]
  have heq : G.vector '' Metric.closedBall (0 : A) C =
      {ξ | ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧ (b : H →L[ℂ] H) τ.vector = ξ} := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨e a, ?_, hv a⟩
      rw [StarAlgEquiv.norm_map]
      simpa only [Metric.mem_closedBall, dist_zero_right] using ha
    · rintro ⟨b, hb, hξ⟩
      obtain ⟨a, rfl⟩ := e.surjective b
      refine ⟨a, ?_, (hv a).symm.trans hξ⟩
      change ‖e a‖ ≤ C at hb
      rw [StarAlgEquiv.norm_map] at hb
      simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  rw [heq]
  exact trace_ball_isClosed τ C

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCommutantTrace
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vacuum trace on the left commutant, obtained directly from tracial
conjugation and the dense algebra vectors. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

theorem conjugation_involutive : Function.Involutive G.conjugation :=
  tracialConjugation_involutive G.trace G.vector G.inner_vector G.tracial G.dense_vector

theorem inner_conjugation_swap (x y : H) :
    inner ℂ (G.conjugation x) y = inner ℂ (G.conjugation y) x := by
  have h := inner_tracialConjugation G.trace G.vector G.inner_vector G.tracial
    G.dense_vector x (G.conjugation y)
  change inner ℂ (G.conjugation x) (G.conjugation (G.conjugation y)) =
    inner ℂ (G.conjugation y) x at h
  rwa [G.conjugation_involutive y] at h

/-- A left-module endomorphism has its adjoint vacuum vector given by tracial conjugation. -/
theorem commutant_conjugation_vector (Z : H →L[ℂ] H)
    (hZ : ∀ a, Z.comp (G.left a) = (G.left a).comp Z) :
    G.conjugation (Z (G.vector 1)) = star Z (G.vector 1) := by
  apply ext_inner_right ℂ
  intro ξ
  refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  rw [G.inner_conjugation_swap, G.conjugation_vector]
  have hleft : G.vector (star a) = (G.left a).adjoint (G.vector 1) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, G.left_vector, mul_one]
  rw [hleft, ContinuousLinearMap.adjoint_inner_left]
  have hcomm := congrArg (fun T : H →L[ℂ] H => T (G.vector 1)) (hZ a)
  change Z (G.left a (G.vector 1)) = G.left a ((Z : H →L[ℂ] H) (G.vector 1)) at hcomm
  rw [← hcomm, G.left_vector, mul_one]
  exact (ContinuousLinearMap.adjoint_inner_left Z (G.vector a) (G.vector 1)).symm

def leftCommutant : VonNeumannAlgebra H := starSubalgebraCommutant G.left.range

theorem mem_leftCommutant_iff (Z : H →L[ℂ] H) :
    Z ∈ G.leftCommutant ↔ ∀ a, Z.comp (G.left a) = (G.left a).comp Z := by
  change Z ∈ starSubalgebraCommutant G.left.range ↔ _
  rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
  constructor
  · intro hz a
    exact (hz (G.left a) ⟨a, rfl⟩).symm
  · intro hz
    rintro _ ⟨a, rfl⟩
    exact (hz a).symm

end TracialCornerGeometry
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

local notation "G" => canonicalGeneratedGeometry τ htr φ ψ
local notation "D₀" => StarAlgHom.range (canonicalGeneratedSecond τ htr φ ψ)

variable [IsClosed ((canonicalGeneratedFirst τ htr φ ψ).range :
    Set (canonicalGeneratedAlgebra τ htr φ ψ))]
  [IsClosed ((canonicalGeneratedSecond τ htr φ ψ).range :
    Set (canonicalGeneratedAlgebra τ htr φ ψ))]

variable (τR : R →ₚ[ℂ] ℂ) (hψτ : ∀ r, τ (ψ r) = τR r)

/-- Transport all small-frame data into the actual second range. -/
def canonicalSmallFrameCore {b : ℝ} (Q : SmallFreeCornerData τR.toLinearMap b) :
    SmallFreeCornerData ((G).baseGeometry D₀).trace b :=
  Q.transport (canonicalGeneratedSecond τ htr φ ψ).rangeRestrict
    τR.toLinearMap ((G).baseGeometry D₀).trace hψτ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixTracialGNS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- Faithfulness of the trace is preserved by normalized matrix extension. -/
theorem normalizedMatrixTrace_faithful (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0)
    (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : normalizedMatrixTrace τ n (star X * X) = 0) : X = 0 := by
  have hz : matrixGNSVector τ n X = 0 :=
    inner_self_eq_zero.mp (by rw [matrixGNSVector_inner, hX])
  have hc : (matrixGNSScale n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (matrixGNSScale_pos (n := n)).ne'
  ext i j
  have hcoord := congrArg (fun ξ : MatrixGNSArray τ n => ξ i j) hz
  change (matrixGNSScale n : ℂ) • gnsTracialVector τ (X i j) = 0 at hcoord
  have hv : gnsTracialVector τ (X i j) = 0 := (smul_eq_zero.mp hcoord).resolve_left hc
  change X i j = 0
  apply gnsTracialVector_injective τ hf
  simpa only [map_zero] using hv

/-- The GNS left representation becomes actual left matrix multiplication
under the normalized array identification. -/
theorem matrixGNSUnitary_left (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) (ξ : (normalizedMatrixTrace τ n).GNS) :
    matrixGNSUnitary τ n ((normalizedMatrixTrace τ n).gnsStarAlgHom X ξ) =
      matrixLeftArray τ X (matrixGNSUnitary τ n ξ) := by
  ext i j
  refine (gnsTracialVector_dense (normalizedMatrixTrace τ n)).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro Y
  change matrixGNSIsometry τ n
    ((normalizedMatrixTrace τ n).gnsStarAlgHom X
      (gnsTracialVector (normalizedMatrixTrace τ n) Y)) i j =
    matrixLeftArray τ X (matrixGNSIsometry τ n
      (gnsTracialVector (normalizedMatrixTrace τ n) Y)) i j
  rw [gnsTracialVector_left, matrixGNSIsometry_vector, matrixGNSIsometry_vector,
    matrixGNSVector_mul]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_AmplifiedNormalRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite diagonal amplification of an actual normal represented algebra
has the expected normal range. -/

noncomputable section
namespace KadisonSimilarity
open scoped CStarAlgebra

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

attribute [local instance] OAI.KadisonSimilarity.normalRange_closed
theorem amplifiedScalarRepresentation_normal_range
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (M : VonNeumannAlgebra H)
    (hrange : σ.range = M.toStarSubalgebra) (n : ℕ) [NeZero n] :
    (amplifiedScalarRepresentation σ n).range =
      (matrixVonNeumann M.commutant n).commutant.toStarSubalgebra := by
  let ρ := M.commutant.toStarSubalgebra.subtype
  have hρ : (representedMatrixHom ρ n).range =
      (matrixVonNeumann M.commutant n).toStarSubalgebra :=
    representedMatrixHom_range ρ M.commutant (subtype_range_eq M.commutant) n
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    have ha : σ a ∈ M.commutant.commutant := by
      rw [M.commutant_commutant]
      change σ a ∈ M.toStarSubalgebra
      rw [← hrange]
      exact ⟨a, rfl⟩
    have hac : σ a ∈ Set.centralizer (ρ.range : Set (H →L[ℂ] H)) := by
      rintro _ ⟨b, rfl⟩
      exact VonNeumannAlgebra.mem_commutant_iff.mp ha b b.property
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro S hS
    have hSm : S ∈ (representedMatrixHom ρ n).range := by
      rw [hρ]
      exact hS
    obtain ⟨X, rfl⟩ := hSm
    exact amplify_mem_matrixRange_commutant ρ n (σ a) hac _ ⟨X, rfl⟩
  · intro hT
    have hTc : T ∈ Set.centralizer ((representedMatrixHom ρ n).range :
        Set (HilbertCopies H n →L[ℂ] HilbertCopies H n)) := by
      rintro _ ⟨X, rfl⟩
      apply VonNeumannAlgebra.mem_commutant_iff.mp hT
      change representedMatrixHom ρ n X ∈ (matrixVonNeumann M.commutant n).toStarSubalgebra
      rw [← hρ]
      exact ⟨X, rfl⟩
    obtain ⟨B, hTB, hB⟩ := matrixRange_commutant_is_diagonal ρ T hTc
    have hBM : B ∈ M := by
      rw [← M.commutant_commutant]
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro S hS
      exact hB S ⟨⟨S, hS⟩, rfl⟩
    have hBr : B ∈ σ.range := by
      rw [hrange]
      exact hBM
    obtain ⟨a, rfl⟩ := hBr
    exact ⟨a, hTB.symm⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixGNSNormality
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The native matrix GNS representation has normal range whenever the
original native GNS representation does. -/

noncomputable section
namespace KadisonSimilarity
open scoped CStarAlgebra ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (M : VonNeumannAlgebra τ.GNS)
  (hrange : τ.gnsStarAlgHom.range = M.toStarSubalgebra)
  (n : ℕ) [NeZero n]

include hrange in
theorem matrix_gns_normal_range :
    (normalizedMatrixTrace τ n).gnsStarAlgHom.range =
      (representationVonNeumannAlgebra (normalizedMatrixTrace τ n).gnsStarAlgHom).toStarSubalgebra := by
  let σ := amplifiedScalarRepresentation τ.gnsStarAlgHom n
  let N := (matrixVonNeumann M.commutant n).commutant
  have hσ : σ.range = N.toStarSubalgebra :=
    amplifiedScalarRepresentation_normal_range τ.gnsStarAlgHom M hrange n
  let ρ := representedMatrixHom σ n
  have hρ : ρ.range = (matrixVonNeumann N n).toStarSubalgebra :=
    representedMatrixHom_range σ N hσ n
  apply normal_range_of_unitary_intertwining
    (normalizedMatrixTrace τ n).gnsStarAlgHom ρ (matrixGNSUnitary τ n) ?_ _ hρ
  intro X
  ext ξ
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, matrixGNSUnitary_left,
    LinearIsometryEquiv.apply_symm_apply]
  rfl

include hrange in
theorem matrix_trace_balls_closed (h1 : τ 1 = 1)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hf : ∀ a, τ (star a * a) = 0 → a = 0) (C : ℝ) :
    IsClosed (gnsTracialVector (normalizedMatrixTrace τ n) ''
      Metric.closedBall (0 : CStarMatrix (Fin n) (Fin n) A) C) := by
  let τn := normalizedMatrixTrace τ n
  let htrn := normalizedMatrixTrace_tracial τ htr (n := n)
  let G := gnsTracialGeometry τn htrn
  exact G.trace_balls_closed_of_normal_range (normalizedMatrixTrace_one τ h1)
    (gnsTracialVector_injective τn (normalizedMatrixTrace_faithful τ hf)) _
    (matrix_gns_normal_range τ M hrange n) C

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixDiagonalEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable {B : Type*} [CStarAlgebra B]

omit [NeZero n] [PartialOrder A] [StarOrderedRing A] in
/-- Diagonal inclusion and entrywise subfactor inclusion commute. -/
theorem matrixEntryHom_diagonal (φ : A →⋆ₐ[ℂ] B) (a : A) :
    matrixEntryHom φ (matrixDiagonalHom n a) = matrixDiagonalHom n (φ a) := by
  ext i j
  simp only [matrixEntryHom_apply, matrixDiagonalHom_apply]
  split_ifs <;> simp only [map_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixRelativeCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Irreducibility of an entrywise matrix inclusion

The scalar matrix units force any relative commutant element to be a constant
diagonal matrix. Its diagonal entry commutes with the original inclusion,
so scalarity of the original relative commutant proves scalarity after
matrix amplification. No normality or factor classification is used.
-/

noncomputable section
namespace KadisonSimilarity

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B] {n : ℕ}

/-- Commutation with all scalar matrix units forces a constant diagonal. -/
theorem matrix_diagonal_of_commutes_units
    (X : CStarMatrix (Fin n) (Fin n) B)
    (hX : ∀ i j : Fin n,
      X * CStarMatrix.ofMatrix (Matrix.single i j (1 : B)) =
        CStarMatrix.ofMatrix (Matrix.single i j (1 : B)) * X) :
    ∃ b : B, X = matrixDiagonalHom n b := by
  let M : Matrix (Fin n) (Fin n) B := CStarMatrix.ofMatrix.symm X
  have hM : Pairwise (fun i j : Fin n => Commute (Matrix.single i j (1 : B)) M) := by
    intro i j _
    have h := congrArg CStarMatrix.ofMatrix.symm (hX i j)
    change M * Matrix.single i j 1 = Matrix.single i j 1 * M at h
    exact h.symm
  obtain ⟨b, hb⟩ := Matrix.mem_range_scalar_of_commute_single hM
  refine ⟨b, ?_⟩
  apply CStarMatrix.ofMatrix.symm.injective
  change M = Matrix.scalar (Fin n) b
  exact hb.symm

variable [NeZero n]

/-- An irreducible inclusion remains irreducible after finite matrix
amplification. Scalars refer to the actual complex algebra maps. -/
theorem scalar_of_matrix_relative_commutant
    (ρ : R →⋆ₐ[ℂ] B)
    (hρ : ∀ b : B, (∀ a : R, b * ρ a = ρ a * b) →
      ∃ z : ℂ, b = algebraMap ℂ B z)
    (X : CStarMatrix (Fin n) (Fin n) B)
    (hX : ∀ Y : CStarMatrix (Fin n) (Fin n) R,
      X * matrixEntryHom ρ Y = matrixEntryHom ρ Y * X) :
    ∃ z : ℂ, X = algebraMap ℂ (CStarMatrix (Fin n) (Fin n) B) z := by
  have hunits i j :
      X * CStarMatrix.ofMatrix (Matrix.single i j (1 : B)) =
        CStarMatrix.ofMatrix (Matrix.single i j (1 : B)) * X := by
    have h := hX (CStarMatrix.ofMatrix (Matrix.single i j (1 : R)))
    simpa only [matrixEntryHom_single, map_one] using h
  obtain ⟨b, hb⟩ := matrix_diagonal_of_commutes_units X hunits
  have hcomm (a : R) : b * ρ a = ρ a * b := by
    have h := hX (matrixDiagonalHom n a)
    rw [matrixEntryHom_diagonal, hb] at h
    apply matrixDiagonalHom_injective n
    simpa only [map_mul] using h
  obtain ⟨z, hz⟩ := hρ b hcomm
  refine ⟨z, ?_⟩
  rw [hb, hz]
  exact (matrixDiagonalHom n).commutes z

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialUltrapowerHom
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- The induced map preserves the actual quotient trace. -/
theorem tracialUltrapowerMap_trace (x : Ultrapower τA hA ω trA) :
    quotientTrace τB hB ω trB (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ x) =
      quotientTrace τA hA ω trA x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change sequenceTrace τB ω (boundedSequenceStarHom φ a) = sequenceTrace τA ω a
  apply congrArg (limUnder (ω : Filter ℕ))
  funext i
  exact hφ (a i)

/-- Faithfulness of the quotient trace makes the induced map injective. -/
theorem tracialUltrapowerMap_injective :
    Function.Injective (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply quotientTrace_faithful τA hA ω trA
  rw [← tracialUltrapowerMap_trace τA τB hA hB ω trA trB φ hφ,
    map_mul, map_star, map_sub, hxy, sub_self, star_zero, zero_mul, map_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_PopaConjugatePosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem quotientTrace_unitary_conjugate (u : unitary (Ultrapower τA hA ω trA))
    (x : Ultrapower τA hA ω trA) :
    quotientTrace τA hA ω trA
      (Unitary.conjStarAlgAut ℂ (Ultrapower τA hA ω trA) u x) =
        quotientTrace τA hA ω trA x := by
  change quotientTrace τA hA ω trA ((u : Ultrapower τA hA ω trA) * x * star (u : Ultrapower τA hA ω trA)) = _
  rw [quotientTrace_tracial τA hA ω trA,
    ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

/-- The conjugated constant copy has exactly its original trace. -/
theorem conjugatedConstantEmbedding_trace (ρ : R →⋆ₐ[ℂ] A)
    (u : unitary (Ultrapower τA hA ω trA)) (x : R) :
    quotientTrace τB hB ω trB
      (conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ u x) = τA (ρ x) := by
  change quotientTrace τB hB ω trB
    (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ
      (Unitary.conjStarAlgAut ℂ (Ultrapower τA hA ω trA) u
        (constant τA hA ω trA (ρ x)))) = _
  rw [tracialUltrapowerMap_trace, quotientTrace_unitary_conjugate, quotientTrace_constant]

/-- Faithfulness survives the constant embedding, conjugation, and inclusion. -/
theorem conjugatedConstantEmbedding_injective (ρ : R →⋆ₐ[ℂ] A)
    (hρ : Function.Injective ρ)
    (hfA : ∀ a : A, τA (star a * a) = 0 → a = 0)
    (u : unitary (Ultrapower τA hA ω trA)) :
    Function.Injective (conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ u) :=
  (tracialUltrapowerMap_injective τA τB hA hB ω trA trB φ hφ).comp
    ((Unitary.conjStarAlgAut ℂ (Ultrapower τA hA ω trA) u).injective.comp
      ((constant_injective τA hA ω trA hfA).comp hρ))

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
local notation "D₀" => StarAlgHom.range (canonicalGeneratedSecond τQ trQ ι ψ)

/-- The fixed small frame transported into the actual free second factor. -/
def canonicalGeneratedSmallFrame {b : ℝ} (Q : SmallFreeCornerData τR.toLinearMap b) :
    CanonicalSecondFrame τB hB ω trB ψ hψ b := by
  letI : IsClosed (D₀ : Set L) := canonicalSecondRange_closed τQ trQ ι ψ hψ
  exact canonicalSmallFrameCore (τ := τQ) (htr := trQ) (φ := ι) (ψ := ψ)
    (τR := τR) (hψτ := hψτ) Q

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

include tr in
lemma gnsTendsto_integerEval {F : J → I → B} {G : I → B} {l : Filter J}
    (h : ∀ i, GNSTendsto τ (fun j => F j i) l (G i))
    {C : ℝ} (hC : 1 ≤ C) (hF : ∀ j i, ‖F j i‖ ≤ C)
    (u : unitary B) (a : Option I) (w : List (IntAtom I)) :
    GNSTendsto τ (fun j => integerEval (F j) u a w) l (integerEval G u a w) := by
  have hprod : ∀ v : List (IntAtom I), GNSTendsto τ
      (fun j => (v.map (fun b => ((u ^ b.1 : unitary B) : B) * wordCoeff (F j) b.2)).prod) l
      ((v.map (fun b => ((u ^ b.1 : unitary B) : B) * wordCoeff G b.2)).prod) := by
    intro v
    induction v with
    | nil => exact GNSTendsto.const τ 1 l
    | cons b v ih =>
      have hb := (GNSTendsto.const τ ((u ^ b.1 : unitary B) : B) l).mul τ tr
        (gnsTendsto_wordCoeff τ h b.2) ‖((u ^ b.1 : unitary B) : B)‖ (fun _ => le_rfl)
      have hn (j) : ‖((u ^ b.1 : unitary B) : B) * wordCoeff (F j) b.2‖ ≤ C := by
        rw [CStarRing.norm_coe_unitary_mul]
        exact wordCoeff_norm_le_bound _ hC (hF j) _
      exact hb.mul τ tr ih C hn
  exact (gnsTendsto_wordCoeff τ h a).mul τ tr (hprod w) C
    (fun j => wordCoeff_norm_le_bound _ hC (hF j) a)

include h1 tr in
/-- Vanishing moments persist when each coefficient is approximated in trace norm
with a common operator-norm bound. -/
theorem integer_moment_zero_of_bounded_limits
    {F : ℕ → I → B} {G : I → B}
    (h : ∀ i, GNSTendsto τ (fun j => F j i) atTop (G i))
    {C : ℝ} (hC : 1 ≤ C) (hF : ∀ j i, ‖F j i‖ ≤ C)
    (u : unitary B) (a : Option I) (w : List (IntAtom I))
    (hz : ∀ j, τ (integerEval (F j) u a w) = 0) :
    τ (integerEval G u a w) = 0 := by
  have ht := trace_tendsto_of_gns τ h1 (gnsTendsto_integerEval τ tr h hC hF u a w)
  have hh : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (τ (integerEval G u a w))) := by
    simpa only [hz] using ht
  exact tendsto_nhds_unique hh tendsto_const_nhds

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_IntegerMomentScaling
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar homogeneity of each finite integer-power mixed word. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching

variable {B I : Type*} [CStarAlgebra B]

/-- Each coefficient can be rescaled separately, including coefficients that
occur repeatedly in the word. -/
theorem integerEval_smul_family (F : I → B) (c : I → ℂ) (u : unitary B)
    (a : Option I) (l : List (IntAtom I)) :
    integerEval (fun i => c i • F i) u a l =
      (wordScalar c a * (l.map (fun b => wordScalar c b.2)).prod) • integerEval F u a l := by
  have ht (v : List (IntAtom I)) :
      (v.map (fun b => ((u ^ b.1 : unitary B) : B) * wordCoeff (fun i => c i • F i) b.2)).prod =
      (v.map (fun b => wordScalar c b.2)).prod •
        (v.map (fun b => ((u ^ b.1 : unitary B) : B) * wordCoeff F b.2)).prod := by
    induction v with
    | nil => simp
    | cons b v ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [wordCoeff_smul_family, ih]
      simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm]
  unfold integerEval
  rw [wordCoeff_smul_family, ht]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_PredualGNSNormality
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive trace normal for a Banach predual has normal native GNS
range. Bounded predual compactness and cyclic coefficients close the GNS
trace-vector balls. -/

noncomputable section
namespace KadisonSimilarity

open Filter Topology BoundedHochschild HochschildNormalPart
open scoped ComplexOrder

universe u
variable {A X : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (τ : A →ₚ[ℂ] ℂ)

theorem gnsCyclicSpace_eq_top :
    cyclicSpace τ.gnsStarAlgHom (gnsTracialVector τ 1) = ⊤ := by
  apply top_unique
  intro ξ _
  refine (gnsTracialVector_dense τ).induction_on ξ
    (cyclicSpace_closed τ.gnsStarAlgHom (gnsTracialVector τ 1)) ?_
  intro a
  have he : gnsTracialVector τ a = τ.gnsStarAlgHom a (gnsTracialVector τ 1) := by
    rw [gnsTracialVector_left, mul_one]
  rw [he]
  exact cyclicSpace_mul τ.gnsStarAlgHom (gnsTracialVector τ 1) a
    (cyclicSpace_mem τ.gnsStarAlgHom (gnsTracialVector τ 1))

theorem gnsCyclic_coefficient_normal (hτ : TraceInPredual e τ) (η : τ.GNS) :
    coefficient τ.gnsStarAlgHom η (gnsTracialVector τ 1) ∈ normalDual e := by
  have hΩ : coefficient τ.gnsStarAlgHom (gnsTracialVector τ 1)
      (gnsTracialVector τ 1) ∈ normalDual e := by
    obtain ⟨z, hz⟩ := hτ
    apply (mem_normalDual e _).mpr
    refine ⟨z, fun a => ?_⟩
    simpa only [coefficient_apply, gnsTracialVector_left, mul_one,
      gnsTracialVector_inner, star_one, one_mul] using hz a
  apply cyclic_coefficients_normal e τ.gnsStarAlgHom
    (gnsTracialVector τ 1) (gnsTracialVector τ 1) hΩ
  rw [gnsCyclicSpace_eq_top]
  trivial

theorem gnsVector_predual_tendsto (hτ : TraceInPredual e τ)
    {I : Type*} {l : Filter I} {a : I → A} {b : A}
    (h : PredualTendsto e a l b) (η : τ.GNS) :
    Tendsto (fun i => inner ℂ η (gnsTracialVector τ (a i))) l
      (𝓝 (inner ℂ η (gnsTracialVector τ b))) := by
  obtain ⟨z, hz⟩ := (mem_normalDual e _).mp (gnsCyclic_coefficient_normal e τ hτ η)
  have he (c : A) : inner ℂ η (gnsTracialVector τ c) = star (e.symm c z) := by
    simpa only [coefficient_apply, gnsTracialVector_left, mul_one] using hz c
  simpa only [he] using (h z).star

theorem predual_gns_trace_balls_closed (hτ : TraceInPredual e τ) (C : ℝ) :
    IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C) := by
  apply IsSeqClosed.isClosed
  intro v ξ hv hlim
  choose a ha he using hv
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨b, hb, hpre⟩ := exists_predual_ultralimit e ω a C
    (fun n => by simpa only [Metric.mem_closedBall, dist_zero_right] using ha n)
  refine ⟨b, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  · apply ext_inner_left ℂ
    intro η
    have hstrong : Tendsto (fun n => inner ℂ η (v n)) (ω : Filter ℕ)
        (𝓝 (inner ℂ η ξ)) := ((tendsto_const_nhds.inner hlim).mono_left hω)
    have hweak := gnsVector_predual_tendsto e τ hτ hpre η
    have heq (n : ℕ) : inner ℂ η (gnsTracialVector τ (a n)) = inner ℂ η (v n) :=
      congrArg (inner ℂ η) (he n)
    exact tendsto_nhds_unique (hweak.congr heq) hstrong

/-- Banach-predual normality supplies exactly the GNS normality required by
the finite-factor commutator argument. -/
theorem hasNormalGNS_of_predual (hτ : TraceInPredual e τ)
    (htr : ∀ a b, τ (a * b) = τ (b * a)) : HasNormalGNS τ :=
  (gnsTracialGeometry τ htr).normal_range_of_closed_trace_balls
    (predual_gns_trace_balls_closed e τ hτ)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_PredualGNSSeparable
attribute [-instance] _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normal positive functional on an algebra with separable predual has
a separable GNS space. Countably many dual evaluations give a total family
of GNS vectors. -/

noncomputable section
namespace KadisonSimilarity

open HochschildNormalPart
open scoped ComplexOrder

universe u
variable {A X : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (τ : A →ₚ[ℂ] ℂ)

theorem exists_countable_total_gns_vectors (hτ : BoundedHochschild.TraceInPredual e τ) :
    ∃ a : ℕ → A, (∀ n, ‖a n‖ ≤ 1) ∧
      ∀ ξ : τ.GNS, (∀ n, inner ℂ ξ (gnsTracialVector τ (a n)) = 0) → ξ = 0 := by
  obtain ⟨g, hg, htotal⟩ := Generator.exists_countable_total_dual X
  refine ⟨fun n => e (g n), fun n => (e.norm_map (g n)).le.trans (hg n), ?_⟩
  intro ξ hξ
  obtain ⟨z, hz⟩ := (mem_normalDual e _).mp (gnsCyclic_coefficient_normal e τ hτ ξ)
  have hz0 : z = 0 := htotal z (fun n => by
    have h := hz (e (g n))
    simpa only [coefficient_apply, gnsTracialVector_left, mul_one,
      e.symm_apply_apply, hξ n, star_eq_zero] using h.symm)
  apply (gnsTracialVector_dense τ).eq_zero_of_inner_left ℂ
  intro a
  have h := hz a
  simpa only [coefficient_apply, gnsTracialVector_left, mul_one, hz0,
    map_zero, star_zero] using h

theorem gns_separable_of_predual (hτ : BoundedHochschild.TraceInPredual e τ) :
    TopologicalSpace.SeparableSpace τ.GNS := by
  obtain ⟨a, _, ha⟩ := exists_countable_total_gns_vectors e τ hτ
  let v : ℕ → τ.GNS := fun n => gnsTracialVector τ (a n)
  let V := (Submodule.span ℂ (Set.range v)).topologicalClosure
  have htop : V = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro ξ hξ
    change ξ = 0
    apply ha ξ
    intro n
    exact (Submodule.mem_orthogonal' V ξ).mp hξ (v n)
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩))
  have hs : TopologicalSpace.IsSeparable (V : Set τ.GNS) :=
    (Set.countable_range v).isSeparable.span.closure
  rw [htop, Submodule.top_coe] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TraceDenseContractions
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.generatedGNSInclusion_vector _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable family of contractions dense for the trace norm. -/

noncomputable section
namespace KadisonSimilarity
open BoundedHochschild Generator.Tracial Filter Topology
open scoped ComplexOrder

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ)

/-- Separability of the GNS space suffices; the algebra need not be norm separable. -/
theorem exists_trace_dense_contractions [TopologicalSpace.SeparableSpace τ.GNS] :
    ∃ d : ℕ → B, (∀ n, ‖d n‖ ≤ 1) ∧
      ∀ b : B, ‖b‖ ≤ 1 → ∃ j : ℕ → ℕ,
        GNSTendsto τ (fun k => d (j k)) atTop b := by
  classical
  let S : Set τ.GNS := gnsTracialVector τ '' Metric.closedBall (0 : B) 1
  let : Nonempty S := ⟨⟨gnsTracialVector τ 0, ⟨0, by simp, rfl⟩⟩⟩
  let z : ℕ → S := TopologicalSpace.denseSeq S
  choose d hd he using fun n => (z n).property
  refine ⟨d, fun n => by simpa only [Metric.mem_closedBall, dist_zero_right] using hd n, ?_⟩
  intro b hb
  let x : S := ⟨gnsTracialVector τ b, ⟨b, by simpa using hb, rfl⟩⟩
  obtain ⟨y, hy, hyt⟩ := mem_closure_iff_seq_limit.mp
    ((TopologicalSpace.denseRange_denseSeq S) x)
  choose j hj using hy
  have hc : Tendsto (fun k => gnsTracialVector τ (d (j k))) atTop
      (𝓝 (gnsTracialVector τ b)) := by
    have ht := continuous_subtype_val.tendsto x |>.comp hyt
    have hf : (fun k => gnsTracialVector τ (d (j k))) = fun k => (y k : τ.GNS) := by
      funext k
      exact (he (j k)).trans (congrArg Subtype.val (hj k))
    rw [hf]
    exact ht
  refine ⟨j, ?_⟩
  have ht := (hc.sub_const (gnsTracialVector τ b)).norm
  have hn (k : ℕ) : ‖gnsTracialVector τ (d (j k)) - gnsTracialVector τ b‖ =
      ‖τ.toPreGNS (d (j k) - b)‖ := by
    rw [← map_sub, gnsTracialVector_apply, UniformSpace.Completion.norm_coe]
  simpa only [GNSTendsto, hn, sub_self, norm_zero] using ht

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

include hσ trσ hφ in
/-- No norm separability is required. The approximating family is dense only
in the trace norm on the unit ball. -/
theorem integer_moments_of_trace_dense
    (d : ℕ → B) (hd : ∀ n, ‖d n‖ ≤ 1)
    (hdense : ∀ b : B, ‖b‖ ≤ 1 → ∃ j : ℕ → ℕ,
      GNSTendsto τ (fun k => d (j k)) atTop b)
    (u : unitary C)
    (hm : ∀ a : Option ℕ, ∀ l : List (IntAtom ℕ), admissibleIntTail l →
      (∀ b ∈ l, b.1 ≠ 0) →
      σ (integerEval (fun n => φ (d n) - σ (φ (d n)) • 1) u a l) = 0)
    (A : I → B) (hA : ∀ i, ‖A i‖ ≤ 1)
    (a : Option I) (l : List (IntAtom I)) (hl : admissibleIntTail l)
    (hk : ∀ b ∈ l, b.1 ≠ 0) :
    σ (integerEval (fun i => φ (A i) - σ (φ (A i)) • 1) u a l) = 0 := by
  classical
  choose j hj using fun i => hdense (A i) (hA i)
  let F : ℕ → I → C := fun n i => φ (d (j i n)) - σ (φ (d (j i n))) • 1
  apply integer_moment_zero_of_bounded_limits σ hσ trσ
    (F := F) (C := 2) (fun i => gnsTendsto_centered σ hσ
      (gnsTendsto_tracePreserving τ σ φ hφ (hj i))) (by norm_num)
    (fun n i => norm_centered_contraction σ hσ _ ((NonUnitalStarAlgHom.norm_apply_le φ _).trans (hd _))) u a l
  intro n
  have hr : integerEval (fun k => φ (d k) - σ (φ (d k)) • 1) u
      (a.map (fun i => j i n)) (l.map (fun b => (b.1, b.2.map (fun i => j i n)))) =
        integerEval (F n) u a l := by
    simp only [integerEval, List.map_map]
    congr 1
    · exact wordCoeff_map _ _ _
    · congr 1
      apply List.map_congr_left
      intro b _
      dsimp only [Function.comp_apply]
      rw [wordCoeff_map]
      rfl
  rw [← hr]
  apply hm
  · refine ⟨?_, ?_⟩
    · exact fun h => hl.1 (List.map_eq_nil_iff.mp h)
    · intro b hb
      rw [← List.map_dropLast] at hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact fun h => hl.2 c hc (Option.map_eq_none_iff.mp h)
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact hk c hc

include hσ trσ hφ in
/-- Scaling each coefficient separately removes the contraction restriction. -/
theorem all_integer_moments_of_trace_dense
    (d : ℕ → B) (hd : ∀ n, ‖d n‖ ≤ 1)
    (hdense : ∀ b : B, ‖b‖ ≤ 1 → ∃ j : ℕ → ℕ,
      GNSTendsto τ (fun k => d (j k)) atTop b)
    (u : unitary C)
    (hm : ∀ a : Option ℕ, ∀ l : List (IntAtom ℕ), admissibleIntTail l →
      (∀ b ∈ l, b.1 ≠ 0) →
      σ (integerEval (fun n => φ (d n) - σ (φ (d n)) • 1) u a l) = 0)
    (A : I → B) (a : Option I) (l : List (IntAtom I)) (hl : admissibleIntTail l)
    (hk : ∀ b ∈ l, b.1 ≠ 0) :
    σ (integerEval (fun i => φ (A i) - σ (φ (A i)) • 1) u a l) = 0 := by
  let c : I → ℂ := fun i => ((‖A i‖ + 1 : ℝ) : ℂ)
  have hc (i : I) : c i ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (ne_of_gt (show 0 < ‖A i‖ + 1 by positivity))
  let A' : I → B := fun i => (c i)⁻¹ • A i
  have hA' (i : I) : ‖A' i‖ ≤ 1 := by
    change ‖(c i)⁻¹ • A i‖ ≤ 1
    rw [norm_smul, norm_inv]
    have hn : ‖c i‖ = ‖A i‖ + 1 := by
      simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖A i‖ + 1)]
    rw [hn, ← div_eq_inv_mul]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hz := integer_moments_of_trace_dense τ σ hσ trσ φ hφ d hd hdense u hm A' hA' a l hl hk
  have he (i : I) : φ (A i) - σ (φ (A i)) • 1 =
      c i • (φ (A' i) - σ (φ (A' i)) • 1) := by
    dsimp only [A']
    rw [map_smul, map_smul, smul_sub, smul_smul, mul_inv_cancel₀ (hc i), one_smul,
      smul_smul]
    congr 1
    congr 1
    simp only [smul_eq_mul]
    field_simp [hc i]
  simp_rw [he]
  rw [integerEval_smul_family, map_smul, hz, smul_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceUltrapowerInclusion
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate source unitaries define the required unitary in the actual
source ultrapower, and its ambient image is the coordinatewise image. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower HochschildPatching TracialUltrapower
open scoped ComplexOrder BoundedContinuousFunction

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b, τA (a * b) = τA (b * a))
  (trB : ∀ a b, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (ht : ∀ a, τB (φ a) = τA a)

theorem tracialUltrapowerMap_quotientUnitary (u : ℕ → unitary A) :
    tracialUltrapowerMap τA τB hA hB ω trA trB φ ht
      (quotientUnitary τA hA ω trA u : Ultrapower τA hA ω trA) =
    (quotientUnitary τB hB ω trB (fun n => mapUnitary φ (u n)) :
      Ultrapower τB hB ω trB) := by
  rw [quotientUnitary_coe, tracialUltrapowerMap_mk, quotientUnitary_coe]
  congr 1
  ext n
  simp only [boundedSequenceStarHom_apply, unitarySequence_apply, mapUnitary_coe]

theorem mapUnitary_tracialUltrapowerMap (u : ℕ → unitary A) :
    mapUnitary (tracialUltrapowerMap τA τB hA hB ω trA trB φ ht)
      (quotientUnitary τA hA ω trA u) =
    quotientUnitary τB hB ω trB (fun n => mapUnitary φ (u n)) := by
  apply Subtype.ext
  exact tracialUltrapowerMap_quotientUnitary τA τB hA hB ω trA trB φ ht u

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ConstantConjugateFreeness
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source quotient unitaries and the concrete conjugated constant embedding. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching HochschildUltrapower
open scoped ComplexOrder BoundedContinuousFunction

section Inclusion
variable {A B R : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [CStarAlgebra R]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b, τA (a * b) = τA (b * a))
  (trB : ∀ a b, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

theorem tracialUltrapowerMap_constant (a : A) :
    tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ (constant τA hA ω trA a) =
      constant τB hB ω trB (φ a) := by
  change quotientHom τB hB ω trB
    (boundedSequenceStarHom φ (constantSequence a)) =
    quotientHom τB hB ω trB (constantSequence (φ a))
  congr 1

theorem conjugatedConstantEmbedding_coordinate (ρ : R →⋆ₐ[ℂ] A)
    (u : ℕ → unitary A) (a : R) :
    conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ
      (quotientUnitary τA hA ω trA u) a =
    Unitary.conjStarAlgAut ℂ (Ultrapower τB hB ω trB)
      (quotientUnitary τB hB ω trB (fun n => mapUnitary φ (u n)))
      (constant τB hB ω trB (φ (ρ a))) := by
  change tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ
    ((quotientUnitary τA hA ω trA u : Ultrapower τA hA ω trA) *
      constant τA hA ω trA (ρ a) * star (quotientUnitary τA hA ω trA u : Ultrapower τA hA ω trA)) = _
  rw [map_mul, map_mul, map_star, tracialUltrapowerMap_quotientUnitary,
    tracialUltrapowerMap_constant]
  rfl

end Inclusion

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixPopaPosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed source factor is conjugated diagonally inside the prescribed
matrix-subfactor ultrapower. Trace and inclusion properties follow from the
concrete maps, with no operator-estimate hypothesis. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hR : τR 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trR : ∀ a b : R, τR (a * b) = τR (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (ρ : R →⋆ₐ[ℂ] B) (hρτ : ∀ a, τB (ρ a) = τR a)
  (n : ℕ) [NeZero n]

local notation "τRn" => normalizedMatrixTrace τR n
local notation "τBn" => normalizedMatrixTrace τB n
local notation "hRn" => normalizedMatrixTrace_one τR hR
local notation "hBn" => normalizedMatrixTrace_one τB hB
local notation "trRn" => normalizedMatrixTrace_tracial τR trR
local notation "trBn" => normalizedMatrixTrace_tracial τB trB
local notation "ρn" => matrixEntryHom (n := n) ρ
local notation "hρn" => normalizedMatrixTrace_entryHom τR τB ρ hρτ

/-- The conjugate of the fixed source factor, diagonal in the matrix
subfactor before passing to the tracial ultrapower. -/
def matrixConjugatedEmbedding (u : unitary (Ultrapower τRn hRn ω trRn)) :
    R →⋆ₐ[ℂ] Ultrapower τBn hBn ω trBn :=
  conjugatedConstantEmbedding τRn τBn hRn hBn ω trRn trBn ρn hρn
    (matrixDiagonalHom n) u

theorem matrixConjugatedEmbedding_trace
    (u : unitary (Ultrapower τRn hRn ω trRn)) (a : R) :
    quotientTrace τBn hBn ω trBn
      (matrixConjugatedEmbedding τR τB hR hB ω trR trB ρ hρτ n u a) = τR a := by
  change quotientTrace τBn hBn ω trBn
    (conjugatedConstantEmbedding τRn τBn hRn hBn ω trRn trBn ρn hρn
      (matrixDiagonalHom n) u a) = τR a
  rw [conjugatedConstantEmbedding_trace, normalizedMatrixTrace_diagonal]

theorem matrixConjugatedEmbedding_injective
    (hfR : ∀ a : R, τR (star a * a) = 0 → a = 0)
    (u : unitary (Ultrapower τRn hRn ω trRn)) :
    Function.Injective (matrixConjugatedEmbedding τR τB hR hB ω trR trB ρ hρτ n u) :=
  conjugatedConstantEmbedding_injective τRn τBn hRn hBn ω trRn trBn ρn hρn
    (matrixDiagonalHom n) (matrixDiagonalHom_injective n)
    (normalizedMatrixTrace_faithful τR hfR) u

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_MatrixFreeCornerApplication
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The free-corner estimate for an actual matrix GNS operator

The matrix subfactor is the entrywise image of the original inclusion.
Projection comparison transports the scalar bound to all sufficiently small
matrix corners. Popa's local conjugacy input chooses the free copy, while
all native GNS geometry is the canonical generated geometry. The remaining
local input consists exactly of the published structural data for that
geometry; it contains no commutator bound.
-/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hR : τR 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trR : ∀ a b : R, τR (a * b) = τR (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (ρ : R →⋆ₐ[ℂ] B) (hρτ : ∀ a, τB (ρ a) = τR a)
  (hfR : ∀ a : R, τR (star a * a) = 0 → a = 0)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  (n : ℕ) [NeZero n]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))
  (Q : SmallFreeCornerData τR.toLinearMap (n : ℝ)⁻¹)

local notation "τRn" => normalizedMatrixTrace τR n
local notation "τBn" => normalizedMatrixTrace τB n
local notation "hRn" => normalizedMatrixTrace_one τR hR
local notation "hBn" => normalizedMatrixTrace_one τB hB
local notation "trRn" => normalizedMatrixTrace_tracial τR trR
local notation "trBn" => normalizedMatrixTrace_tracial τB trB
local notation "ψ" => matrixConjugatedEmbedding τR τB hR hB ω trR trB ρ hρτ n
local notation "hψτ" => matrixConjugatedEmbedding_trace τR τB hR hB ω trR trB ρ hρτ n
local notation "hψ" => matrixConjugatedEmbedding_injective τR τB hR hB ω trR trB ρ hρτ n hfR

/-- The exact local published bundle on the canonical matrix free-product
model. This abbreviation only fixes the generated geometry and transported
frame; it does not assert the existence of any of its fields. -/
abbrev MatrixFreeCornerLocalInput
    (u : unitary (Ultrapower τRn hRn ω trRn))
    (x : CStarMatrix (Fin n) (Fin n) B) (hxsq : x * x = 1) : Prop :=
  CanonicalFreeCornerInput τBn τR hBn ω trBn (ψ u) (hψτ u)
    (hψ u) M
    (canonicalGeneratedSmallFrame τBn τR hBn ω trBn (ψ u) (hψτ u) (hψ u) Q)
    x hxsq

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GNSVectorDensity
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Norm approximation transfers from concrete trace vectors to native
GNS vectors. The generic form keeps the concrete matrix construction small. -/

noncomputable section
namespace KadisonSimilarity

open Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : A →ₚ[ℂ] ℂ) (M : VonNeumannAlgebra H) (υ : TracialRepresentation M)
  (e : A ≃⋆ₐ[ℂ] M.toStarSubalgebra) (hτ : ∀ a, τ a = υ.trace (e a))

omit [CompleteSpace H] in
theorem gns_dist_eq_of_trace_vectors (V : A →ₗ[ℂ] H)
    (hV : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b)) (a b : A) :
    dist (gnsTracialVector τ a) (gnsTracialVector τ b) = dist (V a) (V b) := by
  apply (sq_eq_sq₀ (dist_nonneg : 0 ≤ dist _ _) dist_nonneg).mp
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub,
    norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    gnsTracialVector_inner, hV]

variable {I : Type*} {B : I → Type*} (φ : ∀ i, B i → A)

theorem gns_vectors_dense_of_approximation
    (h : ∀ a : A, ∀ ε : ℝ, 0 < ε → ∃ i b,
      dist (gnsTracialVector τ (φ i b)) (gnsTracialVector τ a) < ε) :
    Dense (⋃ i, Set.range (fun b => gnsTracialVector τ (φ i b))) := by
  intro ξ
  refine (gnsTracialVector_dense τ).induction_on ξ isClosed_closure ?_
  intro a
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨i, b, hb⟩ := h a ε hε
  exact ⟨gnsTracialVector τ (φ i b), Set.mem_iUnion.mpr ⟨i, b, rfl⟩,
    by simpa only [dist_comm] using hb⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialInclusionNormality
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.generatedGNSInclusion_vector _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace-preserving inclusion with closed source trace-vector balls has
normal range in a faithful concrete finite trace representation. -/

noncomputable section
namespace KadisonSimilarity

open Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u v
variable {A : Type u} {H : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (υ : TracialRepresentation M)
  (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] M.toStarSubalgebra)
  (hφ : ∀ a, υ.trace (φ a) = τ a)

include hφ

omit [StarOrderedRing A] in
theorem tracePreservingVector_inner (a b : A) :
    inner ℂ (baseVector υ (φ a)) (baseVector υ (φ b)) = τ (star a * b) := by
  rw [baseVector_inner_trace, ← map_star φ, ← map_mul φ, hφ]

theorem tracePreservingVector_norm (a : A) :
    ‖baseVector υ (φ a)‖ = ‖gnsTracialVector τ a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    tracePreservingVector_inner υ τ φ hφ, gnsTracialVector_inner]

def tracialInclusionIsometry : τ.GNS →ₗᵢ[ℂ] H :=
  ((baseVector υ).comp φ.toLinearMap).extendOfIsometry
    (gnsTracialVector_dense τ) (tracePreservingVector_norm υ τ φ hφ)

@[simp] theorem tracialInclusionIsometry_vector (a : A) :
    tracialInclusionIsometry υ τ φ hφ (gnsTracialVector τ a) = baseVector υ (φ a) :=
  LinearMap.extendOfIsometry_eq _ (gnsTracialVector_dense τ)
    (tracePreservingVector_norm υ τ φ hφ) a

theorem tracialInclusion_trace_balls_closed
    (hclosed : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (C : ℝ) :
    IsClosed ((fun a => baseVector υ (φ a)) '' Metric.closedBall (0 : A) C) := by
  let J := tracialInclusionIsometry υ τ φ hφ
  have heq : (fun a => baseVector υ (φ a)) '' Metric.closedBall (0 : A) C =
      J '' (gnsTracialVector τ '' Metric.closedBall (0 : A) C) := by
    rw [Set.image_image]
    congr 1
    funext a
    exact (tracialInclusionIsometry_vector υ τ φ hφ a).symm
  rw [heq]
  exact J.isometry.isClosedEmbedding.isClosedMap _ (hclosed C)

theorem tracialInclusion_normal_range
    (hclosed : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C)) :
    (M.toStarSubalgebra.subtype.comp φ).range =
      (representationVonNeumannAlgebra (M.toStarSubalgebra.subtype.comp φ)).toStarSubalgebra := by
  let σ := M.toStarSubalgebra.subtype.comp φ
  apply le_antisymm
  · rintro T ⟨a, rfl⟩
    exact mem_representationVonNeumannAlgebra σ a
  · intro T hT
    have hTM : T ∈ M := by
      change T ∈ representationVonNeumannAlgebra σ at hT
      rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
      rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
      intro b hb
      apply hT b
      rintro _ ⟨a, rfl⟩
      exact hb _ (φ a).property
    let x : M.toStarSubalgebra := ⟨T, hTM⟩
    have hx : baseVector υ x ∈ closure
        ((fun a => baseVector υ (φ a)) '' Metric.closedBall (0 : A) (‖T‖ + 1)) := by
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      let δ := min 1 (ε / 2)
      have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
      have hδ1 : δ ≤ 1 := min_le_left _ _
      have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
      obtain ⟨a, han, ha, _⟩ := twoVectorKaplanskyInput σ T hT υ.vector υ.vector δ hδ
      refine ⟨baseVector υ (φ a), ⟨a, ?_, rfl⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using
          han.trans (show ‖T‖ + δ ≤ ‖T‖ + 1 by linarith)
      · rw [dist_eq_norm, norm_sub_rev]
        exact ha.trans_lt hδε
    obtain ⟨a, _, ha⟩ := (tracialInclusion_trace_balls_closed υ τ φ hφ hclosed (‖T‖ + 1)).closure_subset hx
    have hax : φ a = x := by
      apply sub_eq_zero.mp
      apply υ.separating
      change baseVector υ (φ a - x) = 0
      change baseVector υ (φ a) = baseVector υ x at ha
      rw [map_sub, ha, sub_self]
    exact ⟨a, congrArg Subtype.val hax⟩

theorem tracialInclusion_normal_range_of_predual
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (hτ : BoundedHochschild.TraceInPredual e τ) :
    (M.toStarSubalgebra.subtype.comp φ).range =
      (representationVonNeumannAlgebra (M.toStarSubalgebra.subtype.comp φ)).toStarSubalgebra :=
  tracialInclusion_normal_range υ τ φ hφ (predual_gns_trace_balls_closed e τ hτ)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_IntegerMomentMaps
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Naturality and coefficient reindexing for finite integer-power words. -/

namespace KadisonSimilarity
open HochschildPatching
variable {A B I J : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem integerEval_hom (φ : A →⋆ₐ[ℂ] B) (F : I → A) (u : unitary A)
    (a : Option I) (l : List (IntAtom I)) :
    φ (integerEval F u a l) = integerEval (φ ∘ F) (mapUnitary φ u) a l := by
  simp only [integerEval, map_mul, wordCoeff_hom, map_list_prod, List.map_map]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply, map_mul, wordCoeff_hom, mapUnitary_zpow]

theorem integerEval_reindex (F : J → A) (f : I → J) (u : unitary A)
    (a : Option I) (l : List (IntAtom I)) :
    integerEval F u (a.map f) (l.map (fun b => (b.1, b.2.map f))) =
      integerEval (F ∘ f) u a l := by
  simp only [integerEval, List.map_map]
  congr 1
  · exact wordCoeff_map F f a
  · apply congrArg List.prod
    apply List.map_congr_left
    intro b _
    simp only [Function.comp_apply, wordCoeff_map]

end KadisonSimilarity

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GNSSeparableTransport
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separability follows a trace-preserving equivalence of the actual algebras. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (e : A ≃⋆ₐ[ℂ] B) (ht : ∀ a, τB (e a) = τA a)

include ht in
theorem gns_separable_of_trace_equiv [TopologicalSpace.SeparableSpace τA.GNS] :
    TopologicalSpace.SeparableSpace τB.GNS := by
  let J := gnsTracialHomIsometry τA τB e.toStarAlgHom ht
  have hJ : Function.Surjective J := by
    intro x
    change x ∈ Set.range J
    refine (gnsTracialVector_dense τB).induction_on x
      J.isometry.isClosedEmbedding.isClosed_range ?_
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    exact ⟨gnsTracialVector τA a, gnsTracialHomIsometry_vector τA τB e.toStarAlgHom ht a⟩
  have hs := TopologicalSpace.isSeparable_range J.continuous
  rw [Set.range_eq_univ.mpr hJ] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixDiffuseSource
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection comparison and small diagonal matrix corners show that each
finite matrix amplification of the prescribed source is diffuse. -/

noncomputable section
namespace KadisonSimilarity
open UltrapowerBridge
open scoped ComplexOrder

namespace TracialCornerGeometry
variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem proper_subprojection_of_small_trace
    (hf : Function.Injective G.vector)
    (comparison : FiniteFactorProjectionComparison (fun a => (G.trace a).re))
    (small : ∀ s : ℝ, 0 < s → ∃ e : A, IsStarProjection e ∧
      0 < (G.trace e).re ∧ (G.trace e).re < s)
    (p : A) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  have hv : G.vector p ≠ 0 := by
    intro h
    exact hp0 (hf (h.trans (map_zero G.vector).symm))
  have hpnorm : ‖G.vector p‖ ^ 2 = (G.trace p).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.inner_vector,
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    rfl
  have hppos : 0 < (G.trace p).re := by
    rw [← hpnorm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  obtain ⟨e, he, hepos, hetrace⟩ := small _ hppos
  obtain ⟨v, hv, hpv⟩ := comparison p e hp he hetrace.le
  let q := v * star v
  have hq : IsStarProjection q := range_projection_of_initial_projection e v he hv
  have hτq : G.trace q = G.trace e := by
    change G.trace (v * star v) = _
    rw [G.tracial, hv]
  have hq0 : q ≠ 0 := by
    intro h
    have hh := congrArg Complex.re hτq
    rw [h, map_zero] at hh
    exact (ne_of_gt hepos) hh.symm
  have hqp : q ≠ p := by
    intro h
    have hh := congrArg Complex.re hτq
    rw [h] at hh
    exact (ne_of_lt hetrace) hh.symm
  refine ⟨q, hq, hq0, hqp, hpv, ?_⟩
  have hpq : p * q = q := hpv
  have h := congrArg star hpq
  simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using h
end TracialCornerGeometry

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_MatrixSourceFreeness
attribute [-instance] _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved prescribed-source freeness theorem supplies every finite
matrix amplification required by the finite-factor estimate. -/

noncomputable section
namespace KadisonSimilarity
open UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem matrix_gns_separable (τ : B →ₚ[ℂ] ℂ)
    [TopologicalSpace.SeparableSpace τ.GNS] (n : ℕ) [NeZero n] :
    TopologicalSpace.SeparableSpace (normalizedMatrixTrace τ n).GNS := by
  let J := (matrixGNSUnitary τ n).symm
  have hs := TopologicalSpace.isSeparable_range J.continuous
  rw [Set.range_eq_univ.mpr J.surjective] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

end KadisonSimilarity

end

end OAI
end


