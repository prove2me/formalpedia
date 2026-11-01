-- Prove2me | Definitions.Def_OAIQ075A018
-- name    : OAIQ075A018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:09:55.090827+00:00
-- url     : https://prove2.me/theorems/b5661202-572e-40d8-b7e2-366a97f8a1bf
-- title:
--   Definitions bundle OAIQ075A018 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 4 definitions and 3 theorems. The definitions and types are `OAI.KadisonSimilarity.firstCoordinateInclusion`, `OAI.KadisonSimilarity.normalizedRectangularRepresentation`, `OAI.KadisonSimilarity.tracialSeedRepresentation`, `OAI.KadisonSimilarity.tracialSeedVonNeumann`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonSimilarity_Derivation_RectangularDerivations`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Derivation/RectangularDerivations.lean), [`KadisonSimilarity_Similarity_FiniteCyclicSimilarity`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Similarity/FiniteCyclicSimilarity.lean), [`KadisonSimilarity_Tracial_GNSProjectionContinuity`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/GNSProjectionContinuity.lean), [`KadisonSimilarity_Tracial_ProjectionJoinTrace`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/ProjectionJoinTrace.lean), [`KadisonSimilarity_Tracial_ProjectionTraceContinuity`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/ProjectionTraceContinuity.lean), [`KadisonSimilarity_Tracial_TracialNormalSpan`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialNormalSpan.lean).
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A010` and `OAIQ075A011` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI_KadisonSimilarity_exists_corner_intertwiner_of_column_tests`; the proofs of `OAI.KadisonSimilarity.TracialCornerGeometry.generated_dihedral_spectralInput`, `OAI.KadisonSimilarity.TracialCornerGeometry.l2Generated_tracialExpectation`, `OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs`, `OAI.KadisonSimilarity.commutatorEstimate_of_centralDecomposition`, `OAI_KadisonSimilarity_exists_corner_intertwiner_of_column_tests`, `OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv`, `OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable` and `OAI.KadisonSimilarity.similarityTheorem`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A010
import Definitions.Def_OAIQ075A011

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_RectangularDerivations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

def normalizedRectangularRepresentation (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) :
    BoundedUnitalHom A (RectangularSum F K) :=
  rectangularRepresentation ρ σ (normalizedRectangularDerivation δ)
    (normalizedRectangularDerivation_leibniz ρ σ δ hδ)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_FiniteCyclicSimilarity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedMatrixHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finitely cyclic representations reduce to the cyclic case by finite
matrix amplification and the first-coordinate corner. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def firstCoordinateInclusion (n : ℕ) (hn : 0 < n) : H →L[ℂ] HilbertCopies H n :=
  ({ toFun := fun x => PiLp.single 2 (⟨0, hn⟩ : Fin n) x
     map_add' := by intro x y; exact PiLp.single_add _ _
     map_smul' := by
       intro c x
       ext i
       by_cases h : i = (⟨0, hn⟩ : Fin n) <;> simp [h] } :
    H →ₗ[ℂ] HilbertCopies H n).mkContinuous 1 (fun x => by simp)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialNormalSpan
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed star subalgebra of a finite von Neumann algebra generates
exactly the bounded elements in the closure of its trace vectors. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonSimilarity.ambient_closed
variable (S : StarSubalgebra ℂ M.toStarSubalgebra) [IsClosed (S : Set M.toStarSubalgebra)]

def tracialSeedRepresentation : S →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp S.subtype

def tracialSeedVonNeumann : VonNeumannAlgebra H :=
  representationVonNeumannAlgebra (tracialSeedRepresentation S)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ProjectionJoinTrace
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite joins of projections and their trace bound. These elementary
support identities are used to control countable unions of small spectral
projections in the normal representation argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance joinTrace_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ProjectionTraceContinuity
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small trace projections act strongly as zero. The argument uses
countable joins and geometric trace tails, rather than assuming normality
of a star isomorphism between concrete von Neumann algebras. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge Filter
open scoped ComplexOrder Topology

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance projectionContinuity_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GNSProjectionContinuity
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection continuity in the original representation follows from
faithfulness and normality of the chosen trace's native GNS range. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge Filter
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance gnsProjection_closed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (M : VonNeumannAlgebra E) :
    IsClosed (M.toStarSubalgebra : Set (E →L[ℂ] E)) := by
  change IsClosed (M : Set (E →L[ℂ] E))
  infer_instance

end KadisonSimilarity

end

end OAI
end


