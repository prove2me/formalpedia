-- Prove2me | Definitions.Def_OAIQ075A037
-- name    : OAIQ075A037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:16:18.873981+00:00
-- url     : https://prove2.me/theorems/9f858f7d-7ca2-4e53-9465-8769624bd972
-- title:
--   Definitions bundle OAIQ075A037 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.KadisonSimilarity.embeddedWordMatrixActions`, `OAI.KadisonSimilarity.reducedWordCreationModel`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonSimilarity_FreeProduct_EmbeddedWordActions`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/EmbeddedWordActions.lean), [`KadisonSimilarity_FreeProduct_FreeCreationDischarge`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/FreeCreationDischarge.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A030` and `OAIQ075A033` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words`, `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs`, `OAI_KadisonSimilarity_TracialCornerGeometry_tracial_adjoint_repeated_word`, `OAI_KadisonSimilarity_TracialCornerGeometry_tracial_repeated_word` and `OAI_KadisonSimilarity_TracialCornerGeometry_tracial_word_level_ranges`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A030
import Definitions.Def_OAIQ075A033

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_EmbeddedWordActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_base _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_column _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_corner _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensorMapIsometry_insert _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
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

section EmbeddedActions
universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (M : NestedTracialMatrices (A := A) τ V)
  (htrace : ∀ a b, τ (a * b) = τ (b * a)) (S : RealTracialSequence τ)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop)
  {J : ℕ → Type*} [∀ n, NormedAddCommGroup (J n)] [∀ n, InnerProductSpace ℂ (J n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : OrthogonalWordLevels (MultiplicityWordSpace J E (centeredSubspace (V 1))) H)
  (leftRep : ∀ s, Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
  (unitaryRep : ∀ s, Matrix.unitaryGroup (A s) ℂ →* unitary (H →L[ℂ] H))
  (hL : ∀ s a n, (leftRep s a).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (endpointHeadAction (n := n)
        (((tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize).stage s).left a))))
  (hU : ∀ s u n, (unitaryRep s u : H →L[ℂ] H).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (tracialMatrixWordAction τ V L (M.embedding s) hinner hleft htrace
        (NestedTracialMatrices.denseRange_vector τ V M) u n).toContinuousLinearMap))

/-- The action record for the invariant classification, obtained from actual
representations and the two raw word inclusion formulas alone. -/
def embeddedWordMatrixActions :
    WordLevelMatrixActions (tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize) U where
  leftAction s a := leftRep s a
  unitaryAction s u := unitaryRep s u
  wordAction s n u := tracialMatrixWordAction τ V L (M.embedding s) hinner hleft htrace
    (NestedTracialMatrices.denseRange_vector τ V M) u n
  left_inclusion := hL
  left_adjoint_inclusion s a n := by
    have hstar :
        ((tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize).stage s).left (star a) =
          (((tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize).stage s).left a).adjoint := by
      change L (M.embedding s (star a)) = (L (M.embedding s a)).adjoint
      rw [map_star, map_star, ContinuousLinearMap.star_eq_adjoint]
    simpa only [map_star, ContinuousLinearMap.star_eq_adjoint, hstar,
      hilbertTensorLift_adjoint, endpointHeadAction_adjoint] using hL s (star a) n
  unitary_inclusion := hU
  unitary_adjoint_inclusion s u n := by
    have hstar : (unitaryRep s u⁻¹ : H →L[ℂ] H) = (unitaryRep s u : H →L[ℂ] H).adjoint := by
      rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star, ContinuousLinearMap.star_eq_adjoint]
    simpa only [hstar, hilbertTensorLift_adjoint,
      tracialMatrixWordAction_adjoint] using hU s u⁻¹ n
  source_word s n u v := by
    let C := tracialMatrixWordCovariance τ V L (M.embedding s) hinner hleft htrace
      (NestedTracialMatrices.denseRange_vector τ V M) (NestedTracialMatrices.trace_one τ V M)
      (M.trace_embedding s) (Y := (0 : EndpointTensor E (centeredSubspace (V 1)) n →L[ℂ]
        EndpointTensor E (centeredSubspace (V 1)) n)) (by intro w; simp)
    exact C.source_covariance u (fun x => match x with
      | none => 0
      | some (.inl i) => v i
      | some (.inr _) => 0)
  test_word s n u a v := by
    let C := tracialMatrixWordCovariance τ V L (M.embedding s) hinner hleft htrace
      (NestedTracialMatrices.denseRange_vector τ V M) (NestedTracialMatrices.trace_one τ V M)
      (M.trace_embedding s) (Y := (0 : EndpointTensor E (centeredSubspace (V 1)) n →L[ℂ]
        EndpointTensor E (centeredSubspace (V 1)) n)) (by intro w; simp)
    exact C.test_covariance u (fun x => match x with
      | none => a
      | some (.inl _) => 0
      | some (.inr i) => v i)

end EmbeddedActions
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCreationDischarge
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

def reducedWordCreationModel (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D) :
    ReducedWordCreationModel G A D := by
  let W := freeTracialHeadCoordinates G A D hτ hf.symm hgen
  let e := LinearIsometryEquiv.ofEq W.vacuumᗮ (leadingWordSpace G A D false).toSubmodule
    (freeHead_vacuum_orthogonal G A D hτ hf hgen)
  let cA := freeCreationIsometry G A D A true rfl hτ hf.symm
  let cD := freeCreationIsometry G A D D false rfl hτ hf.symm
  let iA := (leadingIntoCentered G A D false).comp e.toLinearIsometry
  refine {
    tail := centeredWordSpace G A D true
    head := W
    aLead := leadingWordSpace G A D true
    createA := cA.comp (hilbertTensorMapIsometry (LinearIsometry.id) iA)
    createD := cD.comp (hilbertTensorMapIsometry (LinearIsometry.id) (leadingIntoCentered G A D true))
    createA_mem := ?_
    createD_mem := ?_
    actionA := ?_
    actionD := ?_ }
  · intro z
    exact freeCreationIsometry_mem G A D A true rfl hτ hf.symm _
  · intro z
    rw [freeHead_vacuum_orthogonal G A D hτ hf hgen]
    exact freeCreationIsometry_mem G A D D false rfl hτ hf.symm _
  · intro a ha y
    change G.left (a : P) (y : H) = cA
      (hilbertTensorMapIsometry (LinearIsometry.id) iA
        (hilbertTensorInsert (G.baseSymmetryLetter A a ha) y))
    rw [hilbertTensorMapIsometry_insert]
    exact (freeCreationIsometry_left G A D A true rfl hτ hf.symm a ha (iA y)).symm
  · intro d hd y
    change G.left (d : P) (y : H) = cD
      (hilbertTensorMapIsometry (LinearIsometry.id) (leadingIntoCentered G A D true)
        (hilbertTensorInsert (G.baseSymmetryLetter D d hd) y))
    rw [hilbertTensorMapIsometry_insert]
    exact (freeCreationIsometry_left G A D D false rfl hτ hf.symm d hd
      (leadingIntoCentered G A D true y)).symm

end KadisonSimilarity

end

end OAI
end


