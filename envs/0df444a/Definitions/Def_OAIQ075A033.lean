-- Prove2me | Definitions.Def_OAIQ075A033
-- name    : OAIQ075A033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:43:53.677762+00:00
-- url     : https://prove2.me/theorems/2a017dc1-56af-4fa4-8ab3-33bf7acb60de
-- title:
--   Definitions bundle OAIQ075A033 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 17 definitions, 3 inductive types or structures, 1 instance and 19 theorems. The definitions and types are `OAI.KadisonSimilarity.PublishedFactorCasesInput`, `OAI.KadisonSimilarity.PublishedSeparableModel`, `OAI.KadisonSimilarity.PublishedUniformInputs`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseTracialMatrixTower`, `OAI.KadisonSimilarity.TracialCornerGeometry.commutantTracialRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionHom`, `OAI.KadisonSimilarity.TracialCornerGeometry.normalMatrixTower`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialWordRepeatedOperator`, `OAI.KadisonSimilarity.TracialCreationFormulas.repeatedWordRealization`, `OAI.KadisonSimilarity.TracialCreationFormulas.toAlternatingCreationCoordinates`, `OAI.KadisonSimilarity.TracialMatrixTower.tail`, `OAI.KadisonSimilarity.WordLevelMatrixActions`, `OAI.KadisonSimilarity.WordLevelMatrixActions.blockCovariance`, `OAI.KadisonSimilarity.WordLevelMatrixActions.diagonalCovariance`, `OAI.KadisonSimilarity.WordLevelMatrixActions.tail`, `OAI.KadisonSimilarity.commonProjectionCentralData`, `OAI.KadisonSimilarity.dyadicUnitaryApprox`, `OAI.KadisonSimilarity.projectionCentralData`, `OAI.KadisonSimilarity.tracialMatrixTowerOfEmbeddings`, `OAI.KadisonSimilarity.wordLevelRepeatedOperator`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonSimilarity_ConditionalMain`, `KadisonSimilarity_FreeProduct_DyadicHaarUnitary`, `KadisonSimilarity_FreeProduct_FreeCreationDischarge`, `KadisonSimilarity_FreeProduct_FreeMatrixExtension`, `KadisonSimilarity_FreeProduct_GeneratedDihedralAlgebras`, `KadisonSimilarity_FreeProduct_OrthogonalWordLevels`, `KadisonSimilarity_FreeProduct_TracialEmbeddedWordStructure`, `KadisonSimilarity_FreeProduct_WordLevelRepeatedOperators`, `KadisonSimilarity_Representation_CentralDecompositionTests`, `KadisonSimilarity_Representation_CommonCentralData`, `KadisonSimilarity_Representation_FactorAssembly`, `KadisonSimilarity_Representation_IsometricFieldClosure`, `KadisonSimilarity_Representation_KaplanskyStrongSequence`, `KadisonSimilarity_Representation_NormalFactorGeneration`, `KadisonSimilarity_Representation_ProjectionCentralData`, `KadisonSimilarity_Representation_ProjectionFieldClosure`, `KadisonSimilarity_Representation_SeparableRepresentationTests`, `KadisonSimilarity_Tracial_CofinalMatrixTowers`, `KadisonSimilarity_Tracial_ConcreteRealSequence`, `KadisonSimilarity_Tracial_GeneratedFiniteFactorModel`, `KadisonSimilarity_Tracial_MatrixStageGrowth`, `KadisonSimilarity_Tracial_NormalSmallCorners`, `KadisonSimilarity_Tracial_SourceCornerQuantization`, `KadisonSimilarity_Tracial_TracialCommutantTrace`, `KadisonSimilarity_Tracial_TracialCreationCoordinates`, `KadisonSimilarity_Tracial_TracialGeneratedNormalClosure`, `KadisonSimilarity_Tracial_TracialMatrixTower`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A026`, `OAIQ075A027`, `OAIQ075A028` and `OAIQ075A029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A036` and `OAIQ075A037`; the statements `OAI_KadisonSimilarity_TracialCornerGeometry_tracial_adjoint_repeated_word`, `OAI_KadisonSimilarity_TracialCornerGeometry_tracial_repeated_word`, `OAI.KadisonSimilarity.commutatorEstimate_of_centralDecomposition`, `OAI_KadisonSimilarity_matrixFreeCornerLocalInput_of_normal_source` and `OAI.KadisonSimilarity.publishedUniformInputs`; the proofs of `OAI.KadisonSimilarity.TracialCornerGeometry.generated_dihedral_spectralInput`, `OAI.KadisonSimilarity.ae_common_fiber_scalar_center`, `OAI_KadisonSimilarity_ae_common_projection_rankOne_mem`, `OAI.KadisonSimilarity.commutatorEstimate_of_centralDecomposition`, `OAI_KadisonSimilarity_matrixFreeCornerLocalInput_of_normal_source`, `OAI.KadisonSimilarity.uniformCommutatorEstimate`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A026
import Definitions.Def_OAIQ075A027
import Definitions.Def_OAIQ075A028
import Definitions.Def_OAIQ075A029

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_OrthogonalWordLevels
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal word-level inclusions turn the proved off-diagonal block
vanishing into actual preservation of each full word level. -/

noncomputable section
namespace KadisonSimilarity

variable {W : ℕ → Type*} [∀ n, NormedAddCommGroup (W n)]
  [∀ n, InnerProductSpace ℂ (W n)] [∀ n, CompleteSpace (W n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section MatrixActions

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- Raw action data on the ambient word Hilbert space. Both ordinary and
adjoint inclusion covariance are explicit, as supplied by reducing free-word
levels. No operator block vanishing is included. -/
structure WordLevelMatrixActions
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H) where
  leftAction : ∀ s, Matrix (A s) (A s) ℂ → H →L[ℂ] H
  unitaryAction : ∀ s, Matrix.unitaryGroup (A s) ℂ → H →L[ℂ] H
  wordAction : ∀ s n, Matrix.unitaryGroup (A s) ℂ →
    EndpointTensor E F n →ₗᵢ[ℂ] EndpointTensor E F n
  left_inclusion : ∀ s a n, (leftAction s a).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (endpointHeadAction (n := n) ((T.stage s).left a)))
  left_adjoint_inclusion : ∀ s a n,
    (leftAction s a).adjoint.comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (endpointHeadAction (n := n) ((T.stage s).left a))).adjoint
  unitary_inclusion : ∀ s u n, (unitaryAction s u).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (wordAction s n u).toContinuousLinearMap)
  unitary_adjoint_inclusion : ∀ s u n,
    (unitaryAction s u).adjoint.comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (wordAction s n u).toContinuousLinearMap).adjoint
  source_word : ∀ s n (u : Matrix.unitaryGroup (A s) ℂ)
      (v : Fin n → Matrix (A s) (A s) ℂ),
    endpointWord T.traceVector (fun i => (T.stage s).center
      ((u : Matrix (A s) (A s) ℂ) * v i * star (u : Matrix (A s) (A s) ℂ))) =
      wordAction s n u (endpointWord T.traceVector (fun i => (T.stage s).center (v i)))
  test_word : ∀ s n (u : Matrix.unitaryGroup (A s) ℂ)
      (a : Matrix (A s) (A s) ℂ) (v : Fin n → Matrix (A s) (A s) ℂ),
    endpointWord ((T.stage s).full (star
      ((u : Matrix (A s) (A s) ℂ) * a * star (u : Matrix (A s) (A s) ℂ))))
      (fun i => T.conjugation ((T.stage s).center
        ((u : Matrix (A s) (A s) ℂ) * v i * star (u : Matrix (A s) (A s) ℂ)))) =
      wordAction s n u (endpointWord ((T.stage s).full (star a))
        (fun i => T.conjugation ((T.stage s).center (v i))))

variable (T : TracialMatrixTower (E := E) (F := F) (A := A))
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)
  (C : WordLevelMatrixActions T U) (Y : H →L[ℂ] H)
  (hleft : ∀ s a, Y.comp (C.leftAction s a) = (C.leftAction s a).comp Y)
  (hunitary : ∀ s u, Y.comp (C.unitaryAction s u) = (C.unitaryAction s u).comp Y)

/-- Ambient commutation and the actual inclusion identities supply the whole
cross-multiplicity covariance of every compressed word block. -/
def WordLevelMatrixActions.blockCovariance (s k l : ℕ) :
    CrossMultiplicityMatrixCovariance (T.stage s) T.conjugation T.traceVector (U.block Y l k) where
  sourceAction := C.wordAction s k
  testAction := C.wordAction s l
  intertwine u := U.block_intertwines Y (C.unitaryAction s u) _ _ (hunitary s u)
    (C.unitary_inclusion s u k) (C.unitary_adjoint_inclusion s u l)
  source_covariance u v := C.source_word s k u (fun i => v (some (.inl i)))
  test_covariance u v := C.test_word s l u (v none) (fun i => v (some (.inr i)))

end MatrixActions

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCreationCoordinates
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

namespace TracialCreationFormulas

variable {G A D W s hzero z ha htrace hhaar} {ALead : Submodule ℂ H}
  (C : TracialCreationFormulas G A D W s hzero z ha htrace hhaar ALead)

/-- Normalize the elementary creation data using the proved norms of the
actual symmetry and corner Haar vectors. -/
def toAlternatingCreationCoordinates (hself : star s = s) (hsquare : s * s = 1)
    (hτ : G.trace 1 = 1) :
    AlternatingCreationCoordinates (centeredSubspace (G.baseVector A 1))
      (centeredSubspace (G.baseVector D 1)) (G.left (s : P))
      (fun n => G.left ((haarCornerLetter z a n : D) : P)) W.vacuumᗮ where
  ALead := ALead
  s := G.baseSymmetryLetter A s hzero
  x := G.baseHaarLetter D z ha htrace hhaar
  norm_s := G.norm_baseSymmetryLetter A s hzero hself hsquare hτ
  norm_x := G.norm_baseHaarLetter D z ha htrace hhaar
  createA := C.createA
  createD := C.createD
  createA_mem := C.createA_mem
  createD_mem := C.createD_mem
  actionA := C.actionA
  actionD := C.actionD

/-- The concrete repeated-multiplicity insertion, together with raw word
factorization and level actions, gives the propagation realization. Complete
prefix isometry and uniform boundedness are both proved by this constructor. -/
def repeatedWordRealization (hself : star s = s) (hsquare : s * s = 1)
    (hτ : G.trace 1 = 1) (m : ℕ) (Y : H →L[ℂ] H)
    (B₀ : G.baseSpace A →L[ℂ] G.baseSpace A)
    (Bₖ : WordMultiplicity (G.baseVector A 1) (m + 1) →L[ℂ]
      WordMultiplicity (G.baseVector A 1) (m + 1))
    (word : ℕ → WordMultiplicity (G.baseVector A 1) (m + 1) →ₗᵢ[ℂ] H)
    (small : G.baseSpace A →L[ℂ] H)
    (hsmall : ∀ v, ‖small v‖ = Real.sqrt a * ‖v‖)
    (hlevelzero : ∀ v, Y (small v) = small (B₀ v))
    (hlevel : ∀ n v, Y (word n
      (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v)) =
      word n (Bₖ (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v)))
    (hsupport : ∀ v, G.left (q : P) (small v) = small v)
    (hword : ∀ n (v : A), word n
      (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1)
        (G.baseVector A v)) =
      G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)
        (G.left ((haarCornerLetter z a n : D) : P) (small (G.baseVector A v)))) :
    TracialRepeatedWordRealization W z a Y B₀ Bₖ := by
  have hword' (n : ℕ) (v : G.baseSpace A) : word n
      (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v) =
      G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)
        (G.left ((haarCornerLetter z a n : D) : P) (small v)) := by
    exact (G.baseVector_dense A).induction_on v
      (isClosed_eq (by fun_prop) (by fun_prop)) (hword n)
  have hselfP : star (s : P) = (s : P) := congrArg (fun x : A => (x : P)) hself
  have hsquareP : (s : P) * (s : P) = 1 := congrArg (fun x : A => (x : P)) hsquare
  exact tracialRepeatedWordRealizationOfCreation W z a (s : P) hselfP hsquareP
    (C.toAlternatingCreationCoordinates hself hsquare hτ) m Y B₀ Bₖ
    (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1))
    word small hsmall hlevelzero hlevel hsupport hword'

end TracialCreationFormulas
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixTower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_base _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_column _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_corner _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
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

variable [StarModule ℂ R]
  (htrace : ∀ a b, τ (a * b) = τ (b * a))
  (hdense : DenseRange V) (S : RealTracialSequence τ)

/-- Every scalar geometric field of the invariant-theory tower is now derived
from the actual tracial representation and raw matrix embeddings. The only
remaining sequence data is an algebraic real orthonormal sequence. -/
def tracialMatrixTowerOfEmbeddings
    (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop) :
    TracialMatrixTower (E := E) (F := centeredSubspace (V 1)) (A := A) where
  stage := embeddedMatrixStage τ V L hinner hleft M
  traceVector := V 1
  norm_traceVector := norm_tracialTraceVector τ V hinner
    (NestedTracialMatrices.trace_one τ V M)
  unit_realization s := by simp [embeddedMatrixStage]
  conjugation := centeredTracialConjugation τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M)
  conjugation_involutive := centeredTracialConjugation_involutive τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M)
  pairing := centeredTracialPairing τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M)
  pairing_conjugation := centeredTracialPairing_conjugation τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M)
  pairing_matrix s := centeredTracialPairing_matrix τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M) L
    (M.embedding s) hleft (M.trace_embedding s)
  inclusion s := M.inclusion 0 s (Nat.zero_le s)
  full_compatible s a := by simp only [embeddedMatrixStage_full, M.compatible]
  center_compatible s a := by simp only [embeddedMatrixStage_center, M.compatible]
  transition := M.inclusion
  full_transition s t h a := by simp only [embeddedMatrixStage_full, M.compatible]
  center_transition s t h a := by simp only [embeddedMatrixStage_center, M.compatible]
  full_mono := embeddedMatrixStage_full_mono τ V L hinner hleft M
  center_mono := embeddedMatrixStage_center_mono τ V L hinner hleft M
  full_dense := M.dense
  center_dense := embeddedMatrixStage_center_dense τ V L hinner hleft M
  size_tendsto := hsize
  realOrthonormal := realTracialHilbertSequence τ V S
  realOrthonormal_orthonormal := realTracialHilbertSequence_orthonormal τ V hinner S
  realOrthonormal_fixed := realTracialHilbertSequence_fixed τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M) S

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordLevelRepeatedOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Canonical multiplicity operators on repeated-letter words

Compression to one normalized repeated word defines the degree-wise operator.
The invariant-intertwiner classification proves that this same operator acts
on every repeated-letter word. Adjoint compatibility follows from the concrete
compression formula.
-/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)] [∀ n, CompleteSpace (G n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]
  (T : TracialMatrixTower (E := E) (F := F) (A := A))
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)

/-- The canonical degree-wise operator is a concrete compression to one unit
repeated word. Its independence of that word is proved below. -/
def wordLevelRepeatedOperator (Y : H →L[ℂ] H) (n : ℕ) : G n →L[ℂ] G n :=
  multiplicityCompression (U.block Y n n)
    (endpointWord T.traceVector (fun _ : Fin n => T.realOrthonormal 0))

variable (C : WordLevelMatrixActions T U) (Y : H →L[ℂ] H)
  (hleft : ∀ s a, Y.comp (C.leftAction s a) = (C.leftAction s a).comp Y)
  (hunitary : ∀ s u, Y.comp (C.unitaryAction s u) = (C.unitaryAction s u).comp Y)

/-- On a diagonal block the cross-multiplicity word covariance is exactly the
existing same-multiplicity covariance. -/
def WordLevelMatrixActions.diagonalCovariance (s n : ℕ) :
    MultiplicityMatrixCovariance (T.stage s) T.conjugation T.traceVector (U.block Y n n) where
  sourceAction := C.wordAction s n
  testAction := C.wordAction s n
  intertwine u := U.block_intertwines Y (C.unitaryAction s u) _ _ (hunitary s u)
    (C.unitary_inclusion s u n) (C.unitary_adjoint_inclusion s u n)
  source_covariance u v := C.source_word s n u (fun i => v (some (.inl i)))
  test_covariance u v := C.test_word s n u (v none) (fun i => v (some (.inr i)))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_CofinalMatrixTowers
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word degrees are fixed before the matrix stage is chosen. Cofinal tails
let each degree start in its own stable range; no single finite stage must
accommodate every number of tensor slots. -/

noncomputable section
namespace KadisonSimilarity

open Filter

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- Discarding finitely many matrix stages preserves every geometric field of
the tower and its dense union. -/
def TracialMatrixTower.tail
    (T : TracialMatrixTower (E := E) (F := F) (A := A)) (b : ℕ) :
    TracialMatrixTower (E := E) (F := F) (A := fun s => A (b + s)) where
  stage s := T.stage (b + s)
  traceVector := T.traceVector
  norm_traceVector := T.norm_traceVector
  unit_realization s := T.unit_realization (b + s)
  conjugation := T.conjugation
  conjugation_involutive := T.conjugation_involutive
  pairing := T.pairing
  pairing_conjugation := T.pairing_conjugation
  pairing_matrix s := T.pairing_matrix (b + s)
  inclusion s := T.transition b (b + s) (Nat.le_add_right b s)
  full_compatible s a := T.full_transition b (b + s) _ a
  center_compatible s a := T.center_transition b (b + s) _ a
  transition s t h := T.transition (b + s) (b + t) (Nat.add_le_add_left h b)
  full_transition s t h := T.full_transition (b + s) (b + t) _
  center_transition s t h := T.center_transition (b + s) (b + t) _
  full_mono := T.full_mono.comp (fun _ _ h => Nat.add_le_add_left h b)
  center_mono := T.center_mono.comp (fun _ _ h => Nat.add_le_add_left h b)
  full_dense := by
    change Dense (⋃ s, fullMatrixStage T.stage (b + s))
    rw [iUnion_nat_tail _ T.full_mono]
    exact T.full_dense
  center_dense := by
    change Dense (⋃ s, centeredMatrixStage T.stage (b + s))
    rw [iUnion_nat_tail _ T.center_mono]
    exact T.center_dense
  size_tendsto := T.size_tendsto.comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat b)
  realOrthonormal := T.realOrthonormal
  realOrthonormal_orthonormal := T.realOrthonormal_orthonormal
  realOrthonormal_fixed := T.realOrthonormal_fixed

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)] [∀ n, CompleteSpace (G n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Ambient actions restrict to the same cofinal sequence of matrix stages. -/
def WordLevelMatrixActions.tail
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)
    (C : WordLevelMatrixActions T U) (b : ℕ) : WordLevelMatrixActions (T.tail b) U where
  leftAction s := C.leftAction (b + s)
  unitaryAction s := C.unitaryAction (b + s)
  wordAction s := C.wordAction (b + s)
  left_inclusion s := C.left_inclusion (b + s)
  left_adjoint_inclusion s := C.left_adjoint_inclusion (b + s)
  unitary_inclusion s := C.unitary_inclusion (b + s)
  unitary_adjoint_inclusion s := C.unitary_adjoint_inclusion (b + s)
  source_word s := C.source_word (b + s)
  test_word s := C.test_word (b + s)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialEmbeddedWordStructure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ s, G.MatrixConjugationExtensionInput D (M.embedding s) A)

variable (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (I s) : ℝ)) Filter.atTop Filter.atTop)

/-- The finite matrix tower constructed from its actual tracial embeddings. -/
def baseTracialMatrixTower :=
  tracialMatrixTowerOfEmbeddings (G.baseGeometry D).trace (G.baseGeometry D).vector
    (G.baseGeometry D).left (G.baseGeometry D).inner_vector
    (G.baseGeometry D).left_vector M (G.baseGeometry D).tracial S hsize

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.tracialEmbeddedMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.tracialEmbeddedMultiplicityInnerFamily
variable (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hword : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)

variable (Y : H →L[ℂ] H)
  (hYL : ∀ s a, Y.comp (G.tracialMatrixLeftRepresentation D M s a) =
    (G.tracialMatrixLeftRepresentation D M s a).comp Y)
  (hYU : ∀ s u, Y.comp
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext s u : H →L[ℂ] H) =
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext s u : H →L[ℂ] H).comp Y)

/-- The canonical multiplicity compression for the actual matrix tower. -/
def tracialWordRepeatedOperator (n : ℕ) :=
  wordLevelRepeatedOperator (G.baseTracialMatrixTower D M S hsize) U Y n

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialGeneratedNormalClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Membership in a concrete finite von Neumann subalgebra is detected by
its closed space of trace vectors. This identifies the normal range of the
bounded tracially generated algebra. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H}

/-- Orthogonality of the conditional expectation detects membership from
the closed trace-vector space, without a uniform bound on approximants. -/
theorem mem_of_traceVector_mem_closure (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra)
    (hx : baseVector τ x ∈ closure (subalgebraTraceVectors τ N)) :
    (x : H →L[ℂ] H) ∈ N := by
  let E := conditionalExpectation τ hNM x
  let y := x - E
  have hE : (E : H →L[ℂ] H) ∈ N := conditionalExpectation_mem τ hNM x
  have ho : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) y :=
    conditionalExpectation_orthogonal τ hNM x
  have hz (z : M.toStarSubalgebra) (hz : (z : H →L[ℂ] H) ∈ N) :
      inner ℂ (baseVector τ y) (baseVector τ z) = 0 := by
    apply inner_eq_zero_symm.mp
    rw [baseVector_inner_trace]
    exact ho ⟨star z, by change star (z : H →L[ℂ] H) ∈ N; exact star_mem hz⟩
  have hclosed : IsClosed {v : H | inner ℂ (baseVector τ y) v = 0} :=
    isClosed_eq (innerSL ℂ (baseVector τ y)).continuous continuous_const
  have hsub : subalgebraTraceVectors τ N ⊆ {v : H | inner ℂ (baseVector τ y) v = 0} := by
    rintro _ ⟨z, hzN, rfl⟩
    exact hz z hzN
  have hx0 : inner ℂ (baseVector τ y) (baseVector τ x) = 0 :=
    closure_minimal hsub hclosed hx
  have hyv : baseVector τ y = baseVector τ x - baseVector τ E := map_sub (baseVector τ) x E
  have hy0 : inner ℂ (baseVector τ y) (baseVector τ y) = 0 := by
    calc
      _ = inner ℂ (baseVector τ y) (baseVector τ x - baseVector τ E) :=
        congrArg (fun z => inner ℂ (baseVector τ y) z) hyv
      _ = 0 := by rw [inner_sub_right, hx0, hz E hE, sub_self]
  have hy : y = 0 := baseVector_injective τ (by
    rw [inner_self_eq_zero.mp hy0, map_zero])
  have hxe : x = E := sub_eq_zero.mp hy
  rwa [hxe]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCreationDischarge
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

omit [IsClosed (A : Set P)] in
theorem freeHead_vacuum_orthogonal (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D) :
    (freeTracialHeadCoordinates G A D hτ hf.symm hgen).vacuumᗮ =
      (leadingWordSpace G A D false).toSubmodule := by
  rw [freeTracialHeadCoordinates_vacuum]
  exact centeredWordSpace_orthogonal G A D hτ hf.symm hgen true

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

instance generatedTestAlgebra_isClosed (D : StarSubalgebra ℂ P) (s : P) :
    IsClosed (G.generatedTestAlgebra D s : Set P) :=
  G.l2GeneratedAlgebra_isClosed _

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalFactorGeneration
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tracial generation by two factors implies generation of the concrete
von Neumann range by their norm-closed algebra. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.factorClosure_closed
theorem normal_range_eq_generated (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra)
    (hgen : G.FactorsTraciallyGenerate A D) :
    let S := (factorAlgebra A D).topologicalClosure
    representationVonNeumannAlgebra (G.left.comp S.subtype) = M := by
  let S := (factorAlgebra A D).topologicalClosure
  let : IsClosed (S : Set P) := factorClosure_closed A D
  let σ := G.left.comp S.subtype
  let N := representationVonNeumannAlgebra σ
  have hNM : N ≤ M := by
    intro T hT
    change T ∈ representationVonNeumannAlgebra σ at hT
    rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
    rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
    intro b hb
    apply hT b
    rintro _ ⟨a, rfl⟩
    apply hb
    change G.left (a : P) ∈ M.toStarSubalgebra
    rw [← hrange]
    exact ⟨(a : P), rfl⟩
  apply le_antisymm hNM
  intro T hT
  let τ := G.normalTracialRepresentation h1 hf M hrange
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  have hv (a : P) : Generator.Tracial.baseVector τ (e a) = G.vector a := by
    change G.left a (G.vector 1) = G.vector a
    rw [G.left_vector, mul_one]
  have hsub : Set.range (G.vector.comp (factorAlgebra A D).subtype.toLinearMap) ⊆
      subalgebraTraceVectors τ N := by
    rintro _ ⟨a, rfl⟩
    refine ⟨e (a : P), ?_, hv (a : P)⟩
    exact mem_representationVonNeumannAlgebra σ
      ⟨(a : P), (factorAlgebra A D).le_topologicalClosure a.property⟩
  exact mem_of_traceVector_mem_closure τ hNM ⟨T, hT⟩
    (closure_mono hsub (hgen (Generator.Tracial.baseVector τ ⟨T, hT⟩)))

/-- It suffices to check the two factors when conjugating the entire normal range. -/
theorem normal_range_map_mem (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra)
    (hgen : G.FactorsTraciallyGenerate A D)
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (hA : ∀ a : A, θ (G.left (a : P)) ∈ M)
    (hD : ∀ d : D, θ (G.left (d : P)) ∈ M) (x : P) :
    θ (G.left x) ∈ M := by
  let S := (factorAlgebra A D).topologicalClosure
  let : IsClosed (S : Set P) := factorClosure_closed A D
  let R := M.toStarSubalgebra.comap (θ.toStarAlgHom.comp G.left)
  have hR : IsClosed (R : Set P) :=
    (base_norm_closed M).preimage ((StarAlgEquiv.isometry θ).continuous.comp (map_continuous G.left))
  have hS : S ≤ R := by
    apply StarSubalgebra.topologicalClosure_minimal ?_ hR
    apply StarAlgebra.adjoin_le
    intro y hy
    rcases hy with hy | hy
    · exact hA ⟨y, hy⟩
    · exact hD ⟨y, hy⟩
  have hN := G.normal_range_eq_generated A D h1 hf M hrange hgen
  have hx : G.left x ∈ representationVonNeumannAlgebra (G.left.comp S.subtype) := by
    rw [hN]
    change G.left x ∈ M.toStarSubalgebra
    rw [← hrange]
    exact ⟨x, rfl⟩
  exact map_generated_mem (G.left.comp S.subtype) M θ
    (fun b => hS b.property) (G.left x) hx

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeMatrixExtension
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable (hfaithful : Function.Injective G.vector) (M : VonNeumannAlgebra H)
  (hrange : G.left.range = M.toStarSubalgebra)

include hfaithful hrange in
theorem freeMatrixExtensionRepresentation_mem (x : P) :
    G.freeMatrixExtensionRepresentation A D ι u h1 hf hgen x ∈ M := by
  apply G.normal_range_map_mem A D h1 hfaithful M hrange hgen (U).conjStarAlgEquiv
  · intro a
    rw [G.freeMatrixExtensionUnitary_base A D ι u h1 hf hgen]
    change G.left (a : P) ∈ M.toStarSubalgebra
    rw [← hrange]
    exact ⟨(a : P), rfl⟩
  · intro d
    rw [G.freeMatrixExtensionUnitary_other A D ι u h1 hf hgen]
    change G.left (matrixConjugateLetter D ι u d : P) ∈ M.toStarSubalgebra
    rw [← hrange]
    exact ⟨(matrixConjugateLetter D ι u d : P), rfl⟩

/-- The algebraic extension in the original algebra, using its faithful normal coordinates. -/
def freeMatrixExtensionHom : P →⋆ₐ[ℂ] P :=
  (equivalenceOfConcreteRange M G.left (G.left_injective hfaithful)
    hrange).symm.toStarAlgHom.comp
      ((G.freeMatrixExtensionRepresentation A D ι u h1 hf hgen).codRestrict
        M.toStarSubalgebra (G.freeMatrixExtensionRepresentation_mem A D ι u h1 hf hgen
          hfaithful M hrange))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCommutantTrace
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem commutant_vector_trace (Z W : H →L[ℂ] H)
    (hZ : ∀ a, Z.comp (G.left a) = (G.left a).comp Z)
    (hW : ∀ a, W.comp (G.left a) = (G.left a).comp W) :
    inner ℂ (G.vector 1) (Z (W (G.vector 1))) =
      inner ℂ (G.vector 1) (W (Z (G.vector 1))) := by
  calc
    _ = inner ℂ (star Z (G.vector 1)) (W (G.vector 1)) :=
      (ContinuousLinearMap.adjoint_inner_left Z (W (G.vector 1)) (G.vector 1)).symm
    _ = inner ℂ (G.conjugation (Z (G.vector 1))) (W (G.vector 1)) := by
      rw [G.commutant_conjugation_vector Z hZ]
    _ = inner ℂ (G.conjugation (W (G.vector 1))) (Z (G.vector 1)) :=
      G.inner_conjugation_swap _ _
    _ = inner ℂ (star W (G.vector 1)) (Z (G.vector 1)) := by
      rw [G.commutant_conjugation_vector W hW]
    _ = _ := ContinuousLinearMap.adjoint_inner_left W (Z (G.vector 1)) (G.vector 1)

theorem leftCommutant_commutes (Z : G.leftCommutant.toStarSubalgebra) (a : P) :
    (Z : H →L[ℂ] H).comp (G.left a) = (G.left a).comp (Z : H →L[ℂ] H) :=
  (G.mem_leftCommutant_iff (Z : H →L[ℂ] H)).mp Z.property a

/-- The left commutant carries the faithful normal vacuum trace. -/
def commutantTracialRepresentation (h1 : G.trace 1 = 1) :
    TracialRepresentation G.leftCommutant where
  vector := G.vector 1
  norm_vector := G.norm_identityVector h1
  cyclic Z W := G.commutant_vector_trace Z W
    (G.leftCommutant_commutes Z) (G.leftCommutant_commutes W)
  separating Z hz := by
    ext ξ
    change (Z : H →L[ℂ] H) ξ = 0
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    have h := congrArg (fun T : H →L[ℂ] H => T (G.vector 1)) (G.leftCommutant_commutes Z a)
    change (Z : H →L[ℂ] H) (G.left a (G.vector 1)) = G.left a ((Z : H →L[ℂ] H) (G.vector 1)) at h
    simpa only [G.left_vector, mul_one, hz, map_zero, zero_apply] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DyadicHaarUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Haar unitary in each corner of a diffuse finite tracial von Neumann
algebra, constructed as a norm limit of finite dyadic spectral sums. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge Filter
open scoped BigOperators Topology CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}
  (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

attribute [local instance] OAI.KadisonSimilarity.haarAlgebra_closed
def dyadicUnitaryApprox (p : AlgebraProjection M) (n : ℕ) :
    CStarCorner p.val p.property := dyadicCornerHom τ hdiff p n (dyadicPhase n)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_NormalSmallCorners
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct small diffuse corners in the original algebra through its
actual faithful normal range, then transport the entire frame back. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

local instance normalCorners_closed_rf23bfd_1 (N : VonNeumannAlgebra H) :
    IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed N
/-- The same full-matrix tower in the concrete normal coordinates. -/
def normalMatrixTower (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra) :
    let τ := G.normalTracialRepresentation h1 hf N hN
    NestedTracialMatrices (A := I) (concreteTraceLinear τ) (Generator.Tracial.baseVector τ) := by
  let τ := G.normalTracialRepresentation h1 hf N hN
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  have hv (a : P) : Generator.Tracial.baseVector τ (e a) = G.vector a := by
    change G.left a (G.vector 1) = G.vector a
    rw [G.left_vector, mul_one]
  refine {
    embedding := fun j => e.toStarAlgHom.comp (M.embedding j)
    trace_embedding := ?_
    inclusion := M.inclusion
    compatible := ?_
    dense := ?_
  }
  · intro j a
    change τ.trace (e (M.embedding j a)) = _
    rw [G.normalTracialRepresentation_trace]
    exact M.trace_embedding j a
  · intro j k h a
    change e (M.embedding k (M.inclusion j k h a)) = e (M.embedding j a)
    rw [M.compatible]
  · apply M.dense.mono
    intro ξ hξ
    obtain ⟨j, a, rfl⟩ := Set.mem_iUnion.mp hξ
    exact Set.mem_iUnion.mpr ⟨j, a, hv (M.embedding j a)⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteRealSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dyadic signs in a diffuse finite tracial von Neumann algebra form
the real tracial sequence required by the matrix-tower construction. The
underlying projections have compatible dyadic refinements and
orthogonality relations. -/

noncomputable section
namespace KadisonSimilarity

open UltrapowerBridge Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

variable (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

/-- Refining earlier signs to the next finite dyadic algebra proves the
off-diagonal moments; the diagonal follows from the square identity. -/
theorem concreteRademacher_inner (i j : ℕ) :
    concreteTraceLinear τ
      (star (concreteRademacher τ hdiff i) * concreteRademacher τ hdiff j) =
      if i = j then 1 else 0 := by
  rw [concreteRademacher_star]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, concreteRademacher_square, concreteTraceLinear_one]
  · rw [ite_eq_right hij]
    exact dyadicRademacher_trace_mul_of_ne τ hdiff ⟨1, IsStarProjection.one _⟩ hij

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FactorAssembly
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

attribute [instance] FiniteFactorModel.cstar FiniteFactorModel.order
  FiniteFactorModel.starOrder FiniteFactorModel.stageNonempty

/-- Precisely the factor alternatives needed downstream. The finite model
is supplied by Popa's increasing-matrix subfactor theorem and the listed
local inputs; the other two alternatives are projection/type classification. -/
def PublishedFactorCasesInput (P : VonNeumannAlgebra H) : Prop :=
  Nonempty (FiniteFactorModel P) ∨ HasInternalIsometryRows P ∨
    Nonempty (FiniteMatrixFactorModel P)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_ConditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform commutator estimates, hyperreflexivity, and similarity
from central factor models and derivation implementation. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A central direct-integral model with separable Hilbert fibers and the
finite or properly infinite factor structure. -/
structure PublishedSeparableModel (P : VonNeumannAlgebra H) where
  Ω : Type u
  [measurable : MeasurableSpace Ω]
  measure : Measure Ω
  K : Ω → Type u
  [normed : ∀ a, NormedAddCommGroup (K a)]
  [inner : ∀ a, InnerProductSpace ℂ (K a)]
  [complete : ∀ a, CompleteSpace (K a)]
  /-- The standard direct-integral decomposition of a separable space has
  separable Hilbert fibers (Blackadar, III.1.6.1–4). -/
  [separableFiber : ∀ a, TopologicalSpace.SeparableSpace (K a)]
  decomposition : CentralDecompositionData measure K P
  cases : ∀ᵐ a ∂measure, PublishedFactorCasesInput (decomposition.algebra a)

attribute [instance] PublishedSeparableModel.measurable PublishedSeparableModel.normed
  PublishedSeparableModel.inner PublishedSeparableModel.complete
  PublishedSeparableModel.separableFiber

/-- Existence of central factor models for separable represented algebras. -/
structure PublishedUniformInputs : Prop where
  separable : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K] (P : VonNeumannAlgebra K),
    Nonempty (PublishedSeparableModel P)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SeparableRepresentationTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common contraction tests for representations

A norm-dense sequence in the unit ball of a separable C-star algebra works in
every representation. The proved finite-vector Kaplansky theorem extends its
weak-operator closure to the unit ball of the represented bicommutant. This
does not require normality of a representation or of a pointwise fiber map.
-/

noncomputable section

namespace KadisonSimilarity

open ContinuousLinearMapWOT Filter
open scoped Topology CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]

omit [TopologicalSpace.SeparableSpace A] in
/-- The image of a norm-dense source unit-ball sequence is weakly dense in
every represented bicommutant's unit ball. -/
theorem represented_contraction_mem_test_closure
    (test : ℕ → A)
    (hdense : ∀ a : A, ‖a‖ ≤ 1 → a ∈ closure (Set.range test))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) (hn : ‖T‖ ≤ 1) :
    ofCLM T ∈ closure (Set.range fun n => ofCLM (σ (test n))) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hsource := mem_weak_closure_of_finite_strong_approximation
    {R | ∃ a : A, ‖a‖ ≤ 1 ∧ σ a = R} T (by
      intro s ε hε
      obtain ⟨a, ha, happrox⟩ := kaplansky_contraction_approximation σ T hT hn s ε hε
      exact ⟨σ a, ⟨a, ha, rfl⟩, happrox⟩)
  apply closure_minimal _ isClosed_closure hsource
  rintro _ ⟨R, ⟨a, ha, rfl⟩, rfl⟩
  exact map_mem_closure (f := fun a => ofCLM (σ a))
    (continuous_ofCLM.comp (map_continuous σ)) (hdense a ha)
    (by rintro _ ⟨n, rfl⟩; exact ⟨n, rfl⟩)

/-- In particular the same source tests work on every Hilbert space of a
family, as required for a field of representations. -/
theorem exists_common_fiber_contraction_tests
    {Ω : Type*} (K : Ω → Type*) [∀ a, NormedAddCommGroup (K a)]
    [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]
    (σ : ∀ a, A →⋆ₐ[ℂ] (K a →L[ℂ] K a)) :
    ∃ test : ℕ → A, (∀ n, ‖test n‖ ≤ 1) ∧
      ∀ a (T : K a →L[ℂ] K a), T ∈ representationVonNeumannAlgebra (σ a) → ‖T‖ ≤ 1 →
        ofCLM T ∈ closure (Set.range fun n => ofCLM (σ a (test n))) := by
  obtain ⟨test, hnorm, hdense⟩ := exists_norm_dense_contraction_tests (A := A)
  exact ⟨test, hnorm, fun a T hT hn =>
    represented_contraction_mem_test_closure test hdense (σ a) T hT hn⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CentralDecompositionTests
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The countable tests in a central decomposition

Starting with representations of one norm-separable C-star subalgebra, their
bicommutant-generation property, and almost-everywhere agreement with the
ambient fiber representatives, the contraction tests are constructed. Only
countably many agreements are used; pointwise fiber evaluation is not
assumed to be a normal map on the von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMapWOT MeasureTheory Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

/-- Construct exactly the `test`, `test_norm`, and `test_dense` fields used
by `CentralDecompositionData`, from a separable source and its fiber
representations. -/
theorem exists_central_decomposition_tests
    (P : VonNeumannAlgebra H)
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (B : Set (H →L[ℂ] H))]
    [TopologicalSpace.SeparableSpace B] (hB : B ≤ P.toStarSubalgebra)
    (algebra : ∀ a, VonNeumannAlgebra (K a))
    (fiber : (vonNeumannCenter P).commutant.toStarSubalgebra → ∀ a, K a →L[ℂ] K a)
    (σ : ∀ a, B →⋆ₐ[ℂ] (K a →L[ℂ] K a))
    (hagrees : ∀ b : B, ∀ᵐ a ∂μ,
      fiber (centerCommutantInclusion P ⟨b.val, hB b.property⟩) a = σ a b)
    (hgenerates : ∀ᵐ a ∂μ, algebra a = representationVonNeumannAlgebra (σ a)) :
    ∃ test : ℕ → P.toStarSubalgebra,
      (∀ n, ‖(test n : H →L[ℂ] H)‖ ≤ 1) ∧
      ∀ᵐ a ∂μ, ∀ T : K a →L[ℂ] K a, T ∈ algebra a → ‖T‖ ≤ 1 →
        ofCLM T ∈ closure (Set.range fun n =>
          ofCLM (fiber (centerCommutantInclusion P (test n)) a)) := by
  obtain ⟨sourceTest, hnorm, hdense⟩ := exists_common_fiber_contraction_tests K σ
  let test : ℕ → P.toStarSubalgebra :=
    fun n => ⟨(sourceTest n).val, hB (sourceTest n).property⟩
  refine ⟨test, hnorm, ?_⟩
  have hagrees_all : ∀ᵐ a ∂μ, ∀ n,
      fiber (centerCommutantInclusion P (test n)) a = σ a (sourceTest n) :=
    eventually_countable_forall.mpr (fun n => hagrees (sourceTest n))
  filter_upwards [hgenerates, hagrees_all] with a hgen ha
  intro T hT hn
  have heq : (fun n => ofCLM (fiber (centerCommutantInclusion P (test n)) a)) =
      (fun n => ofCLM (σ a (sourceTest n))) := by
    funext n
    rw [ha n]
  rw [heq]
  rw [hgen] at hT
  exact hdense a T hT hn

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_KaplanskyStrongSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sequential Kaplansky approximation on a separable Hilbert space

Finite-vector Kaplansky approximation applied to increasing finite sets of
dense vectors gives an actual strongly convergent sequence. Every source
term satisfies the exact norm bound of the target operator.
-/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology CStarAlgebra

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Every member of a represented bicommutant is a strong sequential limit
of source elements, with the exact source norm bound preserved. -/
theorem kaplansky_strong_sequence
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) :
    ∃ a : ℕ → A, (∀ n, ‖a n‖ ≤ ‖T‖) ∧
      ∀ x : H, Tendsto (fun n => σ (a n) x) atTop (𝓝 (T x)) := by
  classical
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let d := TopologicalSpace.denseSeq H
  have hex (n : ℕ) : ∃ a : A, ‖a‖ ≤ ‖T‖ ∧
      ∀ x ∈ (Finset.range (n + 1)).image d, ‖σ a x - T x‖ < 1 / (n + 1 : ℝ) :=
    kaplansky_finite_approximation σ T hT _ _ (by positivity)
  choose a hnorm hclose using hex
  refine ⟨a, hnorm, ?_⟩
  apply strong_tendsto_of_bounded_dense_columns (fun n => σ (a n)) T ‖T‖
    (fun n => (NonUnitalStarAlgHom.norm_apply_le σ (a n)).trans (hnorm n))
  intro j
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) _
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop j] with n hn
  apply (hclose n (d j) _).le
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_IsometricFieldClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Membership in the original represented von Neumann algebra passes to
the fiber algebra through the actual isometric L² embedding. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H F Ω : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Only the source algebra's actual field action and membership are needed;
the fiber fields need not form a simultaneous representation on null sets. -/
theorem ae_field_mem_of_isometric_representation_closure
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (P : Ω → VonNeumannAlgebra F) (R : A → Ω → F →L[ℂ] F)
    (hR : ∀ b (f : Lp F 2 μ), ∀ᵐ x ∂μ,
      isometricExtension J (σ b) f x = R b x (f x))
    (hmem : ∀ b, ∀ᵐ x ∂μ, R b x ∈ P x)
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (Q : Ω → F →L[ℂ] F)
    (hQ : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J T f x = Q x (f x)) :
    ∀ᵐ x ∂μ, Q x ∈ P x := by
  obtain ⟨b, hbound, hstrong⟩ := kaplansky_strong_sequence σ T hT
  apply ae_field_mem_of_norm_bounded_strong_approximation μ P
    (fun n => isometricExtension J (σ (b n))) (isometricExtension J T)
    (fun n => R (b n)) Q (fun n => hR (b n)) hQ
    (isometricExtension_strong_tendsto J (fun n => σ (b n)) T hstrong)
    ‖T‖ (norm_nonneg T) ?_ (fun n => hmem (b n))
  intro n
  rw [isometricExtension_norm]
  exact (NonUnitalStarAlgHom.norm_apply_le σ (b n)).trans (hbound n)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProjectionFieldClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closure in the genuine projection-fiber algebras

Strong Kaplansky approximation first proves membership in the raw
unitized fiber algebra. Compression to the old-unit range then gives
membership in the genuine representation of the original algebra.
No representation on the null complement is needed.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

variable {B H F Ω : Type*} [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- The conull raw unitized fiber representations contain the field of
every operator in the original represented bicommutant. -/
theorem ae_unitization_field_mem_of_isometric_closure
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ b : B, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (σ b) f x = ρ x (Unitization.inr b) (f x))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (Q : s → F →L[ℂ] F)
    (hQ : ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J T f x = Q x (f x)) :
    ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
      Q x ∈ representationVonNeumannAlgebra (ρ x) := by
  classical
  let P : Ω → VonNeumannAlgebra F := fun x =>
    if hx : x ∈ s then representationVonNeumannAlgebra (ρ ⟨x, hx⟩)
    else starSubalgebraCommutant (⊤ : StarSubalgebra ℂ (F →L[ℂ] F))
  let R : B → Ω → F →L[ℂ] F := fun b =>
    zeroExtendOperatorField s (fun x => ρ x (Unitization.inr b))
  have hR : ∀ b (f : Lp F 2 μ), ∀ᵐ x ∂μ,
      isometricExtension J (σ b) f x = R b x (f x) := fun b =>
    zeroExtendOperatorField_action μ s hs hnull _ _ (hρ b)
  have hmem : ∀ b, ∀ᵐ x ∂μ, R b x ∈ P x := by
    intro b
    apply Filter.Eventually.of_forall
    apply zeroExtendOperatorField_mem s P
    intro x
    simpa only [P, dite_eq_left x.property] using
      mem_representationVonNeumannAlgebra (ρ x) (Unitization.inr b)
  have hQ' : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J T f x = zeroExtendOperatorField s Q x (f x) :=
    zeroExtendOperatorField_action μ s hs hnull _ _ hQ
  have hm := ae_field_mem_of_isometric_representation_closure μ J σ P R hR hmem
    T hT (zeroExtendOperatorField s Q) hQ'
  have hmOn := (ae_restrict_iff_subtype hs).mp (ae_restrict_of_ae hm)
  filter_upwards [hmOn] with x hx
  simpa only [zeroExtendOperatorField, dite_eq_left x.property, P] using hx

/-- Passing to the old-unit range yields membership in the actual
variable-fiber representation of the original algebra. -/
theorem ae_projection_field_mem_of_isometric_closure
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ b : B, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (σ b) f x = ρ x (Unitization.inr b) (f x))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (Q : s → F →L[ℂ] F)
    (hQ : ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J T f x = Q x (f x)) :
    ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
      projectionFiberCompression (unitizationProjection (ρ x))
        (unitizationProjection_isStarProjection (ρ x)) (Q x) ∈
          representationVonNeumannAlgebra (unitizationRangeRepresentation (ρ x)) := by
  filter_upwards [ae_unitization_field_mem_of_isometric_closure
    μ s hs hnull J σ ρ hρ T hT Q hQ] with x hx
  exact unitizationFiberCompression_mem (ρ x) (Q x) hx

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

variable (μ : Measure Ω) [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace F]

variable [TopologicalSpace.SeparableSpace H]

/-- A represented bicommutant member has its actual global field in the
bicommutant of the old-unit range representation almost everywhere.
This transports the conull membership statement without choosing arbitrary
representations on the null complement. -/
theorem ae_global_projection_mem_of_isometric_closure
    {A : Type u} [CStarAlgebra A]
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : ∀ _x : s, Unitization ℂ A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ a : A, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (σ a) f x = ρ x (Unitization.inr a) (f x))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (R : Ω → F →L[ℂ] F)
    (hR : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J T f x = R x (f x)) :
    ∀ᵐ x ∂μ, projectionFiberCompression
      (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
      (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x))
      (R x) ∈ representationVonNeumannAlgebra
        (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)) := by
  have hR' : ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J T f x = R x (f x) :=
    fun f => (ae_restrict_iff_subtype hs).mp (ae_restrict_of_ae (hR f))
  have hm := ae_projection_field_mem_of_isometric_closure μ s hs hnull J σ ρ hρ T hT
    (fun x => R x) hR'
  have hm' := hm.mono fun x hx => conull_projection_membership s ρ x (R x) hx
  have hr := (ae_restrict_iff_subtype (μ := μ)
    (p := fun x => projectionFiberCompression
      (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
      (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x))
      (R x) ∈ representationVonNeumannAlgebra
        (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x))) hs).mpr hm'
  have hs' : ∀ᵐ x ∂μ, x ∈ s := mem_ae_iff.mpr hnull
  filter_upwards [hs', ae_imp_of_ae_restrict hr] with x hx h
  exact h hx

/-- Construct all the direct-integral data needed for the separable
commutator estimate, before the separate factor-fiber theorem. The only
geometric inputs are genuine conull representations and actual L² action
identities for the isometric extension. -/
def projectionCentralData
    (P : VonNeumannAlgebra H)
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (B : Set (H →L[ℂ] H))]
    [TopologicalSpace.SeparableSpace B]
    (hB : B ≤ P.toStarSubalgebra)
    (hgen : representationVonNeumannAlgebra B.subtype = P)
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (J : H →ₗᵢ[ℂ] Lp F 2 μ)
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ b : B, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (b : H →L[ℂ] H) f x = ρ x (Unitization.inr b) (f x))
    (R : (vonNeumannCenter P).commutant.toStarSubalgebra → Ω → F →L[ℂ] F)
    (hR : ∀ T : (vonNeumannCenter P).commutant.toStarSubalgebra,
      ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
        isometricExtension J (T : H →L[ℂ] H) f x = R T x (f x)) :
    CentralDecompositionData μ (conullProjectionFiber s ρ) P := by
  classical
  let τ := zeroExtendNonunitalRepresentation s ρ
  let p : Ω → F →L[ℂ] F := fun x => nonunitalUnitProjection (τ x)
  let hp : ∀ x, IsStarProjection (p x) := fun x => nonunitalUnitProjection_isStarProjection (τ x)
  let σf : ∀ x, B →⋆ₐ[ℂ] (conullProjectionFiber s ρ x →L[ℂ] conullProjectionFiber s ρ x) :=
    fun x => nonunitalRangeRepresentation (τ x)
  let algebra : ∀ x, VonNeumannAlgebra (conullProjectionFiber s ρ x) :=
    fun x => representationVonNeumannAlgebra (σf x)
  let fiber : (vonNeumannCenter P).commutant.toStarSubalgebra →
      ∀ x, conullProjectionFiber s ρ x →L[ℂ] conullProjectionFiber s ρ x :=
    fun T x => projectionFiberCompression (p x) (hp x) (R T x)
  have hτ (b : B) : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J (b : H →L[ℂ] H) f x = τ x b (f x) := by
    intro f
    simpa only [τ, zeroExtendNonunitalRepresentation_apply] using
      zeroExtendOperatorField_action μ s hs hnull _ _ (hρ b) f
  have hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J 1 f x = p x (f x) := by
    simpa only [OneMemClass.coe_one, p, nonunitalUnitProjection] using hτ (1 : B)
  have hsub : ∀ T U, ∀ᵐ x ∂μ, fiber (T - U) x = fiber T x - fiber U x := by
    intro T U
    filter_upwards [isometric_raw_field_sub μ J _ R hR T U] with x hx
    dsimp only [fiber]
    rw [hx, projectionFiberCompression_sub]
  have hmul : ∀ T U, ∀ᵐ x ∂μ, fiber (T * U) x = fiber T x * fiber U x := by
    intro T U
    filter_upwards [isometric_raw_field_mul μ J _ R hR T U,
      ae_isometric_field_left_support μ J p hP U (R U) (hR U)] with x hx hu
    dsimp only [fiber]
    rw [hx, projectionFiberCompression_mul (p x) (hp x) (R T x) (R U x) hu]
  have hmem : ∀ T : P.toStarSubalgebra, ∀ᵐ x ∂μ,
      fiber (centerCommutantInclusion P T) x ∈ algebra x := by
    intro T
    have hTin : (T : H →L[ℂ] H) ∈ representationVonNeumannAlgebra B.subtype := by
      rw [hgen]
      exact T.property
    exact ae_global_projection_mem_of_isometric_closure μ s hs hnull J B.subtype ρ hρ
      T hTin (R (centerCommutantInclusion P T)) (hR (centerCommutantInclusion P T))
  have hnorm : ∀ (T : (vonNeumannCenter P).commutant.toStarSubalgebra) c, 0 ≤ c →
      (‖(T : H →L[ℂ] H)‖ ≤ c ↔ ∀ᵐ x ∂μ, ‖fiber T x‖ ≤ c) := by
    intro T c hc
    exact norm_le_iff_compressed_field μ J p hp hP T (R T) (hR T) c hc
  have hmatrix : ∀ n (X : Matrix (Fin n) (Fin n)
      (vonNeumannCenter P).commutant.toStarSubalgebra) c, 0 ≤ c →
      (‖matrixOperator (fun i j => (X i j : H →L[ℂ] H))‖ ≤ c ↔
        ∀ᵐ x ∂μ, ‖matrixOperator (fun i j => fiber (X i j) x)‖ ≤ c) := by
    intro n X c hc
    exact matrix_norm_le_iff_compressed_field μ J p hp hP
      (fun i j => (X i j : H →L[ℂ] H)) (fun i j => R (X i j))
      (fun i j => hR (X i j)) c hc
  have hagrees : ∀ b : B, ∀ᵐ x ∂μ,
      fiber (centerCommutantInclusion P ⟨b.val, hB b.property⟩) x = σf x b := by
    intro b
    have heq := fields_eq_of_same_action μ (isometricExtension J (b : H →L[ℂ] H))
      (R (centerCommutantInclusion P ⟨b.val, hB b.property⟩)) (fun x => τ x b)
      (hR (centerCommutantInclusion P ⟨b.val, hB b.property⟩)) (hτ b)
    filter_upwards [heq] with x hx
    dsimp only [fiber, σf]
    rw [hx]
    exact (projectionFiberAction_eq_compression _ _ _
      (nonunitalUnitProjection_commutes (τ x) b)).symm
  have htests := exists_central_decomposition_tests μ
    (conullProjectionFiber s ρ) P B hB algebra fiber σf hagrees
    (Filter.Eventually.of_forall fun _ => rfl)
  let test := Classical.choose htests
  have htest := (Classical.choose_spec htests).1
  have hdense := (Classical.choose_spec htests).2
  exact {
    algebra := algebra
    fiber := fiber
    map_sub := hsub
    map_mul := hmul
    mem := hmem
    norm_le_iff := hnorm
    matrix_norm_le_iff := hmatrix
    test := test
    test_norm := htest
    test_dense := hdense }

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

/-- Central decomposition with all scalar/matrix norms and countable
contraction tests derived from the common spectral embedding. -/
def commonProjectionCentralData (P : VonNeumannAlgebra H)
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (B : Set (H →L[ℂ] H))]
    [TopologicalSpace.SeparableSpace B]
    (hB : B ≤ P.toStarSubalgebra)
    (hBgen : representationVonNeumannAlgebra B.subtype = P)
    (hcentral : starSubalgebraCommutant π.range = (vonNeumannCenter P).commutant)
    (s : Set (WeakDual.characterSpace ℂ A)) (hs : MeasurableSet s)
    (hnull : (cyclicCommonBaseMeasure π D) sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ]
      (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
    (hρ : ∀ b : B, ∀ f : CommonCyclicHilbert π D,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
        (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) (b : H →L[ℂ] H) f x =
          ρ x (Unitization.inr b) (f x)) :
    CentralDecompositionData (cyclicCommonBaseMeasure π D) (conullProjectionFiber s ρ) P :=
  projectionCentralData (cyclicCommonBaseMeasure π D) P B hB hBgen s hs hnull
    (cyclicCommonEmbedding π D) ρ hρ (commonCentralField π D P hcentral)
    (commonCentralField_action π D P hcentral)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixStageGrowth
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

section Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N : VonNeumannAlgebra H} [Nontrivial N.toStarSubalgebra]

theorem generated_ne_stage_of_diffuse (F : ℕ → FiniteMatrixStage N)
    (hdiff : ∀ p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra,
      IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q) (n : ℕ) :
    FiniteMatrixStage.generated F ≠ (F n).units.concreteAlgebra := by
  intro heq
  let E := F n
  let o : Fin E.size := ⟨0, E.positive⟩
  have hpN : IsStarProjection (E.units.entry o o) := by
    constructor
    · change E.units.entry o o * E.units.entry o o = E.units.entry o o
      simpa only [ite_true] using E.units.mul_entry o o o o
    · exact E.units.star_entry o o
  let p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra :=
    ⟨(E.units.entry o o).val, FiniteMatrixStage.stage_le_generated F n
      ((E.units.mem_concreteAlgebra _).mpr (E.units.entry_mem o o))⟩
  let i : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra →⋆ₐ[ℂ]
      N.toStarSubalgebra := StarSubalgebra.inclusion (FiniteMatrixStage.generated_le F)
  have hinj : Function.Injective i :=
    StarSubalgebra.inclusion_injective (FiniteMatrixStage.generated_le F)
  have hip : i p = E.units.entry o o := Subtype.ext rfl
  have hp : IsStarProjection p := by
    constructor
    · change p * p = p
      apply Subtype.ext
      exact congrArg (fun a : N.toStarSubalgebra => (a : H →L[ℂ] H))
        hpN.isIdempotentElem.eq
    · change star p = p
      apply Subtype.ext
      exact congrArg (fun a : N.toStarSubalgebra => (a : H →L[ℂ] H))
        hpN.isSelfAdjoint.star_eq
  have hp0 : p ≠ 0 := by
    intro hz
    apply E.units.diagonal_ne_zero o
    rw [← hip, hz, map_zero i]
  obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := hdiff p hp hp0
  have hmem : i q ∈ E.units.algebra := by
    apply (E.units.mem_concreteAlgebra _).mp
    change (q : H →L[ℂ] H) ∈ (F n).units.concreteAlgebra
    rw [← heq]
    exact q.property
  have hl : E.units.entry o o * i q = i q := by
    rw [← hip, ← map_mul i p q, hpq]
  have hr : i q * E.units.entry o o = i q := by
    rw [← hip, ← map_mul i q p, hqp']
  rcases matrix_diagonal_no_proper_subprojection E.units o (i q) hmem (hq.map i) hl hr
      with hz | he
  · apply hq0
    apply hinj
    simpa only [map_zero i] using hz
  · exact hqp (hinj (he.trans hip.symm))

end Concrete

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GeneratedFiniteFactorModel
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed matrix subfactor in a normal trace representation
supplies the finite-factor model in the original representation. Only the
prescribed ultrapower free position remains a local input. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {P : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ) (υ : TracialRepresentation N)
  (e : P.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
  (he : ∀ a, υ.trace (e a) = τ a) (F : ℕ → FiniteMatrixStage N)

variable [Nontrivial N.toStarSubalgebra]
  (h1 : τ 1 = 1)
  (htr : ∀ a b, τ (a * b) = τ (b * a))
  (hf : ∀ a, τ (star a * a) = 0 → a = 0)
  (hnormal : HasNormalGNS τ)
  (hmono : Monotone (fun n => (F n).units.concreteAlgebra))
  (hdiff : ∀ p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra,
    IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
      p * q = q ∧ q * p = q)
  (ω : Ultrafilter ℕ)
  (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

local instance generatedStageNonempty (n : ℕ) : Nonempty (Fin (F n).size) :=
  ⟨⟨0, (F n).positive⟩⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceCornerQuantization
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

local instance sourceCornerAmbientClosed_rf23bfd_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
attribute [local instance] OAI.KadisonSimilarity.sourceCornerSourceClosed
/-- A nonzero projection in the source corner can be split there. -/
theorem source_corner_diffuse
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) :
    ∀ q : Corner p hp, IsStarProjection q → q ≠ 0 →
      ∃ r, IsStarProjection r ∧ r ≠ 0 ∧ r ≠ q ∧ q * r = r ∧ r * q = r := by
  have hdN : HochschildDiffuse.NoMinimalProjections N.toStarSubalgebra := by
    intro q hq hq0
    obtain ⟨r, hr, hr0, hrq, hqr, _⟩ := hdiff q hq hq0
    exact ⟨r, hr, (hr.le_iff_mul_eq_right hq).mpr hqr, hr0, hrq⟩
  intro q hq hq0
  obtain ⟨r, hr, hrq, hr0, hrne⟩ := corner_no_minimal p hp hdN q hq hq0
  exact ⟨r, hr, hr0, hrne, (hr.le_iff_mul_eq_right hq).mp hrq,
    (hr.le_iff_mul_eq_left hq).mp hrq⟩

end KadisonSimilarity

end

end OAI
end


