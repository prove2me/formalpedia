-- Prove2me | Definitions.Def_OAIQ075A024
-- name    : OAIQ075A024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:23:23.253516+00:00
-- url     : https://prove2.me/theorems/9b1e88d6-1c1e-46ad-a73a-2855e5d3fb91
-- title:
--   Definitions bundle OAIQ075A024 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 128 declarations of OpenAI's Lean: 53 definitions, 5 inductive types or structures, 3 instances and 67 theorems. The definitions and types are `OAI.KadisonSimilarity.MatrixUnitColumnFamily.map`, `OAI.KadisonSimilarity.MultiplicityMatrixCovariance`, `OAI.KadisonSimilarity.ReducedWordCompressionModel`, `OAI.KadisonSimilarity.ReducedWordCreationModel`, `OAI.KadisonSimilarity.RicardXuCompressionInput`, `OAI.KadisonSimilarity.RicardXuCreationInput`, `OAI.KadisonSimilarity.RicardXuWordDecompositionInput`, `OAI.KadisonSimilarity.SmallFreeCornerData.transport`, `OAI.KadisonSimilarity.TracialCornerGeometry.ambientCornerColumns`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseAInner`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseANormed`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseDInner`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseDNormed`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseMultiplicityNormedFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryRepeatedInclusion`, `OAI.KadisonSimilarity.TracialCornerGeometry.centeredAInner`, `OAI.KadisonSimilarity.TracialCornerGeometry.centeredANormed`, `OAI.KadisonSimilarity.TracialCornerGeometry.centeredBaseAlgebraVector`, `OAI.KadisonSimilarity.TracialCornerGeometry.centeredCornerProjection`, `OAI.KadisonSimilarity.TracialCornerGeometry.centeredDInner`, `OAI.KadisonSimilarity.TracialCornerGeometry.centeredDNormed`, `OAI.KadisonSimilarity.TracialCornerGeometry.cornerGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.cornerMatrixEntry`, `OAI.KadisonSimilarity.TracialCornerGeometry.cornerRestriction`, `OAI.KadisonSimilarity.TracialCornerGeometry.dihedralGroupWordVectors`, `OAI.KadisonSimilarity.TracialCornerGeometry.faithfulRightAction`, `OAI.KadisonSimilarity.TracialCornerGeometry.fullColumnCoordinates`, `OAI.KadisonSimilarity.TracialCornerGeometry.matrixUnitaryMeasurableSpace`, `OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.projectionEndpoint`, `OAI.KadisonSimilarity.TracialCornerGeometry.repeatedDihedralInclusion`, `OAI.KadisonSimilarity.TracialCornerGeometry.supportedCornerColumns`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralColumns`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixHaarProbability`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialWordHeadAction`, `OAI.KadisonSimilarity.TracialHeadCoordinates`, `OAI.KadisonSimilarity.TracialHeadCoordinates.vacuum`, `OAI.KadisonSimilarity.TracialMatrixUnitColumnFamily.map`, `OAI.KadisonSimilarity.TracialRepeatedWordRealization` and 18 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonSimilarity_Derivation_TracialCornerCyclicity`, `KadisonSimilarity_FreeProduct_ActualArcCompression`, `KadisonSimilarity_FreeProduct_BaseSymmetry`, `KadisonSimilarity_FreeProduct_DihedralPositiveDensity`, `KadisonSimilarity_FreeProduct_FreeCompressionGeometry`, `KadisonSimilarity_FreeProduct_HaarCornerLetters`, `KadisonSimilarity_FreeProduct_PublishedWordCreation`, `KadisonSimilarity_FreeProduct_ReducedWordModel`, `KadisonSimilarity_FreeProduct_SmallFreeCornerTransport`, `KadisonSimilarity_FreeProduct_TracialDihedralColumns`, `KadisonSimilarity_FreeProduct_TracialFreeCornerModel`, `KadisonSimilarity_FreeProduct_TracialRepeatedWords`, `KadisonSimilarity_FreeProduct_TracialWordActions`, `KadisonSimilarity_FreeProduct_TracialWordBase`, `KadisonSimilarity_FreeProduct_TracialWordDensity`, `KadisonSimilarity_FreeProduct_WordPrefixRealization`, `KadisonSimilarity_Representation_CenteredBaseDensity`, `KadisonSimilarity_Representation_SquareArrayPadding`, `KadisonSimilarity_Tensor_EndpointClassification`, `KadisonSimilarity_Tensor_MultiplicityClassification`, `KadisonSimilarity_Tensor_TensorHeadSlices`, `KadisonSimilarity_Tracial_ConcreteProjectionComparison`, `KadisonSimilarity_Tracial_CornerTraceScaling`, `KadisonSimilarity_Tracial_DiffuseProjectionStructure`, `KadisonSimilarity_Tracial_IntegerMomentScaling`, `KadisonSimilarity_Tracial_TracialBaseGeometry`, `KadisonSimilarity_Tracial_TracialCornerEstimate`, `KadisonSimilarity_Tracial_TracialCornerHilbert`, `KadisonSimilarity_Tracial_TracialCornerRepresentations`, `KadisonSimilarity_Tracial_TracialCreationCoordinates`, `KadisonSimilarity_Tracial_TracialGeneratedNormalClosure`, `KadisonSimilarity_Tracial_TracialHeadCoordinates`, `KadisonSimilarity_Tracial_TracialMatrixCenter`, `KadisonSimilarity_Tracial_TracialMatrixColumns`, `KadisonSimilarity_Tracial_TracialMatrixCovariance`, `KadisonSimilarity_Tracial_TracialMatrixRealization`, `KadisonSimilarity_Tracial_TracialMatrixSymmetrization`, `KadisonSimilarity_Tracial_TracialMatrixTower`, `KadisonSimilarity_Tracial_TracialMomentContinuity`, `KadisonSimilarity_Tracial_TracialSupportedColumns`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A013`, `OAIQ075A014`, `OAIQ075A015`, `OAIQ075A016` and `OAIQ075A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A028` and `OAIQ075A029`; the statements `OAI_KadisonSimilarity_TracialCornerGeometry_commutator_bound_of_actual_dihedral_compression` and `OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs`; the proofs of `OAI_KadisonSimilarity_TracialCornerGeometry_commutator_bound_of_actual_dihedral_compression`, `OAI_KadisonSimilarity_TracialCornerGeometry_rightSupportInput_of_normal_range` and `OAI_KadisonSimilarity_projection_tendsto_zero_of_normal_geometry`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A013
import Definitions.Def_OAIQ075A014
import Definitions.Def_OAIQ075A015
import Definitions.Def_OAIQ075A016
import Definitions.Def_OAIQ075A017

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixRealization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix stages inside an actual tracial Hilbert representation

A trace-preserving matrix embedding supplies the normalized Hilbert--Schmidt
geometry, the corner left action, and the centered projection used by the
invariant-intertwiner argument. No invariant-theory conclusion is an input.
-/

noncomputable section
namespace KadisonSimilarity

variable {R E α : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [Fintype α] [DecidableEq α]

/-- The stage centering acts as the identity on trace-zero matrices after
including its value in the full Hilbert space. -/
theorem coe_tracialMatrixStage_center_of_trace_zero
    (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] R) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a)
    (a : Matrix α α ℂ) (ha : Matrix.trace a = 0) :
    ((tracialMatrixStage τ V L ι hinner hleft htrace).center a : E) = V (ι a) := by
  apply coe_tracialCenter_of_trace_zero τ V hinner
  change τ (ι a) = 0
  rw [htrace, ha, mul_zero]

section Conjugation

variable [StarModule ℂ R]

variable (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a))
  (hdense : DenseRange V)

/-- The dense extension remains an involution. -/
theorem tracialConjugation_involutive :
    Function.Involutive (tracialConjugation τ V hinner htrace hdense) := by
  intro x
  refine hdense.induction_on x (isClosed_eq (by fun_prop) continuous_id) ?_
  intro a
  simp

theorem centeredTracialConjugation_involutive :
    Function.Involutive (centeredTracialConjugation τ V hinner htrace hdense) := by
  intro x
  apply Subtype.ext
  exact tracialConjugation_involutive τ V hinner htrace hdense x

/-- The continuous bilinear pairing used for matrix trace contractions is built
from the actual centered tracial conjugation. -/
def centeredTracialPairing :
    centeredSubspace (V 1) →L[ℂ] centeredSubspace (V 1) →L[ℂ] ℂ :=
  (innerSL ℂ).comp
    (centeredTracialConjugation τ V hinner htrace hdense).toContinuousLinearMap

theorem centeredTracialPairing_conjugation (x y : centeredSubspace (V 1)) :
    centeredTracialPairing τ V hinner htrace hdense x
      (centeredTracialConjugation τ V hinner htrace hdense y) = inner ℂ y x := by
  exact inner_tracialConjugation τ V hinner htrace hdense x y

/-- On centered matrix vectors the pairing is exactly the normalized matrix
trace, without an assumed pairing formula. -/
theorem centeredTracialPairing_matrix
    (L : R →⋆ₐ[ℂ] (E →L[ℂ] E)) (ι : Matrix α α ℂ →⋆ₐ[ℂ] R)
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (hι : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a)
    (a b : Matrix α α ℂ) (ha : Matrix.trace a = 0) (hb : Matrix.trace b = 0) :
    centeredTracialPairing τ V hinner htrace hdense
      ((tracialMatrixStage τ V L ι hinner hleft hι).center a)
      ((tracialMatrixStage τ V L ι hinner hleft hι).center b) =
      (Fintype.card α : ℂ)⁻¹ * Matrix.trace (a * b) := by
  change inner ℂ
    (tracialConjugation τ V hinner htrace hdense
      (((tracialMatrixStage τ V L ι hinner hleft hι).center a : E)))
    (((tracialMatrixStage τ V L ι hinner hleft hι).center b : E)) = _
  rw [coe_tracialMatrixStage_center_of_trace_zero τ V L ι hinner hleft hι a ha,
    coe_tracialMatrixStage_center_of_trace_zero τ V L ι hinner hleft hι b hb,
    tracialConjugation_apply_vector, hinner, star_star, ← map_mul, hι]

end Conjugation

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_TracialCornerCyclicity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cyclicity of finite tracial corners from dense algebra vectors and
partial-isometry transport. No corner cyclicity or density is assumed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem cornerInto_self (e r : P) (he : IsIdempotentElem e) (hr : IsIdempotentElem r)
    (x : G.corner e r) : G.cornerInto e r he hr x = x := by
  apply Subtype.ext
  have hx := (G.mem_corner e r x).mp x.property
  change G.left e (G.right r x) = x
  rw [hx.2, hx.1]

/-- Corner density is derived from the dense algebra vectors by a surjective
continuous projection. -/
theorem corner_vectors_dense (e r : P) (he : IsIdempotentElem e) (hr : IsIdempotentElem r) :
    DenseRange (fun a : P => G.cornerInto e r he hr (G.vector a)) := by
  have hs : Function.Surjective (G.cornerInto e r he hr) := fun x =>
    ⟨x, G.cornerInto_self e r he hr x⟩
  exact hs.denseRange.comp G.dense_vector (G.cornerInto e r he hr).continuous

end TracialCornerGeometry

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ActualArcCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow-arc finite Fourier compression with actual normalized tracial
dihedral word inclusions. Their formulas and orthogonality are proved. -/

noncomputable section
namespace KadisonSimilarity

variable {R H K : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem dihedralNormalization_sq {t : ℝ} (ht : 0 < t) :
    star (dihedralNormalization t) * dihedralNormalization t = (t : ℂ)⁻¹ := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have h := congrArg (fun z : ℂ => z * (t : ℂ)⁻¹) (dihedralNormalization_identity ht)
  simpa only [mul_assoc, mul_inv_cancel₀ htc, mul_one, one_mul] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

def centeredMatrixStage (R : ∀ s, MatrixHilbertStage (E := E) (F := F) (α := A s))
    (s : ℕ) : Set F := {x | ∃ a, Matrix.trace a = 0 ∧ (R s).center a = x}

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_MultiplicityClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable [CompleteSpace G]

/-- Compression to a chosen unit vector in the non-multiplicity factor. -/
def multiplicityCompression (Y : HilbertTensor G H →L[ℂ] HilbertTensor G H) (w : H) : G →L[ℂ] G :=
  (hilbertTensorRightInsert w).adjoint.comp (Y.comp (hilbertTensorRightInsert w))

section EndpointMultiplicity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {α : Type*} [Fintype α] [DecidableEq α] {k l : ℕ}

/-- Word covariance before taking scalar multiplicity slices. -/
structure MultiplicityMatrixCovariance
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : HilbertTensor G (EndpointTensor E F k) →L[ℂ]
      HilbertTensor G (EndpointTensor E F l)) where
  sourceAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F k →ₗᵢ[ℂ] EndpointTensor E F k
  testAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F l →ₗᵢ[ℂ] EndpointTensor E F l
  intertwine : ∀ u, Y.comp (hilbertTensorLift (sourceAction u).toContinuousLinearMap) =
    (hilbertTensorLift (testAction u).toContinuousLinearMap).comp Y
  source_covariance : ∀ (u : Matrix.unitaryGroup α ℂ)
      (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord Ω (fun i => R.center ((u : Matrix α α ℂ) * v (some (Sum.inl i)) * star (u : Matrix α α ℂ))) =
      sourceAction u (endpointWord Ω (fun i => R.center (v (some (Sum.inl i)))))
  test_covariance : ∀ (u : Matrix.unitaryGroup α ℂ)
      (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord (R.full (star ((u : Matrix α α ℂ) * v none * star (u : Matrix α α ℂ))))
      (fun j => J (R.center ((u : Matrix α α ℂ) * v (some (Sum.inr j)) * star (u : Matrix α α ℂ)))) =
      testAction u (endpointWord (R.full (star (v none)))
        (fun j => J (R.center (v (some (Sum.inr j))))))

end EndpointMultiplicity

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBaseGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- The actual base trace is normalized whenever the ambient trace is. -/
theorem baseGeometry_trace_one (htrace : G.trace 1 = 1) :
    (G.baseGeometry A).trace 1 = 1 := htrace

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_BaseSymmetry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace-zero symmetry of the actual base algebra supplies the normalized
centered letter and its represented selfadjoint involution. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)]

/-- Trace normalization and the symmetry relation give norm one, rather than
requiring a separately chosen unit vector in the centered space. -/
theorem norm_baseSymmetryLetter (s : A) (hzero : G.trace (s : P) = 0)
    (hself : star s = s) (hsquare : s * s = 1) (htrace : G.trace 1 = 1) :
    ‖G.baseSymmetryLetter A s hzero‖ = 1 := by
  have hsq : ‖G.baseVector A s‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.baseVector_inner]
    change Complex.re ((G.baseGeometry A).trace (star s * s)) = 1
    rw [hself, hsquare]
    exact congrArg Complex.re (G.baseGeometry_trace_one A htrace)
  change ‖G.baseVector A s‖ = 1
  nlinarith [norm_nonneg (G.baseVector A s)]

/-- The actual base symmetry determines all normalized repeated-letter
inclusions required by the word multiplicities. -/
def baseSymmetryRepeatedInclusion (s : A) (hzero : G.trace (s : P) = 0)
    (hself : star s = s) (hsquare : s * s = 1) (htrace : G.trace 1 = 1) (k : ℕ) :
    G.baseSpace A →ₗᵢ[ℂ] WordMultiplicity (G.baseVector A 1) k :=
  repeatedMultiplicityInclusion (G.baseVector A 1) (G.baseSymmetryLetter A s hzero)
    (G.norm_baseSymmetryLetter A s hzero hself hsquare htrace) k

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual corner representations on the completed tracial Hilbert corners. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

instance cornerSubmodule_complete : CompleteSpace (G.corner e r).toSubmodule :=
  (G.corner e r).isClosed.completeSpace_coe

theorem corner_inclusion_intertwines (a : CStarCorner e he) :
    (G.left (a : P)).comp (G.corner e r).toSubmodule.subtypeL =
      (G.corner e r).toSubmodule.subtypeL.comp (G.cornerRepresentation e he r a) := rfl

/-- Faithfulness of the dense tracial algebra vectors makes right
multiplication faithful, as required by the full-column theorem. -/
def faithfulRightAction (hV : Function.Injective G.vector) :
    TracialRightAction (P := P) (H := H) where
  right := G.right
  injective := by
    intro a b hab
    apply hV
    have h := congrArg (fun T : H →L[ℂ] H => T (G.vector 1)) hab
    simpa only [G.right_vector, one_mul] using h
  mul := G.right_mul

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized tracial Hilbert representation of an actual C-star corner.
Its density and action are inherited from the ambient tracial representation. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (p : P) (hp : IsStarProjection p)

theorem cornerAlgebraVector_dense : DenseRange (G.cornerAlgebraVector p hp) := by
  apply (G.corner_vectors_dense p p hp.isIdempotentElem hp.isIdempotentElem).mono
  rintro x ⟨a, rfl⟩
  refine ⟨CStarCorner.compress p hp a, ?_⟩
  apply Subtype.ext
  exact (G.cornerProjection_vector p p a).symm

theorem normalizedCornerVector_dense (c : ℂ) (hc : c ≠ 0) :
    DenseRange (G.normalizedCornerVector p hp c) := by
  exact (Homeomorph.smulOfNeZero c hc).surjective.denseRange.comp
    (G.cornerAlgebraVector_dense p hp) (Homeomorph.smulOfNeZero c hc).continuous

/-- The corner representation is constructed without a new GNS or
free-product existence assumption. Only the scalar normalization is chosen. -/
def cornerGeometry (c : ℂ) (hc : c ≠ 0) (hcτ : star c * c = (G.trace p)⁻¹) :
    TracialCornerGeometry (CStarCorner p hp) (G.corner p p) where
  trace := CStarCorner.normalizedTrace p hp G.trace
  vector := G.normalizedCornerVector p hp c
  left := G.cornerRepresentation p hp p
  inner_vector a b := by
    change inner ℂ (c • G.vector (a : P)) (c • G.vector (b : P)) = _
    rw [inner_smul_left, inner_smul_right, G.inner_vector]
    change star c * (c * G.trace (star (a : P) * (b : P))) =
      (G.trace p)⁻¹ * G.trace (star (a : P) * (b : P))
    rw [← mul_assoc, hcτ]
  tracial := CStarCorner.normalizedTrace_tracial p hp G.trace G.tracial
  dense_vector := G.normalizedCornerVector_dense p hp c hc
  left_vector a b := by
    apply Subtype.ext
    change G.left (a : P) (c • G.vector (b : P)) = c • G.vector ((a : P) * (b : P))
    rw [map_smul, G.left_vector]

/-- The positive trace supplies the concrete inverse-square-root scalar. -/
theorem cornerNormalization_ne_zero {t : ℝ} (ht : 0 < t) :
    dihedralNormalization t ≠ 0 := by
  intro hz
  have h := dihedralNormalization_identity ht
  rw [hz, star_zero, zero_mul, zero_mul] at h
  exact zero_ne_one h

/-- The normalized tracial representation on `pL²(P)p`, with the scalar
chosen from the actual trace of `p`. -/
def normalizedCornerGeometry {t : ℝ} (ht : 0 < t) (htp : G.trace p = (t : ℂ)) :
    TracialCornerGeometry (CStarCorner p hp) (G.corner p p) :=
  G.cornerGeometry p hp (dihedralNormalization t) (cornerNormalization_ne_zero ht)
    (by rw [htp]; exact dihedralNormalization_sq ht)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralPositiveDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered dihedral corner is generated in L² by the positive
compressed rotation powers. Apply the bounded centered corner map to the
ordinary rotation/reflection word span; no bounded approximation theorem
or corner-freeness hypothesis is needed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry
variable (G : TracialCornerGeometry P H)

/-- The bounded map that compresses to the corner and removes its scalar part. -/
def centeredCornerProjection (p : P) : H →L[ℂ] H :=
  G.cornerProjection p p - (G.trace p)⁻¹ • InnerProductSpace.rankOne ℂ (G.vector p) (G.vector p)

/-- All ordinary dihedral rotation and reflection-coset vectors. -/
def dihedralGroupWordVectors (d w : Pˣ) : Set H :=
  Set.range (fun l : ℤ => G.vector (↑(w ^ l) : P)) ∪
    Set.range (fun l : ℤ => G.vector ((↑(w ^ l) : P) * (d : P)))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCompressionGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The overlap of a small corner with words starting in the other free
factor. The estimate follows from the displayed tensor geometry. -/

noncomputable section
namespace KadisonSimilarity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Projection onto the chosen first tensor coordinate and a tail subspace. -/
def firstLetterProjection (Ω : E) (Q : F →L[ℂ] F) :
    HilbertTensor E F →L[ℂ] HilbertTensor E F :=
  (hilbertTensorInsert Ω).comp (Q.comp (hilbertTensorInsert Ω).adjoint)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HaarCornerLetters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Haar powers in a tracial corner. Their adjoints give the
orthonormal first-letter sequence used in the propagation argument. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P] {q : P} {hq : IsStarProjection q}

variable (τ : P →ₗ[ℂ] ℂ) (z : unitary (CStarCorner q hq)) {a : ℝ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

/-- The adjoint Haar letters form the actual orthonormal Hilbert sequence
required by the vacuum-slice propagation argument. -/
theorem haarCornerLetter_adjoint_orthonormal (G : TracialCornerGeometry P H)
    (z : unitary (CStarCorner q hq)) {a : ℝ} (ha : 0 < a)
    (htrace : G.trace q = (a : ℂ)) (hhaar : HaarCornerMoments G.trace z a) :
    Orthonormal ℂ (fun n : ℕ => G.vector (star (haarCornerLetter z a n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [G.inner_vector, star_star]
  exact haarCornerLetter_mul_star_trace G.trace z ha htrace hhaar i j

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ReducedWordModel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reduced-word part of the published free-product construction.

Ricard–Xu, J. reine angew. Math. 599 (2006), Section 1, pp. 2–3 of
arXiv:math/0505302, constructs the reduced free-product Hilbert space as the
orthogonal sum of alternating centered tensor words. Regrouping the first
and last factors gives the coordinates below. The input is only this word
construction, without any operator invariance or commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

/-- Regrouped ordinary free-product words. The multiplicity space and the
endpoint space are fixed concrete tensor products of the two base spaces. -/
def TracialWordFormula (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H) : Prop :=
  ∀ (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0),
    U.inclusion n (tracialWordTensor G A D n d b a c ha hc) =
      G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
        (fun i => (c i : P)) * (b : P))

/-- Published input: the alternating centered tensor model for a normalized
faithful tracial reduced product. Its only output is the word coordinates. -/
def RicardXuWordDecompositionInput : Prop :=
  G.trace 1 = 1 → Function.Injective G.vector → ScalarFree G.trace D A →
    ReducedWordGenerated G A D → ∃ U : OrthogonalWordLevels
      (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
        (centeredSubspace (G.baseVector D 1))) H, TracialWordFormula G A D U

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorHeadSlices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.crossMultiplicitySlice_zero _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vacuum coefficients of a head tensor action

The exceptional-projection formula in propagation follows from the actual
head action on the completed tensor product. It does not need to be assumed
separately for every vector or every term of the Haar sequence.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMap
open scoped TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The adjoint of endpoint insertion is the completed tensor slice. -/
theorem hilbertTensorInsert_adjoint (Ω : E) :
    (hilbertTensorInsert (H := F) Ω).adjoint = tensorSlice Ω := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  apply ext_inner_left ℂ
  intro y
  rw [adjoint_inner_right, inner_hilbertTensorInsert, tensorSlice_insert, inner_smul_right]

/-- The actual vacuum subspace in a completed head-tail tensor product. -/
def vacuumSubspace (Ω : E) : Submodule ℂ (HilbertTensor E F) :=
  (hilbertTensorInsert Ω).range

/-- Subtracting the vacuum coefficient leaves an orthogonal vector. -/
theorem vacuum_remainder_orthogonal (Ω : E) (hΩ : ‖Ω‖ = 1) (z : HilbertTensor E F) :
    z - hilbertTensorInsert Ω (tensorSlice Ω z) ∈ (vacuumSubspace (F := F) Ω)ᗮ := by
  have hzero (x : F) : inner ℂ (hilbertTensorInsert Ω x)
      (z - hilbertTensorInsert Ω (tensorSlice Ω z)) = 0 := by
    have hfirst : inner ℂ (hilbertTensorInsert Ω x) z = inner ℂ x (tensorSlice Ω z) := by
      exact (adjoint_inner_right (hilbertTensorInsert Ω) x z).symm.trans
        (congrArg (fun T : HilbertTensor E F →L[ℂ] F => inner ℂ x (T z))
          (hilbertTensorInsert_adjoint Ω))
    have hsecond : inner ℂ (hilbertTensorInsert Ω x)
        (hilbertTensorInsert Ω (tensorSlice Ω z)) = inner ℂ x (tensorSlice Ω z) := by
      exact (inner_hilbertTensorInsert Ω Ω x (tensorSlice Ω z)).trans (by
        rw [inner_self_eq_norm_sq_to_K, hΩ]
        simp)
    exact (inner_sub_right _ _ _).trans (sub_eq_zero.mpr (hfirst.trans hsecond.symm))
  rintro w ⟨x, rfl⟩
  exact hzero x

/-- The vacuum projection exists directly from the tensor decomposition. -/
theorem vacuumSubspace_hasOrthogonalProjection (Ω : E) (hΩ : ‖Ω‖ = 1) :
    (vacuumSubspace (F := F) Ω).HasOrthogonalProjection where
  exists_orthogonal z := ⟨hilbertTensorInsert Ω (tensorSlice Ω z),
    ⟨tensorSlice Ω z, rfl⟩, vacuum_remainder_orthogonal Ω hΩ z⟩

/-- The orthogonal projection onto the vacuum subspace is insertion followed
by its adjoint. -/
theorem vacuumSubspace_starProjection (Ω : E) (hΩ : ‖Ω‖ = 1)
    [(vacuumSubspace (F := F) Ω).HasOrthogonalProjection] :
    (vacuumSubspace (F := F) Ω).starProjection =
      firstLetterProjection Ω (ContinuousLinearMap.id ℂ F) := by
  ext z
  change (vacuumSubspace (F := F) Ω).starProjection z =
    hilbertTensorInsert Ω ((hilbertTensorInsert Ω).adjoint z)
  rw [hilbertTensorInsert_adjoint]
  exact (vacuumSubspace (F := F) Ω).eq_starProjection_of_mem_orthogonal
    ⟨tensorSlice Ω z, rfl⟩ (vacuum_remainder_orthogonal Ω hΩ z)

variable [CompleteSpace E]

/-- Moving the head operator to the slicing vector takes its adjoint. -/
theorem tensorSlice_head (Ω : E) (X : E →L[ℂ] E) :
    (tensorSlice (F := F) Ω).comp (tensorHeadAction X) = tensorSlice (X.adjoint Ω) := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  simp only [comp_apply, tensorHeadAction_insert, tensorSlice_insert]
  rw [adjoint_inner_left]

/-- The full vacuum projection after multiplication is the slice against
`X*Ω`, followed by insertion of `Ω`. -/
theorem firstLetterProjection_head (Ω : E) (X : E →L[ℂ] E) :
    (firstLetterProjection Ω (ContinuousLinearMap.id ℂ F)).comp (tensorHeadAction X) =
      (hilbertTensorInsert Ω).comp (tensorSlice (X.adjoint Ω)) := by
  simp only [firstLetterProjection, ContinuousLinearMap.id_comp,
    hilbertTensorInsert_adjoint, ContinuousLinearMap.comp_assoc, tensorSlice_head]

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Transport the actual vacuum subspace through tracial word coordinates. -/
abbrev tracialVacuumSubspace (U : H ≃ₗᵢ[ℂ] HilbertTensor E F) (Ω : E) : Submodule ℂ H :=
  (vacuumSubspace (F := F) Ω).map U.symm.toLinearIsometry.toLinearMap

omit [CompleteSpace E] in
/-- The projection-coordinate identity follows from its actual subspace
construction, rather than being additional word-model data. -/
theorem tracialVacuumSubspace_projection_coordinates
    (U : H ≃ₗᵢ[ℂ] HilbertTensor E F) (Ω : E) (hΩ : ‖Ω‖ = 1)
    [(vacuumSubspace (F := F) Ω).HasOrthogonalProjection]
    [(tracialVacuumSubspace U Ω).HasOrthogonalProjection] (z : H) :
    U ((tracialVacuumSubspace U Ω).starProjection z) =
      firstLetterProjection Ω (ContinuousLinearMap.id ℂ F) (U z) := by
  have h := U.symm.toLinearIsometry.map_starProjection (vacuumSubspace (F := F) Ω) (U z)
  have hu := congrArg U h
  simpa only [tracialVacuumSubspace, LinearIsometryEquiv.coe_toLinearIsometry,
    U.apply_symm_apply, U.symm_apply_apply, vacuumSubspace_starProjection Ω hΩ] using hu.symm

/-- Transport the head-action formula to a tracial word realization. The two
hypotheses are the ordinary coordinate identities for multiplication and for
the vacuum projection. -/
theorem vacuum_slice_in_coordinates
    (U : H ≃ₗᵢ[ℂ] HilbertTensor E F) (Ω : E)
    (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (X : H →L[ℂ] H) (T : E →L[ℂ] E)
    (hP : ∀ z, U (P.starProjection z) =
      firstLetterProjection Ω (ContinuousLinearMap.id ℂ F) (U z))
    (hX : ∀ z, U (X z) = tensorHeadAction T (U z)) (z : H) :
    P.starProjection (X z) = U.symm
      (hilbertTensorInsert Ω (tensorSlice (T.adjoint Ω) (U z))) := by
  apply U.injective
  rw [hP, hX, U.apply_symm_apply]
  exact congrArg (fun A : HilbertTensor E F →L[ℂ] HilbertTensor E F => A (U z))
    (firstLetterProjection_head Ω T)

end Coordinates
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSupportedColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support projections and represented right columns in a concrete tracial
Hilbert space. These are the ambient spaces used by the full-column lemma. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem cornerProjection_adjoint (e r : P) (he : IsStarProjection e) (hr : IsStarProjection r) :
    (G.cornerProjection e r).adjoint = G.cornerProjection e r := by
  rw [cornerProjection, ContinuousLinearMap.adjoint_comp, G.right_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
    he.isSelfAdjoint.star_eq, hr.isSelfAdjoint.star_eq]
  exact G.right_left e r

/-- The support-equation projection is the actual orthogonal projection
onto the completed two-sided Hilbert corner. -/
theorem cornerInto_eq_adjoint (e r : P) (he : IsStarProjection e) (hr : IsStarProjection r) :
    G.cornerInto e r he.isIdempotentElem hr.isIdempotentElem =
      (G.corner e r).toSubmodule.subtypeL.adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (y : H) (G.cornerProjection e r x) = inner ℂ (y : H) x
  rw [← G.cornerProjection_adjoint e r he hr,
    ContinuousLinearMap.adjoint_inner_right]
  have hfix := congrArg (fun z : G.corner e r => (z : H))
    (G.cornerInto_self e r he.isIdempotentElem hr.isIdempotentElem y)
  change G.cornerProjection e r y = (y : H) at hfix
  rw [hfix]

theorem corner_inclusion_adjoint (e r : P) (he : IsStarProjection e) (hr : IsStarProjection r) :
    (G.corner e r).toSubmodule.subtypeL.comp
      (G.corner e r).toSubmodule.subtypeL.adjoint = G.cornerProjection e r := by
  rw [← G.cornerInto_eq_adjoint e r he hr]
  rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerEstimate
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small-corner commutator estimate supplies the actual bounded
rectangular derivation used in the full-column argument. -/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

universe u v
variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

/-- Compression of the ambient operator to the actual domain and output
corners. The domain may have a smaller right support. -/
def cornerRestriction (Y : H →L[ℂ] H) : G.corner e r →L[ℂ] G.corner e 1 :=
  (G.corner e 1).toSubmodule.subtypeL.adjoint.comp
    (Y.comp (G.corner e r).toSubmodule.subtypeL)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixColumns
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.DihedralSpectralArc.corner_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.haarCornerLetter_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_mul _root_.OAI.KadisonSimilarity.haarCornerPower_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_zero _root_.OAI.KadisonSimilarity.mul_haarCornerPower _root_.OAI.KadisonSimilarity.star_haarCornerLetter _root_.OAI.KadisonSimilarity.star_haarCornerPower _root_.OAI.KadisonSimilarity.support_mul_haarCornerLetter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix-unit column coordinates of a concrete tracial corner. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

theorem cornerToRightColumn_adjoint (hr : IsStarProjection r) (x : G.corner 1 r) :
    (G.cornerToRightColumn e r).toContinuousLinearMap.adjoint x =
      G.cornerInto e r he.isIdempotentElem hr.isIdempotentElem (x : H) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, G.cornerInto_eq_adjoint e r he hr,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

include he in
theorem cornerToRightColumn_projection (hr : IsStarProjection r) :
    (G.cornerToRightColumn e r).toContinuousLinearMap.comp
      (G.cornerToRightColumn e r).toContinuousLinearMap.adjoint =
        G.rightColumnRepresentation r e := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  rw [ContinuousLinearMap.comp_apply, G.cornerToRightColumn_adjoint e he r hr]
  change G.left e (G.right r (x : H)) = G.left e (x : H)
  rw [((G.mem_corner 1 r x).mp x.property).2]

/-- The finite range decomposition in the ambient Hilbert space. -/
def ambientCornerColumns {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) :
    FiniteOrthogonalColumns (G.corner e 1) H n :=
  partialIsometryColumns G.left e he v hv hsum (G.corner e 1).toSubmodule.subtypeₗᵢ (by
    change (G.corner e 1).toSubmodule.subtypeL.comp
      (G.corner e 1).toSubmodule.subtypeL.adjoint = G.left e
    rw [G.corner_inclusion_adjoint e 1 he (IsStarProjection.one P), cornerProjection,
      G.right_one, ContinuousLinearMap.comp_id])

/-- The same finite range decomposition in the right-supported column. -/
def supportedCornerColumns (hr : IsStarProjection r) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) :
    FiniteOrthogonalColumns (G.corner e r) (G.corner 1 r) n :=
  partialIsometryColumns (G.rightColumnRepresentation r) e he v hv hsum
    (G.cornerToRightColumn e r) (G.cornerToRightColumn_projection e he r hr)

/-- Matrix entries of an arbitrary algebra element, as actual elements of
the unital corner algebra. -/
def cornerMatrixEntry {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (a : P) (i j : Fin n) : CStarCorner e he :=
  ⟨star (v i) * a * v j, by
    have hi : e * star (v i) = star (v i) := by
      have h := congrArg star (mul_initial_projection e (v i) he (by simpa using hv i i))
      simpa only [star_mul, star_star, he.isSelfAdjoint.star_eq] using h
    have hj := mul_initial_projection e (v j) he (by simpa using hv j j)
    constructor
    · rw [← mul_assoc, ← mul_assoc, hi]
    · rw [mul_assoc, hj]⟩

theorem cornerRepresentation_compression (a : CStarCorner e he) :
    G.cornerRepresentation e he 1 a =
      (G.corner e 1).toSubmodule.subtypeL.adjoint.comp
        ((G.left (a : P)).comp (G.corner e 1).toSubmodule.subtypeL) := by
  rw [G.corner_inclusion_intertwines e he 1 a, ← ContinuousLinearMap.comp_assoc]
  have hI : (G.corner e 1).toSubmodule.subtypeL.adjoint.comp
      (G.corner e 1).toSubmodule.subtypeL = 1 :=
    (G.corner e 1).toSubmodule.subtypeₗᵢ.adjoint_comp_self
  change _ = ((G.corner e 1).toSubmodule.subtypeL.adjoint.comp
    (G.corner e 1).toSubmodule.subtypeL).comp _
  rw [hI, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

theorem cornerRepresentation_supported_compression (a : CStarCorner e he) :
    G.cornerRepresentation e he r a =
      (G.cornerToRightColumn e r).toContinuousLinearMap.adjoint.comp
        ((G.rightColumnRepresentation r (a : P)).comp
          (G.cornerToRightColumn e r).toContinuousLinearMap) := by
  have hi : (G.rightColumnRepresentation r (a : P)).comp
      (G.cornerToRightColumn e r).toContinuousLinearMap =
      (G.cornerToRightColumn e r).toContinuousLinearMap.comp
        (G.cornerRepresentation e he r a) := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  rw [hi, ← ContinuousLinearMap.comp_assoc,
    (G.cornerToRightColumn e r).adjoint_comp_self, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp]

/-- The ambient matrix coordinate entries are the actual elements
`vᵢ* a vⱼ` of `ePe`. -/
theorem ambientCornerColumns_entry {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) (a : P) (i j : Fin n) :
    G.cornerRepresentation e he 1 (cornerMatrixEntry e he v hv a i j) =
      ((G.ambientCornerColumns e he v hv hsum).inclusion i).adjoint.comp
        ((G.left a).comp ((G.ambientCornerColumns e he v hv hsum).inclusion j)) := by
  rw [G.cornerRepresentation_compression]
  exact (partialIsometryColumns_entry G.left e he v hv hsum
    (G.corner e 1).toSubmodule.subtypeₗᵢ _ a i j).symm

theorem supportedCornerColumns_entry (hr : IsStarProjection r) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) (a : P) (i j : Fin n) :
    G.cornerRepresentation e he r (cornerMatrixEntry e he v hv a i j) =
      ((G.supportedCornerColumns e he r hr v hv hsum).inclusion i).adjoint.comp
        ((G.rightColumnRepresentation r a).comp
          ((G.supportedCornerColumns e he r hr v hv hsum).inclusion j)) := by
  rw [G.cornerRepresentation_supported_compression]
  exact (partialIsometryColumns_entry (G.rightColumnRepresentation r) e he v hv hsum
    (G.cornerToRightColumn e r) _ a i j).symm

/-- Both coordinate unitaries and every entry in the full-column theorem
are now constructed from the same finite family in the tracial algebra. -/
def fullColumnCoordinates (hr : IsStarProjection r) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) :
    FullColumnCoordinates G.left (G.rightColumnRepresentation r)
      (G.cornerRepresentation e he 1) (G.cornerRepresentation e he r) n :=
  fullColumnCoordinatesOfColumns G.left (G.rightColumnRepresentation r)
    (G.cornerRepresentation e he 1) (G.cornerRepresentation e he r)
    (G.ambientCornerColumns e he v hv hsum)
    (G.supportedCornerColumns e he r hr v hv hsum)
    (cornerMatrixEntry e he v hv)
    (G.ambientCornerColumns_entry e he v hv hsum)
    (G.supportedCornerColumns_entry e he r hr v hv hsum)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialHeadCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- Grouping reduced words by their possible initial `D` letter yields these
coordinates. The sole action field is ordinary left multiplication on that
initial tensor factor; no propagation estimate is included. -/
structure TracialHeadCoordinates (GD : TracialCornerGeometry D E)
    (G : TracialCornerGeometry P H) (ι : D →⋆ₐ[ℂ] P) (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  unitary : H ≃ₗᵢ[ℂ] HilbertTensor E F
  left_head : ∀ d z, unitary (G.left (ι d) z) =
    tensorHeadAction (GD.left d) (unitary z)

namespace TracialCornerGeometry

/-- The adjoint of left multiplication has the expected value on the trace
vector, providing the slicing vector without an additional hypothesis. -/
theorem left_adjoint_traceVector (G : TracialCornerGeometry P H) (a : P) :
    (G.left a).adjoint (G.vector 1) = G.vector (star a) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, G.left_vector, mul_one]

end TracialCornerGeometry

namespace TracialHeadCoordinates

variable {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)

/-- The actual exceptional subspace consists of words whose initial `D`
coordinate is the scalar trace vector. -/
abbrev vacuum : Submodule ℂ H := tracialVacuumSubspace W.unitary (GD.vector 1)

end TracialHeadCoordinates
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialRepeatedWords
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

namespace TracialCornerGeometry

/-- A scaled initial projection in the algebra gives the corresponding
operator identity in any represented tracial Hilbert space. -/
theorem embedded_left_scaled_initial (G : TracialCornerGeometry P H)
    (ι : D →⋆ₐ[ℂ] P) (x q : D) (c : ℂ) (hx : star x * x = c • q) :
    (G.left (ι x)).adjoint.comp (G.left (ι x)) = c • G.left (ι q) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  change G.left (star (ι x)) * G.left (ι x) = _
  rw [← map_mul, ← map_star, ← map_mul, hx, map_smul, map_smul]

end TracialCornerGeometry

variable {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)
  [W.vacuum.HasOrthogonalProjection]
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq)) (a : ℝ)
  (Y : H →L[ℂ] H) (B₀ : B →L[ℂ] B) (Bₖ : V →L[ℂ] V)

/-- The remaining raw reduced-word geometry for a fixed positive degree.
All operators acting on the ambient space are specified as left multipliers.
There is no approximation estimate among these fields. -/
structure TracialRepeatedWordRealization where
  repeatVector : B →ₗᵢ[ℂ] V
  word : ℕ → V →ₗᵢ[ℂ] H
  small : B →L[ℂ] H
  small_norm : ∀ v, ‖small v‖ = Real.sqrt a * ‖v‖
  level_zero : ∀ v, Y (small v) = small (B₀ v)
  level_repeated : ∀ n v, Y (word n (repeatVector v)) = word n (Bₖ (repeatVector v))
  support_small : ∀ v, G.left (ι q) (small v) = small v
  prefixElement : ℕ → P
  word_factor : ∀ n v, word n (repeatVector v) =
    G.left (prefixElement n) (G.left (ι (haarCornerLetter z a n)) (small v))
  prefix_isometry : ∀ n, ∀ y ∈ W.vacuumᗮ, ‖G.left (prefixElement n) y‖ = ‖y‖
  prefix_bound : ℝ
  prefix_bound_le : ∀ n, ‖G.left (prefixElement n)‖ ≤ prefix_bound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordPrefixRealization
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed alternating prefixes in propagation are isometries on the
appropriate reduced-word subspace. This follows by iterating the two
one-letter Fock creation formulas. Their global operator bounds follow from
the algebraic symmetry and normalized corner-unitary relations. -/

noncomputable section
namespace KadisonSimilarity

section AlgebraBounds

variable {P : Type*} [CStarAlgebra P]

/-- The algebra norm of every corner Haar letter is bounded uniformly in its
frequency, using only its normalization and corner unitarity. -/
theorem norm_haarCornerLetter_le {q : P} {hq : IsStarProjection q}
    (z : unitary (CStarCorner q hq)) (a : ℝ) (n : ℕ) :
    ‖haarCornerLetter z a n‖ ≤ (Real.sqrt a)⁻¹ := by
  have hpow : ‖haarCornerPower z ((n : ℤ) + 1)‖ ≤ 1 :=
    norm_unitary_le_one (z ^ ((n : ℤ) + 1))
  have hc : ‖haarCornerCoefficient a‖ = (Real.sqrt a)⁻¹ := by
    simp only [haarCornerCoefficient, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg a))]
  rw [haarCornerLetter, norm_smul, hc]
  exact (mul_le_mul_of_nonneg_left hpow
    (inv_nonneg.mpr (Real.sqrt_nonneg a))).trans_eq (mul_one _)

end AlgebraBounds

section TracialPrefix

variable {D P E H F EA ED B V : Type*} [CStarAlgebra D] [CStarAlgebra P]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup EA] [InnerProductSpace ℂ EA]
  [NormedAddCommGroup ED] [InnerProductSpace ℂ ED]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)
  [W.vacuum.HasOrthogonalProjection]
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  (a : ℝ) (s : P)

/-- The degree-`m + 1` alternating algebra prefix. -/
def tracialWordPrefix (m n : ℕ) : P :=
  (s * ι (haarCornerLetter z a n)) ^ m * s

omit [CompleteSpace F] [W.vacuum.HasOrthogonalProjection] in
/-- The left multiplier of the actual algebra prefix is isometric on the
nonvacuum head subspace, by the elementary Fock creation identities. -/
theorem tracialWordPrefix_isometry
    (C : AlternatingCreationCoordinates EA ED (G.left s)
      (fun n => G.left (ι (haarCornerLetter z a n))) W.vacuumᗮ)
    (m n : ℕ) (y : H) (hy : y ∈ W.vacuumᗮ) :
    ‖G.left (tracialWordPrefix (ι := ι) z a s m n) y‖ = ‖y‖ := by
  simpa only [tracialWordPrefix, map_mul, map_pow] using
    (C.prefix_isometry m n y hy).2

/-- The complete prefix has a uniform bound for each fixed degree. Only the
algebraic unitary relations enter this global estimate. -/
theorem norm_tracialWordPrefix_le (hstar : star s = s) (hsq : s * s = 1)
    (m n : ℕ) :
    ‖G.left (tracialWordPrefix (ι := ι) z a s m n)‖ ≤ ((Real.sqrt a)⁻¹) ^ m := by
  have hs : ‖G.left s‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le G.left.toNonUnitalStarAlgHom s).trans
      (norm_symmetry_le_one s hstar hsq)
  have hx : ‖G.left (ι (haarCornerLetter z a n))‖ ≤ (Real.sqrt a)⁻¹ :=
    (NonUnitalStarAlgHom.norm_apply_le G.left.toNonUnitalStarAlgHom _).trans
      ((NonUnitalStarAlgHom.norm_apply_le ι.toNonUnitalStarAlgHom _).trans
        (norm_haarCornerLetter_le z a n))
  have hc : 0 ≤ (Real.sqrt a)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg a)
  induction m with
  | zero => simpa only [tracialWordPrefix, pow_zero, one_mul] using hs
  | succ m ih =>
    have hid : G.left (tracialWordPrefix (ι := ι) z a s (m + 1) n) =
        (G.left s * G.left (ι (haarCornerLetter z a n))) *
          G.left (tracialWordPrefix (ι := ι) z a s m n) := by
      simp only [tracialWordPrefix, pow_succ', map_mul, map_pow, mul_assoc]
    rw [hid, pow_succ']
    calc
      _ ≤ (‖G.left s‖ * ‖G.left (ι (haarCornerLetter z a n))‖) *
          ‖G.left (tracialWordPrefix (ι := ι) z a s m n)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * (Real.sqrt a)⁻¹) * ((Real.sqrt a)⁻¹) ^ m := by
        exact mul_le_mul (mul_le_mul hs hx (norm_nonneg _) zero_le_one) ih
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [one_mul]

/-- Construct the propagation realization from elementary reduced-word
creation and multiplication. Both complete-prefix fields are conclusions. -/
def tracialRepeatedWordRealizationOfCreation
    (hstar : star s = s) (hsq : s * s = 1)
    (C : AlternatingCreationCoordinates EA ED (G.left s)
      (fun n => G.left (ι (haarCornerLetter z a n))) W.vacuumᗮ)
    (m : ℕ) (Y : H →L[ℂ] H) (B₀ : B →L[ℂ] B) (Bₖ : V →L[ℂ] V)
    (repeatVector : B →ₗᵢ[ℂ] V) (word : ℕ → V →ₗᵢ[ℂ] H)
    (small : B →L[ℂ] H)
    (hsmall : ∀ v, ‖small v‖ = Real.sqrt a * ‖v‖)
    (hzero : ∀ v, Y (small v) = small (B₀ v))
    (hlevel : ∀ n v, Y (word n (repeatVector v)) = word n (Bₖ (repeatVector v)))
    (hsupport : ∀ v, G.left (ι q) (small v) = small v)
    (hword : ∀ n v, word n (repeatVector v) =
      G.left (tracialWordPrefix (ι := ι) z a s m n)
        (G.left (ι (haarCornerLetter z a n)) (small v))) :
    TracialRepeatedWordRealization W z a Y B₀ Bₖ where
  repeatVector := repeatVector
  word := word
  small := small
  small_norm := hsmall
  level_zero := hzero
  level_repeated := hlevel
  support_small := hsupport
  prefixElement := tracialWordPrefix (ι := ι) z a s m
  word_factor := hword
  prefix_isometry := tracialWordPrefix_isometry W z a s C m
  prefix_bound := ((Real.sqrt a)⁻¹) ^ m
  prefix_bound_le := norm_tracialWordPrefix_le z a s hstar hsq m

end TracialPrefix
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCreationCoordinates
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)] {q : D} {hq : IsStarProjection q}
  (z : unitary (CStarCorner q hq)) {a : ℝ} (ha : 0 < a)
  (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)

/-- The normalized trace and the exact initial-projection identity give
Hilbert norm one for each positive Haar power. -/
theorem norm_baseHaarLetter (n : ℕ) :
    ‖G.baseHaarLetter D z ha htrace hhaar n‖ = 1 := by
  have hinner : inner ℂ (G.baseVector D (haarCornerLetter z a n))
      (G.baseVector D (haarCornerLetter z a n)) = 1 := by
    rw [G.baseVector_inner]
    change (G.baseGeometry D).trace
      (star (haarCornerLetter z a n) * haarCornerLetter z a n) = 1
    rw [star_haarCornerLetter_mul_self z ha.le, map_smul, smul_eq_mul]
    change ((a⁻¹ : ℝ) : ℂ) * G.trace (q : P) = 1
    rw [htrace, Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne')]
  have hsq : ‖G.baseVector D (haarCornerLetter z a n)‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
    rfl
  change ‖G.baseVector D (haarCornerLetter z a n)‖ = 1
  nlinarith [norm_nonneg (G.baseVector D (haarCornerLetter z a n))]

end TracialCornerGeometry

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_PublishedWordCreation
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- Grouping ordinary reduced words by their first factor. Both the tail
space and the A-leading space are actual closed subspaces of the GNS space. -/
structure ReducedWordCreationModel where
  tail : ClosedSubmodule ℂ H
  head : TracialHeadCoordinates (G.baseGeometry D) G D.subtype tail
  aLead : ClosedSubmodule ℂ H
  createA : HilbertTensor (centeredSubspace (G.baseVector A 1)) head.vacuumᗮ →ₗᵢ[ℂ] H
  createD : HilbertTensor (centeredSubspace (G.baseVector D 1)) aLead →ₗᵢ[ℂ] H
  createA_mem : ∀ w, createA w ∈ aLead
  createD_mem : ∀ w, createD w ∈ head.vacuumᗮ
  actionA : ∀ (a : A) (ha : G.trace (a : P) = 0) (y : head.vacuumᗮ),
    G.left (a : P) y = createA (hilbertTensorInsert (G.baseSymmetryLetter A a ha) y)
  actionD : ∀ (d : D) (hd : G.trace (d : P) = 0) (y : aLead),
    G.left (d : P) y = createD (hilbertTensorInsert (G.baseSymmetryLetter D d hd) y)

/-- Published input specialized to the two actual tracial factors. -/
def RicardXuCreationInput : Prop :=
  G.trace 1 = 1 → Function.Injective G.vector → ScalarFree G.trace D A →
    ReducedWordGenerated G A D → Nonempty (ReducedWordCreationModel G A D)

/-- The vacuum/creation coordinates for multiplication by the second factor.
The projection singles out words beginning in that factor, and `before` is
its orthogonal complement. No operator norm estimate is part of this data. -/
structure ReducedWordCompressionModel where
  tail : ClosedSubmodule ℂ H
  before : ClosedSubmodule ℂ H
  head : TracialHeadCoordinates (G.baseGeometry A) G A.subtype tail
  tailProjection : tail →L[ℂ] tail
  projection_adjoint : tailProjection.adjoint = tailProjection
  projection_sq : tailProjection * tailProjection = tailProjection
  projection_norm : ‖tailProjection‖ ≤ 1
  includeBefore : before →ₗᵢ[ℂ] HilbertTensor (G.baseSpace A) tail
  create : HilbertTensor (centeredSubspace (G.baseVector D 1)) before →ₗᵢ[ℂ]
    HilbertTensor (G.baseSpace A) tail
  complement : includeBefore.toContinuousLinearMap.comp includeBefore.toContinuousLinearMap.adjoint =
    1 - firstLetterProjection (G.baseVector A 1) tailProjection
  create_range : ∀ (b : D) (hb : G.trace (b : P) = 0) x,
    firstLetterProjection (G.baseVector A 1) tailProjection
      (create (hilbertTensorInsert (G.baseSymmetryLetter D b hb) x)) =
        create (hilbertTensorInsert (G.baseSymmetryLetter D b hb) x)
  create_word : ∀ (b : D) (hb : G.trace (b : P) = 0) x,
    head.unitary (G.left (b : P) (head.unitary.symm (includeBefore x))) =
      create (hilbertTensorInsert (G.baseSymmetryLetter D b hb) x)

/-- Section 1 and Lemma 2.3 of Ricard--Xu, restricted to one creation letter
and its preceding-word space in a scalar tracial reduced product. -/
def RicardXuCompressionInput : Prop :=
  G.trace 1 = 1 → Function.Injective G.vector → ScalarFree G.trace D A →
    ReducedWordGenerated G A D → Nonempty (ReducedWordCompressionModel G A D)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialDihedralColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual dihedral columns and reduced-word columns agree on the completed
tracial base space. Their normalizations are derived from the trace; equality
of the two realizations is needed only on bounded algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)

/-- The normalized initial endpoint used by the dihedral word columns. -/
def projectionEndpoint (e : D) (t : ℝ) : G.baseSpace D :=
  dihedralNormalization t • G.baseVector D e

/-- A trace-`t` projection has Hilbert norm `sqrt t`. -/
theorem norm_projectionVector (e : D) (he : IsStarProjection e) {t : ℝ}
    (ht : 0 ≤ t) (hte : G.trace (e : P) = (t : ℂ)) :
    ‖G.baseVector D e‖ = Real.sqrt t := by
  have hsq : ‖G.baseVector D e‖ ^ 2 = t := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.baseVector_inner]
    change Complex.re ((G.trace.comp D.subtype.toLinearMap) (star e * e)) = t
    rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
    exact congrArg Complex.re hte
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg t)).mp
  rw [Real.sq_sqrt ht]
  exact hsq

/-- The actual normalized endpoint has norm one. -/
theorem norm_projectionEndpoint (e : D) (he : IsStarProjection e) {t : ℝ}
    (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ)) :
    ‖G.projectionEndpoint D e t‖ = 1 := by
  rw [projectionEndpoint, norm_smul, G.norm_projectionVector D e he ht.le hte]
  have hn : ‖dihedralNormalization t‖ = (Real.sqrt t)⁻¹ := by
    simp only [dihedralNormalization, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg t))]
  rw [hn, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr ht))]

variable (A : StarSubalgebra ℂ P) [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

/-- The actual finite dihedral column family on the tracial base. -/
def tracialDihedralColumns (N : ℕ) : Fin N → G.baseSpace A →L[ℂ] H := fun i =>
  (G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0 he ht hte i.val).toContinuousLinearMap

variable (U : OrthogonalWordLevels
  (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
    (centeredSubspace (G.baseVector D 1))) H)

/-- The repeated-word column at the actual normalized projection endpoint. -/
def repeatedDihedralInclusion (k : ℕ) : G.baseSpace A →ₗᵢ[ℂ] H :=
  repeatedWordInclusion U k (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k)
    (G.projectionEndpoint D e t) (G.baseSymmetryLetter D d hd0)
    (G.norm_projectionEndpoint D e he ht hte)
    (G.norm_baseSymmetryLetter D d hd0 hdstar hdsq hτ)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixTower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_base _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_column _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_corner _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
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

omit [CompleteSpace E] in
/-- Trace preservation forces every compatible matrix inclusion to preserve
trace-zero matrices, regardless of the change in matrix size. -/
theorem NestedTracialMatrices.trace_zero_inclusion (s t : ℕ) (h : s ≤ t)
    (a : Matrix (A s) (A s) ℂ) (ha : Matrix.trace a = 0) :
    Matrix.trace (M.inclusion s t h a) = 0 := by
  have he : (Fintype.card (A t) : ℂ)⁻¹ * Matrix.trace (M.inclusion s t h a) = 0 := by
    rw [← M.trace_embedding, M.compatible, M.trace_embedding, ha, mul_zero]
  have hn : (Fintype.card (A t) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero hn)

theorem embeddedMatrixStage_center_mono :
    Monotone (centeredMatrixStage (embeddedMatrixStage τ V L hinner hleft M)) := by
  intro s t h x hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨M.inclusion s t h a,
    NestedTracialMatrices.trace_zero_inclusion τ V M s t h a ha, ?_⟩
  simp only [embeddedMatrixStage_center, M.compatible]

/-- Any centered matrix vector is represented by a trace-zero matrix in the
same stage. -/
theorem embeddedMatrixStage_center_trace_zero (s : ℕ) (a : Matrix (A s) (A s) ℂ) :
    ∃ b : Matrix (A s) (A s) ℂ, Matrix.trace b = 0 ∧
      (embeddedMatrixStage τ V L hinner hleft M s).center b =
        (embeddedMatrixStage τ V L hinner hleft M s).center a := by
  let c : ℂ := (Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace a
  refine ⟨a - c • 1, ?_, ?_⟩
  · have hn : (Fintype.card (A s) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, c]
    field_simp
    ring
  · change tracialCenter V (M.embedding s (a - c • 1)) = tracialCenter V (M.embedding s a)
    rw [map_sub (M.embedding s), map_smul (M.embedding s), map_one (M.embedding s),
      map_sub, map_smul, tracialCenter_one,
      smul_zero, sub_zero]

/-- Centered-stage density follows from full-stage density and the actual
orthogonal projection; it is not an extra tower hypothesis. -/
theorem embeddedMatrixStage_center_dense :
    Dense (⋃ s, centeredMatrixStage (embeddedMatrixStage τ V L hinner hleft M) s) := by
  let P := (centeredSubspace (V 1)).orthogonalProjectionOnto
  have hP : Function.Surjective P := by
    intro x
    exact ⟨x, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  apply hP.denseRange.dense_of_mapsTo P.continuous M.dense
  intro x hx
  obtain ⟨s, a, rfl⟩ := Set.mem_iUnion.mp hx
  obtain ⟨b, hb, heq⟩ := embeddedMatrixStage_center_trace_zero τ V L hinner hleft M s a
  apply Set.mem_iUnion.mpr
  exact ⟨s, b, hb, heq⟩

variable [StarModule ℂ R]
  (htrace : ∀ a b, τ (a * b) = τ (b * a))
  (hdense : DenseRange V) (S : RealTracialSequence τ)

/-- Real algebra vectors give the actual fixed orthonormal sequence in the
centered tracial Hilbert space. -/
def realTracialHilbertSequence (n : ℕ) : centeredSubspace (V 1) :=
  tracialCenter V (S.vector n)

include hinner in
omit [CompleteSpace E] [StarModule ℂ R] in
@[simp] theorem coe_realTracialHilbertSequence (n : ℕ) :
    (realTracialHilbertSequence τ V S n : E) = V (S.vector n) :=
  coe_tracialCenter_of_trace_zero τ V hinner _ (S.trace_zero n)

include hinner in
omit [CompleteSpace E] [StarModule ℂ R] in
theorem realTracialHilbertSequence_orthonormal :
    Orthonormal ℂ (realTracialHilbertSequence τ V S) := by
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℂ (realTracialHilbertSequence τ V S i : E)
    (realTracialHilbertSequence τ V S j : E) = _
  rw [coe_realTracialHilbertSequence τ V hinner, coe_realTracialHilbertSequence τ V hinner,
    hinner, S.inner]

theorem realTracialHilbertSequence_fixed (n : ℕ) :
    centeredTracialConjugation τ V hinner htrace hdense
      (realTracialHilbertSequence τ V S n) = realTracialHilbertSequence τ V S n := by
  apply Subtype.ext
  change tracialConjugation τ V hinner htrace hdense
    (realTracialHilbertSequence τ V S n : E) = (realTracialHilbertSequence τ V S n : E)
  rw [coe_realTracialHilbertSequence τ V hinner, tracialConjugation_apply_vector,
    S.selfadjoint]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SmallFreeCornerTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entire small-corner construction is transported together through
the chosen free-position embedding, so the Haar unitary and reflection
retain the same support projection as the matrix frame. -/

noncomputable section
namespace KadisonSimilarity

variable {A B α : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [Fintype α] [DecidableEq α]
  (φ : A →⋆ₐ[ℂ] B)

def MatrixUnitColumnFamily.map (F : MatrixUnitColumnFamily A α) :
    MatrixUnitColumnFamily B α where
  corner := φ F.corner
  corner_projection := F.corner_projection.map φ
  column i := φ (F.column i)
  initial i j := by
    rw [← map_star, ← map_mul, F.initial]
    split_ifs <;> simp only [map_zero]
  resolution := by
    simpa only [map_sum, map_mul, map_star, map_one] using congrArg φ F.resolution
  base := F.base
  base_column := congrArg φ F.base_column

variable (τA : A →ₗ[ℂ] ℂ) (τB : B →ₗ[ℂ] ℂ)
  (hφ : ∀ a, τB (φ a) = τA a)

def TracialMatrixUnitColumnFamily.map (F : TracialMatrixUnitColumnFamily τA α) :
    TracialMatrixUnitColumnFamily τB α where
  toMatrixUnitColumnFamily := F.toMatrixUnitColumnFamily.map φ
  trace_corner := (hφ _).trans F.trace_corner

variable {s : ℝ}

/-- A single embedding carries every piece of the small-corner data, with
the original numerical cutoff unchanged. -/
def SmallFreeCornerData.transport (Q : SmallFreeCornerData τA s) :
    SmallFreeCornerData τB s where
  size := Q.size
  size_pos := Q.size_pos
  frame := Q.frame.map φ τA τB hφ
  trace := Q.trace
  trace_pos := Q.trace_pos
  trace_lt := Q.trace_lt
  corner_trace := (hφ _).trans Q.corner_trace
  half := Q.half.transport φ hφ
  haar := transportedCornerUnitary φ Q.haar
  moments := Q.moments.transport φ τA τB hφ Q.haar

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixCovariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.crossMultiplicitySlice_zero _root_.OAI.KadisonSimilarity.hilbertTensorInsert_apply _root_.OAI.KadisonSimilarity.hilbertTensorLift_insert _root_.OAI.KadisonSimilarity.hilbertTensorRightInsert_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensorInsert _root_.OAI.KadisonSimilarity.multiplicitySlice_zero _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_hilbertTensorInsert _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.tensorSlice_insert _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- The tensor power of an actual Hilbert-space isometry. -/
def algebraicTensorWordIsometry (g : F →ₗᵢ[ℂ] F) :
    (n : ℕ) → TensorWord F n →ₗᵢ[ℂ] TensorWord F n
  | 0 => LinearIsometry.id
  | n + 1 => TensorProduct.mapIsometry g (algebraicTensorWordIsometry g n)

theorem algebraicTensorWordIsometry_apply (g : F →ₗᵢ[ℂ] F) {n : ℕ} (x : Fin n → F) :
    algebraicTensorWordIsometry g n (tensorWord x) = tensorWord (fun i => g (x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change g (x 0) ⊗ₜ[ℂ] algebraicTensorWordIsometry g n (tensorWord (Fin.tail x)) = _
    rw [ih]
    rfl

def completedTensorWordIsometry (g : F →ₗᵢ[ℂ] F) (n : ℕ) :
    CompletedTensorWord F n →ₗᵢ[ℂ] CompletedTensorWord F n :=
  (algebraicTensorWordIsometry g n).completion

@[simp] theorem completedTensorWordIsometry_apply (g : F →ₗᵢ[ℂ] F) {n : ℕ}
    (x : Fin n → F) :
    completedTensorWordIsometry g n (completedTensorWord x) =
      completedTensorWord (fun i => g (x i)) := by
  change (algebraicTensorWordIsometry g n).completion (tensorWord x) = _
  rw [LinearIsometry.completion_apply_coe, algebraicTensorWordIsometry_apply]
  rfl

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def endpointTensorIsometry (p : E →ₗᵢ[ℂ] E) (g : F →ₗᵢ[ℂ] F) (n : ℕ) :
    EndpointTensor E F n →ₗᵢ[ℂ] EndpointTensor E F n :=
  (TensorProduct.mapIsometry p (completedTensorWordIsometry g n)).completion

@[simp] theorem endpointTensorIsometry_apply (p : E →ₗᵢ[ℂ] E) (g : F →ₗᵢ[ℂ] F)
    {n : ℕ} (d : E) (x : Fin n → F) :
    endpointTensorIsometry p g n (endpointWord d x) =
      endpointWord (p d) (fun i => g (x i)) := by
  change (TensorProduct.mapIsometry p (completedTensorWordIsometry g n)).completion
    ((d ⊗ₜ[ℂ] completedTensorWord x : E ⊗[ℂ] CompletedTensorWord F n) :
      UniformSpace.Completion (E ⊗[ℂ] CompletedTensorWord F n)) =
    ((p d ⊗ₜ[ℂ] completedTensorWord (fun i => g (x i)) :
      E ⊗[ℂ] CompletedTensorWord F n) :
      UniformSpace.Completion (E ⊗[ℂ] CompletedTensorWord F n))
  rw [LinearIsometry.completion_apply_coe]
  simp only [TensorProduct.mapIsometry_apply, TensorProduct.map_tmul]
  change ((p d ⊗ₜ[ℂ] completedTensorWordIsometry g n (completedTensorWord x) :
    E ⊗[ℂ] CompletedTensorWord F n) :
    UniformSpace.Completion (E ⊗[ℂ] CompletedTensorWord F n)) = _
  rw [completedTensorWordIsometry_apply]

variable {R : Type v} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [CompleteSpace E] {α : Type*} [Fintype α] [DecidableEq α]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] R)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a)) (hdense : DenseRange V)

/-- Left multiplication followed by the conjugate right multiplication gives
the actual trace-preserving matrix-conjugation isometry. -/
def tracialUnitaryConjugation (u : Matrix.unitaryGroup α ℂ) : E →ₗᵢ[ℂ] E where
  toLinearMap :=
    (((representedMatrixUnitary L ι u).toContinuousLinearMap.comp
      (tracialConjugation τ V hinner htrace hdense).toContinuousLinearMap).comp
      ((representedMatrixUnitary L ι u).toContinuousLinearMap.comp
      (tracialConjugation τ V hinner htrace hdense).toContinuousLinearMap)).toLinearMap
  norm_map' x := by
    change ‖representedMatrixUnitary L ι u
      (tracialConjugation τ V hinner htrace hdense
      (representedMatrixUnitary L ι u (tracialConjugation τ V hinner htrace hdense x)))‖ = _
    simp only [LinearIsometry.norm_map]

include hleft in
@[simp] theorem tracialUnitaryConjugation_apply_vector
    (u : Matrix.unitaryGroup α ℂ) (a : R) :
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u (V a) =
      V (ι (u : Matrix α α ℂ) * a * star (ι (u : Matrix α α ℂ))) := by
  change L (ι (u : Matrix α α ℂ))
    (tracialConjugation τ V hinner htrace hdense
      (L (ι (u : Matrix α α ℂ)) (tracialConjugation τ V hinner htrace hdense (V a)))) = _
  rw [tracialConjugation_apply_vector, hleft, tracialConjugation_apply_vector,
    hleft, star_mul, star_star, mul_assoc]

include hleft in
@[simp] theorem tracialUnitaryConjugation_traceVector (u : Matrix.unitaryGroup α ℂ) :
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u (V 1) = V 1 := by
  have hu : (u : Matrix α α ℂ) * star (u : Matrix α α ℂ) = 1 := u.property.2
  rw [tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense,
    mul_one, ← map_star ι, ← map_mul ι, hu, map_one]

include hleft in
theorem tracialUnitaryConjugation_mem_centered (u : Matrix.unitaryGroup α ℂ)
    (x : centeredSubspace (V 1)) :
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u x ∈ centeredSubspace (V 1) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  calc
    inner ℂ (V 1) (tracialUnitaryConjugation τ V L ι hinner htrace hdense u (x : E)) =
        inner ℂ (V 1) (x : E) := by
      simpa only [tracialUnitaryConjugation_traceVector τ V L ι hinner hleft htrace hdense] using
        (tracialUnitaryConjugation τ V L ι hinner htrace hdense u).inner_map_map (V 1) (x : E)
    _ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property

def centeredUnitaryConjugation (u : Matrix.unitaryGroup α ℂ) :
    centeredSubspace (V 1) →ₗᵢ[ℂ] centeredSubspace (V 1) where
  toFun x := ⟨tracialUnitaryConjugation τ V L ι hinner htrace hdense u x,
    tracialUnitaryConjugation_mem_centered τ V L ι hinner hleft htrace hdense u x⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (tracialUnitaryConjugation τ V L ι hinner htrace hdense u) (x : E) (y : E)
  map_smul' c x := by
    apply Subtype.ext
    exact (tracialUnitaryConjugation τ V L ι hinner htrace hdense u).map_smul c (x : E)
  norm_map' x := (tracialUnitaryConjugation τ V L ι hinner htrace hdense u).norm_map x

/-- The genuine completed endpoint tensor action of a matrix unitary. -/
def tracialMatrixWordAction (u : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    EndpointTensor E (centeredSubspace (V 1)) n →ₗᵢ[ℂ]
      EndpointTensor E (centeredSubspace (V 1)) n :=
  endpointTensorIsometry (tracialUnitaryConjugation τ V L ι hinner htrace hdense u)
    (centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u) n

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CenteredBaseDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace-zero algebra elements are dense in the actual centered base space.
This extends elementary reduced-word identities to completed tensor letters. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)]

/-- The trace-zero algebra elements, with their actual centered Hilbert vectors. -/
def centeredBaseAlgebraVector (a : {a : A // G.trace (a : P) = 0}) :
    centeredSubspace (G.baseVector A 1) := G.baseSymmetryLetter A a.val a.property

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equality of bounded word maps can be tested on actual bounded algebra
letters. This bridges the published product formula to completed word actions. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

attribute [local irreducible] tensorWordSpace TracialCornerGeometry.baseSpace

variable {P H K : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

local instance baseANormed : NormedAddCommGroup (G.baseSpace A) := inferInstance
local instance baseAInner : InnerProductSpace ℂ (G.baseSpace A) := inferInstance
local instance baseDNormed : NormedAddCommGroup (G.baseSpace D) := inferInstance
local instance baseDInner : InnerProductSpace ℂ (G.baseSpace D) := inferInstance
local instance centeredANormed : NormedAddCommGroup (centeredSubspace (G.baseVector A 1)) :=
  inferInstance
local instance centeredAInner : InnerProductSpace ℂ (centeredSubspace (G.baseVector A 1)) :=
  inferInstance
local instance centeredDNormed : NormedAddCommGroup (centeredSubspace (G.baseVector D 1)) :=
  inferInstance
local instance centeredDInner : InnerProductSpace ℂ (centeredSubspace (G.baseVector D 1)) :=
  inferInstance

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The represented left head action follows from the ordinary product
formula in the reduced-word model. It is not extra covariance data. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.actionMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.actionMultiplicityInnerFamily
/-- Left multiplication acts only on the first other-factor endpoint. -/
def tracialWordHeadAction (n : ℕ) (a : D) :
    MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n →L[ℂ]
    MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n :=
  hilbertTensorLift (endpointHeadAction (G.baseRepresentation D a))

end TracialCornerGeometry

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordBase
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vacuum endpoint in degree zero is the actual base Hilbert space.
Consequently the repeated-word action implies base-space invariance; this
is not an additional assumption on the symmetrized operator. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

theorem norm_baseVector_one (hτ : G.trace 1 = 1) : ‖G.baseVector D 1‖ = 1 :=
  norm_tracialTraceVector (G.baseGeometry D).trace (G.baseVector D)
    (G.baseVector_inner D) hτ

local instance baseMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

local instance baseMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable {P H : Type*}
  [CStarAlgebra P]
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  (A D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {I : ℕ → Type*}
  [∀ j, Fintype (I j)]
  [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D)
  (hfaithful : Function.Injective G.vector)

local instance matrixUnitaryCompactSpace (j : ℕ) : CompactSpace (Matrix.unitaryGroup (I j) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi Set.univ fun _ : I j =>
      Set.pi Set.univ fun _ : I j => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  apply hK.of_isClosed_subset (isClosed_unitary (R := Matrix (I j) (I j) ℂ))
  intro x hx k _ l _
  change dist (x k l) 0 ≤ 1
  rw [dist_zero_right]
  have hx' : CStarMatrix.ofMatrix x ∈ unitary (CStarMatrix (I j) (I j) ℂ) := hx
  exact (CStarMatrix.norm_entry_le_norm (M := CStarMatrix.ofMatrix x)).trans
    (le_of_eq (CStarRing.norm_coe_unitary ⟨CStarMatrix.ofMatrix x, hx'⟩))

local instance matrixUnitaryMeasurableSpace (j : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (I j) ℂ) := borel _
local instance matrixUnitaryBorelSpace (j : ℕ) : BorelSpace (Matrix.unitaryGroup (I j) ℂ) := ⟨rfl⟩

/-- Actual normalized Haar measure of the finite matrix unitary group. -/
def tracialMatrixHaarProbability (j : ℕ) : Measure (Matrix.unitaryGroup (I j) ℂ) :=
  Measure.haarMeasure ⊤

instance tracialMatrixHaarProbability_probability (j : ℕ) :
    IsProbabilityMeasure (tracialMatrixHaarProbability (I := I) j) := by
  apply IsProbabilityMeasure.mk
  exact Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts (Matrix.unitaryGroup (I j) ℂ)))

instance tracialMatrixHaarProbability_leftInvariant (j : ℕ) :
    (tracialMatrixHaarProbability (I := I) j).IsMulLeftInvariant :=
  inferInstanceAs (Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (I j) ℂ))).IsMulLeftInvariant

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialFreeCornerModel
attribute [-instance] _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining word and reflection data in the free-corner argument are
constructed from the local published reduced-product model and ordinary
generated-algebra density. In particular neither an invariant word
decomposition nor freeness of the compressed factors is an input. -/

noncomputable section
namespace KadisonSimilarity

universe u v

variable {P : Type u} [CStarAlgebra P]

/-- The canonical half projection of a selfadjoint involution. -/
theorem symmetryHalfProjectionProof {D : StarSubalgebra ℂ P} (d : D)
    (hdstar : star d = d) (hdsq : d * d = 1) :
    IsStarProjection (dihedralHalfProjection
      (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) := by
  apply isStarProjection_dihedralHalfProjection
  · exact congrArg (fun x : D => (x : P)) hdstar
  · apply Units.ext
    exact congrArg (fun x : D => (x : P)) hdsq

/-- The half projection belongs to every star subalgebra containing its
reflection. -/
theorem symmetryHalfProjection_mem (C : StarSubalgebra ℂ P)
    {D : StarSubalgebra ℂ P} (d : D) (hdsq : d * d = 1) (hdC : (d : P) ∈ C) :
    dihedralHalfProjection
      (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ C :=
  C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2 : ℂ)

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SquareArrayPadding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

section Padding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

/-- An operator on the smaller array, extended by zero on all new coordinates. -/
def padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) :
    HilbertCopies H m →L[ℂ] HilbertCopies H m :=
  (copyEmbeddingMap e).comp (Y.comp (copyRestriction e))

end Padding

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteProjectionComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem concrete_projection_trace_mono (τ : TracialRepresentation M)
    {p q : AlgebraProjection M} (hpq : p ≤ q) :
    (τ.trace p.val).re ≤ (τ.trace q.val).re := by
  have hd : IsStarProjection (q.val - p.val) :=
    p.property.sub_of_mul_eq_right q.property hpq
  have ht := projection_trace_sq τ (q.val - p.val) hd
  rw [trace_sub, Complex.sub_re] at ht
  nlinarith [sq_nonneg (τ.norm₂ (q.val - p.val))]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_CornerTraceScaling
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instRing _root_.OAI.PopaCorner.instStarOrderedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.BoundedHochschild.CentralCorner.compressMap_coe _root_.OAI.BoundedHochschild.CentralCorner.compressMap_includeMap _root_.OAI.BoundedHochschild.CentralCorner.extend_apply _root_.OAI.BoundedHochschild.CentralCorner.includeMap_apply _root_.OAI.BoundedHochschild.CentralCorner.restrict_apply _root_.OAI.BoundedHochschild.KadisonRingrose.nestedCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.unitCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.unitCornerTrace_apply _root_.OAI.HochschildPatching.ofCornerUnitary_coe _root_.OAI.HochschildPatching.ofCornerUnitary_support _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.sourceCornerHom_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem original_norm_bound_of_corner {q a : Corner p hp} {δ : ℝ}
    (h : ‖(cornerTrace p hp τ).toPreGNS a‖ ^ 2 < δ * (cornerTrace p hp τ q).re) :
    ‖τ.toPreGNS (a : A)‖ ^ 2 < δ * (τ (q : A)).re := by
  rw [HochschildQuantization.corner_norm_sq, HochschildQuantization.corner_trace_re] at h
  have hh := mul_lt_mul_of_pos_left h ht
  have hl (r : ℝ) : (τ p).re * ((τ p).re⁻¹ * r) = r := by
    rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  have hr (r : ℝ) : (τ p).re * (δ * ((τ p).re⁻¹ * r)) = δ * r := by
    field_simp [ht.ne']
  rwa [hl, hr] at hh

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_DiffuseProjectionStructure
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absence of nonzero abelian projections supplies the exact diffuse
projection condition used by the increasing matrix-subfactor construction. -/

noncomputable section
namespace KadisonSimilarity

open BoundedHochschild.KadisonRingrose
open scoped ComplexOrder

universe u
variable {A X : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem diffuse_projections_of_no_abelian_projection
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (hno : ∀ p : A, FinitePathMain.AbelianProjection p → p = 0) :
    ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  have hII : PopaTypeII.NoTypeICentralPart A := by
    intro z hz _ hz0 hI
    obtain ⟨q, hq, _, hq0, hab⟩ := hI z hz le_rfl hz0
    exact hq0 (hno q (finitePath_abelian_of_popa hq hab))
  intro p hp hp0
  obtain ⟨v, horth, hsum⟩ := typeII_projection_halving e hII hp
  have hvi0 : v.initial ≠ 0 := by
    intro hzero
    have hv : (v : A) = 0 := by simpa only [hzero, mul_zero] using v.mul_initial.symm
    apply hp0
    simpa only [HochschildComparison.PartialIso.initial,
      HochschildComparison.PartialIso.final, hv, star_zero, zero_mul, add_zero] using hsum.symm
  have hvinp : v.initial ≠ p := by
    intro heq
    have hfinal : v.final = 0 := by
      have h := hsum
      rw [heq] at h
      exact add_eq_left.mp h
    have hv : (v : A) = 0 := by simpa only [hfinal, zero_mul] using v.final_mul.symm
    apply hvi0
    simp only [HochschildComparison.PartialIso.initial, hv, star_zero, zero_mul]
  have horth' : v.final * v.initial = 0 := by
    simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq,
      v.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star horth
  refine ⟨v.initial, v.initial_proj, hvi0, hvinp, ?_, ?_⟩
  · rw [← hsum, add_mul, v.initial_proj.isIdempotentElem.eq, horth', add_zero]
  · rw [← hsum, mul_add, v.initial_proj.isIdempotentElem.eq, horth, add_zero]

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

omit [PartialOrder B] [StarOrderedRing B] in
lemma wordCoeff_norm_le_bound (F : I → B) {C : ℝ} (hC : 1 ≤ C)
    (hF : ∀ i, ‖F i‖ ≤ C) (a : Option I) : ‖wordCoeff F a‖ ≤ C := by
  cases a with
  | none => exact (IsStarProjection.norm_le (1 : B) (IsStarProjection.one B)).trans hC
  | some i => exact hF i

lemma gnsTendsto_wordCoeff {F : J → I → B} {G : I → B} {l : Filter J}
    (h : ∀ i, GNSTendsto τ (fun j => F j i) l (G i)) (a : Option I) :
    GNSTendsto τ (fun j => wordCoeff (F j) a) l (wordCoeff G a) := by
  cases a with
  | none => exact GNSTendsto.const τ 1 l
  | some i => exact h i

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

lemma wordCoeff_smul_family (F : I → B) (c : I → ℂ) (a : Option I) :
    wordCoeff (fun i => c i • F i) a = wordScalar c a • wordCoeff F a := by
  cases a <;> simp [wordCoeff, wordScalar]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialGeneratedNormalClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- The trace-vector image of a concrete subalgebra. -/
def subalgebraTraceVectors (τ : TracialRepresentation M) (N : VonNeumannAlgebra H) : Set H :=
  baseVector τ '' {a : M.toStarSubalgebra | (a : H →L[ℂ] H) ∈ N}

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixCenter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Density of full matrix stages forces the center of the original
faithful tracial algebra to be scalar. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

include M in
theorem central_stage_pairing (c : P)
    (hc : ∀ a : P, a * c = c * a) (j : ℕ) (a : Matrix (I j) (I j) ℂ) :
    G.trace (c * M.embedding j a) = G.trace c * G.trace (M.embedding j a) := by
  let F : Matrix (I j) (I j) ℂ →ₗ[ℂ] ℂ :=
    G.trace.comp ((LinearMap.mulLeft ℂ c).comp (M.embedding j).toLinearMap)
  have ht (x y : Matrix (I j) (I j) ℂ) : F (x * y) = F (y * x) := by
    change G.trace (c * M.embedding j (x * y)) = G.trace (c * M.embedding j (y * x))
    rw [map_mul (M.embedding j) x y, map_mul (M.embedding j) y x]
    calc
      _ = G.trace ((c * M.embedding j x) * M.embedding j y) := by rw [mul_assoc]
      _ = G.trace (M.embedding j y * (c * M.embedding j x)) := G.tracial _ _
      _ = _ := by rw [← mul_assoc, hc, mul_assoc]
  have h := matrix_tracial_functional F ht a
  change G.trace (c * M.embedding j a) =
    (Fintype.card (I j) : ℂ)⁻¹ * G.trace (c * M.embedding j 1) * Matrix.trace a at h
  rw [map_one, mul_one] at h
  rw [h, M.trace_embedding]
  ring

include M in
/-- No nonscalar central element survives density of the full matrix stages. -/
theorem central_eq_trace_smul_one (hf : Function.Injective G.vector)
    (c : P) (hc : ∀ a : P, a * c = c * a) : c = G.trace c • (1 : P) := by
  apply hf
  rw [map_smul]
  apply ext_inner_left ℂ
  intro ξ
  have hs : closure (⋃ j, Set.range (fun a => G.vector (M.embedding j a))) ⊆
      {η | inner ℂ η (G.vector c) = inner ℂ η (G.trace c • G.vector 1)} := by
    apply closure_minimal ?_ (isClosed_eq (by fun_prop) (by fun_prop))
    intro η hη
    obtain ⟨j, a, rfl⟩ := Set.mem_iUnion.mp hη
    change inner ℂ (G.vector (M.embedding j a)) (G.vector c) = _
    rw [inner_smul_right, G.inner_vector, G.inner_vector, mul_one, G.tracial]
    simpa only [map_star] using G.central_stage_pairing M c hc j (star a)
  exact hs (M.dense ξ)

include M in
theorem scalar_center_of_matrix_tower (hf : Function.Injective G.vector) :
    ∀ c : P, (∀ a : P, a * c = c * a) → ∃ z : ℂ, c = z • (1 : P) := by
  intro c hc
  exact ⟨G.trace c, G.central_eq_trace_smul_one M hf c hc⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end


