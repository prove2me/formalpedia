-- Prove2me | Definitions.Def_OAIQ075A011
-- name    : OAIQ075A011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:03:02.824793+00:00
-- url     : https://prove2.me/theorems/ec5f0f0e-a242-47fc-ad9b-bfae1691b2a4
-- title:
--   Definitions bundle OAIQ075A011 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 185 declarations of OpenAI's Lean: 55 definitions, 1 inductive type or structure, 6 instances and 123 theorems. The definitions and types are `OAI.KadisonSimilarity.HalfTraceProjectionData.transport`, `OAI.KadisonSimilarity.LabelPairingExpansion`, `OAI.KadisonSimilarity.OrthogonalWordLevels.block`, `OAI.KadisonSimilarity.RepeatedLetterWords`, `OAI.KadisonSimilarity.ScalarKaplanskyClosure`, `OAI.KadisonSimilarity.SymmetryWordAlgebra.spanStarAlgebra`, `OAI.KadisonSimilarity.SymmetryWordAlgebra.wordSpan`, `OAI.KadisonSimilarity.TracialCornerGeometry.cornerInclusion`, `OAI.KadisonSimilarity.TracialExpectation.comapEquiv`, `OAI.KadisonSimilarity.amplifyAlgHom`, `OAI.KadisonSimilarity.binarySpectralResidual`, `OAI.KadisonSimilarity.boundedMatrixHom`, `OAI.KadisonSimilarity.centeredSymmetryWordProducts`, `OAI.KadisonSimilarity.centralProjectionTwirl`, `OAI.KadisonSimilarity.centralReflection`, `OAI.KadisonSimilarity.centralSignHom`, `OAI.KadisonSimilarity.centralSignRepresentation`, `OAI.KadisonSimilarity.centralUnitarySubgroup`, `OAI.KadisonSimilarity.commutantDerivation`, `OAI.KadisonSimilarity.commutativeCyclicIsometry`, `OAI.KadisonSimilarity.conullProjectionFiber`, `OAI.KadisonSimilarity.coordinateIntertwinerData`, `OAI.KadisonSimilarity.crossPairingEquiv`, `OAI.KadisonSimilarity.cycleConstantLabelingsEquiv`, `OAI.KadisonSimilarity.cyclePoolIndex`, `OAI.KadisonSimilarity.cyclicOrbitColumn`, `OAI.KadisonSimilarity.diagonalField`, `OAI.KadisonSimilarity.dyadicPhase`, `OAI.KadisonSimilarity.dyadicRank`, `OAI.KadisonSimilarity.endpointMatching`, `OAI.KadisonSimilarity.finiteCopyIsometry`, `OAI.KadisonSimilarity.finiteCopyProjection`, `OAI.KadisonSimilarity.l2CoordinateIsometry`, `OAI.KadisonSimilarity.l2CoordinateProjection`, `OAI.KadisonSimilarity.l2FiniteAssembly`, `OAI.KadisonSimilarity.l2FiniteCoordinates`, `OAI.KadisonSimilarity.l2FiniteCopiesEquiv`, `OAI.KadisonSimilarity.l2MapIsometry`, `OAI.KadisonSimilarity.matchingSplitEquiv`, `OAI.KadisonSimilarity.matrixRepresentation` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonSimilarity_Derivation_CyclicColumnTests`, `KadisonSimilarity_Derivation_CyclicCommutativeModel`, `KadisonSimilarity_Derivation_CyclicDecomposition`, `KadisonSimilarity_Derivation_CyclicSpectralSum`, `KadisonSimilarity_Derivation_FiniteDerivationColumns`, `KadisonSimilarity_Derivation_RectangularDerivations`, `KadisonSimilarity_FreeProduct_ConcreteHaarDischarge`, `KadisonSimilarity_FreeProduct_HaarCornerLetters`, `KadisonSimilarity_FreeProduct_OrthogonalWordLevels`, `KadisonSimilarity_FreeProduct_PropagationTheorem`, `KadisonSimilarity_FreeProduct_ReducedWordAutomorphisms`, `KadisonSimilarity_FreeProduct_SmallFreeCornerData`, `KadisonSimilarity_FreeProduct_SpectralArc`, `KadisonSimilarity_FreeProduct_SymmetryWordAlgebra`, `KadisonSimilarity_FreeProduct_SymmetryWordRange`, `KadisonSimilarity_FreeProduct_TracialDihedralColumns`, `KadisonSimilarity_Representation_AEColumnOperator`, `KadisonSimilarity_Representation_CentralSymmetrization`, `KadisonSimilarity_Representation_ClosedFamilySpan`, `KadisonSimilarity_Representation_CommonCommutantFields`, `KadisonSimilarity_Representation_CommonSpectralMeasure`, `KadisonSimilarity_Representation_CompressedFieldNorm`, `KadisonSimilarity_Representation_ConullFieldExtension`, `KadisonSimilarity_Representation_ConullRepresentationExtension`, `KadisonSimilarity_Representation_DiagonalFieldAction`, `KadisonSimilarity_Representation_DiagonalFieldAlgebra`, `KadisonSimilarity_Representation_DiagonalOperatorField`, `KadisonSimilarity_Representation_DyadicPhases`, `KadisonSimilarity_Representation_GlobalFiberRestriction`, `KadisonSimilarity_Representation_IntertwinerExtension`, `KadisonSimilarity_Representation_JointFiberRestriction`, `KadisonSimilarity_Representation_L2FiniteCopies`, `KadisonSimilarity_Representation_L2HilbertSum`, `KadisonSimilarity_Representation_L2ScalarIntertwining`, `KadisonSimilarity_Representation_NonunitalRangeRepresentation`, `KadisonSimilarity_Representation_NormalFactorGeneration`, `KadisonSimilarity_Representation_ProjectionCentralData`, `KadisonSimilarity_Representation_ProjectionFieldReduction`, `KadisonSimilarity_Representation_ScalarHilbertSeparability`, `KadisonSimilarity_Representation_ScalarLocalizationLimit`, `KadisonSimilarity_Representation_SpectralDensityIsometry`, `KadisonSimilarity_Representation_SpectralIntertwining`, `KadisonSimilarity_Representation_SpectralStepDischarge`, `KadisonSimilarity_Representation_SupportedFiberAlgebra`, `KadisonSimilarity_Representation_UnitizationFiberClosure`, `KadisonSimilarity_Representation_UnitizationProjection`, `KadisonSimilarity_Similarity_AmplifyExponential`, `KadisonSimilarity_Similarity_ArvesonCompleteNorm`, `KadisonSimilarity_Similarity_CompletelyBounded`, `KadisonSimilarity_Similarity_CompletelyBoundedImplementation`, `KadisonSimilarity_Tensor_EndpointPairings`, `KadisonSimilarity_Tensor_InvariantCycles`, `KadisonSimilarity_Tensor_InvariantTensors`, `KadisonSimilarity_Tensor_TensorClassification`, `KadisonSimilarity_Tensor_TensorPairings`, `KadisonSimilarity_Tracial_BoundedMatrixHom`, `KadisonSimilarity_Tracial_ConcreteTracialExpectation`, `KadisonSimilarity_Tracial_FullColumnTheorem`, `KadisonSimilarity_Tracial_TracialCornerTransport`, `KadisonSimilarity_Tracial_TracialHalfProjectionData`, `KadisonSimilarity_Tracial_TracialMatrixTower`, `KadisonSimilarity_Tracial_TracialNormalSpan`, `KadisonSimilarity_Tracial_TracialSubalgebraTransfer`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A001`, `OAIQ075A003`, `OAIQ075A004`, `OAIQ075A005` and `OAIQ075A006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A017` and `OAIQ075A018`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A001
import Definitions.Def_OAIQ075A003
import Definitions.Def_OAIQ075A004
import Definitions.Def_OAIQ075A005
import Definitions.Def_OAIQ075A006

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompletelyBounded
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- Operator matrices act as a star algebra homomorphism on the Hilbert sum. -/
def matrixRepresentation (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) →⋆ₐ[ℂ]
      (HilbertCopies H n →L[ℂ] HilbertCopies H n) :=
  (operatorMatrixRepresentation n).comp
    (CStarMatrix.ofMatrixStarAlgEquiv.symm :
      CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) ≃⋆ₐ[ℂ]
        Matrix (Fin n) (Fin n) (H →L[ℂ] H)).toStarAlgHom

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_RectangularDerivations
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.listOrbitSum_append _root_.OAI.KadisonSimilarity.listOrbitSum_nil _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.KadisonSimilarity.similarityRepresentation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem norm_mapCopies_le (T : K →L[ℂ] F) (n : ℕ) : ‖mapCopies T n‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro ξ
  have hs : ‖mapCopies T n ξ‖ ^ 2 ≤ (‖T‖ * ‖ξ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i : Fin n, ‖mapCopies T n ξ i‖ ^ 2 ≤
          ∑ i : Fin n, (‖T‖ * ‖ξ i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [mapCopies_apply]
        exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
      _ = ‖T‖ ^ 2 * (∑ i : Fin n, ‖ξ i‖ ^ 2) := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
      _ = (‖T‖ * ‖ξ‖) ^ 2 := by rw [← PiLp.norm_sq_eq_of_L2]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg ξ))).mp hs

def rectangularInl : F →L[ℂ] RectangularSum F K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ F K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ F K)

def rectangularInr : K →L[ℂ] RectangularSum F K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ F K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ F K)

@[simp] theorem rectangularInl_apply (x : F) :
    (rectangularInl (K := K) x).fst = x ∧ (rectangularInl (K := K) x).snd = 0 := by
  simp [rectangularInl]

@[simp] theorem rectangularInr_apply (x : K) :
    (rectangularInr (F := F) x).fst = 0 ∧ (rectangularInr (F := F) x).snd = x := by
  simp [rectangularInr]

/-- The diagonal plus one upper-right block. -/
def rectangularTriangular (ρ : F →L[ℂ] F) (δ : K →L[ℂ] F) (σ : K →L[ℂ] K) :
    RectangularSum F K →L[ℂ] RectangularSum F K :=
  rectangularInl.comp (ρ.comp (WithLp.fstL 2 ℂ F K)) +
    rectangularInl.comp (δ.comp (WithLp.sndL 2 ℂ F K)) +
    rectangularInr.comp (σ.comp (WithLp.sndL 2 ℂ F K))

@[simp] theorem rectangularTriangular_fst (ρ : F →L[ℂ] F) (δ : K →L[ℂ] F)
    (σ : K →L[ℂ] K) (x : RectangularSum F K) :
    (rectangularTriangular ρ δ σ x).fst = ρ x.fst + δ x.snd := by
  simp [rectangularTriangular, rectangularInl, rectangularInr]

@[simp] theorem rectangularTriangular_snd (ρ : F →L[ℂ] F) (δ : K →L[ℂ] F)
    (σ : K →L[ℂ] K) (x : RectangularSum F K) :
    (rectangularTriangular ρ δ σ x).snd = σ x.snd := by
  simp [rectangularTriangular, rectangularInl, rectangularInr]

variable [CompleteSpace F] [CompleteSpace K]

open scoped CStarAlgebra

/-- The bounded unital triangular homomorphism of a rectangular derivation. -/
def rectangularRepresentation (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) :
    BoundedUnitalHom A (RectangularSum F K) := by
  let f : A →ₗ[ℂ] (RectangularSum F K →L[ℂ] RectangularSum F K) :=
    { toFun := fun a => rectangularTriangular (ρ a) (δ a) (σ a)
      map_add' := by
        intro a b
        ext x
        apply (WithLp.equiv 2 (F × K)).injective
        apply Prod.ext
        · simp; abel
        · simp
      map_smul' := by
        intro c a
        ext x
        apply (WithLp.equiv 2 (F × K)).injective
        apply Prod.ext <;> simp [smul_add] }
  have hone : f 1 = 1 := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp [f, rectangularDerivation_map_one ρ σ δ hδ]
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext
    · simp [f, hδ, mul_apply_eq_comp, map_add]; abel
    · simp [f, mul_apply_eq_comp]
  refine ⟨AlgHom.ofLinearMap f hone hmul, ?_⟩
  change Continuous (fun a => rectangularTriangular (ρ a) (δ a) (σ a))
  unfold rectangularTriangular
  exact ((((map_continuous ρ).clm_comp_const _).const_clm_comp _).add
    ((δ.continuous.clm_comp_const _).const_clm_comp _)).add
    (((map_continuous σ).clm_comp_const _).const_clm_comp _)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompletelyBoundedImplementation
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- The diagonal of the triangular representation is a star representation. -/
def rectangularDiagonalStarHom (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : A →⋆ₐ[ℂ] (RectangularSum F K →L[ℂ] RectangularSum F K) :=
  { (rectangularRepresentation ρ σ 0 (by intros; simp)).1 with
    map_star' := by
      intro a
      change rectangularTriangular (ρ (star a)) 0 (σ (star a)) =
        (rectangularTriangular (ρ a) 0 (σ a)).adjoint
      apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
      intro x y
      change inner ℂ (rectangularTriangular (ρ (star a)) 0 (σ (star a)) x).fst y.fst +
          inner ℂ (rectangularTriangular (ρ (star a)) 0 (σ (star a)) x).snd y.snd =
        inner ℂ x.fst (rectangularTriangular (ρ a) 0 (σ a) y).fst +
          inner ℂ x.snd (rectangularTriangular (ρ a) 0 (σ a) y).snd
      rw [rectangularTriangular_fst, rectangularTriangular_snd,
        rectangularTriangular_fst, rectangularTriangular_snd]
      simp only [zero_apply, add_zero, map_star,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] }

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem rectangularDiagonalStarHom_apply
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : A) :
    rectangularDiagonalStarHom ρ σ a = rectangularTriangular (ρ a) 0 (σ a) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FullColumnTheorem
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

section CornerCommutator

variable {C F K : Type*} [CStarAlgebra C]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The rectangular Leibniz rule follows from composition, with no derivation
hypothesis on the corner operator. -/
theorem cornerCommutator_leibniz (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (G : K →L[ℂ] F) (a b : C) :
    cornerCommutator ρ σ G (a * b) =
      (ρ a).comp (cornerCommutator ρ σ G b) +
        (cornerCommutator ρ σ G a).comp (σ b) := by
  ext x
  simp [mul_apply_eq_comp]

end CornerCommutator

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralStepDischarge
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete spectral cut projections

We construct the spectral cuts from the closed range of the positive part.
The construction takes place in the represented Hilbert space; bicommutant
closure proves membership in the given von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Repeated binary rounding, performed inside the given operator algebra. -/
def binarySpectralResidual (A : H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => A
  | k + 1 => binarySpectralResidual A k -
      binarySpectralCorrection (binarySpectralResidual A k) (binarySpectralRadius A k)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicColumnTests
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

def cyclicOrbitColumn (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) : HilbertCopies K n :=
  WithLp.toLp 2 (fun i => σ (a i) Ω)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cyclicOrbitColumn_apply (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) (i : Fin n) : cyclicOrbitColumn σ Ω a i = σ (a i) Ω := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicCommutativeModel
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar spectral coordinates for one cyclic subspace of a commutative
representation. These are the components of the central Hilbert model. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonSimilarity.spectralMeasurableSpace
attribute [local instance] OAI.KadisonSimilarity.spectralBorelSpace
instance commutativeVectorMeasure_regular (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    (commutativeVectorMeasure π ξ).Regular :=
  inferInstanceAs ((VectorSpectralMeasure.measure (commutativeSpectralCalculus π) ξ).Regular)

def commutativeCyclicIsometry (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Lp ℂ 2 (commutativeVectorMeasure π ξ) →ₗᵢ[ℂ] H :=
  VectorSpectralMeasure.cyclicIsometry (commutativeSpectralCalculus π) ξ

theorem commutativeCyclicIsometry_range
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Set.range (commutativeCyclicIsometry π ξ) = closure (Set.range (fun a : A => π a ξ)) := by
  change Set.range (VectorSpectralMeasure.cyclicMap (commutativeSpectralCalculus π) ξ) = _
  rw [VectorSpectralMeasure.cyclicMap_range]
  congr 1
  apply Set.Subset.antisymm
  · rintro _ ⟨f, rfl⟩
    exact ⟨(gelfandStarTransform A).symm f, rfl⟩
  · rintro _ ⟨a, rfl⟩
    refine ⟨gelfandStarTransform A a, ?_⟩
    change π ((gelfandStarTransform A).symm (gelfandStarTransform A a)) ξ = π a ξ
    rw [StarAlgEquiv.symm_apply_apply]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_FiniteDerivationColumns
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-column passage from the uniform commutator estimate to complete
boundedness of a derivation. The finite implementers need no uniform norm bound;
only their scalar commutator bounds are used. -/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology

variable {A H I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The scalar specialization of matrix Kaplansky density and the C*-quotient
norm used in the final derivation argument (Blackadar, I.9.1.3). -/
def ScalarKaplanskyClosure (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (P : VonNeumannAlgebra H) : Prop :=
  ∀ (V : H →L[ℂ] H) (d : ℝ), 0 ≤ d →
    (∀ a, ‖commutator V (σ a)‖ ≤ d * ‖a‖) → scalarCommutatorNorm P V ≤ d

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicDecomposition
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- Orthogonality to one reducing cyclic subspace persists on the whole orbit
of a vector, including its closure. -/
theorem orbitClosure_le_orthogonal (N : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H)
    (hξ : ξ ∈ (orbitClosure N η).toSubmodule.orthogonal) :
    (orbitClosure N ξ).toSubmodule ≤ (orbitClosure N η).toSubmodule.orthogonal := by
  apply (LinearMap.range (orbitLinearMap N ξ)).topologicalClosure_minimal ?_
    (Submodule.isClosed_orthogonal _)
  rintro x ⟨a, rfl⟩
  intro y hy
  change inner ℂ y ((a : H →L[ℂ] H) ξ) = 0
  rw [← ContinuousLinearMap.adjoint_inner_left]
  apply hξ
  exact orbitClosure_invariant N η (star a) y hy

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantTensors
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix-unit isolation of invariant-tensor coefficients

The permutation contractions are given by their coordinate sums. Their
normalization is the number of cycles, including fixed points. We prove the
matrix-unit isolation and uniqueness steps in the invariant-intertwiner
argument. Schur--Weyl spanning is expressed as a multilinear-form property.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

section BlockAmplification

variable {β : Type*} [Fintype β] [DecidableEq β]

omit [DecidableEq ι] [Fintype β] [DecidableEq β] in
theorem cycleConstantLabelings_eq_of_sameCycle (π : Equiv.Perm ι)
    (f : CycleConstantLabelings π β) {i j : ι} (h : π.SameCycle i j) : f.1 i = f.1 j := by
  have hit (n : ℕ) (i : ι) : f.1 ((π ^ n) i) = f.1 i := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, f.2]
      exact ih
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact (hit n i).symm

/-- A concrete equivalence, rather than an assumed formula for orbit counts. -/
def cycleConstantLabelingsEquiv (π : Equiv.Perm ι) :
    CycleConstantLabelings π β ≃ (Quotient (Equiv.Perm.SameCycle.setoid π) → β) where
  toFun f := Quotient.lift f.1 (fun _ _ h => cycleConstantLabelings_eq_of_sameCycle π f h)
  invFun g := ⟨fun i => g ⟦i⟧, fun i => congrArg g (Quotient.sound
    ((show π.SameCycle i (π i) from ⟨1, by simp⟩).symm))⟩
  left_inv _ := rfl
  right_inv g := by
    funext q
    induction q using Quotient.inductionOn
    rfl

end BlockAmplification

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantCycles
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

noncomputable instance permutationCyclesFintype (π : Equiv.Perm ι) :
    Fintype (PermutationCycles π) := Fintype.ofFinite _

instance endpointPairingDecidable (π : Equiv.Perm ι) (i₀ : ι) :
    Decidable (EndpointPairing π i₀) := by
  unfold EndpointPairing Function.Involutive
  infer_instance

/-- A cross pairing determines the bijection indexing its contraction. -/
def crossPairingEquiv {k l : ℕ} (π : Equiv.Perm (Fin k ⊕ Fin l))
    (hπ : Function.Involutive π) (hcross : IsCrossPairing π) : Fin k ≃ Fin l where
  toFun i := (hcross.1 i).choose
  invFun j := (hcross.2 j).choose
  left_inv i := by
    have h := hπ (Sum.inl i)
    rw [(hcross.1 i).choose_spec, (hcross.2 _).choose_spec] at h
    exact Sum.inl.inj h
  right_inv j := by
    have h := hπ (Sum.inr j)
    rw [(hcross.2 j).choose_spec, (hcross.1 _).choose_spec] at h
    exact Sum.inr.inj h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorPairings
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hilbert tensor tests excluding same-side pairings

The source and test vectors are finite sums of actual elementary Hilbert
tensors. Their orthonormal summands give the square-root norm growth, whereas
the isolated pairing coefficient grows with the full number of labels.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {k l : ℕ}

/-- The restriction of a pairing expansion to an orthonormal alphabet. This
is the concrete finite-expansion data used by the test, not an invariant
classification hypothesis. -/
def LabelPairingExpansion {J : Type*} [DecidableEq J]
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (h : J → E) (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ) : Prop :=
  ∀ (s : Fin k → J) (t : Fin l → J),
    inner ℂ (completedTensorWord (fun i => h (t i)))
      (Y (completedTensorWord (fun i => h (s i)))) =
      ∑ Q, c Q * pairingLabelKernel Q (Sum.elim s t)

/-- Disjoint countable pools can be selected from one orthonormal sequence. -/
def cyclePoolIndex (P : PerfectMatching (Fin k ⊕ Fin l)) : PermutationCycles P.1 × ℕ → ℕ :=
  fun q => Nat.pair (Fintype.equivFin (PermutationCycles P.1) q.1).val q.2

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorClassification
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

@[simp] theorem crossPairingEquiv_left {k l : ℕ}
    (P : PerfectMatching (Fin k ⊕ Fin l)) (hcross : IsCrossPairing P.1) (i : Fin k) :
    P.1 (Sum.inl i) = Sum.inr (crossPairingEquiv P.1 P.2.1 hcross i) :=
  (hcross.1 i).choose_spec

@[simp] theorem crossPairingEquiv_right {k l : ℕ}
    (P : PerfectMatching (Fin k ⊕ Fin l)) (hcross : IsCrossPairing P.1) (j : Fin l) :
    P.1 (Sum.inr j) = Sum.inl ((crossPairingEquiv P.1 P.2.1 hcross).symm j) :=
  (hcross.2 j).choose_spec

instance crossMatchingFintype (k l : ℕ) :
    Fintype {P : PerfectMatching (Fin k ⊕ Fin l) // IsCrossPairing P.1} :=
  Fintype.ofFinite _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointPairings
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

omit [Fintype ι] [DecidableEq ι] in
theorem matching_rank_ne (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (i : ι) : rank i ≠ rank (P.1 i) :=
  fun h => P.2.2 i (hrank h).symm

/-- The vertices split into a representative and its partner, once per pair. -/
def matchingSplitEquiv (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) :
    MatchingRepresentatives rank P ⊕ MatchingRepresentatives rank P ≃ ι :=
  Equiv.ofBijective (Sum.elim Subtype.val (fun i => P.1 i)) (by
    constructor
    · intro a b hab
      cases a with
      | inl i =>
        cases b with
        | inl j => exact congrArg Sum.inl (Subtype.ext hab)
        | inr j =>
          have hi := i.property
          have hj := j.property
          change i.val = P.1 j.val at hab
          rw [hab, P.2.1] at hi
          omega
      | inr i =>
        cases b with
        | inl j =>
          have hi := i.property
          have hj := j.property
          change P.1 i.val = j.val at hab
          rw [← hab, P.2.1] at hj
          omega
        | inr j => exact congrArg Sum.inr (Subtype.ext (P.1.injective hab))
    · intro i
      by_cases hi : rank i < rank (P.1 i)
      · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
      · have hne := matching_rank_ne rank hrank P i
        have hpi : rank (P.1 i) < rank (P.1 (P.1 i)) := by rw [P.2.1]; omega
        exact ⟨Sum.inr ⟨P.1 i, hpi⟩, P.2.1 i⟩)

omit [Fintype ι] in
@[simp] theorem matchingSplitEquiv_inl (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (i : MatchingRepresentatives rank P) :
    matchingSplitEquiv rank hrank P (Sum.inl i) = i := rfl

omit [Fintype ι] in
@[simp] theorem matchingSplitEquiv_inr (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (i : MatchingRepresentatives rank P) :
    matchingSplitEquiv rank hrank P (Sum.inr i) = P.1 i := rfl

/-- Add a fixed distinguished endpoint to a tail matching. -/
def endpointMatching (P : PerfectMatching ι) : Equiv.Perm (Option ι) :=
  P.1.optionCongr

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem endpointMatching_none (P : PerfectMatching ι) :
    endpointMatching P none = none := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem endpointMatching_some (P : PerfectMatching ι) (i : ι) :
    endpointMatching P (some i) = some (P.1 i) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem endpointMatching_involutive (P : PerfectMatching ι) :
    Function.Involutive (endpointMatching P) := by
  intro i
  cases i with
  | none => rfl
  | some i => exact congrArg some (P.2.1 i)

omit [Fintype ι] [DecidableEq ι] in
theorem endpointMatching_isEndpointPairing (P : PerfectMatching ι) :
    EndpointPairing (endpointMatching P) none := by
  refine ⟨rfl, endpointMatching_involutive P, ?_⟩
  intro i hi
  cases i with
  | none => rfl
  | some i => exact False.elim (P.2.2 i (Option.some.inj hi))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicSpectralSum
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

attribute [local instance] OAI.KadisonSimilarity.spectralSumMeasurable
local instance spectralSumBorel_r87906b_1 : BorelSpace (WeakDual.characterSpace ℂ A) := ⟨rfl⟩
theorem cyclic_spectral_range (ξ : H) :
    Set.range (commutativeCyclicIsometry π ξ) = (orbitClosure π.range ξ : Set H) := by
  rw [commutativeCyclicIsometry_range]
  change closure (Set.range (fun a : A => π a ξ)) =
    closure (Set.range (fun a : π.range => (a : H →L[ℂ] H) ξ))
  congr 1
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨π.rangeRestrict a, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := a.property
    exact ⟨b, congrArg (fun T : H →L[ℂ] H => T ξ) hb⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HaarCornerLetters
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem haarCornerCoefficient_sq {a : ℝ} (ha : 0 ≤ a) :
    haarCornerCoefficient a * haarCornerCoefficient a = ((a⁻¹ : ℝ) : ℂ) := by
  have h : (Real.sqrt a)⁻¹ * (Real.sqrt a)⁻¹ = a⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt ha]
  unfold haarCornerCoefficient
  exact_mod_cast h

theorem star_haarCornerLetter_mul_self (z : unitary (CStarCorner q hq))
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    star (haarCornerLetter z a n) * haarCornerLetter z a n = ((a⁻¹ : ℝ) : ℂ) • q := by
  rw [star_haarCornerLetter]
  simp only [haarCornerLetter, smul_mul_smul, haarCornerPower_mul,
    neg_add_cancel, haarCornerPower_zero, haarCornerCoefficient_sq ha]

variable (τ : P →ₗ[ℂ] ℂ) (z : unitary (CStarCorner q hq)) {a : ℝ}

/-- The opposite-order products of the normalized powers have delta trace.
This order is the one appearing in the inner products of adjoint letters. -/
theorem haarCornerLetter_mul_star_trace (ha : 0 < a) (htrace : τ q = (a : ℂ))
    (hhaar : HaarCornerMoments τ z a) (i j : ℕ) :
    τ (haarCornerLetter z a i * star (haarCornerLetter z a j)) =
      if i = j then 1 else 0 := by
  rw [star_haarCornerLetter]
  simp only [haarCornerLetter, smul_mul_smul, haarCornerPower_mul,
    map_smul, smul_eq_mul, haarCornerCoefficient_sq ha.le,
    haarCornerPower_trace τ z ha htrace hhaar]
  by_cases hij : i = j
  · subst j
    have he : (i : ℤ) + 1 + -((i : ℤ) + 1) = 0 := by omega
    have hane : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    simp only [he, ↓reduceIte, Complex.ofReal_inv, inv_mul_cancel₀ hane]
  · have he : (i : ℤ) + 1 + -((j : ℤ) + 1) ≠ 0 := by omega
    simp only [hij, he, ↓reduceIte, mul_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DyadicPhases
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dyadic roots of unity, with a refinement estimate. These are the
scalar coefficients for the norm-convergent Haar-unitary construction. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial
open scoped BigOperators

def dyadicRank : (n : ℕ) → DyadicIndex n → ℕ
  | 0, _ => 0
  | n + 1, i => 2 * dyadicRank n i.1 + if i.2 then 1 else 0

def dyadicPhase (n : ℕ) (i : DyadicIndex n) : ℂ :=
  Complex.exp (((2 * Real.pi * (dyadicRank n i : ℝ) / (2 : ℝ) ^ n : ℝ) : ℂ) *
    Complex.I)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_OrthogonalWordLevels
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

namespace OrthogonalWordLevels

variable (U : OrthogonalWordLevels W H)

def block (Y : H →L[ℂ] H) (m n : ℕ) : W n →L[ℂ] W m :=
  (U.coordinate m).comp (Y.comp (U.inclusion n).toContinuousLinearMap)

/-- Compressing a global commutation identity yields the actual block
intertwining. Adjoint covariance of the target inclusion supplies its coordinate
covariance. -/
theorem block_intertwines (Y A : H →L[ℂ] H) {n m : ℕ}
    (S : W n →L[ℂ] W n) (T : W m →L[ℂ] W m)
    (hY : Y.comp A = A.comp Y)
    (hsource : A.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp S)
    (htarget : A.adjoint.comp (U.inclusion m).toContinuousLinearMap =
      (U.inclusion m).toContinuousLinearMap.comp T.adjoint) :
    (U.block Y m n).comp S = T.comp (U.block Y m n) := by
  have hc := congrArg ContinuousLinearMap.adjoint htarget
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] at hc
  ext x
  have hs := congrArg (fun C : W n →L[ℂ] H => C x) hsource
  have hy := congrArg (fun C : H →L[ℂ] H => C (U.inclusion n x)) hY
  have ht := congrArg (fun C : H →L[ℂ] W m => C (Y (U.inclusion n x))) hc
  simp only [ContinuousLinearMap.comp_apply] at hs hy ht
  change A (U.inclusion n x) = U.inclusion n (S x) at hs
  change U.coordinate m (Y (U.inclusion n (S x))) = T (U.coordinate m (Y (U.inclusion n x)))
  rw [← hs, hy]
  exact ht

end OrthogonalWordLevels

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialDihedralColumns
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.dihedralHalfProjection_projectionReflection _root_.OAI.KadisonSimilarity.projectionReflection_mul_self _root_.OAI.KadisonSimilarity.star_projectionReflection _root_.OAI.NaimarkZFC.gns_apply_coe
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

section TraceReflection
variable {P : Type*} [Ring P] [StarRing P] [Algebra ℂ P]

omit [StarRing P] in
/-- A half-trace projection gives a centered reflection. -/
theorem trace_projectionReflection (τ : P →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (p : P) (hp : τ p = (1 / 2 : ℂ)) : τ (projectionReflection p) = 0 := by
  rw [projectionReflection, map_sub, map_add, hp, hτ]
  norm_num

end TraceReflection



end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialHalfProjectionData
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered reflection used by the dihedral test is constructed from a
half-trace projection. Completing a smaller projection by an orthogonal
projection of the complementary trace supplies that projection; no centered
symmetry is assumed in this algebraic step. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace HalfTraceProjectionData

variable {τ : P →ₗ[ℂ] ℂ} {e : P} (Q : HalfTraceProjectionData τ e)

theorem reflection_trace (hτ : τ 1 = 1) : τ Q.reflection = 0 :=
  trace_projectionReflection τ hτ Q.projection Q.trace_half

end HalfTraceProjectionData
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixTower
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

include M in
omit [CompleteSpace E] [∀ s, Nonempty (A s)] in
/-- Density of the matrix union already implies density of the represented
algebra, so no separate cyclic-density assumption is needed by the tower. -/
theorem NestedTracialMatrices.denseRange_vector : DenseRange V := by
  apply M.dense.mono
  intro x hx
  obtain ⟨s, a, rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨M.embedding s a, rfl⟩

include M in
omit [CompleteSpace E] in
/-- A unital trace-preserving nonempty matrix stage normalizes the ambient
trace automatically. -/
theorem NestedTracialMatrices.trace_one : τ 1 = 1 := by
  have hn : (Fintype.card (A 0) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa only [map_one, Matrix.trace_one, inv_mul_cancel₀ hn] using M.trace_embedding 0 1

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerTransport
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- Half-trace completion and both support identities survive the factor
embedding, as does the subsequently constructed centered reflection. -/
def HalfTraceProjectionData.transport
    {τA : A →ₗ[ℂ] ℂ} {τB : B →ₗ[ℂ] ℂ} (hφ : ∀ x, τB (φ x) = τA x)
    {e : A} (Q : HalfTraceProjectionData τA e) : HalfTraceProjectionData τB (φ e) where
  projection := φ Q.projection
  isProjection := Q.isProjection.map φ
  trace_half := (hφ _).trans Q.trace_half
  left_support := by rw [← map_mul, Q.left_support]
  right_support := by rw [← map_mul, Q.right_support]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SmallFreeCornerData
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

local instance instIsClosedContinuousLinearMapComplexIdCoeStarSubalgebra_solutions_1 : IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K)) :=
  Generator.Tracial.base_norm_closed N

end Concrete
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ConcreteHaarDischarge
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise diffuse-corner Haar input used by the free-corner argument
is supplied by the constructed dyadic unitary. -/

noncomputable section
namespace KadisonSimilarity
open UltrapowerBridge

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra K}

local instance concreteHaar_closed : IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K)) :=
  Generator.Tracial.base_norm_closed N

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_PropagationTheorem
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Propagation from a full column through repeated reduced words

Only raw word identities and the elementary tracial operator relations are
supplied below. The error vector, its scaling, the vanishing exceptional
coefficient, and the propagation bound are all derived.
-/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMap
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section WordData

variable {B V E F : Type*}
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Local tracial-word data for one fixed positive word level. The fields are
operator identities, word isometries, and the tensor-coordinate formula for
the exceptional projection. There is no approximation or propagation bound
among the fields. -/
structure RepeatedLetterWords (G : H →L[ℂ] H) (B₀ : B →L[ℂ] B) (Bₖ : V →L[ℂ] V)
    (P : Submodule ℂ H) [P.HasOrthogonalProjection] (a : ℝ) where
  repeatVector : B →ₗᵢ[ℂ] V
  word : ℕ → V →ₗᵢ[ℂ] H
  small : B →L[ℂ] H
  small_norm : ∀ v, ‖small v‖ = Real.sqrt a * ‖v‖
  level_zero : ∀ v, G (small v) = small (B₀ v)
  level_repeated : ∀ n v, G (word n (repeatVector v)) = word n (Bₖ (repeatVector v))
  support : H →L[ℂ] H
  support_small : ∀ v, support (small v) = small v
  letter : ℕ → H →L[ℂ] H
  letter_scale : ∀ n, (letter n).adjoint.comp (letter n) = ((a⁻¹ : ℝ) : ℂ) • support
  wordPrefix : ℕ → H →L[ℂ] H
  word_factor : ∀ n v, word n (repeatVector v) = wordPrefix n (letter n (small v))
  prefix_isometry : ∀ n, ∀ z ∈ Pᗮ, ‖wordPrefix n z‖ = ‖z‖
  prefix_bound : ℝ
  prefix_bound_le : ∀ n, ‖wordPrefix n‖ ≤ prefix_bound
  tensor_coordinates : H →L[ℂ] HilbertTensor E F
  vacuum_insert : F →L[ℂ] H
  adjoint_letters : ℕ → E
  adjoint_letters_orthonormal : Orthonormal ℂ adjoint_letters
  vacuum_slice : ∀ n z, P.starProjection (letter n z) =
    vacuum_insert (tensorSlice (adjoint_letters n) (tensor_coordinates z))

end WordData
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ReducedWordAutomorphisms
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- Every bounded reduced word belongs to the algebra generated by the factors. -/
theorem reducedWord_mem_factorAlgebra (n : ℕ) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D) :
    (d : P) * alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P) ∈
      factorAlgebra A D := by
  have hA (x : A) : (x : P) ∈ factorAlgebra A D :=
    StarAlgebra.subset_adjoin ℂ _ (Or.inl x.property)
  have hD (x : D) : (x : P) ∈ factorAlgebra A D :=
    StarAlgebra.subset_adjoin ℂ _ (Or.inr x.property)
  apply (factorAlgebra A D).mul_mem
  · apply (factorAlgebra A D).mul_mem (hD d)
    unfold alternatingProduct
    have hprod (l : List P) :
        (∀ x ∈ l, x ∈ factorAlgebra A D) → l.prod ∈ factorAlgebra A D := by
      induction l with
      | nil => intro _; exact (factorAlgebra A D).one_mem
      | cons x l ih =>
        intro hl
        exact (factorAlgebra A D).mul_mem (hl x (List.mem_cons_self))
          (ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)))
    apply hprod
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (factorAlgebra A D).mul_mem (hA (a i)) (hD (c i))
  · exact hA b

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SpectralArc
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.dihedralHalfProjection_projectionReflection _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- The half projection of a selfadjoint involution. -/
theorem isStarProjection_dihedralHalfProjection (d : Pˣ)
    (hd : star (d : P) = (d : P)) (hdd : d * d = 1) :
    IsStarProjection (dihedralHalfProjection d) := by
  have hdd' : (d : P) * (d : P) = 1 := by
    rw [← Units.val_mul, hdd, Units.val_one]
  apply isStarProjection_iff'.2
  constructor
  · simp only [dihedralHalfProjection, smul_mul_assoc, mul_smul_comm,
      add_mul, mul_add, one_mul, mul_one, hdd']
    module
  · simp only [dihedralHalfProjection, star_smul, star_add, star_one, hd]
    norm_num

/-- Centering the reflection fixes the trace of its half projection. -/
theorem trace_dihedralHalfProjection (τ : P →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (d : Pˣ) (hd : τ (d : P) = 0) : τ (dihedralHalfProjection d) = (1 / 2 : ℂ) := by
  simp only [dihedralHalfProjection, map_smul, map_add, hτ, hd, add_zero, smul_eq_mul,
    mul_one]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SymmetryWordRange
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base expectation on the algebra generated by the other free factor
and one centered symmetry. The only density datum is the ordinary reduced
word span; the two-dimensional expectation range is proved. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- Ordinary products of the alternating reduced symmetry words. -/
def centeredSymmetryWordProducts (τ : P →ₗ[ℂ] ℂ) (D : StarSubalgebra ℂ P) (s : P) :
    Set P := {x | ∃ (side : Bool) (xs : List P), CenteredSymmetryWord τ D s side xs ∧
      x = xs.prod}

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SymmetryWordAlgebra
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic normal forms for the algebra generated by a star subalgebra
and a symmetry. Centering the other-factor letters and cancelling adjacent
symmetries proves the reduced-word density used by the base expectation. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace SymmetryWordAlgebra

variable (τ : P →ₗ[ℂ] ℂ) (D : StarSubalgebra ℂ P) (s : P)

def wordSpan : Submodule ℂ P := Submodule.span ℂ (centeredSymmetryWordProducts τ D s)

theorem word_mem {side : Bool} {xs : List P} (h : CenteredSymmetryWord τ D s side xs) :
    xs.prod ∈ wordSpan τ D s := Submodule.subset_span ⟨side, xs, h, rfl⟩

theorem one_mem : (1 : P) ∈ wordSpan τ D s :=
  word_mem τ D s (.nil true)

theorem symmetry_mem : s ∈ wordSpan τ D s := by
  simpa using word_mem τ D s (.symmetry (.nil true))

variable (hτ : τ 1 = 1)

include hτ in
/-- Centering an arbitrary other-factor letter provides its normal form
before a word starting with the symmetry. -/
theorem other_mul_false_word (d : P) (hd : d ∈ D) {xs : List P}
    (hw : CenteredSymmetryWord τ D s false xs) :
    d * xs.prod ∈ wordSpan τ D s := by
  have hc := word_mem τ D s
    (CenteredSymmetryWord.other (traceCentered_mem τ D hd)
      (traceCentered_trace τ hτ d) hw)
  have hs := (wordSpan τ D s).smul_mem (τ d) (word_mem τ D s hw)
  have heq : d * xs.prod = traceCentered τ d * xs.prod + τ d • xs.prod := by
    calc
      _ = (traceCentered τ d + τ d • (1 : P)) * xs.prod := by rw [traceCentered_add]
      _ = _ := by rw [add_mul, smul_mul_assoc, one_mul]
  rw [heq]
  exact (wordSpan τ D s).add_mem hc hs

include hτ in
theorem other_mul_word (d : P) (hd : d ∈ D) {side : Bool} {xs : List P}
    (hw : CenteredSymmetryWord τ D s side xs) :
    d * xs.prod ∈ wordSpan τ D s := by
  cases hw with
  | nil side => exact other_mul_false_word τ D s hτ d hd (.nil false)
  | @other a ys ha _ tail =>
    change d * (a * ys.prod) ∈ _
    rw [← mul_assoc]
    exact other_mul_false_word τ D s hτ (d * a) (D.mul_mem hd ha) tail
  | symmetry tail => exact other_mul_false_word τ D s hτ d hd (.symmetry tail)

include hτ in
theorem other_mul_mem (d : P) (hd : d ∈ D) {x : P} (hx : x ∈ wordSpan τ D s) :
    d * x ∈ wordSpan τ D s := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨side, xs, hw, rfl⟩ := hx
    exact other_mul_word τ D s hτ d hd hw
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using (wordSpan τ D s).add_mem hx hy
  | smul c x _ hx => simpa only [mul_smul_comm] using (wordSpan τ D s).smul_mem c hx

include hτ in
theorem other_mem (d : P) (hd : d ∈ D) : d ∈ wordSpan τ D s := by
  simpa only [mul_one] using other_mul_mem τ D s hτ d hd (one_mem τ D s)

variable (hsq : s * s = 1)

include hsq in
theorem symmetry_mul_word {side : Bool} {xs : List P}
    (hw : CenteredSymmetryWord τ D s side xs) :
    s * xs.prod ∈ wordSpan τ D s := by
  cases hw with
  | nil side => simpa using symmetry_mem τ D s
  | other hd hz tail => exact word_mem τ D s (.symmetry (.other hd hz tail))
  | symmetry tail =>
    change s * (s * _) ∈ _
    rw [← mul_assoc, hsq, one_mul]
    exact word_mem τ D s tail

include hsq in
theorem symmetry_mul_mem {x : P} (hx : x ∈ wordSpan τ D s) :
    s * x ∈ wordSpan τ D s := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨side, xs, hw, rfl⟩ := hx
    exact symmetry_mul_word τ D s hsq hw
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using (wordSpan τ D s).add_mem hx hy
  | smul c x _ hx => simpa only [mul_smul_comm] using (wordSpan τ D s).smul_mem c hx

include hτ hsq in
theorem word_mul_mem {side : Bool} {xs : List P}
    (hw : CenteredSymmetryWord τ D s side xs) {y : P} (hy : y ∈ wordSpan τ D s) :
    xs.prod * y ∈ wordSpan τ D s := by
  induction hw with
  | nil side => simpa only [List.prod_nil, one_mul] using hy
  | other hd _ _ ih =>
    simpa only [List.prod_cons, mul_assoc] using other_mul_mem τ D s hτ _ hd ih
  | symmetry _ ih =>
    simpa only [List.prod_cons, mul_assoc] using symmetry_mul_mem τ D s hsq ih

include hτ hsq in
theorem mul_mem {x y : P} (hx : x ∈ wordSpan τ D s) (hy : y ∈ wordSpan τ D s) :
    x * y ∈ wordSpan τ D s := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨side, xs, hw, rfl⟩ := hx
    exact word_mul_mem τ D s hτ hsq hw hy
  | zero => simp
  | add x z _ _ hx hz => simpa only [add_mul] using (wordSpan τ D s).add_mem hx hz
  | smul c x _ hx => simpa only [smul_mul_assoc] using (wordSpan τ D s).smul_mem c hx

variable (hstar : star s = s)

include hτ hsq hstar in
theorem star_word_mem {side : Bool} {xs : List P}
    (hw : CenteredSymmetryWord τ D s side xs) :
    star xs.prod ∈ wordSpan τ D s := by
  induction hw with
  | nil side => simpa only [List.prod_nil, star_one] using one_mem τ D s
  | other hd _ _ ih =>
    simpa only [List.prod_cons, star_mul] using
      mul_mem τ D s hτ hsq ih (other_mem τ D s hτ _ (_root_.StarMemClass.star_mem hd))
  | symmetry _ ih =>
    simpa only [List.prod_cons, star_mul, hstar] using
      mul_mem τ D s hτ hsq ih (symmetry_mem τ D s)

include hτ hsq hstar in
theorem star_mem {x : P} (hx : x ∈ wordSpan τ D s) : star x ∈ wordSpan τ D s := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨side, xs, hw, rfl⟩ := hx
    exact star_word_mem τ D s hτ hsq hstar hw
  | zero => simpa only [star_zero] using (wordSpan τ D s).zero_mem
  | add x y _ _ hx hy => simpa only [star_add] using (wordSpan τ D s).add_mem hx hy
  | smul c x _ hx => simpa only [star_smul] using (wordSpan τ D s).smul_mem (star c) hx

def spanStarAlgebra : StarSubalgebra ℂ P where
  carrier := wordSpan τ D s
  zero_mem' := (wordSpan τ D s).zero_mem
  one_mem' := one_mem τ D s
  add_mem' := (wordSpan τ D s).add_mem
  mul_mem' := mul_mem τ D s hτ hsq
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (wordSpan τ D s).smul_mem c (one_mem τ D s)
  star_mem' := star_mem τ D s hτ hsq hstar

end SymmetryWordAlgebra

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_AEColumnOperator
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering fiber operators from almost-everywhere column data

The common conull set is obtained from countably many additive and
`i`-linearity identities. The extension has the original norm bound;
each fixed column agrees almost everywhere with the original data.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, NormedSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

/-- Bounded AE column data gives a genuine bounded complex-linear operator
on every fiber of a measurable conull restriction. -/
theorem exists_conull_columnOperators
    [TopologicalSpace.SeparableSpace E] (C : ℝ≥0)
    (f : ∀ _x : E, ∀ a, K a)
    (hzero : ∀ᵐ a ∂μ, f 0 a = 0)
    (hadd : ∀ x y : E, ∀ᵐ a ∂μ, f (x + y) a = f x a + f y a)
    (hI : ∀ x : E, ∀ᵐ a ∂μ, f (Complex.I • x) a = Complex.I • f x a)
    (hnorm : ∀ x : E, ∀ᵐ a ∂μ, ‖f x a‖ ≤ C * ‖x‖) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ T : ∀ a : s, E →L[ℂ] K a,
        (∀ a, ‖T a‖ ≤ C) ∧
        ∀ x : E, ∀ᵐ a ∂Measure.comap ((↑) : s → Ω) μ, T a x = f x a := by
  classical
  obtain ⟨S, hcount, hdense, hIS⟩ := exists_countable_dense_complex_addSubgroup E
  let : Countable S := hcount.to_subtype
  have hex := ae_exists_operator_of_countable_additive μ K S hdense hIS C
    (fun x a => f x a) hzero (fun x y => hadd x y) (fun x => hI x) (fun x => hnorm x)
  obtain ⟨s, hs, hsm, hsexists⟩ := hex.exists_measurable_mem
  choose T hT hext using fun a : s => hsexists a a.property
  refine ⟨s, hsm, mem_ae_iff.mp hs, T, hT, ?_⟩
  intro x
  have hsub (u v : E) : ∀ᵐ a ∂μ, f (u - v) a = f u a - f v a := by
    filter_upwards [hadd (u - v) v] with a ha
    exact eq_sub_iff_add_eq.mpr (by simpa only [sub_add_cancel] using ha.symm)
  have h := ae_columnOperator_agrees_at μ K S hdense C f hsub hnorm x
  have hr := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae h)
  exact hr.mono fun a ha => ha (T a) (hT a) (hext a)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CentralSymmetrization
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging over finite families of central projections

The finite sign groups and their averages are constructed explicitly. A weak
operator cluster point of the net indexed by finite projection families
commutes with every central projection. The final passage to the whole center
uses only the already stated spectral-step specialization of Blackadar.
-/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMapWOT
open scoped Topology Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def centralUnitarySubgroup (P : VonNeumannAlgebra H) :
    Subgroup (unitary (H →L[ℂ] H)) where
  carrier := {u | (u : H →L[ℂ] H) ∈ vonNeumannCenter P}
  one_mem' := (vonNeumannCenter P).one_mem
  mul_mem' := fun ha hb => (vonNeumannCenter P).mul_mem ha hb
  inv_mem' := fun hu => by
    change (star _ : H →L[ℂ] H) ∈ vonNeumannCenter P
    exact star_mem hu

theorem centralUnitary_commute (P : VonNeumannAlgebra H)
    (u v : centralUnitarySubgroup P) : Commute u v := by
  change u * v = v * u
  apply Subtype.ext
  apply Subtype.ext
  exact ((VonNeumannAlgebra.mem_commutant_iff.mp v.property.2)
    (u.val : H →L[ℂ] H) u.property.1)

def centralReflection {P : VonNeumannAlgebra H} (p : CentralProjection P) :
    centralUnitarySubgroup P :=
  ⟨⟨2 * p.val - 1, p.property.2.two_mul_sub_one_mem_unitary⟩, by
    change 2 * p.val - 1 ∈ vonNeumannCenter P
    rw [two_mul]
    exact (vonNeumannCenter P).sub_mem
      ((vonNeumannCenter P).add_mem p.property.1 p.property.1)
      (vonNeumannCenter P).one_mem⟩

theorem centralReflection_square {P : VonNeumannAlgebra H}
    (p : CentralProjection P) : centralReflection p * centralReflection p = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (2 * p.val - 1) * (2 * p.val - 1) = 1
  rw [two_mul]
  have hp := p.property.2.isIdempotentElem.eq
  simp only [mul_sub, sub_mul, mul_add, add_mul, hp, one_mul, mul_one]
  abel

def centralSignHom {P : VonNeumannAlgebra H} (p : CentralProjection P) :
    ℤˣ →* centralUnitarySubgroup P where
  toFun g := if g = 1 then 1 else centralReflection p
  map_one' := by simp
  map_mul' g h := by
    rcases intUnit_eq_one_or_neg_one g with rfl | rfl <;>
      rcases intUnit_eq_one_or_neg_one h with rfl | rfl <;>
      simp [centralReflection_square]

def centralSignRepresentation (P : VonNeumannAlgebra H)
    (s : Finset (CentralProjection P)) : (s → ℤˣ) →* (H →L[ℂ] H) :=
  (unitary (H →L[ℂ] H)).subtype.comp
    ((centralUnitarySubgroup P).subtype.comp
      (MonoidHom.noncommPiCoprod (fun p : s => centralSignHom p.val)
        (fun _ _ _ _ _ => centralUnitary_commute P _ _)))

/-- The finite average belonging to a finite family of central projections. -/
def centralProjectionTwirl (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (s : Finset (CentralProjection P)) : H →L[ℂ] H :=
  finiteTwirl (centralSignRepresentation P s) Y

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ClosedFamilySpan
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

omit [CompleteSpace E] in
theorem closedFamilySpan_inner_zero (v : I → E) (w : J → E)
    (h : ∀ i j, inner ℂ (v i) (w j) = 0)
    (x : closedFamilySpan v) (y : closedFamilySpan w) : inner ℂ (x : E) (y : E) = 0 := by
  have hw (i : I) : (closedFamilySpan w).toSubmodule ≤ (innerSL ℂ (v i)).ker := by
    apply (Submodule.span ℂ (Set.range w)).topologicalClosure_minimal
      (Submodule.span_le.mpr ?_) (innerSL ℂ (v i)).isClosed_ker
    rintro _ ⟨j, rfl⟩
    exact h i j
  have hv : (closedFamilySpan v).toSubmodule ≤ (innerSL ℂ (y : E)).ker := by
    apply (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal
      (Submodule.span_le.mpr ?_) (innerSL ℂ (y : E)).isClosed_ker
    rintro _ ⟨i, rfl⟩
    exact inner_eq_zero_symm.mp (hw i y.property)
  exact inner_eq_zero_symm.mp (hv x.property)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalOperatorField
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The field of a diagonal-commuting L² operator

An operator commuting with every measurable localization has bounded
constant-vector columns. Those actual columns determine a field of bounded
operators on a measurable conull subset of the base, without any additional
pointwise linearity assumption.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Reconstruct the pointwise operator from its actual constant-vector
columns. Each fixed column is preserved almost everywhere. -/
theorem exists_conull_diagonal_operator_field
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ field : ∀ _a : s, H →L[ℂ] H,
        (∀ a, ‖field a‖ ≤ ‖T‖) ∧
        ∀ x : H, ∀ᵐ a ∂Measure.comap ((↑) : s → Ω) μ,
          field a x = T (Lp.const 2 μ x) a := by
  let U : H →L[ℂ] Lp H 2 μ := T.comp (Lp.constL 2 μ ℂ)
  apply exists_conull_columnOperators μ (fun _ => H) ‖T‖₊ (fun x a => U x a)
  · filter_upwards [Lp.coeFn_zero H 2 μ] with a ha
    simpa only [map_zero, Pi.zero_apply] using ha
  · intro x y
    filter_upwards [Lp.coeFn_add (U x) (U y)] with a ha
    simpa only [map_add, Pi.add_apply] using ha
  · intro x
    filter_upwards [Lp.coeFn_smul Complex.I (U x)] with a ha
    simpa only [map_smul, Pi.smul_apply] using ha
  · intro x
    exact diagonal_commutant_column_bound μ T hT x

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFieldAction
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise action on all L² vectors

The field reconstructed from constant columns acts pointwise on arbitrary
L² vectors. Indicator constants give a dense class; two successive AE
subsequences prove that the pointwise-action identity is norm closed.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Commutation with diagonal localizations extends the constant-column
formula to every L² vector. -/
theorem diagonal_operator_action_of_columns
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T)
    (field : Ω → H →L[ℂ] H)
    (hcolumns : ∀ x : H, ∀ᵐ a ∂μ, T (Lp.const 2 μ x) a = field a x)
    (f : Lp H 2 μ) : ∀ᵐ a ∂μ, T f a = field a (f a) := by
  apply Lp.induction (by simp : (2 : ℝ≥0∞) ≠ ∞)
    (motive := fun f => ∀ᵐ a ∂μ, T f a = field a (f a))
    ?_ ?_ (isClosed_pointwise_operator_action μ T field) f
  · intro c r hr hμr
    change ∀ᵐ a ∂μ, T (indicatorConstLp 2 hr hμr.ne c) a =
      field a (indicatorConstLp 2 hr hμr.ne c a)
    have heq := congrArg (fun S : Lp H 2 μ →L[ℂ] Lp H 2 μ => S (Lp.const 2 μ c))
      (hT r hr)
    change T (l2Localization μ r hr (Lp.const 2 μ c)) =
      l2Localization μ r hr (T (Lp.const 2 μ c)) at heq
    rw [l2Localization_const] at heq
    filter_upwards [hcolumns c, l2Localization_ae μ r hr (T (Lp.const 2 μ c)),
      indicatorConstLp_coeFn (p := 2) (hs := hr) (hμs := hμr.ne) (c := c)]
      with a hc hl hi
    rw [heq, hl, hi]
    by_cases ha : a ∈ r
    · simpa only [Set.indicator_of_mem ha] using hc
    · simp only [Set.indicator_of_notMem ha, map_zero]
  · intro f g hf hg _ hfa hga
    filter_upwards [hfa, hga, Lp.coeFn_add (hf.toLp f) (hg.toLp g),
      Lp.coeFn_add (T (hf.toLp f)) (T (hg.toLp g))] with a hfa hga hfg hout
    rw [map_add, hout, hfg, Pi.add_apply, Pi.add_apply, map_add, hfa, hga]

variable [TopologicalSpace.SeparableSpace H]

/-- The actual field of a diagonal-commuting operator, with the complete
pointwise-action formula on all L² vectors. -/
theorem exists_conull_diagonal_field_action
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ field : ∀ _a : s, H →L[ℂ] H,
        (∀ a, ‖field a‖ ≤ ‖T‖) ∧
        ∀ f : Lp H 2 μ, ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ,
          T f a = field a (f a) := by
  classical
  obtain ⟨s, hsm, hsnull, field, hnorm, hcols⟩ :=
    exists_conull_diagonal_operator_field μ T hT
  let R : Ω → H →L[ℂ] H := fun a => if ha : a ∈ s then field ⟨a, ha⟩ else 0
  have hs : ∀ᵐ a ∂μ, a ∈ s := mem_ae_iff.mpr hsnull
  have hc (x : H) : ∀ᵐ a ∂μ, T (Lp.const 2 μ x) a = R a x := by
    have hr : ∀ᵐ a ∂μ.restrict s, T (Lp.const 2 μ x) a = R a x := by
      apply (ae_restrict_iff_subtype hsm).mpr
      filter_upwards [hcols x] with a ha
      simpa only [R, dite_eq_left a.property] using ha.symm
    filter_upwards [hs, (ae_restrict_iff' hsm).mp hr] with a ha h
    exact h ha
  refine ⟨s, hsm, hsnull, field, hnorm, ?_⟩
  intro f
  have hf := diagonal_operator_action_of_columns μ T hT R hc f
  have hr := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae hf)
  filter_upwards [hr] with a ha
  simpa only [R, dite_eq_left a.property] using ha

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFieldAlgebra
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebraic laws for fields of diagonal-commuting operators

The fields are constructed from the actual operators. Their algebraic laws
hold almost everywhere, by the pointwise action on all L² vectors and a
countable dense family of constant columns.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Extending by the zero operator outside the conull reconstruction set
produces a field on the original measure space. -/
theorem exists_global_diagonal_field
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) :
    ∃ field : Ω → H →L[ℂ] H, (∀ a, ‖field a‖ ≤ ‖T‖) ∧
      ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = field a (f a) := by
  classical
  obtain ⟨s, hsm, hsnull, R, hnorm, haction⟩ :=
    exists_conull_diagonal_field_action μ T hT
  let field : Ω → H →L[ℂ] H := fun a => if ha : a ∈ s then R ⟨a, ha⟩ else 0
  refine ⟨field, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ s
    · simpa only [field, dite_eq_left ha] using hnorm ⟨a, ha⟩
    · simpa only [field, dite_eq_right ha, norm_zero] using norm_nonneg T
  · intro f
    have hr : ∀ᵐ a ∂μ.restrict s, T f a = field a (f a) := by
      apply (ae_restrict_iff_subtype hsm).mpr
      filter_upwards [haction f] with a ha
      simpa only [field, dite_eq_left a.property] using ha
    have hs : ∀ᵐ a ∂μ, a ∈ s := mem_ae_iff.mpr hsnull
    filter_upwards [hs, (ae_restrict_iff' hsm).mp hr] with a ha h
    exact h ha

/-- A chosen genuine field for an operator in the diagonal commutant. -/
def diagonalField
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) : Ω → H →L[ℂ] H :=
  Classical.choose (exists_global_diagonal_field μ T hT)

theorem diagonalField_action
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) (f : Lp H 2 μ) :
    ∀ᵐ a ∂μ, T f a = diagonalField μ T hT a (f a) :=
  (Classical.choose_spec (exists_global_diagonal_field μ T hT)).2 f

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_L2HilbertSum
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Hilbert sum of scalar L² spaces over one measure is the L² space
of the coordinate Hilbert space. The construction uses actual L² maps. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Lift a Hilbert isometry pointwise to L². -/
def l2MapIsometry (J : E →ₗᵢ[ℂ] F) : Lp E 2 μ →ₗᵢ[ℂ] Lp F 2 μ where
  toLinearMap := (J.toContinuousLinearMap.compLpL 2 μ).toLinearMap
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [l2_norm_sq_eq_integral, l2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [J.toContinuousLinearMap.coeFn_compLpL (p := 2) (μ := μ) f] with x hx
    change ‖(J.toContinuousLinearMap.compLpL 2 μ) f x‖ ^ 2 = ‖f x‖ ^ 2
    rw [hx]
    change ‖J (f x)‖ ^ 2 = ‖f x‖ ^ 2
    rw [J.norm_map]

theorem l2MapIsometry_ae (J : E →ₗᵢ[ℂ] F) (f : Lp E 2 μ) :
    l2MapIsometry μ J f =ᵐ[μ] (fun x => J (f x)) :=
  J.toContinuousLinearMap.coeFn_compLpL (p := 2) (μ := μ) f

variable {ι : Type*} [DecidableEq ι]

def scalarCoordinateIsometry (i : ι) : ℂ →ₗᵢ[ℂ] ScalarHilbertCoordinates ι where
  toLinearMap := (lp.singleContinuousLinearMap ℂ (fun _ : ι => ℂ) 2 i).toLinearMap
  norm_map' z := by
    change ‖lp.single (E := fun _ : ι => ℂ) 2 i z‖ = ‖z‖
    exact lp.norm_single (p := 2) (E := fun _ : ι => ℂ) (by norm_num) i z

def l2CoordinateIsometry (i : ι) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp (ScalarHilbertCoordinates ι) 2 μ :=
  l2MapIsometry μ (scalarCoordinateIsometry i)

def l2CoordinateProjection (i : ι) : Lp (ScalarHilbertCoordinates ι) 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).compLpL 2 μ

omit [DecidableEq ι] in
theorem l2CoordinateProjection_ae (i : ι) (f : Lp (ScalarHilbertCoordinates ι) 2 μ) :
    l2CoordinateProjection μ i f =ᵐ[μ] (fun x => f x i) :=
  (lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).coeFn_compLpL (p := 2) (μ := μ) f

theorem l2Coordinate_inner (i : ι) (f : Lp ℂ 2 μ)
    (g : Lp (ScalarHilbertCoordinates ι) 2 μ) :
    ⟪l2CoordinateIsometry μ i f, g⟫_ℂ = ⟪f, l2CoordinateProjection μ i g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2MapIsometry_ae μ (scalarCoordinateIsometry i) f,
    l2CoordinateProjection_ae μ i g] with x hf hg
  change inner ℂ (l2MapIsometry μ (scalarCoordinateIsometry i) f x) (g x) = _
  rw [hf, hg]
  exact lp.inner_single_left (𝕜 := ℂ) i (f x) (g x)

theorem l2Coordinate_orthogonal : OrthogonalFamily ℂ (fun _ : ι => Lp ℂ 2 μ)
    (l2CoordinateIsometry μ) := by
  intro i j hij f g
  rw [l2Coordinate_inner, L2.inner_def]
  have hz : l2CoordinateProjection μ i (l2CoordinateIsometry μ j g) =ᵐ[μ] 0 := by
    filter_upwards [l2CoordinateProjection_ae μ i (l2CoordinateIsometry μ j g),
      l2MapIsometry_ae μ (scalarCoordinateIsometry j) g] with x hp hi
    rw [hp]
    change (l2MapIsometry μ (scalarCoordinateIsometry j) g x) i = 0
    rw [hi]
    change lp.single (E := fun _ : ι => ℂ) 2 j (g x) i = 0
    simp [lp.single_apply, hij.symm]
  calc
    _ = ∫ _x : Ω, (0 : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hz] with x hx
      simp only [hx, Pi.zero_apply, inner_zero_right]
    _ = 0 := integral_zero _ _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_L2FiniteCopies
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Hilbert sums commute with L²

The isometry is the actual finite assembly of coordinate sections. Its
pointwise formula is retained for transporting operator matrix actions.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Insert a vector into a finite Hilbert coordinate. -/
def finiteCopyIsometry {n : ℕ} (i : Fin n) : H →ₗᵢ[ℂ] HilbertCopies H n where
  toLinearMap := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) i)).toLinearMap
  norm_map' x := PiLp.norm_single 2 (fun _ : Fin n => H) i x

@[simp] theorem finiteCopyIsometry_apply {n : ℕ} (i : Fin n) (x : H) :
    finiteCopyIsometry (H := H) i x = PiLp.single 2 i x := rfl

/-- Assemble a finite tuple of L² sections into one tuple-valued section. -/
def l2FiniteAssembly (n : ℕ) :
    HilbertCopies (Lp H 2 μ) n →L[ℂ] Lp (HilbertCopies H n) 2 μ :=
  sumColumns (fun i : Fin n => (l2MapIsometry μ (finiteCopyIsometry (H := H) i)).toContinuousLinearMap)

theorem l2FiniteAssembly_ae {n : ℕ} (f : HilbertCopies (Lp H 2 μ) n) :
    ∀ᵐ a ∂μ, ∀ i : Fin n, l2FiniteAssembly (H := H) μ n f a i = f i a := by
  have hparts : ∀ᵐ a ∂μ, ∀ i : Fin n,
      l2MapIsometry μ (finiteCopyIsometry (H := H) i) (f i) a = finiteCopyIsometry (H := H) i (f i a) :=
    eventually_countable_forall.mpr fun i => l2MapIsometry_ae μ (finiteCopyIsometry (H := H) i) (f i)
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin n => l2MapIsometry μ (finiteCopyIsometry (H := H) i) (f i))
  filter_upwards [hparts, hsum] with a ha hs
  intro i
  rw [l2FiniteAssembly, sumColumns_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  rw [hs]
  simp only [Finset.sum_apply, ha, finiteCopyIsometry_apply]
  simp

theorem l2FiniteAssembly_norm {n : ℕ} (f : HilbertCopies (Lp H 2 μ) n) :
    ‖l2FiniteAssembly (H := H) μ n f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2FiniteAssembly, sumColumns_apply,
    norm_sum_sq_of_pairwise_orthogonal, PiLp.norm_sq_eq_of_L2]
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun t : ℝ => t ^ 2) ((l2MapIsometry μ (finiteCopyIsometry (H := H) i)).norm_map (f i))
  · intro i j hij
    rw [L2.inner_def]
    calc
      (∫ a, inner ℂ (l2MapIsometry μ (finiteCopyIsometry (H := H) i) (f i) a)
          (l2MapIsometry μ (finiteCopyIsometry (H := H) j) (f j) a) ∂μ) = ∫ _a : Ω, (0 : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [l2MapIsometry_ae μ (finiteCopyIsometry (H := H) i) (f i),
          l2MapIsometry_ae μ (finiteCopyIsometry (H := H) j) (f j)] with a hi hj
        rw [hi, hj]
        simp only [finiteCopyIsometry_apply, PiLp.inner_apply, PiLp.single_apply]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hki : k = i
        · subst k
          simp [hij]
        · simp [hki]
      _ = 0 := integral_zero _ _

def finiteCopyProjection {n : ℕ} (i : Fin n) : HilbertCopies H n →L[ℂ] H :=
  PiLp.proj 2 (fun _ : Fin n => H) i

/-- The inverse takes the actual pointwise coordinate projections. -/
def l2FiniteCoordinates (n : ℕ) :
    Lp (HilbertCopies H n) 2 μ →L[ℂ] HilbertCopies (Lp H 2 μ) n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => Lp H 2 μ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (finiteCopyProjection (H := H) i).compLpL 2 μ)

@[simp] theorem l2FiniteCoordinates_apply {n : ℕ}
    (f : Lp (HilbertCopies H n) 2 μ) (i : Fin n) :
    l2FiniteCoordinates (H := H) μ n f i = (finiteCopyProjection (H := H) i).compLpL 2 μ f := rfl

theorem l2FiniteCoordinates_ae {n : ℕ} (f : Lp (HilbertCopies H n) 2 μ) :
    ∀ᵐ a ∂μ, ∀ i : Fin n, l2FiniteCoordinates (H := H) μ n f i a = f a i :=
  eventually_countable_forall.mpr fun i =>
    (finiteCopyProjection (H := H) i).coeFn_compLpL (p := 2) (μ := μ) f

theorem l2FiniteAssembly_coordinates {n : ℕ} (f : Lp (HilbertCopies H n) 2 μ) :
    l2FiniteAssembly (H := H) μ n (l2FiniteCoordinates (H := H) μ n f) = f := by
  apply Lp.ext
  filter_upwards [l2FiniteAssembly_ae μ (l2FiniteCoordinates (H := H) μ n f),
    l2FiniteCoordinates_ae μ f] with a ha hb
  ext i
  exact (ha i).trans (hb i)

/-- The exact unitary identification of finite L² sums. -/
def l2FiniteCopiesEquiv (n : ℕ) :
    HilbertCopies (Lp H 2 μ) n ≃ₗᵢ[ℂ] Lp (HilbertCopies H n) 2 μ :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (l2FiniteAssembly (H := H) μ n).toLinearMap
      norm_map' := l2FiniteAssembly_norm μ }
    (fun f => ⟨l2FiniteCoordinates (H := H) μ n f, l2FiniteAssembly_coordinates μ f⟩)

theorem l2FiniteCopiesEquiv_ae {n : ℕ} (f : HilbertCopies (Lp H 2 μ) n) :
    ∀ᵐ a ∂μ, ∀ i : Fin n, l2FiniteCopiesEquiv (H := H) μ n f a i = f i a :=
  l2FiniteAssembly_ae μ f

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralDensityIsometry
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication by a square-root density identifies the scalar L²
coordinates of a spectral measure with a subspace over a common base measure. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal ENNReal Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  (u : X → ℝ≥0) (hu : Measurable u)
  (hL2 : MemLp (fun x => (u x : ℂ)) 2 μ)

variable [IsFiniteMeasure (squaredDensityMeasure μ u)]

omit [T2Space X] in
include hu in
theorem weightedContinuous_norm (f : C(X, ℂ)) :
    ‖weightedContinuousVector μ u hu hL2 f‖ =
      ‖ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq_eq_integral, l2_norm_sq_eq_integral]
  have ha := weightedContinuousVector_ae μ u hu hL2 f
  have hb := ContinuousMap.coeFn_toLp (μ := squaredDensityMeasure μ u) (p := 2) (𝕜 := ℂ) f
  rw [integral_congr_ae (ha.mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx),
    integral_congr_ae (hb.mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx)]
  rw [squaredDensityMeasure, integral_withDensity_eq_integral_smul (hu.pow_const 2)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [norm_mul, mul_pow, NNReal.smul_def, NNReal.coe_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (u x).coe_nonneg, smul_eq_mul]

def spectralDensityIsometry [ (squaredDensityMeasure μ u).WeaklyRegular] :
    Lp ℂ 2 (squaredDensityMeasure μ u) →ₗᵢ[ℂ] Lp ℂ 2 μ := by
  let F := weightedContinuousLinear μ u hu hL2
  let J := F.extendOfNorm (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ).toLinearMap
  refine ⟨J.toLinearMap, ?_⟩
  intro ξ
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
    (μ := squaredDensityMeasure μ u) (𝕜 := ℂ) (by norm_num)).induction
      (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) ξ
  obtain ⟨f, rfl⟩ := hy
  have he : J (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ f) = F f := by
    apply LinearMap.extendOfNorm_eq
    · exact ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
        (μ := squaredDensityMeasure μ u) (𝕜 := ℂ) (by norm_num)
    · exact ⟨1, fun g => by
        change ‖weightedContinuousVector μ u hu hL2 g‖ ≤
          1 * ‖ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ g‖
        simpa only [one_mul] using (weightedContinuous_norm μ u hu hL2 g).le⟩
  change ‖J (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ f)‖ = _
  rw [he]
  exact weightedContinuous_norm μ u hu hL2 f

theorem spectralDensityIsometry_toLp [(squaredDensityMeasure μ u).WeaklyRegular]
    (f : C(X, ℂ)) :
    spectralDensityIsometry μ u hu hL2
      (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ f) =
        weightedContinuousVector μ u hu hL2 f := by
  change (weightedContinuousLinear μ u hu hL2).extendOfNorm
    (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ).toLinearMap
      (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ f) = _
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
      (μ := squaredDensityMeasure μ u) (𝕜 := ℂ) (by norm_num)
  · refine ⟨1, fun g => ?_⟩
    change ‖weightedContinuousVector μ u hu hL2 g‖ ≤
      1 * ‖ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ g‖
    simpa only [one_mul] using (weightedContinuous_norm μ u hu hL2 g).le

section MeasureTransport
variable (ν : Measure X) [IsFiniteMeasure ν] [ν.WeaklyRegular]

omit [IsFiniteMeasure (squaredDensityMeasure μ u)] in
def spectralDensityIsometryOfEq (heq : squaredDensityMeasure μ u = ν) :
    Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ := by
  subst ν
  exact spectralDensityIsometry μ u hu hL2

end MeasureTransport
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralIntertwining
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both spectral coordinate maps intertwine the continuous scalar action.
The identities are proved first on continuous functions and extended by density. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

variable (μ : Measure X) (u : X → ℝ≥0) (hu : Measurable u)
  (hL2 : MemLp (fun x => (u x : ℂ)) 2 μ)

omit [T2Space X] in
theorem weightedContinuousVector_mul (f g : C(X, ℂ)) :
    continuousL2Mul μ f (weightedContinuousVector μ u hu hL2 g) =
      weightedContinuousVector μ u hu hL2 (f * g) := by
  apply Lp.ext
  filter_upwards [continuousL2Mul_ae μ f (weightedContinuousVector μ u hu hL2 g),
    weightedContinuousVector_ae μ u hu hL2 g,
    weightedContinuousVector_ae μ u hu hL2 (f * g)] with x hm hg hfg
  rw [hm, hg, hfg, ContinuousMap.mul_apply]
  ring

variable [IsFiniteMeasure (squaredDensityMeasure μ u)]
  [(squaredDensityMeasure μ u).WeaklyRegular]

theorem spectralDensityIsometry_intertwines (f : C(X, ℂ))
    (ξ : Lp ℂ 2 (squaredDensityMeasure μ u)) :
    spectralDensityIsometry μ u hu hL2
      (continuousL2Mul (squaredDensityMeasure μ u) f ξ) =
        continuousL2Mul μ f (spectralDensityIsometry μ u hu hL2 ξ) := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
    (μ := squaredDensityMeasure μ u) (𝕜 := ℂ) (by norm_num)).induction
      (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) ξ
  obtain ⟨g, rfl⟩ := hy
  rw [continuousL2Mul_toLp, spectralDensityIsometry_toLp, spectralDensityIsometry_toLp,
    weightedContinuousVector_mul]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_L2ScalarIntertwining
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar multiplication is preserved by coordinate inclusions and the
cyclic spectral maps. These are the intertwining identities for the common
central Hilbert model. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem l2MapIsometry_scalar_intertwines (J : ℂ →ₗᵢ[ℂ] H) (f : C(X, ℂ)) (ξ : Lp ℂ 2 μ) :
    l2MapIsometry μ J (continuousL2Mul μ f ξ) =
      VectorL2.continuousL2Mul μ f (l2MapIsometry μ J ξ) := by
  apply Lp.ext
  filter_upwards [l2MapIsometry_ae μ J (continuousL2Mul μ f ξ),
    continuousL2Mul_ae μ f ξ,
    VectorL2.continuousL2Mul_ae μ f (l2MapIsometry μ J ξ),
    l2MapIsometry_ae μ J ξ] with x hJ hm hV hξ
  rw [hJ, hm, hV, hξ]
  change J (f x • ξ x) = f x • J (ξ x)
  exact J.map_smul (f x) (ξ x)

/-- Compose a scalar intertwiner with a fixed Hilbert coordinate and retain
its intertwining identity without unfolding the scalar construction. -/
def coordinateIntertwinerData (ν : Measure X) (V : ℂ →ₗᵢ[ℂ] H)
    (d : {J : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ //
      ∀ (f : C(X, ℂ)) (ξ : Lp ℂ 2 ν),
        J (continuousL2Mul ν f ξ) = continuousL2Mul μ f (J ξ)}) :
    {J : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp H 2 μ //
      ∀ (f : C(X, ℂ)) (ξ : Lp ℂ 2 ν),
        J (continuousL2Mul ν f ξ) = VectorL2.continuousL2Mul μ f (J ξ)} := by
  refine ⟨(l2MapIsometry μ V).comp d.val, ?_⟩
  intro f ξ
  change l2MapIsometry μ V (d.val (continuousL2Mul ν f ξ)) = _
  rw [d.property f ξ]
  exact l2MapIsometry_scalar_intertwines μ V f _

section Density
variable [T2Space X] (ν : Measure X) [IsFiniteMeasure ν] [ν.WeaklyRegular]
  (u : X → ℝ≥0) (hu : Measurable u) (hL2 : MemLp (fun x => (u x : ℂ)) 2 μ)

theorem spectralDensityIsometryOfEq_intertwines (heq : squaredDensityMeasure μ u = ν)
    (f : C(X, ℂ)) (ξ : Lp ℂ 2 ν) :
    spectralDensityIsometryOfEq μ u hu hL2 ν heq (continuousL2Mul ν f ξ) =
      continuousL2Mul μ f (spectralDensityIsometryOfEq μ u hu hL2 ν heq ξ) := by
  subst ν
  exact spectralDensityIsometry_intertwines μ u hu hL2 f ξ

/-- Retain the intertwining property with the chosen measure-change isometry,
so later concrete instantiations do not unfold its extension construction. -/
def spectralDensityIntertwinerData (heq : squaredDensityMeasure μ u = ν) :
    {J : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ //
      ∀ (f : C(X, ℂ)) (ξ : Lp ℂ 2 ν),
        J (continuousL2Mul ν f ξ) = continuousL2Mul μ f (J ξ)} :=
  ⟨spectralDensityIsometryOfEq μ u hu hL2 ν heq,
    spectralDensityIsometryOfEq_intertwines μ ν u hu hL2 heq⟩

end Density

section Cyclic
variable [T2Space X] [CompleteSpace H]
  {A : Type*} [CommCStarAlgebra A]

attribute [local instance] OAI.KadisonSimilarity.scalarIntertwiningMeasurable
attribute [local instance] OAI.KadisonSimilarity.scalarIntertwiningBorel
theorem commutativeCyclicIsometry_intertwines
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (a : A)
    (ξ : Lp ℂ 2 (commutativeVectorMeasure π v)) :
    commutativeCyclicIsometry π v
      (continuousL2Mul (commutativeVectorMeasure π v) (gelfandStarTransform A a) ξ) =
        π a (commutativeCyclicIsometry π v ξ) := by
  change Lp ℂ 2 (VectorSpectralMeasure.measure (commutativeSpectralCalculus π) v) at ξ
  change VectorSpectralMeasure.cyclicMap (commutativeSpectralCalculus π) v
    (continuousL2Mul (VectorSpectralMeasure.measure (commutativeSpectralCalculus π) v)
      (gelfandStarTransform A a) ξ) =
        π a (VectorSpectralMeasure.cyclicMap (commutativeSpectralCalculus π) v ξ)
  rw [VectorSpectralMeasure.cyclicMap_intertwines]
  change π ((gelfandStarTransform A).symm (gelfandStarTransform A a)) _ = π a _
  rw [StarAlgEquiv.symm_apply_apply]

end Cyclic
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonSpectralMeasure
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One finite measure dominates every member of a countable family of
finite spectral measures. The Radon–Nikodym densities give common coordinates. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (ν : ι → Measure Ω)
  [∀ n, IsFiniteMeasure (ν n)]

instance commonSpectralMeasure_finite : IsFiniteMeasure (commonSpectralMeasure ν) :=
  inferInstanceAs (IsFiniteMeasure (Measure.sum ν).toFinite)

theorem component_absolutelyContinuous_common (n : ι) :
    ν n ≪ commonSpectralMeasure ν :=
  (Measure.absolutelyContinuous_sum_right n (Measure.AbsolutelyContinuous.refl (ν n))).trans
    (absolutelyContinuous_toFinite (Measure.sum ν))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_IntertwinerExtension
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension by zero along an isometric Hilbert-space embedding. These
identities transport the central commutant to the common scalar L² model. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

theorem isometricExtension_sub (T U : H →L[ℂ] H) :
    isometricExtension J (T - U) = isometricExtension J T - isometricExtension J U := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [isometricExtension, ContinuousLinearMap.comp_apply, sub_apply,
    map_sub, LinearIsometry.coe_toContinuousLinearMap]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ScalarLocalizationLimit
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable localizations are strong limits of uniformly bounded continuous
scalar multipliers. Consequently their commutant is already determined by the
continuous scalar multipliers. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  [IsFiniteMeasure μ] [μ.Regular]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [T2Space X] [IsFiniteMeasure μ] [μ.Regular] [CompleteSpace H] in
/-- Dominated convergence for bounded scalar multipliers on vector-valued L². -/
theorem continuous_scalar_tendsto_localization
    (s : Set X) (hs : MeasurableSet s) (f : ℕ → C(X, ℂ))
    (hf : ∀ n x, ‖f n x‖ ≤ 1)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop
      (𝓝 (s.indicator (fun _ => (1 : ℂ)) x))) (ξ : Lp H 2 μ) :
    Tendsto (fun n => VectorL2.continuousL2Mul μ (f n) ξ) atTop
      (𝓝 (l2Localization μ s hs ξ)) := by
  let d (n : ℕ) : Lp H 2 μ :=
    VectorL2.continuousL2Mul μ (f n) ξ - l2Localization μ s hs ξ
  have hda (n : ℕ) : ∀ᵐ x ∂μ,
      d n x = (f n x - s.indicator (fun _ => (1 : ℂ)) x) • ξ x := by
    filter_upwards [Lp.coeFn_sub (VectorL2.continuousL2Mul μ (f n) ξ)
      (l2Localization μ s hs ξ), VectorL2.continuousL2Mul_ae μ (f n) ξ,
      l2Localization_ae μ s hs ξ] with x hd hm hl
    change (VectorL2.continuousL2Mul μ (f n) ξ - l2Localization μ s hs ξ) x = _
    rw [hd, Pi.sub_apply, hm, hl]
    by_cases hx : x ∈ s <;> simp [hx, sub_smul]
  have hint : Integrable (fun x => 4 * ‖ξ x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ξ)).mp
      (Lp.memLp ξ)).const_mul 4
  have hb (n : ℕ) : ∀ᵐ x ∂μ, ‖‖d n x‖ ^ 2‖ ≤ 4 * ‖ξ x‖ ^ 2 := by
    filter_upwards [hda n] with x hx
    rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hi : ‖s.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
      by_cases hx : x ∈ s <;> simp [hx]
    have hh : ‖f n x - s.indicator (fun _ => (1 : ℂ)) x‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [hf n x])
    have hm := mul_le_mul_of_nonneg_right hh (norm_nonneg (ξ x))
    nlinarith [norm_nonneg (f n x - s.indicator (fun _ => (1 : ℂ)) x),
      sq_nonneg (2 * ‖ξ x‖ - ‖f n x - s.indicator (fun _ => (1 : ℂ)) x‖ * ‖ξ x‖)]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ‖d n x‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [ht, eventually_countable_forall.mpr hda] with x hx hd
    have hzero : Tendsto
        (fun n => (f n x - s.indicator (fun _ => (1 : ℂ)) x) • ξ x) atTop (𝓝 0) := by
      simpa only [sub_self, zero_smul] using (hx.sub (tendsto_const_nhds (x := s.indicator (fun _ => (1 : ℂ)) x))).smul_const (ξ x)
    simpa only [hd, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hzero.norm.pow 2
  have hsq : Tendsto (fun n => ‖d n‖ ^ 2) atTop (𝓝 0) := by
    simpa only [Pi.pow_apply, ← l2_norm_sq_eq_integral, integral_zero] using
      (tendsto_integral_of_dominated_convergence (fun x => 4 * ‖ξ x‖ ^ 2)
        (fun n => (Lp.aestronglyMeasurable (d n)).norm.pow 2) hint hb hlim)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun n => Real.sqrt (‖d n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at h
  have he : (fun n => Real.sqrt (‖d n‖ ^ 2)) = (fun n => ‖d n‖) :=
    funext fun n => Real.sqrt_sq (norm_nonneg (d n))
  rw [he, Real.sqrt_zero] at h
  exact h

omit [CompleteSpace H] in
/-- Commutation with continuous scalar functions implies commutation with every
measurable localization, on the actual vector-valued L² space. -/
theorem commutes_localizations_of_continuous
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ f : C(X, ℂ),
      T * VectorL2.continuousL2Mul μ f = VectorL2.continuousL2Mul μ f * T)
    (s : Set X) (hs : MeasurableSet s) :
    T * l2Localization μ s hs = l2Localization μ s hs * T := by
  obtain ⟨f, hf, ht⟩ := exists_continuous_indicator_ae_sequence μ s hs
  apply ContinuousLinearMap.ext
  intro ξ
  have h₁ := T.continuous.continuousAt.tendsto.comp
    (continuous_scalar_tendsto_localization μ s hs f hf ht ξ)
  have h₂ := continuous_scalar_tendsto_localization μ s hs f hf ht (T ξ)
  have he (n : ℕ) : T (VectorL2.continuousL2Mul μ (f n) ξ) =
      VectorL2.continuousL2Mul μ (f n) (T ξ) :=
    congrArg (fun S : Lp H 2 μ →L[ℂ] Lp H 2 μ => S ξ) (hT (f n))
  exact tendsto_nhds_unique h₁ (h₂.congr (fun n => (he n).symm))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ScalarHilbertSeparability
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable coordinate Hilbert space used by the spectral model is
separable, by approximation with its finite-coordinate vectors. -/

noncomputable section
namespace KadisonSimilarity
open TopologicalSpace

instance scalarHilbertCoordinates_separable (ι : Type*) [Countable ι] :
    SeparableSpace (ScalarHilbertCoordinates ι) := by
  classical
  let s : Set (ScalarHilbertCoordinates ι) :=
    Set.range (fun i : ι => lp.single (E := fun _ : ι => ℂ) 2 i 1)
  have hs : IsSeparable (Submodule.span ℂ s : Set (ScalarHilbertCoordinates ι)) :=
    (Set.countable_range _).isSeparable.span
  have hd : closure (Submodule.span ℂ s : Set (ScalarHilbertCoordinates ι)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro f
    apply mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top f)
    apply Filter.Eventually.of_forall
    intro t
    apply Submodule.sum_mem
    intro i _
    have hi : lp.single (E := fun _ : ι => ℂ) 2 i 1 ∈ Submodule.span ℂ s :=
      Submodule.subset_span ⟨i, rfl⟩
    simpa only [← lp.single_smul, smul_eq_mul, mul_one] using
      (Submodule.smul_mem (Submodule.span ℂ s) (f i) hi)
  exact isSeparable_univ_iff.mp (hd ▸ hs.closure)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonCommutantFields
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable {A H : Type*}
  [CommCStarAlgebra A]
  [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))

attribute [local instance] commonCyclicMeasurable commonCyclicBorel 

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace H] in
theorem commutant_commutes_representation
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra) (a : A) :
    (T : H →L[ℂ] H) * π a = π a * T := by
  have ht : (T : H →L[ℂ] H) ∈ starSubalgebraCommutant π.range := T.property
  rw [← SetLike.mem_coe, coe_starSubalgebraCommutant] at ht
  exact (ht (π a) ⟨a, rfl⟩).symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProjectionFieldReduction
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

def projectionFiberInclusion (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    projectionFiber p hp →ₗᵢ[ℂ] H := (projectionFiber p hp).toSubmodule.subtypeₗᵢ

def projectionFiberRetraction (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    H →L[ℂ] projectionFiber p hp := p.codRestrict _ (fun x => ⟨x, rfl⟩)

@[simp] theorem projectionFiberRetraction_coe (p : H →L[ℂ] H) (hp : IsStarProjection p) (x : H) :
    (projectionFiberRetraction p hp x : H) = p x := rfl

theorem projectionFiber_fixed (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (x : projectionFiber p hp) : p (x : H) = x := by
  obtain ⟨y, hy⟩ := x.property
  change p.toLinearMap y = (x : H) at hy
  rw [← hy]
  exact congrArg (fun T : H →L[ℂ] H => T y) hp.isIdempotentElem.eq

@[simp] theorem projectionFiberRetraction_inclusion (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    (projectionFiberRetraction p hp).comp (projectionFiberInclusion p hp).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (projectionFiber p hp) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact projectionFiber_fixed p hp x

theorem norm_projectionFiberRetraction_le (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    ‖projectionFiberRetraction p hp‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖p x‖ ≤ 1 * ‖x‖
  exact (p.le_opNorm x).trans (mul_le_mul_of_nonneg_right
    (norm_projection_le_one p hp.isSelfAdjoint.star_eq hp.isIdempotentElem.eq) (norm_nonneg x))

/-- Compression is defined on every operator, even before support is proved. -/
def projectionFiberCompression (p : H →L[ℂ] H) (hp : IsStarProjection p) (T : H →L[ℂ] H) :
    projectionFiber p hp →L[ℂ] projectionFiber p hp :=
  (projectionFiberRetraction p hp).comp (T.comp (projectionFiberInclusion p hp).toContinuousLinearMap)

@[simp] theorem projectionFiberCompression_coe (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : H →L[ℂ] H) (x : projectionFiber p hp) :
    (projectionFiberCompression p hp T x : H) = p (T (x : H)) := rfl

/-- Extending the compressed supported operator by zero recovers it. -/
theorem projectionFiberCompression_extension
    (p : H →L[ℂ] H) (hp : IsStarProjection p) (T : H →L[ℂ] H)
    (hleft : p * T = T) (hright : T * p = T) :
    (projectionFiberInclusion p hp).toContinuousLinearMap.comp
      ((projectionFiberCompression p hp T).comp (projectionFiberRetraction p hp)) = T := by
  apply ContinuousLinearMap.ext
  intro x
  change p (T (p x)) = T x
  have hl := congrArg (fun A : H →L[ℂ] H => A (p x)) hleft
  have hr := congrArg (fun A : H →L[ℂ] H => A x) hright
  exact hl.trans hr

/-- No norm is lost by restricting a supported operator to the projection range. -/
theorem norm_projectionFiberCompression
    (p : H →L[ℂ] H) (hp : IsStarProjection p) (T : H →L[ℂ] H)
    (hleft : p * T = T) (hright : T * p = T) :
    ‖projectionFiberCompression p hp T‖ = ‖T‖ := by
  have h := norm_split_extension (projectionFiberInclusion p hp).toContinuousLinearMap
    (projectionFiberRetraction p hp)
    (projectionFiberInclusion p hp).norm_toContinuousLinearMap_le
    (norm_projectionFiberRetraction_le p hp) (projectionFiberRetraction_inclusion p hp)
    (projectionFiberCompression p hp T)
  rw [projectionFiberCompression_extension p hp T hleft hright] at h
  exact h.symm

theorem projectionFiber_invariant (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : H →L[ℂ] H) (hcomm : Commute p T) :
    ∀ x ∈ projectionFiber p hp, T x ∈ projectionFiber p hp := by
  rintro x ⟨y, rfl⟩
  refine ⟨T y, ?_⟩
  exact congrArg (fun A : H →L[ℂ] H => A y) hcomm.eq

/-- A commuting operator acts on the closed range by ordinary restriction. -/
def projectionFiberAction (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : H →L[ℂ] H) (hcomm : Commute p T) :
    projectionFiber p hp →L[ℂ] projectionFiber p hp :=
  T.restrict (projectionFiber_invariant p hp T hcomm)

@[simp] theorem projectionFiberAction_coe (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : H →L[ℂ] H) (hcomm : Commute p T) (x : projectionFiber p hp) :
    (projectionFiberAction p hp T hcomm x : H) = T (x : H) := rfl

theorem projectionFiberAction_eq_compression (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : H →L[ℂ] H) (hcomm : Commute p T) :
    projectionFiberAction p hp T hcomm = projectionFiberCompression p hp T := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact (projectionFiber_fixed p hp (projectionFiberAction p hp T hcomm x)).symm

variable {A : Type*} [CStarAlgebra A]

/-- A genuine representation commuting with a projection restricts to a
genuine unital representation on its actual Hilbert range. -/
def projectionFiberRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (p : H →L[ℂ] H) (hp : IsStarProjection p) (hcomm : ∀ a, Commute p (σ a)) :
    A →⋆ₐ[ℂ] (projectionFiber p hp →L[ℂ] projectionFiber p hp) where
  toFun a := projectionFiberAction p hp (σ a) (hcomm a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : H) (σ (star a) (x : H)) =
      inner ℂ y ((projectionFiberAction p hp (σ a) (hcomm a)).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : H) (σ (star a) (x : H)) =
      inner ℂ (σ a (y : H)) (x : H)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem projectionFiberRepresentation_coe
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hcomm : ∀ a, Commute p (σ a)) (a : A) (x : projectionFiber p hp) :
    (projectionFiberRepresentation σ p hp hcomm a x : H) = σ a (x : H) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CompressedFieldNorm
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem ae_isometric_field_left_support
    (T : H →L[ℂ] H) (R : Ω → F →L[ℂ] F)
    (hR : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J T f x = R x (f x)) :
    ∀ᵐ x ∂μ, p x * R x = R x := by
  apply ae_field_left_support μ _ _ p R hP hR
  rw [← isometricExtension_mul, one_mul]

theorem ae_isometric_field_right_support
    (T : H →L[ℂ] H) (R : Ω → F →L[ℂ] F)
    (hR : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J T f x = R x (f x)) :
    ∀ᵐ x ∂μ, R x * p x = R x := by
  apply ae_field_right_support μ _ _ p R hP hR
  rw [← isometricExtension_mul, mul_one]

theorem norm_le_iff_compressed_field
    (T : H →L[ℂ] H) (R : Ω → F →L[ℂ] F)
    (hR : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J T f x = R x (f x))
    (C : ℝ) (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ᵐ x ∂μ, ‖projectionFiberCompression (p x) (hp x) (R x)‖ ≤ C := by
  have hn := pointwise_field_norm_iff μ (isometricExtension J T) R hR C hC
  rw [isometricExtension_norm] at hn
  have hc : ∀ᵐ x ∂μ, ‖projectionFiberCompression (p x) (hp x) (R x)‖ = ‖R x‖ := by
    filter_upwards [ae_isometric_field_left_support μ J p hP T R hR,
      ae_isometric_field_right_support μ J p hP T R hR] with x hl hr
    exact norm_projectionFiberCompression (p x) (hp x) (R x) hl hr
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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConullFieldExtension
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend fields from a conull measurable base by zero while retaining
their actual L² action on the original measure space. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {Ω F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (μ : Measure Ω) (s : Set Ω)

theorem zeroExtendOperatorField_action (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (T : Lp F 2 μ →L[ℂ] Lp F 2 μ) (Q : s → F →L[ℂ] F)
    (hQ : ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ, T f x = Q x (f x)) :
    ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, T f x = zeroExtendOperatorField s Q x (f x) := by
  intro f
  have hmem : ∀ᵐ x ∂μ, x ∈ s := by
    rw [ae_iff]
    exact hnull
  have hr : ∀ᵐ x ∂μ.restrict s, T f x = zeroExtendOperatorField s Q x (f x) := by
    apply (ae_restrict_iff_subtype hs).mpr
    filter_upwards [hQ f] with x hx
    simpa only [zeroExtendOperatorField, dite_eq_left x.property] using hx
  filter_upwards [hmem, ae_imp_of_ae_restrict hr] with x hx hh
  exact hh hx

variable [CompleteSpace F]

omit [MeasurableSpace Ω] in
theorem zeroExtendOperatorField_mem
    (P : Ω → VonNeumannAlgebra F) (Q : s → F →L[ℂ] F)
    (hQ : ∀ x : s, Q x ∈ P x) :
    ∀ x, zeroExtendOperatorField s Q x ∈ P x := by
  intro x
  by_cases hx : x ∈ s
  · simpa only [zeroExtendOperatorField, dite_eq_left hx] using hQ ⟨x, hx⟩
  · simp only [zeroExtendOperatorField, dite_eq_right hx]
    exact (P x).toStarSubalgebra.zero_mem

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NonunitalRangeRepresentation
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonunital representation of a unital C-star algebra becomes unital
on the range of the image of its unit. This also covers the zero fibers
used outside a conull spectral base. -/

noncomputable section
namespace KadisonSimilarity

variable {B K : Type*} [CStarAlgebra B]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem nonunitalUnitProjection_isStarProjection (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    IsStarProjection (nonunitalUnitProjection ρ) :=
  (IsStarProjection.one B).map ρ

theorem nonunitalUnitProjection_commutes (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    Commute (nonunitalUnitProjection ρ) (ρ b) := by
  change ρ 1 * ρ b = ρ b * ρ 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

def nonunitalRangeRepresentation (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    B →⋆ₐ[ℂ]
      (projectionFiber (nonunitalUnitProjection ρ) (nonunitalUnitProjection_isStarProjection ρ) →L[ℂ]
        projectionFiber (nonunitalUnitProjection ρ) (nonunitalUnitProjection_isStarProjection ρ)) where
  toFun b := projectionFiberAction (nonunitalUnitProjection ρ)
    (nonunitalUnitProjection_isStarProjection ρ) (ρ b) (nonunitalUnitProjection_commutes ρ b)
  map_zero' := by ext x; simp
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact projectionFiber_fixed _ _ x
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (algebraMap ℂ B c) (x : K) = c • (x : K)
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    change c • (nonunitalUnitProjection ρ (x : K)) = c • (x : K)
    rw [projectionFiber_fixed]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : K) (ρ (star a) (x : K)) =
      inner ℂ y ((projectionFiberAction _ _ (ρ a) _).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : K) (ρ (star a) (x : K)) = inner ℂ (ρ a (y : K)) (x : K)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem nonunitalRangeRepresentation_coe
    (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (b : B)
    (x : projectionFiber (nonunitalUnitProjection ρ) (nonunitalUnitProjection_isStarProjection ρ)) :
    (nonunitalRangeRepresentation ρ b x : K) = ρ b (x : K) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConullRepresentationExtension
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the original algebra's conull fiber representations by zero.
The maps remain nonunital star homomorphisms at every base point, so their
unit projections give genuine representations on every projection fiber. -/

noncomputable section
namespace KadisonSimilarity

variable {Ω B F : Type*} [CStarAlgebra B]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (s : Set Ω)

theorem zeroExtendNonunitalRepresentation_apply
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F)) (b : B) (x : Ω) :
    zeroExtendNonunitalRepresentation s ρ x b =
      zeroExtendOperatorField s (fun y => ρ y (Unitization.inr b)) x := by
  classical
  by_cases hx : x ∈ s
  · simp only [zeroExtendNonunitalRepresentation, zeroExtendOperatorField, dite_eq_left hx,
      NonUnitalStarAlgHom.comp_apply,
      Unitization.inrNonUnitalStarAlgHom_apply]
    rfl
  · simp only [zeroExtendNonunitalRepresentation, zeroExtendOperatorField, dite_eq_right hx,
      NonUnitalStarAlgHom.zero_apply]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSubalgebraTransfer
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction to the closed algebra generated by the free factors
preserves both commutation and the small-corner estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry
variable (G : TracialCornerGeometry P H) (L : StarSubalgebra ℂ P)

variable [IsClosed (L : Set P)]

/-- A corner element of a subalgebra is the same ambient corner element,
with exactly the same norm. -/
def cornerInclusion (e : L) (he : IsStarProjection e)
    (x : CStarCorner e he) : CStarCorner (e : P) (he.map L.subtype) :=
  ⟨((x : L) : P), ⟨congrArg (fun y : L => (y : P)) x.property.1,
    congrArg (fun y : L => (y : P)) x.property.2⟩⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteTracialExpectation
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact trace-pairing expectation consumed by the free-corner proof is
constructed on concrete finite tracial von Neumann inclusions and transported
through faithful algebra coordinates. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

section Concrete
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {N M : VonNeumannAlgebra H}

local instance expectationAlgebra_closed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  Generator.Tracial.base_norm_closed M

end Concrete

section Transport
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Transport the trace-pairing characterization to the inverse image of
the same concrete subalgebra. Only the actual trace identity is required. -/
def TracialExpectation.comapEquiv
    {τA : A →ₗ[ℂ] ℂ} {τB : B →ₗ[ℂ] ℂ} {S : StarSubalgebra ℂ B}
    (E : TracialExpectation τB S) (e : A ≃⋆ₐ[ℂ] B)
    (hτ : ∀ a, τB (e a) = τA a) :
    TracialExpectation τA (S.comap e.toStarAlgHom) where
  map := e.symm.toAlgEquiv.toLinearMap.comp (E.map.comp e.toAlgEquiv.toLinearMap)
  range x := by
    change e (e.symm (E.map (e x))) ∈ S
    rw [e.apply_symm_apply]
    exact E.range (e x)
  pairing x c hc := by
    change τA (c * e.symm (E.map (e x))) = τA (c * x)
    rw [← hτ, map_mul, e.apply_symm_apply, E.pairing (e x) (e c) hc,
      ← map_mul, hτ]

end Transport
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialNormalSpan
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

local instance ambient_closed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  base_norm_closed M

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalFactorGeneration
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

local instance factorClosure_closed :
    IsClosed ((factorAlgebra A D).topologicalClosure : Set P) :=
  (factorAlgebra A D).isClosed_topologicalClosure

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_UnitizationProjection
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover a represented unital algebra from its unitization by restricting
to the image of its old unit. -/

noncomputable section
namespace KadisonSimilarity

variable {B K : Type*} [CStarAlgebra B]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem unitizationProjection_isStarProjection
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    IsStarProjection (unitizationProjection ρ) := by
  have h : IsStarProjection (Unitization.inr (1 : B) : Unitization ℂ B) := by
    rw [Unitization.isStarProjection_inr_iff]
    exact IsStarProjection.one B
  exact h.map ρ

theorem unitizationProjection_commutes
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : Unitization ℂ B) :
    Commute (unitizationProjection ρ) (ρ b) :=
  (unitization_old_unit_commutes b).map ρ

/-- The original algebra acts unitally on the range of its own unit, even
though its inclusion into its unitization is nonunital. -/
def unitizationRangeRepresentation (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    B →⋆ₐ[ℂ]
      (projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ) →L[ℂ]
        projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ)) where
  toFun b := projectionFiberAction (unitizationProjection ρ)
    (unitizationProjection_isStarProjection ρ) (ρ (Unitization.inr b))
    (unitizationProjection_commutes ρ _)
  map_zero' := by ext x; simp
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact projectionFiber_fixed _ _ x
  map_add' a b := by ext x; simp
  map_mul' a b := by
    ext x
    simp [Unitization.inr_mul, mul_apply_eq_comp]
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (Unitization.inr (algebraMap ℂ B c)) (x : K) = c • (x : K)
    have heq : (Unitization.inr (algebraMap ℂ B c) : Unitization ℂ B) =
        c • Unitization.inr (1 : B) := by
      rw [Algebra.algebraMap_eq_smul_one, Unitization.inr_smul]
    rw [heq, map_smul]
    change c • (unitizationProjection ρ (x : K)) = c • (x : K)
    rw [projectionFiber_fixed]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : K) (ρ (Unitization.inr (star a)) (x : K)) =
      inner ℂ y ((projectionFiberAction _ _ (ρ (Unitization.inr a)) _).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : K) (ρ (Unitization.inr (star a)) (x : K)) =
      inner ℂ (ρ (Unitization.inr a) (y : K)) (x : K)
    rw [Unitization.inr_star, map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem unitizationRangeRepresentation_coe
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B)
    (x : projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ)) :
    (unitizationRangeRepresentation ρ b x : K) = ρ (Unitization.inr b) (x : K) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_JointFiberRestriction
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- Both old units act by exactly the same ambient projection. -/
theorem unitizationRestrict_projection (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) :
    unitizationProjection (unitizationRestrict φ ρ) = unitizationProjection ρ := by
  change unitizationRestrict φ ρ (Unitization.inr 1) = ρ (Unitization.inr 1)
  rw [unitizationRestrict_inr, map_one]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_GlobalFiberRestriction
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem nonunitalRestrict_projection (φ : B →⋆ₐ[ℂ] S)
    (τ : S →⋆ₙₐ[ℂ] (F →L[ℂ] F)) :
    nonunitalUnitProjection (τ.comp φ.toNonUnitalStarAlgHom) = nonunitalUnitProjection τ := by
  change τ (φ 1) = τ 1
  rw [map_one]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_UnitizationFiberClosure
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bicommutant closure on the old-unit fibers

Restriction to the range of the old unit sends the represented unitization
bicommutant into the bicommutant of the genuine original-algebra
representation. This uses commutants and actual compression, including when
the range is the zero Hilbert space.
-/

noncomputable section
namespace KadisonSimilarity

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Retraction onto the closed range of an orthogonal projection is the
Hilbert adjoint of its inclusion. -/
theorem projectionFiberRetraction_eq_adjoint (p : K →L[ℂ] K) (hp : IsStarProjection p) :
    projectionFiberRetraction p hp =
      (projectionFiberInclusion p hp).toContinuousLinearMap.adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (p x) (y : K) = inner ℂ x (y : K)
  have hadjoint : p.adjoint = p := hp.isSelfAdjoint.star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right p x (y : K), hadjoint,
    projectionFiber_fixed]

/-- A supported operator is the zero extension of its actual compression. -/
theorem isometricExtension_projectionFiberCompression
    (p : K →L[ℂ] K) (hp : IsStarProjection p) (T : K →L[ℂ] K)
    (hleft : p * T = T) (hright : T * p = T) :
    isometricExtension (projectionFiberInclusion p hp)
      (projectionFiberCompression p hp T) = T := by
  rw [isometricExtension, ← projectionFiberRetraction_eq_adjoint,
    ContinuousLinearMap.comp_assoc]
  exact projectionFiberCompression_extension p hp T hleft hright

variable {B : Type*} [CStarAlgebra B]

theorem unitization_inr_left_support
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    unitizationProjection ρ * ρ (Unitization.inr b) = ρ (Unitization.inr b) := by
  change ρ (Unitization.inr (1 : B)) * ρ (Unitization.inr b) = _
  rw [← map_mul, ← Unitization.inr_mul, one_mul]

theorem unitization_inr_right_support
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    ρ (Unitization.inr b) * unitizationProjection ρ = ρ (Unitization.inr b) := by
  change ρ (Unitization.inr b) * ρ (Unitization.inr (1 : B)) = _
  rw [← map_mul, ← Unitization.inr_mul, mul_one]

theorem unitizationRangeRepresentation_eq_compression
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    unitizationRangeRepresentation ρ b =
      projectionFiberCompression (unitizationProjection ρ)
        (unitizationProjection_isStarProjection ρ) (ρ (Unitization.inr b)) :=
  projectionFiberAction_eq_compression _ _ _ (unitizationProjection_commutes ρ _)

/-- The zero extension of the original algebra's range representation is
the given represented inr element, not a new abstract representation. -/
theorem isometricExtension_unitizationRangeRepresentation
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    isometricExtension (projectionFiberInclusion (unitizationProjection ρ)
      (unitizationProjection_isStarProjection ρ)) (unitizationRangeRepresentation ρ b) =
      ρ (Unitization.inr b) := by
  rw [unitizationRangeRepresentation_eq_compression]
  exact isometricExtension_projectionFiberCompression _ _ _
    (unitization_inr_left_support ρ b) (unitization_inr_right_support ρ b)

/-- Operators in the commutant of the genuine old-unit range
representation extend to operators commuting with the full unitization. -/
theorem unitizationRange_commutant_extension_commutes
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (T : projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ)
      →L[ℂ] projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ))
    (hT : T ∈ (representationVonNeumannAlgebra (unitizationRangeRepresentation ρ)).commutant)
    (a : Unitization ℂ B) :
    isometricExtension (projectionFiberInclusion (unitizationProjection ρ)
      (unitizationProjection_isStarProjection ρ)) T * ρ a =
      ρ a * isometricExtension (projectionFiberInclusion (unitizationProjection ρ)
        (unitizationProjection_isStarProjection ρ)) T := by
  have hinr (b : B) :
      isometricExtension (projectionFiberInclusion (unitizationProjection ρ)
        (unitizationProjection_isStarProjection ρ)) T * ρ (Unitization.inr b) =
      ρ (Unitization.inr b) * isometricExtension
        (projectionFiberInclusion (unitizationProjection ρ)
          (unitizationProjection_isStarProjection ρ)) T := by
    have h := congrArg (isometricExtension (projectionFiberInclusion
      (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ)))
      (VonNeumannAlgebra.mem_commutant_iff.mp hT
        (unitizationRangeRepresentation ρ b)
        (mem_representationVonNeumannAlgebra (unitizationRangeRepresentation ρ) b)).symm
    simpa only [isometricExtension_mul,
      isometricExtension_unitizationRangeRepresentation] using h
  rw [unitization_representation_decomposition ρ a, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hinr]

/-- Compression to the old-unit fiber preserves represented bicommutant
membership. No support condition on the original operator is required. -/
theorem unitizationFiberCompression_mem
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Q : K →L[ℂ] K) (hQ : Q ∈ representationVonNeumannAlgebra ρ) :
    projectionFiberCompression (unitizationProjection ρ)
      (unitizationProjection_isStarProjection ρ) Q ∈
        representationVonNeumannAlgebra (unitizationRangeRepresentation ρ) := by
  rw [projectionFiberCompression, projectionFiberRetraction_eq_adjoint]
  exact compression_mem_of_extended_commutant
    (projectionFiberInclusion (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ))
    (representationVonNeumannAlgebra (unitizationRangeRepresentation ρ)) ρ
    (unitizationRange_commutant_extension_commutes ρ) Q hQ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SupportedFiberAlgebra
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic identities for compressing supported operators to the actual
range of an orthogonal projection. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (p : H →L[ℂ] H) (hp : IsStarProjection p)

theorem projectionFiberCompression_sub (T U : H →L[ℂ] H) :
    projectionFiberCompression p hp (T - U) =
      projectionFiberCompression p hp T - projectionFiberCompression p hp U := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change p ((T - U) (x : H)) = p (T (x : H)) - p (U (x : H))
  simp only [sub_apply, map_sub]

theorem projectionFiberCompression_mul (T U : H →L[ℂ] H) (hU : p * U = U) :
    projectionFiberCompression p hp (T * U) =
      projectionFiberCompression p hp T * projectionFiberCompression p hp U := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change p (T (U (x : H))) = p (T (p (U (x : H))))
  have h := congrArg (fun R : H →L[ℂ] H => R (x : H)) hU
  change p (U (x : H)) = U (x : H) at h
  rw [h]

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

/-- The genuine old-unit range at every base point, including zero fibers
on the null complement of the original representations. -/
abbrev conullProjectionFiber {A : Type u} [CStarAlgebra A]
    (s : Set Ω) (ρ : ∀ _x : s, Unitization ℂ A →⋆ₐ[ℂ] (F →L[ℂ] F)) (x : Ω) : Type u :=
  projectionFiber (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
    (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x))

variable (μ : Measure Ω) [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace F]

omit [CompleteSpace F] in
theorem fields_eq_of_same_action
    (T : Lp F 2 μ →L[ℂ] Lp F 2 μ) (R Q : Ω → F →L[ℂ] F)
    (hR : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, T f x = R x (f x))
    (hQ : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, T f x = Q x (f x)) :
    ∀ᵐ x ∂μ, R x = Q x := by
  apply ae_operator_eq_of_forall_vectors
  intro v
  filter_upwards [pointwise_action_column μ T R hR v,
    pointwise_action_column μ T Q hQ v] with x hr hq
  exact hr.symm.trans hq

theorem isometric_raw_field_sub
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (M : StarSubalgebra ℂ (H →L[ℂ] H))
    (R : M → Ω → F →L[ℂ] F)
    (hR : ∀ T : M, ∀ f : Lp F 2 μ,
      ∀ᵐ x ∂μ, isometricExtension J (T : H →L[ℂ] H) f x = R T x (f x))
    (T U : M) : ∀ᵐ x ∂μ, R (T - U) x = R T x - R U x := by
  apply ae_operator_eq_of_forall_vectors
  intro v
  have ht := pointwise_action_column μ _ _ (hR T) v
  have hu := pointwise_action_column μ _ _ (hR U) v
  have htu := pointwise_action_column μ _ _ (hR (T - U)) v
  change ∀ᵐ x ∂μ, isometricExtension J
    ((T : H →L[ℂ] H) - (U : H →L[ℂ] H)) (Lp.const 2 μ v) x = R (T - U) x v at htu
  rw [isometricExtension_sub] at htu
  filter_upwards [ht, hu, htu,
    Lp.coeFn_sub (isometricExtension J T (Lp.const 2 μ v))
      (isometricExtension J U (Lp.const 2 μ v))] with x ht hu htu hs
  simpa only [sub_apply, hs, Pi.sub_apply, ht, hu] using htu.symm

theorem isometric_raw_field_mul
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (M : StarSubalgebra ℂ (H →L[ℂ] H))
    (R : M → Ω → F →L[ℂ] F)
    (hR : ∀ T : M, ∀ f : Lp F 2 μ,
      ∀ᵐ x ∂μ, isometricExtension J (T : H →L[ℂ] H) f x = R T x (f x))
    (T U : M) : ∀ᵐ x ∂μ, R (T * U) x = R T x * R U x := by
  apply pointwise_field_mul μ _ _ _ _ _ (hR T) (hR U)
  have h := hR (T * U)
  change ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
    isometricExtension J ((T : H →L[ℂ] H) * (U : H →L[ℂ] H)) f x = R (T * U) x (f x) at h
  simpa only [isometricExtension_mul] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_AmplifyExponential
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def amplifyAlgHom (n : ℕ) :
    (H →L[ℂ] H) →ₐ[ℂ] (HilbertCopies H n →L[ℂ] HilbertCopies H n) where
  toFun Y := amplify Y n
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp
  map_add' _ _ := by ext x i; simp
  map_mul' _ _ := by ext x i; simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  commutes' c := by ext x i; simp [Algebra.algebraMap_eq_smul_one]

omit [CompleteSpace H] in
@[simp] theorem amplify_smul (c : ℝ) (Y : H →L[ℂ] H) (n : ℕ) :
    amplify (c • Y) n = c • amplify Y n := by ext x i; simp

omit [CompleteSpace H] in
@[simp] theorem amplify_neg (Y : H →L[ℂ] H) (n : ℕ) :
    amplify (-Y) n = -amplify Y n := by ext x i; simp

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_ArvesonCompleteNorm
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete completely bounded commutator norm controls the actual
entrywise C-star matrix amplifications needed for factorization. -/

noncomputable section
namespace KadisonSimilarity
open scoped ENNReal ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonSimilarity.arvesonComplete_closed
def commutantDerivation (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    M.commutant.toStarSubalgebra →L[ℂ] (H →L[ℂ] H) :=
  (innerDerivation T).comp M.commutant.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_BoundedMatrixHom
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedMatrixHom_apply
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

def boundedMatrixHom (π : BoundedUnitalHom A H) (n : ℕ) :
    BoundedUnitalHom (CStarMatrix (Fin n) (Fin n) A) (HilbertCopies H n) := by
  let ρ := (operatorMatrixRepresentation (H := H) n).toAlgHom.comp
    (π.1.mapMatrix.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.toAlgHom)
  refine ⟨ρ, ?_⟩
  have hmap : Continuous (fun X : Matrix (Fin n) (Fin n) A => X.map π.1) := by
    exact continuous_pi fun i => continuous_pi fun j =>
      π.2.comp ((continuous_apply j).comp (continuous_apply i))
  have hop : Continuous (fun X : Matrix (Fin n) (Fin n) (H →L[ℂ] H) => matrixOperator X) := by
    let L := (matrixRepresentation (H := H) n).toLinearMap.mkContinuous 1
      (fun X => by
        simpa using (NonUnitalStarAlgHom.norm_apply_le (matrixRepresentation (H := H) n) X))
    exact L.continuous.comp CStarMatrix.ofMatrixL.continuous
  exact hop.comp (hmap.comp CStarMatrix.ofMatrixL.symm.continuous)

@[simp] theorem boundedMatrixHom_apply (π : BoundedUnitalHom A H) (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) A) (ξ : HilbertCopies H n) (i : Fin n) :
    (boundedMatrixHom π n).1 X ξ i = ∑ j, π.1 (X i j) (ξ j) := by
  exact matrixOperator_apply _ ξ i

end KadisonSimilarity

end

end OAI
end


