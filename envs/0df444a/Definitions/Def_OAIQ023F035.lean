-- Prove2me | Definitions.Def_OAIQ023F035
-- name    : OAIQ023F035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T19:46:27.017825+00:00
-- url     : https://prove2.me/theorems/9a5b1b36-c4bb-4ebf-ac3a-50069370f801
-- title:
--   Definitions bundle OAIQ023F035 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 15 definitions and 7 theorems. The definitions and types are `OAI.LittleFinitistic.SelectedChainHomology.D0Iso`, `OAI.LittleFinitistic.SelectedChainHomology.D1Iso`, `OAI.LittleFinitistic.SelectedChainHomology.D2Iso`, `OAI.LittleFinitistic.SelectedDiagramEvaluation.D0Iso`, `OAI.LittleFinitistic.SelectedDiagramEvaluation.D1Iso`, `OAI.LittleFinitistic.SelectedDiagramEvaluation.D2Iso`, `OAI.LittleFinitistic.SelectedDiagramEvaluation.V0Iso`, `OAI.LittleFinitistic.SelectedNativeEvaluation.D0Iso`, `OAI.LittleFinitistic.SelectedNativeEvaluation.D1Iso`, `OAI.LittleFinitistic.SelectedNativeEvaluation.D2Iso`, `OAI.LittleFinitistic.SelectedRealization.coordinates`, `OAI.LittleFinitistic.SourceImageEvaluation.corner`, `OAI.LittleFinitistic.SourceImageEvaluation.oddDoubleImageIso`, `OAI.LittleFinitistic.SourceImageEvaluation.shiftedImageIso`, `OAI.LittleFinitistic.SourceImageEvaluation.summandImageIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Localization_SourceActionEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Localization/SourceActionEvaluation.lean), [`Finitistic_Localization_SourceCornerEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Localization/SourceCornerEvaluation.lean), [`Finitistic_Localization_SourceImageEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Localization/SourceImageEvaluation.lean), [`Finitistic_Localization_SourceOddDoubleEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Localization/SourceOddDoubleEvaluation.lean), [`Finitistic_Selected_SelectedChainHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedChainHomology.lean), [`Finitistic_Selected_SelectedDiagramEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedDiagramEvaluation.lean), [`Finitistic_Selected_SelectedNativeEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedNativeEvaluation.lean), [`Finitistic_Selected_SelectedRealization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedRealization.lean).
--
--   **Imports.** It imports the bundle `OAIQ023F033` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ023F037`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F033

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceActionEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SourceImageEvaluation.instAdditiveKaroubiQRelationsFiniteVectorDerivedCompleted
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceActionEvaluation
open QuadraticEncoding SelectionEncoding QuadraticPresentation
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

/-- The native theta evaluates to the entire R-action, not just its generators. -/
theorem action_evaluates : evaluated (Y := Y) E = given (Y := Y) E := by
  let q := originalMap k (Fin E.generators) (QuotientAction.polynomial E.relations)
  have h : ((evaluated (Y := Y) E).comp E.equiv.toAlgHom).comp q =
      ((given (Y := Y) E).comp E.equiv.toAlgHom).comp q := by
    apply FreeAlgebra.hom_ext
    funext a
    exact evaluated_generator E a
  apply AlgHom.ext
  intro r
  obtain ⟨f,hf⟩ := (original k (Fin E.generators) (QuotientAction.polynomial E.relations)).mkₐ_surjective
    (α := k) (E.equiv.symm r)
  have hr : E.equiv (q f) = r := by rw [show q f = E.equiv.symm r from hf]; exact E.equiv.apply_symm_apply r
  have hh := AlgHom.congr_fun h f
  simpa only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,hr] using hh

theorem action_square (r : R) :
    (evaluation (Y := Y) E).map (SourceQuotientAction.theta E r) ≫ (vertexIso (Y := Y) E 0).hom =
      (vertexIso (Y := Y) E 0).hom ≫
        (vectorStalk (k := k)).map (liftedEndHom ((Algebra.lsmul k k Y) r)) := by
  have h := congrArg (fun f => (vertexIso (Y := Y) E 0).hom ≫ f)
    (AlgHom.congr_fun (action_evaluates (Y := Y) E) r)
  dsimp [evaluated,given,identifiedEndHom] at h
  simpa only [← Category.assoc,Iso.hom_inv_id,Category.id_comp,Category.comp_id] using h


/-- Whole-action compatibility in the bounded finite-dimensional derived target. -/
theorem derived_action_square (r : R) :
    (SourceEvaluation.derived (representation (Y := Y) E) ⋙ derivedTargetInclusion (k := k)).map
      (SourceQuotientAction.theta E r) ≫
        (SourceEvaluation.derivedVertexIso (representation (Y := Y) E) 0).hom =
    (SourceEvaluation.derivedVertexIso (representation (Y := Y) E) 0).hom ≫
      DerivedCategory.Qh.map ((vectorStalk (k := k)).map (liftedEndHom ((Algebra.lsmul k k Y) r))) := by
  have h := congrArg DerivedCategory.Qh.map (action_square (Y := Y) E r)
  simp only [Functor.map_comp] at h
  exact h

end LittleFinitistic.SourceActionEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceImageEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation

open QuadraticEncoding FiniteProjectiveHomotopy
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

lemma projection_inclusion (e : R) :
    projection (Y := Y) E e ≫ inclusion (Y := Y) E e =
      (evaluation (Y := Y) E ⋙ derivedTargetInclusion (k := k)).map (SourceQuotientAction.theta E e) := by
  exact sandwich_map_eq ((vectorStalk (k := k)) ⋙ DerivedCategory.Qh)
    (vertexIso (Y := Y) E) (imageProjection (action (k := k) (Y := Y) e).hom)
    (imageInclusion (action (k := k) (Y := Y) e).hom) (action (k := k) (Y := Y) e)
    ((evaluation (Y := Y) E ⋙ derivedTargetInclusion (k := k)).map (SourceQuotientAction.theta E e))
    (image_projection_inclusion _) (SourceActionEvaluation.derived_action_square (Y := Y) E e)

def summandImageIso (e : R) (he : e*e=e) :
    (completed (Y := Y) E).obj (U E e he) ≅ imageDerived (k := k) (Y := Y) e :=
  completedExtensionImageIso (evaluation (Y := Y) E) (U E e he) (imageDerived (k := k) (Y := Y) e)
    ((derivedTargetInclusion (k := k)).preimage (projection (Y := Y) E e))
    ((derivedTargetInclusion (k := k)).preimage (inclusion (Y := Y) E e))
    (by
      apply (derivedTargetInclusion (k := k)).map_injective
      rw [Functor.map_comp]
      erw [Functor.map_preimage,Functor.map_preimage]
      exact projection_inclusion E e)
    (by
      apply (derivedTargetInclusion (k := k)).map_injective
      erw [Functor.map_comp,CategoryTheory.Functor.map_id]
      erw [Functor.map_preimage,Functor.map_preimage]
      exact inclusion_projection E e he)
end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceCornerEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation

open QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

def corner (e a : R) (he : e*e=e) : U E e he ⟶ U E e he :=
  ⟨SourceQuotientAction.theta E (e*a*e), by
    change ((SourceQuotientAction.theta E) e * (SourceQuotientAction.theta E) (e*a*e)) *
      (SourceQuotientAction.theta E) e = _
    simp only [← map_mul]
    congr 1
    simp only [← mul_assoc,he]
    rw [mul_assoc (e*a) e e,he]⟩

lemma corner_projection_square (e a : R) (he : e*e=e) :
    (evaluation (Y := Y) E ⋙ derivedTargetInclusion (k := k)).map (SourceQuotientAction.theta E (e*a*e)) ≫
      projection (Y := Y) E e = projection (Y := Y) E e ≫
        (derivedTargetInclusion (k := k)).map (imageCorner (k := k) (Y := Y) e a) := by
  unfold imageCorner
  erw [Functor.map_preimage]
  have h := image_corner_square (action (k := k) (Y := Y) e).hom (action (k := k) (Y := Y) a).hom (action_idem (k := k) (Y := Y) e he)
  have hc : action (k := k) (Y := Y) (e*a*e) = ModuleCat.ofHom
      ((action (k := k) (Y := Y) e).hom * (action (k := k) (Y := Y) a).hom * (action (k := k) (Y := Y) e).hom) := by
    simp only [action,map_mul]
    rfl
  rw [← hc] at h
  exact map_projection_square ((vectorStalk (k := k)) ⋙ DerivedCategory.Qh)
    (vertexIso (Y := Y) E) (imageProjection (action (k := k) (Y := Y) e).hom)
    (action (k := k) (Y := Y) (e*a*e))
    (imageCornerEnd (action (k := k) (Y := Y) e).hom (action (k := k) (Y := Y) a).hom)
    ((evaluation (Y := Y) E ⋙ derivedTargetInclusion (k := k)).map
      (SourceQuotientAction.theta E (e*a*e)))
    (SourceActionEvaluation.derived_action_square (Y := Y) E (e*a*e)) h

theorem completed_corner_square (e a : R) (he : e*e=e) :
    (completed (Y := Y) E).map (corner E e a he) ≫ (summandImageIso (Y := Y) E e he).hom =
      (summandImageIso (Y := Y) E e he).hom ≫ imageCorner (k := k) (Y := Y) e a := by
  apply completedExtensionImageSquare
  apply (derivedTargetInclusion (k := k)).map_injective
  rw [Functor.map_comp,Functor.map_comp]
  erw [Functor.map_preimage]
  exact corner_projection_square E e a he

lemma selecting_action_eq_corner (e : R) (he : e*e=e) (hc : ∀ r : R,e*r=r*e)
    (alpha : R →ₐ[k] R) (r : R) :
    FormalSummandAction.action (SourceQuotientAction.theta E) e he hc alpha r =
      corner E e (alpha r) he := by
  apply Karoubi.Hom.ext
  exact FormalSummandAction.action_f _ _ _ _ _ _
end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceOddDoubleEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation

open QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

def shiftedImageIso (e : R) (he : e*e=e) (n : ℤ) :
    (completed (Y := Y) E).obj (OddDouble.formalShift (U E e he) n) ≅
      (imageDerived (k := k) (Y := Y) e)⟦n⟧ :=
  (shiftIso (Y := Y) E n).app (U E e he) ≪≫
    (shiftFunctor _ n).mapIso (summandImageIso (Y := Y) E e he)

attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instHasFiniteBiproductsKaroubiQRelations
attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instHasBinaryBiproductsKaroubiQRelations
attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instPreservesBinaryBiproductsKaroubiQRelationsFiniteVectorDerivedCompleted
def oddDoubleImageIso (e : R) (he : e*e=e) :
    (completed (Y := Y) E).obj (U E e he ⊞ OddDouble.formalShift (U E e he) 3) ≅
      imageDerived (k := k) (Y := Y) e ⊞ (imageDerived (k := k) (Y := Y) e)⟦(3 : ℤ)⟧ :=
  (completed (Y := Y) E).mapBiprod _ _ ≪≫
    biprod.mapIso (summandImageIso (Y := Y) E e he) (shiftedImageIso (Y := Y) E e he 3)

end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedDiagramEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.testModule_module _root_.OAI.LittleFinitistic.testModule_scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedDiagramEvaluation
open QuadraticEncoding SelectedFixedDiagram SourceImageEvaluation
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

/-- Evaluation of the one fixed actual V0 is precisely eY direct-sum eY[3]. -/
def V0Iso : (F (Y := Y)).obj fixed.V0 ≅ target (Y := Y) :=
  (factors (Y := Y) encoding).symm.app fixed.V0 ≪≫
    ((G (Y := Y)).mapIso fixed.iso ≪≫ oddDoubleImageIso (Y := Y) encoding e idem)

def D0Iso : (sourceEvaluation (Y := Y)).obj fixed.D0 ≅ target (Y := Y) :=
  (sourceFactors (Y := Y)).symm.app fixed.D0 ≪≫ ((F (Y := Y)).mapIso fixed.phi0 ≪≫ V0Iso (Y := Y))
def D1Iso : (sourceEvaluation (Y := Y)).obj fixed.D1 ≅ target (Y := Y) :=
  (sourceFactors (Y := Y)).symm.app fixed.D1 ≪≫ ((F (Y := Y)).mapIso fixed.phi1 ≪≫ V0Iso (Y := Y))
def D2Iso : (sourceEvaluation (Y := Y)).obj fixed.D2 ≅ target (Y := Y) :=
  (sourceFactors (Y := Y)).symm.app fixed.D2 ≪≫ ((F (Y := Y)).mapIso fixed.phi2 ≪≫ V0Iso (Y := Y))

end LittleFinitistic.SelectedDiagramEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedNativeEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedNativeEvaluation
open QuadraticEncoding SourceImageEvaluation FiniteProjectiveHomotopy SelectedFixedDiagram
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

def D0Iso : (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).obj fixed.D0 ≅ target (Y := Y) :=
  SelectedDiagramEvaluation.D0Iso ≪≫ targetIso
def D1Iso : (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).obj fixed.D1 ≅ target (Y := Y) :=
  SelectedDiagramEvaluation.D1Iso ≪≫ targetIso
def D2Iso : (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).obj fixed.D2 ≅ target (Y := Y) :=
  SelectedDiagramEvaluation.D2Iso ≪≫ targetIso
end LittleFinitistic.SelectedNativeEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedChainHomology
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedChainHomology
open QuadraticEncoding SelectedFixedDiagram SelectedNativeEvaluation SelectedTensorComparison
open SelectedTargetHomology
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

/-- All three actual tensors have the primary H(Y) as homology in both selected degrees. -/
def D0Iso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (complex (Y := Y) fixed.D0).homology n ≅ H (Y := Y) :=
  homologyIso _ SelectedNativeEvaluation.D0Iso n hn
def D1Iso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (complex (Y := Y) fixed.D1).homology n ≅ H (Y := Y) :=
  homologyIso _ SelectedNativeEvaluation.D1Iso n hn
def D2Iso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (complex (Y := Y) fixed.D2).homology n ≅ H (Y := Y) :=
  homologyIso _ SelectedNativeEvaluation.D2Iso n hn

end LittleFinitistic.SelectedChainHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedRealization
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.SelectedRealization
open SelectedFixedDiagram QuadraticEncoding SelectedNativeEvaluation
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

attribute [local instance] OAI.LittleFinitistic.SelectedRealization.selectedModule
attribute [local instance] OAI.LittleFinitistic.SelectedRealization.selectedTower
def coordinates (n : ℤ) (hn : n = 0 ∨ n = -3) :
    ∀ v : Fin 3, (SelectedTensor.source (input (Y := Y)) v).homology n ≅ H (Y := Y) :=
  Fin.cases (SelectedChainHomology.D0Iso n hn)
    (Fin.cases (SelectedChainHomology.D1Iso n hn)
      (fun _ => SelectedChainHomology.D2Iso n hn))

end LittleFinitistic.SelectedRealization

end

end OAI
end


