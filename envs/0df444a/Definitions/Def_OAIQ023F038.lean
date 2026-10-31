-- Prove2me | Definitions.Def_OAIQ023F038
-- name    : OAIQ023F038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:07:48.451009+00:00
-- url     : https://prove2.me/theorems/048bcb0c-5840-4709-ae34-bd4e08a8d4e2
-- title:
--   Definitions bundle OAIQ023F038 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 5 definitions and 12 theorems. The definitions and types are `OAI.LittleFinitistic.FiniteSelectionFamily.realization`, `OAI.LittleFinitistic.SelectedRealization.cohomology`, `OAI.LittleFinitistic.SelectedRealization.realization`, `OAI.LittleFinitistic.SelectedShiftedRealization.realization`, `OAI.LittleFinitistic.SelectedShiftedRealization.realizationNested`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Localization_SourceOddDoubleEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Localization/SourceOddDoubleEvaluation.lean), [`Finitistic_Selected_SelectedChainHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedChainHomology.lean), [`Finitistic_Selected_SelectedDiagramEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedDiagramEvaluation.lean), [`Finitistic_Selected_SelectedNativeAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedNativeAction.lean), [`Finitistic_Selected_SelectedRealization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedRealization.lean), [`Finitistic_Selected_SelectedShiftedRealization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedShiftedRealization.lean), [`Finitistic_Selection_FiniteSelectionFamily`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selection/FiniteSelectionFamily.lean).
--
--   **Imports.** It imports the bundles `OAIQ023F036` and `OAIQ023F037` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.LittleFinitistic.Main.exists_counterexample`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F036
import Definitions.Def_OAIQ023F037

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceOddDoubleEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso
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

attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instHasFiniteBiproductsKaroubiQRelations
attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instHasBinaryBiproductsKaroubiQRelations
attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instPreservesBinaryBiproductsKaroubiQRelationsFiniteVectorDerivedCompleted
theorem oddDouble_selecting_square (e : R) (he : e*e=e) (hc : ∀ r : R,e*r=r*e)
    (alpha : R →ₐ[k] R) (r : R) :
    (completed (Y := Y) E).map
      (FormalSummandAction.oddDoubleAction (SourceQuotientAction.theta E) e he hc alpha r) ≫
      (oddDoubleImageIso (Y := Y) E e he).hom =
    (oddDoubleImageIso (Y := Y) E e he).hom ≫
      biprod.map (imageCorner (k := k) (Y := Y) e (alpha r)) ((imageCorner (k := k) (Y := Y) e (alpha r))⟦(3 : ℤ)⟧') := by
  have hc' := selecting_action_eq_corner E e he hc alpha r
  have hd := (BiprodEvaluationSquare.action_formula
    (SourceQuotientAction.theta E) e he hc alpha r).trans
      (congrArg₂ (fun f g => biprod.map f g) hc'
        (congrArg (OddDouble.formalShiftFunctor 3).map hc'))
  exact (congrArg (fun f => (completed (Y := Y) E).map f ≫
    (oddDoubleImageIso (Y := Y) E e he).hom) hd).trans
      (oddDouble_corner_square E e (alpha r) he)
end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedDiagramEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso _root_.OAI.LittleFinitistic.testModule_module _root_.OAI.LittleFinitistic.testModule_scalarTower
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

/-- The V0 identification intertwines every selected algebra element on both summands. -/
theorem V0_action (r : SelectionRing) :
    (F (Y := Y)).map (fixed.rho r) ≫ (V0Iso (Y := Y)).hom =
      (V0Iso (Y := Y)).hom ≫ targetAction (Y := Y) r := by
  have hf := (factors (Y := Y) encoding).inv.naturality (fixed.rho r)
  have hi := congrArg (fun f => (G (Y := Y)).map f) (fixed.equivariant r)
  simp only [Functor.map_comp] at hi
  have ho := oddDouble_selecting_square (Y := Y) encoding e idem central alpha r
  exact DiagramEvaluationSquares.compose _ _ _
    ((factors (Y := Y) encoding).symm.app fixed.V0)
    ((factors (Y := Y) encoding).symm.app fixed.V0)
    ((G (Y := Y)).mapIso fixed.iso ≪≫ oddDoubleImageIso (Y := Y) encoding e idem)
    ((G (Y := Y)).mapIso fixed.iso ≪≫ oddDoubleImageIso (Y := Y) encoding e idem)
    hf (DiagramEvaluationSquares.compose _ _ _
      ((G (Y := Y)).mapIso fixed.iso) ((G (Y := Y)).mapIso fixed.iso)
      (oddDoubleImageIso (Y := Y) encoding e idem) (oddDoubleImageIso (Y := Y) encoding e idem)
      hi ho)

/-- Every first-family arrow of the same fixed K diagram has its selected action. -/
theorem D_arrow01 (a : Fin (encoding.generators+1)) :
    (sourceEvaluation (Y := Y)).map (fixed.f a) ≫ (D1Iso (Y := Y)).hom =
      (D0Iso (Y := Y)).hom ≫ targetAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) := by
  have hn := (sourceFactors (Y := Y)).inv.naturality (fixed.f a)
  have hp := congrArg (fun f => (F (Y := Y)).map f) (fixed.arrow01 a)
  simp only [Functor.map_comp] at hp
  exact DiagramEvaluationSquares.compose _ _ _
    ((sourceFactors (Y := Y)).symm.app fixed.D0) ((sourceFactors (Y := Y)).symm.app fixed.D1)
    ((F (Y := Y)).mapIso fixed.phi0 ≪≫ V0Iso (Y := Y))
    ((F (Y := Y)).mapIso fixed.phi1 ≪≫ V0Iso (Y := Y)) hn
    (DiagramEvaluationSquares.compose _ _ _
      ((F (Y := Y)).mapIso fixed.phi0) ((F (Y := Y)).mapIso fixed.phi1)
      (V0Iso (Y := Y)) (V0Iso (Y := Y)) hp (V0_action _))

theorem D_arrow12 (a : Fin (encoding.generators+1)) :
    (sourceEvaluation (Y := Y)).map (fixed.g a) ≫ (D2Iso (Y := Y)).hom =
      (D1Iso (Y := Y)).hom ≫ targetAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) := by
  have hn := (sourceFactors (Y := Y)).inv.naturality (fixed.g a)
  have hp := congrArg (fun f => (F (Y := Y)).map f) (fixed.arrow12 a)
  simp only [Functor.map_comp] at hp
  exact DiagramEvaluationSquares.compose _ _ _
    ((sourceFactors (Y := Y)).symm.app fixed.D1) ((sourceFactors (Y := Y)).symm.app fixed.D2)
    ((F (Y := Y)).mapIso fixed.phi1 ≪≫ V0Iso (Y := Y))
    ((F (Y := Y)).mapIso fixed.phi2 ≪≫ V0Iso (Y := Y)) hn
    (DiagramEvaluationSquares.compose _ _ _
      ((F (Y := Y)).mapIso fixed.phi1) ((F (Y := Y)).mapIso fixed.phi2)
      (V0Iso (Y := Y)) (V0Iso (Y := Y)) hp (V0_action _))

end LittleFinitistic.SelectedDiagramEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedNativeAction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso
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
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

variable [FiniteDimensional ℂ Y]

theorem D_arrow01 (a : Fin (encoding.generators+1)) :
    (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).map (fixed.f a) ≫ (D1Iso (Y := Y)).hom =
      (D0Iso (Y := Y)).hom ≫ targetAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  DiagramEvaluationSquares.compose _ _ _ SelectedDiagramEvaluation.D0Iso
    SelectedDiagramEvaluation.D1Iso targetIso targetIso
    (SelectedDiagramEvaluation.D_arrow01 a) (target_square _)

theorem D_arrow12 (a : Fin (encoding.generators+1)) :
    (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).map (fixed.g a) ≫ (D2Iso (Y := Y)).hom =
      (D1Iso (Y := Y)).hom ≫ targetAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  DiagramEvaluationSquares.compose _ _ _ SelectedDiagramEvaluation.D1Iso
    SelectedDiagramEvaluation.D2Iso targetIso targetIso
    (SelectedDiagramEvaluation.D_arrow12 a) (target_square _)
end LittleFinitistic.SelectedNativeEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedChainHomology
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso
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

/-- This applies to any chain representative of the same fixed first arrow. -/
lemma arrow01 (a : Fin (encoding.generators+1))
    (f : SelectedChainDiagram.D0 ⟶ SelectedChainDiagram.D1)
    (hf : (HomotopyCategory.quotient _ _).map f = (fixed.f a).hom)
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (representation (Y := Y)) f) n ≫ (D1Iso n hn).hom =
      (D0Iso n hn).hom ≫ HAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  homology_arrow f (fixed.f a) hf SelectedNativeEvaluation.D0Iso SelectedNativeEvaluation.D1Iso _
    (SelectedNativeEvaluation.D_arrow01 a) n hn

lemma arrow12 (a : Fin (encoding.generators+1))
    (g : SelectedChainDiagram.D1 ⟶ SelectedChainDiagram.D2)
    (hg : (HomotopyCategory.quotient _ _).map g = (fixed.g a).hom)
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (representation (Y := Y)) g) n ≫ (D2Iso n hn).hom =
      (D1Iso n hn).hom ≫ HAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  homology_arrow g (fixed.g a) hg SelectedNativeEvaluation.D1Iso SelectedNativeEvaluation.D2Iso _
    (SelectedNativeEvaluation.D_arrow12 a) n hn

lemma fixed_arrow01 (a : Fin (encoding.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap
      (tensorMap (representation (Y := Y)) (SelectedChainDiagram.fixedChain.f a)) n ≫ (D1Iso n hn).hom =
      (D0Iso n hn).hom ≫ HAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  arrow01 a _ (SelectedChainDiagram.fixedChain.f_quotient a) n hn
lemma fixed_arrow12 (a : Fin (encoding.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap
      (tensorMap (representation (Y := Y)) (SelectedChainDiagram.fixedChain.g a)) n ≫ (D2Iso n hn).hom =
      (D1Iso n hn).hom ≫ HAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  arrow12 a _ (SelectedChainDiagram.fixedChain.g_quotient a) n hn
end LittleFinitistic.SelectedChainHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedRealization
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK
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
lemma coordinates01 (a : Fin (encoding.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) (input (Y := Y))).mapHomologicalComplex (.up ℤ)).map
      (SelectedRectification.f a)) n ≫ (coordinates (Y := Y) n hn 1).hom =
      (coordinates (Y := Y) n hn 0).hom ≫ EvaluationVertexDiagram.action (Y := H (Y := Y)) (selectedRepresentation (Y := Y)) a := by
  erw [selected_action (Y := Y)]
  exact SelectedChainHomology.fixed_arrow01 a n hn

lemma coordinates12 (a : Fin (encoding.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) (input (Y := Y))).mapHomologicalComplex (.up ℤ)).map
      (SelectedRectification.g a)) n ≫ (coordinates (Y := Y) n hn 2).hom =
      (coordinates (Y := Y) n hn 1).hom ≫ EvaluationVertexDiagram.action (Y := H (Y := Y)) (selectedRepresentation (Y := Y)) a := by
  erw [selected_action (Y := Y)]
  exact SelectedChainHomology.fixed_arrow12 a n hn

/-- The entire cohomology B-module is the manuscript's M(H(Y)), in both degrees. -/
def cohomology (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (SelectedTensor.complex (input (Y := Y))).homology n ≅ reference (Y := Y) :=
  SelectedReferenceCohomology.iso _ (selectedRepresentation (Y := Y)) n (coordinates (Y := Y) n hn)
    (fun a => coordinates01 a n hn) (fun a => coordinates12 a n hn)

/-- The one fixed selecting bimodule realizes H on every finite-dimensional Y.
This is an isomorphism in the full B-module derived category. -/
def realization :
    SelectedTensorSplitting.object (input (Y := Y)) ≅
      (DerivedCategory.singleFunctor (ModuleCat (B P)) 0).obj (reference (Y := Y)) ⊞
        ((DerivedCategory.singleFunctor (ModuleCat (B P)) 0).obj (reference (Y := Y)))⟦(3 : ℤ)⟧ :=
  SelectedTensorSplitting.split _ _ (cohomology 0 (Or.inl rfl))
    (cohomology (-3) (Or.inr rfl)) source_zero
end LittleFinitistic.SelectedRealization

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_FiniteSelectionFamily
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instAddCommGroupInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteDimensionalComplexInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleComplexInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.FiniteSelectionFamily
open SelectedFixedDiagram QuadraticEncoding

/-- The proved one-step realization uses the actual endomap of the finite family. -/
def realization (Y : S) :
    SelectedTensorSplitting.object (representation Y).Evaluation ≅
      derived (H Y) ⊞ (derived (H Y))⟦(3 : ℤ)⟧ :=
  SelectedRealization.realization (Y := vector Y)

end LittleFinitistic.FiniteSelectionFamily

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedShiftedRealization
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instAddCommGroupInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteDimensionalComplexInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleComplexInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.SelectedShiftedRealization
open SelectedFixedDiagram QuadraticEncoding SelectedOrdinaryAlgebra
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- The concrete two summands for one application of the actual shifted tensor. -/
def realizationNested (Y : FiniteSelectionFamily.S.{0}) :
    G.obj (FiniteSelectionFamily.derived Y) ≅
      (FiniteSelectionFamily.derived (FiniteSelectionFamily.H Y))⟦b⟧ ⊞
        ((FiniteSelectionFamily.derived (FiniteSelectionFamily.H Y))⟦(3 : ℤ)⟧)⟦b⟧ :=
  comparison Y ≪≫ (shiftFunctor _ b).mapIso (FiniteSelectionFamily.realization Y) ≪≫
    (shiftFunctor _ b).mapBiprod _ _

/-- The source convention places the two summands in shifts b and b+3. -/
def realization (Y : FiniteSelectionFamily.S.{0}) :
    G.obj (FiniteSelectionFamily.derived Y) ≅
      (FiniteSelectionFamily.derived (FiniteSelectionFamily.H Y))⟦b⟧ ⊞
        (FiniteSelectionFamily.derived (FiniteSelectionFamily.H Y))⟦b+3⟧ :=
  realizationNested Y ≪≫ biprod.mapIso (Iso.refl _)
    ((shiftAdd _ (3 : ℤ) b).symm ≪≫ eqToIso (by rw [add_comm (3 : ℤ) b]))

end LittleFinitistic.SelectedShiftedRealization

end

end OAI
end


