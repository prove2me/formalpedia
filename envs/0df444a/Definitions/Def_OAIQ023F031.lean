-- Prove2me | Definitions.Def_OAIQ023F031
-- name    : OAIQ023F031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T19:31:57.737633+00:00
-- url     : https://prove2.me/theorems/9ca33274-7db4-4ef6-8f86-2f28038322ef
-- title:
--   Definitions bundle OAIQ023F031 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 82 declarations of OpenAI's Lean: 44 definitions, 1 inductive type or structure, 9 instances and 28 theorems. The definitions and types are `OAI.LittleFinitistic.EncodingModuleAssembly.equiv`, `OAI.LittleFinitistic.FiniteSelectionFamily.derived`, `OAI.LittleFinitistic.FiniteSelectionFamily.module`, `OAI.LittleFinitistic.FiniteSelectionFamily.representation`, `OAI.LittleFinitistic.QuadraticEncoding.arrowK01`, `OAI.LittleFinitistic.QuadraticEncoding.arrowK12`, `OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluation`, `OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluation`, `OAI.LittleFinitistic.QuadraticEncoding.homotopyVertexIso`, `OAI.LittleFinitistic.QuadraticEncoding.liftedVertexEquiv`, `OAI.LittleFinitistic.QuadraticEncoding.pathModuleMap`, `OAI.LittleFinitistic.QuadraticEncoding.vertexK`, `OAI.LittleFinitistic.RelationVertexSequence.sequenceIso`, `OAI.LittleFinitistic.SelectedChainHomology.comparison`, `OAI.LittleFinitistic.SelectedChainHomology.complex`, `OAI.LittleFinitistic.SelectedChainHomology.derivedIso`, `OAI.LittleFinitistic.SelectedChainHomology.homologyIso`, `OAI.LittleFinitistic.SelectedChainHomology.representation`, `OAI.LittleFinitistic.SelectedChainHomology.source`, `OAI.LittleFinitistic.SelectedDiagramEvaluation.sourceEvaluation`, `OAI.LittleFinitistic.SelectedFixedDiagram.Data`, `OAI.LittleFinitistic.SelectedFixedDiagram.U`, `OAI.LittleFinitistic.SelectedFixedDiagram.fixed`, `OAI.LittleFinitistic.SelectedFixedDiagram.oddDouble`, `OAI.LittleFinitistic.SelectedFixedDiagram.selectedAction`, `OAI.LittleFinitistic.SelectedFixedDiagram.theta`, `OAI.LittleFinitistic.SelectedRectification.D0`, `OAI.LittleFinitistic.SelectedTensorComparison.finiteIso`, `OAI.LittleFinitistic.SourceActionEvaluation.representation`, `OAI.LittleFinitistic.SourceEvaluation.evaluation`, `OAI.LittleFinitistic.SourceEvaluation.finite`, `OAI.LittleFinitistic.SourceEvaluation.vertexIso`, `OAI.LittleFinitistic.SourceModelBridge.ambient`, `OAI.LittleFinitistic.SourceModelBridge.forgetProj`, `OAI.LittleFinitistic.SourceModelBridge.rightStalk`, `OAI.LittleFinitistic.SourceModelBridge.stalkUnderlyingIso`, `OAI.LittleFinitistic.SourceModelBridge.toBounded`, `OAI.LittleFinitistic.SourceModelBridge.vertexIso`, `OAI.LittleFinitistic.SourceQuotientAction.a01`, `OAI.LittleFinitistic.SourceQuotientAction.a12` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Encoding_EncodingModuleAssembly`, `Finitistic_Encoding_RelationVertexCoordinates`, `Finitistic_Encoding_RelationVertexSequence`, `Finitistic_Localization_BoundedQuotientEvaluation`, `Finitistic_Localization_BoundedQuotientGenerators`, `Finitistic_Localization_EvaluationVertexDiagram`, `Finitistic_Localization_FiniteEvaluationTarget`, `Finitistic_Localization_HomotopyVertexEvaluation`, `Finitistic_Localization_QuotientRelations`, `Finitistic_Localization_SourceActionEvaluation`, `Finitistic_Localization_SourceEvaluation`, `Finitistic_Localization_SourceModelBridge`, `Finitistic_Localization_SourceQuotientAction`, `Finitistic_Rectification_FinalGradedAcyclic`, `Finitistic_Selected_SelectedChainHomology`, `Finitistic_Selected_SelectedDiagramEvaluation`, `Finitistic_Selected_SelectedFixedDiagram`, `Finitistic_Selected_SelectedRectification`, `Finitistic_Selected_SelectedTensorComparison`, `Finitistic_Selection_FiniteSelectionFamily`.
--
--   **Imports.** It imports the bundles `OAIQ023F028`, `OAIQ023F029` and `OAIQ023F030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F033` and `OAIQ023F034`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F028
import Definitions.Def_OAIQ023F029
import Definitions.Def_OAIQ023F030

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationVertexCoordinates
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.RelationVertexCoordinates
open QuadraticEncoding RelationBasisCoefficients ExternalTensor.Section4
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D : RightComplex (QuadraticEncoding.B P))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P

/-- The source-zero p entry becomes the actual length-two path quotient. -/
theorem p_square (a : Fin (d+1)) :
    (oneIso P D).hom ≫ (tensor P D).map (quotientEntry P a) =
      (vertex P).map (path k T (s).e₀ (s).e₁ (arrow01 P a) ((s).ha a) D) ≫
        (zeroIso P D).hom := by
  apply CornerPathTransport.path_square
  intro x
  change (CornerSpaces.corner20Equiv (composition P))
    (CornerColumnPaths.cornerMap (composition P) 2 0 1 (arrow01 P a) ((s).ha a) x) =
    (quotientEntry P a).hom ((CornerSpaces.corner21Equiv (composition P)) x)
  rw [show (quotientEntry P a).hom ((CornerSpaces.corner21Equiv (composition P)) x) =
    (relationSpace P).mkQ (((CornerSpaces.corner21Equiv (composition P)) x) ⊗ₜ[k] basis a)
      from RelationMatrixSequence.quotient_injection P a _]
  simpa only [LinearEquiv.symm_apply_apply] using
    CornerArrowCoordinates.lengthTwo_coordinate P a ((CornerSpaces.corner21Equiv (composition P)) x)

/-- The source-zero q entry uses the original coefficients and actual b-arrow maps. -/
theorem q_square (r : RelationIndex P) (a : Fin (d+1)) :
    (twoIso P D).hom ≫ (tensor P D).map (relationEntry P r a) =
      (vertex P).map (∑ b, basisCoefficient P r a b •
        path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D) ≫ (oneIso P D).hom := by
  have hb (b : Fin (d+1)) :
      (twoIso P D).hom ≫ (tensor P D).map (TensorArrowSum.insertion k d b) =
      (vertex P).map (path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D) ≫
        (oneIso P D).hom := by
    refine CornerPathTransport.path_square (composition P) D 2 1 2
      (CornerSpaces.diagonalEquiv (composition P) 2) (CornerSpaces.corner21Equiv (composition P))
      (arrow12 P b) ((s).hb b) (TensorArrowSum.insertion k d b).hom ?_
    intro x
    change (CornerSpaces.corner21Equiv (composition P))
      (CornerColumnPaths.cornerMap (composition P) 2 1 2 (arrow12 P b) ((s).hb b) x) =
        (TensorArrowSum.insertion k d b).hom ((CornerSpaces.diagonalEquiv (composition P) 2) x)
    rw [TensorArrowSum.insertion_apply]
    simpa only [LinearEquiv.symm_apply_apply] using
      CornerArrowCoordinates.arrow12_coordinate P b ((CornerSpaces.diagonalEquiv (composition P) 2) x)
  rw [relationEntry_eq]
  simp only [Functor.map_sum,Functor.map_smul,Preadditive.comp_sum,Linear.comp_smul]
  refine (Finset.sum_congr rfl
    (fun b _ => congrArg (basisCoefficient P r a b • ·) (hb b))).trans ?_
  refine (Finset.sum_congr rfl (fun b _ =>
    (Linear.smul_comp _ _ _ (basisCoefficient P r a b)
      ((vertex P).map (path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D))
      (oneIso P D).hom).symm)).trans ?_
  exact (Preadditive.sum_comp Finset.univ
      (fun b => basisCoefficient P r a b •
        (vertex P).map (path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D))
      (oneIso P D).hom).symm
end LittleFinitistic.RelationVertexCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationVertexSequence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.shiftIso_apply _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTerm_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTotal_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_add _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_zero _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.ofModule_generator _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_composition _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathMap_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.projection_inclusion _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s'_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex0_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex1_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex2_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.QuadraticEncoding.actionArrow_zero _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.RelationVertexSequence
open QuadraticEncoding RelationBasisCoefficients ExternalTensor.Section4
open ExternalTensor.Section4.SourceFiltration RelationVertexCoordinates
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
local notation "data" => Exactness.data s D₀ D₁ D₂ f g

attribute [local instance] OAI.LittleFinitistic.RelationVertexSequence.instHasFiniteBiproductsRightComplexB
attribute [local instance] OAI.LittleFinitistic.RelationVertexSequence.instHasFiniteBiproductsBiComplexB
theorem p_square : (oneSumIso P D₀).hom ≫ (tensor P D₀).map (RelationMatrixSequence.quotient P) =
    (vertex P).map (p0 data) ≫ (zeroIso P D₀).hom := by
  have hg : biproduct.desc (quotientEntry P) = RelationMatrixSequence.quotient P := by
    apply biproduct.hom_ext'
    intro a
    simp [quotientEntry]
  rw [← hg]
  exact FiniteSumTransport.desc_square (vertex P) (tensor P D₀)
    (arrowFamily P D₀) (PathBasisIso.family k d) (fun _ => oneIso P D₀)
    (zeroIso P D₀) (data).pa₀ (quotientEntry P) (RelationVertexCoordinates.p_square P D₀)

theorem q_square : (twoSumIso P D₀).hom ≫ (tensor P D₀).map (RelationMatrixSequence.inclusion P) =
    (vertex P).map (q0 data) ≫ (oneSumIso P D₀).hom := by
  apply FiniteSumTransport.matrix_square
  intro r a
  have he := q_entry P D₀ D₁ D₂ f g r a
  change (twoIso P D₀).hom ≫ (tensor P D₀).map (relationEntry P r a) =
    (vertex P).map (biproduct.ι (relationFamily P D₀) r ≫ q0 data ≫
      biproduct.π (arrowFamily P D₀) a) ≫ (oneIso P D₀).hom
  rw [he]
  exact RelationVertexCoordinates.q_square P D₀ r a

def sequenceIso : (originalSequence P D₀ D₁ D₂ f g).map (vertex P) ≅
    (RelationMatrixSequence.sequence P).map (tensor P D₀) :=
  ShortComplex.isoMk (twoSumIso P D₀) (oneSumIso P D₀) (zeroIso P D₀)
    (q_square P D₀ D₁ D₂ f g) (p_square P D₀ D₁ D₂ f g)

/-- The original source-zero p/q maps are a short exact relation sequence at the final vertex. -/
theorem shortExact : ((originalSequence P D₀ D₁ D₂ f g).map (vertex P)).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso (sequenceIso P D₀ D₁ D₂ f g)).2
    (((RelationMatrixSequence.splitting P).map (tensor P D₀)).shortExact)
end LittleFinitistic.RelationVertexSequence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FinalGradedAcyclic
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.shiftIso_apply _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTerm_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTotal_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_add _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_zero _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.ofModule_generator _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_composition _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathMap_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.projection_inclusion _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s'_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex0_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex1_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex2_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.QuadraticEncoding.actionArrow_zero _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace LittleFinitistic.FinalGradedAcyclic
open QuadraticEncoding ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
open RectificationTotal
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
local notation "data" => Exactness.data s D₀ D₁ D₂ f g

/-- The original source-zero quotient at vertex two is acyclic, with every relation column retained. -/
theorem grade0_vertex2_acyclic :
    ((RelationVertexCoordinates.vertex P).obj (Exactness.G0 s D₀ D₁ D₂ f g)).Acyclic := by
  let F := BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex (composition P) 2)
  let S := (RelationVertexSequence.originalSequence P D₀ D₁ D₂ f g).map
    (RelationVertexCoordinates.vertex P)
  have he : mapNullHomotopy F (p0 data) (q0 data) (h0 data) = Homotopy.ofEq S.zero := by
    ext i j
    simp [mapNullHomotopy_hom,h0,Homotopy.ofEq]
    rfl
  apply GradedVertexAcyclic.acyclic_of_iso
    (totalInterchange F (p0 data) (q0 data) (h0 data))
  rw [he]
  exact RectificationAcyclic.short_exact_total_acyclic S
    (RelationVertexSequence.shortExact P D₀ D₁ D₂ f g)
end LittleFinitistic.FinalGradedAcyclic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_EncodingModuleAssembly
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.EncodingModuleAssembly
open QuadraticEncoding VertexDecomposition VertexModuleAssembly
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module (B P) M] [Module (B P) N]
  [IsScalarTower k (B P) M] [IsScalarTower k (B P) N]

/-- Reconstruct a full module isomorphism from the three actual vertex-space
isomorphisms and the two finite arrow families. Its underlying vector-space map
is precisely the direct-sum assembly of the supplied vertex isomorphisms. -/
def equiv (E : ∀ i, Space (system P) M i ≃ₗ[k] Space (system P) N i)
    (h01 : ∀ a x, E 1 (arrow (system P) (i := 0) (j := 1) (arrow01 P a)
      (CanonicalArrowCompatibility.arrow01_target P a) x) =
      arrow (system P) (i := 0) (j := 1) (arrow01 P a)
        (CanonicalArrowCompatibility.arrow01_target P a) (E 0 x))
    (h12 : ∀ b x, E 2 (arrow (system P) (i := 1) (j := 2) (arrow12 P b)
      (CanonicalArrowCompatibility.arrow12_target P b) x) =
      arrow (system P) (i := 1) (j := 2) (arrow12 P b)
        (CanonicalArrowCompatibility.arrow12_target P b) (E 1 x)) : M ≃ₗ[B P] N :=
  EncodingLinearity.linearEquiv P (assembled (system P) E)
    (vertex_smul (system P) E)
    (fun a => arrow_smul (system P) E (arrow01 P a)
      (CanonicalArrowCompatibility.arrow01_target P a)
      ((ConcreteQuadraticDiagram.quadratic P).ha a) (h01 a))
    (fun b => arrow_smul (system P) E (arrow12 P b)
      (CanonicalArrowCompatibility.arrow12_target P b)
      ((ConcreteQuadraticDiagram.quadratic P).hb b) (h12 b))
end LittleFinitistic.EncodingModuleAssembly

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_BoundedQuotientEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.homotopyEvaluationLinear _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingTriangulated _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageShift _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic
open BalancedTensor FiniteProjectiveHomotopy IdempotentTensor
universe u v

namespace QuadraticEncoding
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

variable {P} {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

def boundedEvaluation : BoundedK P ⥤ HomotopyCategory (ModuleCat.{max u v} k) (.up ℤ) :=
  inclusion (B P)ᵐᵒᵖ ⋙ homotopyEvaluation k (B P) X.Evaluation

instance boundedEvaluationShift : (boundedEvaluation X).CommShift ℤ :=
  inferInstanceAs ((inclusion (B P)ᵐᵒᵖ ⋙ homotopyEvaluation k (B P) X.Evaluation).CommShift ℤ)

/-- Evaluation of every bounded-projective representative has bounded finite-dimensional terms. -/
theorem boundedEvaluation_finite [FiniteDimensional k Y] (T : BoundedK P) :
    (∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (((boundedEvaluation X).obj T).as.X i)) ∧
    ∀ i, FiniteDimensional k (((boundedEvaluation X).obj T).as.X i) := by
  obtain ⟨⟨a,b,hb⟩,hp⟩ := T.property
  constructor
  · exact ⟨a,b,bounded_support X.Evaluation T.obj.as a b hb⟩
  · intro i
    have := (hp i).1
    have : FiniteDimensional k (B P) := finiteDimensional P
    exact tensorFunctor_finite X.Evaluation (T.obj.as.X i)
end QuadraticEncoding
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_BoundedQuotientGenerators
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingTriangulated _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageShift _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The actual degree-zero right vertex projective in K. -/
def vertexK (i : Fin 3) : BoundedK P :=
  ⟨(HomotopyCategory.quotient _ _).obj ((degreeZero P).obj (vertexModule P i)),
    single_property (vertexModule P i) 0⟩

def arrowK01 (h : Fin (d+1)) : vertexK P 0 ⟶ vertexK P 1 :=
  (inclusion (B P)ᵐᵒᵖ).preimage
    ((HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule01 P h)))
def arrowK12 (h : Fin (d+1)) : vertexK P 1 ⟶ vertexK P 2 :=
  (inclusion (B P)ᵐᵒᵖ).preimage
    ((HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule12 P h)))

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationVertexDiagram
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.EvaluationVertexDiagram
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

/-- The first arrow family acts by the given representation, including the identity arrow. -/
theorem arrow01_square (a : Fin (d+1))
    (ha : ThreeVertexAlgebra.vertex (composition P) 1 * arrow01 P a = arrow01 P a) :
    (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
      (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a) ha).app (module X) ≫
      (vertexIso X 1).hom = (vertexIso X 0).hom ≫ action X a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change X.projection 1 (arrow01 P a • z.val) =
    (Fin.cases (motive := fun _ => Module.End k Y) (1 : Module.End k Y) X.generator a) (X.projection 0 z.val)
  exact congrArg (X.projection 1) (X.arrow01_smul a (show X.Evaluation from z.val))

/-- The second arrow family has the same specified representation action. -/
theorem arrow12_square (b : Fin (d+1))
    (hb : ThreeVertexAlgebra.vertex (composition P) 2 * arrow12 P b = arrow12 P b) :
    (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
      (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b) hb).app (module X) ≫
      (vertexIso X 2).hom = (vertexIso X 1).hom ≫ action X b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change X.projection 2 (arrow12 P b • z.val) =
    (Fin.cases (motive := fun _ => Module.End k Y) (1 : Module.End k Y) X.generator b) (X.projection 1 z.val)
  exact congrArg (X.projection 2) (X.arrow12_smul b (show X.Evaluation from z.val))
end LittleFinitistic.EvaluationVertexDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteEvaluationTarget
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.barBicomplex_projective _root_.OAI.DerivedBar.barTotal_projective _root_.OAI.DerivedBar.complex_projective _root_.OAI.DerivedBar.countComplex_projective _root_.OAI.DerivedBar.countSum_projective _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingTriangulated _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDMinimal.term_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageShift _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.ofModule_generator _root_.OAI.LittleFinitistic.QuadraticEncoding.actionArrow_zero _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y)

theorem finiteEvaluation_property (T : BoundedK P) :
    objects k ((boundedEvaluation X).obj T) := by
  obtain ⟨hb,hf⟩ := boundedEvaluation_finite X T
  refine ⟨hb,fun i => ⟨hf i,?_⟩⟩
  exact ModuleCat.projective_of_categoryTheory_projective _

/-- Evaluation with bounded finite-dimensional vector-space complexes as its actual target. -/
def finiteEvaluation : BoundedK P ⥤ FiniteVectorHomotopy.{u,v} (k := k) :=
  (objects k).lift (boundedEvaluation X) (finiteEvaluation_property X)

instance finiteEvaluationShift : (finiteEvaluation X).CommShift ℤ := by
  dsimp [finiteEvaluation]
  infer_instance
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_QuotientRelations
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.commute _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.towerLeft _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.actionArrow_zero _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
open Representation IdempotentTensor FiniteProjectiveHomotopy
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

lemma pathMap_target (z : Paths k d) : vertexId (P := P) 2 * pathMap P z = pathMap P z := by
  change ThreeVertexAlgebra.mul (composition P) (0,0,1,0,0,0)
    (0,0,0,0,0,(relationSpace P).mkQ z) = _
  simp [ThreeVertexAlgebra.mul, pathMap, lengthTwo]

/-- Left multiplication by a length-two path, as a linear family of module maps. -/
def pathModuleMap : Paths k d →ₗ[k] (vertexModule P 0 ⟶ vertexModule P 2) where
  toFun z := ModuleCat.ofHom (leftMultiply (pathMap P z) (pathMap_target P z))
  map_add' z w := by
    ext m : 2
    apply Subtype.ext
    change pathMap P (z+w) * m.val = pathMap P z * m.val + pathMap P w * m.val
    rw [map_add, add_mul]
  map_smul' c z := by
    ext m : 2
    apply Subtype.ext
    change pathMap P (c • z) * m.val = (pathMap P z * m.val) * algebraMap k (B P) c
    rw [map_smul, smul_mul_assoc, Algebra.smul_def, Algebra.commutes]

lemma pathModuleMap_basis (h l : Fin (d+1)) :
    pathModuleMap P (basis h ⊗ₜ[k] basis l) = arrowModule01 P l ≫ arrowModule12 P h := by
  ext m : 2
  apply Subtype.ext
  change pathMap P (basis h ⊗ₜ[k] basis l) * m.val = arrow12 P h * (arrow01 P l * m.val)
  rw [← arrow_product, mul_assoc]

lemma pathModuleMap_kills (z : Paths k d) (hz : z ∈ relationSpace P) : pathModuleMap P z = 0 := by
  ext m : 2
  apply Subtype.ext
  change pathMap P z * m.val = 0
  rw [(pathMap_eq_zero_iff P z).mpr hz,zero_mul]

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_HomotopyVertexEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.homotopyEvaluationLinear _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorLinear _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingTriangulated _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageShift _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.actionArrow_zero _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
open BalancedTensor FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

def liftedVertexEquiv (i : Fin 3) :
    (tensorFunctor k (B P) X.Evaluation).obj (vertexModule P i) ≃ₗ[k] ULift.{u} Y :=
  (evaluationVertexEquiv X i).trans ULift.moduleEquiv.symm

lemma tensor_arrow01_square (h : Fin (d+1)) :
    (tensorFunctor k (B P) X.Evaluation).map (arrowModule01 P h) ≫
      (liftedVertexEquiv X 1).toModuleIso.hom =
    (liftedVertexEquiv X 0).toModuleIso.hom ≫ actionArrow X h := by
  ext z
  have h := evaluation_arrow01 X h (evaluationVertexEquiv X 0 z)
  simpa [liftedVertexEquiv, actionArrow] using h

lemma tensor_arrow12_square (h : Fin (d+1)) :
    (tensorFunctor k (B P) X.Evaluation).map (arrowModule12 P h) ≫
      (liftedVertexEquiv X 2).toModuleIso.hom =
    (liftedVertexEquiv X 1).toModuleIso.hom ≫ actionArrow X h := by
  ext z
  have h := evaluation_arrow12 X h (evaluationVertexEquiv X 1 z)
  simpa [liftedVertexEquiv, actionArrow] using h

/-- Evaluation of each concrete degree-zero vertex object is the stalk complex Y. -/
def homotopyVertexIso (i : Fin 3) :
    (boundedEvaluation X).obj (vertexK P i) ≅ (vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y)) :=
  (HomotopyCategory.quotient _ _).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex
      (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).app (vertexModule P i)) ≪≫
  (vectorStalk (k := k)).mapIso (liftedVertexEquiv X i).toModuleIso

lemma homotopy_arrow01_square (h : Fin (d+1)) :
    (boundedEvaluation X).map (arrowK01 P h) ≫ (homotopyVertexIso X 1).hom =
    (homotopyVertexIso X 0).hom ≫ (vectorStalk (k := k)).map (actionArrow X h) := by
  change (homotopyEvaluation k (B P) X.Evaluation).map
    ((inclusion (B P)ᵐᵒᵖ).map (arrowK01 P h)) ≫ _ = _
  unfold arrowK01
  erw [Functor.map_preimage]
  change ((tensorFunctor k (B P) X.Evaluation).mapHomotopyCategory (.up ℤ)).map
    ((HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule01 P h))) ≫
    ((HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 1)) ≫
      (HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (liftedVertexEquiv X 1).toModuleIso.hom)) =
    ((HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 0)) ≫
      (HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (liftedVertexEquiv X 0).toModuleIso.hom)) ≫
    (HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (actionArrow X h))
  simp only [Functor.mapHomotopyCategory_map]
  have hn := (HomologicalComplex.singleMapHomologicalComplex
    (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.naturality (arrowModule01 P h)
  have hm := congrArg (fun f => (HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map f)
    (tensor_arrow01_square X h)
  simp only [Functor.map_comp] at hm
  have hc := (congrArg (fun f => f ≫
    (HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map
      (liftedVertexEquiv X 1).toModuleIso.hom) hn).trans (by
        simpa only [Category.assoc, Functor.comp_map, degreeZero] using congrArg (fun f =>
          (HomologicalComplex.singleMapHomologicalComplex
            (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 0) ≫ f) hm)
  have hfin := congrArg (fun f => (HomotopyCategory.quotient (ModuleCat.{max u v} k) (.up ℤ)).map f) hc
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map, degreeZero] at hfin ⊢
  exact hfin

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceQuotientAction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.commute _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.towerLeft _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationExact _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationFacShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationLift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationShift
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.actionArrow_zero _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.SourceQuotientAction
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The two concrete presentations of the same right ideal e_i B. -/
def vertexIso (i : Fin 3) : (SourceVerdier.E P i).obj ≅ vertexModule P i :=
  (ConcreteTensorEvaluation.idealEquiv (SourceVerdier.vertex P i)
    (SourceVerdier.vertex_idem P i)).toModuleIso

def nativeHom (i j : Fin 3) :
    (vertexModule P i ⟶ vertexModule P j) →ₗ[k]
      (SourceVerdier.E P i ⟶ SourceVerdier.E P j) where
  toFun f := ObjectProperty.homMk ((vertexIso P i).hom ≫ f ≫ (vertexIso P j).inv)
  map_add' f g := by
    apply ObjectProperty.hom_ext
    change (vertexIso P i).hom ≫ (f+g) ≫ (vertexIso P j).inv =
      (vertexIso P i).hom ≫ f ≫ (vertexIso P j).inv +
      (vertexIso P i).hom ≫ g ≫ (vertexIso P j).inv
    simp [Preadditive.comp_add,Preadditive.add_comp]
  map_smul' a f := by
    apply ObjectProperty.hom_ext
    change (vertexIso P i).hom ≫ (a • f) ≫ (vertexIso P j).inv =
      a • ((vertexIso P i).hom ≫ f ≫ (vertexIso P j).inv)
    simp

lemma nativeHom_comp {i j l : Fin 3}
    (f : vertexModule P i ⟶ vertexModule P j) (g : vertexModule P j ⟶ vertexModule P l) :
    nativeHom P i l (f ≫ g) = nativeHom P i j f ≫ nativeHom P j l g := by
  apply ObjectProperty.hom_ext
  change _ = ((vertexIso P i).hom ≫ f ≫ (vertexIso P j).inv) ≫
    ((vertexIso P j).hom ≫ g ≫ (vertexIso P l).inv)
  simp [nativeHom]

lemma nativeHom_arrow01 (a : Fin (d+1)) :
    nativeHom P 0 1 (arrowModule01 P a) = SourceVerdier.arrow01 P a := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  rfl
lemma nativeHom_arrow12 (a : Fin (d+1)) :
    nativeHom P 1 2 (arrowModule12 P a) = SourceVerdier.arrow12 P a := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  rfl

instance singleAdditive : (HomologicalComplex.single (SourceVerdier.Proj P) (.up ℤ) (0 : ℤ)).Additive :=
  inferInstanceAs ((CochainComplex.singleFunctor (SourceVerdier.Proj P) 0).Additive)
instance singleLinear : (HomologicalComplex.single (SourceVerdier.Proj P) (.up ℤ) (0 : ℤ)).Linear k :=
  inferInstanceAs ((CochainComplex.singleFunctor (SourceVerdier.Proj P) 0).Linear k)
instance stalkAdditive : (SourceVerdier.stalk P).Additive := by
  unfold SourceVerdier.stalk
  infer_instance
instance stalkLinear : (SourceVerdier.stalk P).Linear k where
  map_smul := by
    intro X Y f a
    apply ObjectProperty.hom_ext
    exact (HomologicalComplex.single (SourceVerdier.Proj P) (.up ℤ) (0 : ℤ) ⋙
      HomotopyCategory.quotient _ _).map_smul a f

abbrev vertex (i : Fin 3) : SourceVerdier.Q P :=
  (SourceVerdier.q P).obj ((SourceVerdier.stalk P).obj (SourceVerdier.E P i))
abbrev a01 (a : Fin (d+1)) : vertex P 0 ⟶ vertex P 1 :=
  (SourceVerdier.stalk P ⋙ SourceVerdier.q P).map (SourceVerdier.arrow01 P a)
abbrev a12 (a : Fin (d+1)) : vertex P 1 ⟶ vertex P 2 :=
  (SourceVerdier.stalk P ⋙ SourceVerdier.q P).map (SourceVerdier.arrow12 P a)
instance instIsIsoQA01OfNatFinHAddNat : IsIso (a01 P 0) := SourceVerdier.s_inverted P
instance instIsIsoQA12OfNatFinHAddNat : IsIso (a12 P 0) := SourceVerdier.s'_inverted P

def path : Paths k d →ₗ[k] (vertex P 0 ⟶ vertex P 2) :=
  ((SourceVerdier.stalk P ⋙ SourceVerdier.q P).mapLinearMap k).comp
    ((nativeHom P 0 2).comp (pathModuleMap P))

lemma path_basis (h l : Fin (d+1)) :
    path P (basis h ⊗ₜ[k] basis l) = a01 P l ≫ a12 P h := by
  change (SourceVerdier.stalk P ⋙ SourceVerdier.q P).map
    (nativeHom P 0 2 (pathModuleMap P (basis h ⊗ₜ[k] basis l))) = _
  rw [pathModuleMap_basis,nativeHom_comp,nativeHom_arrow01,nativeHom_arrow12,Functor.map_comp]

lemma path_kills (z : Paths k d) (hz : z ∈ relationSpace P) : path P z = 0 := by
  change (SourceVerdier.stalk P ⋙ SourceVerdier.q P).map
    (nativeHom P 0 2 (pathModuleMap P z)) = 0
  rw [pathModuleMap_kills P z hz,map_zero,Functor.map_zero]

lemma commutation (h : Fin d) : a01 P 0 ≫ a12 P h.succ = a01 P h.succ ≫ a12 P 0 := by
  have hz := path_kills P (QuadraticEncoding.commutation h)
    (Submodule.subset_span (Or.inl ⟨h,rfl⟩))
  simpa only [QuadraticEncoding.commutation,map_sub,path_basis,sub_eq_zero] using hz

lemma homogenized (j : Fin t) :
    (∑ h, ∑ l, P.quadratic j h l • (a01 P l.succ ≫ a12 P h.succ)) +
    (∑ h, P.linear j h • (a01 P h.succ ≫ a12 P 0)) +
    P.constant j • (a01 P 0 ≫ a12 P 0) = 0 := by
  have hz := path_kills P (QuadraticEncoding.homogenized P j)
    (Submodule.subset_span (Or.inr ⟨j,rfl⟩))
  simpa only [QuadraticEncoding.homogenized,map_add,map_sum,map_smul,path_basis] using hz

/-- The actual theta on E0 in the primary's source Verdier quotient. -/
def theta {R : Type*} [Ring R] [Algebra k R] (E : SelectionEncoding.Encoding k R) :
    R →ₐ[k] End (vertex E.relations 0) :=
  QuotientAction.presentedAction E.relations (a01 E.relations 0) (a12 E.relations 0)
    (fun h => a01 E.relations h.succ) (fun h => a12 E.relations h.succ)
    (commutation E.relations) (homogenized E.relations) E.equiv
end LittleFinitistic.SourceQuotientAction

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceModelBridge
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SourceModelBridge
open QuadraticEncoding FiniteProjectiveHomotopy
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

abbrev forgetProj := (ProjectiveComplexes.finiteProjective (B P)).ι
abbrev ambient : SourceVerdier.K P ⥤ HomotopyCategory (ModuleCat.{u} (B P)ᵐᵒᵖ) (.up ℤ) :=
  (BoundedHomotopy.bounded (SourceVerdier.Proj P)).ι ⋙ (forgetProj P).mapHomotopyCategory (.up ℤ)

lemma ambient_property (T : SourceVerdier.K P) : objects (B P)ᵐᵒᵖ ((ambient P).obj T) := by
  obtain ⟨a,b,ha,hb⟩ := (BoundedHomotopy.bounded_quotient_obj_iff _ _).mp T.property
  change ComplexProperty (B P)ᵐᵒᵖ (((forgetProj P).mapHomologicalComplex (.up ℤ)).obj T.obj.as)
  constructor
  · refine ⟨a,b,fun i hi => ?_⟩
    apply (forgetProj P).map_isZero
    rcases hi with hi | hi
    · exact CochainComplex.isZero_of_isStrictlyGE T.obj.as a i hi
    · exact CochainComplex.isZero_of_isStrictlyLE T.obj.as b i hi
  · intro i
    change Module.Finite (B P)ᵐᵒᵖ (T.obj.as.X i).obj ∧ Projective (T.obj.as.X i).obj
    have := (T.obj.as.X i).property.2
    exact ⟨(T.obj.as.X i).property.1,ModuleCat.projective_of_categoryTheory_projective _⟩

/-- Forgetting the projective subcategory gives actual bounded projective module complexes. -/
def toBounded : SourceVerdier.K P ⥤ BoundedK P :=
  (objects (B P)ᵐᵒᵖ).lift (ambient P) (ambient_property P)
instance instCommShiftKBoundedKToBoundedInt : (toBounded P).CommShift ℤ := by unfold toBounded; infer_instance

abbrev rightStalk := HomotopyCategory.singleFunctor (ModuleCat.{u} (B P)ᵐᵒᵖ) 0

def stalkUnderlyingIso (M : SourceVerdier.Proj P) :
    (ambient P).obj ((SourceVerdier.stalk P).obj M) ≅ (rightStalk P).obj M.obj :=
  (HomotopyCategory.quotient _ _).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex (forgetProj P) (.up ℤ) (0 : ℤ)).app M)

lemma stalkUnderlying_square {M N : SourceVerdier.Proj P} (f : M ⟶ N) :
    (ambient P).map ((SourceVerdier.stalk P).map f) ≫ (stalkUnderlyingIso P N).hom =
      (stalkUnderlyingIso P M).hom ≫ (rightStalk P).map f.hom := by
  have h := (HomologicalComplex.singleMapHomologicalComplex
    (forgetProj P) (.up ℤ) (0 : ℤ)).hom.naturality f
  have h' := congrArg (fun g => (HomotopyCategory.quotient _ _).map g) h
  change ((forgetProj P).mapHomotopyCategory (.up ℤ)).map
    ((HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.single (SourceVerdier.Proj P) (.up ℤ) (0 : ℤ)).map f)) ≫ _ = _
  rw [Functor.mapHomotopyCategory_map]
  simp only [Functor.map_comp, Functor.comp_map] at h'
  exact h'


def vertexIso (i : Fin 3) :
    (toBounded P).obj ((SourceVerdier.stalk P).obj (SourceVerdier.E P i)) ≅ vertexK P i :=
  (inclusion (B P)ᵐᵒᵖ).preimageIso
    (stalkUnderlyingIso P (SourceVerdier.E P i) ≪≫
      (rightStalk P).mapIso (SourceQuotientAction.vertexIso P i))

end LittleFinitistic.SourceModelBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceEvaluation
open QuadraticEncoding FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

def evaluation : SourceVerdier.K P ⥤ HomotopyCategory (ModuleCat.{max u v} k) (.up ℤ) :=
  SourceModelBridge.toBounded P ⋙ boundedEvaluation X

def vertexIso (i : Fin 3) :
    (evaluation X).obj ((SourceVerdier.stalk P).obj (SourceVerdier.E P i)) ≅
      (vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y)) :=
  (boundedEvaluation X).mapIso (SourceModelBridge.vertexIso P i) ≪≫ homotopyVertexIso X i

lemma actionArrow_zero : actionArrow X 0 = 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext y
  rfl

variable [FiniteDimensional k Y]
def finite : SourceVerdier.K P ⥤ FiniteVectorHomotopy.{u,v} (k := k) :=
  SourceModelBridge.toBounded P ⋙ finiteEvaluation X
end LittleFinitistic.SourceEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceActionEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower
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

def representation : Representation E.relations Y :=
  LittleFinitistic.QuadraticEncoding.Representation.ofModule (generator E) (generator_relations E)

end LittleFinitistic.SourceActionEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedFixedDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationExact _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationFacShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationLift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.evaluationShift _root_.OAI.LittleFinitistic.testModule_module _root_.OAI.LittleFinitistic.testModule_scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace LittleFinitistic.SelectedFixedDiagram
open SelectionEncoding RelationBasisCoefficients RelationBasisAction FormalSummandAction

abbrev theta := SourceQuotientAction.theta encoding

local instance instHasFiniteBiproductsKaroubiQComplexP : HasFiniteBiproducts (Karoubi (SourceVerdier.Q P)) :=
  Karoubi.karoubi_hasFiniteBiproducts
local instance instHasBinaryBiproductsKaroubiQComplexP : HasBinaryBiproducts (Karoubi (SourceVerdier.Q P)) :=
  hasBinaryBiproducts_of_finite_biproducts _

abbrev U := summand theta e idem
abbrev oddDouble := U ⊞ OddDouble.formalShift U 3
abbrev selectedAction := oddDoubleAction theta e idem central alpha

/-- All choices, arrows, relation-basis equations and equivariant identifications
for the actual selecting algebra. No evaluation module is a parameter. -/
structure Data where
  V0 : SourceVerdier.Q P
  rho : SelectionRing →ₐ[ℂ] End V0
  iso : (toKaroubi (SourceVerdier.Q P)).obj V0 ≅ oddDouble
  D0 : SourceVerdier.K P
  D1 : SourceVerdier.K P
  D2 : SourceVerdier.K P
  phi0 : (SourceVerdier.q P).obj D0 ≅ V0
  phi1 : (SourceVerdier.q P).obj D1 ≅ V0
  phi2 : (SourceVerdier.q P).obj D2 ≅ V0
  f : Fin (encoding.generators+1) → (D0 ⟶ D1)
  g : Fin (encoding.generators+1) → (D1 ⟶ D2)
  equivariant : ∀ r : SelectionRing,
    (toKaroubi (SourceVerdier.Q P)).map (rho r) ≫ iso.hom = iso.hom ≫ selectedAction r
  arrow01 : ∀ a, (SourceVerdier.q P).map (f a) ≫ phi1.hom =
    phi0.hom ≫ rho (arrow (generator encoding) a)
  arrow12 : ∀ b, (SourceVerdier.q P).map (g b) ≫ phi2.hom =
    phi1.hom ≫ rho (arrow (generator encoding) b)
  relations : ∀ r : RelationIndex P,
    ∑ a, ∑ b, basisCoefficient P r a b • (f a ≫ g b) = 0

/-- Choose once, using the proved native finite-diagram theorem and actual theta. -/
def fixed : Data := Classical.choice (by
  obtain ⟨V,rho,i,D0,D1,D2,p0,p1,p2,f,g,he,hf,hg,hr⟩ :=
    ConcreteFixedDiagram.fixed_diagram encoding theta e idem central alpha
  exact ⟨⟨V,rho,i,D0,D1,D2,p0,p1,p2,f,g,he,hf,hg,hr⟩⟩)

end LittleFinitistic.SelectedFixedDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedDiagramEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.testModule_module _root_.OAI.LittleFinitistic.testModule_scalarTower
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

abbrev sourceEvaluation := SourceEvaluation.finite
  (SourceActionEvaluation.representation (Y := Y) encoding) ⋙ (FiniteProjectiveHomotopy.derivedEmbedding ℂ).toEssImage

end LittleFinitistic.SelectedDiagramEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTensorComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedTensorComparison
open QuadraticEncoding FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

variable [FiniteDimensional k Y]
def finiteIso (D : SourceVerdier.K P) :
    (HomotopyCategory.quotient _ _).obj (tensor X D) ≅
      (inclusion k).obj ((SourceEvaluation.finite X).obj D) := Iso.refl _

end LittleFinitistic.SelectedTensorComparison

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedChainHomology
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule
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
abbrev representation := SourceActionEvaluation.representation (Y := Y) encoding
abbrev complex (D : SourceVerdier.K P) := tensor (representation (Y := Y)) D
abbrev source := SelectedDiagramEvaluation.sourceEvaluation (Y := Y)

def derivedIso (D : SourceVerdier.K P) :
    DerivedCategory.Q.obj (complex (Y := Y) D) ≅ I.obj ((source (Y := Y)).obj D) :=
  (DerivedCategory.quotientCompQhIso C).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso (finiteIso (representation (Y := Y)) D)

def comparison (D : SourceVerdier.K P) (n : ℤ) :
    (complex (Y := Y) D).homology n ≅ (cohomology n).obj ((source (Y := Y)).obj D) :=
  (DerivedCategory.homologyFunctorFactors C n).symm.app _ ≪≫
    (DerivedCategory.homologyFunctor C n).mapIso (derivedIso (Y := Y) D)

/-- Actual homology of a selected chain tensor, with its chosen target identification. -/
def homologyIso (D : SourceVerdier.K P)
    (e : (source (Y := Y)).obj D ≅ target (Y := Y))
    (n : ℤ) (hn : n = 0 ∨ n = -3) : (complex (Y := Y) D).homology n ≅ H (Y := Y) :=
  comparison D n ≪≫ (cohomology n).mapIso e ≪≫ modelIso n hn

end LittleFinitistic.SelectedChainHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedRectification
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.SelectedRectification
open SelectedFixedDiagram ExternalTensor.Section4 RelationBasisCoefficients

abbrev D0 := UnderlyingRepresentatives.complex P fixed.D0
end LittleFinitistic.SelectedRectification

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_FiniteSelectionFamily
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower
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

abbrev representation (Y : S) := SourceActionEvaluation.representation (Y := vector Y) encoding
abbrev module (Y : S) := EvaluationVertexDiagram.module (representation Y)
abbrev derived (Y : S) := (DerivedCategory.singleFunctor (ModuleCat (B P)) 0).obj (module Y)

end LittleFinitistic.FiniteSelectionFamily

end

end OAI
end


