-- Prove2me | Definitions.Def_OAIQ023F030
-- name    : OAIQ023F030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T19:19:43.979978+00:00
-- url     : https://prove2.me/theorems/142a765a-a670-45f3-850e-2053cc07a9a6
-- title:
--   Definitions bundle OAIQ023F030 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 62 declarations of OpenAI's Lean: 33 definitions, 7 instances and 22 theorems. The definitions and types are `OAI.LittleFinitistic.EvaluationVertexDiagram.equiv`, `OAI.LittleFinitistic.EvaluationVertexDiagram.vertexIso`, `OAI.LittleFinitistic.FullTensorRectification.arrow01Map`, `OAI.LittleFinitistic.FullTensorRectification.arrow12Map`, `OAI.LittleFinitistic.FullTensorRectification.target`, `OAI.LittleFinitistic.FullTensorRectification.tensor`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.forgetAugmentationTargetIso`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.forgetBimoduleComplex`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.forgetBimoduleTerm`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.forgetBimoduleTerminal`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.forgetIntegerBimoduleComplex`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleAugmentation`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleComplex`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.retract`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.ordinaryXObject`, `OAI.LittleFinitistic.OrdinarySimulation.computedTensorIso`, `OAI.LittleFinitistic.OrdinarySimulation.genuineComputedTensor`, `OAI.LittleFinitistic.OrdinarySimulation.genuineComputedTensorIso`, `OAI.LittleFinitistic.OrdinarySimulation.genuineFiniteComplexIso`, `OAI.LittleFinitistic.OrdinarySimulation.genuineFiniteTermIso`, `OAI.LittleFinitistic.OrdinarySimulation.genuineSourceShiftComparison`, `OAI.LittleFinitistic.OrdinarySimulation.genuineTensorFunctor`, `OAI.LittleFinitistic.OrdinarySimulation.sourceBimoduleTotalComparison`, `OAI.LittleFinitistic.OrdinarySimulation.sourceShiftComparison`, `OAI.LittleFinitistic.QuadraticEncoding.arrowModule01`, `OAI.LittleFinitistic.QuadraticEncoding.arrowModule12`, `OAI.LittleFinitistic.QuadraticEncoding.evaluationVertexEquiv`, `OAI.LittleFinitistic.QuadraticEncoding.vertexModule`, `OAI.LittleFinitistic.RelationVertexSequence.arrowFamily`, `OAI.LittleFinitistic.RelationVertexSequence.oneSumIso`, `OAI.LittleFinitistic.RelationVertexSequence.relationFamily`, `OAI.LittleFinitistic.RelationVertexSequence.twoSumIso`, `OAI.LittleFinitistic.VertexHomotopyEquivalence.target`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Encoding_RelationVertexSequence`, `Finitistic_Localization_BoundedQuotientEvaluation`, `Finitistic_Localization_EvaluationModule`, `Finitistic_Localization_EvaluationVertexDiagram`, `Finitistic_Localization_UnderlyingRepresentatives`, `Finitistic_Ordinary_OrdinaryBimoduleAugmentation`, `Finitistic_Ordinary_OrdinaryBimoduleAugmentationQuasiIso`, `Finitistic_Ordinary_OrdinaryBimoduleResolutionProjective`, `Finitistic_Ordinary_OrdinaryGenuineBimoduleComparison`, `Finitistic_Ordinary_OrdinaryIntegerResolution`, `Finitistic_Ordinary_OrdinarySimulationComparison`, `Finitistic_Ordinary_OrdinarySourceBimoduleTotal`, `Finitistic_Ordinary_OrdinaryTensorBimoduleResolution`, `Finitistic_Ordinary_OrdinaryTensorResolution`, `Finitistic_Ordinary_OrdinaryTensorResolutionComplex`, `Finitistic_Ordinary_OrdinaryTensorTotalAcyclic`, `Finitistic_Ordinary_OrdinaryXAugmentation`, `Finitistic_Rectification_FirstVertex`, `Finitistic_Rectification_FullTensorRectification`, `Finitistic_Rectification_GradedVertexAcyclic`, `Finitistic_Rectification_SecondVertex`, `Finitistic_Rectification_VertexHomotopyEquivalence`, `Finitistic_Rectification_VertexTensorEvaluation`, `Finitistic_Rectification_VertexTotalProperties`, `Finitistic_Rectification_VertexZeroTotal`, `Finitistic_Selected_SelectedVertexTensorEvaluation`.
--
--   **Imports.** It imports the bundles `OAIQ023F025`, `OAIQ023F026` and `OAIQ023F027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F031` and `OAIQ023F032`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F025
import Definitions.Def_OAIQ023F026
import Definitions.Def_OAIQ023F027

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationVertexSequence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.shiftIso_apply _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTerm_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTotal_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_add _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_zero _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_composition _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathMap_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.projection_inclusion _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s'_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex0_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex1_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex2_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second
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
abbrev arrowFamily : Fin (d+1) → BiComplex k T := fun _ => (columnComplex k T (s).e₁).obj D₀
abbrev relationFamily : RelationIndex P → BiComplex k T := fun _ => (columnComplex k T (s).e₂).obj D₀

def oneSumIso := FiniteSumTransport.iso (vertex P) (tensor P D₀)
  (arrowFamily P D₀) (PathBasisIso.family k d) (fun _ => oneIso P D₀)
def twoSumIso := FiniteSumTransport.iso (vertex P) (tensor P D₀)
  (relationFamily P D₀) (FiniteBasisIso.family (k := k) : RelationIndex P → _) (fun _ => twoIso P D₀)

theorem q_entry (r : RelationIndex P) (a : Fin (d+1)) :
    biproduct.ι (relationFamily P D₀) r ≫ q0 data ≫ biproduct.π (arrowFamily P D₀) a =
      ∑ b, basisCoefficient P r a b •
        path k T (s).e₁ (s).e₂ (arrow12 P b) ((s).hb b) D₀ := by
  classical
  change biproduct.ι (data).W r ≫ q0 data ≫ biproduct.π (data).U a = _
  simp only [q0,biproduct.ι_desc_assoc,Preadditive.sum_comp,Category.assoc]
  simp only [biproduct.ι_π]
  rw [Finset.sum_eq_single a]
  · simp [Exactness.data,inducedData,ConcreteQuadraticDiagram.quadratic]
    rfl
  · intro b hb hba
    simp [hba]
  · simp

end LittleFinitistic.RelationVertexSequence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationModule
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ}
variable {Y : Type v} [AddCommGroup Y] [Module k Y]

namespace Representation
variable {P : Relations k d t} (X : Representation P Y)

instance instSMulCommClassBEvaluation : SMulCommClass k (B P) X.Evaluation where
  smul_comm c a y := by
    change c • X.act a y = X.act a (c • y)
    rw [evaluation_smul, evaluation_smul]
    apply Prod.ext
    · simp [act, smul_comm c a.1]
    apply Prod.ext <;> simp [act, smul_add, smul_smul, mul_comm]

end Representation
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexTensorEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticEncoding.Representation
open IdempotentTensor BalancedTensor
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y]
variable (X : Representation P Y)

lemma arrow01_target (h : Fin (d+1)) : vertexId (P := P) 1 * arrow01 P h = arrow01 P h := by
  change ThreeVertexAlgebra.mul (composition P) _ _ = _
  simp [vertexId,ThreeVertexAlgebra.vertex,ThreeVertexAlgebra.mul,arrow01]
lemma arrow01_source (h : Fin (d+1)) : arrow01 P h * vertexId (P := P) 0 = arrow01 P h := by
  change ThreeVertexAlgebra.mul (composition P) _ _ = _
  simp [vertexId,ThreeVertexAlgebra.vertex,ThreeVertexAlgebra.mul,arrow01]
lemma arrow12_target (h : Fin (d+1)) : vertexId (P := P) 2 * arrow12 P h = arrow12 P h := by
  change ThreeVertexAlgebra.mul (composition P) _ _ = _
  simp [vertexId,ThreeVertexAlgebra.vertex,ThreeVertexAlgebra.mul,arrow12]
lemma arrow12_source (h : Fin (d+1)) : arrow12 P h * vertexId (P := P) 1 = arrow12 P h := by
  change ThreeVertexAlgebra.mul (composition P) _ _ = _
  simp [vertexId,ThreeVertexAlgebra.vertex,ThreeVertexAlgebra.mul,arrow12]

end LittleFinitistic.QuadraticEncoding.Representation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedVertexTensorEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorLinear _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.commute _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.towerLeft _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
open IdempotentTensor BalancedTensor Representation
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The manuscript's actual right vertex projectives. -/
def vertexModule (i : Fin 3) : ModuleCat.{u} (B P)ᵐᵒᵖ :=
  ModuleCat.of (B P)ᵐᵒᵖ (rightIdeal (vertexId (P := P) i))

def arrowModule01 (h : Fin (d+1)) : vertexModule P 0 ⟶ vertexModule P 1 :=
  ModuleCat.ofHom (leftMultiply (arrow01 P h) (arrow01_target h))
def arrowModule12 (h : Fin (d+1)) : vertexModule P 1 ⟶ vertexModule P 2 :=
  ModuleCat.ofHom (leftMultiply (arrow12 P h) (arrow12_target h))

variable {P} {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

/-- The natural identifications for the actual tensor functor. -/
def evaluationVertexEquiv (i : Fin 3) :
    (tensorFunctor k (B P) X.Evaluation).obj (vertexModule P i) ≃ₗ[k] Y :=
  (tensorFunctorEquiv (rightIdeal (vertexId (P := P) i)) X.Evaluation).trans (X.vertexTensorEquiv i)

theorem evaluation_arrow01 (h : Fin (d+1)) (y : Y) :
    evaluationVertexEquiv X 1
      ((tensorFunctor k (B P) X.Evaluation).map (arrowModule01 P h)
        ((evaluationVertexEquiv X 0).symm y)) =
      (Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator h) y := by
  change X.projection 1 ((arrow01 P h * vertexId (P := P) 0) • X.inclusion 0 y) = _
  rw [arrow01_source]
  erw [X.arrow01_smul]
  rfl

theorem evaluation_arrow12 (h : Fin (d+1)) (y : Y) :
    evaluationVertexEquiv X 2
      ((tensorFunctor k (B P) X.Evaluation).map (arrowModule12 P h)
        ((evaluationVertexEquiv X 1).symm y)) =
      (Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator h) y := by
  change X.projection 2 ((arrow12 P h * vertexId (P := P) 1) • X.inclusion 1 y) = _
  rw [arrow12_source]
  erw [X.arrow12_smul]
  rfl

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_BoundedQuotientEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.commute _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.towerLeft _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

instance vertexModuleFinite (i : Fin 3) : Module.Finite (B P)ᵐᵒᵖ (vertexModule P i) := by
  let e := Representation.vertexId (P := P) i
  have he : e*e=e := (ThreeVertexAlgebra.directedSystem (composition P)).idem i
  apply Module.Finite.of_surjective (splitProjection he)
  intro m
  exact ⟨MulOpposite.op m.val,Subtype.ext m.property⟩

instance vertexModuleProjective (i : Fin 3) : Projective (vertexModule P i) := by
  have : Module.Projective (B P)ᵐᵒᵖ (vertexModule P i) :=
    rightIdeal_projective ((ThreeVertexAlgebra.directedSystem (composition P)).idem i)
  exact ModuleCat.projective_of_categoryTheory_projective (vertexModule P i)

end QuadraticEncoding
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationVertexDiagram
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The vertex of the actual evaluation module is exactly the original vector space. -/
def equiv (i : Fin 3) :
    (LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj (module X) ≃ₗ[k] Y where
  toFun z := X.projection i z.val
  invFun y := ⟨X.inclusion i y, by
    erw [VertexFunctor.mem_fixed, X.vertex_smul, X.projection_inclusion]⟩
  left_inv z := by
    apply Subtype.ext
    have hz := (VertexFunctor.mem_fixed _ _ _ _ z.val).1 z.property
    exact (X.vertex_smul i (show X.Evaluation from z.val)).symm.trans hz
  right_inv y := X.projection_inclusion i y
  map_add' x y := (X.projection i).map_add x.val y.val
  map_smul' c z := by
    change X.projection i (algebraMap k (B P) c • z.val) = c • X.projection i z.val
    calc
      X.projection i (algebraMap k (B P) c • (show X.Evaluation from z.val)) =
          X.projection i (c • (show X.Evaluation from z.val)) :=
        congrArg (X.projection i) (IsScalarTower.algebraMap_smul (B P) c (show X.Evaluation from z.val))
      _ = c • X.projection i z.val := (X.projection i).map_smul c (show X.Evaluation from z.val)

def vertexIso (i : Fin 3) := (equiv X i).toModuleIso

end LittleFinitistic.EvaluationVertexDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_UnderlyingRepresentatives
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.UnderlyingRepresentatives
open SourceVerdier ConcreteChainRepresentatives
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

theorem finite (X : K P) (n : ℤ) :
    Module.Finite (QuadraticEncoding.B P)ᵐᵒᵖ ((complex P X).X n) :=
  ((representative P X).X n).property.1

attribute [local instance] ExternalTensor.Section4.rightModuleK

end LittleFinitistic.UnderlyingRepresentatives

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorResolution
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)
namespace TensorResolution
open ChainAlgebra

def retract (n : ℕ) : B ⊗[k] ChainAlgebra k l →ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ] term k B l n :=
  (leftMultiply k B l (TensorIdeal.vertex (k := k) (B := B) (extendedVertex k l n))).codRestrict _ (fun x => by
    change _ * (_ * x) = _ * x
    rw [← mul_assoc, TensorIdeal.vertex_idempotent _ (extendedVertex_idempotent k l n)])

instance term_projective (n : ℕ) : Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (term k B l n) := by
  let : Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (B ⊗[k] ChainAlgebra k l) :=
    Module.Projective.of_equiv (regularEquiv k B l)
  apply Module.Projective.of_split (term k B l n).subtype (retract k B l n)
  ext x
  exact x.property

end TensorResolution
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorResolutionComplex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

instance projectiveTerm (n : ℕ) : Projective (termObject k B l n) := inferInstance

end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryIntegerResolution
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_vertex_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.action_tmul_mk _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.evaluation_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

theorem integerTerm_projective (n : ℤ) : Projective ((integerComplex k B l).X n) := by
  by_cases h : n < -(l:ℤ)
  · exact (integerTerm_lower k B l n h).projective
  let j := (n+(l:ℤ)).toNat
  have hj : (degreeEmbedding l).f j = n := by
    simp only [degreeEmbedding_apply]
    dsimp [j]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  exact Projective.of_iso ((complex k B l).extendXIso (degreeEmbedding l) hj).symm (projectiveTerm k B l j)
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorBimoduleResolution
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

/-- The genuine bimodule resolution in exactly the source interval [-l,0]. -/
def integerBimoduleComplex : CochainComplex (ModuleCat.{u} (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ)) ℤ :=
  (bimoduleComplex k B l).extend (degreeEmbedding l)

def forgetBimoduleTerm (n : ℕ) :
    (forgetBimodule k B l).obj (ModuleCat.of _ (bimoduleTerm k B l n)) ≅ termObject k B l n := by
  let e : (forgetBimodule k B l).obj (ModuleCat.of _ (bimoduleTerm k B l n)) ≃ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
      term k B l n :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        apply Subtype.ext
        change TensorIdeal.coefficient (1:B) * (x.val * r.unop) = x.val * r.unop
        rw [map_one,one_mul] }
  exact e.toModuleIso

/-- Forgetting the retained left action recovers the verified ordinary finite resolution. -/
def forgetBimoduleComplex :
    ((forgetBimodule k B l).mapHomologicalComplex (.up ℕ)).obj (bimoduleComplex k B l) ≅ complex k B l :=
  HomologicalComplex.Hom.isoOfComponents (forgetBimoduleTerm k B l) (by
    intro n m h
    change n+1=m at h
    subst m
    change (forgetBimoduleTerm k B l n).hom ≫ (complex k B l).d n (n+1) =
      (forgetBimodule k B l).map ((bimoduleComplex k B l).d n (n+1)) ≫ (forgetBimoduleTerm k B l (n+1)).hom
    have h₁ : (complex k B l).d n (n+1) = ModuleCat.ofHom (differential k B l n) :=
      CochainComplex.of_d (termObject k B l) (fun n => ModuleCat.ofHom (differential k B l n)) n
    have h₂ : (bimoduleComplex k B l).d n (n+1) = ModuleCat.ofHom (bimoduleDifferential k B l n) :=
      CochainComplex.of_d (fun n => ModuleCat.of (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) (bimoduleTerm k B l n))
        (fun n => ModuleCat.ofHom (bimoduleDifferential k B l n)) n
    rw [h₁,h₂]
    rfl)

/-- Every integer term and differential agrees after forgetting the left action. -/
def forgetIntegerBimoduleComplex :
    ((forgetBimodule k B l).mapHomologicalComplex (.up ℤ)).obj (integerBimoduleComplex k B l) ≅
      integerComplex k B l :=
  FunctorExtension.iso (forgetBimodule k B l) (bimoduleComplex k B l) (degreeEmbedding l) ≪≫
    ((degreeEmbedding l).extendFunctor _).mapIso (forgetBimoduleComplex k B l)
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleAugmentation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

def forgetBimoduleTerminal : (forgetBimodule k B l).obj (bimoduleTerminalObject k B l) ≅
    ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B) := by
  let e : (forgetBimodule k B l).obj (bimoduleTerminalObject k B l) ≃ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
      TerminalTensor B :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (1:B) * (TerminalTensor.value B x * terminalAugmentation k B l r.unop) =
          TerminalTensor.value B x * terminalAugmentation k B l r.unop
        exact one_mul _ }
  exact e.toModuleIso

def forgetAugmentationTargetIso :
    ((forgetBimodule k B l).mapHomologicalComplex (.up ℕ)).obj
      ((HomologicalComplex.single _ (.up ℕ) l).obj (bimoduleTerminalObject k B l)) ≅
    (HomologicalComplex.single _ (.up ℕ) l).obj
      (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) :=
  (HomologicalComplex.singleMapHomologicalComplex (forgetBimodule k B l) (.up ℕ) l).app
      (bimoduleTerminalObject k B l) ≪≫
    (HomologicalComplex.single _ (.up ℕ) l).mapIso (forgetBimoduleTerminal k B l)
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleAugmentationQuasiIso
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_vertex_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.action_tmul_mk _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.evaluation_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

/-- The genuine augmentation becomes exactly the already verified right-module augmentation. -/
theorem forget_bimoduleAugmentation :
    (forgetBimoduleComplex k B l).hom ≫ augmentationMap k B l =
      ((forgetBimodule k B l).mapHomologicalComplex (.up ℕ)).map (bimoduleAugmentationMap k B l) ≫
        (forgetAugmentationTargetIso k B l).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = l
  · subst n
    change (forgetBimoduleTerm k B l l).hom ≫ (augmentationMap k B l).f l =
      (forgetBimodule k B l).map ((bimoduleAugmentationMap k B l).f l) ≫
        (forgetAugmentationTargetIso k B l).hom.f l
    have h₁ : (augmentationMap k B l).f l = augmentationHom k B l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).inv := by
      unfold augmentationMap
      apply HomologicalComplex.mkHomToSingle_f
    have h₂ : (bimoduleAugmentationMap k B l).f l = bimoduleAugmentationHom k B l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l (bimoduleTerminalObject k B l)).inv := by
      unfold bimoduleAugmentationMap
      apply HomologicalComplex.mkHomToSingle_f
    rw [h₁,h₂]
    change (forgetBimoduleTerm k B l l).hom ≫ augmentationHom k B l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).inv =
      (forgetBimodule k B l).map (bimoduleAugmentationHom k B l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l (bimoduleTerminalObject k B l)).inv) ≫
      ((HomologicalComplex.singleMapHomologicalComplex (forgetBimodule k B l) (.up ℕ) l).hom.app
        (bimoduleTerminalObject k B l)).f l ≫
      ((HomologicalComplex.single _ (.up ℕ) l).map (forgetBimoduleTerminal k B l).hom).f l
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    rw [(forgetBimodule k B l).map_comp]
    have hc := ((forgetBimodule k B l).mapIso
      (HomologicalComplex.singleObjXSelf (.up ℕ) l (bimoduleTerminalObject k B l))).inv_hom_id_assoc
        ((forgetBimoduleTerminal k B l).hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℕ) l
            (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).inv)
    rw [Category.assoc]
    refine Eq.trans ?_ (congrArg (fun t => (forgetBimodule k B l).map (bimoduleAugmentationHom k B l) ≫ t) hc).symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) l
      (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) n hn).eq_of_tgt _ _

/-- Actual augmentation quasi-isomorphism with its outside left B-action retained. -/
theorem bimoduleAugmentationMap_quasiIso : QuasiIso (bimoduleAugmentationMap k B l) := by
  apply (RestrictionHomology.quasiIso_iff
    (Algebra.TensorProduct.includeRight (R := k) (A := B) (B := (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ)).toRingHom _).mp
  let g := ((forgetBimodule k B l).mapHomologicalComplex (.up ℕ)).map (bimoduleAugmentationMap k B l)
  let := augmentationMap_quasiIso k B l
  have h : QuasiIso (g ≫ (forgetAugmentationTargetIso k B l).hom) := by
    dsimp only [g]
    rw [← forget_bimoduleAugmentation]
    infer_instance
  exact (quasiIso_iff_comp_right g (forgetAugmentationTargetIso k B l).hom).mp h

/-- The source's augmentation in degrees [-l,0], as a genuine bimodule map. -/
def integerBimoduleAugmentation : integerBimoduleComplex k B l ⟶
    (HomologicalComplex.single _ (.up ℤ) 0).obj (bimoduleTerminalObject k B l) :=
  HomologicalComplex.extendMap (bimoduleAugmentationMap k B l) (degreeEmbedding l) ≫
    (HomologicalComplex.extendSingleIso (e := degreeEmbedding l)
      (X := bimoduleTerminalObject k B l) l 0 (by simp)).hom

theorem integerBimoduleAugmentation_quasiIso : QuasiIso (integerBimoduleAugmentation k B l) := by
  have := bimoduleAugmentationMap_quasiIso k B l
  exact inferInstanceAs (QuasiIso
    (HomologicalComplex.extendMap (bimoduleAugmentationMap k B l) (degreeEmbedding l) ≫
      (HomologicalComplex.extendSingleIso (e := degreeEmbedding l)
        (X := bimoduleTerminalObject k B l) l 0 (by simp)).hom))
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorTotalAcyclic
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic
namespace OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

instance integerTerm_moduleProjective (n : ℤ) :
    Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ
      (ComplexTensor.rightTerm k (B ⊗[k] ChainAlgebra k l) (integerComplex k B l) n) := by
  let := integerTerm_projective k B l n
  exact (inferInstance : Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ ((integerComplex k B l).X n))

end OrdinarySimulation.TensorResolution
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleResolutionProjective
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

/-- The actual genuine bimodule resolution is right-projective in every integer degree. -/
instance integerBimoduleRight_projective (n : ℤ) :
    Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ
      (ComplexTensor.rightTerm k (B ⊗[k] ChainAlgebra k l)
        (BimoduleComplexTensor.rightComplex k B (B ⊗[k] ChainAlgebra k l) (integerBimoduleComplex k B l)) n) := by
  let e := (HomologicalComplex.eval _ _ n).mapIso (forgetIntegerBimoduleComplex k B l)
  let : Projective ((((forgetBimodule k B l).mapHomologicalComplex (.up ℤ)).obj
      (integerBimoduleComplex k B l)).X n) := Projective.of_iso e.symm (integerTerm_projective k B l n)
  exact ModuleCat.projective_of_module_projective
    ((((forgetBimodule k B l).mapHomologicalComplex (.up ℤ)).obj (integerBimoduleComplex k B l)).X n)

theorem integerBimodule_lower (n : ℤ) (hn : n < -(l:ℤ)) : IsZero ((integerBimoduleComplex k B l).X n) := by
  apply (bimoduleComplex k B l).isZero_extend_X (degreeEmbedding l) n
  intro j hj
  simp only [degreeEmbedding_apply] at hj
  omega

theorem integerBimodule_upper (n : ℤ) (hn : 0 < n) : IsZero ((integerBimoduleComplex k B l).X n) := by
  have h := (integerTerm_upper k B l n hn).of_iso
    ((HomologicalComplex.eval _ _ n).mapIso (forgetIntegerBimoduleComplex k B l))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hs := ModuleCat.isZero_iff_subsingleton.mp h
  exact hs
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySimulationComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

/-- Full bimodule chain comparison, including all zero terms and the genuine integer shift sign. -/
def computedTensorIso
    (hLower : ∀ n : ℤ, n < a → IsZero (P.X n))
    (hUpper : ∀ n : ℕ, l < n → IsZero (P.X (a+(n:ℤ)))) :
    computedTensorComplex P a l ≅ P⟦a+(l:ℤ)⟧ := by
  letI := unsignedSupport P a l hLower
  exact ((TensorResolution.degreeEmbedding l).extendFunctor (ModuleCat.{u} (Enveloping k B))).mapIso
      (FullTensorTerm.complexIso P a l hUpper ≪≫ restrictedShiftIso P a l) ≪≫
    SupportedExtension.iso (unsignedShift P (a+(l:ℤ))) (TensorResolution.degreeEmbedding l) ≪≫
    shiftSignIso P (a+(l:ℤ))

/-- Exact source indexing: b=a+l, with only the manuscript's support hypothesis. -/
def sourceShiftComparison (b : ℤ) (hb : a+(l:ℤ)=b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) :
    computedTensorComplex P a l ≅ P⟦b⟧ := by
  subst b
  exact computedTensorIso P a l (fun n hn => hP n (Or.inl hn))
    (fun n hn => hP (a+(n:ℤ)) (Or.inr (by omega)))
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryGenuineBimoduleComparison
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

abbrev genuineTensorFunctor :=
  bimoduleTensorFunctor k B (B ⊗[k] ChainAlgebra k l) Bᵐᵒᵖ (BimoduleO P a l)

def genuineFiniteTermIso (n : ℕ) :
    (genuineTensorFunctor P a l).obj ((TensorResolution.bimoduleComplex k B l).X n) ≅
      (FullTensorTerm.complex P a l).X n := by
  let e : BimoduleCoefficients k B (B ⊗[k] ChainAlgebra k l)
      ((TensorResolution.bimoduleComplex k B l).X n) ≃ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
        TensorResolution.term k B l n := (TensorResolution.forgetBimoduleTerm k B l n).toLinearEquiv
  have he (b : B) (x : BimoduleCoefficients k B (B ⊗[k] ChainAlgebra k l)
      ((TensorResolution.bimoduleComplex k B l).X n)) : e (b • x) = b • e x := by
    apply Subtype.ext
    change TensorIdeal.coefficient b * (x.val * 1) = TensorIdeal.coefficient b * x.val
    rw [mul_one]
  exact (TwoSidedTensor.congrLeft (k := k) (S := B) (T := Bᵐᵒᵖ) (N := BimoduleO P a l) e he).toModuleIso

/-- The actual finite bimodule tensor agrees with the existing full computation, preserving both B-actions. -/
def genuineFiniteComplexIso :
    ((genuineTensorFunctor P a l).mapHomologicalComplex (.up ℕ)).obj
      (TensorResolution.bimoduleComplex k B l) ≅ FullTensorTerm.complex P a l :=
  HomologicalComplex.Hom.isoOfComponents (genuineFiniteTermIso P a l) (by
    intro n m h
    change n+1=m at h
    subst m
    change (genuineFiniteTermIso P a l n).hom ≫ (FullTensorTerm.complex P a l).d n (n+1) =
      (genuineTensorFunctor P a l).map ((TensorResolution.bimoduleComplex k B l).d n (n+1)) ≫
        (genuineFiniteTermIso P a l (n+1)).hom
    have h₁ : (FullTensorTerm.complex P a l).d n (n+1) = ModuleCat.ofHom (FullTensorTerm.differential P a l n) :=
      CochainComplex.of_d (fun n => ModuleCat.of (Enveloping k B) (FullTensorTerm P a l n))
        (fun n => ModuleCat.ofHom (FullTensorTerm.differential P a l n)) n
    have h₂ : (TensorResolution.bimoduleComplex k B l).d n (n+1) =
        ModuleCat.ofHom (TensorResolution.bimoduleDifferential k B l n) :=
      CochainComplex.of_d (fun n => ModuleCat.of (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ)
        (TensorResolution.bimoduleTerm k B l n))
        (fun n => ModuleCat.ofHom (TensorResolution.bimoduleDifferential k B l n)) n
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    dsimp only [genuineTensorFunctor, bimoduleTensorFunctor, FullTensorTerm.complex]
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro q o
    rfl)

/-- The actual all-integer tensor of genuine Q_T with O, retaining both outside B-actions. -/
def genuineComputedTensor : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ :=
  ((genuineTensorFunctor P a l).mapHomologicalComplex (.up ℤ)).obj
    (TensorResolution.integerBimoduleComplex k B l)

/-- Agreement with the preserved full signed-comparison input in every integer degree. -/
def genuineComputedTensorIso : genuineComputedTensor P a l ≅ computedTensorComplex P a l :=
  FunctorExtension.iso (genuineTensorFunctor P a l) (TensorResolution.bimoduleComplex k B l)
      (TensorResolution.degreeEmbedding l) ≪≫
    ((TensorResolution.degreeEmbedding l).extendFunctor _).mapIso (genuineFiniteComplexIso P a l)

/-- The actual ordinary tensor Q_T tensor O is isomorphic to P[b] as B-bimodule complexes.
Only the manuscript support and indexing hypotheses are used. -/
def genuineSourceShiftComparison (b : ℤ) (hb : a+(l:ℤ)=b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) :
    genuineComputedTensor P a l ≅ P⟦b⟧ :=
  genuineComputedTensorIso P a l ≪≫ sourceShiftComparison P a l b hb hP
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySourceBimoduleTotal
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
variable (b : ℤ) (hb : a+(l:ℤ)=b)
variable (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The source signed total comparison for every Z, with the actual outside B-action retained. -/
def sourceBimoduleTotalComparison :
    BimoduleComplexTensor.total k B (B ⊗[k] ChainAlgebra k l)
      (TensorResolution.integerBimoduleComplex k B l)
      (middleLeftComplex k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l) Z)
      (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) ≅
    BimoduleComplexTensor.total k B B (P⟦b⟧) Z
      (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) :=
  (BimoduleComplexTensor.totalAssociativityIso k B (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l)
    (TensorResolution.integerBimoduleComplex k B l) Z
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)).symm ≪≫
  BimoduleComplexTensor.totalRightIso k B B (genuineSourceShiftComparison P a l b hb hP) Z
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryXAugmentation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instAddCommGroup _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instIsScalarTowerEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModule _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModuleEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

/-- The actual ordinary X, represented as a genuine D-bimodule. -/
abbrev ordinaryXObject : ModuleCat.{u} ((AlgebraD k l B) ⊗[k] (AlgebraD k l B)ᵐᵒᵖ) :=
  RetainedBimodule.object k (AlgebraD k l B) (AlgebraD k l B) (BimoduleX P a l)

end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexZeroTotal
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.VertexZeroTotal
open ExternalTensor.Section4
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
local notation "B" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P

variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))

/-- Both higher columns of the constructed total vanish at the first vertex. -/
theorem higher_zero (n : ℤ) :
    IsZero ((vertexFunctor P).obj ((L1Prime s D₀ D₁ D₂ f g).X n)) ∧
    IsZero ((vertexFunctor P).obj ((L2Prime s D₀ D₁ D₂ f g).X n)) := by
  let G := HomologicalComplex.eval (ModuleCat.{u} (Enveloping k B)) (.up ℤ) n ⋙ vertexFunctor P
  let := preservesBinaryBiproducts_of_preservesBiproducts G
  constructor
  · change IsZero (G.obj ((⨁ fun _ : Fin (d+1) =>
      (columnComplex k B (s).e₁).obj D₀) ⊞ (⨁ fun _ : Fin (d+1) =>
      (columnComplex k B (s).e₂).obj D₁)))
    apply (G.mapBiprod _ _).isZero_iff.mpr
    rw [biprod_isZero_iff]
    constructor
    · apply (G.mapBiproduct _).isZero_iff.mpr
      exact sum_isZero _ (fun _ => column_zero P 1 (by decide) D₀ n)
    · apply (G.mapBiproduct _).isZero_iff.mpr
      exact sum_isZero _ (fun _ => column_zero P 2 (by decide) D₁ n)
  · change IsZero (G.obj (⨁ fun _ : RelationBasisCoefficients.RelationIndex P =>
      (columnComplex k B (s).e₂).obj D₀))
    apply (G.mapBiproduct _).isZero_iff.mpr
    exact sum_isZero _ (fun _ => column_zero P 2 (by decide) D₀ n)

/-- At vertex zero, the original zero-column inclusion in the actual total is an isomorphism. -/
theorem inclusion_isIso (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0) :
    IsIso (((vertexFunctor P).mapHomologicalComplex (.up ℤ)).map
      (InducedRectification.inclusion s D₀ D₁ D₂ f g H)) :=
  ZeroColumnTotal.mapped_inclusion_isIso _ _ _ (vertexFunctor P)
    (fun n => (higher_zero P D₀ D₁ D₂ f g n).1)
    (fun n => (higher_zero P D₀ D₁ D₂ f g n).2)
end LittleFinitistic.VertexZeroTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FirstVertex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.FirstVertex
open ExternalTensor.Section4

universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
local notation "B" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

theorem columnInclusion_isIso :
    IsIso ((vertexComplex P).map (columnInclusion P D₀ D₁ D₂ f g)) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts (vertexComplex P)
  apply mapped_inl_isIso
  apply ((vertexComplex P).mapBiprod _ _).isZero_iff.mpr
  rw [biprod_isZero_iff]
  exact ⟨VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 0 1 (by decide) D₁,
    VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 0 2 (by decide) D₂⟩

/-- At the first vertex the original insertion is already a chain isomorphism. -/
theorem iota_isIso : IsIso (iota P D₀ D₁ D₂ f g H) := by
  have := columnInclusion_isIso P D₀ D₁ D₂ f g
  have := VertexZeroTotal.inclusion_isIso P D₀ D₁ D₂ f g H
  let e : D₀ ≅ (vertexComplex P).obj ((columnComplex k B (s).e₀).obj D₀) :=
    VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 0 D₀
  change IsIso (e.hom ≫ (vertexComplex P).map (columnInclusion P D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (InducedRectification.inclusion s D₀ D₁ D₂ f g H))
  infer_instance
end LittleFinitistic.FirstVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_GradedVertexAcyclic
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace LittleFinitistic.GradedVertexAcyclic

open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P

/-- The relation column of the actual source-zero quotient vanishes at vertex one. -/
theorem relationColumn_vertex1_zero :
    IsZero ((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 1).obj
      (Exactness.data s D₀ D₁ D₂ f g).L₂) := by
  let F := AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 1
  change IsZero (F.obj (⨁ fun _ : RelationBasisCoefficients.RelationIndex P =>
    (columnComplex k T (s).e₂).obj D₀))
  apply (F.mapBiproduct _).isZero_iff.mpr
  exact sum_isZero _ (fun _ =>
    VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 1 2 (by decide) D₀)

end LittleFinitistic.GradedVertexAcyclic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SecondVertex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.shiftIso_apply _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTerm_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.shiftTotal_hom_apply _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrow12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_add _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluation_zero _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator01_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.generator12_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_composition _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.pathMap_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.projection_inclusion _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s'_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.s_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex0_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex1_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertex2_smul _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.SourceVerdier.cones_first _root_.OAI.LittleFinitistic.SourceVerdier.cones_second
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.SecondVertex
open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P

theorem intoF1_isIso : IsIso ((vertexComplex P).map (intoF1 P D₀ D₁ D₂ f g)) := by
  let F := vertex P
  let G := vertexComplex P
  have hz : IsZero (G.obj (Z (k := k) (B := T))) := by
    apply G.map_isZero
    apply ZeroColumnTotal.complex_zero
    intro n
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have hv : IsZero (G.obj ((columnComplex k T (s).e₂).obj D₂)) :=
    VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 1 2 (by decide) D₂
  have hs : IsZero (G.obj (F1₁ (Exactness.data s D₀ D₁ D₂ f g))) := by
    apply (G.mapBiproduct _).isZero_iff.mpr
    exact sum_isZero _ (fun _ =>
      VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 1 2 (by decide) D₁)
  have hi := ZeroColumnTotal.mapped_inclusion_isIso
    (p1 (Exactness.data s D₀ D₁ D₂ f g)) 0 (h1 (Exactness.data s D₀ D₁ D₂ f g)) F
    (fun n => (HomologicalComplex.eval _ _ n).map_isZero hs)
    (fun n => (HomologicalComplex.eval _ _ n).map_isZero hz)
  have hj := FirstVertex.mapped_inl_isIso G
    ((columnComplex k T (s).e₁).obj D₁) ((columnComplex k T (s).e₂).obj D₂) hv
  let := hi
  let := hj
  dsimp [intoF1]
  erw [Functor.map_comp]
  exact (show IsIso (G.map (biprod.inl :
    (columnComplex k T (s).e₁).obj D₁ ⟶ F1₀ (Exactness.data s D₀ D₁ D₂ f g)) ≫
      G.map (RectificationTotal.inclusion (p1 (Exactness.data s D₀ D₁ D₂ f g)) 0
        (h1 (Exactness.data s D₀ D₁ D₂ f g)))) from by
    have : IsIso (G.map (biprod.inl :
      (columnComplex k T (s).e₁).obj D₁ ⟶ F1₀ (Exactness.data s D₀ D₁ D₂ f g))) := hj
    rw [isIso_comp_left_iff]
    exact hi)

end LittleFinitistic.SecondVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexTotalProperties
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.VertexTotalProperties
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

variable {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy
  (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

/-- Every actual vertex of the constructed total has projective right-module terms. -/
theorem total_projective (v : Fin 3)
    (h₀ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₂.X n)) (n : ℤ) :
    Projective (((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) v).obj
      (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)).X n) :=
  projective (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) v)
    ((ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition P)).idem v) _
    (InducedRectification.rightTotal_projective (ConcreteQuadraticDiagram.quadratic P)
      D₀ D₁ D₂ f g H h₀ h₁ h₂ n)

theorem total_bounded (v : Fin 3) (lo hi : ℤ)
    (h₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (h₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (h₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n)) :
    ∀ n, n < lo-2 ∨ hi < n → IsZero
      (((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) v).obj
        (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)).X n) := by
  intro n hn
  exact (BimoduleVertex.functor k (QuadraticEncoding.B P)
    (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) v)).map_isZero
    (InducedRectification.total_bounded (ConcreteQuadraticDiagram.quadratic P)
      D₀ D₁ D₂ f g H lo hi h₀ h₁ h₂ n hn)
end LittleFinitistic.VertexTotalProperties

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexHomotopyEquivalence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.VertexHomotopyEquivalence
open ExternalTensor.Section4
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

abbrev target (v : Fin 3) : RightComplex (QuadraticEncoding.B P) :=
  (AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) v).obj
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)

end LittleFinitistic.VertexHomotopyEquivalence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FullTensorRectification
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.FullTensorRectification
open ExternalTensor.Section4 QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B P) N]

/-- The actual left B-module complex P tensor_B N. -/
abbrev tensor := ((BimoduleBalancedTensor.functor k (B P) N).mapHomologicalComplex (.up ℤ)).obj
  (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)

abbrev target (v : Fin 3) :=
  ((LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) v)).mapHomologicalComplex
    (.up ℤ)).obj (tensor P D₀ D₁ D₂ f g H N)

abbrev arrow01Map (a : Fin (d+1)) :=
  ((LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
    (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a)
    (CanonicalArrowCompatibility.arrow01_target P a)).mapHomologicalComplex (.up ℤ)).app
      (tensor P D₀ D₁ D₂ f g H N)
abbrev arrow12Map (b : Fin (d+1)) :=
  ((LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
    (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b)
    (CanonicalArrowCompatibility.arrow12_target P b)).mapHomologicalComplex (.up ℤ)).app
      (tensor P D₀ D₁ D₂ f g H N)

end LittleFinitistic.FullTensorRectification

end

end OAI
end


