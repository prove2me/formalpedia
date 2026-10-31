-- Prove2me | Definitions.Def_OAIQ023F032
-- name    : OAIQ023F032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T19:32:53.876983+00:00
-- url     : https://prove2.me/theorems/66105821-8167-4eec-97dc-c601bf41381a
-- title:
--   Definitions bundle OAIQ023F032 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 26 definitions, 1 inductive type or structure, 5 instances and 17 theorems. The definitions and types are `OAI.LittleFinitistic.FullTensorRectification.compatibility01`, `OAI.LittleFinitistic.FullTensorRectification.compatibility12`, `OAI.LittleFinitistic.FullTensorRectification.iota`, `OAI.LittleFinitistic.GradedVertexAcyclic.grade0Vertex1Iso`, `OAI.LittleFinitistic.GradedVertexAcyclic.grade1VertexIso`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.augmentation`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.augmentationToX`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.complex`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.derivedEvenIterate`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.derivedSquareComparison`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.derivedSquareObject`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.derivedTensor`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.derivedTensorComparison`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.firstBlockComparison`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.ordinaryOComplex`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.recoveredObjectIso`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.secondBlockComparison`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.squareComparison`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.target`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.targetIso`, `OAI.LittleFinitistic.OrdinarySimulation.XResolution.tensorFunctor`, `OAI.LittleFinitistic.RectificationLemma.Verified`, `OAI.LittleFinitistic.SelectedFirstBlockFamily.instHasDerivedCategoryModuleCatBComplexP`, `OAI.LittleFinitistic.SelectedOrdinaryOrbit.instHasDerivedCategoryModuleCatBComplexP`, `OAI.LittleFinitistic.SelectedTensorComparison.tensorMap`, `OAI.LittleFinitistic.TensorCohomologyDiagram.comparison`, `OAI.LittleFinitistic.VertexHomotopyEquivalence.iota`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Localization_QuotientRelations`, `Finitistic_Localization_SourceOddDoubleEvaluation`, `Finitistic_Localization_TensorCohomologyDiagram`, `Finitistic_Ordinary_OrdinaryDerivedIterates`, `Finitistic_Ordinary_OrdinaryDerivedSquareComparison`, `Finitistic_Ordinary_OrdinaryXAugmentation`, `Finitistic_Ordinary_OrdinaryXBlockComparison`, `Finitistic_Ordinary_OrdinaryXDerivedTensor`, `Finitistic_Ordinary_OrdinaryXResolution`, `Finitistic_Rectification_FullTensorRectification`, `Finitistic_Rectification_GradedVertexAcyclic`, `Finitistic_Rectification_RectificationLemma`, `Finitistic_Rectification_SecondVertex`, `Finitistic_Rectification_ThirdVertexFiltration`, `Finitistic_Rectification_VertexHomotopyEquivalence`, `Finitistic_Selected_SelectedCohomologyVanishing`, `Finitistic_Selected_SelectedFirstBlockFamily`, `Finitistic_Selected_SelectedOrdinaryAlgebra`, `Finitistic_Selected_SelectedOrdinaryOrbit`, `Finitistic_Selected_SelectedTensorComparison`.
--
--   **Imports.** It imports the bundles `OAIQ023F028` and `OAIQ023F030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F033` and `OAIQ023F034`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F028
import Definitions.Def_OAIQ023F030

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_QuotientRelations
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingTriangulated _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageShift _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
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

instance boundedKLinear : Linear k (BoundedK P) := inferInstance

instance degreeZeroAdditive : (degreeZero P).Additive := by
  dsimp [degreeZero]
  infer_instance
instance degreeZeroLinear : (degreeZero P).Linear k :=
  inferInstanceAs ((CochainComplex.singleFunctor (ModuleCat.{u} (B P)ᵐᵒᵖ) 0).Linear k)

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceOddDoubleEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule
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

local instance instHasFiniteBiproductsKaroubiQRelations : HasFiniteBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  Karoubi.karoubi_hasFiniteBiproducts
local instance instHasBinaryBiproductsKaroubiQRelations : HasBinaryBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  hasBinaryBiproducts_of_finite_biproducts _
end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_GradedVertexAcyclic
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
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

/-- The actual source-one quotient is the adjacent-arrow cone after taking vertex two. -/
def grade1VertexIso :
    (AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2).obj
      (Exactness.G1 s D₀ D₁ D₂ f g) ≅
    mappingCone ((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2).map
      (ConcreteAdjacentGraded.arrow12Sum P D₁)) :=
  (AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2).mapIso
    (grade1ConeIso (Exactness.data s D₀ D₁ D₂ f g)).symm ≪≫
  mappingCone.mapHomologicalComplexIso (pGrade1 (Exactness.data s D₀ D₁ D₂ f g))
    (BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) 2))

theorem grade1_vertex2_acyclic :
    ((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2).obj
      (Exactness.G1 s D₀ D₁ D₂ f g)).Acyclic :=
  acyclic_of_iso (grade1VertexIso P D₀ D₁ D₂ f g)
    (ConcreteAdjacentGraded.vertex2_cone_acyclic P D₁)

/-- The actual source-zero quotient at vertex one is the first adjacent-arrow cone. -/
def grade0Vertex1Iso :
    (AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 1).obj
      (Exactness.G0 s D₀ D₁ D₂ f g) ≅
    mappingCone ((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 1).map
      (ConcreteAdjacentGraded.arrow01Sum P D₀)) :=
  ZeroLastColumn.mappedTotalIso (p0 (Exactness.data s D₀ D₁ D₂ f g))
    (q0 (Exactness.data s D₀ D₁ D₂ f g)) (h0 (Exactness.data s D₀ D₁ D₂ f g))
    (BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) 1))
    (relationColumn_vertex1_zero P D₀ D₁ D₂ f g)

theorem grade0_vertex1_acyclic :
    ((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 1).obj
      (Exactness.G0 s D₀ D₁ D₂ f g)).Acyclic :=
  acyclic_of_iso (grade0Vertex1Iso P D₀ D₁ D₂ f g)
    (ConcreteAdjacentGraded.vertex1_cone_acyclic P D₀)
end LittleFinitistic.GradedVertexAcyclic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ThirdVertexFiltration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.ThirdVertexFiltration
open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "s" => ConcreteQuadraticDiagram.quadratic P

/-- The original deepest source-filtration inclusion is a quasi-isomorphism at vertex two. -/
theorem inclusion_quasiIso :
    QuasiIso ((vertexComplex P).map (Exactness.i2 s D₀ D₁ D₂ f g)) := by
  let S := Complex.source1 s D₀ D₁ D₂ f g
  exact RectificationAcyclic.quasiIso_of_acyclic_quotient (S.map (vertexComplex P))
    (Complex.vertex_shortExact ((s).e₂)
      ((ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition P)).idem 2) S
      (Complex.source1_shortExact s D₀ D₁ D₂ f g))
    (GradedVertexAcyclic.grade1_vertex2_acyclic P D₀ D₁ D₂ f g)
end LittleFinitistic.ThirdVertexFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SecondVertex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

theorem filtration_inclusion_quasiIso :
    QuasiIso ((vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H)) := by
  let S := Complex.source0 s D₀ D₁ D₂ f g H
  exact RectificationAcyclic.quasiIso_of_acyclic_quotient (S.map (vertexComplex P))
    (Complex.vertex_shortExact ((s).e₁) ((ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition P)).idem 1) S
      (Complex.source0_shortExact s D₀ D₁ D₂ f g H))
    (GradedVertexAcyclic.grade0_vertex1_acyclic P D₀ D₁ D₂ f g)

theorem iota_quasiIso : QuasiIso (iota P D₀ D₁ D₂ f g H) := by
  let := intoF1_isIso P D₀ D₁ D₂ f g
  let := filtration_inclusion_quasiIso P D₀ D₁ D₂ f g H
  let e : D₁ ≅ (vertexComplex P).obj ((columnComplex k T (s).e₁).obj D₁) :=
    VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 1 D₁
  change QuasiIso (e.hom ≫ (vertexComplex P).map (intoF1 P D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H))
  infer_instance

end LittleFinitistic.SecondVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexHomotopyEquivalence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

def iota (v : Fin 3) : source P D₀ D₁ D₂ v ⟶ target P D₀ D₁ D₂ f g H v := by
  refine Fin.cases (FirstVertex.iota P D₀ D₁ D₂ f g H)
    (Fin.cases (SecondVertex.iota P D₀ D₁ D₂ f g H) ?_) v
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact ThirdVertex.iota P D₀ D₁ D₂ f g H

end LittleFinitistic.VertexHomotopyEquivalence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FullTensorRectification
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorLinear _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The original vertex insertion after balanced tensoring and the canonical comparison. -/
def iota (v : Fin 3) : source P D₀ D₁ D₂ N v ⟶ target P D₀ D₁ D₂ f g H N v :=
  ((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map
    (VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H v) ≫
  (TensorArrowComparison.complexIso k (B P) N (ThreeVertexAlgebra.vertex (composition P) v)
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem v)
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)).hom

lemma original_iota0 : VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H 0 =
    FirstVertex.iota P D₀ D₁ D₂ f g H := by rfl
lemma original_iota1 : VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H 1 =
    SecondVertex.iota P D₀ D₁ D₂ f g H := by rfl
lemma original_iota2 : VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H 2 =
    ThirdVertex.iota P D₀ D₁ D₂ f g H := by rfl

/-- Actual arrow compatibility on the vertex diagram of the full B-valued tensor. -/
def compatibility01 (a : Fin (d+1)) : Homotopy
    (iota P D₀ D₁ D₂ f g H N 0 ≫ arrow01Map P D₀ D₁ D₂ f g H N a)
    (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (f a) ≫
      iota P D₀ D₁ D₂ f g H N 1) := by
  have h := ((BalancedTensor.tensorFunctor k (B P) N).mapHomotopy
    (CanonicalArrowCompatibility.compatibility01 P D₀ D₁ D₂ f g H a)).compRight
      (TensorArrowComparison.complexIso k (B P) N (ThreeVertexAlgebra.vertex (composition P) 1)
        ((ThreeVertexAlgebra.directedSystem (composition P)).idem 1)
        (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)).hom
  erw [Functor.map_comp_assoc _ (FirstVertex.iota P D₀ D₁ D₂ f g H)
      (CanonicalArrowCompatibility.arrow01Map P D₀ D₁ D₂ f g H a),
    Functor.map_comp_assoc _ (f a) (SecondVertex.iota P D₀ D₁ D₂ f g H)] at h
  have hs := TensorArrowComparison.complex_arrow_square k (B P) N
    (ThreeVertexAlgebra.vertex (composition P) 0) (ThreeVertexAlgebra.vertex (composition P) 1)
    (arrow01 P a) ((ThreeVertexAlgebra.directedSystem (composition P)).idem 0)
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem 1)
    (CanonicalArrowCompatibility.arrow01_target P a)
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)
  erw [hs] at h
  dsimp only [iota]
  erw [original_iota0, original_iota1, Category.assoc]
  exact h

/-- The second arrow family retains its original maps as well. -/
def compatibility12 (b : Fin (d+1)) : Homotopy
    (iota P D₀ D₁ D₂ f g H N 1 ≫ arrow12Map P D₀ D₁ D₂ f g H N b)
    (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (g b) ≫
      iota P D₀ D₁ D₂ f g H N 2) := by
  have h := ((BalancedTensor.tensorFunctor k (B P) N).mapHomotopy
    (CanonicalArrowCompatibility.compatibility12 P D₀ D₁ D₂ f g H b)).compRight
      (TensorArrowComparison.complexIso k (B P) N (ThreeVertexAlgebra.vertex (composition P) 2)
        ((ThreeVertexAlgebra.directedSystem (composition P)).idem 2)
        (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)).hom
  erw [Functor.map_comp_assoc _ (SecondVertex.iota P D₀ D₁ D₂ f g H)
      (CanonicalArrowCompatibility.arrow12Map P D₀ D₁ D₂ f g H b),
    Functor.map_comp_assoc _ (g b) (ThirdVertex.iota P D₀ D₁ D₂ f g H)] at h
  have hs := TensorArrowComparison.complex_arrow_square k (B P) N
    (ThreeVertexAlgebra.vertex (composition P) 1) (ThreeVertexAlgebra.vertex (composition P) 2)
    (arrow12 P b) ((ThreeVertexAlgebra.directedSystem (composition P)).idem 1)
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem 2)
    (CanonicalArrowCompatibility.arrow12_target P b)
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)
  erw [hs] at h
  dsimp only [iota]
  erw [original_iota1, original_iota2, Category.assoc]
  exact h
end LittleFinitistic.FullTensorRectification

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TensorCohomologyDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorLinear _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.TensorCohomologyDiagram
open ExternalTensor.Section4 QuadraticEncoding FullTensorRectification
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B P) N]

/-- From cohomology of an evaluated representative to the actual vertex of
cohomology of the full B-module tensor complex. -/
def comparison (v : Fin 3) (n : ℤ) : (source P D₀ D₁ D₂ N v).homology n ⟶
    (LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) v)).obj
      ((tensor P D₀ D₁ D₂ f g H N).homology n) :=
  homologyMap (iota P D₀ D₁ D₂ f g H N v) n ≫
    (VertexHomology.iso (algebraMap k (B P)) (ThreeVertexAlgebra.vertex (composition P) v)
      ((ThreeVertexAlgebra.directedSystem (composition P)).idem v)
      (LeftVertexHomology.scalar_commute k (B P) _) (tensor P D₀ D₁ D₂ f g H N) n).hom

/-- The first-family cohomology square retains the full original arrow action. -/
theorem arrow01_square (a : Fin (d+1)) (n : ℤ) :
    homologyMap (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (f a)) n ≫
      comparison P D₀ D₁ D₂ f g H N 1 n =
    comparison P D₀ D₁ D₂ f g H N 0 n ≫
      (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
        (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a)
        (CanonicalArrowCompatibility.arrow01_target P a)).app
          ((tensor P D₀ D₁ D₂ f g H N).homology n) := by
  have h := (FullTensorRectification.compatibility01 P D₀ D₁ D₂ f g H N a).homologyMap_eq n
  erw [homologyMap_comp (iota P D₀ D₁ D₂ f g H N 0)
      (arrow01Map P D₀ D₁ D₂ f g H N a) n,
    homologyMap_comp (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (f a))
      (iota P D₀ D₁ D₂ f g H N 1) n] at h
  dsimp only [comparison]
  erw [← Category.assoc, ← h, Category.assoc]
  erw [LeftVertexHomology.arrow_homology]
  exact (Category.assoc _ _ _).symm

/-- The second-family cohomology square retains the full original arrow action. -/
theorem arrow12_square (b : Fin (d+1)) (n : ℤ) :
    homologyMap (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (g b)) n ≫
      comparison P D₀ D₁ D₂ f g H N 2 n =
    comparison P D₀ D₁ D₂ f g H N 1 n ≫
      (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
        (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b)
        (CanonicalArrowCompatibility.arrow12_target P b)).app
          ((tensor P D₀ D₁ D₂ f g H N).homology n) := by
  have h := (FullTensorRectification.compatibility12 P D₀ D₁ D₂ f g H N b).homologyMap_eq n
  erw [homologyMap_comp (iota P D₀ D₁ D₂ f g H N 1)
      (arrow12Map P D₀ D₁ D₂ f g H N b) n,
    homologyMap_comp (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (g b))
      (iota P D₀ D₁ D₂ f g H N 2) n] at h
  dsimp only [comparison]
  erw [← Category.assoc, ← h, Category.assoc]
  erw [LeftVertexHomology.arrow_homology]
  exact (Category.assoc _ _ _).symm
end LittleFinitistic.TensorCohomologyDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryXResolution
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instAddCommGroup _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instIsScalarTowerEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModule _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModuleEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

abbrev ordinaryOComplex : CochainComplex (ModuleCat.{u} ((B ⊗[k] ChainAlgebra k l) ⊗[k] Bᵐᵒᵖ)) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj (ordinaryOObject P a l)

/-- The manuscript's actual Q_X = O[0] ⊕ Q_T, with both D-actions retained. -/
def complex := OffDiagonal.complex k B (B ⊗[k] ChainAlgebra k l)
  (ordinaryOComplex P a l) (TensorResolution.integerBimoduleComplex k B l)

abbrev target := OffDiagonal.complex k B (B ⊗[k] ChainAlgebra k l)
  (ordinaryOComplex P a l)
  ((HomologicalComplex.single _ (.up ℤ) 0).obj (TensorResolution.bimoduleTerminalObject k B l))

/-- The identity on O and the genuine terminal augmentation give a D-bimodule chain map. -/
def augmentation : complex P a l ⟶ target P a l :=
  OffDiagonal.complexMap k B (B ⊗[k] ChainAlgebra k l) (𝟙 _)
    (TensorResolution.integerBimoduleAugmentation k B l)

theorem ordinaryOComplex_right_projective
    [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)] (n : ℤ) :
    Module.Projective Bᵐᵒᵖ (BimoduleCoefficients k (B ⊗[k] ChainAlgebra k l) B
      ((ordinaryOComplex P a l).X n)) := by
  let F : ModuleCat.{u} ((B ⊗[k] ChainAlgebra k l) ⊗[k] Bᵐᵒᵖ) ⥤ ModuleCat.{u} Bᵐᵒᵖ := ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight (R := k) (A := B ⊗[k] ChainAlgebra k l) (B := Bᵐᵒᵖ)).toRingHom
  by_cases hn : n = 0
  · subst n
    have := ordinaryO_right_projective P a l
    have : Module.Projective Bᵐᵒᵖ (F.obj (ordinaryOObject P a l)) :=
      Module.Projective.of_equiv (RetainedBimodule.rightEquiv k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l)).symm
    have : Projective (F.obj (ordinaryOObject P a l)) := ModuleCat.projective_of_categoryTheory_projective _
    have : Projective (F.obj ((ordinaryOComplex P a l).X 0)) := Projective.of_iso
      (F.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ordinaryOObject P a l))).symm inferInstance
    exact ModuleCat.projective_of_module_projective (F.obj ((ordinaryOComplex P a l).X 0))
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ordinaryOObject P a l) n hn
    have : Projective (F.obj ((ordinaryOComplex P a l).X n)) := (F.map_isZero hz).projective
    exact ModuleCat.projective_of_module_projective (F.obj ((ordinaryOComplex P a l).X n))

/-- Every actual term of Q_X is right-D-projective; no left projectivity is assumed. -/
theorem right_projective
    [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)] (n : ℤ) :
    Module.Projective (AlgebraD k l B)ᵐᵒᵖ
      (BimoduleCoefficients k (AlgebraD k l B) (AlgebraD k l B) ((complex P a l).X n)) := by
  have := ordinaryOComplex_right_projective P a l n
  have : Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ
      (BimoduleCoefficients k B (B ⊗[k] ChainAlgebra k l)
        ((TensorResolution.integerBimoduleComplex k B l).X n)) :=
    TensorResolution.integerBimoduleRight_projective k B l n
  have := OffDiagonal.right_projective B (B ⊗[k] ChainAlgebra k l)
    (BimoduleCoefficients k (B ⊗[k] ChainAlgebra k l) B ((ordinaryOComplex P a l).X n))
    (BimoduleCoefficients k B (B ⊗[k] ChainAlgebra k l) ((TensorResolution.integerBimoduleComplex k B l).X n))
  exact Module.Projective.of_equiv (RetainedBimodule.rightEquiv k (AlgebraD k l B) (AlgebraD k l B) _).symm

/-- The support of the genuine resolution is exactly bounded by [-l,0]. -/
theorem vanishes (n : ℤ) (hn : n < -(l:ℤ) ∨ 0 < n) : IsZero ((complex P a l).X n) := by
  have hn0 : n ≠ 0 := by omega
  have hO := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ordinaryOObject P a l) n hn0
  have hT : IsZero ((TensorResolution.integerBimoduleComplex k B l).X n) := hn.elim
    (TensorResolution.integerBimodule_lower k B l n) (TensorResolution.integerBimodule_upper k B l n)
  have := ModuleCat.isZero_iff_subsingleton.mp hO
  have := ModuleCat.isZero_iff_subsingleton.mp hT
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact inferInstanceAs (Subsingleton (((ordinaryOComplex P a l).X n) ×
    ((TensorResolution.integerBimoduleComplex k B l).X n)))
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryXAugmentation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instAddCommGroup _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instIsScalarTowerEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModule _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModuleEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

def recoveredObjectIso : OffDiagonal.object k B (B ⊗[k] ChainAlgebra k l)
    (ordinaryOObject P a l) (TensorResolution.bimoduleTerminalObject k B l) ≅ ordinaryXObject P a l := by
  let eO := RetainedBimodule.rightEquiv k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l)
  let eT := RetainedBimodule.rightEquiv k B (B ⊗[k] ChainAlgebra k l) (TerminalTensor B)
  let e := OffDiagonal.congr eO eT
  have he (d : AlgebraD k l B) x : e (d • x) = d • e x := by
    apply Prod.ext
    · exact RetainedBimodule.rightEquiv_left k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l) d.2 x.1
    · exact RetainedBimodule.rightEquiv_left k B (B ⊗[k] ChainAlgebra k l) (TerminalTensor B) d.1 x.2
  exact (RetainedBimodule.congr (k := k) e he).toModuleIso

/-- The previous component target is exactly X in degree zero, with both D-actions. -/
def targetIso : target P a l ≅ (HomologicalComplex.single _ (.up ℤ) 0).obj (ordinaryXObject P a l) :=
  OffDiagonal.singleIso k B (B ⊗[k] ChainAlgebra k l) (ordinaryOObject P a l)
    (TensorResolution.bimoduleTerminalObject k B l) ≪≫
    (HomologicalComplex.single _ (.up ℤ) 0).mapIso (recoveredObjectIso P a l)

def augmentationToX : complex P a l ⟶
    (HomologicalComplex.single _ (.up ℤ) 0).obj (ordinaryXObject P a l) :=
  augmentation P a l ≫ (targetIso P a l).hom

/-- The actual bounded right-projective complex augments quasi-isomorphically to X. -/
theorem augmentationToX_quasiIso : QuasiIso (augmentationToX P a l) := by
  have := TensorResolution.integerBimoduleAugmentation_quasiIso k B l
  have : QuasiIso (augmentation P a l) := OffDiagonal.complexMap_quasiIso k B (B ⊗[k] ChainAlgebra k l)
    (𝟙 (ordinaryOComplex P a l)) (TensorResolution.integerBimoduleAugmentation k B l)
  unfold augmentationToX
  infer_instance
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryXDerivedTensor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instAddCommGroup _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instIsScalarTowerEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModule _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModuleEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]

instance rightTerm_projective (n : ℤ) : Module.Projective (AlgebraD k l B)ᵐᵒᵖ
    (ComplexTensor.rightTerm k (AlgebraD k l B)
      (BimoduleComplexTensor.rightComplex k (AlgebraD k l B) (AlgebraD k l B) (complex P a l)) n) :=
  right_projective P a l n

/-- Tensor with the actual right-projective Q_X on arbitrary input complexes of D-modules. -/
abbrev tensorFunctor := BimoduleComplexTensor.totalFunctor k (AlgebraD k l B) (AlgebraD k l B)
  (complex P a l) (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (AlgebraD k l B))]

/-- The derived endofunctor obtained from the actual bounded resolution of X. -/
def derivedTensor : DerivedCategory (ModuleCat.{u} (AlgebraD k l B)) ⥤
    DerivedCategory (ModuleCat.{u} (AlgebraD k l B)) :=
  BimoduleComplexTensor.derivedTotal k (AlgebraD k l B) (AlgebraD k l B) (complex P a l)
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)

def derivedTensorComparison : DerivedCategory.Q ⋙ derivedTensor P a l ≅
    tensorFunctor P a l ⋙ DerivedCategory.Q :=
  BimoduleComplexTensor.derivedTotalComparison k (AlgebraD k l B) (AlgebraD k l B) (complex P a l)
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryXBlockComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

/-- The first actual tensor application is exactly ordinary O tensor Z on the second block. -/
def firstBlockComparison (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    (tensorFunctor P a l).obj (BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l) Z) ≅
    BlockModule.secondComplex B (B ⊗[k] ChainAlgebra k l)
      (middleLeftComplex k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l) Z) :=
  BlockTensor.firstTotalIso k B (B ⊗[k] ChainAlgebra k l) (ordinaryOComplex P a l)
    (TensorResolution.integerBimoduleComplex k B l) Z
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) ≪≫
  ((ProductModules.secondInflation B (B ⊗[k] ChainAlgebra k l)).mapHomologicalComplex (.up ℤ)).mapIso
    (SingleBimoduleTensor.totalIso k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l) Z
      (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) (Fin.last l)
      (by simp [TensorResolution.finiteDegrees]))

/-- The second actual tensor application selects Q_T and retains first-block support. -/
def secondBlockComparison (Y : CochainComplex (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)) ℤ) :
    (tensorFunctor P a l).obj (BlockModule.secondComplex B (B ⊗[k] ChainAlgebra k l) Y) ≅
    BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l)
      (BimoduleComplexTensor.total k B (B ⊗[k] ChainAlgebra k l) (TensorResolution.integerBimoduleComplex k B l) Y
        (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)) :=
  BlockTensor.secondTotalIso k B (B ⊗[k] ChainAlgebra k l) (ordinaryOComplex P a l)
    (TensorResolution.integerBimoduleComplex k B l) Y
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)

/-- The complete actual chain-level square calculation, with the source support and outside action. -/
def squareComparison (b : ℤ) (hb : a+(l:ℤ)=b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    (tensorFunctor P a l).obj ((tensorFunctor P a l).obj (BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l) Z)) ≅
    BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l)
      (BimoduleComplexTensor.total k B B (P⟦b⟧) Z
        (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)) :=
  (tensorFunctor P a l).mapIso (firstBlockComparison P a l Z) ≪≫
  secondBlockComparison P a l (middleLeftComplex k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l) Z) ≪≫
  ((ProductModules.firstInflation B (B ⊗[k] ChainAlgebra k l)).mapHomologicalComplex (.up ℤ)).mapIso
    (sourceBimoduleTotalComparison P a l b hb hP Z)
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryDerivedSquareComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirst_additive _root_.OAI.LittleFinitistic.BlockModule.derivedFirst_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirst_isTriangulated _root_.OAI.LittleFinitistic.BlockModule.derivedFirst_lifting _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
variable (b : ℤ) (hb : a+(l:ℤ)=b)
variable (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (AlgebraD k l B))]

/-- The actual native derived square comparison on every complex Z, with first-block support.
Both tensor functors are the localization lifts of their verified bounded projective models. -/
def derivedSquareComparison (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    (derivedTensor P a l).obj ((derivedTensor P a l).obj
      ((BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj (DerivedCategory.Q.obj Z))) ≅
    (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj
      ((shiftedDerivedTensor P b l).obj (DerivedCategory.Q.obj Z)) :=
  (derivedTensor P a l).mapIso ((derivedTensor P a l).mapIso
    ((BlockModule.derivedFirstComparison B (B ⊗[k] ChainAlgebra k l)).app Z)) ≪≫
  (derivedTensor P a l).mapIso ((derivedTensorComparison P a l).app
    (BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l) Z)) ≪≫
  (derivedTensorComparison P a l).app
    ((tensorFunctor P a l).obj (BlockModule.firstComplex B (B ⊗[k] ChainAlgebra k l) Z)) ≪≫
  DerivedCategory.Q.mapIso (squareComparison P a l b hb hP Z) ≪≫
  ((BlockModule.derivedFirstComparison B (B ⊗[k] ChainAlgebra k l)).app
    (BimoduleComplexTensor.total k B B (P⟦b⟧) Z
      (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l))).symm ≪≫
  (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).mapIso
    ((shiftedDerivedTensorComparison P b l).app Z).symm
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryDerivedIterates
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirst_additive _root_.OAI.LittleFinitistic.BlockModule.derivedFirst_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirst_isTriangulated _root_.OAI.LittleFinitistic.BlockModule.derivedFirst_lifting _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (b : ℤ) (hb : a+(l:ℤ)=b)
variable (hP : ∀ n : ℤ, n < a ∨ b < n → Limits.IsZero (P.X n))
variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (AlgebraD k l B))]

/-- The actual ordinary square on every native derived object, using essential surjectivity of Q. -/
def derivedSquareObject (Y : DerivedCategory (ModuleCat.{u} B)) :
    (derivedTensor P a l).obj ((derivedTensor P a l).obj
      ((BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj Y)) ≅
    (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj
      ((shiftedDerivedTensor P b l).obj Y) :=
  let e := DerivedCategory.Q.objObjPreimageIso Y
  (derivedTensor P a l).mapIso ((derivedTensor P a l).mapIso
    ((BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).mapIso e.symm)) ≪≫
  derivedSquareComparison P a l b hb hP (DerivedCategory.Q.objPreimage Y) ≪≫
  (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).mapIso
    ((shiftedDerivedTensor P b l).mapIso e)

/-- Every even iterate is the first-block inflation of the corresponding actual P[b] tensor iterate. -/
def derivedEvenIterate (n : ℕ) (Y : DerivedCategory (ModuleCat.{u} B)) :
    ((derivedTensor P a l).obj)^[2*n]
      ((BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj Y) ≅
    (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj
      (((shiftedDerivedTensor P b l).obj)^[n] Y) := by
  induction n with
  | zero => exact Iso.refl _
  | succ n ih =>
    have hn : 2*(n+1) = (2*n+1)+1 := by omega
    rw [hn,Function.iterate_succ_apply',Function.iterate_succ_apply',Function.iterate_succ_apply']
    exact (derivedTensor P a l).mapIso ((derivedTensor P a l).mapIso ih) ≪≫
      derivedSquareObject P a l b hb hP (((shiftedDerivedTensor P b l).obj)^[n] Y)
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_RectificationLemma
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.RectificationLemma
open ExternalTensor.Section4 QuadraticEncoding CanonicalArrowCompatibility
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

/-- The conclusions of the paper's rectification lemma for the explicitly constructed
bimodule complex and original vertex insertion maps. -/
structure Verified (lo hi : ℤ) : Prop where
  bounded : ∀ n, n < lo-2 ∨ hi < n → IsZero
    ((InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H).X n)
  projective : ∀ n, Projective
    ((InducedRectification.rightTotal (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H).X n)
  finite : ∀ n, FiniteDimensional k ((forgetK k (B P)).obj
    ((InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H).X n))
  vertices : ∀ v : Fin 3, ∃ j :
    VertexHomotopyEquivalence.target P D₀ D₁ D₂ f g H v ⟶
    VertexHomotopyEquivalence.source P D₀ D₁ D₂ v,
    Nonempty (Homotopy (VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H v ≫ j) (𝟙 _)) ∧
    Nonempty (Homotopy (j ≫ VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H v) (𝟙 _))
  arrows01 : ∀ a, Nonempty (Homotopy
    (FirstVertex.iota P D₀ D₁ D₂ f g H ≫ arrow01Map P D₀ D₁ D₂ f g H a)
    (f a ≫ SecondVertex.iota P D₀ D₁ D₂ f g H))
  arrows12 : ∀ b, Nonempty (Homotopy
    (SecondVertex.iota P D₀ D₁ D₂ f g H ≫ arrow12Map P D₀ D₁ D₂ f g H b)
    (g b ≫ ThirdVertex.iota P D₀ D₁ D₂ f g H))

end LittleFinitistic.RectificationLemma

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedCohomologyVanishing
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedCohomologyVanishing
open QuadraticEncoding
section General
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The three actual vertex functors jointly detect a zero module. -/
theorem module_isZero (M : ModuleCat.{u} (B P))
    (h : ∀ i : Fin 3, IsZero
      ((LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj M)) :
    IsZero M := by
  let M' := (ModuleCat.restrictScalars (algebraMap k (B P))).obj M
  have (i : Fin 3) : Subsingleton
      (VertexDecomposition.Space (EncodingModuleAssembly.system P) M' i) := by
    let := ModuleCat.subsingleton_of_isZero (h i)
    exact (LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) i) M).symm.injective.subsingleton
  have : Subsingleton M' := (VertexDecomposition.equiv (EncodingModuleAssembly.system P) M').injective.subsingleton
  have : Subsingleton M := inferInstanceAs (Subsingleton M')
  exact ModuleCat.isZero_of_subsingleton M
end General

open SelectedFixedDiagram
end LittleFinitistic.SelectedCohomologyVanishing

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedOrdinaryAlgebra
open SelectedFixedDiagram QuadraticEncoding
open OrdinarySimulation

instance base_finite : FiniteDimensional ℂ (B P) := QuadraticEncoding.finiteDimensional P
end LittleFinitistic.SelectedOrdinaryAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTensorComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
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

abbrev tensorMap {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E) :=
  ((BalancedTensor.tensorFunctor k (B P) X.Evaluation).mapHomologicalComplex (.up ℤ)).map
    (((UnderlyingRepresentatives.forget P).mapHomologicalComplex (.up ℤ)).map f)

end LittleFinitistic.SelectedTensorComparison

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedFirstBlockFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedFirstBlockFamily
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
open SelectedOrdinaryAlgebra SelectedFixedDiagram QuadraticEncoding
local instance instHasDerivedCategoryModuleCatBComplexP : HasDerivedCategory.{1} (ModuleCat.{0} (B P)) :=
  HasDerivedCategory.standard (ModuleCat.{0} (B P))
end LittleFinitistic.SelectedFirstBlockFamily

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LittleFinitistic.SelectedOrdinaryOrbit
open SelectedOrdinaryAlgebra SelectedFixedDiagram QuadraticEncoding
local instance instHasDerivedCategoryModuleCatBComplexP : HasDerivedCategory.{1} (ModuleCat.{0} (B P)) :=
  HasDerivedCategory.standard (ModuleCat.{0} (B P))

end LittleFinitistic.SelectedOrdinaryOrbit

end

end OAI
end


