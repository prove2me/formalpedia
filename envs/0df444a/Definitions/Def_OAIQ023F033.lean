-- Prove2me | Definitions.Def_OAIQ023F033
-- name    : OAIQ023F033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T19:40:59.878566+00:00
-- url     : https://prove2.me/theorems/ba302b27-9790-421b-887d-0e68c97de4db
-- title:
--   Definitions bundle OAIQ023F033 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 69 declarations of OpenAI's Lean: 32 definitions, 2 inductive types or structures, 24 instances and 11 theorems. The definitions and types are `OAI.LittleFinitistic.SelectedChainDiagram.D0`, `OAI.LittleFinitistic.SelectedChainDiagram.D1`, `OAI.LittleFinitistic.SelectedChainDiagram.D2`, `OAI.LittleFinitistic.SelectedChainDiagram.Data`, `OAI.LittleFinitistic.SelectedChainDiagram.fixedChain`, `OAI.LittleFinitistic.SelectedDiagramEvaluation.F`, `OAI.LittleFinitistic.SelectedDiagramEvaluation.G`, `OAI.LittleFinitistic.SelectedDiagramEvaluation.sourceFactors`, `OAI.LittleFinitistic.SelectedRealization.input`, `OAI.LittleFinitistic.SelectedRealization.selectedRepresentation`, `OAI.LittleFinitistic.SelectedRectification.D1`, `OAI.LittleFinitistic.SelectedRectification.D2`, `OAI.LittleFinitistic.SelectedRectification.f`, `OAI.LittleFinitistic.SelectedTensor.source`, `OAI.LittleFinitistic.SelectedWindow.Window`, `OAI.LittleFinitistic.SourceActionEvaluation.evaluated`, `OAI.LittleFinitistic.SourceActionEvaluation.evaluation`, `OAI.LittleFinitistic.SourceActionEvaluation.vertexIso`, `OAI.LittleFinitistic.SourceEvaluation.derived`, `OAI.LittleFinitistic.SourceEvaluation.derivedVertexIso`, `OAI.LittleFinitistic.SourceEvaluation.finiteFactors`, `OAI.LittleFinitistic.SourceEvaluation.homotopyFactors`, `OAI.LittleFinitistic.SourceEvaluation.quotientFinite`, `OAI.LittleFinitistic.SourceEvaluation.quotientHomotopy`, `OAI.LittleFinitistic.SourceEvaluation.quotientVertexIso`, `OAI.LittleFinitistic.SourceImageEvaluation.U`, `OAI.LittleFinitistic.SourceImageEvaluation.completed`, `OAI.LittleFinitistic.SourceImageEvaluation.evaluation`, `OAI.LittleFinitistic.SourceImageEvaluation.factors`, `OAI.LittleFinitistic.SourceImageEvaluation.inclusion`, `OAI.LittleFinitistic.SourceImageEvaluation.projection`, `OAI.LittleFinitistic.SourceImageEvaluation.representation`, `OAI.LittleFinitistic.SourceImageEvaluation.shiftIso`, `OAI.LittleFinitistic.SourceImageEvaluation.vertexIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Localization_BoundedQuotientEvaluation`, `Finitistic_Localization_EvaluationLinear`, `Finitistic_Localization_FiniteEvaluationTarget`, `Finitistic_Localization_HomotopyVertexEvaluation`, `Finitistic_Localization_SourceActionEvaluation`, `Finitistic_Localization_SourceEvaluation`, `Finitistic_Localization_SourceImageEvaluation`, `Finitistic_Localization_SourceModelBridge`, `Finitistic_Localization_SourceOddDoubleEvaluation`, `Finitistic_Selected_SelectedChainDiagram`, `Finitistic_Selected_SelectedDiagramEvaluation`, `Finitistic_Selected_SelectedRealization`, `Finitistic_Selected_SelectedRectification`, `Finitistic_Selected_SelectedTensor`, `Finitistic_Selected_SelectedWindow`.
--
--   **Imports.** It imports the bundles `OAIQ023F031` and `OAIQ023F032` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F035` and `OAIQ023F036`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F031
import Definitions.Def_OAIQ023F032

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_BoundedQuotientEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.homotopyEvaluationLinear _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingTriangulated _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageShift _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
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

instance boundedEvaluationAdditive : (boundedEvaluation X).Additive :=
  inferInstanceAs (inclusion (B P)ᵐᵒᵖ ⋙ homotopyEvaluation k (B P) X.Evaluation).Additive
instance boundedEvaluationTriangulated : (boundedEvaluation X).IsTriangulated :=
  inferInstanceAs (inclusion (B P)ᵐᵒᵖ ⋙ homotopyEvaluation k (B P) X.Evaluation).IsTriangulated

end QuadraticEncoding
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_HomotopyVertexEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.homotopyEvaluationLinear _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorLinear _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingTriangulated _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageShift _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
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

lemma homotopy_arrow12_square (h : Fin (d+1)) :
    (boundedEvaluation X).map (arrowK12 P h) ≫ (homotopyVertexIso X 2).hom =
    (homotopyVertexIso X 1).hom ≫ (vectorStalk (k := k)).map (actionArrow X h) := by
  change (homotopyEvaluation k (B P) X.Evaluation).map
    ((inclusion (B P)ᵐᵒᵖ).map (arrowK12 P h)) ≫ _ = _
  unfold arrowK12
  erw [Functor.map_preimage]
  change ((tensorFunctor k (B P) X.Evaluation).mapHomotopyCategory (.up ℤ)).map
    ((HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule12 P h))) ≫
    ((HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 2)) ≫
      (HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (liftedVertexEquiv X 2).toModuleIso.hom)) =
    ((HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 1)) ≫
      (HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (liftedVertexEquiv X 1).toModuleIso.hom)) ≫
    (HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (actionArrow X h))
  simp only [Functor.mapHomotopyCategory_map]
  have hn := (HomologicalComplex.singleMapHomologicalComplex
    (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.naturality (arrowModule12 P h)
  have hm := congrArg (fun f => (HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map f)
    (tensor_arrow12_square X h)
  simp only [Functor.map_comp] at hm
  have hc := (congrArg (fun f => f ≫
    (HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map
      (liftedVertexEquiv X 2).toModuleIso.hom) hn).trans (by
        simpa only [Category.assoc, Functor.comp_map, degreeZero] using congrArg (fun f =>
          (HomologicalComplex.singleMapHomologicalComplex
            (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 1) ≫ f) hm)
  have hfin := congrArg (fun f => (HomotopyCategory.quotient (ModuleCat.{max u v} k) (.up ℤ)).map f) hc
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map, degreeZero] at hfin ⊢
  exact hfin
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationLinear
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingTriangulated _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageShift _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
open BalancedTensor FiniteProjectiveHomotopy
universe u v w z
namespace QuadraticEncoding
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

instance boundedEvaluationLinear : (boundedEvaluation X).Linear k :=
  inferInstanceAs ((inclusion (B P)ᵐᵒᵖ ⋙ homotopyEvaluation k (B P) X.Evaluation).Linear k)

end QuadraticEncoding
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteEvaluationTarget
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingTriangulated _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageShift _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
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

instance finiteEvaluationAdditive : (finiteEvaluation X).Additive := by
  dsimp [finiteEvaluation]
  infer_instance
instance finiteEvaluationTriangulated : (finiteEvaluation X).IsTriangulated := by
  dsimp [finiteEvaluation]
  infer_instance

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceModelBridge
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
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

instance instAdditiveKBoundedKToBounded : (toBounded P).Additive := by unfold toBounded; infer_instance
instance instLinearKBoundedKToBounded : (toBounded P).Linear k where
  map_smul := by
    intro X Y f a
    apply ObjectProperty.hom_ext
    exact (ambient P).map_smul a f
instance instIsTriangulatedKBoundedKToBounded : (toBounded P).IsTriangulated := by unfold toBounded; infer_instance

lemma vertex_arrow01 (a : Fin (d+1)) :
    (toBounded P).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P a)) ≫
      (vertexIso P 1).hom = (vertexIso P 0).hom ≫ arrowK01 P a := by
  apply (inclusion (B P)ᵐᵒᵖ).map_injective
  simp only [Functor.map_comp,vertexIso,Functor.preimageIso,Functor.map_preimage]
  change (ambient P).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P a)) ≫
    ((stalkUnderlyingIso P (SourceVerdier.E P 1)).hom ≫
      (rightStalk P).map (SourceQuotientAction.vertexIso P 1).hom) = _
  rw [← Category.assoc,stalkUnderlying_square,Category.assoc,← Functor.map_comp]
  have h := congrArg (fun f => f.hom ≫ (SourceQuotientAction.vertexIso P 1).hom)
    (SourceQuotientAction.nativeHom_arrow01 P a)
  dsimp [SourceQuotientAction.nativeHom] at h
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at h
  rw [← h,Functor.map_comp]
  unfold arrowK01
  erw [Functor.map_preimage]
  exact (Category.assoc _ _ _).symm

lemma vertex_arrow12 (a : Fin (d+1)) :
    (toBounded P).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow12 P a)) ≫
      (vertexIso P 2).hom = (vertexIso P 1).hom ≫ arrowK12 P a := by
  apply (inclusion (B P)ᵐᵒᵖ).map_injective
  simp only [Functor.map_comp,vertexIso,Functor.preimageIso,Functor.map_preimage]
  change (ambient P).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow12 P a)) ≫
    ((stalkUnderlyingIso P (SourceVerdier.E P 2)).hom ≫
      (rightStalk P).map (SourceQuotientAction.vertexIso P 2).hom) = _
  rw [← Category.assoc,stalkUnderlying_square,Category.assoc,← Functor.map_comp]
  have h := congrArg (fun f => f.hom ≫ (SourceQuotientAction.vertexIso P 2).hom)
    (SourceQuotientAction.nativeHom_arrow12 P a)
  dsimp [SourceQuotientAction.nativeHom] at h
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at h
  rw [← h,Functor.map_comp]
  unfold arrowK12
  erw [Functor.map_preimage]
  exact (Category.assoc _ _ _).symm
end LittleFinitistic.SourceModelBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
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

instance instLinearKHomotopyCategoryIntModuleCatUpEvaluation : (evaluation X).Linear k := by unfold evaluation; infer_instance

lemma arrow01_square (a : Fin (d+1)) :
    (evaluation X).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P a)) ≫
      (vertexIso X 1).hom = (vertexIso X 0).hom ≫ (vectorStalk (k := k)).map (actionArrow X a) := by
  have h := congrArg (fun f => (boundedEvaluation X).map f) (SourceModelBridge.vertex_arrow01 P a)
  simp only [Functor.map_comp] at h
  dsimp only [vertexIso,Iso.trans_hom,Functor.mapIso_hom,evaluation,Functor.comp_map]
  rw [← Category.assoc,h,Category.assoc,homotopy_arrow01_square,← Category.assoc]

lemma arrow12_square (a : Fin (d+1)) :
    (evaluation X).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow12 P a)) ≫
      (vertexIso X 2).hom = (vertexIso X 1).hom ≫ (vectorStalk (k := k)).map (actionArrow X a) := by
  have h := congrArg (fun f => (boundedEvaluation X).map f) (SourceModelBridge.vertex_arrow12 P a)
  simp only [Functor.map_comp] at h
  dsimp only [vertexIso,Iso.trans_hom,Functor.mapIso_hom,evaluation,Functor.comp_map]
  rw [← Category.assoc,h,Category.assoc,homotopy_arrow12_square,← Category.assoc]

instance first_inverted : IsIso ((evaluation X).map (SourceVerdier.cones P).first.mor₁) := by
  change IsIso ((evaluation X).map (SourceVerdier.s P))
  have : IsIso ((evaluation X).map (SourceVerdier.s P) ≫ (vertexIso X 1).hom) := by
    change IsIso ((evaluation X).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P 0)) ≫ _)
    rw [arrow01_square,actionArrow_zero,CategoryTheory.Functor.map_id,Category.comp_id]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (vertexIso X 1).hom
instance second_inverted : IsIso ((evaluation X).map (SourceVerdier.cones P).second.mor₁) := by
  change IsIso ((evaluation X).map (SourceVerdier.s' P))
  have : IsIso ((evaluation X).map (SourceVerdier.s' P) ≫ (vertexIso X 2).hom) := by
    change IsIso ((evaluation X).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow12 P 0)) ≫ _)
    rw [arrow12_square,actionArrow_zero,CategoryTheory.Functor.map_id,Category.comp_id]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (vertexIso X 2).hom

variable [FiniteDimensional k Y]
instance instAdditiveKFiniteVectorHomotopyFinite : (finite X).Additive := by unfold finite; infer_instance
instance instCommShiftKFiniteVectorHomotopyFiniteInt : (finite X).CommShift ℤ := by unfold finite; infer_instance
instance instIsTriangulatedKFiniteVectorHomotopyFinite : (finite X).IsTriangulated := by unfold finite; infer_instance
instance finite_first : IsIso ((finite X).map (SourceVerdier.cones P).first.mor₁) := by
  have : IsIso ((inclusion k).map ((finite X).map (SourceVerdier.cones P).first.mor₁)) :=
    inferInstanceAs (IsIso ((evaluation X).map (SourceVerdier.cones P).first.mor₁))
  exact isIso_of_reflects_iso _ (inclusion k)
instance finite_second : IsIso ((finite X).map (SourceVerdier.cones P).second.mor₁) := by
  have : IsIso ((inclusion k).map ((finite X).map (SourceVerdier.cones P).second.mor₁)) :=
    inferInstanceAs (IsIso ((evaluation X).map (SourceVerdier.cones P).second.mor₁))
  exact isIso_of_reflects_iso _ (inclusion k)

def quotientFinite : SourceVerdier.Q P ⥤ FiniteVectorHomotopy.{u,v} (k := k) :=
  (SourceVerdier.cones P).evaluation (finite X)
def finiteFactors : SourceVerdier.q P ⋙ quotientFinite X ≅ finite X :=
  (SourceVerdier.cones P).evaluation_fac (finite X)
instance instAdditiveQFiniteVectorHomotopyQuotientFinite : (quotientFinite X).Additive := by
  rw [Localization.functor_additive_iff (SourceVerdier.q P) (SourceVerdier.Sigma P)]
  exact Functor.additive_of_iso (finiteFactors X).symm
instance instCommShiftQFiniteVectorHomotopyQuotientFiniteInt : (quotientFinite X).CommShift ℤ := by unfold quotientFinite; infer_instance

def quotientHomotopy : SourceVerdier.Q P ⥤ HomotopyCategory (ModuleCat.{max u v} k) (.up ℤ) :=
  quotientFinite X ⋙ inclusion k
instance instAdditiveQHomotopyCategoryIntModuleCatUpQuotientHomotopy : (quotientHomotopy X).Additive := by unfold quotientHomotopy; infer_instance

def homotopyFactors : SourceVerdier.q P ⋙ quotientHomotopy X ≅ evaluation X :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (finiteFactors X) (inclusion k)
instance instLiftingKQHomotopyCategoryIntModuleCatUpQSigmaEvaluationQuotientHomotopy : Localization.Lifting (SourceVerdier.q P) (SourceVerdier.Sigma P)
    (evaluation X) (quotientHomotopy X) := ⟨homotopyFactors X⟩
instance instLinearQHomotopyCategoryIntModuleCatUpQuotientHomotopy : (quotientHomotopy X).Linear k :=
  (Localization.functor_linear_iff (SourceVerdier.q P) (SourceVerdier.Sigma P) k
    (evaluation X) (quotientHomotopy X)).mp inferInstance

def quotientVertexIso (i : Fin 3) :
    (quotientHomotopy X).obj (SourceQuotientAction.vertex P i) ≅
      (vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y)) :=
  (homotopyFactors X).app ((SourceVerdier.stalk P).obj (SourceVerdier.E P i)) ≪≫ vertexIso X i

lemma quotient_arrow01_square (a : Fin (d+1)) :
    (quotientHomotopy X).map (SourceQuotientAction.a01 P a) ≫ (quotientVertexIso X 1).hom =
      (quotientVertexIso X 0).hom ≫ (vectorStalk (k := k)).map (actionArrow X a) := by
  have h := (homotopyFactors X).hom.naturality ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P a))
  have h' : (quotientHomotopy X).map (SourceQuotientAction.a01 P a) ≫
      ((homotopyFactors X).app ((SourceVerdier.stalk P).obj (SourceVerdier.E P 1))).hom =
    ((homotopyFactors X).app ((SourceVerdier.stalk P).obj (SourceVerdier.E P 0))).hom ≫
      (evaluation X).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P a)) := h
  dsimp only [quotientVertexIso,Iso.trans_hom]
  rw [← Category.assoc,h',Category.assoc,arrow01_square,← Category.assoc]

def derived : SourceVerdier.Q P ⥤ FiniteVectorDerived.{u,v} (k := k) :=
  quotientFinite X ⋙ (derivedEmbedding k).toEssImage
instance instAdditiveQFiniteVectorDerivedDerived : (derived X).Additive := by unfold derived; infer_instance
instance instCommShiftQFiniteVectorDerivedDerivedInt : (derived X).CommShift ℤ := by unfold derived; infer_instance

def derivedVertexIso (i : Fin 3) :
    (derived X ⋙ derivedTargetInclusion (k := k)).obj (SourceQuotientAction.vertex P i) ≅
      DerivedCategory.Qh.obj ((vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y))) :=
  DerivedCategory.Qh.mapIso (quotientVertexIso X i)
end LittleFinitistic.SourceEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceActionEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite
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

abbrev evaluation := SourceEvaluation.quotientHomotopy (representation (Y := Y) E)
abbrev vertexIso := SourceEvaluation.quotientVertexIso (representation (Y := Y) E)

def evaluated : R →ₐ[k] End ((vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y))) :=
  (identifiedEndHom (evaluation (Y := Y) E) _ (vertexIso (Y := Y) E 0)).comp
    (SourceQuotientAction.theta E)

lemma theta_generator (h : Fin E.generators) :
    SourceQuotientAction.theta E (generator E h) =
      SourceQuotientAction.a01 E.relations h.succ ≫ inv (SourceQuotientAction.a01 E.relations 0) := by
  simp only [SourceQuotientAction.theta,QuotientAction.presentedAction,AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom,generator,AlgEquiv.symm_apply_apply,QuotientAction.quotientAction_generator,
    QuotientAction.normalized]

lemma generator_square (h : Fin E.generators) :
    (evaluation (Y := Y) E).map (SourceQuotientAction.theta E (generator E h)) ≫
      (vertexIso (Y := Y) E 0).hom = (vertexIso (Y := Y) E 0).hom ≫
        (vectorStalk (k := k)).map (liftedEndHom ((Algebra.lsmul k k Y) (generator E h))) := by
  rw [theta_generator]
  apply QuotientAction.normalized_evaluation (SourceQuotientAction.a01 E.relations 0)
    (fun h => SourceQuotientAction.a01 E.relations h.succ) (evaluation (Y := Y) E)
    (vertexIso (Y := Y) E 0) (vertexIso (Y := Y) E 1)
    (fun h => (vectorStalk (k := k)).map (liftedEndHom ((Algebra.lsmul k k Y) (generator E h))))
  · simpa only [SourceEvaluation.actionArrow_zero,CategoryTheory.Functor.map_id,Category.comp_id] using
      SourceEvaluation.quotient_arrow01_square (representation (Y := Y) E) 0
  · intro h
    exact SourceEvaluation.quotient_arrow01_square (representation (Y := Y) E) h.succ

lemma evaluated_generator (h : Fin E.generators) :
    evaluated (Y := Y) E (generator E h) = given (Y := Y) E (generator E h) := by
  have hh := congrArg (fun f => (vertexIso (Y := Y) E 0).inv ≫ f) (generator_square (Y := Y) E h)
  change (vertexIso (Y := Y) E 0).inv ≫
    ((evaluation (Y := Y) E).map (SourceQuotientAction.theta E (generator E h)) ≫
      (vertexIso (Y := Y) E 0).hom) = _ at hh
  dsimp [evaluated,given,identifiedEndHom]
  simpa only [Category.assoc,Iso.inv_hom_id_assoc,Category.id_comp,Category.comp_id] using hh

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

abbrev representation := SourceActionEvaluation.representation (Y := Y) E
abbrev evaluation := SourceEvaluation.derived (representation (Y := Y) E)
abbrev vertexIso := SourceEvaluation.derivedVertexIso (representation (Y := Y) E) 0

def completed : Karoubi (SourceVerdier.Q E.relations) ⥤ FiniteVectorDerived.{u,v} (k := k) :=
  (functorExtension _ _).obj (evaluation (Y := Y) E)
instance instAdditiveKaroubiQRelationsFiniteVectorDerivedCompleted : (completed (Y := Y) E).Additive := completedExtensionAdditive _
def factors : toKaroubi (SourceVerdier.Q E.relations) ⋙ completed (Y := Y) E ≅ evaluation (Y := Y) E :=
  completedExtensionFactors _

abbrev U (e : R) (he : e*e=e) := FormalSummandAction.summand (SourceQuotientAction.theta E) e he

def projection (e : R) :
    (derivedTargetInclusion (k := k)).obj ((evaluation (Y := Y) E).obj (SourceQuotientAction.vertex E.relations 0)) ⟶
      (derivedTargetInclusion (k := k)).obj (imageDerived (k := k) (Y := Y) e) :=
  (vertexIso (Y := Y) E).hom ≫ DerivedCategory.Qh.map
    ((vectorStalk (k := k)).map (imageProjection (action (k := k) (Y := Y) e).hom))
def inclusion (e : R) :
    (derivedTargetInclusion (k := k)).obj (imageDerived (k := k) (Y := Y) e) ⟶
      (derivedTargetInclusion (k := k)).obj ((evaluation (Y := Y) E).obj (SourceQuotientAction.vertex E.relations 0)) :=
  DerivedCategory.Qh.map ((vectorStalk (k := k)).map (imageInclusion (action (k := k) (Y := Y) e).hom)) ≫
    (vertexIso (Y := Y) E).inv

lemma inclusion_projection (e : R) (he : e*e=e) :
    inclusion (Y := Y) E e ≫ projection (Y := Y) E e = 𝟙 _ := by
  dsimp only [inclusion,projection]
  erw [Category.assoc,Iso.inv_hom_id_assoc]
  erw [← Functor.map_comp,← Functor.map_comp,image_inclusion_projection _ (action_idem (k := k) (Y := Y) e he)]
  erw [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_id]
  rfl
end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceOddDoubleEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
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

/-- The additive extension respects the native formal shift. -/
def shiftIso (n : ℤ) :
    OddDouble.formalShiftFunctor (C := SourceVerdier.Q E.relations) n ⋙ completed (Y := Y) E ≅
      completed (Y := Y) E ⋙ shiftFunctor (FiniteVectorDerived.{u,v} (k := k)) n :=
  completedCommutationIso (evaluation (Y := Y) E) _ _ ((evaluation (Y := Y) E).commShiftIso n)

attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instHasFiniteBiproductsKaroubiQRelations
attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instHasBinaryBiproductsKaroubiQRelations
local instance instPreservesBinaryBiproductsKaroubiQRelationsFiniteVectorDerivedCompleted : PreservesBinaryBiproducts (completed (Y := Y) E) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

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

abbrev F := SourceImageEvaluation.evaluation (Y := Y) encoding
abbrev G := completed (Y := Y) encoding

def sourceFactors : SourceVerdier.q P ⋙ F (Y := Y) ≅ sourceEvaluation (Y := Y) :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
    (SourceEvaluation.finiteFactors (SourceActionEvaluation.representation (Y := Y) encoding))
    (FiniteProjectiveHomotopy.derivedEmbedding ℂ).toEssImage

end LittleFinitistic.SelectedDiagramEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedChainDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedChainDiagram
open SelectedFixedDiagram RelationBasisCoefficients ConcreteChainRepresentatives

abbrev D0 := representative P fixed.D0
abbrev D1 := representative P fixed.D1
abbrev D2 := representative P fixed.D2

/-- Chain representatives and all specified relation homotopies for the one fixed diagram. -/
structure Data where
  f : Fin (encoding.generators+1) → (D0 ⟶ D1)
  g : Fin (encoding.generators+1) → (D1 ⟶ D2)
  f_quotient : ∀ a, (HomotopyCategory.quotient (SourceVerdier.Proj P) (.up ℤ)).map (f a) = (fixed.f a).hom
  g_quotient : ∀ b, (HomotopyCategory.quotient (SourceVerdier.Proj P) (.up ℤ)).map (g b) = (fixed.g b).hom
  homotopy : ∀ r : RelationIndex P,
    Homotopy (∑ a, ∑ b, basisCoefficient P r a b • (f a ≫ g b)) 0

/-- These choices, too, are made once before any evaluation module Y. -/
def fixedChain : Data := Classical.choice (by
  obtain ⟨f,g,hf,hg,⟨h⟩⟩ := quadratic_representatives P _ _ _
    fixed.D0 fixed.D1 fixed.D2 fixed.f fixed.g (basisCoefficient P) fixed.relations
  exact ⟨⟨f,g,hf,hg,h⟩⟩)

universe v
end LittleFinitistic.SelectedChainDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedRectification
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.SelectedRectification
open SelectedFixedDiagram ExternalTensor.Section4 RelationBasisCoefficients

abbrev D1 := UnderlyingRepresentatives.complex P fixed.D1
abbrev D2 := UnderlyingRepresentatives.complex P fixed.D2
def f (a : Fin (encoding.generators+1)) : D0 ⟶ D1 := F.map (SelectedChainDiagram.fixedChain.f a)
end LittleFinitistic.SelectedRectification

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.SelectedTensor
open SelectedFixedDiagram SelectedRectification QuadraticEncoding
variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module (B P) N]

abbrev source (v : Fin 3) := FullTensorRectification.source P D0 D1 D2 N v
end LittleFinitistic.SelectedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedRealization
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite
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
abbrev input := (SelectedChainHomology.representation (Y := Y)).Evaluation
abbrev selectedRepresentation := SourceActionEvaluation.representation (Y := H (Y := Y)) encoding
end LittleFinitistic.SelectedRealization

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedWindow
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedWindow
open SelectedFixedDiagram SelectedRectification

/-- A common finite support window chosen from the fixed representatives alone. -/
structure Window where
  lo : ℤ
  hi : ℤ
  bound0 : ∀ n, n < lo ∨ hi < n → IsZero (D0.X n)
  bound1 : ∀ n, n < lo ∨ hi < n → IsZero (D1.X n)
  bound2 : ∀ n, n < lo ∨ hi < n → IsZero (D2.X n)

end LittleFinitistic.SelectedWindow

end

end OAI
end


