-- Prove2me | Definitions.Def_OAIQ023F036
-- name    : OAIQ023F036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:00:39.961002+00:00
-- url     : https://prove2.me/theorems/eee95878-9883-4922-975f-6e74a92513aa
-- title:
--   Definitions bundle OAIQ023F036 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 103 declarations of OpenAI's Lean: 68 definitions, 20 instances and 15 theorems. The definitions and types are `OAI.LittleFinitistic.SelectedBarBimodule.comparisonX`, `OAI.LittleFinitistic.SelectedBarBimodule.leftEquiv`, `OAI.LittleFinitistic.SelectedBarBimodule.rightEquiv`, `OAI.LittleFinitistic.SelectedBarComparison.instHasDerivedCategoryModuleCatD`, `OAI.LittleFinitistic.SelectedBarComparison.native`, `OAI.LittleFinitistic.SelectedBarComparison.powerIso`, `OAI.LittleFinitistic.SelectedBarComparison.resolution`, `OAI.LittleFinitistic.SelectedBarPowers.comparison`, `OAI.LittleFinitistic.SelectedBarPowers.instHasDerivedCategoryModuleCatD`, `OAI.LittleFinitistic.SelectedBaseIterates.input`, `OAI.LittleFinitistic.SelectedBaseIterates.object`, `OAI.LittleFinitistic.SelectedCohomologyAssembly.iso`, `OAI.LittleFinitistic.SelectedCountCohomology.comparison`, `OAI.LittleFinitistic.SelectedCountCohomology.count`, `OAI.LittleFinitistic.SelectedCountCohomology.instHasDerivedCategoryModuleCatD`, `OAI.LittleFinitistic.SelectedCountExtinction.instHasDerivedCategoryModuleCatD`, `OAI.LittleFinitistic.SelectedFirstBlockFamily.derived`, `OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation`, `OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation`, `OAI.LittleFinitistic.SelectedFirstBlockFamily.instHasDerivedCategoryModuleCatD`, `OAI.LittleFinitistic.SelectedFirstBlockFamily.moduleIso`, `OAI.LittleFinitistic.SelectedFirstBlockFamily.stalkIso`, `OAI.LittleFinitistic.SelectedOrdinaryAlgebra.A`, `OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D`, `OAI.LittleFinitistic.SelectedOrdinaryAlgebra.X`, `OAI.LittleFinitistic.SelectedOrdinaryAlgebra.a`, `OAI.LittleFinitistic.SelectedOrdinaryAlgebra.augmentation`, `OAI.LittleFinitistic.SelectedOrdinaryAlgebra.b`, `OAI.LittleFinitistic.SelectedOrdinaryAlgebra.length`, `OAI.LittleFinitistic.SelectedOrdinaryDimension.bound`, `OAI.LittleFinitistic.SelectedOrdinaryModules.augmentationRing`, `OAI.LittleFinitistic.SelectedOrdinaryModules.firstProjection`, `OAI.LittleFinitistic.SelectedOrdinaryModules.module`, `OAI.LittleFinitistic.SelectedOrdinaryModules.testModule`, `OAI.LittleFinitistic.SelectedOrdinaryOrbit.barPower`, `OAI.LittleFinitistic.SelectedOrdinaryOrbit.evenIteration`, `OAI.LittleFinitistic.SelectedOrdinaryOrbit.first`, `OAI.LittleFinitistic.SelectedOrdinaryOrbit.firstIso`, `OAI.LittleFinitistic.SelectedOrdinaryOrbit.firstStalk`, `OAI.LittleFinitistic.SelectedOrdinaryOrbit.instHasDerivedCategoryModuleCatD` and 28 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Localization_SourceEvaluation`, `Finitistic_Selected_SelectedBarBimodule`, `Finitistic_Selected_SelectedBarComparison`, `Finitistic_Selected_SelectedBarPowers`, `Finitistic_Selected_SelectedBaseIterates`, `Finitistic_Selected_SelectedCohomologyAssembly`, `Finitistic_Selected_SelectedCohomologyVanishing`, `Finitistic_Selected_SelectedCountCohomology`, `Finitistic_Selected_SelectedCountExtinction`, `Finitistic_Selected_SelectedFirstBlockFamily`, `Finitistic_Selected_SelectedOrdinaryAlgebra`, `Finitistic_Selected_SelectedOrdinaryDimension`, `Finitistic_Selected_SelectedOrdinaryModules`, `Finitistic_Selected_SelectedOrdinaryOrbit`, `Finitistic_Selected_SelectedOrdinaryResolution`, `Finitistic_Selected_SelectedPDBarConsumer`, `Finitistic_Selected_SelectedPDConclusion`, `Finitistic_Selected_SelectedPDDetection`, `Finitistic_Selected_SelectedRealization`, `Finitistic_Selected_SelectedRectification`, `Finitistic_Selected_SelectedReferenceCohomology`, `Finitistic_Selected_SelectedShiftedRealization`, `Finitistic_Selected_SelectedTensor`, `Finitistic_Selected_SelectedTensorSplitting`, `Finitistic_Selected_SelectedWindow`.
--
--   **Imports.** It imports the bundles `OAIQ023F033` and `OAIQ023F034` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ023F038`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F033
import Definitions.Def_OAIQ023F034

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SourceImageEvaluation.instAdditiveKaroubiQRelationsFiniteVectorDerivedCompleted
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

instance instAdditiveKHomotopyCategoryIntModuleCatUpEvaluation : (evaluation X).Additive := by unfold evaluation; infer_instance
instance instIsTriangulatedKHomotopyCategoryIntModuleCatUpEvaluation : (evaluation X).IsTriangulated := by unfold evaluation; infer_instance

variable [FiniteDimensional k Y]
instance instIsTriangulatedQFiniteVectorHomotopyQuotientFinite : (quotientFinite X).IsTriangulated := by unfold quotientFinite; infer_instance

instance instIsTriangulatedQFiniteVectorDerivedDerived : (derived X).IsTriangulated := by unfold derived; infer_instance

end LittleFinitistic.SourceEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedRectification
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.SelectedRectification
open SelectedFixedDiagram ExternalTensor.Section4 RelationBasisCoefficients

def g (b : Fin (encoding.generators+1)) : D1 ⟶ D2 := F.map (SelectedChainDiagram.fixedChain.g b)
def relations (r : RelationIndex P) :
    Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D0 D1 D2 f g r) 0 :=
  UnderlyingRepresentatives.relationHomotopy P (encoding.generators+1) (encoding.generators+1)
    (Module.finrank ℂ (QuadraticEncoding.relationSpace P)) fixed.D0 fixed.D1 fixed.D2
    SelectedChainDiagram.fixedChain.f SelectedChainDiagram.fixedChain.g (basisCoefficient P)
    SelectedChainDiagram.fixedChain.homotopy r

/-- One explicit bimodule complex chosen before any evaluation module. -/
def bimodule : BiComplex ℂ (QuadraticEncoding.B P) :=
  InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D0 D1 D2 f g relations

end LittleFinitistic.SelectedRectification

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedWindow
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedWindow
open SelectedFixedDiagram SelectedRectification

instance instNonemptyWindow : Nonempty Window := by
  obtain ⟨l₀,h₀,b₀⟩ := UnderlyingRepresentatives.bounded P fixed.D0
  obtain ⟨l₁,h₁,b₁⟩ := UnderlyingRepresentatives.bounded P fixed.D1
  obtain ⟨l₂,h₂,b₂⟩ := UnderlyingRepresentatives.bounded P fixed.D2
  refine ⟨⟨min l₀ (min l₁ l₂), max h₀ (max h₁ h₂), ?_, ?_, ?_⟩⟩
  · intro n hn; apply b₀ n; omega
  · intro n hn; apply b₁ n; omega
  · intro n hn; apply b₂ n; omega

def window : Window := Classical.choice inferInstance
abbrev lo := window.lo
abbrev hi := window.hi

/-- Every term outside the fixed total's resulting support window is zero. -/
theorem bounded (n : ℤ) (hn : n < lo - 2 ∨ hi < n) : IsZero (bimodule.X n) :=
  InducedRectification.total_bounded (ConcreteQuadraticDiagram.quadratic P)
    D0 D1 D2 f g relations lo hi window.bound0 window.bound1 window.bound2 n hn

/-- The support choices retain the complete proved rectification certificate. -/
theorem verified : RectificationLemma.Verified P D0 D1 D2 f g relations lo hi :=
  RectificationLemma.rectification P D0 D1 D2 f g relations lo hi
    window.bound0 window.bound1 window.bound2
    (UnderlyingRepresentatives.projective P fixed.D0)
    (UnderlyingRepresentatives.projective P fixed.D1)
    (UnderlyingRepresentatives.projective P fixed.D2)
    (UnderlyingRepresentatives.finite P fixed.D0)
    (UnderlyingRepresentatives.finite P fixed.D1)
    (UnderlyingRepresentatives.finite P fixed.D2)
end LittleFinitistic.SelectedWindow

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryAlgebra
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
attribute [-simp] _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id
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

/-- A fixed support interval containing degree zero, chosen before any test module. -/
def a : ℤ := min (SelectedWindow.lo-2) 0
def b : ℤ := max SelectedWindow.hi 0
def length : ℕ := (b-a).toNat

theorem a_le_zero : a ≤ 0 := min_le_right _ _
theorem b_nonneg : 0 ≤ b := le_max_right _ _
theorem endpoints : a + (length : ℤ) = b := by
  have ha := a_le_zero
  have hb := b_nonneg
  dsimp [length]
  omega

theorem support (n : ℤ) (hn : n < a ∨ b < n) :
    IsZero (SelectedRectification.bimodule.X n) := by
  apply SelectedWindow.bounded n
  dsimp [a,b] at hn
  omega

instance term_finite (n : ℤ) :
    FiniteDimensional ℂ ((underlyingComplex (k := ℂ) SelectedRectification.bimodule).X n) :=
  SelectedWindow.verified.finite n
instance term_projective (n : ℤ) :
    Module.Projective (B P)ᵐᵒᵖ ((underlyingRightComplex SelectedRectification.bimodule).X n) := by
  let : Projective ((underlyingRightComplex SelectedRectification.bimodule).X n) :=
    SelectedWindow.verified.projective n
  exact ModuleCat.projective_of_module_projective _

/-- The actual finite-dimensional ordinary algebra and off-diagonal bimodule. -/
abbrev D := AlgebraD ℂ length (B P)
abbrev X := BimoduleX SelectedRectification.bimodule a length
instance D_finite : FiniteDimensional ℂ D := inferInstance

/-- The manuscript's one fixed square-zero algebra. No projective-dimension
conclusion is asserted here. -/
abbrev A := TrivSqZeroExt D X
abbrev augmentation : A →ₐ[ℂ] D := TrivSqZeroExt.fstHom ℂ D X

end LittleFinitistic.SelectedOrdinaryAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryResolution
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedOrdinaryResolution
open SelectedOrdinaryAlgebra

/-- The one fixed genuine D-bimodule resolution Q_X used by the source. -/
abbrev complex := OrdinarySimulation.XResolution.complex SelectedRectification.bimodule a length
abbrev target := OrdinarySimulation.XResolution.ordinaryXObject SelectedRectification.bimodule a length
abbrev augmentation := OrdinarySimulation.XResolution.augmentationToX
  SelectedRectification.bimodule a length

theorem augmentation_quasiIso : QuasiIso augmentation :=
  OrdinarySimulation.XResolution.augmentationToX_quasiIso SelectedRectification.bimodule a length

theorem right_projective (n : ℤ) : Module.Projective Dᵐᵒᵖ
    (BimoduleCoefficients ℂ D D (complex.X n)) :=
  OrdinarySimulation.XResolution.right_projective SelectedRectification.bimodule a length n

theorem bounded (n : ℤ) (hn : n < -(length : ℤ) ∨ 0 < n) : IsZero (complex.X n) :=
  OrdinarySimulation.XResolution.vanishes SelectedRectification.bimodule a length n hn

local instance instHasDerivedCategoryModuleCatD : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- Tensor via the actual bounded right-projective Q_X, with the left D-action retained. -/
abbrev derived := OrdinarySimulation.XResolution.derivedTensor SelectedRectification.bimodule a length
end LittleFinitistic.SelectedOrdinaryResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedBarBimodule
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedBarBimodule
open SelectedOrdinaryAlgebra

/-- The action presentation of X used by the generic native/bar comparison. -/
abbrev comparisonX := BimoduleBarComparison.Actions ℂ D SelectedOrdinaryResolution.target

/-- Recover exactly the original right action of the constructed ordinary X. -/
def rightEquiv : comparisonX ≃ₗ[Dᵐᵒᵖ] X :=
  RetainedBimodule.rightEquiv ℂ D D X

/-- The same identification preserves the original outside left D-action. -/
theorem left_action (d : D) (x : comparisonX) : rightEquiv (d • x) = d • rightEquiv x :=
  RetainedBimodule.rightEquiv_left ℂ D D X d x

def leftEquiv : comparisonX ≃ₗ[D] X where
  toFun := rightEquiv
  invFun := rightEquiv.symm
  left_inv := rightEquiv.left_inv
  right_inv := rightEquiv.right_inv
  map_add' := rightEquiv.map_add
  map_smul' := left_action

theorem right_action (d : Dᵐᵒᵖ) (x : comparisonX) :
    leftEquiv (d • x) = d • leftEquiv x := rightEquiv.map_smul d x
end LittleFinitistic.SelectedBarBimodule

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
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

/-- Evaluate the one fixed selecting bimodule, retaining its full left action. -/
abbrev complex := FullTensorRectification.tensor P D0 D1 D2 f g relations N
abbrev comparison (v : Fin 3) (n : ℤ) :=
  TensorCohomologyDiagram.comparison P D0 D1 D2 f g relations N v n

/-- Every cohomology comparison is invertible for the fixed selected representatives. -/
instance comparison_isIso (v : Fin 3) (n : ℤ) : IsIso (comparison N v n) := by
  obtain ⟨l₀,h₀,b₀⟩ := UnderlyingRepresentatives.bounded P fixed.D0
  obtain ⟨l₁,h₁,b₁⟩ := UnderlyingRepresentatives.bounded P fixed.D1
  obtain ⟨l₂,h₂,b₂⟩ := UnderlyingRepresentatives.bounded P fixed.D2
  let lo := min l₀ (min l₁ l₂)
  let hi := max h₀ (max h₁ h₂)
  refine TensorCohomologyDiagram.comparison_isIso P D0 D1 D2 f g relations N v n lo hi
    (fun n hn => b₀ n ?_) (fun n hn => b₁ n ?_) (fun n hn => b₂ n ?_)
    (UnderlyingRepresentatives.projective P fixed.D0)
    (UnderlyingRepresentatives.projective P fixed.D1)
    (UnderlyingRepresentatives.projective P fixed.D2)
  all_goals dsimp [lo,hi] at hn; omega

def comparisonIso (v : Fin 3) (n : ℤ) := asIso (comparison N v n)

end LittleFinitistic.SelectedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedCohomologyAssembly
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.SelectedCohomologyAssembly
open SelectedFixedDiagram SelectedRectification QuadraticEncoding

variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module (B P) N]
variable (n : ℤ) (R : ModuleCat (B P))
variable (E : ∀ v : Fin 3, (SelectedTensor.source N v).homology n ≅
  (LeftVertexHomology.vertex ℂ (B P) (ThreeVertexAlgebra.vertex (composition P) v)).obj R)

/-- Convert an identified evaluated-representative cohomology diagram into the
full cohomology B-module of the one fixed selecting tensor. Only the reference
diagram identification is an input; the tensor vertex comparisons are proved. -/
def iso
    (h01 : ∀ a,
      homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) N).mapHomologicalComplex (.up ℤ)).map (f a)) n ≫
        (E 1).hom = (E 0).hom ≫
        (LeftVertexHomology.arrow ℂ (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
          (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a)
          (CanonicalArrowCompatibility.arrow01_target P a)).app R)
    (h12 : ∀ b,
      homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) N).mapHomologicalComplex (.up ℤ)).map (g b)) n ≫
        (E 2).hom = (E 1).hom ≫
        (LeftVertexHomology.arrow ℂ (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
          (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b)
          (CanonicalArrowCompatibility.arrow12_target P b)).app R) :
    (SelectedTensor.complex N).homology n ≅ R :=
  VertexCategoricalAssembly.iso P _ R
    (fun v => (SelectedTensor.comparisonIso N v n).symm ≪≫ E v)
    (fun a => transfer_square _ _ _ (SelectedTensor.comparisonIso N 0 n)
      (SelectedTensor.comparisonIso N 1 n) (E 0) (E 1)
      (TensorCohomologyDiagram.arrow01_square P D0 D1 D2 f g relations N a n) (h01 a))
    (fun b => transfer_square _ _ _ (SelectedTensor.comparisonIso N 1 n)
      (SelectedTensor.comparisonIso N 2 n) (E 1) (E 2)
      (TensorCohomologyDiagram.arrow12_square P D0 D1 D2 f g relations N b n) (h12 b))
end LittleFinitistic.SelectedCohomologyAssembly

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedReferenceCohomology
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.SelectedReferenceCohomology
open SelectedFixedDiagram SelectedRectification QuadraticEncoding

variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module (B P) N]
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] (X : Representation P Y)
variable (n : ℤ) (E : ∀ v : Fin 3,
  (SelectedTensor.source N v).homology n ≅ ModuleCat.of ℂ Y)

/-- Identify the full tensor cohomology with the actual evaluation module from
three coordinate models and their generator actions. -/
def iso
    (h01 : ∀ a,
      homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) N).mapHomologicalComplex (.up ℤ)).map (f a)) n ≫
        (E 1).hom = (E 0).hom ≫ EvaluationVertexDiagram.action X a)
    (h12 : ∀ b,
      homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) N).mapHomologicalComplex (.up ℤ)).map (g b)) n ≫
        (E 2).hom = (E 1).hom ≫ EvaluationVertexDiagram.action X b) :
    (SelectedTensor.complex N).homology n ≅ EvaluationVertexDiagram.module X := by
  apply SelectedCohomologyAssembly.iso N n (EvaluationVertexDiagram.module X)
    (fun v => E v ≪≫ (EvaluationVertexDiagram.vertexIso X v).symm)
  · intro a
    exact transfer_to_vertices _ _ _ (E 0) (E 1)
      (EvaluationVertexDiagram.vertexIso X 0) (EvaluationVertexDiagram.vertexIso X 1)
      (h01 a) (EvaluationVertexDiagram.arrow01_square X a (CanonicalArrowCompatibility.arrow01_target P a))
  · intro b
    exact transfer_to_vertices _ _ _ (E 1) (E 2)
      (EvaluationVertexDiagram.vertexIso X 1) (EvaluationVertexDiagram.vertexIso X 2)
      (h12 b) (EvaluationVertexDiagram.arrow12_square X b (CanonicalArrowCompatibility.arrow12_target P b))
end LittleFinitistic.SelectedReferenceCohomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedCohomologyVanishing
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedCohomologyVanishing
open QuadraticEncoding

open SelectedFixedDiagram
variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module (B P) N]

/-- Vanishing on all three evaluated representatives gives actual cohomology
vanishing of the fixed selecting tensor as a B-module. -/
theorem cohomology_isZero (n : ℤ)
    (h : ∀ v : Fin 3, IsZero ((SelectedTensor.source N v).homology n)) :
    IsZero ((SelectedTensor.complex N).homology n) := by
  apply module_isZero P
  intro v
  exact (SelectedTensor.comparisonIso N v n).isZero_iff.mp (h v)
end LittleFinitistic.SelectedCohomologyVanishing

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTensorSplitting
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.SelectedTensorSplitting
open SelectedFixedDiagram QuadraticEncoding
variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module (B P) N]

/-- The actual derived object represented by the full B-valued fixed tensor complex. -/
abbrev object : DerivedCategory (ModuleCat (B P)) := DerivedCategory.Q.obj (SelectedTensor.complex N)

def homologyIso (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat (B P)) n).obj (object N) ≅
      (SelectedTensor.complex N).homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat (B P)) n).app (SelectedTensor.complex N)

/-- Support of the evaluated representative diagram implies actual derived
cohomological support of the full tensor object. -/
theorem twoDegrees
    (h : ∀ n : ℤ, n ≠ 0 → n ≠ -3 → ∀ v : Fin 3,
      IsZero ((SelectedTensor.source N v).homology n)) :
    DerivedTruncation.TwoDegrees (object N) := by
  intro n hn0 hn3
  exact (homologyIso N n).isZero_iff.mpr
    (SelectedCohomologyVanishing.cohomology_isZero N n (h n hn0 hn3))

/-- Apply the proved B-linear truncation splitting to the actual fixed tensor,
using full module cohomology models and source-diagram support. -/
def split (R : ModuleCat (B P))
    (h0 : (SelectedTensor.complex N).homology 0 ≅ R)
    (h3 : (SelectedTensor.complex N).homology (-3) ≅ R)
    (hz : ∀ n : ℤ, n ≠ 0 → n ≠ -3 → ∀ v : Fin 3,
      IsZero ((SelectedTensor.source N v).homology n)) :
    object N ≅ (DerivedCategory.singleFunctor (ModuleCat (B P)) 0).obj R ⊞
      ((DerivedCategory.singleFunctor (ModuleCat (B P)) 0).obj R)⟦(3 : ℤ)⟧ :=
  TwoDegreeFormality.splitIsoWithModels P (object N) (twoDegrees N hz) R R
    (homologyIso N 0 ≪≫ h0) (homologyIso N (-3) ≪≫ h3)
end LittleFinitistic.SelectedTensorSplitting

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedRealization
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
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
abbrev reference := EvaluationVertexDiagram.module (selectedRepresentation (Y := Y))

omit [FiniteDimensional ℂ Y] in
lemma selected_action (a : Fin (encoding.generators+1)) :
    EvaluationVertexDiagram.action (Y := H (Y := Y)) (selectedRepresentation (Y := Y)) a =
      HAction (Y := Y) (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [HAction_apply]
  refine Fin.cases ?_ (fun j => ?_) a
  · change x = (1 : SelectionRing) • x
    rw [one_smul]
  · rfl

end LittleFinitistic.SelectedRealization

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryModules
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedOrdinaryModules
open SelectedFixedDiagram QuadraticEncoding SelectedOrdinaryAlgebra
open FiniteSelectionFamily

abbrev firstProjection : D →+* B P := RingHom.fst _ _
abbrev augmentationRing : A →+* D := SelectedOrdinaryAlgebra.augmentation.toRingHom
instance instModuleDInflated (Y : S.{0}) : Module D (Inflated Y) := Module.compHom (Inflated Y) firstProjection
instance instModuleAInflated (Y : S.{0}) : Module A (Inflated Y) :=
  Module.compHom (Inflated Y) (firstProjection.comp augmentationRing)
instance instIsScalarTowerComplexDInflated (Y : S.{0}) : IsScalarTower ℂ D (Inflated Y) where
  smul_assoc c d x := by
    change (c • d.1) • x = c • (d.1 • x)
    exact smul_assoc c d.1 x
instance instIsScalarTowerComplexAInflated (Y : S.{0}) : IsScalarTower ℂ A (Inflated Y) where
  smul_assoc c a x := by
    change (c • a.fst.1) • x = c • (a.fst.1 • x)
    exact smul_assoc c a.fst.1 x

instance instFiniteAInflated (Y : S.{0}) : Module.Finite A (Inflated Y) :=
  Module.Finite.of_restrictScalars_finite ℂ A (Inflated Y)

abbrev module (Y : S.{0}) := ModuleCat.of A (Inflated Y)

/-- Actual finite-dimensional modules over the one fixed A; their projective
 dimensions are the remaining homological conclusion. -/
abbrev testModule (m : ℕ) [NeZero m] := module (test m)

end LittleFinitistic.SelectedOrdinaryModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedBaseIterates
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedBaseIterates
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

/-- The actual first-block D-module underlying the inflated A-module. -/
abbrev input (Y : FiniteSelectionFamily.S.{0}) := ModuleCat.of D (Inflated Y)

local instance instModuleComplexCarrierD_r281923_1 (N : ModuleCat.{0} D) : Module ℂ N := DerivedBar.BimoduleTensor.scalarModule ℂ D N
local instance instIsScalarTowerComplexDCarrier_r281923_1 (N : ModuleCat.{0} D) : IsScalarTower ℂ D N where
  smul_assoc c d n := by
    change (c • d) • n = (algebraMap ℂ D c) • (d • n)
    have hd : c • d = (algebraMap ℂ D c) * d := by
      exact Algebra.smul_def c d
    rw [hd, mul_smul]
instance input_finiteD (Y : FiniteSelectionFamily.S.{0}) : Module.Finite D (input Y) :=
  Module.Finite.of_restrictScalars_finite ℂ D (Inflated Y)

instance input_finite (Y : FiniteSelectionFamily.S.{0}) : FiniteDimensional ℂ (input Y) :=
  Module.Finite.trans D (input Y)

local instance instHasDerivedCategoryModuleCatD_r281923_1 : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)
/-- Genuine bar-derived iteration of the actual X over the actual D. -/
abbrev object (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :=
  DerivedBar.IterateSupport.object ℂ D X (input Y) r

end LittleFinitistic.SelectedBaseIterates

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedFirstBlockFamily
attribute [-instance] _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule
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
attribute [local instance] OAI.LittleFinitistic.SelectedFirstBlockFamily.instHasDerivedCategoryModuleCatBComplexP
local instance instHasDerivedCategoryModuleCatD : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- The actual exact inflation functor from B-modules to the first D-block. -/
abbrev inflation : ModuleCat.{0} (B P) ⥤ ModuleCat.{0} D := ModuleCat.restrictScalars SelectedOrdinaryModules.firstProjection
instance inflation_preservesFiniteLimits : PreservesFiniteLimits inflation := by
  have h : PreservesFiniteLimits inflation ∧ PreservesFiniteColimits inflation :=
    ((Functor.exact_tfae inflation).out (2-1) (4-1)).mp
      (RestrictionHomology.mapsExact SelectedOrdinaryModules.firstProjection)
  exact h.1
instance inflation_preservesFiniteColimits : PreservesFiniteColimits inflation := by
  have h : PreservesFiniteLimits inflation ∧ PreservesFiniteColimits inflation :=
    ((Functor.exact_tfae inflation).out (2-1) (4-1)).mp
      (RestrictionHomology.mapsExact SelectedOrdinaryModules.firstProjection)
  exact h.2
abbrev derivedInflation := inflation.mapDerivedCategory

instance derivedInflation_additive : derivedInflation.Additive := by
  rw [Localization.functor_additive_iff DerivedCategory.Qh
    (HomotopyCategory.subcategoryAcyclic (ModuleCat.{0} (B P))).trW]
  exact Functor.additive_of_iso inflation.mapDerivedCategoryFactorsh.symm

/-- This is the original selected input, with precisely its constructed D-action. -/
def moduleIso (Y : FiniteSelectionFamily.S.{0}) :
    inflation.obj (FiniteSelectionFamily.module Y) ≅ SelectedBaseIterates.input Y :=
  Iso.refl _

abbrev derived (Y : FiniteSelectionFamily.S.{0}) :=
  (DerivedCategory.singleFunctor (ModuleCat D) 0).obj (SelectedBaseIterates.input Y)

/-- Exact inflation on derived categories agrees with the selected first-block stalk. -/
def stalkIso (Y : FiniteSelectionFamily.S.{0}) :
    derivedInflation.obj (FiniteSelectionFamily.derived Y) ≅ derived Y :=
  (inflation.mapDerivedCategorySingleFunctor 0).app (FiniteSelectionFamily.module Y) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat D) 0).mapIso (moduleIso Y)

end LittleFinitistic.SelectedFirstBlockFamily

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedBarComparison
attribute [-instance] _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.SelectedBarComparison
open SelectedOrdinaryAlgebra SelectedBarBimodule
local instance instHasDerivedCategoryModuleCatD : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- The actual fixed resolution supplies every generic native/bar premise. -/
def resolution := BimoduleTotal.ofNonpositiveResolution
  SelectedOrdinaryResolution.complex SelectedOrdinaryResolution.target length
  SelectedOrdinaryResolution.augmentation SelectedOrdinaryResolution.augmentation_quasiIso
  (fun n => SelectedOrdinaryResolution.right_projective n) SelectedOrdinaryResolution.bounded

/-- The native finite-interval presentation of tensor by the actual Q_X. Its
comparison to the ordinary total presentation is proved separately. -/
abbrev native := resolution.data.derived

/-- Every actual native iterate on a stalk is the original-X bar-derived iterate. -/
def powerIso (N : ModuleCat.{0} D) (r : ℕ) :
    (native.obj^[r]) (DerivedCategory.Q.obj (BimoduleTotal.singleInput D N)) ≅
      DerivedBar.IterateSupport.object ℂ D X N r :=
  BimoduleTotal.nonpositiveResolutionPowerIso
    SelectedOrdinaryResolution.complex SelectedOrdinaryResolution.target length
    SelectedOrdinaryResolution.augmentation SelectedOrdinaryResolution.augmentation_quasiIso
    (fun n => SelectedOrdinaryResolution.right_projective n) SelectedOrdinaryResolution.bounded N r ≪≫
  (DerivedBar.integerDerivedIterateIndexedIso D ℂ comparisonX N r).symm ≪≫
  (DerivedBar.chainToIntegerDerived D).mapIso
    ((DerivedBar.BimoduleTensor.derivedIterateCongr ℂ D leftEquiv right_action r).app
      ((DerivedBar.chainQ D).obj ((ChainComplex.single₀ (ModuleCat D)).obj N)))
end LittleFinitistic.SelectedBarComparison

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedBarPowers
attribute [-instance] _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedBarPowers
open SelectedOrdinaryAlgebra SelectedBarComparison
local instance instHasDerivedCategoryModuleCatD : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- All powers on the exact selected first-block derived family are the original
bar-derived powers; every resolution, scalar, action and stalk bridge is discharged. -/
def comparison (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (native.obj^[r]) (SelectedFirstBlockFamily.derived Y) ≅ SelectedBaseIterates.object Y r :=
  (eqToIso (BimoduleTotal.nativeIterate_obj resolution r (SelectedFirstBlockFamily.derived Y))).symm ≪≫
  (BimoduleTotal.nativeIterate resolution r).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat D) 0).app (SelectedBaseIterates.input Y)) ≪≫
  eqToIso (BimoduleTotal.nativeIterate_obj resolution r
    (DerivedCategory.Q.obj (BimoduleTotal.singleInput D (SelectedBaseIterates.input Y)))) ≪≫
  powerIso (SelectedBaseIterates.input Y) r

end LittleFinitistic.SelectedBarPowers

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryDimension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedOrdinaryDimension
open SelectedOrdinaryAlgebra SelectedFixedDiagram

/-- A fixed numerical bound determined solely by the fixed selecting bimodule. -/
abbrev bound : ℕ := 3 * length + 2

end LittleFinitistic.SelectedOrdinaryDimension

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedCountCohomology
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedCountCohomology
open SelectedOrdinaryAlgebra SelectedBaseIterates
local instance instHasDerivedCategoryModuleCatD : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- The original summand with exactly r square-zero factors in the actual bar complex. -/
abbrev count (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :=
  DerivedBar.ParityBridge.countObject ℂ D X (input Y) r

/-- Its exact standard integer-shift identification with the genuine derived iterate. -/
def comparison (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (object Y r)⟦(r : ℤ)⟧ ≅ count Y r :=
  DerivedBar.ParityBridge.countObjectComparison ℂ D X (input Y) r

end LittleFinitistic.SelectedCountCohomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedCountExtinction
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedCountExtinction
open SelectedOrdinaryAlgebra SelectedBaseIterates SelectedCountCohomology
local instance instHasDerivedCategoryModuleCatD : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

end LittleFinitistic.SelectedCountExtinction

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedShiftedRealization
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instAddCommGroup _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instIsScalarTowerEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModule _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModuleEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instAddCommGroupInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteDimensionalComplexInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleComplexInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated
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

/-- The actual shifted selecting bimodule, with its full B actions. -/
abbrev shifted := SelectedRectification.bimodule⟦b⟧

def model : BimoduleTotal.BoundedProjective ℂ (B P) shifted where
  lower := -(length : ℤ)
  upper := 0
  bounded := OrdinarySimulation.shifted_support _ b length a endpoints support
  projective n := by
    exact SelectedOrdinaryAlgebra.term_projective (n+b)

abbrev G := model.derived

/-- Tensoring a selected stalk by the shifted fixed bimodule shifts the already
verified full B-linear tensor complex. -/
def comparison (Y : FiniteSelectionFamily.S.{0}) :
    G.obj (FiniteSelectionFamily.derived Y) ≅
      (SelectedTensorSplitting.object (FiniteSelectionFamily.representation Y).Evaluation)⟦b⟧ :=
  model.nativeSingleEvaluation (FiniteSelectionFamily.representation Y).Evaluation ≪≫
    DerivedCategory.Q.mapIso
      ((((BimoduleBalancedTensor.functor ℂ (B P)
        (FiniteSelectionFamily.representation Y).Evaluation).mapHomologicalComplex (.up ℤ)).commShiftIso b).app
          SelectedRectification.bimodule) ≪≫
    (DerivedCategory.Q.commShiftIso b).app _

end LittleFinitistic.SelectedShiftedRealization

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryOrbit
attribute [-instance] _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule
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
local instance instHasDerivedCategoryModuleCatD : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

attribute [local instance] OAI.LittleFinitistic.SelectedOrdinaryOrbit.instHasDerivedCategoryModuleCatBComplexP
abbrev first := BlockModule.derivedFirst (B P) ((B P) ⊗[ℂ] OrdinarySimulation.ChainAlgebra ℂ length)
abbrev ordinary := SelectedOrdinaryResolution.derived

/-- The source's first-block localization is the actual selected exact inflation. -/
def firstIso : first ≅ SelectedFirstBlockFamily.derivedInflation :=
  BlockModule.derivedFirstIso (B P) ((B P) ⊗[ℂ] OrdinarySimulation.ChainAlgebra ℂ length)

def firstStalk (Y : FiniteSelectionFamily.S.{0}) :
    first.obj (FiniteSelectionFamily.derived Y) ≅ SelectedFirstBlockFamily.derived Y :=
  firstIso.app _ ≪≫ SelectedFirstBlockFamily.stalkIso Y

local instance resolution_projective : ∀ n, Module.Projective Dᵐᵒᵖ
    (ComplexTensor.rightTerm ℂ D (BimoduleTotal.right ℂ D SelectedOrdinaryResolution.complex) n) :=
  fun n => SelectedOrdinaryResolution.right_projective n

/-- Both tensor presentations use the identical Q_X and signed finite total. -/
def nativeIso : ordinary ≅ SelectedBarComparison.native :=
  BimoduleTotalPresentation.boundedNonpositiveDerivedIso ℂ D SelectedOrdinaryResolution.complex
    SelectedBarComparison.resolution.data length rfl rfl

/-- The source's shifted P[b] tensor is the concrete selecting shifted model. -/
def shiftedIso : OrdinarySimulation.shiftedDerivedTensor SelectedRectification.bimodule b length ≅
    SelectedShiftedRealization.G :=
  BimoduleTotalPresentation.shiftedDerivedIso SelectedRectification.bimodule b length
    SelectedShiftedRealization.model rfl rfl

/-- Every ordinary iterate on the selected first-block stalk is the original bar iterate. -/
def barPower (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (ordinary.obj^[r]) (SelectedFirstBlockFamily.derived Y) ≅ SelectedBaseIterates.object Y r :=
  functorObjectIteration nativeIso r _ ≪≫ SelectedBarPowers.comparison Y r

/-- Exact Section 5 even-iteration formula, with both presentation distinctions discharged. -/
def evenIteration (Y : FiniteSelectionFamily.S.{0}) (j : ℕ) :
    SelectedBaseIterates.object Y (2*j) ≅
      first.obj ((SelectedShiftedRealization.G.obj^[j]) (FiniteSelectionFamily.derived Y)) :=
  (barPower Y (2*j)).symm ≪≫ mapObjectIteration ordinary (firstStalk Y).symm (2*j) ≪≫
    OrdinarySimulation.XResolution.derivedEvenIterate SelectedRectification.bimodule a length b
      endpoints support j (FiniteSelectionFamily.derived Y) ≪≫
    first.mapIso (functorObjectIteration shiftedIso j _)

end LittleFinitistic.SelectedOrdinaryOrbit

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedPDDetection
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDDetection
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

instance residueModuleK : Module ℂ (PDTensor.Residue (A := A)) := PDResidueScalar.moduleK ℂ A
end LittleFinitistic.SelectedPDDetection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedPDBarConsumer
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDDetection
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

/-- The literal two-sided bar over the one fixed square-zero algebra. -/
abbrev baseBar (Y : FiniteSelectionFamily.S.{0}) :=
  DerivedBar.twoSidedComplex ℂ A D (Inflated Y) augmentation

end LittleFinitistic.SelectedPDDetection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedPDConclusion
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDConclusion
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

local instance instHasDerivedCategoryModuleCatD_r281923_2 : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)
/-- The canonical base-change Tor is computed by the actual selected bar,
independently of which compatible field-scalar instance presents that bar. -/
def baseTorIso (Y : FiniteSelectionFamily.S.{0}) (n : ℕ) :
    ((DerivedBar.Balanced.tensorFunctor augmentation).leftDerived n).obj (module Y) ≅
      (SelectedPDDetection.baseBar Y).homology n :=
  DerivedBar.Balanced.tensorBarHomologyIso augmentation (Inflated Y) n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat D) (.down ℕ) n).mapIso
      (DerivedBar.tensorBarIso ℂ A D (Inflated Y) augmentation)

end LittleFinitistic.SelectedPDConclusion

end

end OAI
end


