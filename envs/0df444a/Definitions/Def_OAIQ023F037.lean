-- Prove2me | Definitions.Def_OAIQ023F037
-- name    : OAIQ023F037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T19:48:22.091406+00:00
-- url     : https://prove2.me/theorems/355c3690-6bc4-4028-b189-868a1b7703c4
-- title:
--   Definitions bundle OAIQ023F037 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Localization_SourceOddDoubleEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Localization/SourceOddDoubleEvaluation.lean), [`Finitistic_Selected_SelectedChainHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedChainHomology.lean), [`Finitistic_Selected_SelectedRealization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedRealization.lean).
--
--   **Imports.** It imports the bundles `OAIQ023F034` and `OAIQ023F035` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ023F038`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F034
import Definitions.Def_OAIQ023F035

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceOddDoubleEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
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

theorem shifted_corner_square (e a : R) (he : e*e=e) (n : ℤ) :
    (completed (Y := Y) E).map ((OddDouble.formalShiftFunctor n).map (corner E e a he)) ≫
      (shiftedImageIso (Y := Y) E e he n).hom =
    (shiftedImageIso (Y := Y) E e he n).hom ≫ (imageCorner (k := k) (Y := Y) e a)⟦n⟧' := by
  have hn := (shiftIso (Y := Y) E n).hom.naturality (corner E e a he)
  have hm := congrArg (shiftFunctor (FiniteVectorDerived.{u,v} (k := k)) n).map
    (completed_corner_square (Y := Y) E e a he)
  simp only [Functor.map_comp] at hm
  exact compose_square _ _ _ _ _ hn hm

attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instHasFiniteBiproductsKaroubiQRelations
attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instHasBinaryBiproductsKaroubiQRelations
attribute [local instance] OAI.LittleFinitistic.SourceImageEvaluation.instPreservesBinaryBiproductsKaroubiQRelationsFiniteVectorDerivedCompleted
theorem oddDouble_corner_square (e a : R) (he : e*e=e) :
    (completed (Y := Y) E).map
      (biprod.map (corner E e a he) ((OddDouble.formalShiftFunctor 3).map (corner E e a he))) ≫
      (oddDoubleImageIso (Y := Y) E e he).hom =
    (oddDoubleImageIso (Y := Y) E e he).hom ≫
      biprod.map (imageCorner (k := k) (Y := Y) e a) ((imageCorner (k := k) (Y := Y) e a)⟦(3 : ℤ)⟧') := by
  exact BiprodEvaluationSquare.square (completed (Y := Y) E)
    (corner E e a he) ((OddDouble.formalShiftFunctor 3).map (corner E e a he))
    (summandImageIso (Y := Y) E e he) (shiftedImageIso (Y := Y) E e he 3)
    (imageCorner (k := k) (Y := Y) e a) ((imageCorner (k := k) (Y := Y) e a)⟦(3 : ℤ)⟧')
    (completed_corner_square E e a he) (shifted_corner_square E e a he 3)

end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedChainHomology
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
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

lemma D0_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((complex (Y := Y) fixed.D0).homology n) :=
  homology_zero _ SelectedNativeEvaluation.D0Iso n h0 hm
lemma D1_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((complex (Y := Y) fixed.D1).homology n) :=
  homology_zero _ SelectedNativeEvaluation.D1Iso n h0 hm
lemma D2_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((complex (Y := Y) fixed.D2).homology n) :=
  homology_zero _ SelectedNativeEvaluation.D2Iso n h0 hm

end LittleFinitistic.SelectedChainHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedRealization
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated
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
lemma source_zero (n : ℤ) (hn0 : n ≠ 0) (hn3 : n ≠ -3) (v : Fin 3) :
    IsZero ((SelectedTensor.source (input (Y := Y)) v).homology n) := by
  fin_cases v
  · exact SelectedChainHomology.D0_zero n hn0 hn3
  · exact SelectedChainHomology.D1_zero n hn0 hn3
  · exact SelectedChainHomology.D2_zero n hn0 hn3

end LittleFinitistic.SelectedRealization

end

end OAI
end


