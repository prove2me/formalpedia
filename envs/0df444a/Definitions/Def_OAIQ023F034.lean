-- Prove2me | Definitions.Def_OAIQ023F034
-- name    : OAIQ023F034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T19:43:13.582664+00:00
-- url     : https://prove2.me/theorems/9aef7863-c278-42a5-9bda-324688f84eaa
-- title:
--   Definitions bundle OAIQ023F034 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 2 definitions, 6 instances and 12 theorems. The definitions and types are `OAI.LittleFinitistic.SelectedOrdinaryModules.Inflated`, `OAI.LittleFinitistic.VertexCategoricalAssembly.iso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Localization_SourceEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Localization/SourceEvaluation.lean), [`Finitistic_Localization_TensorCohomologyDiagram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Localization/TensorCohomologyDiagram.lean), [`Finitistic_Rectification_FullTensorRectification`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/FullTensorRectification.lean), [`Finitistic_Rectification_RectificationLemma`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/RectificationLemma.lean), [`Finitistic_Rectification_ThirdVertex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/ThirdVertex.lean), [`Finitistic_Rectification_VertexCategoricalAssembly`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/VertexCategoricalAssembly.lean), [`Finitistic_Rectification_VertexHomotopyEquivalence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/VertexHomotopyEquivalence.lean), [`Finitistic_Selected_SelectedChainHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedChainHomology.lean), [`Finitistic_Selected_SelectedOrdinaryModules`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedOrdinaryModules.lean), [`Finitistic_Selected_SelectedTensorComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Selected/SelectedTensorComparison.lean).
--
--   **Imports.** It imports the bundles `OAIQ023F031` and `OAIQ023F032` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F036` and `OAIQ023F037`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F031
import Definitions.Def_OAIQ023F032

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

instance instCommShiftKHomotopyCategoryIntModuleCatUpEvaluation : (evaluation X).CommShift ℤ := by unfold evaluation; infer_instance
end LittleFinitistic.SourceEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ThirdVertex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceEvaluation.instCommShiftKHomotopyCategoryIntModuleCatUpEvaluation _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.ThirdVertex
open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)
local notation "s" => ConcreteQuadraticDiagram.quadratic P

theorem filtration_inclusion_quasiIso :
    QuasiIso ((vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H)) := by
  let S := Complex.source0 s D₀ D₁ D₂ f g H
  exact RectificationAcyclic.quasiIso_of_acyclic_quotient (S.map (vertexComplex P))
    (Complex.vertex_shortExact ((s).e₂)
      ((ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition P)).idem 2) S
      (Complex.source0_shortExact s D₀ D₁ D₂ f g H))
    (FinalGradedAcyclic.grade0_vertex2_acyclic P D₀ D₁ D₂ f g)

theorem iota_quasiIso : QuasiIso (iota P D₀ D₁ D₂ f g H) := by
  let := ThirdVertexFiltration.inclusion_quasiIso P D₀ D₁ D₂ f g
  let := filtration_inclusion_quasiIso P D₀ D₁ D₂ f g H
  let e : D₂ ≅ (vertexComplex P).obj ((columnComplex k (QuadraticEncoding.B P) (s).e₂).obj D₂) :=
    VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 2 D₂
  change QuasiIso (e.hom ≫ (vertexComplex P).map (Exactness.i2 s D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H))
  infer_instance

end LittleFinitistic.ThirdVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexHomotopyEquivalence
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.barBicomplex_projective _root_.OAI.DerivedBar.barTotal_projective _root_.OAI.DerivedBar.complex_projective _root_.OAI.DerivedBar.countComplex_projective _root_.OAI.DerivedBar.countSum_projective _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDMinimal.term_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceEvaluation.instCommShiftKHomotopyCategoryIntModuleCatUpEvaluation _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- All three original vertex insertions are quasi-isomorphisms. -/
theorem iota_quasiIso (v : Fin 3) : QuasiIso (iota P D₀ D₁ D₂ f g H v) := by
  fin_cases v
  · let := FirstVertex.iota_isIso P D₀ D₁ D₂ f g H
    change QuasiIso (FirstVertex.iota P D₀ D₁ D₂ f g H)
    infer_instance
  · exact SecondVertex.iota_quasiIso P D₀ D₁ D₂ f g H
  · exact ThirdVertex.iota_quasiIso P D₀ D₁ D₂ f g H

/-- The actual vertex insertions have chain-map inverses and both homotopies.
Only the boundedness and projectivity of the chosen chain representatives are inputs. -/
theorem homotopy_inverse (v : Fin 3) (lo hi : ℤ)
    (b₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (b₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (b₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n))
    (p₀ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₀.X n))
    (p₁ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₁.X n))
    (p₂ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₂.X n)) :
    ∃ j : target P D₀ D₁ D₂ f g H v ⟶ source P D₀ D₁ D₂ v,
      Nonempty (Homotopy (iota P D₀ D₁ D₂ f g H v ≫ j) (𝟙 _)) ∧
      Nonempty (Homotopy (j ≫ iota P D₀ D₁ D₂ f g H v) (𝟙 _)) := by
  have : (source P D₀ D₁ D₂ v).IsStrictlyLE hi := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    fin_cases v
    · exact b₀ n (Or.inr hn)
    · exact b₁ n (Or.inr hn)
    · exact b₂ n (Or.inr hn)
  have : (target P D₀ D₁ D₂ f g H v).IsStrictlyLE hi := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact VertexTotalProperties.total_bounded P D₀ D₁ D₂ f g H v lo hi b₀ b₁ b₂ n (Or.inr hn)
  have (n : ℤ) : Projective ((source P D₀ D₁ D₂ v).X n) := by
    fin_cases v
    · change Projective (D₀.X n)
      let := p₀ n
      exact ModuleCat.projective_of_categoryTheory_projective (D₀.X n)
    · change Projective (D₁.X n)
      let := p₁ n
      exact ModuleCat.projective_of_categoryTheory_projective (D₁.X n)
    · change Projective (D₂.X n)
      let := p₂ n
      exact ModuleCat.projective_of_categoryTheory_projective (D₂.X n)
  have (n : ℤ) : Projective ((target P D₀ D₁ D₂ f g H v).X n) :=
    VertexTotalProperties.total_projective P D₀ D₁ D₂ f g H v p₀ p₁ p₂ n
  let := iota_quasiIso P D₀ D₁ D₂ f g H v
  exact RectificationAcyclic.bounded_projective_homotopy_inverse
    (iota P D₀ D₁ D₂ f g H v) hi
end LittleFinitistic.VertexHomotopyEquivalence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FullTensorRectification
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorLinear _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceEvaluation.instCommShiftKHomotopyCategoryIntModuleCatUpEvaluation _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The equivalences retain the full left B-valued tensor target and the exact original maps. -/
theorem equivalence (v : Fin 3) (lo hi : ℤ)
    (b₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (b₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (b₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n))
    (p₀ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₀.X n))
    (p₁ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₁.X n))
    (p₂ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₂.X n)) :
    ∃ E : HomotopyEquiv (source P D₀ D₁ D₂ N v) (target P D₀ D₁ D₂ f g H N v),
      E.hom = iota P D₀ D₁ D₂ f g H N v := by
  obtain ⟨j,⟨h₁⟩,⟨h₂⟩⟩ := VertexHomotopyEquivalence.homotopy_inverse P D₀ D₁ D₂ f g H
    v lo hi b₀ b₁ b₂ p₀ p₁ p₂
  let E : HomotopyEquiv (VertexHomotopyEquivalence.source P D₀ D₁ D₂ v)
      (VertexHomotopyEquivalence.target P D₀ D₁ D₂ f g H v) :=
    ⟨VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H v,j,h₁,h₂⟩
  exact ⟨((BalancedTensor.tensorFunctor k (B P) N).mapHomotopyEquiv E).trans
    (HomotopyEquiv.ofIso (TensorArrowComparison.complexIso k (B P) N
      (ThreeVertexAlgebra.vertex (composition P) v)
      ((ThreeVertexAlgebra.directedSystem (composition P)).idem v)
      (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H))),rfl⟩

end LittleFinitistic.FullTensorRectification

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TensorCohomologyDiagram
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceEvaluation.instCommShiftKHomotopyCategoryIntModuleCatUpEvaluation _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The canonical cohomology comparison is invertible under the proved input hypotheses. -/
theorem comparison_isIso (v : Fin 3) (n lo hi : ℤ)
    (b₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (b₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (b₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n))
    (p₀ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₀.X n))
    (p₁ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₁.X n))
    (p₂ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₂.X n)) :
    IsIso (comparison P D₀ D₁ D₂ f g H N v n) := by
  obtain ⟨E,hE⟩ := FullTensorRectification.equivalence P D₀ D₁ D₂ f g H N
    v lo hi b₀ b₁ b₂ p₀ p₁ p₂
  have : IsIso (homologyMap (iota P D₀ D₁ D₂ f g H N v) n) := by
    rw [← hE]
    exact (E.toHomologyIso n).isIso_hom
  unfold comparison
  infer_instance

end LittleFinitistic.TensorCohomologyDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_RectificationLemma
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.additive _root_.OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.commShift _root_.OAI.LittleFinitistic.BimoduleTotal.derived_additive _root_.OAI.LittleFinitistic.BimoduleTotal.derived_commShift _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalFunctor_preservesZeroMorphisms _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceEvaluation.instCommShiftKHomotopyCategoryIntModuleCatUpEvaluation _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- Full rectification for arbitrary bounded finite projective input complexes,
using only the assigned relation homotopies. No conclusion about the constructed
P, its vertices, or its arrow homotopies is assumed. -/
theorem rectification (lo hi : ℤ)
    (b₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (b₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (b₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n))
    (p₀ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₀.X n))
    (p₁ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₁.X n))
    (p₂ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₂.X n))
    (f₀ : ∀ n, Module.Finite (B P)ᵐᵒᵖ (D₀.X n))
    (f₁ : ∀ n, Module.Finite (B P)ᵐᵒᵖ (D₁.X n))
    (f₂ : ∀ n, Module.Finite (B P)ᵐᵒᵖ (D₂.X n)) :
    Verified P D₀ D₁ D₂ f g H lo hi := by
  have := QuadraticEncoding.finiteDimensional P
  exact {
    bounded := InducedRectification.total_bounded _ _ _ _ _ _ _ lo hi b₀ b₁ b₂
    projective := InducedRectification.rightTotal_projective _ _ _ _ _ _ _ p₀ p₁ p₂
    finite := induced_total_finite _ _ _ _ _ _ _ f₀ f₁ f₂
    vertices := fun v => VertexHomotopyEquivalence.homotopy_inverse P D₀ D₁ D₂ f g H
      v lo hi b₀ b₁ b₂ p₀ p₁ p₂
    arrows01 := fun a => ⟨CanonicalArrowCompatibility.compatibility01 P D₀ D₁ D₂ f g H a⟩
    arrows12 := fun b => ⟨CanonicalArrowCompatibility.compatibility12 P D₀ D₁ D₂ f g H b⟩ }
end LittleFinitistic.RectificationLemma

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexCategoricalAssembly
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instAddCommGroupEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instFiniteDimensionalEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instModuleEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceEvaluation.instCommShiftKHomotopyCategoryIntModuleCatUpEvaluation _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.VertexCategoricalAssembly
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (M N : ModuleCat.{u} (B P))
variable (E : ∀ i : Fin 3,
  (LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj M ≅
    (LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj N)

/-- Compatible categorical vertex isomorphisms determine a full B-module isomorphism.
The hypotheses are exactly the two finite arrow squares; length-two actions follow. -/
def iso
    (h01 : ∀ a,
      (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
        (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a)
        (CanonicalArrowCompatibility.arrow01_target P a)).app M ≫ (E 1).hom =
      (E 0).hom ≫ (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
        (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a)
        (CanonicalArrowCompatibility.arrow01_target P a)).app N)
    (h12 : ∀ b,
      (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
        (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b)
        (CanonicalArrowCompatibility.arrow12_target P b)).app M ≫ (E 2).hom =
      (E 1).hom ≫ (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
        (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b)
        (CanonicalArrowCompatibility.arrow12_target P b)).app N) : M ≅ N := by
  let e := EncodingModuleAssembly.equiv P (vertexEquiv P M N E)
    (fun a x => ?_) (fun b x => ?_)
  · exact e.toModuleIso
  · apply Subtype.ext
    have hh := congrArg (fun f => ModuleCat.Hom.hom f
      ((LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) 0) M).symm x)) (h01 a)
    have hh' := congrArg Subtype.val hh
    exact hh'
  · apply Subtype.ext
    have hh := congrArg (fun f => ModuleCat.Hom.hom f
      ((LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) 1) M).symm x)) (h12 b)
    have hh' := congrArg Subtype.val hh
    exact hh'
end LittleFinitistic.VertexCategoricalAssembly

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTensorComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
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

lemma map_comparison {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E)
    (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) :
    (HomotopyCategory.quotient _ _).map (tensorMap X f) ≫ (finiteIso X E).hom =
      (finiteIso X D).hom ≫ (inclusion k).map ((SourceEvaluation.finite X).map a) := by
  dsimp only [finiteIso,Iso.refl_hom]
  erw [Category.comp_id,Category.id_comp]
  change _ = ((BalancedTensor.tensorFunctor k (B P) X.Evaluation).mapHomotopyCategory (.up ℤ)).map
    (((UnderlyingRepresentatives.forget P).mapHomotopyCategory (.up ℤ)).map a.hom)
  erw [← ha,Functor.mapHomotopyCategory_map,Functor.mapHomotopyCategory_map]
end LittleFinitistic.SelectedTensorComparison

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedChainHomology
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite
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

lemma derived_map {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E) (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) :
    DerivedCategory.Q.map (tensorMap (representation (Y := Y)) f) ≫
      (derivedIso (Y := Y) E).hom =
        (derivedIso (Y := Y) D).hom ≫ I.map ((source (Y := Y)).map a) := by
  have h := congrArg DerivedCategory.Qh.map (map_comparison (representation (Y := Y)) f a ha)
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.quotientCompQhIso C).inv.naturality
    (tensorMap (representation (Y := Y)) f)
  exact DiagramEvaluationSquares.compose _ _ _
    ((DerivedCategory.quotientCompQhIso C).symm.app (complex (Y := Y) D))
    ((DerivedCategory.quotientCompQhIso C).symm.app (complex (Y := Y) E))
    (DerivedCategory.Qh.mapIso (finiteIso (representation (Y := Y)) D))
    (DerivedCategory.Qh.mapIso (finiteIso (representation (Y := Y)) E)) hn h

lemma comparison_map {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E) (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) (n : ℤ) :
    HomologicalComplex.homologyMap (tensorMap (representation (Y := Y)) f) n ≫
      (comparison (Y := Y) E n).hom =
        (comparison (Y := Y) D n).hom ≫ (cohomology n).map ((source (Y := Y)).map a) := by
  have h := congrArg (DerivedCategory.homologyFunctor C n).map (derived_map (Y := Y) f a ha)
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.homologyFunctorFactors C n).inv.naturality
    (tensorMap (representation (Y := Y)) f)
  exact DiagramEvaluationSquares.compose _ _ _
    ((DerivedCategory.homologyFunctorFactors C n).symm.app (complex (Y := Y) D))
    ((DerivedCategory.homologyFunctorFactors C n).symm.app (complex (Y := Y) E))
    ((DerivedCategory.homologyFunctor C n).mapIso (derivedIso (Y := Y) D))
    ((DerivedCategory.homologyFunctor C n).mapIso (derivedIso (Y := Y) E)) hn h

lemma homology_zero (D : SourceVerdier.K P)
    (e : (source (Y := Y)).obj D ≅ target (Y := Y))
    (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) : IsZero ((complex (Y := Y) D).homology n) :=
  (comparison D n ≪≫ (cohomology n).mapIso e).isZero_iff.mpr (target_zero n h0 hm)

lemma homology_arrow {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E) (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom)
    (eD : (source (Y := Y)).obj D ≅ target (Y := Y))
    (eE : (source (Y := Y)).obj E ≅ target (Y := Y)) (r : SelectionRing)
    (hs : (source (Y := Y)).map a ≫ eE.hom = eD.hom ≫ targetAction (Y := Y) r)
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (representation (Y := Y)) f) n ≫
      (homologyIso E eE n hn).hom =
        (homologyIso D eD n hn).hom ≫ HAction (Y := Y) r := by
  have h := congrArg (cohomology n).map hs
  simp only [Functor.map_comp] at h
  exact DiagramEvaluationSquares.compose _ _ _
    (comparison D n) (comparison E n)
    ((cohomology n).mapIso eD ≪≫ modelIso n hn)
    ((cohomology n).mapIso eE ≪≫ modelIso n hn)
    (comparison_map f a ha n)
    (DiagramEvaluationSquares.compose _ _ _ ((cohomology n).mapIso eD)
      ((cohomology n).mapIso eE) (modelIso n hn) (modelIso n hn) h (model_action n hn r))

end LittleFinitistic.SelectedChainHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryModules
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
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

/-- The source module M(Y), supported on the first D-block and inflated to A. -/
def Inflated (Y : S.{0}) := (representation Y).Evaluation
instance instAddCommGroupInflated (Y : S.{0}) : AddCommGroup (Inflated Y) :=
  inferInstanceAs (AddCommGroup (representation Y).Evaluation)
instance instModuleComplexInflated (Y : S.{0}) : Module ℂ (Inflated Y) :=
  inferInstanceAs (Module ℂ (representation Y).Evaluation)
instance instModuleBComplexPInflated (Y : S.{0}) : Module (B P) (Inflated Y) :=
  inferInstanceAs (Module (B P) (representation Y).Evaluation)
instance instIsScalarTowerComplexBPInflated (Y : S.{0}) : IsScalarTower ℂ (B P) (Inflated Y) :=
  inferInstanceAs (IsScalarTower ℂ (B P) (representation Y).Evaluation)

instance instFiniteDimensionalComplexInflated (Y : S.{0}) : FiniteDimensional ℂ (Inflated Y) :=
  inferInstanceAs (FiniteDimensional ℂ (representation Y).Evaluation)

end LittleFinitistic.SelectedOrdinaryModules

end

end OAI
end


