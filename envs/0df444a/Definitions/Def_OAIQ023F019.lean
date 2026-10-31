-- Prove2me | Definitions.Def_OAIQ023F019
-- name    : OAIQ023F019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T16:12:18.983745+00:00
-- url     : https://prove2.me/theorems/56004f57-a867-45a3-8c5e-0ed3b1690f8a
-- title:
--   Definitions bundle OAIQ023F019 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 102 declarations of OpenAI's Lean: 34 definitions, 22 instances and 46 theorems. The definitions and types are `OAI.LittleFinitistic.BimoduleTotal.columnFunctor`, `OAI.LittleFinitistic.BimoduleTotalPresentation.termEquiv`, `OAI.LittleFinitistic.BimoduleTotalPresentation.totalTermEquiv`, `OAI.LittleFinitistic.BimoduleVertex.diagonalEquiv`, `OAI.LittleFinitistic.CornerPathTransport.coordinateIso`, `OAI.LittleFinitistic.CornerTensor.diagonalColumnEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.AlgebraD`, `OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTermEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient`, `OAI.LittleFinitistic.OrdinarySimulation.Compression.vertexEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.Compression.vertexInsert`, `OAI.LittleFinitistic.OrdinarySimulation.Compression.vertexSpace`, `OAI.LittleFinitistic.OrdinarySimulation.FirstBlockTensor.equivalence`, `OAI.LittleFinitistic.OrdinarySimulation.FirstBlockTensor.forward`, `OAI.LittleFinitistic.OrdinarySimulation.FirstBlockTensor.inverse`, `OAI.LittleFinitistic.OrdinarySimulation.OrdinaryTerms.action`, `OAI.LittleFinitistic.OrdinarySimulation.OrdinaryTerms.module`, `OAI.LittleFinitistic.OrdinarySimulation.SecondBlockTensor.equivalence`, `OAI.LittleFinitistic.OrdinarySimulation.cochainModule`, `OAI.LittleFinitistic.SelectedChainHomology.modelIso`, `OAI.LittleFinitistic.SelectedDiagramEvaluation.target`, `OAI.LittleFinitistic.SelectedDiagramEvaluation.targetAction`, `OAI.LittleFinitistic.SelectedNativeEvaluation.target`, `OAI.LittleFinitistic.SelectedNativeEvaluation.targetAction`, `OAI.LittleFinitistic.SelectedNativeEvaluation.targetIso`, `OAI.LittleFinitistic.SelectedTargetHomology.shiftedHomologyIso`, `OAI.LittleFinitistic.SelectedTargetHomology.shiftedIso`, `OAI.LittleFinitistic.SelectedTargetHomology.targetH0`, `OAI.LittleFinitistic.SelectedTargetHomology.targetHm3`, `OAI.LittleFinitistic.SingleBimoduleTensor.selectedTermEquiv`, `OAI.LittleFinitistic.SingleBimoduleTensor.termEquivAt`, `OAI.LittleFinitistic.VertexColumnComplex.diagonalComplexIso`, `OAI.LittleFinitistic.VertexColumnComplex.diagonalNatIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bimodule_BimoduleInputFunctor`, `Finitistic_Bimodule_BimoduleSingleTerms`, `Finitistic_Bimodule_BimoduleTotalPresentation`, `Finitistic_Bimodule_BimoduleVertex`, `Finitistic_Localization_FiniteDerivedEvaluation`, `Finitistic_Ordinary_OrdinaryBimodule`, `Finitistic_Ordinary_OrdinaryBlockTensorTerms`, `Finitistic_Ordinary_OrdinaryChainAlgebra`, `Finitistic_Ordinary_OrdinaryChainDirected`, `Finitistic_Ordinary_OrdinaryCochain`, `Finitistic_Ordinary_OrdinaryComplexAction`, `Finitistic_Ordinary_OrdinaryCompression`, `Finitistic_Ordinary_OrdinaryFirstBlockTensor`, `Finitistic_Ordinary_OrdinaryFirstBlockTotal`, `Finitistic_Ordinary_OrdinarySecondBlockTensor`, `Finitistic_Ordinary_OrdinaryShiftDerivedTensor`, `Finitistic_Ordinary_OrdinarySingleTensorTerms`, `Finitistic_Ordinary_OrdinaryTensorIdealActions`, `Finitistic_Ordinary_OrdinaryVertexCompression`, `Finitistic_Rectification_CornerPathTransport`, `Finitistic_Rectification_CornerTensor`, `Finitistic_Rectification_VertexColumnComplex`, `Finitistic_Rectification_VertexColumnModels`, `Finitistic_Rectification_VertexFunctor`, `Finitistic_Rectification_VertexTotalProperties`, `Finitistic_Selected_SelectedChainHomology`, `Finitistic_Selected_SelectedDiagramEvaluation`, `Finitistic_Selected_SelectedNativeAction`, `Finitistic_Selected_SelectedNativeEvaluation`, `Finitistic_Selected_SelectedTargetHomology`.
--
--   **Imports.** It imports the bundles `OAIQ023F011`, `OAIQ023F012`, `OAIQ023F013`, `OAIQ023F014` and `OAIQ023F015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F022`, `OAIQ023F023` and `OAIQ023F024`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F011
import Definitions.Def_OAIQ023F012
import Definitions.Def_OAIQ023F013
import Definitions.Def_OAIQ023F014
import Definitions.Def_OAIQ023F015

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct

namespace LittleFinitistic.CornerTensor
open ThreeVertexAlgebra CornerSpaces CornerProjection TensorProjection
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule
universe u v
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
variable (N : Type v) [AddCommGroup N] [Module k N]
  [Module (ThreeVertexAlgebra μ)ᵐᵒᵖ N] [IsScalarTower k (ThreeVertexAlgebra μ)ᵐᵒᵖ N]

/-- The diagonal vertex component of its own induced column is exactly N. -/
def diagonalColumnEquiv (i : Fin 3) :
    TensorProjection.fixed (B := ThreeVertexAlgebra μ) (N := N) (projection μ i i)
      ≃ₗ[(ThreeVertexAlgebra μ)ᵐᵒᵖ] N :=
  (cornerTensorEquiv μ N i i).symm.trans
    ((rightCongr (B := ThreeVertexAlgebra μ) (N := N) (diagonalEquiv μ i)).trans
      (scalarTensorEquiv μ N))
end LittleFinitistic.CornerTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.VertexFunctor
universe u
variable {A B : Type u} [Ring A] [Ring B]
variable (β : B →+* A) (e : A) (he : e*e=e) (hc : ∀ b, e*β b=β b*e)

include he in
/-- Vertex components of right-projective modules are right-projective. -/
theorem projective (M : ModuleCat.{u} A) [Module.Projective B (restricted β M)] :
    Module.Projective B (fixed β e hc M) := by
  exact Module.Projective.of_split (inclusion β e hc M) (projection β e he hc M)
    (projection_inclusion β e he hc M)

end LittleFinitistic.VertexFunctor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleVertex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.biBinaryBiproducts _root_.OAI.ExternalTensor.Section4.biFiniteBiproducts _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleVertex

universe u
variable {k : Type u} [Field k]
variable {V W U : Type u} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
local notation "T" => ThreeVertexAlgebra μ
variable (N : ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ)
attribute [local instance] ExternalTensor.Section4.rightModuleK
  ExternalTensor.rightModule ExternalTensor.bimodule

/-- A column's own vertex is its original right module, with no replacement action. -/
def diagonalEquiv (i : Fin 3) :
    (functor k T (ThreeVertexAlgebra.vertex μ i)).obj
      ((ExternalTensor.Section4.columnFunctor k T
        (ThreeVertexAlgebra.vertex μ i)).obj N) ≃ₗ[Tᵐᵒᵖ] N :=
  (columnFixedEquiv μ N i i).trans (CornerTensor.diagonalColumnEquiv μ N i)
end LittleFinitistic.BimoduleVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexColumnModels
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.biBinaryBiproducts _root_.OAI.ExternalTensor.Section4.biFiniteBiproducts _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.LittleFinitistic.TensorComplex.mapRight_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.VertexColumnModels
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
variable (N : ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ)
local notation "T" => ThreeVertexAlgebra μ
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule

/-- Vertices below the directed support have zero actual column component. -/
theorem reverse_zero (i j : Fin 3) (hij : i < j) :
    Subsingleton (BimoduleVertex.columnFixed μ N i j) := by
  have hc : Subsingleton (CornerSpaces.corner μ i j) :=
    ⟨fun x y => (CornerSpaces.corner_zero_of_lt μ i j hij x).trans
      (CornerSpaces.corner_zero_of_lt μ i j hij y).symm⟩
  let := hc
  have ht : ∀ x : CornerSpaces.corner μ i j ⊗[k] N, x = 0 := by
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul x n => simp [Subsingleton.elim x 0]
    | add x y hx hy => simp [hx,hy]
  refine ⟨fun x y => (cornerEquiv μ N i j).injective ?_⟩
  exact (ht _).trans (ht _).symm

/-- The inverse diagonal equivalence is the manuscript's original insertion e_i tensor n. -/
theorem diagonal_symm_val (i : Fin 3) (n : N) :
    ((BimoduleVertex.diagonalEquiv μ N i).symm n).val =
      ExternalTensor.columnInclusion k T N (ThreeVertexAlgebra.vertex μ i) n := by
  change (⟨(1 : k) • ThreeVertexAlgebra.vertex μ i, _⟩ :
    ExternalTensor.leftIdeal T (ThreeVertexAlgebra.vertex μ i)) ⊗ₜ[k] n =
      ExternalTensor.generator T (ThreeVertexAlgebra.vertex μ i) ⊗ₜ[k] n
  congr 1
  apply Subtype.ext
  exact one_smul k _

end LittleFinitistic.VertexColumnModels

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexColumnComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.biBinaryBiproducts _root_.OAI.ExternalTensor.Section4.biFiniteBiproducts _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.VertexColumnComplex
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
local notation "T" => ThreeVertexAlgebra μ
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule

/-- The diagonal insertion is natural in the original right module. -/
def diagonalNatIso (i : Fin 3) : 𝟭 (ModuleCat.{u} Tᵐᵒᵖ) ≅ vertexColumn μ i i :=
  NatIso.ofComponents (fun N => (BimoduleVertex.diagonalEquiv μ N i).symm.toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro n
    apply Subtype.ext
    change ((BimoduleVertex.diagonalEquiv μ N i).symm (f.hom n)).val =
      ExternalTensor.columnMap k (ThreeVertexAlgebra.vertex μ i) f.hom
        (((BimoduleVertex.diagonalEquiv μ M i).symm n).val)
    rw [VertexColumnModels.diagonal_symm_val,VertexColumnModels.diagonal_symm_val]
    rfl)

/-- On actual complexes, the diagonal vertex is the original complex via its specified insertion. -/
def diagonalComplexIso (i : Fin 3) (D : CochainComplex (ModuleCat.{u} Tᵐᵒᵖ) ℤ) :
    D ≅ ((vertexColumn μ i i).mapHomologicalComplex (.up ℤ)).obj D :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (diagonalNatIso μ i).app (D.X n))
    (fun n m _ => ((diagonalNatIso μ i).hom.naturality (D.d n m)).symm)

/-- Every term of a reverse vertex column is zero, hence the actual complex is zero. -/
theorem reverse_isZero (i j : Fin 3) (hij : i < j)
    (D : CochainComplex (ModuleCat.{u} Tᵐᵒᵖ) ℤ) :
    IsZero (((vertexColumn μ i j).mapHomologicalComplex (.up ℤ)).obj D) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (VertexColumnModels.reverse_zero μ (D.X n) i j hij).elim _ _
end LittleFinitistic.VertexColumnComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerPathTransport
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.linear _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.CornerPathTransport
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
variable (D : CochainComplex (ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ) ℤ)
local notation "T" => ThreeVertexAlgebra μ

def coordinateIso (v i : Fin 3) {M : Type u} [AddCommGroup M] [Module k M]
    (ξ : CornerSpaces.corner μ v i ≃ₗ[k] M) :
    (AdjacentArrowSum.vertexComplex μ v).obj ((ExternalTensor.Section4.columnComplex k T
      (ThreeVertexAlgebra.vertex μ i)).obj D) ≅
      (TensorComplex.tensorFunctor (k := k) D).obj (ModuleCat.of k M) :=
  (CornerColumnComplex.complexIso μ v i D).symm ≪≫
    (TensorComplex.tensorFunctor (k := k) D).mapIso ξ.toModuleIso

/-- Coordinate transport preserves each actual path map, before taking any finite sum. -/
theorem path_square (v i j : Fin 3) {M N : Type u}
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (ξ : CornerSpaces.corner μ v j ≃ₗ[k] M)
    (η : CornerSpaces.corner μ v i ≃ₗ[k] N)
    (a : T) (ha : a * ThreeVertexAlgebra.vertex μ i = a)
    (f : M →ₗ[k] N)
    (hc : ∀ x, η (CornerColumnPaths.cornerMap μ v i j a ha x) = f (ξ x)) :
    (coordinateIso μ D v j ξ).hom ≫ (TensorComplex.tensorFunctor (k := k) D).map
      (ModuleCat.ofHom f) =
    (AdjacentArrowSum.vertexComplex μ v).map
      (ExternalTensor.Section4.path k T (ThreeVertexAlgebra.vertex μ i)
        (ThreeVertexAlgebra.vertex μ j) a ha D) ≫ (coordinateIso μ D v i η).hom := by
  let F := TensorComplex.tensorFunctor (k := k) D
  have hm : ModuleCat.ofHom ξ.toLinearMap ≫ ModuleCat.ofHom f =
      ModuleCat.ofHom (CornerColumnPaths.cornerMap μ v i j a ha) ≫
        ModuleCat.ofHom η.toLinearMap := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun x => (hc x).symm)
  have hF := congrArg F.map hm
  simp only [Functor.map_comp] at hF
  apply (cancel_epi (CornerColumnComplex.complexIso μ v j D).hom).1
  calc
    _ = F.map (ModuleCat.ofHom ξ.toLinearMap) ≫ F.map (ModuleCat.ofHom f) := by
      change (CornerColumnComplex.complexIso μ v j D).hom ≫
        ((CornerColumnComplex.complexIso μ v j D).inv ≫
          F.map (ModuleCat.ofHom ξ.toLinearMap)) ≫ F.map (ModuleCat.ofHom f) = _
      erw [Category.assoc]
      exact (CornerColumnComplex.complexIso μ v j D).hom_inv_id_assoc _
    _ = F.map (ModuleCat.ofHom (CornerColumnPaths.cornerMap μ v i j a ha)) ≫
        F.map (ModuleCat.ofHom η.toLinearMap) := hF
    _ = (F.map (ModuleCat.ofHom
          (CornerColumnPaths.cornerMap μ v i j a ha)) ≫
        (CornerColumnComplex.complexIso μ v i D).hom) ≫
          (coordinateIso μ D v i η).hom := by
      simp [coordinateIso,F,TensorComplex.tensorFunctor]
      show _ = (_ ≫ (CornerColumnComplex.complexIso μ v i D).hom) ≫
        ((CornerColumnComplex.complexIso μ v i D).inv ≫ _)
      rw [Category.assoc]
      erw [Iso.hom_inv_id_assoc]
      rfl
    _ = _ := by
      erw [CornerColumnPaths.path_naturality]
      exact Category.assoc _ _ _
end LittleFinitistic.CornerPathTransport

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryChainAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k : Type u) [Field k] (l : ℕ)

namespace ChainAlgebra

@[simp] theorem arrow_mul_arrow (i j : Fin l) :
    arrow k l i * arrow k l j = 0 := by
  change mul k l (arrow k l i) (arrow k l j) = 0
  apply Prod.ext <;> funext a <;> simp [mul, arrow, zero_eq]

@[simp] theorem vertex_target_arrow (i : Fin l) :
    vertex k l i.succ * arrow k l i = arrow k l i := by
  apply Prod.ext <;> funext j
  · change (Pi.single i.succ 1 : Fin (l+1) → k) j * 0 = 0
    simp
  · change (Pi.single i.succ 1 : _ → k) j.succ * (Pi.single i 1 : _ → k) j + 0 * 0 = (Pi.single i 1 : _ → k) j
    by_cases h : j = i <;> simp [h, Fin.succ_inj]

@[simp] theorem arrow_vertex_source (i : Fin l) :
    arrow k l i * vertex k l i.castSucc = arrow k l i := by
  apply Prod.ext <;> funext j
  · change (0:k) * (Pi.single i.castSucc 1 : Fin (l+1) → k) j = 0
    simp
  · change 0 * 0 + (Pi.single i 1 : _ → k) j * (Pi.single i.castSucc 1 : _ → k) j.castSucc = (Pi.single i 1 : _ → k) j
    by_cases h : j = i <;> simp [h, Fin.castSucc_inj]

end ChainAlgebra

variable (B : Type u) [Ring B] [Algebra k B]
/-- The actual ordinary algebra D of Section 5. -/
abbrev AlgebraD := B × (B ⊗[k] ChainAlgebra k l)
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorIdealActions
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.IdempotentTensor.leftMultiply_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorIdeal
universe u
variable {k B C : Type u} [Field k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]
variable (e : C)

instance leftModule : Module B (IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e)) :=
  Module.compHom _ (leftAction (k := k) (B := B) e).toRingHom

instance towerLeft : IsScalarTower k B (IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e)) where
  smul_assoc r b x := by
    change leftAction e (r • b) x = r • leftAction e b x
    rw [map_smul]
    rfl

instance commute : SMulCommClass B (B ⊗[k] C)ᵐᵒᵖ
    (IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e)) where
  smul_comm b r x := (leftAction e b).map_smul r x

@[simp] theorem left_smul_value (b : B)
    (x : IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e)) :
    (b • x).val = coefficient b * x.val := rfl
end LittleFinitistic.OrdinarySimulation.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryComplexAction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {k : Type u} [Field k] {l : ℕ}
namespace ChainAlgebra
/-- The coefficient of the unique possible arrow from j to i. -/
def coefficient (x : ChainAlgebra k l) (i j : Fin (l+1)) : k :=
  if h : j.val < l then if i.val = j.val+1 then x.2 ⟨j.val,h⟩ else 0 else 0

@[simp] theorem coefficient_mul (x y : ChainAlgebra k l) (i j : Fin (l+1)) :
    coefficient (x*y) i j = x.1 i * coefficient y i j + coefficient x i j * y.1 j := by
  unfold coefficient
  split
  next h =>
    split
    next hij =>
      have hi : i = (⟨j.val,h⟩ : Fin l).succ := Fin.ext hij
      have hj : j = (⟨j.val,h⟩ : Fin l).castSucc := rfl
      rw [mul_radical, hi]
      rfl
    next h => simp
  next h => simp

@[simp] theorem coefficient_one (i j : Fin (l+1)) :
    coefficient (1 : ChainAlgebra k l) i j = 0 := by
  unfold coefficient
  have hz (j : Fin l) : (1 : ChainAlgebra k l).2 j = 0 := rfl
  split <;> simp [hz]

@[simp] theorem coefficient_zero (i j : Fin (l+1)) :
    coefficient (0 : ChainAlgebra k l) i j = 0 := by
  unfold coefficient
  split <;> simp

@[simp] theorem coefficient_add (x y : ChainAlgebra k l) (i j : Fin (l+1)) :
    coefficient (x+y) i j = coefficient x i j + coefficient y i j := by
  unfold coefficient
  split <;> simp
  split <;> simp

@[simp] theorem coefficient_vertex (h i j : Fin (l+1)) :
    coefficient (vertex k l h) i j = 0 := by
  unfold coefficient
  split <;> simp [vertex]

@[simp] theorem coefficient_arrow (h : Fin l) (i j : Fin (l+1)) :
    coefficient (arrow k l h) i j = if i = h.succ ∧ j = h.castSucc then 1 else 0 := by
  classical
  simp only [coefficient, arrow, Pi.single_apply, Fin.ext_iff,
    Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> simp_all

end ChainAlgebra

namespace OrdinaryTerms
variable (V : Fin (l+1) → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable (d : ∀ i j, V i →ₗ[k] V j)

/-- Coordinate action induced by the genuine differential, not an assumed representation. -/
def action (x : ChainAlgebra k l) (v : OrdinaryTerms V) (i : Fin (l+1)) : V i :=
  x.1 i • v i + ∑ j, ChainAlgebra.coefficient x i j • d j i (v j)

theorem action_add (x : ChainAlgebra k l) (v w : OrdinaryTerms V) :
    action V d x (v+w) = action V d x v + action V d x w := by
  funext i
  simp only [action, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  abel

/-- The complex equation d²=0 implies associativity of the ordinary action. -/
theorem action_mul (dd : ∀ i j h, (d j h).comp (d i j) = 0)
    (x y : ChainAlgebra k l) (v : OrdinaryTerms V) :
    action V d (x*y) v = action V d x (action V d y v) := by
  have hz (i j h) (w : V i) : d j h (d i j w) = 0 := by
    have := LinearMap.congr_fun (dd i j h) w
    simpa using this
  funext i
  simp only [action, ChainAlgebra.mul_diagonal, ChainAlgebra.coefficient_mul,
    map_add, map_smul, map_sum, hz, smul_zero, Finset.sum_const_zero, add_zero,
    smul_add, Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
  simp only [mul_comm]
  abel

/-- Each ordinary vertex projects onto the corresponding genuine term. -/
theorem action_vertex (h : Fin (l+1)) (v : OrdinaryTerms V) :
    action V d (ChainAlgebra.vertex k l h) v = Pi.single h (v h) := by
  classical
  funext i
  simp only [action, ChainAlgebra.coefficient_vertex, zero_smul,
    Finset.sum_const_zero, add_zero]
  change (Pi.single h 1 : Fin (l+1) → k) i • v i = Pi.single h (v h) i
  by_cases hi : i = h
  · subst i; simp
  · simp [hi]

/-- Each ordinary arrow acts by the actual differential on its source term. -/
theorem action_arrow (h : Fin l) (v : OrdinaryTerms V) :
    action V d (ChainAlgebra.arrow k l h) v =
      Pi.single h.succ (d h.castSucc h.succ (v h.castSucc)) := by
  classical
  funext i
  have hz : (ChainAlgebra.arrow k l h).1 i = 0 := rfl
  simp only [action, hz, zero_smul, zero_add, ChainAlgebra.coefficient_arrow]
  by_cases hi : i = h.succ
  · subst i; simp
  · simp [hi]

theorem action_one (v : OrdinaryTerms V) : action V d 1 v = v := by
  funext i
  have ho : (1 : ChainAlgebra k l).1 i = 1 := rfl
  simp [action, ho]

theorem action_zero (v : OrdinaryTerms V) : action V d 0 v = 0 := by
  funext i
  simp only [action, ChainAlgebra.coefficient_zero, zero_smul, Finset.sum_const_zero, add_zero]
  simp [ChainAlgebra.zero_eq]

theorem add_action (x y : ChainAlgebra k l) (v : OrdinaryTerms V) :
    action V d (x+y) v = action V d x v + action V d y v := by
  funext i
  have ha : (x+y).1 i = x.1 i + y.1 i := rfl
  simp only [action, ha, Pi.add_apply, ChainAlgebra.coefficient_add, add_smul, Finset.sum_add_distrib]
  abel

/-- The ordinary C-module constructed from the complex equation. -/
@[instance_reducible]
def module (dd : ∀ i j h, (d j h).comp (d i j) = 0) :
    Module (ChainAlgebra k l) (OrdinaryTerms V) where
  smul := action V d
  one_smul := action_one V d
  mul_smul := action_mul V d dd
  smul_zero x := by
    change action V d x 0 = 0
    funext i
    simp [action]
  smul_add := action_add V d
  add_smul := add_action V d
  zero_smul := action_zero V d

variable (dd : ∀ i j h, (d j h).comp (d i j) = 0)

/-- Any additional scalar action commuting with k and with d commutes with C.
Applied to B and Bᵐᵒᵖ this proves both bimodule actions, without postulating them. -/
theorem action_commutes (R : Type*) [Monoid R] [∀ i, DistribMulAction R (V i)]
    [∀ i, SMulCommClass k R (V i)]
    (hd : ∀ i j (r : R) (v : V i), d i j (r • v) = r • d i j v)
    (x : ChainAlgebra k l) (r : R) (v : OrdinaryTerms V) :
    action V d x (r • v) = r • action V d x v := by
  funext i
  simp only [action, Pi.smul_apply, hd, smul_add, Finset.smul_sum]
  congr 1
  · exact smul_comm _ _ _
  · apply Finset.sum_congr rfl; intro j _; exact smul_comm _ _ _

instance finiteDimensional [∀ i, FiniteDimensional k (V i)] :
    FiniteDimensional k (OrdinaryTerms V) := inferInstanceAs (FiniteDimensional k (∀ i, V i))
end OrdinaryTerms
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryCochain
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k : Type u} [Field k]

/-- The ordinary C-module O formed from the actual terms and differential of P. -/
@[instance_reducible]
def cochainModule (P : CochainComplex (ModuleCat.{u} k) ℤ) (a : ℤ) (l : ℕ) :
    Module (ChainAlgebra k l) (OrdinaryTerms (intervalTerms P a l)) :=
  OrdinaryTerms.module _ (intervalDifferential P a l) (intervalDifferential_square P a l)
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryCompression
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

namespace Compression
variable (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (l : ℕ)
instance instModule : Module k (Compression P a l) :=
  inferInstanceAs (Module k (OrdinaryTerms (intervalTerms (underlyingComplex (k := k) P) a l)))
instance instModuleChainAlgebra : Module (ChainAlgebra k l) (Compression P a l) :=
  cochainModule (underlyingComplex (k := k) P) a l

instance scalarTowerA : IsScalarTower k A (Compression P a l) where
  smul_assoc c r v := by
    funext i
    change (c • r) • v i = (algebraMap k A c) • r • v i
    rw [Algebra.smul_def, mul_smul]

instance instSMulCommClassChainAlgebra : SMulCommClass (ChainAlgebra k l) A (Compression P a l) where
  smul_comm x r v := by
    let (n : ℤ) : Module k (P.X n) := Module.compHom _ (algebraMap k A)
    let (n : ℤ) : IsScalarTower k A (P.X n) := IsScalarTower.of_compHom k A (P.X n)
    let (i : Fin (l+1)) : Module A (intervalTerms (underlyingComplex (k := k) P) a l i) := inferInstanceAs (Module A (P.X (a + (i.val : ℤ))))
    let (i : Fin (l+1)) : SMulCommClass k A (intervalTerms (underlyingComplex (k := k) P) a l i) := inferInstanceAs (SMulCommClass k A (P.X (a + (i.val : ℤ))))
    change OrdinaryTerms.action (intervalTerms (underlyingComplex (k := k) P) a l) (intervalDifferential (underlyingComplex (k := k) P) a l) x (r • v) = r • OrdinaryTerms.action (intervalTerms (underlyingComplex (k := k) P) a l) (intervalDifferential (underlyingComplex (k := k) P) a l) x v
    apply OrdinaryTerms.action_commutes
    intro i j r v
    exact (P.d (a + (i.val : ℤ)) (a + (j.val : ℤ))).hom.map_smul r v

instance finiteDimensional [∀ n, FiniteDimensional k ((underlyingComplex (k := k) P).X n)] :
    FiniteDimensional k (Compression P a l) :=
  inferInstanceAs (FiniteDimensional k (∀ i : Fin (l+1), (underlyingComplex (k := k) P).X (a+(i.val:ℤ))))
end Compression
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimodule
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

namespace BimoduleO
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
instance instModule : Module k (BimoduleO P a l) := inferInstanceAs (Module k (Compression P a l))
instance instIsScalarTowerEnveloping : IsScalarTower k (Enveloping k B) (BimoduleO P a l) := inferInstanceAs (IsScalarTower k (Enveloping k B) (Compression P a l))
instance instModuleChainAlgebra : Module (ChainAlgebra k l) (BimoduleO P a l) :=
  inferInstanceAs (Module (ChainAlgebra k l) (Compression P a l))

instance instSMulCommClassChainAlgebraEnveloping : SMulCommClass (ChainAlgebra k l) (Enveloping k B) (BimoduleO P a l) :=
  inferInstanceAs (SMulCommClass (ChainAlgebra k l) (Enveloping k B) (Compression P a l))

instance towerLeft : IsScalarTower k B (BimoduleO P a l) := by
  apply IsScalarTower.of_algebraMap_smul
  intro c v
  change (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := Bᵐᵒᵖ) ((algebraMap k B) c)) •
    (v : Compression P a l) = c • v
  rw [AlgHom.commutes]
  exact algebraMap_smul (Enveloping k B) c v

instance towerRight : IsScalarTower k Bᵐᵒᵖ (BimoduleO P a l) := by
  apply IsScalarTower.of_algebraMap_smul
  intro c v
  change (Algebra.TensorProduct.includeRight (R := k) (A := B) ((algebraMap k Bᵐᵒᵖ) c)) •
    (v : Compression P a l) = c • v
  rw [AlgHom.commutes]
  exact algebraMap_smul (Enveloping k B) c v

instance commuteChainLeft : SMulCommClass (ChainAlgebra k l) B (BimoduleO P a l) where
  smul_comm x b v := by
    change x • (((b ⊗ₜ[k] (1:Bᵐᵒᵖ)) : Enveloping k B) • (v : Compression P a l)) =
      ((b ⊗ₜ[k] (1:Bᵐᵒᵖ)) : Enveloping k B) • (x • (v : Compression P a l))
    exact smul_comm _ _ _

instance commuteChainRight : SMulCommClass (ChainAlgebra k l) Bᵐᵒᵖ (BimoduleO P a l) where
  smul_comm x b v := by
    change x • ((((1:B) ⊗ₜ[k] b) : Enveloping k B) • (v : Compression P a l)) =
      (((1:B) ⊗ₜ[k] b) : Enveloping k B) • (x • (v : Compression P a l))
    exact smul_comm _ _ _

instance finiteDimensional [∀ n, FiniteDimensional k ((underlyingComplex (k := k) P).X n)] :
    FiniteDimensional k (BimoduleO P a l) := inferInstanceAs (FiniteDimensional k (Compression P a l))
end BimoduleO
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleInputFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B))

instance inputFunctor_additive : (inputFunctor k B M).Additive where
  map_add {N N'} {f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => exact (map_zero _).trans (map_zero _).symm
    | ht m n => exact (BalancedTensor.mk k B _ _ m).map_add _ _
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

abbrev columnFunctor (P : BiComplex k B) (p : ℤ) :
    CochainComplex (ModuleCat.{u} B) ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ :=
  (inputFunctor k B (P.X p)).mapHomologicalComplex (.up ℤ) ⋙ shiftFunctor _ (-p)

instance columnFunctor_additive (P : BiComplex k B) (p : ℤ) :
    (columnFunctor k B P p).Additive := by unfold columnFunctor; infer_instance

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleSingleTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (N : ModuleCat.{u} B)

theorem singleTerm_isZero (n a : ℤ) (h : a ≠ n) :
    IsZero (ModuleCat.of B (Term k B P (singleInput B N) a (n + -a))) :=
  (inputFunctor k B (P.X a)).map_isZero
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 N (n + -a) (by omega))

variable {k B}

variable (k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

theorem totalSingle_isZero (n : ℤ) (hn : ∀ i, p i ≠ n) :
    IsZero (ModuleCat.of B (TotalTerm k B P p (singleInput B N) n)) := by
  let (i : Fin l) := ModuleCat.subsingleton_of_isZero (singleTerm_isZero k B P N n (p i) (hn i))
  exact ModuleCat.isZero_of_subsingleton _

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalPresentation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotalPresentation
open ExternalTensor.Section4
universe u

variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The canonical balanced quotient comparison retains the outside B action. -/
def termEquiv (r q : ℤ) :
    BimoduleComplexTensor.term k B B P Z r q ≃ₗ[B] BimoduleTotal.Term k B P Z r q :=
  { (BimoduleComplexTensor.forgetEquiv k B B P Z r q).toAddEquiv with
    map_smul' := by
      intro b x
      change BimoduleComplexTensor.forgetEquiv k B B P Z r q (b • x) =
        b • (show BimoduleTotal.Term k B P Z r q from
          BimoduleComplexTensor.forgetEquiv k B B P Z r q x)
      let F : BimoduleComplexTensor.term k B B P Z r q →+ BimoduleTotal.Term k B P Z r q :=
        (BimoduleComplexTensor.forgetEquiv k B B P Z r q).toAddEquiv.toAddMonoidHom
      induction x using BalancedTensor.induction_on with
      | hz => exact addHom_smul_zero F b
      | ht m n => rfl
      | ha x y hx hy => exact addHom_smul_add F b x y hx hy }

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def totalTermEquiv (n : ℤ) :
    BimoduleComplexTensor.totalTerm k B B P Z p n ≃ₗ[B]
      BimoduleTotal.TotalTerm k B P p Z n :=
  LinearEquiv.piCongrRight (fun i => termEquiv k B P Z (p i) (n + -(p i)))

end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteDerivedEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y)

instance derivedToEssImageShift : ((derivedEmbedding.{u,max u v} k).toEssImage).CommShift ℤ := by
  dsimp [Functor.toEssImage]
  infer_instance
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFirstBlockTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation.FirstBlockTensor
universe u
variable (k L R O T Z : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable [AddCommGroup O] [Module k O] [Module R O] [Module Lᵐᵒᵖ O]
  [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O] [SMulCommClass R Lᵐᵒᵖ O]
variable [AddCommGroup T] [Module k T] [Module L T] [Module Rᵐᵒᵖ T]
  [IsScalarTower k L T] [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T]
variable [AddCommGroup Z] [Module k Z] [Module L Z] [IsScalarTower k L Z]

def forward : source k L R O T Z →ₗ[k] target k L R O Z :=
  BalancedTensor.lift ((BalancedTensor.mk k L O Z).compl₁₂
    (show OffDiagonal O T →ₗ[k] O from LinearMap.fst k O T)
    (show BlockModule.First k L R Z →ₗ[k] Z from LinearMap.id)) (by
      intro d x z
      exact BalancedTensor.balance (k := k) (A := L) (M := O) (N := Z) d.1 x.1 (show Z from z))

def inverse : target k L R O Z →ₗ[k] source k L R O T Z :=
  BalancedTensor.lift ((BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z)).compl₁₂
    (show O →ₗ[k] OffDiagonal O T from LinearMap.inl k O T)
    (show Z →ₗ[k] BlockModule.First k L R Z from LinearMap.id)) (by
      intro a o z
      have h := BalancedTensor.balance (k := k) (A := L × R) (M := OffDiagonal O T)
        (N := BlockModule.First k L R Z) (a,0) (o,0) z
      change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z)
          (MulOpposite.op a • o,(0:Rᵐᵒᵖ) • (0:T)) (show BlockModule.First k L R Z from z) =
        BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z) (o,0)
          (show BlockModule.First k L R Z from a • z) at h
      rw [smul_zero] at h
      exact h)

omit [Module R O] [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O]
  [SMulCommClass R Lᵐᵒᵖ O] [Module L T] [IsScalarTower k L T]
  [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T] [IsScalarTower k L Z] in
theorem inverse_forward (x : source k L R O T Z) :
    inverse k L R O T Z (forward k L R O T Z x) = x := by
  let F := (inverse k L R O T Z).comp (forward k L R O T Z)
  have h : F = LinearMap.id := by
    apply BalancedTensor.ext
    intro x z
    change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z) (x.1,0) z =
      BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z) x z
    let q := (BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z)).flip z
    have hx : x = (x.1,0) + (0,x.2) := Prod.ext (add_zero _).symm (zero_add _).symm
    exact ((congrArg q hx).trans ((q.map_add _ _).trans
      ((congrArg (q (x.1,0) + ·) (other_block_zero k L R O T Z x.2 z)).trans (add_zero _)))).symm
  exact congrArg (fun f => f x) h

omit [Module R O] [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O]
  [SMulCommClass R Lᵐᵒᵖ O] [Module L T] [IsScalarTower k L T]
  [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T] [IsScalarTower k L Z] in
theorem forward_inverse (x : target k L R O Z) :
    forward k L R O T Z (inverse k L R O T Z x) = x := by
  have h : (forward k L R O T Z).comp (inverse k L R O T Z) = LinearMap.id := by
    apply BalancedTensor.ext
    intro o z
    rfl
  exact congrArg (fun f => f x) h

/-- Tensor on the first block selects O and has its actual output on the second block. -/
def equivalence : source k L R O T Z ≃ₗ[L × R] target k L R O Z where
  toFun := forward k L R O T Z
  invFun := inverse k L R O T Z
  left_inv := inverse_forward k L R O T Z
  right_inv := forward_inverse k L R O T Z
  map_add' := (forward k L R O T Z).map_add
  map_smul' d x := by
    let F := forward k L R O T Z
    have h : F.comp (LeftTensor.action k (L × R) (L × R) (OffDiagonal O T)
        (BlockModule.First k L R Z) d) =
        (Algebra.lsmul k k (target k L R O Z) d).comp F := by
      apply BalancedTensor.ext
      intro x z
      rfl
    exact congrArg (fun f => f x) h

end LittleFinitistic.OrdinarySimulation.FirstBlockTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySecondBlockTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation.SecondBlockTensor
universe u
variable (k L R O T Z : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable [AddCommGroup O] [Module k O] [Module R O] [Module Lᵐᵒᵖ O]
  [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O] [SMulCommClass R Lᵐᵒᵖ O]
variable [AddCommGroup T] [Module k T] [Module L T] [Module Rᵐᵒᵖ T]
  [IsScalarTower k L T] [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T]
variable [AddCommGroup Z] [Module k Z] [Module R Z] [IsScalarTower k R Z]

/-- Tensor on the second block selects T and has its actual output on the first block. -/
def equivalence : source k L R O T Z ≃ₗ[L × R] target k L R T Z where
  toFun := forward k L R O T Z
  invFun := inverse k L R O T Z
  left_inv := inverse_forward k L R O T Z
  right_inv := forward_inverse k L R O T Z
  map_add' := (forward k L R O T Z).map_add
  map_smul' d x := by
    let F := forward k L R O T Z
    have h : F.comp (LeftTensor.action k (L × R) (L × R) (OffDiagonal O T)
        (BlockModule.Second k L R Z) d) =
        (Algebra.lsmul k k (target k L R T Z) d).comp F := by
      apply BalancedTensor.ext
      intro x z
      rfl
    exact congrArg (fun f => f x) h

end LittleFinitistic.OrdinarySimulation.SecondBlockTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBlockTensorTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.BlockTensor
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ)
variable (T : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ)

open BimoduleComplexTensor

def firstTermEquiv (Z : CochainComplex (ModuleCat.{u} L) ℤ) (p q : ℤ) :
    term k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p q ≃ₗ[L × R]
      BlockModule.Second k L R (term k R L O Z p q) := by
  let M := OffDiagonal (BimoduleCoefficients k R L (O.X p)) (BimoduleCoefficients k L R (T.X p))
  let eM := RetainedBimodule.rightEquiv k (L × R) (L × R) M
  let eZ : ComplexTensor.leftTerm k (L × R) (BlockModule.firstComplex L R Z) q ≃ₗ[L × R]
      BlockModule.First k L R (ComplexTensor.leftTerm k L Z q) := LinearEquiv.refl _ _
  exact (LeftTensor.congr (k := k) (A := L × R) (S := L × R) eM (RetainedBimodule.rightEquiv_left k (L × R) (L × R) M) eZ).trans
    (FirstBlockTensor.equivalence k L R (BimoduleCoefficients k R L (O.X p))
      (BimoduleCoefficients k L R (T.X p)) (ComplexTensor.leftTerm k L Z q))

theorem firstTermEquiv_map (Z : CochainComplex (ModuleCat.{u} L) ℤ) {p p' q q' : ℤ}
    (fO : O.X p ⟶ O.X p') (fT : T.X p ⟶ T.X p') (g : Z.X q ⟶ Z.X q') :
    (firstTermEquiv k L R O T Z p' q').toLinearMap.comp
      (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z)
        (OffDiagonal.objectMap k L R fO fT) ((ProductModules.firstInflation L R).map g)) =
    (BlockModule.secondMap k L R (map k R L O Z fO g)).comp
      (firstTermEquiv k L R O T Z p q).toLinearMap := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  rfl

end LittleFinitistic.OrdinarySimulation.BlockTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryChainDirected
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_add _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_mul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_one _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_vertex _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.coefficient_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra
universe u
variable (k : Type u) [Field k] (l : ℕ)

theorem vertex_orthogonal (i j : Fin (l+1)) (hij : i ≠ j) : vertex k l i * vertex k l j = 0 := by
  apply Prod.ext
  · funext t
    change (Pi.single i (1:k) : Fin (l+1) → k) t * (Pi.single j (1:k) : Fin (l+1) → k) t = 0
    by_cases ht : t=i
    · subst t; simp [hij.symm]
    · simp [ht]
  · funext t
    change (Pi.single i (1:k) : Fin (l+1) → k) t.succ * 0 + 0 * (Pi.single j (1:k) : Fin (l+1) → k) t.castSucc = 0
    simp

theorem vertex_complete : ∑ i : Fin (l+1), vertex k l i = 1 := by
  apply Prod.ext
  · funext t
    have h := map_sum ((LinearMap.proj t).comp
      (LinearMap.fst k (Fin (l+1) → k) (Fin l → k))) (fun i : Fin (l+1) => vertex k l i) Finset.univ
    change (∑ i : Fin (l+1), vertex k l i).1 t = 1
    exact h.trans (by
      change (∑ i : Fin (l+1), (Pi.single i (1:k) : Fin (l+1) → k) t) = 1
      simp [Pi.single_apply])
  · funext t
    have h := map_sum ((LinearMap.proj t).comp
      (LinearMap.snd k (Fin (l+1) → k) (Fin l → k))) (fun i : Fin (l+1) => vertex k l i) Finset.univ
    change (∑ i : Fin (l+1), vertex k l i).2 t = 0
    exact h.trans (by
      change (∑ _i : Fin (l+1), (0:k)) = 0
      simp)

theorem vertex_directed (i j : Fin (l+1)) (hij : j < i) (x : ChainAlgebra k l) :
    vertex k l j * x * vertex k l i = 0 := by
  apply Prod.ext
  · funext t
    change ((Pi.single j (1:k) : Fin (l+1) → k) t * x.1 t) *
      (Pi.single i (1:k) : Fin (l+1) → k) t = 0
    by_cases ht : t=j
    · subst t; simp [ne_of_lt hij]
    · simp [ht]
  · funext t
    change ((Pi.single j (1:k) : Fin (l+1) → k) t.succ * x.1 t.succ) * 0 +
      ((Pi.single j (1:k) : Fin (l+1) → k) t.succ * x.2 t + 0 * x.1 t.castSucc) *
        (Pi.single i (1:k) : Fin (l+1) → k) t.castSucc = 0
    by_cases h₁ : t.succ=j
    · have h₂ : t.castSucc ≠ i := by
        intro h
        have := congrArg Fin.val h₁
        have := congrArg Fin.val h
        change j.val < i.val at hij
        simp at *
        omega
      simp [h₂]
    · simp [h₁]

end LittleFinitistic.OrdinarySimulation.ChainAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFirstBlockTotal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BimoduleAssociativity.scalarEquiv_mk _root_.OAI.LittleFinitistic.ComplexTensor.finiteTotalMap_apply _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_comp _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_id _root_.OAI.LittleFinitistic.ComplexTensor.map_id_left
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.BlockTensor
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ)
variable (T : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} L) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
open BimoduleComplexTensor

def firstTotalEquiv (n : ℤ) :
    totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n ≃ₗ[L × R]
      BlockModule.Second k L R (totalTerm k R L O Z p n) :=
  (LinearEquiv.piCongrRight (fun i => firstTermEquiv k L R O T Z (p i) (n + -(p i)))).trans
    (show (∀ i : Fin l, BlockModule.Second k L R (term k R L O Z (p i) (n + -(p i)))) ≃ₗ[L × R]
      BlockModule.Second k L R (totalTerm k R L O Z p n) from LinearEquiv.refl _ _)

@[simp] theorem firstTotalEquiv_apply (n : ℤ)
    (z : totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n)
    (i : Fin l) : firstTotalEquiv k L R O T Z p n z i =
      firstTermEquiv k L R O T Z (p i) (n + -(p i)) (z i) := rfl

theorem first_entry (n : ℤ) (i j : Fin l) :
    (firstTermEquiv k L R O T Z (p j) ((n+1) + -(p j))).toLinearMap.comp
      (entry k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n i j) =
    (BlockModule.secondMap k L R (entry k R L O Z p n i j)).comp
      (firstTermEquiv k L R O T Z (p i) (n + -(p i))).toLinearMap := by
  unfold entry
  split_ifs with h
  · have he : n + -(p i) = (n+1) + -(p j) := by omega
    have ht : (ProductModules.firstInflation L R).map (eqToHom (congrArg Z.X he)) =
        eqToHom (congrArg (BlockModule.firstComplex L R Z).X he) := by
      generalize n + -(p i) = q at he ⊢
      generalize (n+1) + -(p j) = q' at he ⊢
      subst q'
      simp only [eqToHom_refl,CategoryTheory.Functor.map_id]
      rfl
    have hh := firstTermEquiv_map k L R O T Z (O.d (p i) (p j)) (T.d (p i) (p j)) (eqToHom (congrArg Z.X he))
    rw [ht,← OffDiagonal.complex_d_all] at hh
    exact hh
  · apply LinearMap.ext
    intro x
    change firstTermEquiv k L R O T Z (p j) ((n+1) + -(p j)) 0 = 0
    exact (firstTermEquiv k L R O T Z (p j) ((n+1) + -(p j))).map_zero

theorem first_vertical (n : ℤ) (i : Fin l) :
    (firstTermEquiv k L R O T Z (p i) ((n+1) + -(p i))).toLinearMap.comp
      (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) (𝟙 _)
        ((BlockModule.firstComplex L R Z).d (n + -(p i)) ((n+1) + -(p i)))) =
    (BlockModule.secondMap k L R (map k R L O Z (𝟙 _) (Z.d (n + -(p i)) ((n+1) + -(p i))))).comp
      (firstTermEquiv k L R O T Z (p i) (n + -(p i))).toLinearMap := by
  exact firstTermEquiv_map k L R O T Z (𝟙 (O.X (p i))) (𝟙 (T.X (p i))) (Z.d _ _)

theorem first_differential (n : ℤ)
    (z : totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n) :
    firstTotalEquiv k L R O T Z p (n+1)
      (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n z) =
    differential k R L O Z p n (firstTotalEquiv k L R O T Z p n z) := by
  funext j
  change firstTermEquiv k L R O T Z (p j) ((n+1) + -(p j))
      (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n z j) =
    differential k R L O Z p n (firstTotalEquiv k L R O T Z p n z) j
  simp only [differential,
    LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,map_add,map_sum]
  apply congrArg₂ (· + ·)
  · change firstTermEquiv k L R O T Z (p j) ((n+1) + -(p j))
        ((((-(p j)).negOnePow : ℤ)) •
          (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) (𝟙 _)
            ((BlockModule.firstComplex L R Z).d (n + -(p j)) ((n+1) + -(p j))) (z j))) =
      (((-(p j)).negOnePow : ℤ)) •
        (map k R L O Z (𝟙 _) (Z.d (n + -(p j)) ((n+1) + -(p j))))
          (firstTermEquiv k L R O T Z (p j) (n + -(p j)) (z j))
    rw [map_zsmul]
    congr 1
    exact congrArg (fun f => f (z j)) (first_vertical k L R O T Z p n j)
  · erw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun f => f (z i)) (first_entry k L R O T Z p n i j)

end LittleFinitistic.OrdinarySimulation.BlockTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryShiftDerivedTensor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (b : ℤ) (l : ℕ)
variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]

instance shifted_right_projective (n : ℤ) : Module.Projective Bᵐᵒᵖ
    (ComplexTensor.rightTerm k B (BimoduleComplexTensor.rightComplex k B B (P⟦b⟧)) n) :=
  inferInstanceAs (Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X (n+b)))

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySingleTensorTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.SingleBimoduleTensor
universe u
variable (k S A N : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup N] [Module k N] [Module S N] [Module Aᵐᵒᵖ N]
  [IsScalarTower k S N] [IsScalarTower k Aᵐᵒᵖ N] [SMulCommClass S Aᵐᵒᵖ N]

variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
open BimoduleComplexTensor

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p) (i₀ : Fin l) (h₀ : p i₀ = 0)

def termEquivAt (q : ℤ) (hq : q = 0) (n : ℤ) :
    term k S A (complex k S A N) Z q (n + -q) ≃ₗ[S] ((middleLeftComplex k S A N Z)⟦-q⟧).X n :=
  LeftTensor.congr (coefficientEquivAt k S A N q hq) (coefficientEquivAt_left k S A N q hq)
    (LinearEquiv.refl A (ComplexTensor.leftTerm k A Z (n + -q)))

abbrev selectedTermEquiv (n : ℤ) := termEquivAt k S A N Z (p i₀) h₀ n

end LittleFinitistic.SingleBimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryVertexCompression
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.finiteDimensional _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation.Compression
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (l : ℕ)

theorem vertex_action (i : Fin (l+1)) (v : Compression P a l) :
    ChainAlgebra.vertex k l i • v = insert P a l i (project P a l i v) := by
  exact OrdinaryTerms.action_vertex (intervalTerms (underlyingComplex (k := k) P) a l)
    (intervalDifferential (underlyingComplex (k := k) P) a l) i v

/-- The vertex part is a submodule over A, hence retains both B-actions when A=B tensor B-op. -/
def vertexSpace (i : Fin (l+1)) : Submodule A (Compression P a l) where
  carrier := {v | ChainAlgebra.vertex k l i • v = v}
  zero_mem' := smul_zero _
  add_mem' := by
    intro x y hx hy
    change ChainAlgebra.vertex k l i • (x+y) = x+y
    rw [smul_add, hx, hy]
  smul_mem' r v hv := by
    change ChainAlgebra.vertex k l i • (r • v) = r • v
    rw [smul_comm, hv]

def vertexInsert (i : Fin (l+1)) : P.X (a+(i.val:ℤ)) →ₗ[A] vertexSpace (k := k) P a l i :=
  (insert P a l i).codRestrict _ (fun v => by
    change ChainAlgebra.vertex k l i • insert P a l i v = insert P a l i v
    rw [vertex_action]
    congr 1
    change (Pi.single i v : ∀ j : Fin (l+1), P.X (a+(j.val:ℤ))) i = v
    simp)

/-- Actual A-linear identification of the compressed vertex with its original term. -/
def vertexEquiv (i : Fin (l+1)) : vertexSpace (k := k) P a l i ≃ₗ[A] P.X (a+(i.val:ℤ)) where
  __ := (project P a l i).comp (vertexSpace (k := k) P a l i).subtype
  invFun := vertexInsert (k := k) P a l i
  left_inv x := by
    apply Subtype.ext
    exact (vertex_action (k := k) P a l i x.val).symm.trans x.property
  right_inv v := by
    change (Pi.single i v : ∀ j : Fin (l+1), P.X (a+(j.val:ℤ))) i = v
    simp

end LittleFinitistic.OrdinarySimulation.Compression

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexTotalProperties
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The actual vertex of a right-projective bimodule remains right-projective. -/
theorem projective (e : B) (he : e*e=e) (M : ModuleCat.{u} (Enveloping k B))
    (hM : Projective ((forgetRight k B).obj M)) :
    Projective ((BimoduleVertex.functor k B e).obj M) := by
  let := hM
  have : Module.Projective Bᵐᵒᵖ (VertexFunctor.restricted (BimoduleVertex.restriction k B) M) :=
    inferInstanceAs (Module.Projective Bᵐᵒᵖ ((forgetRight k B).obj M))
  have := VertexFunctor.projective (BimoduleVertex.restriction k B) (BimoduleVertex.vertex k B e)
      (BimoduleVertex.vertex_idempotent k B e he) (BimoduleVertex.vertex_commute k B e) M
  change Projective (ModuleCat.of Bᵐᵒᵖ
    (VertexFunctor.fixed (BimoduleVertex.restriction k B) (BimoduleVertex.vertex k B e)
      (BimoduleVertex.vertex_commute k B e) M))
  exact ModuleCat.projective_of_categoryTheory_projective (R := Bᵐᵒᵖ) _

end LittleFinitistic.VertexTotalProperties

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedDiagramEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.testModule_module _root_.OAI.LittleFinitistic.testModule_scalarTower
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

abbrev target := imageDerived (k := ℂ) (Y := Y) e ⊞ (imageDerived (k := ℂ) (Y := Y) e)⟦(3 : ℤ)⟧
def targetAction (r : SelectionRing) : target (Y := Y) ⟶ target (Y := Y) :=
  biprod.map (imageCorner (k := ℂ) (Y := Y) e (alpha r)) ((imageCorner (k := ℂ) (Y := Y) e (alpha r))⟦(3 : ℤ)⟧')

end LittleFinitistic.SelectedDiagramEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedNativeEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
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

/-- The actual primary H(Y), concentrated in degree zero, and its shift by three. -/
abbrev target := HDerived (Y := Y) ⊞ (HDerived (Y := Y))⟦(3 : ℤ)⟧
def targetIso : SelectedDiagramEvaluation.target (Y := Y) ≅ target (Y := Y) :=
  biprod.mapIso (imageIso (Y := Y))
    ((shiftFunctor (FiniteVectorDerived.{0,v} (k := ℂ)) (3 : ℤ)).mapIso (imageIso (Y := Y)))

end LittleFinitistic.SelectedNativeEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedNativeAction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.SelectedTargetHomology.instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
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

abbrev targetAction (r : SelectionRing) : End (target (Y := Y)) :=
  biprod.map (HDerivedAction (Y := Y) r) ((HDerivedAction (Y := Y) r)⟦(3 : ℤ)⟧')

lemma target_square (r : SelectionRing) :
    SelectedDiagramEvaluation.targetAction (Y := Y) r ≫ (targetIso (Y := Y)).hom =
      (targetIso (Y := Y)).hom ≫ targetAction (Y := Y) r := by
  have h := image_square (Y := Y) r
  have hs := congrArg (shiftFunctor (FiniteVectorDerived.{0,v} (k := ℂ)) (3 : ℤ)).map h
  simp only [Functor.map_comp] at hs
  dsimp only [SelectedDiagramEvaluation.targetAction,targetIso,targetAction,biprod.mapIso]
  apply biprod.hom_ext
  · simp only [Category.assoc,biprod.map_fst,biprod.map_fst_assoc,h]
  · simp only [Category.assoc,biprod.map_snd,biprod.map_snd_assoc,Functor.mapIso_hom,hs]

end LittleFinitistic.SelectedNativeEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTargetHomology
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedTargetHomology
open QuadraticEncoding SelectedNativeEvaluation FiniteProjectiveHomotopy
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]
def shiftedIso : I.obj ((HDerived (Y := Y))⟦(3 : ℤ)⟧) ≅
    (DerivedCategory.singleFunctor C (-3)).obj (H (Y := Y)) :=
  (I.commShiftIso (3 : ℤ)).app _ ≪≫
    (shiftFunctor _ (3 : ℤ)).mapIso (stalkIso (Y := Y)) ≪≫
      ((DerivedCategory.singleFunctors C).shiftIso 3 (-3) 0 (by norm_num)).app _

def shiftedHomologyIso : (cohomology (-3)).obj ((HDerived (Y := Y))⟦(3 : ℤ)⟧) ≅ H (Y := Y) :=
  (DerivedCategory.homologyFunctor C (-3)).mapIso shiftedIso ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-3)).app _

lemma shifted_zero (n : ℤ) (hn : n ≠ -3) :
    IsZero ((cohomology n).obj ((HDerived (Y := Y))⟦(3 : ℤ)⟧)) :=
  ((DerivedCategory.homologyFunctor C n).mapIso (shiftedIso (Y := Y))).isZero_iff.mpr
    (single_zero _ _ _ hn)

def targetH0 : (cohomology 0).obj (target (Y := Y)) ≅ H (Y := Y) :=
  (cohomology 0).mapBiprod _ _ ≪≫
    (isoBiprodZero (shifted_zero (Y := Y) 0 (by norm_num))).symm ≪≫ stalkHomologyIso

def targetHm3 : (cohomology (-3)).obj (target (Y := Y)) ≅ H (Y := Y) :=
  (cohomology (-3)).mapBiprod _ _ ≪≫
    (isoZeroBiprod (stalk_zero (Y := Y) (-3) (by norm_num))).symm ≪≫ shiftedHomologyIso

lemma target_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((cohomology n).obj (target (Y := Y))) :=
  ((cohomology n).mapBiprod _ _).isZero_iff.mpr
    ((biprod_isZero_iff _ _).mpr ⟨stalk_zero n h0,shifted_zero n hm⟩)

lemma shifted_action (r : SelectionRing) :
    (cohomology (-3)).map ((HDerivedAction (Y := Y) r)⟦(3 : ℤ)⟧') ≫
      (shiftedHomologyIso (Y := Y)).hom =
        (shiftedHomologyIso (Y := Y)).hom ≫ HAction (Y := Y) r := by
  have hst : I.map (HDerivedAction (Y := Y) r) =
      (DerivedCategory.singleFunctor C 0).map (HAction (Y := Y) r) := by
    change DerivedCategory.Qh.map ((inclusion ℂ).map (HKAction (Y := Y) r)) = _
    dsimp only [HKAction]
    erw [Functor.map_preimage]
    rfl
  have hshift : I.map ((HDerivedAction (Y := Y) r)⟦(3 : ℤ)⟧') ≫ (shiftedIso (Y := Y)).hom =
      (shiftedIso (Y := Y)).hom ≫
        (DerivedCategory.singleFunctor C (-3)).map (HAction (Y := Y) r) := by
    have h1 := (I.commShiftIso (3 : ℤ)).hom.naturality (HDerivedAction (Y := Y) r)
    have h2 := ((DerivedCategory.singleFunctors C).shiftIso 3 (-3) 0 (by norm_num)).hom.naturality
      (HAction (Y := Y) r)
    dsimp only [Functor.comp_map] at h1 h2
    rw [hst] at h1
    have hh := (congrArg (fun f => f ≫
      (((DerivedCategory.singleFunctors C).shiftIso 3 (-3) 0 (by norm_num)).app
        (H (Y := Y))).hom) h1).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun g => (I.commShiftIso (3 : ℤ)).hom.app (HDerived (Y := Y)) ≫ g) h2))
    dsimp only [shiftedIso, stalkIso, Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom]
    erw [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _).symm)

  have h := congrArg (DerivedCategory.homologyFunctor C (-3)).map hshift
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-3)).hom.naturality
    (HAction (Y := Y) r)
  dsimp only [Functor.comp_map,Functor.id_map] at hn
  dsimp only [shiftedHomologyIso,Iso.trans_hom,Functor.mapIso_hom,cohomology,Functor.comp_map]
  rw [← Category.assoc,h,Category.assoc]
  exact (congrArg (fun g => (DerivedCategory.homologyFunctor C (-3)).map
    (shiftedIso (Y := Y)).hom ≫ g) hn).trans (Category.assoc _ _ _).symm

lemma targetH0_hom : (targetH0 (Y := Y)).hom =
    (cohomology 0).map biprod.fst ≫ (stalkHomologyIso (Y := Y)).hom := by
  simp [targetH0,isoBiprodZero]
  erw [biprod.lift_fst_assoc]
lemma targetHm3_hom : (targetHm3 (Y := Y)).hom =
    (cohomology (-3)).map biprod.snd ≫ (shiftedHomologyIso (Y := Y)).hom := by
  simp [targetHm3,isoZeroBiprod]
  erw [biprod.lift_snd_assoc]

lemma targetH0_action (r : SelectionRing) :
    (cohomology 0).map (targetAction (Y := Y) r) ≫ (targetH0 (Y := Y)).hom =
      (targetH0 (Y := Y)).hom ≫ HAction (Y := Y) r := by
  rw [targetH0_hom,← Category.assoc,← Functor.map_comp]
  simp only [targetAction,biprod.map_fst,Functor.map_comp,Category.assoc,stalk_action]
lemma targetHm3_action (r : SelectionRing) :
    (cohomology (-3)).map (targetAction (Y := Y) r) ≫ (targetHm3 (Y := Y)).hom =
      (targetHm3 (Y := Y)).hom ≫ HAction (Y := Y) r := by
  rw [targetHm3_hom,← Category.assoc,← Functor.map_comp]
  simp only [targetAction,biprod.map_snd,Functor.map_comp,Category.assoc,shifted_action]
end LittleFinitistic.SelectedTargetHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedChainHomology
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedChainHomology
open QuadraticEncoding SelectedFixedDiagram SelectedNativeEvaluation
open SelectedTargetHomology
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

def modelIso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (cohomology n).obj (target (Y := Y)) ≅ H (Y := Y) := by
  by_cases h : n = 0
  · subst n; exact targetH0
  · have hm : n = -3 := hn.resolve_left h
    subst n; exact targetHm3

lemma model_action (n : ℤ) (hn : n = 0 ∨ n = -3) (r : SelectionRing) :
    (cohomology n).map (targetAction (Y := Y) r) ≫ (modelIso (Y := Y) n hn).hom =
      (modelIso (Y := Y) n hn).hom ≫ HAction (Y := Y) r := by
  rcases hn with rfl | rfl
  · exact targetH0_action r
  · exact targetHm3_action r

end LittleFinitistic.SelectedChainHomology

end

end OAI
end


