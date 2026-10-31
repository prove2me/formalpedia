-- Prove2me | Definitions.Def_OAIQ023F027
-- name    : OAIQ023F027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T18:42:37.887095+00:00
-- url     : https://prove2.me/theorems/40839923-3930-45c5-bcfe-85a01f14bf69
-- title:
--   Definitions bundle OAIQ023F027 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 1 definition, 1 instance and 1 theorem. The definitions and types are `OAI.LittleFinitistic.OrdinarySimulation.shiftedDerivedTensorComparison`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Ordinary_OrdinaryShiftDerivedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryShiftDerivedTensor.lean), [`Finitistic_Ordinary_OrdinarySimulationComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinarySimulationComparison.lean), [`Finitistic_Ordinary_OrdinaryTensorBimoduleComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryTensorBimoduleComparison.lean).
--
--   **Imports.** It imports the bundle `OAIQ023F023` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ023F030`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F023

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryShiftDerivedTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.ordinaryProjective _root_.OAI.LittleFinitistic.BimoduleTotalPresentation.projectiveDegrees _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instAddCommGroup _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModule _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModuleEnveloping _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

def shiftedDerivedTensorComparison : DerivedCategory.Q ⋙ shiftedDerivedTensor P b l ≅
    BimoduleComplexTensor.totalFunctor k B B (P⟦b⟧)
      (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l) ⋙ DerivedCategory.Q :=
  BimoduleComplexTensor.derivedTotalComparison k B B (P⟦b⟧)
    (TensorResolution.finiteDegrees l) (TensorResolution.finiteDegrees_strictMono l)

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorBimoduleComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

namespace VertexTensor
variable (i : Fin (l+1))
instance instIsScalarTowerEnveloping : IsScalarTower k (Enveloping k B) (VertexTensor P a l i) where
  smul_assoc r x z := by
    change action P a l i (r • x) z = r • action P a l i x z
    rw [map_smul]
    rfl

end VertexTensor
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySimulationComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
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

/-- The lower support condition of the manuscript supplies strict support after reindexing. -/
theorem unsignedSupport (hP : ∀ n : ℤ, n < a → IsZero (P.X n)) :
    (unsignedShift P (a+(l:ℤ))).IsStrictlySupported (TensorResolution.degreeEmbedding l) :=
  ⟨fun n hn => by
    have hlt : n < -(l:ℤ) := by
      by_contra h
      let j := (n+(l:ℤ)).toNat
      have hj : (TensorResolution.degreeEmbedding l).f j = n := by
        simp only [TensorResolution.degreeEmbedding_apply]
        dsimp [j]
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      exact hn j hj
    exact hP (n+(a+l)) (by omega)⟩

end LittleFinitistic.OrdinarySimulation

end

end OAI
end


