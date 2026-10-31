-- Prove2me | Definitions.Def_OAIQ023F012
-- name    : OAIQ023F012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T16:01:21.715632+00:00
-- url     : https://prove2.me/theorems/19fdcbdd-2c09-4b76-94f5-1f55a00e70a9
-- title:
--   Definitions bundle OAIQ023F012 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 150 declarations of OpenAI's Lean: 80 definitions, 14 instances and 56 theorems. The definitions and types are `OAI.LittleFinitistic.BalancedVertexFunctor.Space`, `OAI.LittleFinitistic.BalancedVertexFunctor.comparison`, `OAI.LittleFinitistic.BalancedVertexFunctor.functor`, `OAI.LittleFinitistic.BalancedVertexFunctor.spaceMap`, `OAI.LittleFinitistic.BalancedVertexImage.V`, `OAI.LittleFinitistic.BalancedVertexImage.W`, `OAI.LittleFinitistic.BalancedVertexImage.equiv`, `OAI.LittleFinitistic.BalancedVertexImage.fixedEquiv`, `OAI.LittleFinitistic.BalancedVertexImage.inclusion`, `OAI.LittleFinitistic.BalancedVertexImage.projection`, `OAI.LittleFinitistic.BimoduleAssociativity.coefficient`, `OAI.LittleFinitistic.BimoduleAssociativity.equivalence`, `OAI.LittleFinitistic.BimoduleAssociativity.scalarEquiv`, `OAI.LittleFinitistic.BimoduleAssociativity.source`, `OAI.LittleFinitistic.BimoduleAssociativity.target`, `OAI.LittleFinitistic.BimoduleBalancedTensor.Input`, `OAI.LittleFinitistic.BimoduleBalancedTensor.Tensor`, `OAI.LittleFinitistic.BimoduleBalancedTensor.action`, `OAI.LittleFinitistic.BimoduleBalancedTensor.functor`, `OAI.LittleFinitistic.BimoduleBalancedTensor.inputAction`, `OAI.LittleFinitistic.BimoduleBalancedTensor.inputEnveloping`, `OAI.LittleFinitistic.BimoduleBalancedTensor.map`, `OAI.LittleFinitistic.BimoduleBarComparison.Actions`, `OAI.LittleFinitistic.BimoduleBarComparison.BarTensor`, `OAI.LittleFinitistic.BimoduleBarComparison.fromBar`, `OAI.LittleFinitistic.BimoduleBarComparison.fromBarUnbalanced`, `OAI.LittleFinitistic.BimoduleBarComparison.tensorEquiv`, `OAI.LittleFinitistic.BimoduleBarComparison.tensorFunctorIso`, `OAI.LittleFinitistic.BimoduleBarComparison.toBar`, `OAI.LittleFinitistic.BimoduleBarComparison.toBarLinear`, `OAI.LittleFinitistic.BimoduleComplexTensor.associativeTermEquiv`, `OAI.LittleFinitistic.BimoduleComplexTensor.associativeTotalEquiv`, `OAI.LittleFinitistic.BimoduleComplexTensor.differential`, `OAI.LittleFinitistic.BimoduleComplexTensor.entry`, `OAI.LittleFinitistic.BimoduleComplexTensor.forgetEquiv`, `OAI.LittleFinitistic.BimoduleComplexTensor.forgetTotalEquiv`, `OAI.LittleFinitistic.BimoduleComplexTensor.map`, `OAI.LittleFinitistic.BimoduleComplexTensor.middleBimoduleComplex`, `OAI.LittleFinitistic.BimoduleComplexTensor.term`, `OAI.LittleFinitistic.BimoduleComplexTensor.termInputMap` and 40 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bimodule_BimoduleBalancedTensor`, `Finitistic_Bimodule_BimoduleBarTensorComparison`, `Finitistic_Bimodule_BimoduleInputFunctor`, `Finitistic_Bimodule_BimoduleTensorFunctor`, `Finitistic_Bimodule_BimoduleTensorUnderlying`, `Finitistic_Bimodule_BimoduleTotalFunctor`, `Finitistic_Bimodule_BimoduleTotalTerms`, `Finitistic_Bimodule_BimoduleVertex`, `Finitistic_Encoding_QuadraticEncoding`, `Finitistic_Localization_EvaluationModule`, `Finitistic_Ordinary_OrdinaryAssociativeTensorModules`, `Finitistic_Ordinary_OrdinaryAssociativityNaturality`, `Finitistic_Ordinary_OrdinaryBimoduleAssociativeTerms`, `Finitistic_Ordinary_OrdinaryBimoduleAssociativity`, `Finitistic_Ordinary_OrdinaryBimoduleTensorFunctor`, `Finitistic_Ordinary_OrdinaryBimoduleTensorTerms`, `Finitistic_Ordinary_OrdinaryBimoduleTensorTotal`, `Finitistic_Ordinary_OrdinaryBimoduleTotalAssociativity`, `Finitistic_Ordinary_OrdinaryBimoduleTotalMaps`, `Finitistic_Ordinary_OrdinaryComplexTensorMaps`, `Finitistic_Ordinary_OrdinaryLeftTensorCongruence`, `Finitistic_Ordinary_OrdinaryLeftTensorMaps`, `Finitistic_Ordinary_OrdinaryMiddleTensorFunctors`, `Finitistic_Ordinary_OrdinaryTensorColumnAcyclic`, `Finitistic_Ordinary_OrdinaryTensorFiniteMatrix`, `Finitistic_Ordinary_OrdinaryTensorInputMaps`, `Finitistic_Ordinary_OrdinaryTensorMixedSign`, `Finitistic_Ordinary_OrdinaryTensorRightRestriction`, `Finitistic_Ordinary_OrdinaryTensorTotalFunctor`, `Finitistic_Ordinary_OrdinaryTensorTotalQuasiIso`, `Finitistic_Ordinary_OrdinaryTwoSidedTensor`, `Finitistic_Rectification_ColumnProperties`, `Finitistic_Rectification_CornerColumnComplex`, `Finitistic_Rectification_CornerColumnPaths`, `Finitistic_Rectification_CornerProjection`, `Finitistic_Rectification_CornerTensor`, `Finitistic_Rectification_VertexColumnComplex`, `Finitistic_Rectification_VertexColumnModels`, `Finitistic_Rectification_VertexFunctor`, `Finitistic_Tensor_BalancedProjectiveLeft`, `Finitistic_Tensor_BalancedVertexFunctor`, `Finitistic_Tensor_BalancedVertexImage`.
--
--   **Imports.** It imports the bundles `OAIQ023F005`, `OAIQ023F006`, `OAIQ023F007` and `OAIQ023F008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F018`, `OAIQ023F019`, `OAIQ023F020` and `OAIQ023F039`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F005
import Definitions.Def_OAIQ023F006
import Definitions.Def_OAIQ023F007
import Definitions.Def_OAIQ023F008

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnProperties
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule

/-- Exact boundedness transfer for each induced column. -/
theorem column_isZero (e : B) (D : RightComplex B) (i : ℤ)
    (hi : IsZero (D.X i)) : IsZero (((columnComplex k B e).obj D).X i) :=
  (columnFunctor k B e).map_isZero hi

theorem sum_term_isZero {I : Type} [Fintype I] (K : I → BiComplex k B)
    (n : ℤ) (hK : ∀ i, IsZero ((K i).X n)) : IsZero ((⨁ K).X n) := by
  apply ((HomologicalComplex.eval _ _ n).mapBiproduct K).isZero_iff.mpr
  exact sum_isZero _ hK

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

def homogenized (P : Relations k d t) (j : Fin t) : Paths k d :=
  (∑ h, ∑ l, P.quadratic j h l • (basis h.succ ⊗ₜ[k] basis l.succ)) +
  (∑ h, P.linear j h • (basis 0 ⊗ₜ[k] basis h.succ)) +
  P.constant j • (basis 0 ⊗ₜ[k] basis 0)

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerProjection
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace LittleFinitistic.CornerProjection
open ThreeVertexAlgebra CornerSpaces
universe u
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)

theorem projection_idempotent (i j : Fin 3) :
    (projection μ i j).comp (projection μ i j) = projection μ i j := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change vertex μ i * (vertex μ i * x.val) = vertex μ i * x.val
  rw [← mul_assoc,videm]

/-- The image of the actual column projector is the concrete two-sided path corner. -/
def rangeEquiv (i j : Fin 3) : (projection μ i j).range ≃ₗ[k] corner μ i j where
  toFun x := ⟨x.val.val,by
    obtain ⟨y,hy⟩ := x.property
    have h := congrArg Subtype.val hy
    change vertex μ i * y.val = x.val.val at h
    change vertex μ i * x.val.val * vertex μ j = x.val.val
    rw [← h,← mul_assoc,videm,mul_assoc,ideal_right_fixed]⟩
  invFun x := ⟨⟨x.val,⟨x.val,corner_right_fixed μ i j x⟩⟩,by
    refine ⟨⟨x.val,⟨x.val,corner_right_fixed μ i j x⟩⟩,?_⟩
    apply Subtype.ext
    exact corner_left_fixed μ i j x⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl
end LittleFinitistic.CornerProjection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.TensorComplex.mapRight_tmul
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

/-- The concrete corner tensor is the fixed submodule of the induced column. -/
def cornerTensorEquiv (i j : Fin 3) :
    (corner μ i j ⊗[k] N) ≃ₗ[(ThreeVertexAlgebra μ)ᵐᵒᵖ]
    TensorProjection.fixed (B := ThreeVertexAlgebra μ) (N := N) (projection μ i j) :=
  (rightCongr (B := ThreeVertexAlgebra μ) (N := N) (rangeEquiv μ i j).symm).trans
    (imageTensorEquiv (B := ThreeVertexAlgebra μ) (N := N)
      (projection μ i j) (projection_idempotent μ i j))

/-- This fixed-space definition uses the original left vertex action on the column. -/
theorem fixed_iff_left_action (i j : Fin 3)
    (x : ExternalTensor.Column k (ThreeVertexAlgebra μ) N (vertex μ j)) :
    x ∈ TensorProjection.fixed (B := ThreeVertexAlgebra μ) (projection μ i j) ↔
      vertex μ i • x = x := by
  rw [TensorProjection.mem_fixed]
  have h : rightMap (B := ThreeVertexAlgebra μ) (projection μ i j) x = vertex μ i • x := by
    induction x using OAI.tensorInductionOn with
    | tmul m n => rfl
    | add x y hx hy => simp_all [smul_add]
  rw [h]

end LittleFinitistic.CornerTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

theorem projection_inclusion (M : ModuleCat.{u} A) :
    (projection β e he hc M).comp (inclusion β e hc M) = LinearMap.id := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  exact (mem_fixed β e hc M m.val).1 m.property

end LittleFinitistic.VertexFunctor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleVertex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

abbrev columnObj (j : Fin 3) : ModuleCat.{u} (T ⊗[k] Tᵐᵒᵖ) :=
  ModuleCat.of _ (ExternalTensor.Column k T N (ThreeVertexAlgebra.vertex μ j))
abbrev columnFixed (i j : Fin 3) :=
  VertexFunctor.fixed (restriction k T) (vertex k T (ThreeVertexAlgebra.vertex μ i))
    (vertex_commute k T (ThreeVertexAlgebra.vertex μ i)) (columnObj μ N j)

/-- Identifies the original enveloping vertex action with its corner projector. -/
def columnFixedEquiv (i j : Fin 3) :
    columnFixed μ N i j ≃ₗ[Tᵐᵒᵖ]
    TensorProjection.fixed (B := T) (N := N) (CornerProjection.projection μ i j) := by
  refine
    { toFun := fun x => ⟨x.val, ?_⟩
      invFun := fun x => ⟨x.val, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun b x => ?_ }
  · apply (CornerTensor.fixed_iff_left_action μ N i j _).2
    have hx := (VertexFunctor.mem_fixed _ _ _ _ x.val).1 x.property
    change (ThreeVertexAlgebra.vertex μ i ⊗ₜ[k] (1 : Tᵐᵒᵖ)) • x.val = x.val at hx
    exact (ExternalTensor.left_eq_enveloping k T
      (ExternalTensor.leftIdeal T (ThreeVertexAlgebra.vertex μ j)) N
      (ThreeVertexAlgebra.vertex μ i) x.val).trans hx
  · apply Subtype.ext
    exact (ExternalTensor.right_eq_enveloping k T
      (ExternalTensor.leftIdeal T (ThreeVertexAlgebra.vertex μ j)) N b x.val).symm

  · apply (VertexFunctor.mem_fixed _ _ _ _ _).2
    have hx := (CornerTensor.fixed_iff_left_action μ N i j x.val).1 x.property
    exact (ExternalTensor.left_eq_enveloping k T
      (ExternalTensor.leftIdeal T (ThreeVertexAlgebra.vertex μ j)) N
      (ThreeVertexAlgebra.vertex μ i) x.val).symm.trans hx
end LittleFinitistic.BimoduleVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexColumnModels
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The actual vertex of an induced column is its path-corner tensor. -/
def cornerEquiv (i j : Fin 3) :
    BimoduleVertex.columnFixed μ N i j ≃ₗ[Tᵐᵒᵖ] (CornerSpaces.corner μ i j ⊗[k] N) :=
  (BimoduleVertex.columnFixedEquiv μ N i j).trans
    (CornerTensor.cornerTensorEquiv μ N i j).symm

end LittleFinitistic.VertexColumnModels

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexColumnComplex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.biBinaryBiproducts _root_.OAI.ExternalTensor.Section4.biFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

abbrev vertexColumn (i j : Fin 3) : ModuleCat.{u} Tᵐᵒᵖ ⥤ ModuleCat.{u} Tᵐᵒᵖ :=
  ExternalTensor.Section4.columnFunctor k T (ThreeVertexAlgebra.vertex μ j) ⋙
    BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex μ i)

end LittleFinitistic.VertexColumnComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerColumnComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.biBinaryBiproducts _root_.OAI.ExternalTensor.Section4.biFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.CornerColumnComplex
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule

/-- Every actual vertex column is its concrete corner-tensor complex. -/
def complexIso (i j : Fin 3)
    (D : CochainComplex (ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ) ℤ) :
    TensorComplex.complex D (ModuleCat.of k (CornerSpaces.corner μ i j)) ≅
      ((VertexColumnComplex.vertexColumn μ i j).mapHomologicalComplex (.up ℤ)).obj D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (VertexColumnModels.cornerEquiv μ (D.X n) i j).symm.toModuleIso) (by
      intro n m hnm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using OAI.tensorInductionOn with
      | tmul c v => rfl
      | add x y hx hy =>
        exact (map_add _ _ _).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm))
end LittleFinitistic.CornerColumnComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerColumnPaths
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.biBinaryBiproducts _root_.OAI.ExternalTensor.Section4.biFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.CornerColumnPaths
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
local notation "T" => ThreeVertexAlgebra μ
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule

/-- Right multiplication by the original path on the actual vertex corner. -/
def cornerMap (v i j : Fin 3) (a : ThreeVertexAlgebra μ)
    (ha : a * ThreeVertexAlgebra.vertex μ i = a) :
    CornerSpaces.corner μ v j →ₗ[k] CornerSpaces.corner μ v i where
  toFun x := ⟨x.val*a,by
    change ThreeVertexAlgebra.vertex μ v * (x.val*a) * ThreeVertexAlgebra.vertex μ i = x.val*a
    calc
      _ = (ThreeVertexAlgebra.vertex μ v * x.val) *
        (a * ThreeVertexAlgebra.vertex μ i) := by simp only [mul_assoc]
      _ = x.val*a := by rw [CornerProjection.corner_left_fixed,ha]⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' c x := Subtype.ext (smul_mul_assoc _ _ _)

/-- The corner-tensor identification carries the actual induced path map to right multiplication. -/
theorem path_naturality (v i j : Fin 3) (a : ThreeVertexAlgebra μ)
    (ha : a * ThreeVertexAlgebra.vertex μ i = a)
    (D : CochainComplex (ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ) ℤ) :
    TensorComplex.complexMap D (ModuleCat.ofHom (cornerMap μ v i j a ha)) ≫
        (CornerColumnComplex.complexIso μ v i D).hom =
      (CornerColumnComplex.complexIso μ v j D).hom ≫
        ((BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex μ v)).mapHomologicalComplex (.up ℤ)).map
          (ExternalTensor.Section4.path k T (ThreeVertexAlgebra.vertex μ i)
            (ThreeVertexAlgebra.vertex μ j) a ha D) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul c z => rfl
  | add x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

end LittleFinitistic.CornerColumnPaths

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBalancedTensor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.Free.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.Free.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRightTo_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_tensorInv _root_.OAI.LittleFinitistic.IdempotentTensor.tensorInv_tensorEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleBalancedTensor
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B))
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

abbrev Input := BalancedTensor.ScalarModule k B ((forgetRight k B).obj M)
local instance inputEnveloping : Module (Enveloping k B) (Input k B M) :=
  inferInstanceAs (Module (Enveloping k B) M)

abbrev Tensor := BalancedTensor.Tensor k B (Input k B M) N

def inputAction (b : B) : Input k B M →ₗ[Bᵐᵒᵖ] Input k B M :=
  VertexFunctor.action (BimoduleVertex.restriction k B) (BimoduleVertex.vertex k B b)
    (BimoduleVertex.vertex_commute k B b) M

/-- The original left B action on a genuine bimodule descends through balancing over B. -/
def action : B →+* Module.End k (Tensor k B M N) where
  toFun b := BalancedTensor.mapLeft (k := k) N (inputAction k B M b)
  map_zero' := by
    apply BalancedTensor.ext
    intro m n
    change BalancedTensor.mk k B (Input k B M) N (((0 : B) ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n = 0
    rw [TensorProduct.zero_tmul]
    have hz : (0 : Enveloping k B) • (m : M) = 0 := Module.zero_smul (R := Enveloping k B) m
    rw [hz]
    simp
  map_one' := by
    apply BalancedTensor.ext
    intro m n
    change BalancedTensor.mk k B (Input k B M) N (((1 : B) ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n =
      BalancedTensor.mk k B (Input k B M) N m n
    rw [← Algebra.TensorProduct.one_def,one_smul]
  map_add' a b := by
    apply BalancedTensor.ext
    intro m n
    change BalancedTensor.mk k B (Input k B M) N (((a+b) ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n =
      BalancedTensor.mk k B (Input k B M) N ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n +
      BalancedTensor.mk k B (Input k B M) N ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n
    rw [TensorProduct.add_tmul,add_smul]
    exact LinearMap.congr_fun ((BalancedTensor.mk k B (Input k B M) N).map_add _ _) n
  map_mul' a b := by
    apply BalancedTensor.ext
    intro m n
    change BalancedTensor.mk k B (Input k B M) N (((a*b) ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n =
      BalancedTensor.mk k B (Input k B M) N
        ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M))) n
    rw [← mul_smul,Algebra.TensorProduct.tmul_mul_tmul,one_mul]

instance leftModule : Module B (Tensor k B M N) :=
  Module.compHom (Tensor k B M N) (action k B M N)

@[simp] theorem smul_mk (b : B) (m : Input k B M) (n : N) :
    b • BalancedTensor.mk k B (Input k B M) N m n =
      BalancedTensor.mk k B (Input k B M) N
        ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M)) n := rfl
end LittleFinitistic.BimoduleBalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTensorFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.Free.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.Free.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRightTo_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_tensorInv _root_.OAI.LittleFinitistic.IdempotentTensor.tensorInv_tensorEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleBalancedTensor
open ExternalTensor.Section4
attribute [local instance] inputEnveloping
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B))
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

theorem algebraMap_smul (c : k) (x : Tensor k B M N) :
    algebraMap k B c • x = c • x := by
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n =>
    rw [smul_mk]
    have he : (algebraMap k B c ⊗ₜ[k] (1 : Bᵐᵒᵖ)) =
        algebraMap k (Enveloping k B) c :=
      (Algebra.TensorProduct.includeLeft : B →ₐ[k] Enveloping k B).commutes c
    rw [he]
    have hm : algebraMap k (Enveloping k B) c • (m : M) = (c • m : Input k B M) := by
      change algebraMap k (Enveloping k B) c • (m : M) =
        BimoduleVertex.restriction k B (algebraMap k Bᵐᵒᵖ c) • (m : M)
      rw [show BimoduleVertex.restriction k B (algebraMap k Bᵐᵒᵖ c) =
        algebraMap k (Enveloping k B) c from
        (Algebra.TensorProduct.includeRight : Bᵐᵒᵖ →ₐ[k] Enveloping k B).commutes c]
    rw [hm]
    exact LinearMap.congr_fun ((BalancedTensor.mk k B (Input k B M) N).map_smul c m) n
  | ha x y hx hy => simp_all [smul_add]

instance scalarTower : IsScalarTower k B (Tensor k B M N) :=
  IsScalarTower.of_algebraMap_smul (algebraMap_smul k B M N)

variable {M} {M' : ModuleCat.{u} (Enveloping k B)}
/-- A genuine bimodule map induces a map preserving the full left B action after tensoring. -/
def map (f : M ⟶ M') : Tensor k B M N →ₗ[B] Tensor k B M' N where
  __ := (BalancedTensor.mapLeft (k := k) N ((forgetRight k B).map f).hom).toAddMonoidHom
  map_smul' b x := by
    induction x using BalancedTensor.induction_on with
    | hz =>
      rw [smul_zero]
      exact (map_zero _).trans
        ((congrArg (b • ·) (map_zero _)).trans (smul_zero b)).symm
    | ht m n =>
      change BalancedTensor.mk k B (Input k B M') N (f.hom
        ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M))) n =
        BalancedTensor.mk k B (Input k B M') N
          ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • f.hom m) n
      exact congrArg (fun m' => BalancedTensor.mk k B (Input k B M') N m' n)
        (f.hom.map_smul (b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) (m : M))
    | ha x y hx hy =>
      rw [smul_add]
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
        ((smul_add b _ _).symm.trans (congrArg (b • ·) (map_add _ _ _).symm)))

/-- The actual balanced tensor functor from bimodules to left modules. -/
def functor : ModuleCat.{u} (Enveloping k B) ⥤ ModuleCat.{u} B where
  obj M := ModuleCat.of B (Tensor k B M N)
  map f := ModuleCat.ofHom (map k B N f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

instance additive : (functor k B N).Additive where
  map_add := by
    intros M M' f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz =>
      exact (map_zero _).trans (map_zero _).symm
    | ht m n =>
      change BalancedTensor.mk k B (Input k B M') N (f.hom m + g.hom m) n = _
      exact LinearMap.congr_fun ((BalancedTensor.mk k B (Input k B M') N).map_add _ _) n
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
end LittleFinitistic.BimoduleBalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTensorUnderlying
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.Free.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.Free.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRightTo_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_tensorInv _root_.OAI.LittleFinitistic.IdempotentTensor.tensorInv_tensorEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleBalancedTensor
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

/-- Finite input vector spaces give finite balanced tensor spaces. -/
instance finite (M : ModuleCat.{u} (Enveloping k B))
    [FiniteDimensional k (Input k B M)] [FiniteDimensional k N] :
    FiniteDimensional k (Tensor k B M N) := by
  dsimp [Tensor]
  infer_instance
end LittleFinitistic.BimoduleBalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryComplexTensorMaps
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)

/-- The balanced map for actual maps between terms of the two input complexes. -/
def map {p p' q q' : ℤ} (f : Q.X p ⟶ Q.X p') (g : Z.X q ⟶ Z.X q') :
    term k A Q Z p q →ₗ[k] term k A Q Z p' q' :=
  bimap (k := k)
    (M := rightTerm k A Q p) (M' := rightTerm k A Q p')
    (N := leftTerm k A Z q) (N' := leftTerm k A Z q') f.hom g.hom

@[simp] theorem map_comp {p p' p'' q q' q'' : ℤ}
    (f : Q.X p ⟶ Q.X p') (f' : Q.X p' ⟶ Q.X p'')
    (g : Z.X q ⟶ Z.X q') (g' : Z.X q' ⟶ Z.X q'') :
    (map k A Q Z f' g').comp (map k A Q Z f g) = map k A Q Z (f ≫ f') (g ≫ g') :=
  bimap_comp _ _ _ _

@[simp] theorem map_zero_left {p p' q q' : ℤ} (g : Z.X q ⟶ Z.X q') :
    map k A Q Z (0 : Q.X p ⟶ Q.X p') g = 0 := bimap_zero_left _

@[simp] theorem map_zero_right {p p' q q' : ℤ} (f : Q.X p ⟶ Q.X p') :
    map k A Q Z f (0 : Z.X q ⟶ Z.X q') = 0 := bimap_zero_right _

/-- The column at right degree p, including the standard total-complex sign (-1)^p. -/
def column (p : ℤ) : CochainComplex (ModuleCat.{u} k) ℤ :=
  (((fixedTensorFunctor k A (rightTerm k A Q p)).mapHomologicalComplex (.up ℤ)).obj Z)⟦-p⟧

@[simp] theorem column_d (p n m : ℤ) :
    ((column k A Q Z p).d n m).hom =
      (-p).negOnePow • map k A Q Z (𝟙 (Q.X p)) (Z.d (n + -p) (m + -p)) := by
  apply BalancedTensor.ext
  intro x y
  rfl

/-- Horizontal tensor maps reindex the unchanged left factor along the total degree. -/
def horizontal (n p p' : ℤ) (h : p+1=p') :
    term k A Q Z p (n + -p) →ₗ[k] term k A Q Z p' ((n+1) + -p') :=
  map k A Q Z (Q.d p p') (eqToHom (congrArg Z.X (by omega)))

theorem horizontal_square (n p p' p'' : ℤ) (h : p+1=p') (h' : p'+1=p'') :
    (horizontal k A Q Z (n+1) p' p'' h').comp (horizontal k A Q Z n p p' h) = 0 := by
  unfold horizontal
  rw [map_comp,Q.d_comp_d,map_zero_left]
end LittleFinitistic.ComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorColumnAcyclic
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)

@[simp] theorem map_id_left {p q q' : ℤ} (g : Z.X q ⟶ Z.X q') :
    map k A Q Z (𝟙 (Q.X p)) g =
      @mapRightTo k A (rightTerm k A Q p) (leftTerm k A Z q) (leftTerm k A Z q')
        _ _ _ _ _ _ _ _ _ (scalarLeftTower k A (Z.X q))
        _ _ _ (scalarLeftTower k A (Z.X q')) g.hom := by
  apply BalancedTensor.ext
  intro x y
  rfl

end LittleFinitistic.ComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorMixedSign
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)

/-- Signed vertical tensor differential on the concrete balanced tensor term. -/
def vertical (n p : ℤ) : term k A Q Z p (n + -p) →ₗ[k] term k A Q Z p ((n+1) + -p) :=
  (-p).negOnePow • map k A Q Z (𝟙 (Q.X p)) (Z.d (n + -p) ((n+1) + -p))

/-- The two mixed terms cancel with the actual integer total-complex signs. -/
theorem horizontal_mixed (n p p' : ℤ) (h : p+1=p') :
    (vertical k A Q Z (n+1) p').comp (horizontal k A Q Z n p p' h) +
      (horizontal k A Q Z (n+1) p p' h).comp (vertical k A Q Z n p) = 0 := by
  unfold vertical horizontal
  rw [LinearMap.smul_comp,LinearMap.comp_smul,map_comp,map_comp,Category.comp_id,Category.id_comp]
  have hd := transport_d A Z
    (show n + -p = (n+1) + -p' by omega)
    (show (n+1) + -p = ((n+1)+1) + -p' by omega)
  rw [hd]
  have hs : (-p').negOnePow = -(-p).negOnePow := by
    subst p'
    simp only [Int.negOnePow_neg,Int.negOnePow_succ]
  rw [hs]
  change (-(↑((-p).negOnePow) : ℤ)) • _ + (↑((-p).negOnePow) : ℤ) • _ = (0 : term k A Q Z p (n + -p) →ₗ[k] term k A Q Z p' (((n+1)+1) + -p'))
  rw [neg_smul,neg_add_cancel]
end LittleFinitistic.ComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorFiniteMatrix
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.ComplexTensor.map_id_left _root_.OAI.LittleFinitistic.FiniteColumnComplex.componentMap_apply _root_.OAI.LittleFinitistic.FiniteColumnComplex.coneEquiv_coordinate _root_.OAI.LittleFinitistic.FiniteColumnComplex.coneEquiv_symm_coordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ)

abbrev columns := fun i : Fin l => column k A Q Z (p i)

/-- The actual horizontal matrix entry, zero unless the right degrees are consecutive. -/
def entry (n : ℤ) (i j : Fin l) :
    term k A Q Z (p i) (n + -(p i)) →ₗ[k] term k A Q Z (p j) ((n+1) + -(p j)) :=
  if h : p i + 1 = p j then horizontal k A Q Z n (p i) (p j) h else 0

theorem entry_square (n : ℤ) (i j t : Fin l) :
    (entry k A Q Z p (n+1) j t).comp (entry k A Q Z p n i j) = 0 := by
  unfold entry
  split_ifs with h₁ h₂ h₂
  · exact horizontal_square k A Q Z n (p i) (p j) (p t) h₂ h₁
  · simp only [LinearMap.comp_zero]
  · simp only [LinearMap.zero_comp]
  · simp only [LinearMap.zero_comp]

theorem entry_mixed (n : ℤ) (i j : Fin l) :
    (vertical k A Q Z (n+1) (p j)).comp (entry k A Q Z p n i j) +
      (entry k A Q Z p (n+1) i j).comp (vertical k A Q Z n (p i)) = 0 := by
  unfold entry
  split_ifs with h
  · exact horizontal_mixed k A Q Z n (p i) (p j) h
  · simp only [LinearMap.comp_zero,LinearMap.zero_comp,add_zero]

/-- The actual finite horizontal tensor differential, on the sum of all selected columns. -/
def matrix (n : ℤ) : FiniteColumnComplex.term (columns k A Q Z p) n →ₗ[k]
    FiniteColumnComplex.term (columns k A Q Z p) (n+1) :=
  LinearMap.pi (fun j => ∑ i : Fin l, (entry k A Q Z p n i j).comp (LinearMap.proj i))

@[simp] theorem matrix_apply (n : ℤ)
    (z : FiniteColumnComplex.term (columns k A Q Z p) n) (j : Fin l) :
    matrix k A Q Z p n z j = ∑ i : Fin l, entry k A Q Z p n i j (z i) := by
  change ((∑ i : Fin l, (entry k A Q Z p n i j).comp
    (LinearMap.proj i) : (∀ t : Fin l, term k A Q Z (p t) (n + -(p t))) →ₗ[k]
      term k A Q Z (p j) ((n+1) + -(p j))) z) = _
  exact LinearMap.sum_apply _ _ _

theorem matrix_square (n : ℤ) :
    (matrix k A Q Z p (n+1)).comp (matrix k A Q Z p n) = 0 := by
  apply LinearMap.ext
  intro z
  funext j
  change matrix k A Q Z p (n+1) (matrix k A Q Z p n z) j = 0
  simp only [matrix_apply,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro t _
  exact congrArg (fun f => f (z t)) (entry_square k A Q Z p n t i j)

theorem matrix_mixed (n : ℤ) :
    (FiniteColumnComplex.diagonal (columns k A Q Z p) (n+1)).comp (matrix k A Q Z p n) +
    (matrix k A Q Z p (n+1)).comp (FiniteColumnComplex.diagonal (columns k A Q Z p) n) = 0 := by
  apply LinearMap.ext
  intro z
  funext j
  change ((column k A Q Z (p j)).d (n+1) ((n+1)+1)).hom (matrix k A Q Z p n z j) +
    matrix k A Q Z p (n+1) (FiniteColumnComplex.diagonal (columns k A Q Z p) n z) j = 0
  simp only [matrix_apply,FiniteColumnComplex.diagonal_apply]
  erw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  have h := congrArg (fun f => f (z i)) (entry_mixed k A Q Z p n i j)
  simp only [vertical] at h
  simp only [column_d]
  exact h

theorem matrix_upper (hp : StrictMono p) (n : ℤ) (j : Fin l)
    (z : FiniteColumnComplex.term (columns k A Q Z p) n)
    (hz : ∀ i : Fin l, i.val < j.val → z i = 0) : matrix k A Q Z p n z j = 0 := by
  rw [matrix_apply]
  apply Finset.sum_eq_zero
  intro i _
  unfold entry
  split_ifs with h
  · have hij : i < j := hp.lt_iff_lt.mp (by omega)
    erw [hz i hij,map_zero]
    rfl
  · rfl

/-- Actual tensor horizontal maps satisfy every requirement of the finite total construction. -/
def tensorHorizontal (hp : StrictMono p) : FiniteColumnComplex.Horizontal (columns k A Q Z p) where
  d := matrix k A Q Z p
  square := matrix_square k A Q Z p
  mixed := matrix_mixed k A Q Z p
  strictUpper := matrix_upper k A Q Z p hp

/-- The signed total tensor complex on a finite interval of the right complex. -/
def finiteTotal (hp : StrictMono p) : CochainComplex (ModuleCat.{u} k) ℤ :=
  FiniteColumnComplex.total (columns k A Q Z p) (tensorHorizontal k A Q Z p hp)
end LittleFinitistic.ComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorInputMaps
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.ComplexTensor.map_id_left
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z')

/-- The actual map induced by an input chain map in a single balanced tensor term. -/
def inputMap (p q : ℤ) : term k A Q Z p q →ₗ[k] term k A Q Z' p q :=
  bimap (k := k) (M := rightTerm k A Q p) (M' := rightTerm k A Q p)
    (N := leftTerm k A Z q) (N' := leftTerm k A Z' q) LinearMap.id (f.f q).hom

/-- Input chain maps act on the signed columns by the actual shifted tensor functor. -/
def columnMap (p : ℤ) : column k A Q Z p ⟶ column k A Q Z' p :=
  (shiftFunctor _ (-p)).map
    (((fixedTensorFunctor k A (rightTerm k A Q p)).mapHomologicalComplex (.up ℤ)).map f)

@[simp] theorem columnMap_f (p n : ℤ) :
    ((columnMap k A Q f p).f n).hom = inputMap k A Q f p (n + -p) := by
  apply BalancedTensor.ext
  intro x y
  rfl

/-- The horizontal tensor differential is natural in the arbitrary input complex. -/
theorem horizontal_inputMap (n p p' : ℤ) (h : p+1=p') :
    (horizontal k A Q Z' n p p' h).comp (inputMap k A Q f p (n + -p)) =
      (inputMap k A Q f p' ((n+1) + -p')).comp (horizontal k A Q Z n p p' h) := by
  unfold horizontal inputMap map
  erw [bimap_comp,bimap_comp,LinearMap.comp_id]
  congr 1
  have hn := inputMap_transport A f (show n + -p = (n+1) + -p' by omega)
  exact congrArg ModuleCat.Hom.hom hn.symm

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

theorem entry_inputMap (n : ℤ) (i j : Fin l) :
    (entry k A Q Z' p n i j).comp (inputMap k A Q f (p i) (n + -(p i))) =
      (inputMap k A Q f (p j) ((n+1) + -(p j))).comp (entry k A Q Z p n i j) := by
  unfold entry
  split_ifs with h
  · exact horizontal_inputMap k A Q f n (p i) (p j) h
  · simp only [LinearMap.zero_comp,LinearMap.comp_zero]

/-- The full horizontal matrix commutes with the actual input map. -/
theorem matrix_inputMap (n : ℤ) :
    (matrix k A Q Z' p n).comp
      (FiniteColumnComplex.componentMap (columns k A Q Z p) (columns k A Q Z' p)
        (fun i => columnMap k A Q f (p i)) n) =
    (FiniteColumnComplex.componentMap (columns k A Q Z p) (columns k A Q Z' p)
      (fun i => columnMap k A Q f (p i)) (n+1)).comp (matrix k A Q Z p n) := by
  apply LinearMap.ext
  intro z
  funext j
  change matrix k A Q Z' p n
    (FiniteColumnComplex.componentMap (columns k A Q Z p) (columns k A Q Z' p)
      (fun i => columnMap k A Q f (p i)) n z) j =
      ((columnMap k A Q f (p j)).f (n+1)).hom (matrix k A Q Z p n z j)
  simp only [matrix_apply,FiniteColumnComplex.componentMap_apply,columnMap_f]
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun g => g (z i)) (entry_inputMap k A Q f p n i j)
end LittleFinitistic.ComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorTotalFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.ComplexTensor.map_id_left _root_.OAI.LittleFinitistic.FiniteColumnComplex.coneEquiv_coordinate _root_.OAI.LittleFinitistic.FiniteColumnComplex.coneEquiv_symm_coordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
namespace FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K L : Fin l → CochainComplex (ModuleCat.{u} R) ℤ) (f : ∀ i, K i ⟶ L i)

theorem diagonal_componentMap (n : ℤ) :
    (diagonal L n).comp (componentMap K L f n) = (componentMap K L f (n+1)).comp (diagonal K n) := by
  apply LinearMap.ext
  intro z
  funext i
  exact congrArg (fun g => g.hom (z i)) ((f i).comm n (n+1))

end FiniteColumnComplex
namespace ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable {Z Z' Z'' : CochainComplex (ModuleCat.{u} A) ℤ}
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- Actual tensor total applied to an arbitrary chain map of input complexes. -/
def finiteTotalMap (f : Z ⟶ Z') : finiteTotal k A Q Z p hp ⟶ finiteTotal k A Q Z' p hp :=
  FiniteColumnComplex.complexMap (columns k A Q Z p) (columns k A Q Z' p)
    (FiniteColumnComplex.totalDifferential _ (tensorHorizontal k A Q Z p hp))
    (FiniteColumnComplex.totalDifferential _ (tensorHorizontal k A Q Z' p hp))
    (fun i => columnMap k A Q f (p i)) (by
      intro n
      change (FiniteColumnComplex.diagonal (columns k A Q Z' p) n + matrix k A Q Z' p n).comp _ =
        (FiniteColumnComplex.componentMap _ _ (fun i => columnMap k A Q f (p i)) (n+1)).comp
          (FiniteColumnComplex.diagonal (columns k A Q Z p) n + matrix k A Q Z p n)
      rw [LinearMap.add_comp,LinearMap.comp_add,
        FiniteColumnComplex.diagonal_componentMap,matrix_inputMap])

@[simp] theorem finiteTotalMap_apply (f : Z ⟶ Z') (n : ℤ)
    (z : FiniteColumnComplex.term (columns k A Q Z p) n) (i : Fin l) :
    ((finiteTotalMap k A Q p hp f).f n).hom z i = inputMap k A Q f (p i) (n + -(p i)) (z i) := by
  change ((columnMap k A Q f (p i)).f n).hom (z i) = _
  rw [columnMap_f]
  rfl

@[simp] theorem inputMap_id (p q : ℤ) : inputMap k A Q (𝟙 Z) p q = LinearMap.id := by
  apply BalancedTensor.ext
  intro x y
  rfl

@[simp] theorem inputMap_comp (f : Z ⟶ Z') (g : Z' ⟶ Z'') (p q : ℤ) :
    (inputMap k A Q g p q).comp (inputMap k A Q f p q) = inputMap k A Q (f ≫ g) p q := by
  apply BalancedTensor.ext
  intro x y
  rfl

end ComplexTensor
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorTotalQuasiIso
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
namespace ComplexTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z')

/-- Every shifted projective tensor column preserves arbitrary quasi-isomorphisms. -/
theorem columnMap_quasiIso (p : ℤ) [Module.Projective Aᵐᵒᵖ (rightTerm k A Q p)] [QuasiIso f] :
    QuasiIso (columnMap k A Q f p) := by
  have ht := BalancedTensor.projectiveTensor_quasiIso k A (rightTerm k A Q p) f
  let := ht
  exact inferInstanceAs (QuasiIso ((shiftFunctor _ (-p)).map
    (((BalancedTensor.fixedTensorFunctor k A (rightTerm k A Q p)).mapHomologicalComplex
      (.up ℤ)).map f)))

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The actual signed finite tensor functor preserves quasi-isomorphisms of arbitrary complexes. -/
theorem finiteTotalMap_quasiIso [∀ i, Module.Projective Aᵐᵒᵖ (rightTerm k A Q (p i))] [QuasiIso f] :
    QuasiIso (finiteTotalMap k A Q p hp f) := by
  let (i : Fin l) := columnMap_quasiIso k A Q f (p i)
  unfold finiteTotalMap
  exact FiniteColumnComplex.complexMap_quasiIso _ _ _ _ _ _

end ComplexTensor
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
attribute [local instance] BimoduleBalancedTensor.inputEnveloping
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

abbrev Term (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ) (p q : ℤ) :=
  BimoduleBalancedTensor.Tensor k B (P.X p) (ComplexTensor.leftTerm k B Z q)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleInputFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk
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

abbrev InputTensor (N : ModuleCat.{u} B) :=
  BimoduleBalancedTensor.Tensor k B M (BalancedTensor.ScalarLeftModule k B N)

def inputModuleMap {N N' : ModuleCat.{u} B} (f : N ⟶ N') :
    InputTensor k B M N →ₗ[B] InputTensor k B M N' where
  __ := (@BalancedTensor.mapRightTo k B (BimoduleBalancedTensor.Input k B M)
    (BalancedTensor.ScalarLeftModule k B N) (BalancedTensor.ScalarLeftModule k B N')
    _ _ _ _ _ _ _ _ _ (BalancedTensor.scalarLeftTower k B N)
    _ _ _ (BalancedTensor.scalarLeftTower k B N') f.hom).toAddMonoidHom
  map_smul' b x := by
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy => simp_all [smul_add]

/-- Tensor by one genuine bimodule, varying the left-module input and retaining the outside action. -/
def inputFunctor : ModuleCat.{u} B ⥤ ModuleCat.{u} B where
  obj N := ModuleCat.of B (InputTensor k B M N)
  map f := ModuleCat.ofHom (inputModuleMap k B M f)
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarTensorComparison
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.DerivedBar.BimoduleTensor.leftMap_quotient _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleBarComparison
open ExternalTensor.Section4 BimoduleTotal
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B))

abbrev Actions := BimoduleBalancedTensor.Input k B M
attribute [local instance] BimoduleBalancedTensor.inputEnveloping

instance outsideModule : Module B (Actions k B M) :=
  Module.compHom (Actions k B M) (Algebra.TensorProduct.includeLeft : B →ₐ[k] Enveloping k B).toRingHom

instance outsideComm : SMulCommClass B Bᵐᵒᵖ (Actions k B M) where
  smul_comm b r x := by
    change ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (((1 : B) ⊗ₜ[k] r) • (x : M))) =
      (((1 : B) ⊗ₜ[k] r) • ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (x : M)))
    rw [← mul_smul,← mul_smul]
    congr 1
    simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

instance outsideTower : IsScalarTower k B (Actions k B M) :=
  IsScalarTower.of_algebraMap_smul (by
    intro c x
    change (Algebra.TensorProduct.includeLeft : B →ₐ[k] Enveloping k B) (algebraMap k B c) • (x : M) =
      (Algebra.TensorProduct.includeRight : Bᵐᵒᵖ →ₐ[k] Enveloping k B) (algebraMap k Bᵐᵒᵖ c) • (x : M)
    rw [AlgHom.commutes,AlgHom.commutes])

variable (N : ModuleCat.{u} B)

attribute [local instance] OAI.LittleFinitistic.BimoduleBarComparison.instModuleCarrier_solutions
attribute [local instance] OAI.LittleFinitistic.BimoduleBarComparison.instIsScalarTowerCarrier_solutions
abbrev BarTensor := DerivedBar.BimoduleTensor.tensor k B (Actions k B M) N

/-- The field-linear balanced universal map to the bar worker's B-linear quotient. -/
def toBarLinear : InputTensor k B M N →ₗ[k] BarTensor k B M N :=
  BalancedTensor.lift
    ((TensorProduct.mk k (Actions k B M) (BalancedTensor.ScalarLeftModule k B N)).compr₂
      ((DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N).restrictScalars k))
    (by intro b m n; exact DerivedBar.BimoduleTensor.balanced k B (Actions k B M) N m b n)

/-- This comparison retains the actual outside B-action. -/
def toBar : InputTensor k B M N →ₗ[B] BarTensor k B M N where
  __ := (toBarLinear k B M N).toAddMonoidHom
  map_smul' b x := by
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n =>
      change DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N ((b • m) ⊗ₜ[k] n) =
        b • DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N (m ⊗ₜ[k] n)
      exact (DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N).map_smul b
        ((m : Actions k B M) ⊗ₜ[k] (n : N))
    | ha x y hx hy => simp_all [smul_add]

/-- The reverse unbalanced tensor map is B-linear before passing to the quotient. -/
def fromBarUnbalanced : Actions k B M ⊗[k] (BalancedTensor.ScalarLeftModule k B N) →ₗ[B]
    InputTensor k B M N where
  __ := (TensorProduct.lift (BalancedTensor.mk k B (Actions k B M)
    (BalancedTensor.ScalarLeftModule k B N))).toAddMonoidHom
  map_smul' b x := by
    induction x using OAI.tensorInductionOn with
    | tmul m n => rfl
    | add x y hx hy => simp_all [smul_add]

def fromBar : BarTensor k B M N →ₗ[B] InputTensor k B M N :=
  (DerivedBar.BimoduleTensor.relations k B (Actions k B M) N).liftQ
    (fromBarUnbalanced k B M N) (by
      apply Submodule.span_le.mpr
      rintro z ⟨m,b,n,rfl⟩
      change fromBarUnbalanced k B M N ((MulOpposite.op b • m) ⊗ₜ[k] n - m ⊗ₜ[k] (b • n)) = 0
      exact ((fromBarUnbalanced k B M N).map_sub _ _).trans
        (sub_eq_zero.mpr (BalancedTensor.balance b m n)))

/-- The two independently defined balanced quotients are naturally B-linearly isomorphic. -/
def tensorEquiv : InputTensor k B M N ≃ₗ[B] BarTensor k B M N where
  __ := toBar k B M N
  invFun := fromBar k B M N
  left_inv x := by
    change fromBar k B M N (toBar k B M N x) = x
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy => simp only [map_add,hx,hy]
  right_inv x := by
    change toBar k B M N (fromBar k B M N x) = x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change toBar k B M N (fromBar k B M N
        (DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N x)) =
          DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N x
      induction x using OAI.tensorInductionOn with
      | tmul m n => rfl
      | add x y hx hy =>
        exact (((toBar k B M N).comp ((fromBar k B M N).comp
          (DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N))).map_add x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- Agreement with the exact ordinary bimodule functor used by DerivedBar. -/
def tensorFunctorIso : inputFunctor k B M ≅
    DerivedBar.BimoduleTensor.tensorFunctor k B (Actions k B M) :=
  NatIso.ofComponents (fun N => (tensorEquiv k B M N).toModuleIso) (by
    intro N N' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => exact (map_zero _).trans (map_zero _).symm
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm))
end LittleFinitistic.BimoduleBarComparison

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalFunctor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

abbrev TotalTerm (n : ℤ) := ∀ i : Fin l, Term k B P Z (p i) (n + -(p i))
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationModule
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator
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

@[simp] theorem arrowAction_basis (i : Fin (d+1)) :
    X.arrowAction (basis i) = Fin.cases 1 X.generator i := by
  classical
  simp [arrowAction, basis, Pi.single_apply]

def rawPathAction : Paths k d →ₗ[k] Module.End k Y :=
  TensorProduct.lift ((LinearMap.mul k (Module.End k Y)).compl₁₂ X.arrowAction X.arrowAction)

@[simp] theorem rawPathAction_tmul (w v : Arrows k d) :
    X.rawPathAction (w ⊗ₜ[k] v) = X.arrowAction w * X.arrowAction v := rfl

end Representation
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryAssociativeTensorModules
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u

variable (k A B M N Z : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z] [IsScalarTower k B Z]

namespace RightTensor
instance instIsScalarTowerMulOpposite : IsScalarTower k Bᵐᵒᵖ (RightTensor k A B M N) where
  smul_assoc r b z := by
    change action k A B M N (r • b) z = r • action k A B M N b z
    rw [map_smul]
    rfl

end RightTensor

namespace LeftTensor
instance instIsScalarTower : IsScalarTower k A (LeftTensor k B A N Z) where
  smul_assoc r a z := by
    change action k A B N Z (r • a) z = r • action k A B N Z a z
    rw [map_smul]
    rfl

end LeftTensor
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryAssociativityNaturality
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u
variable {k A B M M' N Z Z' : Type u} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z] [IsScalarTower k B Z]
variable [AddCommGroup Z'] [Module k Z'] [Module B Z'] [IsScalarTower k B Z']

/-- A map of the last left module retains the middle bimodule's left A-action. -/
def LeftTensor.mapLast (g : Z →ₗ[B] Z') : LeftTensor k B A N Z →ₗ[A] LeftTensor k B A N Z' where
  __ := (BalancedTensor.mapRightTo (k := k) (M := N) g).toAddHom
  map_smul' a x := by
    let F : LeftTensor k B A N Z →ₗ[k] LeftTensor k B A N Z' :=
      BalancedTensor.mapRightTo (k := k) (M := N) g
    have h : F.comp (LeftTensor.action k A B N Z a) =
        (LeftTensor.action k A B N Z' a).comp F := by
      apply BalancedTensor.ext
      intro n z
      rfl
    exact congrArg (fun g => g x) h

end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTwoSidedTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic
universe u

variable (k A S T M N : Type u) [Field k] [Ring A] [Algebra k A] [Ring S] [Algebra k S]
  [Ring T] [Algebra k T]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module S M] [IsScalarTower k S M] [SMulCommClass S Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [Module T N] [IsScalarTower k T N] [SMulCommClass T A N]

namespace TwoSidedTensor
instance instModuleTensorProduct : Module (S ⊗[k] T) (TwoSidedTensor k A S T M N) := Module.compHom _ (action k A S T M N).toRingHom
instance instIsScalarTowerTensorProduct : IsScalarTower k (S ⊗[k] T) (TwoSidedTensor k A S T M N) where
  smul_assoc r x z := by
    change action k A S T M N (r • x) z = r • action k A S T M N x z
    rw [map_smul]
    rfl

def mk : M →ₗ[k] N →ₗ[k] TwoSidedTensor k A S T M N := BalancedTensor.mk k A M N

@[simp] theorem tmul_smul_mk (s : S) (t : T) (m : M) (n : N) :
    (s ⊗ₜ[k] t) • mk k A S T M N m n = mk k A S T M N (s • m) (t • n) := rfl

variable {k A S T M N}
variable {M' : Type u} [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
  [Module S M'] [IsScalarTower k S M'] [SMulCommClass S Aᵐᵒᵖ M']

/-- Functoriality of the actual tensor with both outside actions retained. -/
def map (f : M →ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m) :
    TwoSidedTensor k A S T M N →ₗ[S ⊗[k] T] TwoSidedTensor k A S T M' N where
  __ := (BalancedTensor.mapLeft (k := k) N f).toAddHom
  map_smul' x z := by
    let F : TwoSidedTensor k A S T M N →ₗ[k] TwoSidedTensor k A S T M' N :=
      BalancedTensor.mapLeft (k := k) N f
    have h : F.comp (action k A S T M N x) = (action k A S T M' N x).comp F := by
      induction x using OAI.tensorInductionOn with
      | tmul s t =>
        apply BalancedTensor.ext
        intro m n
        change BalancedTensor.mk k A M' N (f (s • m)) (t • n) =
          BalancedTensor.mk k A M' N (s • f m) (t • n)
        rw [hf]
      | add x y hx hy =>
        simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]
    exact congrArg (fun g => g z) h

@[simp] theorem map_mk (f : M →ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m) (m : M) (n : N) :
    map (T := T) (N := N) f hf (mk k A S T M N m n) = mk k A S T M' N (f m) n := rfl

end TwoSidedTensor
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTensorFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic
universe u
variable (k S A T N : Type u) [Field k] [Ring S] [Ring A] [Ring T]
  [Algebra k S] [Algebra k A] [Algebra k T]
variable [AddCommGroup N] [Module k N] [Module A N] [Module T N]
  [IsScalarTower k A N] [IsScalarTower k T N] [SMulCommClass T A N]

/-- Actual ordinary tensor with a fixed bimodule, preserving both outside actions. -/
def bimoduleTensorFunctor : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ) ⥤ ModuleCat.{u} (S ⊗[k] T) where
  obj M := ModuleCat.of _ (TwoSidedTensor k A S T (BimoduleCoefficients k S A M) N)
  map f := ModuleCat.ofHom (TwoSidedTensor.map (T := T) (N := N)
    (BimoduleCoefficients.map k S A f) (BimoduleCoefficients.map_left k S A f))
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m n
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m n
    rfl

instance bimoduleTensorFunctor_additive : (bimoduleTensorFunctor k S A T N).Additive where
  map_add {M M'} {f g} := by
    dsimp only [bimoduleTensorFunctor]
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m n
    exact congrArg (fun h => h n)
      ((BalancedTensor.mk k A (BimoduleCoefficients k S A M') N).map_add (f.hom m) (g.hom m))
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryLeftTensorMaps
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.LeftTensor
universe u
variable {k A S M M' N N' : Type u} [Field k] [Ring A] [Ring S] [Algebra k A] [Algebra k S]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module S M] [IsScalarTower k S M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
  [Module S M'] [IsScalarTower k S M'] [SMulCommClass S Aᵐᵒᵖ M']
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']

/-- The actual balanced bimap retains the outside left action. -/
def bimap (f : M →ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m)
    (g : N →ₗ[A] N') : LeftTensor k A S M N →ₗ[S] LeftTensor k A S M' N' where
  __ := (BalancedTensor.bimap (k := k) f g).toAddHom
  map_smul' s z := by
    change BalancedTensor.bimap (k := k) f g (action k S A M N s z) =
      action k S A M' N' s (BalancedTensor.bimap (k := k) f g z)
    induction z using BalancedTensor.induction_on with
    | hz =>
      exact ((BalancedTensor.bimap (k := k) f g).comp (action k S A M N s)).map_zero.trans
        (((action k S A M' N' s).comp (BalancedTensor.bimap (k := k) f g)).map_zero).symm
    | ht m n =>
      change BalancedTensor.mk k A M' N' (f (s • m)) (g n) =
        BalancedTensor.mk k A M' N' (s • f m) (g n)
      rw [hf]
    | ha x y hx hy =>
      exact (((BalancedTensor.bimap (k := k) f g).comp (action k S A M N s)).map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans
          (((action k S A M' N' s).comp (BalancedTensor.bimap (k := k) f g)).map_add x y).symm)

@[simp] theorem bimap_mk (f : M →ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m)
    (g : N →ₗ[A] N') (m : M) (n : N) :
    bimap f hf g (mk k S A M N m n) = mk k S A M' N' (f m) (g n) := rfl
end LittleFinitistic.LeftTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorRightRestriction
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.TwoSidedTensor
universe u
variable (k A B S M N : Type u) [Field k] [Ring A] [Ring B] [Ring S]
  [Algebra k A] [Algebra k B] [Algebra k S]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module S M] [IsScalarTower k S M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]

attribute [local instance] OAI.LittleFinitistic.TwoSidedTensor.instSMulCommClassMulOpposite
/-- The actual outside right action obtained by restricting the enveloping action. -/
abbrev rightRestriction : ModuleCat.{u} Bᵐᵒᵖ :=
  (ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := Bᵐᵒᵖ)).toRingHom).obj
    (ModuleCat.of (S ⊗[k] Bᵐᵒᵖ) (TwoSidedTensor k A S Bᵐᵒᵖ M N))

/-- The one-sided right tensor action equals the restriction of the genuine two-sided action. -/
def rightActionEquiv : RightTensor k A B M N ≃ₗ[Bᵐᵒᵖ] rightRestriction k A B S M N where
  toFun x := x
  invFun x := x
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' r x := by
    let F : BalancedTensor.Tensor k A M N →ₗ[k] BalancedTensor.Tensor k A M N :=
      RightTensor.action k A B M N r
    let G : BalancedTensor.Tensor k A M N →ₗ[k] BalancedTensor.Tensor k A M N :=
      TwoSidedTensor.action k A S Bᵐᵒᵖ M N ((1:S) ⊗ₜ[k] r)
    have h : F = G := by
      apply BalancedTensor.ext
      intro m n
      change BalancedTensor.mk k A M N m (r • n) = BalancedTensor.mk k A M N ((1:S) • m) (r • n)
      rw [one_smul]
    exact congrArg (fun f => f x) h

end LittleFinitistic.TwoSidedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleAssociativity
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleAssociativity
universe u
variable (k S A B M N Z : Type u) [Field k] [Ring S] [Ring A] [Ring B]
  [Algebra k S] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z] [IsScalarTower k B Z]

attribute [local instance] OAI.LittleFinitistic.BimoduleAssociativity.instSMulCommClassMulOpposite_solutions
abbrev coefficient := BimoduleCoefficients k S B
  (ModuleCat.of (S ⊗[k] Bᵐᵒᵖ) (TwoSidedTensor k A S Bᵐᵒᵖ M N))
abbrev source := LeftTensor k B S (coefficient k S A B M N) Z
abbrev target := LeftTensor k A S M (LeftTensor k B A N Z)

def scalarEquiv : source k S A B M N Z ≃ₗ[k] target k S A B M N Z := by
  let e : coefficient k S A B M N ≃ₗ[Bᵐᵒᵖ] RightTensor k A B M N :=
    (TwoSidedTensor.rightActionEquiv k A B S M N).symm
  exact (BalancedTensor.congr (k := k) e (LinearEquiv.refl B Z)).trans
    (BalancedAssociativity.equivalence k A B M N Z)

@[simp] theorem scalarEquiv_mk (m : M) (n : N) (z : Z) :
    scalarEquiv k S A B M N Z (LeftTensor.mk k S B (coefficient k S A B M N) Z
      (TwoSidedTensor.mk k A S Bᵐᵒᵖ M N m n) z) =
    LeftTensor.mk k S A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z) := rfl

theorem coefficient_smul_mk (s : S) (m : M) (n : N) :
    s • (show coefficient k S A B M N from TwoSidedTensor.mk k A S Bᵐᵒᵖ M N m n) =
    (show coefficient k S A B M N from TwoSidedTensor.mk k A S Bᵐᵒᵖ M N (s • m) n) := by
  change (s ⊗ₜ[k] (1:Bᵐᵒᵖ)) • TwoSidedTensor.mk k A S Bᵐᵒᵖ M N m n = _
  rw [TwoSidedTensor.tmul_smul_mk,one_smul]

theorem scalarEquiv_smul_mk (s : S) (m : M) (n : N) (z : Z) :
    scalarEquiv k S A B M N Z
        (s • LeftTensor.mk k S B (coefficient k S A B M N) Z
          (show coefficient k S A B M N from TwoSidedTensor.mk k A S Bᵐᵒᵖ M N m n) z) =
      s • scalarEquiv k S A B M N Z
        (LeftTensor.mk k S B (coefficient k S A B M N) Z
          (show coefficient k S A B M N from TwoSidedTensor.mk k A S Bᵐᵒᵖ M N m n) z) := by
  erw [LeftTensor.smul_mk, coefficient_smul_mk]
  exact (scalarEquiv_mk k S A B M N Z (s • m) n z).trans
    ((LeftTensor.smul_mk k S A M (LeftTensor k B A N Z) s m
      (LeftTensor.mk k A B N Z n z)).symm.trans
        (congrArg (fun y => s • y) (scalarEquiv_mk k S A B M N Z m n z).symm))

/-- Ordinary balanced associativity retains the actual outside left action. -/
def equivalence : source k S A B M N Z ≃ₗ[S] target k S A B M N Z where
  __ := (scalarEquiv k S A B M N Z).toAddEquiv
  map_smul' s x := by
    let e := (scalarEquiv k S A B M N Z).toLinearMap
    let L := e.comp (LeftTensor.action k S B (coefficient k S A B M N) Z s)
    let R := (LeftTensor.action k S A M (LeftTensor k B A N Z) s).comp e
    have h : L = R := by
      apply BalancedTensor.ext
      intro y z
      let Lz : BalancedTensor.Tensor k A M N →+ target k S A B M N Z :=
        (L.comp ((LeftTensor.mk k S B (coefficient k S A B M N) Z).flip z)).toAddMonoidHom
      let Rz : BalancedTensor.Tensor k A M N →+ target k S A B M N Z :=
        (R.comp ((LeftTensor.mk k S B (coefficient k S A B M N) Z).flip z)).toAddMonoidHom
      have hz : Lz = Rz := by
        apply AddMonoidHom.ext
        intro y
        induction y using BalancedTensor.induction_on with
        | hz => exact Lz.map_zero.trans Rz.map_zero.symm
        | ha x y hx hy =>
          exact (Lz.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (Rz.map_add x y).symm)
        | ht m n => exact scalarEquiv_smul_mk k S A B M N Z s m n z
      exact congrArg (fun f => f y) hz
    exact congrArg (fun f => f x) h

end LittleFinitistic.BimoduleAssociativity

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTensorTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)

abbrev term (p q : ℤ) := LeftTensor k A S (BimoduleCoefficients k S A (Q.X p)) (ComplexTensor.leftTerm k A Z q)

/-- Both actual term maps with the outside left action retained. -/
def map {p p' q q' : ℤ} (f : Q.X p ⟶ Q.X p') (g : Z.X q ⟶ Z.X q') :
    term k S A Q Z p q →ₗ[S] term k S A Q Z p' q' :=
  LeftTensor.bimap (BimoduleCoefficients.map k S A f) (BimoduleCoefficients.map_left k S A f) g.hom

/-- Forgetting the outside action gives exactly the previous balanced tensor term. -/
def forgetEquiv (p q : ℤ) : term k S A Q Z p q ≃ₗ[k]
    ComplexTensor.term k A (rightComplex k S A Q) Z p q := by
  let e : BimoduleCoefficients k S A (Q.X p) ≃ₗ[Aᵐᵒᵖ]
      ComplexTensor.rightTerm k A (rightComplex k S A Q) p := LinearEquiv.refl _ _
  exact BalancedTensor.congr (k := k) e (LinearEquiv.refl A (ComplexTensor.leftTerm k A Z q))

/-- The retained-action map has precisely the same underlying balanced map. -/
theorem forget_map {p p' q q' : ℤ} (f : Q.X p ⟶ Q.X p') (g : Z.X q ⟶ Z.X q') :
    (forgetEquiv k S A Q Z p' q').toLinearMap.comp ((map k S A Q Z f g).restrictScalars k) =
      (ComplexTensor.map k A (rightComplex k S A Q) Z
        ((ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := Aᵐᵒᵖ)).toRingHom).map f) g).comp
        (forgetEquiv k S A Q Z p q).toLinearMap := by
  apply BalancedTensor.ext
  intro x y
  rfl
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryLeftTensorCongruence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.LeftTensor
universe u
variable {k A S M M' N N' : Type u} [Field k] [Ring A] [Ring S] [Algebra k A] [Algebra k S]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module S M] [IsScalarTower k S M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
  [Module S M'] [IsScalarTower k S M'] [SMulCommClass S Aᵐᵒᵖ M']
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']

/-- Actual balanced tensor congruence retaining the outside left action. -/
def congr (f : M ≃ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m)
    (g : N ≃ₗ[A] N') : LeftTensor k A S M N ≃ₗ[S] LeftTensor k A S M' N' where
  __ := bimap f.toLinearMap hf g.toLinearMap
  invFun := (BalancedTensor.congr (k := k) f g).symm
  left_inv := (BalancedTensor.congr (k := k) f g).left_inv
  right_inv := (BalancedTensor.congr (k := k) f g).right_inv
end LittleFinitistic.LeftTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryMiddleTensorFunctors
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (k A B N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]

/-- Tensor by the fixed middle bimodule, retaining its actual left action. -/
def middleLeftFunctor : ModuleCat.{u} B ⥤ ModuleCat.{u} A where
  obj Z := ModuleCat.of A (LeftTensor k B A N (BalancedTensor.ScalarLeftModule k B Z))
  map {Z Z'} g := ModuleCat.ofHom
    (LeftTensor.mapLast (k := k) (A := A) (N := N)
      (Z := BalancedTensor.ScalarLeftModule k B Z) (Z' := BalancedTensor.ScalarLeftModule k B Z') g.hom)
  map_id Z := by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro n z
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro n z
    rfl

instance middleLeftFunctor_additive : (middleLeftFunctor k A B N).Additive where
  map_add {Z Z'} {f g} := by
    dsimp only [middleLeftFunctor]
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro n z
    exact (BalancedTensor.mk k B N (BalancedTensor.ScalarLeftModule k B Z') n).map_add (f.hom z) (g.hom z)

/-- The genuine left tensor complex, with its left A-action. -/
def middleLeftComplex (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((middleLeftFunctor k A B N).mapHomologicalComplex (.up ℤ)).obj Z
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleAssociativeTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A B N : Type u) [Field k] [Ring S] [Ring A] [Ring B]
  [Algebra k S] [Algebra k A] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

attribute [local instance] OAI.LittleFinitistic.BimoduleComplexTensor.instSMulCommClassMulOpposite_solutions
abbrev middleBimoduleComplex := ((bimoduleTensorFunctor k S A Bᵐᵒᵖ N).mapHomologicalComplex (.up ℤ)).obj Q

/-- Associativity on actual cochain terms, retaining the outside S-action. -/
def associativeTermEquiv (p q : ℤ) :
    term k S B (middleBimoduleComplex k S A B N Q) Z p q ≃ₗ[S]
      term k S A Q (middleLeftComplex k A B N Z) p q := by
  let eZ : LeftTensor k B A N (ComplexTensor.leftTerm k B Z q) ≃ₗ[A]
      ComplexTensor.leftTerm k A (middleLeftComplex k A B N Z) q := LinearEquiv.refl _ _
  exact (BimoduleAssociativity.equivalence k S A B (BimoduleCoefficients k S A (Q.X p)) N
    (ComplexTensor.leftTerm k B Z q)).trans
    (LeftTensor.congr (LinearEquiv.refl Aᵐᵒᵖ (BimoduleCoefficients k S A (Q.X p))) (fun _ _ => rfl) eZ)

/-- Associativity commutes with both actual cochain-term maps. -/
theorem associativeTermEquiv_map {p p' q q' : ℤ} (f : Q.X p ⟶ Q.X p') (g : Z.X q ⟶ Z.X q') :
    (associativeTermEquiv k S A B N Q Z p' q').toLinearMap.comp
      (map k S B (middleBimoduleComplex k S A B N Q) Z ((bimoduleTensorFunctor k S A Bᵐᵒᵖ N).map f) g) =
    (map k S A Q (middleLeftComplex k A B N Z) f ((middleLeftFunctor k A B N).map g)).comp
      (associativeTermEquiv k S A B N Q Z p q).toLinearMap := by
  let F := (associativeTermEquiv k S A B N Q Z p' q').toLinearMap.comp
    (map k S B (middleBimoduleComplex k S A B N Q) Z ((bimoduleTensorFunctor k S A Bᵐᵒᵖ N).map f) g)
  let G := (map k S A Q (middleLeftComplex k A B N Z) f ((middleLeftFunctor k A B N).map g)).comp
    (associativeTermEquiv k S A B N Q Z p q).toLinearMap
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  let j := (LeftTensor.mk k S B
    (BimoduleCoefficients k S B ((middleBimoduleComplex k S A B N Q).X p))
    (ComplexTensor.leftTerm k B Z q)).flip z
  let L : BalancedTensor.Tensor k A (BimoduleCoefficients k S A (Q.X p)) N →+
      term k S A Q (middleLeftComplex k A B N Z) p' q' :=
    ((F.restrictScalars k).comp j).toAddMonoidHom
  let R : BalancedTensor.Tensor k A (BimoduleCoefficients k S A (Q.X p)) N →+
      term k S A Q (middleLeftComplex k A B N Z) p' q' :=
    ((G.restrictScalars k).comp j).toAddMonoidHom
  have h : L = R := by
    apply AddMonoidHom.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => exact L.map_zero.trans R.map_zero.symm
    | ht m n => rfl
    | ha x y hx hy =>
      exact (L.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)
  exact congrArg (fun f => f x) h

end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTensorTotal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

abbrev totalTerm (n : ℤ) := ∀ i : Fin l, term k S A Q Z (p i) (n + -(p i))

def forgetTotalEquiv (n : ℤ) : totalTerm k S A Q Z p n ≃ₗ[k]
    FiniteColumnComplex.term (ComplexTensor.columns k A (rightComplex k S A Q) Z p) n :=
  LinearEquiv.piCongrRight (fun i => forgetEquiv k S A Q Z (p i) (n + -(p i)))

/-- The horizontal arrow map retains its left action and exact degree transport. -/
def entry (n : ℤ) (i j : Fin l) : term k S A Q Z (p i) (n + -(p i)) →ₗ[S]
    term k S A Q Z (p j) ((n+1) + -(p j)) :=
  if h : p i + 1 = p j then map k S A Q Z (Q.d (p i) (p j))
    (eqToHom (congrArg Z.X (by omega))) else 0

/-- The actual signed differential, now linear for the outside algebra. -/
def differential (n : ℤ) : totalTerm k S A Q Z p n →ₗ[S] totalTerm k S A Q Z p (n+1) :=
  LinearMap.pi (fun j =>
    ((-(p j)).negOnePow • map k S A Q Z (𝟙 (Q.X (p j)))
      (Z.d (n + -(p j)) ((n+1) + -(p j)))).comp (LinearMap.proj j) +
    ∑ i : Fin l, (entry k S A Q Z p n i j).comp (LinearMap.proj i))

theorem forget_entry (n : ℤ) (i j : Fin l) (z : term k S A Q Z (p i) (n + -(p i))) :
    forgetEquiv k S A Q Z (p j) ((n+1) + -(p j)) (entry k S A Q Z p n i j z) =
      ComplexTensor.entry k A (rightComplex k S A Q) Z p n i j
        (forgetEquiv k S A Q Z (p i) (n + -(p i)) z) := by
  unfold entry ComplexTensor.entry
  split_ifs with h
  · exact congrArg (fun f => f z) (forget_map k S A Q Z (Q.d (p i) (p j))
      (eqToHom (congrArg Z.X (show n + -(p i) = (n+1) + -(p j) by omega))))
  · exact map_zero _

/-- Forgetting the outside action gives exactly the previously verified signed differential. -/
theorem forget_differential (n : ℤ) (z : totalTerm k S A Q Z p n) :
    forgetTotalEquiv k S A Q Z p (n+1) (differential k S A Q Z p n z) =
      (FiniteColumnComplex.totalDifferential (ComplexTensor.columns k A (rightComplex k S A Q) Z p)
        (ComplexTensor.tensorHorizontal k A (rightComplex k S A Q) Z p hp)).d n
        (forgetTotalEquiv k S A Q Z p n z) := by
  funext j
  change forgetEquiv k S A Q Z (p j) ((n+1) + -(p j))
      ((differential k S A Q Z p n z) j) = _
  simp only [forgetTotalEquiv,differential,
    LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,FiniteColumnComplex.totalDifferential,ComplexTensor.tensorHorizontal,
    FiniteColumnComplex.diagonal_apply,Pi.add_apply,ComplexTensor.matrix_apply]
  simp only [map_add,map_sum,LinearMap.smul_apply,ComplexTensor.column_d]
  apply congrArg₂ (· + ·)
  · change forgetEquiv k S A Q Z (p j) ((n+1) + -(p j))
        ((((-(p j)).negOnePow : ℤ)) •
          (map k S A Q Z (𝟙 (Q.X (p j))) (Z.d (n + -(p j)) ((n+1) + -(p j))) (z j))) =
      (((-(p j)).negOnePow : ℤ)) •
        (ComplexTensor.map k A (rightComplex k S A Q) Z (𝟙 ((rightComplex k S A Q).X (p j)))
          (Z.d (n + -(p j)) ((n+1) + -(p j)))
          (forgetEquiv k S A Q Z (p j) (n + -(p j)) (z j)))
    rw [map_zsmul]
    congr 1
    exact congrArg (fun f => f (z j)) (forget_map k S A Q Z (𝟙 (Q.X (p j)))
      (Z.d (n + -(p j)) ((n+1) + -(p j))))
  · apply Finset.sum_congr rfl
    intro i _
    exact forget_entry k S A Q Z p n i j (z i)

end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTotalAssociativity
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A B N : Type u) [Field k] [Ring S] [Ring A] [Ring B]
  [Algebra k S] [Algebra k A] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

attribute [local instance] OAI.LittleFinitistic.BimoduleComplexTensor.instSMulCommClassMulOpposite_solutions_1
def associativeTotalEquiv (n : ℤ) :
    totalTerm k S B (middleBimoduleComplex k S A B N Q) Z p n ≃ₗ[S]
      totalTerm k S A Q (middleLeftComplex k A B N Z) p n :=
  LinearEquiv.piCongrRight (fun i => associativeTermEquiv k S A B N Q Z (p i) (n + -(p i)))

theorem associative_entry (n : ℤ) (i j : Fin l) :
    (associativeTermEquiv k S A B N Q Z (p j) ((n+1) + -(p j))).toLinearMap.comp
      (entry k S B (middleBimoduleComplex k S A B N Q) Z p n i j) =
    (entry k S A Q (middleLeftComplex k A B N Z) p n i j).comp
      (associativeTermEquiv k S A B N Q Z (p i) (n + -(p i))).toLinearMap := by
  unfold entry
  split_ifs with h
  · have he : n + -(p i) = (n+1) + -(p j) := by omega
    have hh := associativeTermEquiv_map k S A B N Q Z (Q.d (p i) (p j)) (eqToHom (congrArg Z.X he))
    have ht : (middleLeftFunctor k A B N).map (eqToHom (congrArg Z.X he)) =
        eqToHom (congrArg (middleLeftComplex k A B N Z).X he) := by
      generalize n + -(p i) = q at he ⊢
      generalize (n+1) + -(p j) = q' at he ⊢
      subst q'
      simp only [eqToHom_refl,CategoryTheory.Functor.map_id]
      rfl
    rw [ht] at hh
    exact hh
  · simp only [LinearMap.comp_zero,LinearMap.zero_comp]

theorem associative_vertical (n : ℤ) (i : Fin l) :
    (associativeTermEquiv k S A B N Q Z (p i) ((n+1) + -(p i))).toLinearMap.comp
      (map k S B (middleBimoduleComplex k S A B N Q) Z (𝟙 _)
        (Z.d (n + -(p i)) ((n+1) + -(p i)))) =
    (map k S A Q (middleLeftComplex k A B N Z) (𝟙 _)
      ((middleLeftComplex k A B N Z).d (n + -(p i)) ((n+1) + -(p i)))).comp
      (associativeTermEquiv k S A B N Q Z (p i) (n + -(p i))).toLinearMap := by
  have h := associativeTermEquiv_map k S A B N Q Z (𝟙 (Q.X (p i)))
    (Z.d (n + -(p i)) ((n+1) + -(p i)))
  rw [(bimoduleTensorFunctor k S A Bᵐᵒᵖ N).map_id] at h
  exact h

theorem associative_differential (n : ℤ)
    (z : totalTerm k S B (middleBimoduleComplex k S A B N Q) Z p n) :
    associativeTotalEquiv k S A B N Q Z p (n+1)
      (differential k S B (middleBimoduleComplex k S A B N Q) Z p n z) =
    differential k S A Q (middleLeftComplex k A B N Z) p n
      (associativeTotalEquiv k S A B N Q Z p n z) := by
  funext j
  simp only [associativeTotalEquiv,LinearEquiv.piCongrRight_apply,differential,
    LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,map_add,map_sum]
  apply congrArg₂ (· + ·)
  · change associativeTermEquiv k S A B N Q Z (p j) ((n+1) + -(p j))
        ((((-(p j)).negOnePow : ℤ)) •
          (map k S B (middleBimoduleComplex k S A B N Q) Z (𝟙 _)
            (Z.d (n + -(p j)) ((n+1) + -(p j))) (z j))) =
      (((-(p j)).negOnePow : ℤ)) •
        (map k S A Q (middleLeftComplex k A B N Z) (𝟙 _)
          ((middleLeftComplex k A B N Z).d (n + -(p j)) ((n+1) + -(p j))))
          (associativeTermEquiv k S A B N Q Z (p j) (n + -(p j)) (z j))
    rw [map_zsmul]
    congr 1
    exact congrArg (fun f => f (z j)) (associative_vertical k S A B N Q Z p n j)
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun f => f (z i)) (associative_entry k S A B N Q Z p n i j)

end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTotalMaps
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z')
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def termInputMap (r q : ℤ) : term k S A Q Z r q →ₗ[S] term k S A Q Z' r q :=
  LeftTensor.bimap (N := ComplexTensor.leftTerm k A Z q) (N' := ComplexTensor.leftTerm k A Z' q)
    (BimoduleCoefficients.map k S A (𝟙 (Q.X r)))
    (BimoduleCoefficients.map_left k S A (𝟙 (Q.X r))) (f.f q).hom

theorem termInputMap_id (Z : CochainComplex (ModuleCat.{u} A) ℤ) (r q : ℤ) :
    termInputMap k S A Q (𝟙 Z) r q = LinearMap.id := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x y
  rfl

theorem termInputMap_comp {Z'' : CochainComplex (ModuleCat.{u} A) ℤ} (g : Z' ⟶ Z'') (r q : ℤ) :
    termInputMap k S A Q (f ≫ g) r q =
      (termInputMap k S A Q g r q).comp (termInputMap k S A Q f r q) := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x y
  rfl

def totalInputMap (n : ℤ) : totalTerm k S A Q Z p n →ₗ[S] totalTerm k S A Q Z' p n :=
  LinearMap.pi (fun i => (termInputMap k S A Q f (p i) (n + -(p i))).comp (LinearMap.proj i))

end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_BalancedProjectiveLeft
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.ComplexTensor.column_d _root_.OAI.LittleFinitistic.ComplexTensor.finiteTotalMap_apply _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_comp _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_id _root_.OAI.LittleFinitistic.ComplexTensor.map_comp _root_.OAI.LittleFinitistic.ComplexTensor.map_id_left _root_.OAI.LittleFinitistic.ComplexTensor.map_zero_left _root_.OAI.LittleFinitistic.ComplexTensor.map_zero_right _root_.OAI.LittleFinitistic.ComplexTensor.matrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u
variable {k A M M' M'' N N' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable [AddCommGroup M''] [Module k M''] [Module Aᵐᵒᵖ M''] [IsScalarTower k Aᵐᵒᵖ M'']
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']

omit [IsScalarTower k Aᵐᵒᵖ M] in
theorem mapRightTo_split (i : N →ₗ[A] N') (p : N' →ₗ[A] N)
    (hp : p.comp i = LinearMap.id) (z : Tensor k A M N) :
    mapRightTo p (mapRightTo i z) = z := by
  induction z using BalancedTensor.induction_on with
  | hz => simp
  | ht m n =>
    rw [mapRightTo_mk,mapRightTo_mk]
    exact congrArg (mk k A M N m) (LinearMap.congr_fun hp n)
  | ha x y hx hy => simp only [map_add,hx,hy]

theorem leftTensor_exact_of_split (i : N →ₗ[A] N') (p : N' →ₗ[A] N)
    (hp : p.comp i = LinearMap.id) (f : M →ₗ[Aᵐᵒᵖ] M') (g : M' →ₗ[Aᵐᵒᵖ] M'')
    (h : Function.Exact f g)
    (h' : Function.Exact (mapLeft (k := k) N' f) (mapLeft (k := k) N' g)) :
    Function.Exact (mapLeft (k := k) N f) (mapLeft (k := k) N g) := by
  intro z
  constructor
  · intro hz
    have hi : mapLeft N' g (mapRightTo i z) = 0 := by
      rw [mapLeft_mapRightTo,hz,map_zero]
    obtain ⟨y,hy⟩ := (h' _).mp hi
    refine ⟨mapRightTo p y, ?_⟩
    rw [mapLeft_mapRightTo,hy,mapRightTo_split i p hp]
  · rintro ⟨y,rfl⟩
    induction y using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rw [mapLeft_mk,mapLeft_mk,(h (f m)).mpr ⟨m,rfl⟩,map_zero,LinearMap.zero_apply]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]

/-- Projectivity of the left input preserves every exact sequence in the right variable. -/
theorem projectiveLeftTensor_exact [Module.Projective A N]
    (f : M →ₗ[Aᵐᵒᵖ] M') (g : M' →ₗ[Aᵐᵒᵖ] M'') (h : Function.Exact f g) :
    Function.Exact (mapLeft (k := k) N f) (mapLeft (k := k) N g) := by
  obtain ⟨i,hi⟩ := (Module.projective_def' (R := A) (P := N)).mp inferInstance
  exact leftTensor_exact_of_split i (Finsupp.linearCombination A id) hi f g h
    (FreeLeft.tensor_exact (k := k) N f g h)
end LittleFinitistic.BalancedTensor

namespace LittleFinitistic.BimoduleBalancedTensor
open ExternalTensor.Section4
universe u
variable (k B N : Type u) [Field k] [Ring B] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module B N] [IsScalarTower k B N]
variable [Module.Projective B N]

/-- Exactness of tensoring genuine bimodules with a projective left module,
with the result still in B-Mod. -/
theorem projectiveInput_mapsExact
    (S : ShortComplex (ModuleCat.{u} (Enveloping k B))) (hS : S.Exact) :
    (S.map (functor k B N)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  have h : Function.Exact
      (((forgetRight k B).map S.f).hom : Input k B S.X₁ →ₗ[Bᵐᵒᵖ] Input k B S.X₂)
      (((forgetRight k B).map S.g).hom : Input k B S.X₂ →ₗ[Bᵐᵒᵖ] Input k B S.X₃) := by
    intro x
    constructor
    · exact (ShortComplex.moduleCat_exact_iff S).mp hS x
    · rintro ⟨y,rfl⟩
      exact congrArg (fun t => t.hom y) S.zero
  intro z hz
  exact ((BalancedTensor.projectiveLeftTensor_exact (k := k) (N := N)
    (((forgetRight k B).map S.f).hom : Input k B S.X₁ →ₗ[Bᵐᵒᵖ] Input k B S.X₂)
    (((forgetRight k B).map S.g).hom : Input k B S.X₂ →ₗ[Bᵐᵒᵖ] Input k B S.X₃) h) z).mp hz

theorem projectiveInput_preservesHomology : (functor k B N).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (projectiveInput_mapsExact k B N)

end LittleFinitistic.BimoduleBalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_BalancedVertexImage
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.Free.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.Free.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRightTo_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.ComplexTensor.column_d _root_.OAI.LittleFinitistic.ComplexTensor.finiteTotalMap_apply _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_comp _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_id _root_.OAI.LittleFinitistic.ComplexTensor.map_comp _root_.OAI.LittleFinitistic.ComplexTensor.map_id_left _root_.OAI.LittleFinitistic.ComplexTensor.map_zero_left _root_.OAI.LittleFinitistic.ComplexTensor.map_zero_right _root_.OAI.LittleFinitistic.ComplexTensor.matrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BalancedVertexImage
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B)) (e : B) (he : e*e=e)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

local instance originalRightModule_rfedd0a_1 : Module Bᵐᵒᵖ M :=
  Module.compHom M (BimoduleVertex.restriction k B)
abbrev V := (BimoduleVertex.functor k B e).obj M
abbrev W := (forgetRight k B).obj M

def inclusion : V k B M e ⟶ W k B M := ModuleCat.ofHom
  (VertexFunctor.inclusion (BimoduleVertex.restriction k B) (BimoduleVertex.vertex k B e)
    (BimoduleVertex.vertex_commute k B e) M)
def projection : W k B M ⟶ V k B M e := ModuleCat.ofHom
  (VertexFunctor.projection (BimoduleVertex.restriction k B) (BimoduleVertex.vertex k B e)
    (BimoduleVertex.vertex_idempotent k B e he) (BimoduleVertex.vertex_commute k B e) M)

theorem split : inclusion k B M e ≫ projection k B M e he = 𝟙 _ :=
  ModuleCat.hom_ext (VertexFunctor.projection_inclusion (BimoduleVertex.restriction k B)
    (BimoduleVertex.vertex k B e) (BimoduleVertex.vertex_idempotent k B e he)
    (BimoduleVertex.vertex_commute k B e) M)

theorem projector : ((F k B N).map (projection k B M e he ≫ inclusion k B M e)).hom =
    BimoduleBalancedTensor.action k B M N e := by
  apply BalancedTensor.ext
  intro m n
  rfl

/-- The image of the original vertex projector after tensoring is the actual left vertex. -/
def fixedEquiv :
    AdditiveSplitImage.fixed (F k B N) (inclusion k B M e) (projection k B M e he) ≃ₗ[k]
      IdempotentTensor.leftSpace (k := k) e (BimoduleBalancedTensor.Tensor k B M N) where
  toFun x := ⟨x.val,by
    change BimoduleBalancedTensor.action k B M N e x.val = x.val
    rw [← projector k B M e he N]
    exact (AdditiveSplitImage.mem_fixed _ _ _ x.val).1 x.property⟩
  invFun x := ⟨x.val,by
    exact (AdditiveSplitImage.mem_fixed (F k B N) (inclusion k B M e)
      (projection k B M e he) x.val).2
        ((LinearMap.congr_fun (projector k B M e he N) x.val).trans x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Vertex extraction commutes with actual balanced tensoring, without a flatness assumption. -/
def equiv : (F k B N).obj (V k B M e) ≃ₗ[k]
    IdempotentTensor.leftSpace (k := k) e (BimoduleBalancedTensor.Tensor k B M N) :=
  (AdditiveSplitImage.equiv (F k B N) (inclusion k B M e) (projection k B M e he)
    (split k B M e he)).trans (fixedEquiv k B M e he N)

@[simp] theorem equiv_apply_val (x : (F k B N).obj (V k B M e)) :
    (equiv k B M e he N x).val = ((F k B N).map (inclusion k B M e)).hom x := rfl
end LittleFinitistic.BalancedVertexImage

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_BalancedVertexFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BalancedVertexFunctor
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (e : B) (he : e*e=e)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

abbrev Space (M : ModuleCat.{u} (Enveloping k B)) :=
  IdempotentTensor.leftSpace (k := k) e (BimoduleBalancedTensor.Tensor k B M N)

def spaceMap {M M' : ModuleCat.{u} (Enveloping k B)} (f : M ⟶ M') :
    Space k B e N M →ₗ[k] Space k B e N M' :=
  (((BimoduleBalancedTensor.map k B N f).restrictScalars k).comp
    (Space k B e N M).subtype).codRestrict _ (by
      intro x
      change e • (BimoduleBalancedTensor.map k B N f x.val) =
        BimoduleBalancedTensor.map k B N f x.val
      rw [← (BimoduleBalancedTensor.map k B N f).map_smul,x.property])

/-- The actual left vertex of the balanced tensor, with its original induced maps. -/
def functor : ModuleCat.{u} (Enveloping k B) ⥤ ModuleCat.{u} k where
  obj M := ModuleCat.of k (Space k B e N M)
  map f := ModuleCat.ofHom (spaceMap k B e N f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : (BimoduleBalancedTensor.functor k B N).obj M ⟶
        (BimoduleBalancedTensor.functor k B N).obj M => f.hom x.val)
      ((BimoduleBalancedTensor.functor k B N).map_id M)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => ModuleCat.Hom.hom f x.val)
      ((BimoduleBalancedTensor.functor k B N).map_comp f g)

instance additive : (functor k B e N).Additive where
  map_add := by
    intros M M' f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun a : (BimoduleBalancedTensor.functor k B N).obj M ⟶
      (BimoduleBalancedTensor.functor k B N).obj M' => a.hom x.val)
      ((BimoduleBalancedTensor.functor k B N).map_add (f := f) (g := g))

/-- Vertex extraction commutes naturally with the original balanced tensor functor. -/
def comparison : BimoduleVertex.functor k B e ⋙ BalancedTensor.tensorFunctor k B N ≅
    functor k B e N :=
  NatIso.ofComponents (fun M => (BalancedVertexImage.equiv k B M e he N).toModuleIso) (by
    intro M M' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hn : (BimoduleVertex.functor k B e).map f ≫ BalancedVertexImage.inclusion k B M' e =
        BalancedVertexImage.inclusion k B M e ≫ (forgetRight k B).map f := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      rfl
    have hF := congrArg (fun a => (BalancedTensor.tensorFunctor k B N).map a) hn
    simp only [Functor.map_comp] at hF
    exact congrArg (fun a => ModuleCat.Hom.hom a x) hF)

end LittleFinitistic.BalancedVertexFunctor

end

end OAI
end


