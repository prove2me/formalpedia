-- Prove2me | Definitions.Def_OAIQ023F014
-- name    : OAIQ023F014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:49:20.312765+00:00
-- url     : https://prove2.me/theorems/91191a77-0d58-4b77-8d0d-ca1ca71bc967
-- title:
--   Definitions bundle OAIQ023F014 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 12 definitions, 2 instances and 8 theorems. The definitions and types are `OAI.LittleFinitistic.LeftVertexHomology.spaceEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.arrow`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.mul`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.vertex`, `OAI.LittleFinitistic.OrdinarySimulation.FirstBlockTensor.source`, `OAI.LittleFinitistic.OrdinarySimulation.FirstBlockTensor.target`, `OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.equivalence`, `OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.inclusion`, `OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftAction`, `OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftMultiply`, `OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.project`, `OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.retraction`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Ordinary_OrdinaryChainAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryChainAlgebra.lean), [`Finitistic_Ordinary_OrdinaryFirstBlockTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryFirstBlockTensor.lean), [`Finitistic_Ordinary_OrdinaryTensorIdeal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryTensorIdeal.lean), [`Finitistic_Ordinary_OrdinaryTensorIdealActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryTensorIdealActions.lean), [`Finitistic_Rectification_LeftVertexHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/LeftVertexHomology.lean), [`Finitistic_Rectification_VertexTensorLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/VertexTensorLinear.lean).
--
--   **Imports.** It imports the bundles `OAIQ023F007` and `OAIQ023F008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F019` and `OAIQ023F020`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F007
import Definitions.Def_OAIQ023F008

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryChainAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

def mul (x y : ChainAlgebra k l) : ChainAlgebra k l :=
  (fun i => x.1 i * y.1 i,
   fun i => x.1 i.succ * y.2 i + x.2 i * y.1 i.castSucc)

instance instRing : Ring (ChainAlgebra k l) where
  __ := (inferInstance : AddCommGroup (ChainAlgebra k l))
  mul := mul k l
  one := unit k l
  mul_assoc x y z := by
    change mul k l (mul k l x y) z = mul k l x (mul k l y z)
    apply Prod.ext <;> funext i <;> simp only [mul] <;> ring
  one_mul x := by
    change mul k l (unit k l) x = x
    apply Prod.ext <;> funext i <;> simp [mul, unit]
  mul_one x := by
    change mul k l x (unit k l) = x
    apply Prod.ext <;> funext i <;> simp [mul, unit]
  left_distrib x y z := by
    change mul k l x (y+z) = mul k l x y + mul k l x z
    rw [add_eq k l (mul k l x y) (mul k l x z), add_eq k l y z]
    apply Prod.ext <;> funext i <;> simp only [mul, Pi.add_apply] <;> ring
  right_distrib x y z := by
    change mul k l (x+y) z = mul k l x z + mul k l y z
    rw [add_eq k l (mul k l x z) (mul k l y z), add_eq k l x y]
    apply Prod.ext <;> funext i <;> simp only [mul, Pi.add_apply] <;> ring
  zero_mul x := by
    change mul k l 0 x = 0
    apply Prod.ext <;> funext i <;> simp [mul, zero_eq]
  mul_zero x := by
    change mul k l x 0 = 0
    apply Prod.ext <;> funext i <;> simp [mul, zero_eq]

@[simp] theorem mul_diagonal (x y : ChainAlgebra k l) (i : Fin (l+1)) :
    (x*y).1 i = x.1 i * y.1 i := rfl
@[simp] theorem mul_radical (x y : ChainAlgebra k l) (i : Fin l) :
    (x*y).2 i = x.1 i.succ * y.2 i + x.2 i * y.1 i.castSucc := rfl

def vertex (i : Fin (l+1)) : ChainAlgebra k l := (Pi.single i 1, 0)
def arrow (i : Fin l) : ChainAlgebra k l := (0, Pi.single i 1)

@[simp] theorem vertex_idempotent (i : Fin (l+1)) :
    vertex k l i * vertex k l i = vertex k l i := by
  apply Prod.ext <;> funext j
  · change ((Pi.single i 1 : _ → k) j) * ((Pi.single i 1 : _ → k) j) = (Pi.single i 1 : _ → k) j
    by_cases h : j = i <;> simp [h]
  · change (mul k l (vertex k l i) (vertex k l i)).2 j = 0
    simp [mul, vertex]

end ChainAlgebra

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFirstBlockTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

abbrev source := LeftTensor k (L × R) (L × R) (OffDiagonal O T) (BlockModule.First k L R Z)
abbrev target := BlockModule.Second k L R (LeftTensor k L R O Z)

end LittleFinitistic.OrdinarySimulation.FirstBlockTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorIdeal
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (e : C) (he : e*e=e)

def project : C →ₗ[k] IdempotentTensor.rightIdeal e where
  toFun c := ⟨e*c, by change e*(e*c)=e*c; rw [← mul_assoc,he]⟩
  map_add' x y := Subtype.ext (mul_add e x y)
  map_smul' r x := Subtype.ext (mul_smul_comm r e x)

def inclusion : B ⊗[k] IdempotentTensor.rightIdeal e →ₗ[k] B ⊗[k] C :=
  TensorProduct.map (LinearMap.id) ((IdempotentTensor.rightIdeal e).subtype.restrictScalars k)

def retraction : B ⊗[k] C →ₗ[k] B ⊗[k] IdempotentTensor.rightIdeal e :=
  TensorProduct.map (LinearMap.id) (project e he)

theorem inclusion_retraction (z : B ⊗[k] C) :
    inclusion e (retraction e he z) = vertex e * z := by
  induction z using OAI.tensorInductionOn with
  | tmul b c =>
    simp only [inclusion,retraction,TensorProduct.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,Submodule.subtype_apply,project,LinearMap.coe_mk,
      AddHom.coe_mk,vertex,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  | add x y hx hy => simp only [map_add,mul_add,hx,hy]

theorem retraction_inclusion (z : B ⊗[k] IdempotentTensor.rightIdeal e) :
    retraction e he (inclusion e z) = z := by
  induction z using OAI.tensorInductionOn with
  | tmul b c =>
    change b ⊗ₜ[k] (⟨e*c.val, _⟩ : IdempotentTensor.rightIdeal e) = b ⊗ₜ[k] c
    congr 1
    exact Subtype.ext c.property
  | add x y hx hy => simp only [map_add,hx,hy]

include he in
theorem inclusion_fixed (z : B ⊗[k] IdempotentTensor.rightIdeal e) :
    vertex e * inclusion e z = inclusion e z := by
  rw [← inclusion_retraction e he, retraction_inclusion e he]

/-- The source term B tensor eC is the actual right ideal (1 tensor e)(B tensor C). -/
def equivalence : B ⊗[k] IdempotentTensor.rightIdeal e ≃ₗ[k]
    IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e) where
  toFun z := ⟨inclusion e z, inclusion_fixed e he z⟩
  invFun z := retraction e he z.val
  left_inv := retraction_inclusion e he
  right_inv z := Subtype.ext ((inclusion_retraction e he z.val).trans z.property)
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' r x := Subtype.ext (map_smul _ r x)

@[simp] theorem equivalence_tmul (b : B) (c : IdempotentTensor.rightIdeal e) :
    (equivalence (B := B) e he (b ⊗ₜ[k] c)).val = b ⊗ₜ[k] c.val := rfl
end LittleFinitistic.OrdinarySimulation.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorIdealActions
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

theorem coefficient_commute (b : B) :
    vertex (k := k) e * coefficient b = coefficient b * vertex e := by
  simp only [vertex,coefficient,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]

def leftMultiply (b : B) : IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e) →ₗ[(B ⊗[k] C)ᵐᵒᵖ]
    IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e) where
  toFun x := ⟨coefficient b * x.val, by
    change vertex e * (coefficient b * x.val) = coefficient b * x.val
    rw [← mul_assoc, coefficient_commute, mul_assoc, x.property]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' r x := Subtype.ext (mul_assoc _ _ r.unop).symm

def leftAction : B →ₐ[k] Module.End (B ⊗[k] C)ᵐᵒᵖ
    (IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e)) where
  toFun := leftMultiply e
  map_one' := by ext x; exact one_mul x.val
  map_mul' b c := by
    ext x
    change coefficient (b*c) * x.val = coefficient b * (coefficient c * x.val)
    rw [map_mul,mul_assoc]
  map_zero' := by
    ext x
    change coefficient (0:B) * x.val = 0
    rw [map_zero,zero_mul]
  map_add' b c := by
    ext x
    change coefficient (b+c) * x.val = coefficient b * x.val + coefficient c * x.val
    rw [map_add,add_mul]
  commutes' r := by
    ext x
    change coefficient (algebraMap k B r) * x.val = r • x.val
    rw [AlgHom.commutes, Algebra.smul_def]

end LittleFinitistic.OrdinarySimulation.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_LeftVertexHomology
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.LeftVertexHomology
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- Identify the vertex functor with the actual fixed subspace of scalar restriction. -/
def spaceEquiv (e : B) (M : ModuleCat.{u} B) :
    (vertex k B e).obj M ≃ₗ[k]
      IdempotentTensor.leftSpace (k := k) e ((ModuleCat.restrictScalars (algebraMap k B)).obj M) where
  toFun x := ⟨x.val, (VertexFunctor.mem_fixed _ _ _ M x.val).1 x.property⟩
  invFun x := ⟨x.val, (VertexFunctor.mem_fixed _ _ _ M x.val).2 x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LittleFinitistic.LeftVertexHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexTensorLinear
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace LittleFinitistic.TensorComplex
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (D : CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ)
instance linear : (tensorFunctor (k := k) D).Linear k where
  map_smul := by
    intro M N f c
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul m y =>
      change (c • f.hom m) ⊗ₜ[k] y = f.hom m ⊗ₜ[k]
        ((algebraMap k Bᵐᵒᵖ c) • (y : D.X n))
      exact TensorProduct.smul_tmul (R := k) c (f.hom m) (y : ScalarModule k B (D.X n))
    | add x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
end LittleFinitistic.TensorComplex

end

end OAI
end


