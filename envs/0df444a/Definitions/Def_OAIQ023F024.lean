-- Prove2me | Definitions.Def_OAIQ023F024
-- name    : OAIQ023F024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T17:05:21.270622+00:00
-- url     : https://prove2.me/theorems/a1d98d90-45af-42c7-a6a9-4fd5074d4d4d
-- title:
--   Definitions bundle OAIQ023F024 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 14 definitions, 7 instances and 10 theorems. The definitions and types are `OAI.LittleFinitistic.OrdinarySimulation.BimoduleX`, `OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.secondTermEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.secondTotalEquiv`, `OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.secondTotalIso`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.terminalCharacter`, `OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.tensorModel`, `OAI.LittleFinitistic.OrdinarySimulation.terminalAugmentation`, `OAI.LittleFinitistic.PDBarQuotient.torIsoTwoSided`, `OAI.LittleFinitistic.PDBarQuotient.twoSidedIso`, `OAI.LittleFinitistic.PDResidueAssociativity.residueTorIso`, `OAI.LittleFinitistic.PDResidueAssociativity.twoSidedIso`, `OAI.LittleFinitistic.SingleBimoduleTensor.shiftedTotalIso`, `OAI.LittleFinitistic.SingleBimoduleTensor.totalIso`, `OAI.LittleFinitistic.SingleBimoduleTensor.totalTermEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Dimension_PDBarTensorComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Dimension/PDBarTensorComparison.lean), [`Finitistic_Dimension_PDResidueBaseBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Dimension/PDResidueBaseBar.lean), [`Finitistic_Localization_FiniteDerivedEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Localization/FiniteDerivedEvaluation.lean), [`Finitistic_Ordinary_OrdinaryBlockBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryBlockBimodule.lean), [`Finitistic_Ordinary_OrdinaryBlockTensorTerms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryBlockTensorTerms.lean), [`Finitistic_Ordinary_OrdinaryChainAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryChainAlgebra.lean), [`Finitistic_Ordinary_OrdinarySecondBlockTotal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinarySecondBlockTotal.lean), [`Finitistic_Ordinary_OrdinarySingleTensorTerms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinarySingleTensorTerms.lean), [`Finitistic_Ordinary_OrdinarySingleTensorTotal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinarySingleTensorTotal.lean), [`Finitistic_Ordinary_OrdinaryTerminal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryTerminal.lean).
--
--   **Imports.** It imports the bundles `OAIQ023F017`, `OAIQ023F018`, `OAIQ023F019` and `OAIQ023F020` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ023F026`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F017
import Definitions.Def_OAIQ023F018
import Definitions.Def_OAIQ023F019
import Definitions.Def_OAIQ023F020

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDBarTensorComparison
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- Comparison to the literal two-sided bar complex used in the splitting. -/
def twoSidedIso :
    ((PDTensor.tensorFunctor k A (RightBase f)).mapHomologicalComplex _).obj
      (DerivedBar.projectiveResolution k A N).complex ≅
    ((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj
      (DerivedBar.twoSidedComplex k A D N f) :=
  barQuotientIso f N ≪≫
    ((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).mapIso
      (DerivedBar.tensorBarIso k A D N f)

variable [FiniteDimensional k A] [FiniteDimensional k N]
/-- Tor computed by the literal two-sided bar, with no assumed quotient comparison. -/
def torIsoTwoSided (n : ℕ) :
    PDTensor.Tor (k := k) (RightBase f) (ModuleCat.of A N) n ≅
      (((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj
        (DerivedBar.twoSidedComplex k A D N f)).homology n :=
  (DerivedBar.projectiveResolution k A N).isoLeftDerivedObj
    (PDTensor.tensorFunctor k A (RightBase f)) n ≪≫
      (HomologicalComplex.homologyFunctor _ _ n).mapIso (twoSidedIso f N)
end LittleFinitistic.PDBarQuotient

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDResidueBaseBar
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDResidueAssociativity
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]

variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
local notation "S" => PDTensor.Residue (A := D)
local notation "SA" => PDResidueProjection.InflatedResidue f

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def twoSidedIso :
    ((PDTensor.tensorFunctor k A SA).mapHomologicalComplex _).obj (DerivedBar.projectiveResolution k A N).complex ≅
      ((PDTensor.tensorFunctor k D S).mapHomologicalComplex _).obj (DerivedBar.twoSidedComplex k A D N f) :=
  barIso f N ≪≫ ((PDTensor.tensorFunctor k D S).mapHomologicalComplex _).mapIso
    (DerivedBar.tensorBarIso k A D N f)

variable (hf : Function.Surjective f)
variable (hsq : ∀ a ∈ RingHom.ker f.toRingHom, ∀ b ∈ RingHom.ker f.toRingHom, a*b=0)

/-- Actual residue Tor is computed by tensoring the free D-bar with D/rad D.
This proves the needed change-of-rings comparison on the actual models. -/
def residueTorIso (n : ℕ) : PDTensor.Tor (k := k) (PDTensor.Residue (A := A)) (ModuleCat.of A N) n ≅
    (((PDTensor.tensorFunctor k D S).mapHomologicalComplex _).obj
      (DerivedBar.twoSidedComplex k A D N f)).homology n :=
  PDResidueProjection.torIso f hf hsq (ModuleCat.of A N) (DerivedBar.projectiveResolution k A N) n ≪≫
    (DerivedBar.projectiveResolution k A N).isoLeftDerivedObj (PDTensor.tensorFunctor k A SA) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (twoSidedIso f N)

end LittleFinitistic.PDResidueAssociativity

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

instance derivedToEssImageTriangulated : ((derivedEmbedding.{u,max u v} k).toEssImage).IsTriangulated := by
  dsimp [Functor.toEssImage]
  infer_instance

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryChainAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The terminal simple right module is the character at vertex l. -/
def terminalCharacter : ChainAlgebra k l →ₐ[k] k where
  toFun x := x.1 (Fin.last l)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
end ChainAlgebra

variable (B : Type u) [Ring B] [Algebra k B]
instance finiteDimensionalD [FiniteDimensional k B] :
    FiniteDimensional k (AlgebraD k l B) := inferInstance
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTerminal
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
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

/-- The terminal character extended along the B-factor. -/
def terminalAugmentation : (B ⊗[k] ChainAlgebra k l) →ₐ[k] B :=
  Algebra.TensorProduct.lift (AlgHom.id k B)
    ((Algebra.ofId k B).comp (ChainAlgebra.terminalCharacter k l)) (by
      intro b c
      change b * algebraMap k B (ChainAlgebra.terminalCharacter k l c) =
        algebraMap k B (ChainAlgebra.terminalCharacter k l c) * b
      exact (Algebra.commutes _ _).symm)

namespace TerminalTensor
instance instModuleMulOppositeTensorProductChainAlgebra : Module (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B) :=
  Module.compHom B (terminalAugmentation k B l).toRingHom.op

@[simp] theorem right_action (x : (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) (t : TerminalTensor B) :
    value B (x • t) = value B t * terminalAugmentation k B l x.unop := rfl

instance towerLeft : IsScalarTower k B (TerminalTensor B) := inferInstanceAs (IsScalarTower k B B)

instance towerRight : IsScalarTower k (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B) where
  smul_assoc c x v := by
    change value B v * terminalAugmentation k B l (c • x.unop) = c • (value B v * terminalAugmentation k B l x.unop)
    rw [map_smul, mul_smul_comm]

instance commuteActions : SMulCommClass B (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B) where
  smul_comm b x t := by
    change b * (value B t * terminalAugmentation k B l x.unop) =
      (b*value B t) * terminalAugmentation k B l x.unop
    exact (mul_assoc _ _ _).symm

/-- Explicit identification of this coordinate model with the source tensor product. -/
def tensorModel : (B ⊗[k] k) ≃ₗ[k] TerminalTensor B := TensorProduct.rid k B

@[simp] theorem tensorModel_tmul (b : B) (c : k) :
    tensorModel k B (b ⊗ₜ[k] c) = c • b := rfl

instance finiteDimensional [FiniteDimensional k B] : FiniteDimensional k (TerminalTensor B) :=
  inferInstanceAs (FiniteDimensional k B)
end TerminalTensor
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBlockBimodule
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k L R O T : Type u} [Field k] [Ring L] [Ring R]
  [AddCommGroup O] [AddCommGroup T]

open CategoryTheory
open scoped TensorProduct
variable {B : Type u} [Ring B] [Algebra k B]

/-- The actual ordinary Section 5 bimodule X over D=B×(B tensor C). -/
abbrev BimoduleX (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ) :=
  OffDiagonal (BimoduleO P a l) (TerminalTensor B)

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBlockTensorTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

def secondTermEquiv (Z : CochainComplex (ModuleCat.{u} R) ℤ) (p q : ℤ) :
    term k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p q ≃ₗ[L × R]
      BlockModule.First k L R (term k L R T Z p q) := by
  let M := OffDiagonal (BimoduleCoefficients k R L (O.X p)) (BimoduleCoefficients k L R (T.X p))
  let eM := RetainedBimodule.rightEquiv k (L × R) (L × R) M
  let eZ : ComplexTensor.leftTerm k (L × R) (BlockModule.secondComplex L R Z) q ≃ₗ[L × R]
      BlockModule.Second k L R (ComplexTensor.leftTerm k R Z q) := LinearEquiv.refl _ _
  exact (LeftTensor.congr (k := k) (A := L × R) (S := L × R) eM (RetainedBimodule.rightEquiv_left k (L × R) (L × R) M) eZ).trans
    (SecondBlockTensor.equivalence k L R (BimoduleCoefficients k R L (O.X p))
      (BimoduleCoefficients k L R (T.X p)) (ComplexTensor.leftTerm k R Z q))

theorem secondTermEquiv_map (Z : CochainComplex (ModuleCat.{u} R) ℤ) {p p' q q' : ℤ}
    (fO : O.X p ⟶ O.X p') (fT : T.X p ⟶ T.X p') (g : Z.X q ⟶ Z.X q') :
    (secondTermEquiv k L R O T Z p' q').toLinearMap.comp
      (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z)
        (OffDiagonal.objectMap k L R fO fT) ((ProductModules.secondInflation L R).map g)) =
    (BlockModule.firstMap k L R (map k L R T Z fT g)).comp
      (secondTermEquiv k L R O T Z p q).toLinearMap := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  rfl
end LittleFinitistic.OrdinarySimulation.BlockTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySecondBlockTotal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BimoduleAssociativity.scalarEquiv_mk _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id _root_.OAI.LittleFinitistic.ComplexTensor.finiteTotalMap_apply _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_comp _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_id _root_.OAI.LittleFinitistic.ComplexTensor.map_id_left _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply
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
variable (Z : CochainComplex (ModuleCat.{u} R) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
open BimoduleComplexTensor

def secondTotalEquiv (n : ℤ) :
    totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n ≃ₗ[L × R]
      BlockModule.First k L R (totalTerm k L R T Z p n) :=
  (LinearEquiv.piCongrRight (fun i => secondTermEquiv k L R O T Z (p i) (n + -(p i)))).trans
    (show (∀ i : Fin l, BlockModule.First k L R (term k L R T Z (p i) (n + -(p i)))) ≃ₗ[L × R]
      BlockModule.First k L R (totalTerm k L R T Z p n) from LinearEquiv.refl _ _)

@[simp] theorem secondTotalEquiv_apply (n : ℤ)
    (z : totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n)
    (i : Fin l) : secondTotalEquiv k L R O T Z p n z i =
      secondTermEquiv k L R O T Z (p i) (n + -(p i)) (z i) := rfl

theorem second_entry (n : ℤ) (i j : Fin l) :
    (secondTermEquiv k L R O T Z (p j) ((n+1) + -(p j))).toLinearMap.comp
      (entry k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n i j) =
    (BlockModule.firstMap k L R (entry k L R T Z p n i j)).comp
      (secondTermEquiv k L R O T Z (p i) (n + -(p i))).toLinearMap := by
  unfold entry
  split_ifs with h
  · have he : n + -(p i) = (n+1) + -(p j) := by omega
    have ht : (ProductModules.secondInflation L R).map (eqToHom (congrArg Z.X he)) =
        eqToHom (congrArg (BlockModule.secondComplex L R Z).X he) := by
      generalize n + -(p i) = q at he ⊢
      generalize (n+1) + -(p j) = q' at he ⊢
      subst q'
      simp only [eqToHom_refl,CategoryTheory.Functor.map_id]
      rfl
    have hh := secondTermEquiv_map k L R O T Z (O.d (p i) (p j)) (T.d (p i) (p j)) (eqToHom (congrArg Z.X he))
    rw [ht,← OffDiagonal.complex_d_all] at hh
    exact hh
  · apply LinearMap.ext
    intro x
    change secondTermEquiv k L R O T Z (p j) ((n+1) + -(p j)) 0 = 0
    exact (secondTermEquiv k L R O T Z (p j) ((n+1) + -(p j))).map_zero

theorem second_vertical (n : ℤ) (i : Fin l) :
    (secondTermEquiv k L R O T Z (p i) ((n+1) + -(p i))).toLinearMap.comp
      (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) (𝟙 _)
        ((BlockModule.secondComplex L R Z).d (n + -(p i)) ((n+1) + -(p i)))) =
    (BlockModule.firstMap k L R (map k L R T Z (𝟙 _) (Z.d (n + -(p i)) ((n+1) + -(p i))))).comp
      (secondTermEquiv k L R O T Z (p i) (n + -(p i))).toLinearMap := by
  exact secondTermEquiv_map k L R O T Z (𝟙 (O.X (p i))) (𝟙 (T.X (p i))) (Z.d _ _)

theorem second_differential (n : ℤ)
    (z : totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n) :
    secondTotalEquiv k L R O T Z p (n+1)
      (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n z) =
    differential k L R T Z p n (secondTotalEquiv k L R O T Z p n z) := by
  funext j
  change secondTermEquiv k L R O T Z (p j) ((n+1) + -(p j))
      (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n z j) =
    differential k L R T Z p n (secondTotalEquiv k L R O T Z p n z) j
  simp only [differential,
    LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,map_add,map_sum]
  apply congrArg₂ (· + ·)
  · change secondTermEquiv k L R O T Z (p j) ((n+1) + -(p j))
        ((((-(p j)).negOnePow : ℤ)) •
          (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) (𝟙 _)
            ((BlockModule.secondComplex L R Z).d (n + -(p j)) ((n+1) + -(p j))) (z j))) =
      (((-(p j)).negOnePow : ℤ)) •
        (map k L R T Z (𝟙 _) (Z.d (n + -(p j)) ((n+1) + -(p j))))
          (secondTermEquiv k L R O T Z (p j) (n + -(p j)) (z j))
    rw [map_zsmul]
    congr 1
    exact congrArg (fun f => f (z j)) (second_vertical k L R O T Z p n j)
  · erw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun f => f (z i)) (second_entry k L R O T Z p n i j)

/-- Actual tensor with the off-diagonal complex on a second-block input is the first-block T-total. -/
def secondTotalIso :
    total k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p hp ≅
      BlockModule.firstComplex L R (total k L R T Z p hp) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (secondTotalEquiv k L R O T Z p n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    have h₁ : (total k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p hp).d n (n+1) =
        ModuleCat.ofHom (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of (L × R) (totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n))
        (fun n => ModuleCat.ofHom (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n)) n
    have h₂ : (total k L R T Z p hp).d n (n+1) = ModuleCat.ofHom (differential k L R T Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of L (totalTerm k L R T Z p n))
        (fun n => ModuleCat.ofHom (differential k L R T Z p n)) n
    change _ ≫ (ProductModules.firstInflation L R).map ((total k L R T Z p hp).d n (n+1)) = _
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (second_differential k L R O T Z p n z).symm)
end LittleFinitistic.OrdinarySimulation.BlockTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySingleTensorTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

theorem termEquivAt_map (q : ℤ) (hq : q = 0) (n m : ℤ) (g : Z.X (n + -q) ⟶ Z.X (m + -q)) :
    (termEquivAt k S A N Z q hq m).toLinearMap.comp (map k S A (complex k S A N) Z (𝟙 _) g) =
    ((middleLeftFunctor k S A N).map g).hom.comp (termEquivAt k S A N Z q hq n).toLinearMap := by
  let : Module k (((middleLeftComplex k S A N Z)⟦-q⟧).X m) :=
    inferInstanceAs (Module k (LeftTensor k A S N (ComplexTensor.leftTerm k A Z (m + -q))))
  let : IsScalarTower k S (((middleLeftComplex k S A N Z)⟦-q⟧).X m) :=
    inferInstanceAs (IsScalarTower k S (LeftTensor k A S N (ComplexTensor.leftTerm k A Z (m + -q))))
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  rfl

def totalTermEquiv (n : ℤ) : totalTerm k S A (complex k S A N) Z p n ≃ₗ[S]
    ((middleLeftComplex k S A N Z)⟦-(p i₀)⟧).X n :=
  (FinitePiSupport.equivalence (fun i => term k S A (complex k S A N) Z (p i) (n + -(p i)))
    i₀ (otherTerm_subsingleton k S A N Z p hp i₀ h₀ n)).trans
    (selectedTermEquiv k S A N Z p i₀ h₀ n)
end LittleFinitistic.SingleBimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySingleTensorTotal
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
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p) (i₀ : Fin l) (h₀ : p i₀ = 0)
open BimoduleComplexTensor

theorem termEquivAt_vertical (q : ℤ) (hq : q = 0) (n : ℤ)
    (y : term k S A (complex k S A N) Z q (n + -q)) :
    termEquivAt k S A N Z q hq (n+1)
      (((-q).negOnePow • map k S A (complex k S A N) Z (𝟙 _)
        (Z.d (n + -q) ((n+1) + -q))) y) =
    (((middleLeftComplex k S A N Z)⟦-q⟧).d n (n+1)).hom (termEquivAt k S A N Z q hq n y) := by
  change termEquivAt k S A N Z q hq (n+1)
      ((((-q).negOnePow : ℤ)) • (map k S A (complex k S A N) Z (𝟙 _)
        (Z.d (n + -q) ((n+1) + -q))) y) =
    (((-q).negOnePow : ℤ)) • (((middleLeftFunctor k S A N).map (Z.d (n + -q) ((n+1) + -q))).hom
      (termEquivAt k S A N Z q hq n y))
  rw [map_zsmul]
  congr 1
  exact congrArg (fun f => f y) (termEquivAt_map k S A N Z q hq n (n+1) (Z.d _ _))

theorem totalTermEquiv_differential (n : ℤ) (z : totalTerm k S A (complex k S A N) Z p n) :
    totalTermEquiv k S A N Z p hp i₀ h₀ (n+1) (differential k S A (complex k S A N) Z p n z) =
    (((middleLeftComplex k S A N Z)⟦-(p i₀)⟧).d n (n+1)).hom (totalTermEquiv k S A N Z p hp i₀ h₀ n z) := by
  change termEquivAt k S A N Z (p i₀) h₀ (n+1)
      (differential k S A (complex k S A N) Z p n z i₀) =
    (((middleLeftComplex k S A N Z)⟦-(p i₀)⟧).d n (n+1)).hom (termEquivAt k S A N Z (p i₀) h₀ n (z i₀))
  rw [differential_selected k S A N Z p hp i₀ h₀]
  exact termEquivAt_vertical k S A N Z (p i₀) h₀ n (z i₀)

/-- A genuine ordinary bimodule in degree zero has exactly its ordinary tensor complex as total. -/
def shiftedTotalIso : total k S A (complex k S A N) Z p hp ≅ (middleLeftComplex k S A N Z)⟦-(p i₀)⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (totalTermEquiv k S A N Z p hp i₀ h₀ n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    have hd : (total k S A (complex k S A N) Z p hp).d n (n+1) = ModuleCat.ofHom (differential k S A (complex k S A N) Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A (complex k S A N) Z p n))
        (fun n => ModuleCat.ofHom (differential k S A (complex k S A N) Z p n)) n
    rw [hd]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (totalTermEquiv_differential k S A N Z p hp i₀ h₀ n z).symm)

/-- Removing the proved zero shift identifies the ordinary tensor complex exactly. -/
def totalIso : total k S A (complex k S A N) Z p hp ≅ middleLeftComplex k S A N Z :=
  shiftedTotalIso k S A N Z p hp i₀ h₀ ≪≫
    (eqToIso (congrArg (fun q : ℤ => (middleLeftComplex k S A N Z)⟦q⟧) (show -(p i₀) = 0 by omega))) ≪≫
    (shiftFunctorZero (CochainComplex (ModuleCat.{u} S) ℤ) ℤ).app (middleLeftComplex k S A N Z)
end LittleFinitistic.SingleBimoduleTensor

end

end OAI
end


