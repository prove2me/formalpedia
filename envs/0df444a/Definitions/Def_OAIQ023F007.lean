-- Prove2me | Definitions.Def_OAIQ023F007
-- name    : OAIQ023F007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:45:10.278778+00:00
-- url     : https://prove2.me/theorems/a507715b-3601-4b71-8a63-06c29c39d74f
-- title:
--   Definitions bundle OAIQ023F007 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 130 declarations of OpenAI's Lean: 54 definitions, 15 instances and 61 theorems. The definitions and types are `OAI.ExternalTensor.rightSwap`, `OAI.LittleFinitistic.BalancedAssociativity.Left`, `OAI.LittleFinitistic.BalancedAssociativity.Right`, `OAI.LittleFinitistic.BalancedAssociativity.equivalence`, `OAI.LittleFinitistic.BalancedAssociativity.forward`, `OAI.LittleFinitistic.BalancedAssociativity.forwardAt`, `OAI.LittleFinitistic.BalancedAssociativity.forwardBilinear`, `OAI.LittleFinitistic.BalancedAssociativity.inverse`, `OAI.LittleFinitistic.BalancedAssociativity.inverseAt`, `OAI.LittleFinitistic.BalancedAssociativity.inverseBilinear`, `OAI.LittleFinitistic.BalancedTensor.Free.equivalence`, `OAI.LittleFinitistic.BalancedTensor.Free.evaluation`, `OAI.LittleFinitistic.BalancedTensor.Free.insertion`, `OAI.LittleFinitistic.BalancedTensor.FreeLeft.equivalence`, `OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation`, `OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion`, `OAI.LittleFinitistic.BalancedTensor.bimap`, `OAI.LittleFinitistic.BalancedTensor.bimoduleAction`, `OAI.LittleFinitistic.BalancedTensor.congr`, `OAI.LittleFinitistic.BalancedTensor.fixedTensorFunctor`, `OAI.LittleFinitistic.BalancedTensor.homotopyEvaluation`, `OAI.LittleFinitistic.BalancedTensor.leftAction`, `OAI.LittleFinitistic.BalancedTensor.mapLeft`, `OAI.LittleFinitistic.BalancedTensor.mapRight`, `OAI.LittleFinitistic.BalancedTensor.mapRightTo`, `OAI.LittleFinitistic.BalancedTensor.rightAction`, `OAI.LittleFinitistic.BalancedTensor.tensorFunctor`, `OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv`, `OAI.LittleFinitistic.BalancedVertexImage.F`, `OAI.LittleFinitistic.ComplexTensor.term`, `OAI.LittleFinitistic.CornerSpaces.corner`, `OAI.LittleFinitistic.CornerSpaces.diagonalEquiv`, `OAI.LittleFinitistic.IdempotentTensor.leftMultiply`, `OAI.LittleFinitistic.IdempotentTensor.tensorEquiv`, `OAI.LittleFinitistic.IdempotentTensor.tensorEval`, `OAI.LittleFinitistic.IdempotentTensor.tensorInv`, `OAI.LittleFinitistic.LeftTensor`, `OAI.LittleFinitistic.LeftTensor.action`, `OAI.LittleFinitistic.LeftTensor.mk`, `OAI.LittleFinitistic.QuadraticEncoding.Paths` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Encoding_QuadraticEncoding`, `Finitistic_Localization_EvaluationModule`, `Finitistic_Localization_FiniteProjectiveHomotopy`, `Finitistic_Localization_FiniteSupportReindex`, `Finitistic_Localization_HomotopyEvaluation`, `Finitistic_Localization_TensorEvaluationComparison`, `Finitistic_Localization_TensorEvaluationFunctor`, `Finitistic_Ordinary_OrdinaryAssociativeTensorModules`, `Finitistic_Ordinary_OrdinaryBalancedActions`, `Finitistic_Ordinary_OrdinaryBalancedAssociativity`, `Finitistic_Ordinary_OrdinaryBalancedCongruence`, `Finitistic_Ordinary_OrdinaryComplexTensorMaps`, `Finitistic_Ordinary_OrdinaryFixedTensorFunctor`, `Finitistic_Ordinary_OrdinaryFreeTensor`, `Finitistic_Ordinary_OrdinaryFreeTensorExactness`, `Finitistic_Ordinary_OrdinaryProjectiveTensor`, `Finitistic_Ordinary_OrdinaryTensorBimap`, `Finitistic_Ordinary_OrdinaryTensorExactness`, `Finitistic_Ordinary_OrdinaryTwoSidedTensor`, `Finitistic_Rectification_ColumnFinite`, `Finitistic_Rectification_CornerProjection`, `Finitistic_Rectification_CornerSpaces`, `Finitistic_Rectification_ExternalTensor`, `Finitistic_Rectification_InducedColumns`, `Finitistic_Rectification_TensorComplex`, `Finitistic_Rectification_TensorProjection`, `Finitistic_Rectification_TotalFinite`, `Finitistic_Selected_SelectedFiniteTensorEvaluation`, `Finitistic_Tensor_BalancedFreeLeft`, `Finitistic_Tensor_BalancedTensor`, `Finitistic_Tensor_BalancedTensorMaps`, `Finitistic_Tensor_BalancedVertexImage`, `Finitistic_Tensor_IdempotentTensor`, `Finitistic_Tensor_IdempotentTensorMaps`.
--
--   **Imports.** It imports the bundles `OAIQ023F000`, `OAIQ023F001` and `OAIQ023F002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F011`, `OAIQ023F012`, `OAIQ023F013`, `OAIQ023F014` and `OAIQ023F015`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F000
import Definitions.Def_OAIQ023F001
import Definitions.Def_OAIQ023F002

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
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

abbrev Paths (k : Type u) [Field k] (d : ℕ) := Arrows k d ⊗[k] Arrows k d

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationModule
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
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

def arrowAction : Arrows k d →ₗ[k] Module.End k Y :=
  ∑ i, (LinearMap.proj i).smulRight (Fin.cases 1 X.generator i)

end Representation
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteProjectiveHomotopy
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject
namespace LittleFinitistic.FiniteProjectiveHomotopy
universe u v
variable (R : Type u) [Ring R]

lemma finite_biprod (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N] :
    Module.Finite R ((M ⊞ N) : ModuleCat R) :=
  finite_of_iso R (ModuleCat.biprodIsoProd M N).symm

end LittleFinitistic.FiniteProjectiveHomotopy

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteSupportReindex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.FiniteSupportReindex
universe u
variable {R : Type u} [Ring R]
variable (V : ℤ → ModuleCat.{u} R)
variable {l m : ℕ} (p : Fin l → ℤ) (q : Fin m → ℤ)

theorem coefficient_outside (n : ℤ) (hn : ∀ i, p i ≠ n) : coefficient V p n = 0 := by
  classical
  exact dite_eq_right (by simpa only [not_exists] using hn)

end LittleFinitistic.FiniteSupportReindex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_BalancedTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.BalancedTensor
universe u v w w' z
variable (k : Type u) [Field k] (A : Type v) [Ring A]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable (N : Type w') [AddCommGroup N] [Module k N] [Module A N]

variable {k A M N}

variable {V : Type z} [AddCommGroup V] [Module k V]

@[elab_as_elim] theorem induction_on {C : Tensor k A M N → Prop} (x : Tensor k A M N)
    (hz : C 0) (ht : ∀ m n, C (mk k A M N m n))
    (ha : ∀ a b, C a → C b → C (a+b)) : C x := by
  classical
  by_cases zero_tensor : x = 0
  · simpa [zero_tensor] using hz
  clear zero_tensor
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction x using OAI.tensorInductionOn with
    | tmul m n => exact ht m n
    | add a b h₁ h₂ => exact ha _ _ h₁ h₂

@[ext] theorem ext {f g : Tensor k A M N →ₗ[k] V}
    (h : ∀ m n, f (mk k A M N m n) = g (mk k A M N m n)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using induction_on with
  | hz => simp
  | ht m n => exact h m n
  | ha a b h₁ h₂ => simp [h₁,h₂]
end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_BalancedTensorMaps
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor
universe u v w w' w'' z
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable {M : Type w} [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable {M' : Type w'} [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M']
variable {M'' : Type w''} [AddCommGroup M''] [Module k M''] [Module Aᵐᵒᵖ M'']
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]
variable [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M']
  [IsScalarTower k Aᵐᵒᵖ M'']

/-- Tensor an actual right-module homomorphism with the identity. -/
def mapLeft (f : M →ₗ[Aᵐᵒᵖ] M') : Tensor k A M N →ₗ[k] Tensor k A M' N :=
  lift ((mk k A M' N).compl₁₂ (f.restrictScalars k) LinearMap.id) (by
    intro a m n
    change mk k A M' N (f (MulOpposite.op a • m)) n = mk k A M' N (f m) (a • n)
    rw [map_smul]
    exact balance a (f m) n)

@[simp] theorem mapLeft_mk (f : M →ₗ[Aᵐᵒᵖ] M') (m : M) (n : N) :
    mapLeft (k := k) N f (mk k A M N m n) = mk k A M' N (f m) n := rfl

@[simp] theorem mapLeft_id : mapLeft (k := k) N (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M) = LinearMap.id := by
  apply ext
  intro m n
  rfl

@[simp] theorem mapLeft_comp (f : M →ₗ[Aᵐᵒᵖ] M') (g : M' →ₗ[Aᵐᵒᵖ] M'') :
    mapLeft (k := k) N (g.comp f) = (mapLeft (k := k) N g).comp (mapLeft (k := k) N f) := by
  apply ext
  intro m n
  rfl

@[simp] theorem mapLeft_add (f g : M →ₗ[Aᵐᵒᵖ] M') :
    mapLeft (k := k) N (f+g) = mapLeft (k := k) N f + mapLeft (k := k) N g := by
  apply ext
  intro m n
  simp
end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TensorEvaluationFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u v w z
variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]

variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

/-- The actual tensor evaluation functor on all right A-modules. -/
def tensorFunctor : ModuleCat.{w} Aᵐᵒᵖ ⥤ ModuleCat.{max w z} k where
  obj M := ModuleCat.of k (Tensor k A (ScalarModule k A M) N)
  map {M M'} f := ModuleCat.ofHom
    (mapLeft (k := k) (M := ScalarModule k A M) (M' := ScalarModule k A M') N f.hom)
  map_id M := ModuleCat.hom_ext (mapLeft_id (k := k) N)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    rfl

instance tensorFunctorAdditive : (tensorFunctor k A N).Additive where
  map_add {M M'} {f g} := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    change mk k A (ScalarModule k A M') N (f.hom m + g.hom m) n =
      mk k A (ScalarModule k A M') N (f.hom m) n + mk k A (ScalarModule k A M') N (g.hom m) n
    exact LinearMap.congr_fun ((mk k A (ScalarModule k A M') N).map_add (f.hom m) (g.hom m)) n
end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_HomotopyEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u v w z
variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

/-- Termwise tensor evaluation on actual complexes, descended through chain homotopies. -/
def homotopyEvaluation :
    HomotopyCategory (ModuleCat.{w} Aᵐᵒᵖ) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{max w z} k) (ComplexShape.up ℤ) :=
  (tensorFunctor k A N).mapHomotopyCategory (ComplexShape.up ℤ)

instance homotopyEvaluationShift : (homotopyEvaluation.{u,v,w,z} k A N).CommShift ℤ :=
  inferInstanceAs (((tensorFunctor.{u,v,w,z} k A N).mapHomotopyCategory (ComplexShape.up ℤ)).CommShift ℤ)

instance homotopyEvaluationTriangulated : (homotopyEvaluation.{u,v,w,z} k A N).IsTriangulated :=
  inferInstanceAs (((tensorFunctor.{u,v,w,z} k A N).mapHomotopyCategory (ComplexShape.up ℤ)).IsTriangulated)
end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TensorEvaluationComparison
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u v w z
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k Aᵐᵒᵖ M]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

/-- Compare the functor's canonical scalar restriction with an existing compatible k-action. -/
def tensorFunctorEquiv :
    (tensorFunctor k A N).obj (ModuleCat.of Aᵐᵒᵖ M) ≃ₗ[k] Tensor k A M N where
  __ := mapLeft (k := k) N (fromScalarModule (k := k) M)
  invFun := mapLeft (k := k) N (toScalarModule (k := k) M)
  left_inv z := by
    change mapLeft (k := k) N (toScalarModule (k := k) M)
      (mapLeft (k := k) N (fromScalarModule (k := k) M) z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha a b h₁ h₂ =>
      simp only [map_add]
      exact congrArg₂ (fun a b => a+b) h₁ h₂
  right_inv z := by
    change mapLeft (k := k) N (fromScalarModule (k := k) M)
      (mapLeft (k := k) N (toScalarModule (k := k) M) z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha a b h₁ h₂ =>
      simp only [map_add]
      exact congrArg₂ (fun a b => a+b) h₁ h₂

@[simp] theorem tensorFunctorEquiv_mk (m : ScalarModule k A (ModuleCat.of Aᵐᵒᵖ M)) (n : N) :
    tensorFunctorEquiv M N (mk k A (ScalarModule k A (ModuleCat.of Aᵐᵒᵖ M)) N m n) =
      mk k A M N m n := rfl
end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBalancedActions
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.BalancedTensor
universe u
variable {k A M N S T : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- Tensor an actual left-module homomorphism with the identity. -/
def mapRight (f : N →ₗ[A] N) : Tensor k A M N →ₗ[k] Tensor k A M N :=
  lift ((mk k A M N).compl₁₂ LinearMap.id (f.restrictScalars k)) (by
    intro a m n
    change mk k A M N (MulOpposite.op a • m) (f n) = mk k A M N m (f (a • n))
    rw [f.map_smul, balance])

omit [IsScalarTower k Aᵐᵒᵖ M] in
@[simp] theorem mapRight_mk (f : N →ₗ[A] N) (m : M) (n : N) :
    mapRight (k := k) (M := M) f (mk k A M N m n) = mk k A M N m (f n) := rfl

variable [Ring S] [Algebra k S] [Module S M] [IsScalarTower k S M]
  [SMulCommClass S Aᵐᵒᵖ M]

/-- The left coefficient action is induced from the first balanced-tensor factor. -/
def leftAction : S →ₐ[k] Module.End k (Tensor k A M N) where
  toFun s := mapLeft N (Algebra.lsmul k Aᵐᵒᵖ M s)
  map_one' := by apply ext; intro m n; simp
  map_mul' s t := by apply ext; intro m n; simp
  map_zero' := by apply ext; intro m n; simp
  map_add' s t := by apply ext; intro m n; simp
  commutes' r := by apply ext; intro m n; simp

omit [IsScalarTower k A N] in
@[simp] theorem leftAction_mk (s : S) (m : M) (n : N) :
    leftAction (k := k) (A := A) (N := N) s (mk k A M N m n) = mk k A M N (s • m) n := rfl

variable [Ring T] [Algebra k T] [Module T N] [IsScalarTower k T N]
  [SMulCommClass T A N]

/-- The right coefficient action is induced from the second balanced-tensor factor. -/
def rightAction : T →ₐ[k] Module.End k (Tensor k A M N) where
  toFun t := mapRight (Algebra.lsmul k A N t)
  map_one' := by apply ext; intro m n; simp
  map_mul' s t := by apply ext; intro m n; simp
  map_zero' := by apply ext; intro m n; simp
  map_add' s t := by apply ext; intro m n; simp
  commutes' r := by apply ext; intro m n; simp

omit [IsScalarTower k Aᵐᵒᵖ M] in
@[simp] theorem rightAction_mk (t : T) (m : M) (n : N) :
    rightAction (k := k) (A := A) (M := M) t (mk k A M N m n) = mk k A M N m (t • n) := rfl

/-- Both outside actions on a balanced tensor, combined without forgetting either factor. -/
def bimoduleAction : (S ⊗[k] T) →ₐ[k] Module.End k (Tensor k A M N) :=
  Algebra.TensorProduct.lift (leftAction (k := k) (A := A) (M := M) (N := N))
    (rightAction (k := k) (A := A) (M := M) (N := N)) (by
      intro s t
      apply ext
      intro m n
      rfl)

@[simp] theorem bimoduleAction_tmul_mk (s : S) (t : T) (m : M) (n : N) :
    bimoduleAction (k := k) (A := A) (M := M) (N := N) (s ⊗ₜ[k] t) (mk k A M N m n) =
      mk k A M N (s • m) (t • n) := rfl
end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryAssociativeTensorModules
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u
/-- A tensor retaining the right action of the middle bimodule. -/
def RightTensor (k A : Type u) (_ : Type u) (M N : Type u) [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
    [AddCommGroup N] [Module k N] [Module A N] := BalancedTensor.Tensor k A M N

/-- A tensor retaining the left action of the middle bimodule. -/
def LeftTensor (k B : Type u) (_ : Type u) (N Z : Type u) [Field k] [Ring B] [Algebra k B]
    [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N]
    [AddCommGroup Z] [Module k Z] [Module B Z] := BalancedTensor.Tensor k B N Z

variable (k A B M N Z : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z] [IsScalarTower k B Z]

namespace RightTensor
instance instAddCommGroup : AddCommGroup (RightTensor k A B M N) := inferInstanceAs (AddCommGroup (BalancedTensor.Tensor k A M N))
instance instModule : Module k (RightTensor k A B M N) := inferInstanceAs (Module k (BalancedTensor.Tensor k A M N))

attribute [local instance] OAI.LittleFinitistic.RightTensor.instSMulCommClassMulOpposite
def action : Bᵐᵒᵖ →ₐ[k] Module.End k (RightTensor k A B M N) :=
  BalancedTensor.rightAction
instance instModuleMulOpposite : Module Bᵐᵒᵖ (RightTensor k A B M N) := Module.compHom _ (action k A B M N).toRingHom

def mk : M →ₗ[k] N →ₗ[k] RightTensor k A B M N := BalancedTensor.mk k A M N

omit [IsScalarTower k Aᵐᵒᵖ M] in
@[simp] theorem smul_mk (b : Bᵐᵒᵖ) (m : M) (n : N) :
    b • mk k A B M N m n = mk k A B M N m (b • n) := rfl
end RightTensor

namespace LeftTensor
instance instAddCommGroup : AddCommGroup (LeftTensor k B A N Z) := inferInstanceAs (AddCommGroup (BalancedTensor.Tensor k B N Z))
instance instModule : Module k (LeftTensor k B A N Z) := inferInstanceAs (Module k (BalancedTensor.Tensor k B N Z))

def action : A →ₐ[k] Module.End k (LeftTensor k B A N Z) := BalancedTensor.leftAction
instance instModule_1 : Module A (LeftTensor k B A N Z) := Module.compHom _ (action k A B N Z).toRingHom

def mk : N →ₗ[k] Z →ₗ[k] LeftTensor k B A N Z := BalancedTensor.mk k B N Z

omit [IsScalarTower k B Z] in
@[simp] theorem smul_mk (a : A) (n : N) (z : Z) :
    a • mk k A B N Z n z = mk k A B N Z (a • n) z := rfl
end LeftTensor
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBalancedAssociativity
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedAssociativity
open BalancedTensor
universe u
variable (k A B M N Z : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z]

abbrev Left := Tensor k B (RightTensor k A B M N) Z
abbrev Right := Tensor k A M (LeftTensor k B A N Z)

/-- Reassociate a fixed last input through the actual A-balanced quotient. -/
def forwardAt (z : Z) : RightTensor k A B M N →ₗ[k] Right k A B M N Z :=
  lift ((mk k A M (LeftTensor k B A N Z)).compl₁₂ LinearMap.id ((LeftTensor.mk k A B N Z).flip z)) (by
    intro a m n
    change mk k A M (LeftTensor k B A N Z) (MulOpposite.op a • m) (LeftTensor.mk k A B N Z n z) =
      mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z (a • n) z)
    rw [balance,LeftTensor.smul_mk])

@[simp] theorem forwardAt_mk (m : M) (n : N) (z : Z) :
    forwardAt k A B M N Z z (RightTensor.mk k A B M N m n) =
      mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z) := rfl

def forwardBilinear : RightTensor k A B M N →ₗ[k] Z →ₗ[k] Right k A B M N Z where
  toFun x :=
    { toFun := fun z => forwardAt k A B M N Z z x
      map_add' := fun z z' => by
        have h : forwardAt k A B M N Z (z+z') =
            forwardAt k A B M N Z z + forwardAt k A B M N Z z' := by
          apply BalancedTensor.ext
          intro m n
          change mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n (z+z')) =
            mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z) +
            mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z')
          simp only [map_add]
        exact congrArg (fun f => f x) h
      map_smul' := fun r z => by
        have h : forwardAt k A B M N Z (r • z) = r • forwardAt k A B M N Z z := by
          apply BalancedTensor.ext
          intro m n
          change mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n (r • z)) =
            r • mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z)
          simp only [map_smul]
        exact congrArg (fun f => f x) h }
  map_add' x y := by ext z; exact (forwardAt k A B M N Z z).map_add x y
  map_smul' r x := by ext z; exact (forwardAt k A B M N Z z).map_smul r x

/-- The actual forward associativity map of balanced tensors. -/
def forward : Left k A B M N Z →ₗ[k] Right k A B M N Z :=
  lift (forwardBilinear k A B M N Z) (by
    intro b x z
    have h : (forwardAt k A B M N Z z).comp (RightTensor.action k A B M N (MulOpposite.op b)) =
        forwardAt k A B M N Z (b • z) := by
      apply BalancedTensor.ext
      intro m n
      change forwardAt k A B M N Z z (MulOpposite.op b • RightTensor.mk k A B M N m n) =
        forwardAt k A B M N Z (b • z) (RightTensor.mk k A B M N m n)
      rw [RightTensor.smul_mk,forwardAt_mk,forwardAt_mk]
      exact congrArg (mk k A M (LeftTensor k B A N Z) m) (balance b n z)
    exact congrArg (fun f => f x) h)


@[simp] theorem forward_mk (m : M) (n : N) (z : Z) :
    forward k A B M N Z (mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) z) =
      mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z) := rfl

/-- Reassociate a fixed first input through the actual B-balanced quotient. -/
def inverseAt (m : M) : LeftTensor k B A N Z →ₗ[k] Left k A B M N Z :=
  lift ((mk k B (RightTensor k A B M N) Z).compl₁₂ (RightTensor.mk k A B M N m) LinearMap.id) (by
    intro b n z
    change mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m (MulOpposite.op b • n)) z =
      mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) (b • z)
    rw [← RightTensor.smul_mk,balance])

@[simp] theorem inverseAt_mk (m : M) (n : N) (z : Z) :
    inverseAt k A B M N Z m (LeftTensor.mk k A B N Z n z) =
      mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) z := rfl

def inverseBilinear : M →ₗ[k] LeftTensor k B A N Z →ₗ[k] Left k A B M N Z where
  toFun := inverseAt k A B M N Z
  map_add' m m' := by
    apply BalancedTensor.ext
    intro n z
    change mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N (m+m') n) z =
      mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) z +
      mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m' n) z
    simp only [map_add,LinearMap.add_apply]
  map_smul' r m := by
    apply BalancedTensor.ext
    intro n z
    change mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N (r • m) n) z =
      r • mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) z
    simp only [map_smul,LinearMap.smul_apply]

/-- The actual inverse associativity map of balanced tensors. -/
def inverse : Right k A B M N Z →ₗ[k] Left k A B M N Z :=
  lift (inverseBilinear k A B M N Z) (by
    intro a m x
    have h : inverseAt k A B M N Z (MulOpposite.op a • m) =
        (inverseAt k A B M N Z m).comp (LeftTensor.action k A B N Z a) := by
      apply BalancedTensor.ext
      intro n z
      change inverseAt k A B M N Z (MulOpposite.op a • m) (LeftTensor.mk k A B N Z n z) =
        inverseAt k A B M N Z m (a • LeftTensor.mk k A B N Z n z)
      rw [LeftTensor.smul_mk,inverseAt_mk,inverseAt_mk]
      exact congrArg (fun y => mk k B (RightTensor k A B M N) Z y z) (balance a m n)
    exact congrArg (fun f => f x) h)


@[simp] theorem inverse_mk (m : M) (n : N) (z : Z) :
    inverse k A B M N Z (mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z)) =
      mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) z := rfl

/-- Associativity of the actual noncommutative balanced tensor, with no flatness hypotheses. -/
def equivalence : Left k A B M N Z ≃ₗ[k] Right k A B M N Z where
  __ := forward k A B M N Z
  invFun := inverse k A B M N Z
  left_inv x := by
    let F := (inverse k A B M N Z).comp (forward k A B M N Z)
    have h : F = LinearMap.id := by
      apply BalancedTensor.ext
      intro y z
      have hz : F.comp ((mk k B (RightTensor k A B M N) Z).flip z) =
          (mk k B (RightTensor k A B M N) Z).flip z := by
        apply BalancedTensor.ext
        intro m n
        rfl
      exact congrArg (fun f => f y) hz
    exact congrArg (fun f => f x) h
  right_inv x := by
    let F := (forward k A B M N Z).comp (inverse k A B M N Z)
    have h : F = LinearMap.id := by
      apply BalancedTensor.ext
      intro m y
      have hm : F.comp (mk k A M (LeftTensor k B A N Z) m) =
          mk k A M (LeftTensor k B A N Z) m := by
        apply BalancedTensor.ext
        intro n z
        rfl
      exact congrArg (fun f => f y) hm
    exact congrArg (fun f => f x) h

end LittleFinitistic.BalancedAssociativity

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_IdempotentTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.IdempotentTensor
universe u v w
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable (e : A)

variable (N : Type w) [AddCommGroup N] [Module k N] [Module A N]
  [IsScalarTower k A N]

/-- The natural map eA tensor_A N → eN. -/
def tensorEval : BalancedTensor.Tensor k A (rightIdeal e) N →ₗ[k] leftSpace (k := k) e N :=
  BalancedTensor.lift (productEval (k := k) e N) (by
    intro a m n
    apply Subtype.ext
    exact mul_smul m.val a n)

@[simp] theorem tensorEval_mk (m : rightIdeal e) (n : N) :
    (tensorEval (k := k) e N (BalancedTensor.mk k A (rightIdeal e) N m n)).val = m.val • n := rfl

variable (he : e*e=e)

def tensorInv : leftSpace (k := k) e N →ₗ[k] BalancedTensor.Tensor k A (rightIdeal e) N :=
  (BalancedTensor.mk k A (rightIdeal e) N ⟨e,he⟩).comp (leftSpace (k := k) e N).subtype

@[simp] theorem tensorEval_tensorInv (n : leftSpace (k := k) e N) :
    tensorEval (k := k) e N (tensorInv (k := k) e N he n) = n := by
  apply Subtype.ext
  exact n.property

@[simp] theorem tensorInv_tensorEval (z : BalancedTensor.Tensor k A (rightIdeal e) N) :
    tensorInv (k := k) e N he (tensorEval (k := k) e N z) = z := by
  induction z using BalancedTensor.induction_on with
  | hz => simp
  | ht m n =>
    change BalancedTensor.mk k A (rightIdeal e) N ⟨e,he⟩ (m.val • n) =
      BalancedTensor.mk k A (rightIdeal e) N m n
    rw [← BalancedTensor.balance]
    have hm : MulOpposite.op m.val • (⟨e,he⟩ : rightIdeal e) = m := by
      apply Subtype.ext
      exact m.property
    rw [hm]
  | ha a b h₁ h₂ => simp [h₁,h₂]

/-- Evaluation on a vertex projective is its actual vertex space. -/
def tensorEquiv : BalancedTensor.Tensor k A (rightIdeal e) N ≃ₗ[k] leftSpace (k := k) e N where
  __ := tensorEval (k := k) e N
  invFun := tensorInv (k := k) e N he
  left_inv := tensorInv_tensorEval (k := k) e N he
  right_inv := tensorEval_tensorInv (k := k) e N he
end LittleFinitistic.IdempotentTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorExactness
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic
namespace BalancedTensor
universe u
variable {k A M N N' N'' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
variable [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

/-- The actual covariant map in the left-module factor of a balanced tensor. -/
def mapRightTo (f : N →ₗ[A] N') : Tensor k A M N →ₗ[k] Tensor k A M N' :=
  lift ((mk k A M N').compl₁₂ LinearMap.id (f.restrictScalars k)) (by
    intro a m n
    change mk k A M N' (MulOpposite.op a • m) (f n) = mk k A M N' m (f (a • n))
    rw [f.map_smul,balance])

@[simp] theorem mapRightTo_mk (f : N →ₗ[A] N') (m : M) (n : N) :
    mapRightTo (k := k) (M := M) f (mk k A M N m n) = mk k A M N' m (f n) := rfl

end BalancedTensor

end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFixedTensorFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

variable (M : Type u) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]

/-- Tensor by a fixed actual right module on every left module. -/
def fixedTensorFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} k where
  obj N := ModuleCat.of k (Tensor k A M (ScalarLeftModule k A N))
  map {N N'} f := ModuleCat.ofHom
    (mapRightTo (k := k) (M := M) (N := ScalarLeftModule k A N) (N' := ScalarLeftModule k A N') f.hom)
  map_id N := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    rfl

instance fixedTensorFunctor_additive : (fixedTensorFunctor k A M).Additive where
  map_add {N N'} {f g} := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    exact (mk k A M (ScalarLeftModule k A N') m).map_add (f.hom n) (g.hom n)

end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFreeTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor.Free
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (I N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def evaluation : Tensor k A (I →₀ Aᵐᵒᵖ) N →ₗ[k] (I →₀ N) :=
  lift (evaluateBilinear (k := k) I N) (by
    intro a m n
    induction m using Finsupp.induction_linear with
    | zero => simp only [smul_zero,map_zero,LinearMap.zero_apply]
    | add x y hx hy => simp only [smul_add,map_add,LinearMap.add_apply,hx,hy]
    | single i x =>
      rw [Finsupp.smul_single,evaluateBilinear_single,evaluateBilinear_single]
      change Finsupp.single i ((x.unop*a) • n) = Finsupp.single i (x.unop • (a • n))
      rw [mul_smul])

@[simp] theorem evaluation_single (i : I) (x : Aᵐᵒᵖ) (n : N) :
    evaluation (k := k) I N (mk k A (I →₀ Aᵐᵒᵖ) N (Finsupp.single i x) n) =
      Finsupp.single i (x.unop • n) := evaluateBilinear_single I N i x n

def insertion : (I →₀ N) →ₗ[k] Tensor k A (I →₀ Aᵐᵒᵖ) N :=
  Finsupp.lsum k (fun i => mk k A (I →₀ Aᵐᵒᵖ) N (Finsupp.single i 1))

omit [IsScalarTower k A N] in
@[simp] theorem insertion_single (i : I) (n : N) :
    insertion (k := k) (A := A) I N (Finsupp.single i n) =
      mk k A (I →₀ Aᵐᵒᵖ) N (Finsupp.single i 1) n := by
  simp only [insertion,Finsupp.lsum_single]

theorem evaluation_insertion (z : I →₀ N) :
    evaluation (k := k) (A := A) I N (insertion I N z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single i n => rw [insertion_single,evaluation_single,MulOpposite.unop_one,one_smul]

theorem insertion_evaluation (z : Tensor k A (I →₀ Aᵐᵒᵖ) N) :
    insertion I N (evaluation (k := k) I N z) = z := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n =>
    induction m using Finsupp.induction_linear with
    | zero => simp only [map_zero,LinearMap.zero_apply]
    | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]
    | single i x =>
      rw [evaluation_single,insertion_single,← balance]
      congr 1
      rw [MulOpposite.op_unop,Finsupp.smul_single,smul_eq_mul,mul_one]
  | ha x y hx hy => simp only [map_add,hx,hy]

/-- The actual free balanced tensor, for arbitrary index sets and arbitrary modules N. -/
def equivalence : Tensor k A (I →₀ Aᵐᵒᵖ) N ≃ₗ[k] (I →₀ N) where
  __ := evaluation (k := k) I N
  invFun := insertion I N
  left_inv := insertion_evaluation I N
  right_inv := evaluation_insertion I N
end LittleFinitistic.BalancedTensor.Free

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFreeTensorExactness
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor.Free
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (I : Type u)
variable {N N' N'' : Type u}
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
variable [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

theorem evaluation_naturality (f : N →ₗ[A] N') (z : Tensor k A (I →₀ Aᵐᵒᵖ) N) :
    evaluation (k := k) I N' (mapRightTo f z) =
      Finsupp.mapRange.linearMap (f.restrictScalars k) (evaluation (k := k) I N z) := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n =>
    induction m using Finsupp.induction_linear with
    | zero => simp only [map_zero,LinearMap.zero_apply]
    | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]
    | single i x =>
      simp only [mapRightTo_mk,evaluation_single]
      change Finsupp.single i (MulOpposite.unop x • f n) =
        Finsupp.mapRange f f.map_zero (Finsupp.single i (MulOpposite.unop x • n))
      rw [Finsupp.mapRange_single, f.map_smul]
  | ha x y hx hy => simp only [map_add,hx,hy]

/-- Tensor by an arbitrary free right module preserves every exact module sequence. -/
theorem tensor_exact (f : N →ₗ[A] N') (g : N' →ₗ[A] N'') (h : Function.Exact f g) :
    Function.Exact (mapRightTo (k := k) (M := I →₀ Aᵐᵒᵖ) f)
      (mapRightTo (k := k) (M := I →₀ Aᵐᵒᵖ) g) := by
  intro z
  constructor
  · intro hz
    have hz' : Finsupp.mapRange.linearMap (g.restrictScalars k) (evaluation (k := k) I N' z) = 0 := by
      rw [← evaluation_naturality,hz,map_zero]
    obtain ⟨y,hy⟩ := (finsupp_exact (k := k) I f g h _).mp hz'
    refine ⟨(equivalence (k := k) (A := A) I N).symm y, ?_⟩
    apply (equivalence (k := k) (A := A) I N').injective
    change evaluation (k := k) I N' (mapRightTo f ((equivalence (k := k) (A := A) I N).symm y)) = _
    rw [evaluation_naturality]
    change Finsupp.mapRange.linearMap (f.restrictScalars k)
      ((equivalence (k := k) (A := A) I N) ((equivalence (k := k) (A := A) I N).symm y)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y,rfl⟩
    induction y using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n => rw [mapRightTo_mk,mapRightTo_mk,(h (f n)).mpr ⟨n,rfl⟩,map_zero]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
end LittleFinitistic.BalancedTensor.Free

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProjectiveTensor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u
variable {k A M M' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable {N N' N'' : Type u}
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
variable [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

theorem mapLeft_mapRightTo (i : M →ₗ[Aᵐᵒᵖ] M') (f : N →ₗ[A] N') (z : Tensor k A M N) :
    mapLeft N' i (mapRightTo f z) = mapRightTo f (mapLeft N i z) := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n => rfl
  | ha x y hx hy => simp only [map_add,hx,hy]

omit [IsScalarTower k A N] in
theorem mapLeft_split (i : M →ₗ[Aᵐᵒᵖ] M') (p : M' →ₗ[Aᵐᵒᵖ] M)
    (hp : p.comp i = LinearMap.id) (z : Tensor k A M N) :
    mapLeft N p (mapLeft N i z) = z := by
  have hm := congrArg (fun f : Tensor k A M N →ₗ[k] Tensor k A M N => f z)
    (mapLeft_comp (k := k) N i p).symm
  simpa only [hp,mapLeft_id,LinearMap.id_apply,LinearMap.comp_apply] using hm

/-- Exactness descends through an actual split right-module retract. -/
theorem tensor_exact_of_split (i : M →ₗ[Aᵐᵒᵖ] M') (p : M' →ₗ[Aᵐᵒᵖ] M)
    (hp : p.comp i = LinearMap.id) (f : N →ₗ[A] N') (g : N' →ₗ[A] N'')
    (h : Function.Exact f g)
    (h' : Function.Exact (mapRightTo (k := k) (M := M') f) (mapRightTo (k := k) (M := M') g)) :
    Function.Exact (mapRightTo (k := k) (M := M) f) (mapRightTo (k := k) (M := M) g) := by
  intro z
  constructor
  · intro hz
    have hi : mapRightTo g (mapLeft N' i z) = 0 := by
      rw [← mapLeft_mapRightTo,hz,map_zero]
    obtain ⟨y,hy⟩ := (h' _).mp hi
    refine ⟨mapLeft N p y, ?_⟩
    rw [← mapLeft_mapRightTo,hy,mapLeft_split i p hp]
  · rintro ⟨y,rfl⟩
    induction y using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n => rw [mapRightTo_mk,mapRightTo_mk,(h (f n)).mpr ⟨n,rfl⟩,map_zero]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]

/-- Projectivity of the actual right module suffices, with no hypothesis on the left modules. -/
theorem projectiveTensor_exact [Module.Projective Aᵐᵒᵖ M]
    (f : N →ₗ[A] N') (g : N' →ₗ[A] N'') (h : Function.Exact f g) :
    Function.Exact (mapRightTo (k := k) (M := M) f) (mapRightTo (k := k) (M := M) g) := by
  obtain ⟨i,hi⟩ := (Module.projective_def' (R := Aᵐᵒᵖ) (P := M)).mp inferInstance
  exact tensor_exact_of_split i (Finsupp.linearCombination Aᵐᵒᵖ id) hi f g h
    (Free.tensor_exact (k := k) M f g h)

variable (k A M)

theorem projectiveTensor_mapsExact [Module.Projective Aᵐᵒᵖ M]
    (S : ShortComplex (ModuleCat.{u} A)) (hS : S.Exact) :
    (S.map (fixedTensorFunctor k A M)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  have h : Function.Exact
      (S.f.hom : ScalarLeftModule k A S.X₁ →ₗ[A] ScalarLeftModule k A S.X₂)
      (S.g.hom : ScalarLeftModule k A S.X₂ →ₗ[A] ScalarLeftModule k A S.X₃) := by
    intro n
    constructor
    · exact (ShortComplex.moduleCat_exact_iff S).mp hS n
    · rintro ⟨m,rfl⟩
      exact congrArg (fun f => f.hom m) S.zero
  have ht := @projectiveTensor_exact k A M _ _ _ _ _ _ _
    (ScalarLeftModule k A S.X₁) (ScalarLeftModule k A S.X₂) (ScalarLeftModule k A S.X₃)
    _ _ _ (scalarLeftTower k A S.X₁)
    _ _ _ (scalarLeftTower k A S.X₂) _ _ _ (scalarLeftTower k A S.X₃)
    _ S.f.hom S.g.hom h
  intro z hz
  exact (ht z).mp hz

theorem projectiveTensor_preservesHomology [Module.Projective Aᵐᵒᵖ M] :
    (fixedTensorFunctor k A M).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (projectiveTensor_mapsExact k A M)

/-- Degree-zero projective tensor preserves quasi-isomorphisms of arbitrary complexes. -/
theorem projectiveTensor_quasiIso [Module.Projective Aᵐᵒᵖ M]
    {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z') [QuasiIso f] :
    QuasiIso (((fixedTensorFunctor k A M).mapHomologicalComplex (.up ℤ)).map f) := by
  let := projectiveTensor_preservesHomology k A M
  infer_instance
end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorBimap
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor
universe u
variable {k A M M' M'' N N' N'' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable [AddCommGroup M''] [Module k M''] [Module Aᵐᵒᵖ M''] [IsScalarTower k Aᵐᵒᵖ M'']
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
variable [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

/-- The actual balanced tensor map in both variables. -/
def bimap (f : M →ₗ[Aᵐᵒᵖ] M') (g : N →ₗ[A] N') : Tensor k A M N →ₗ[k] Tensor k A M' N' :=
  (mapRightTo g).comp (mapLeft N f)

@[simp] theorem bimap_mk (f : M →ₗ[Aᵐᵒᵖ] M') (g : N →ₗ[A] N') (m : M) (n : N) :
    bimap (k := k) f g (mk k A M N m n) = mk k A M' N' (f m) (g n) := rfl

@[simp] theorem bimap_comp (f : M →ₗ[Aᵐᵒᵖ] M') (f' : M' →ₗ[Aᵐᵒᵖ] M'')
    (g : N →ₗ[A] N') (g' : N' →ₗ[A] N'') :
    (bimap (k := k) f' g').comp (bimap f g) = bimap (f'.comp f) (g'.comp g) := by
  apply ext
  intro m n
  rfl

@[simp] theorem bimap_zero_left (g : N →ₗ[A] N') :
    bimap (k := k) (0 : M →ₗ[Aᵐᵒᵖ] M') g = 0 := by
  apply ext
  intro m n
  simp only [bimap_mk,LinearMap.zero_apply,map_zero,LinearMap.zero_apply]

@[simp] theorem bimap_zero_right (f : M →ₗ[Aᵐᵒᵖ] M') :
    bimap (k := k) f (0 : N →ₗ[A] N') = 0 := by
  apply ext
  intro m n
  simp only [bimap_mk,LinearMap.zero_apply,map_zero]
end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBalancedCongruence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor
universe u
variable {k A M M' N N' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']

/-- Actual balanced tensor congruence under module equivalences in both factors. -/
def congr (e : M ≃ₗ[Aᵐᵒᵖ] M') (f : N ≃ₗ[A] N') : Tensor k A M N ≃ₗ[k] Tensor k A M' N' where
  __ := bimap (k := k) e.toLinearMap f.toLinearMap
  invFun := bimap (k := k) e.symm.toLinearMap f.symm.toLinearMap
  left_inv x := by
    change bimap e.symm.toLinearMap f.symm.toLinearMap (bimap e.toLinearMap f.toLinearMap x) = x
    induction x using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n => simp only [bimap_mk,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    | ha x y hx hy => simp only [map_add,hx,hy]
  right_inv x := by
    change bimap e.toLinearMap f.toLinearMap (bimap e.symm.toLinearMap f.symm.toLinearMap x) = x
    induction x using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n => simp only [bimap_mk,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    | ha x y hx hy => simp only [map_add,hx,hy]
end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryComplexTensorMaps
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

abbrev term (p q : ℤ) := Tensor k A (rightTerm k A Q p) (leftTerm k A Z q)

end LittleFinitistic.ComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTwoSidedTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic
universe u
/-- Balanced tensor with its two outside coefficient algebras recorded in the type. -/
def TwoSidedTensor (k A _S _T M N : Type u) [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
    [AddCommGroup N] [Module k N] [Module A N] := BalancedTensor.Tensor k A M N

variable (k A S T M N : Type u) [Field k] [Ring A] [Algebra k A] [Ring S] [Algebra k S]
  [Ring T] [Algebra k T]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module S M] [IsScalarTower k S M] [SMulCommClass S Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [Module T N] [IsScalarTower k T N] [SMulCommClass T A N]

namespace TwoSidedTensor
instance instAddCommGroup : AddCommGroup (TwoSidedTensor k A S T M N) := inferInstanceAs (AddCommGroup (BalancedTensor.Tensor k A M N))
instance instModule : Module k (TwoSidedTensor k A S T M N) := inferInstanceAs (Module k (BalancedTensor.Tensor k A M N))

def action : (S ⊗[k] T) →ₐ[k] Module.End k (TwoSidedTensor k A S T M N) :=
  BalancedTensor.bimoduleAction
end TwoSidedTensor
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ExternalTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.ExternalTensor.columnInclusion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct


noncomputable section
namespace ExternalTensor

variable (k B M N : Type*) [Field k] [Ring B] [Algebra k B]
  [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

attribute [local instance] bimodule rightModule


/-- Factor swap, with the external right action on the source. -/
def rightSwap : (M ⊗[k] N) ≃ₗ[Bᵐᵒᵖ] (N ⊗[k] M) where
  __ := (TensorProduct.comm k M N).toAddEquiv
  map_smul' c x := by
    induction x using OAI.tensorInductionOn with
    | tmul m n => simp [right_smul_tmul, TensorProduct.smul_tmul']
    | add x y hx hy => simp_all [smul_add]

omit [Module B M] [IsScalarTower k B M] in
/-- In fact no dimension restriction on M is needed for right projectivity. -/
theorem projective_right [Module.Projective Bᵐᵒᵖ N] :
    Module.Projective Bᵐᵒᵖ (M ⊗[k] N) :=
  Module.Projective.of_equiv (rightSwap k B M N).symm


/-- The chosen right action is the restriction of the enveloping action. -/
theorem right_eq_enveloping (c : Bᵐᵒᵖ) (x : M ⊗[k] N) :
    c • x = (1 ⊗ₜ[k] c : B ⊗[k] Bᵐᵒᵖ) • x := by
  induction x using OAI.tensorInductionOn with
  | tmul m n => simp
  | add x y hx hy => simp_all [smul_add]

/-- The usual left action on the first tensor factor is the other restriction. -/
theorem left_eq_enveloping (b : B) (x : M ⊗[k] N) :
    b • x = (b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • x := by
  induction x using OAI.tensorInductionOn with
  | tmul m n => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp_all [smul_add]

instance commutingActions : SMulCommClass B Bᵐᵒᵖ (M ⊗[k] N) where
  smul_comm b c x := by
    induction x using OAI.tensorInductionOn with
    | tmul m n => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp_all [smul_add]

end ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_InducedColumns
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
noncomputable section

namespace ExternalTensor

attribute [local instance] bimodule rightModule

variable (k B : Type*) [Field k] [Ring B] [Algebra k B]

attribute [local instance] leftIdeal_finiteDimensional

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

theorem column_projective (e : B) [Module.Projective Bᵐᵒᵖ N] :
    Module.Projective Bᵐᵒᵖ (Column k B N e) :=
  projective_right k B (leftIdeal B e) N

end ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnFinite
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

theorem biprod_finite {X Y : ModuleCat.{u} k}
    (hX : FiniteDimensional k X) (hY : FiniteDimensional k Y) :
    FiniteDimensional k (X ⊞ Y : ModuleCat.{u} k) := by
  let := hX
  let := hY
  apply finite_of_iso k (ModuleCat.biprodIsoProd X Y)
  change Module.Finite k (X × Y)
  infer_instance

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerSpaces
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.CornerSpaces
open ThreeVertexAlgebra

universe u
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)

/-- The actual two-sided corner e_i B e_j as a vector subspace. -/
def corner (i j : Fin 3) : Submodule k (ThreeVertexAlgebra μ) where
  carrier := {x | vertex μ i * x * vertex μ j = x}
  zero_mem' := by
    change vertex μ i * (0 : ThreeVertexAlgebra μ) * vertex μ j = 0
    rw [mul_zero,zero_mul]
  add_mem' := by
    intro x y hx hy
    change vertex μ i * x * vertex μ j = x at hx
    change vertex μ i * y * vertex μ j = y at hy
    change vertex μ i * (x+y) * vertex μ j = x+y
    rw [mul_add,add_mul,hx,hy]
  smul_mem' := by
    intro r x hx
    change vertex μ i * x * vertex μ j = x at hx
    change vertex μ i * (r • x) * vertex μ j = r • x
    rw [mul_smul_comm,smul_mul_assoc,hx]

/-- A diagonal corner has only its scalar trivial path. -/
noncomputable def diagonalEquiv (i : Fin 3) : corner μ i i ≃ₗ[k] k where
  toFun x := if i = 0 then x.val.1 else if i = 1 then x.val.2.1 else x.val.2.2.1
  invFun c := ⟨c • vertex μ i,by
    change vertex μ i * (c • vertex μ i) * vertex μ i = c • vertex μ i
    rw [mul_smul_comm,smul_mul_assoc]
    have hi := (directedSystem μ).idem i
    change vertex μ i * vertex μ i = vertex μ i at hi
    rw [hi,hi]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.property
    change mul μ (mul μ (vertex μ i) x.val) (vertex μ i) = x.val at hx
    fin_cases i <;> simpa [vertex,mul,smul_eq μ] using hx
  right_inv c := by fin_cases i <;> simp [vertex,smul_eq μ]
  map_add' x y := by fin_cases i <;> rfl
  map_smul' c x := by fin_cases i <;> rfl

end LittleFinitistic.CornerSpaces

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerProjection
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
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

theorem corner_left_fixed (i j : Fin 3) (x : corner μ i j) : vertex μ i * x.val = x.val := by
  have hx := x.property
  change vertex μ i * x.val * vertex μ j = x.val at hx
  calc
    vertex μ i * x.val = vertex μ i * (vertex μ i * x.val * vertex μ j) := congrArg (fun a : ThreeVertexAlgebra μ => vertex μ i * a) hx.symm
    _ = vertex μ i * x.val * vertex μ j := by simp only [← mul_assoc,videm]
    _ = x.val := hx

theorem corner_right_fixed (i j : Fin 3) (x : corner μ i j) : x.val * vertex μ j = x.val := by
  have hx := x.property
  change vertex μ i * x.val * vertex μ j = x.val at hx
  calc
    x.val * vertex μ j = (vertex μ i * x.val * vertex μ j) * vertex μ j := congrArg (fun a : ThreeVertexAlgebra μ => a * vertex μ j) hx.symm
    _ = vertex μ i * x.val * vertex μ j := by rw [mul_assoc,videm]
    _ = x.val := hx

end LittleFinitistic.CornerProjection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TensorProjection
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.ExternalTensor.columnInclusion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.TensorProjection
attribute [local instance] ExternalTensor.rightModule
variable {k B M M' N : Type*} [Field k] [Ring B] [Algebra k B]
  [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

/-- Tensor a k-linear map with the identity while retaining the actual right B-action. -/
def rightMap (f : M →ₗ[k] M') : (M ⊗[k] N) →ₗ[Bᵐᵒᵖ] (M' ⊗[k] N) where
  __ := (TensorProduct.map f LinearMap.id).toAddMonoidHom
  map_smul' c x := by
    induction x using OAI.tensorInductionOn with
    | tmul m n => simp [ExternalTensor.right_smul_tmul]
    | add x y hx hy => simp_all [smul_add]

@[simp] theorem rightMap_tmul (f : M →ₗ[k] M') (m : M) (n : N) :
    rightMap (B := B) f (m ⊗ₜ[k] n) = f m ⊗ₜ[k] n := rfl

/-- Transport a first-factor vector-space equivalence as an actual right-module equivalence. -/
def rightCongr (e : M ≃ₗ[k] M') : (M ⊗[k] N) ≃ₗ[Bᵐᵒᵖ] (M' ⊗[k] N) where
  __ := rightMap (B := B) (N := N) e.toLinearMap
  invFun := rightMap (B := B) (N := N) e.symm.toLinearMap
  left_inv x := by
    induction x using OAI.tensorInductionOn with
    | tmul m n => simp
    | add x y hx hy => simp_all
  right_inv x := by
    induction x using OAI.tensorInductionOn with
    | tmul m n => simp
    | add x y hx hy => simp_all

variable (p : M →ₗ[k] M)

/-- The actual fixed submodule for a projector on the first tensor factor. -/
def fixed : Submodule Bᵐᵒᵖ (M ⊗[k] N) := (rightMap (B := B) p - LinearMap.id).ker

@[simp] theorem mem_fixed (x : M ⊗[k] N) : x ∈ fixed (B := B) p ↔ rightMap (B := B) p x = x := by
  simp [fixed,sub_eq_zero]

/-- The eigenspace e(M tensor N) is exactly (eM) tensor N as a right module. -/
def imageTensorEquiv (hp : p.comp p = p) : (p.range ⊗[k] N) ≃ₗ[Bᵐᵒᵖ] fixed (B := B) (N := N) p where
  toFun x := ⟨rightMap (B := B) (N := N) p.range.subtype x,by
    rw [mem_fixed]
    induction x using OAI.tensorInductionOn with
    | tmul m n => simp [range_fixed p hp m]
    | add x y hx hy => simp_all⟩
  invFun x := rightMap (B := B) (N := N) p.rangeRestrict x.val
  left_inv x := by
    induction x using OAI.tensorInductionOn with
    | tmul m n =>
      simp only [rightMap_tmul]
      congr 1
      apply Subtype.ext
      exact range_fixed p hp m
    | add x y hx hy => simp_all
  right_inv x := by
    apply Subtype.ext
    have h : rightMap (B := B) p.range.subtype (rightMap (B := B) (N := N) p.rangeRestrict x.val) =
        rightMap (B := B) p x.val := by
      generalize x.val = y
      induction y using OAI.tensorInductionOn with
      | tmul m n => rfl
      | add a b ha hb => simp_all
    exact h.trans ((mem_fixed p x.val).1 x.property)
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' c x := Subtype.ext (map_smul _ c x)
end LittleFinitistic.TensorProjection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TensorComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.ExternalTensor.columnInclusion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace LittleFinitistic.TensorComplex
attribute [local instance] ExternalTensor.rightModule
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

variable {k B}
/-- The actual tensor differential, with the original right B-action. -/
def mapRight (M : ModuleCat.{u} k) {N N' : ModuleCat.{u} Bᵐᵒᵖ} (g : N ⟶ N') :
    (M ⊗[k] ScalarModule k B N) →ₗ[Bᵐᵒᵖ] (M ⊗[k] ScalarModule k B N') where
  __ := (TensorProduct.map LinearMap.id
    ((ModuleCat.restrictScalars (algebraMap k Bᵐᵒᵖ)).map g).hom).toAddMonoidHom
  map_smul' c x := by
    induction x using OAI.tensorInductionOn with
    | tmul m n =>
      change TensorProduct.mk k M (ScalarModule k B N') m (g.hom (c • (n : N))) = TensorProduct.mk k M (ScalarModule k B N') m (c • g.hom n)
      exact congrArg (TensorProduct.mk k M (ScalarModule k B N') m) (g.hom.map_smul c (n : N))
    | add x y hx hy => simp_all [smul_add]

@[simp] theorem mapRight_tmul (M : ModuleCat.{u} k) {N N' : ModuleCat.{u} Bᵐᵒᵖ}
    (g : N ⟶ N') (m : M) (n : ScalarModule k B N) :
    mapRight M g (m ⊗ₜ[k] n) = TensorProduct.mk k M (ScalarModule k B N') m (g.hom n) := rfl

variable (D : CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ)
/-- Tensor a vector space with every term and differential of the given right-module complex. -/
def complex (M : ModuleCat.{u} k) : CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ where
  X i := ModuleCat.of Bᵐᵒᵖ (M ⊗[k] ScalarModule k B (D.X i))
  d i j := ModuleCat.ofHom (mapRight M (D.d i j))
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul m n =>
      have h : (D.d i j).hom (n : D.X i) = 0 := by rw [D.shape i j hij]; rfl
      exact (congrArg (TensorProduct.mk k M (ScalarModule k B (D.X j)) m) h).trans
        (map_zero (TensorProduct.mk k M (ScalarModule k B (D.X j)) m))
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  d_comp_d' i j l hij hjl := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul m n =>
      change TensorProduct.mk k M (ScalarModule k B (D.X l)) m ((D.d j l).hom ((D.d i j).hom n)) = 0
      have h := congrArg (fun f : D.X i ⟶ D.X l => f.hom n) (D.d_comp_d i j l)
      change (D.d j l).hom ((D.d i j).hom n) = 0 at h
      exact (congrArg (TensorProduct.mk k M (ScalarModule k B (D.X l)) m) h).trans
        (map_zero (TensorProduct.mk k M (ScalarModule k B (D.X l)) m))
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- The first-factor tensor map is a chain map. -/
def complexMap {M M' : ModuleCat.{u} k} (f : M ⟶ M') : complex D M ⟶ complex D M' where
  f i := ModuleCat.ofHom (TensorProjection.rightMap (B := B)
    (N := ScalarModule k B (D.X i)) f.hom)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul m n => rfl
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- The genuine additive tensor-with-D functor required by the path exact sequence. -/
def tensorFunctor : ModuleCat.{u} k ⥤ CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ where
  obj := complex D
  map := complexMap D
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul m n => rfl
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul m n => rfl
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

instance tensorFunctor_additive : (tensorFunctor (k := k) D).Additive where
  map_add {M M'} {f g} := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul m n => exact TensorProduct.add_tmul _ _ _
    | add x y hx hy =>
      change TensorProjection.rightMap (B := B) (f.hom + g.hom) (x+y) =
        TensorProjection.rightMap (B := B) f.hom (x+y) + TensorProjection.rightMap (B := B) g.hom (x+y)
      simp only [map_add]
      change TensorProjection.rightMap (B := B) (f.hom + g.hom) x =
        TensorProjection.rightMap (B := B) f.hom x + TensorProjection.rightMap (B := B) g.hom x at hx
      change TensorProjection.rightMap (B := B) (f.hom + g.hom) y =
        TensorProjection.rightMap (B := B) f.hom y + TensorProjection.rightMap (B := B) g.hom y at hy
      rw [hx,hy]
      abel

end LittleFinitistic.TensorComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TotalFinite
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
noncomputable section
namespace ExternalTensor.Section4
universe u
variable {k : Type u} [Field k]
section General
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
variable {L₀ L₁ L₂ : CochainComplex C ℤ} (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁)
    (h : Homotopy (q ≫ p) 0)

/-- The rectification total has finite-dimensional terms whenever
an additive scalar restriction makes all three columns finite-dimensional. -/
theorem total_finite_after (F : C ⥤ ModuleCat.{u} k) [F.Additive]
    (h₀ : ∀ i, FiniteDimensional k (F.obj (L₀.X i)))
    (h₁ : ∀ i, FiniteDimensional k (F.obj (L₁.X i)))
    (h₂ : ∀ i, FiniteDimensional k (F.obj (L₂.X i))) (i : ℤ) :
    FiniteDimensional k (F.obj ((LittleFinitistic.RectificationTotal.total p q h).X i)) := by
  let := preservesBinaryBiproducts_of_preservesBiproducts F
  apply finite_of_iso k (F.mapIso (LittleFinitistic.RectificationTotal.termIso p q h i) ≪≫
    F.mapBiprod _ _ ≪≫ biprod.mapIso (F.mapBiprod _ _) (Iso.refl _))
  exact biprod_finite k (biprod_finite k (h₂ (i+2)) (h₁ (i+1))) (h₀ i)

end General

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedFiniteTensorEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BalancedTensor
universe u v w z
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

instance tensorFinite (M : Type w) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
    [FiniteDimensional k M] [FiniteDimensional k N] : FiniteDimensional k (Tensor k A M N) := by
  unfold Tensor
  infer_instance

theorem tensorFunctor_finite [FiniteDimensional k Aᵐᵒᵖ] [FiniteDimensional k N]
    (M : ModuleCat.{w} Aᵐᵒᵖ) [Module.Finite Aᵐᵒᵖ M] :
    FiniteDimensional k ((tensorFunctor k A N).obj M) := by
  let : Module.Finite Aᵐᵒᵖ (ScalarModule k A M) := inferInstanceAs (Module.Finite Aᵐᵒᵖ M)
  let : Module.Finite k (ScalarModule k A M) := Module.Finite.trans Aᵐᵒᵖ (ScalarModule k A M)
  exact inferInstanceAs (FiniteDimensional k (Tensor k A (ScalarModule k A M) N))

/-- The termwise evaluation preserves every actual zero term, hence bounded support. -/
theorem complex_zero (K : CochainComplex (ModuleCat.{w} Aᵐᵒᵖ) ℤ) (i : ℤ)
    (h : IsZero (K.X i)) :
    IsZero (((tensorFunctor k A N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K |>.X i) :=
  (tensorFunctor k A N).map_isZero h

/-- A bounded input has a bounded output with the same interval of possible nonzero terms. -/
theorem bounded_support (K : CochainComplex (ModuleCat.{w} Aᵐᵒᵖ) ℤ) (a b : ℤ)
    (h : ∀ i, i < a ∨ b < i → IsZero (K.X i)) :
    ∀ i, i < a ∨ b < i →
      IsZero (((tensorFunctor k A N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K |>.X i) :=
  fun i hi => complex_zero N K i (h i hi)
end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_BalancedFreeLeft
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor.FreeLeft
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (I M : Type u) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k Aᵐᵒᵖ M]

def evaluation : Tensor k A M (I →₀ A) →ₗ[k] (I →₀ M) :=
  lift (evaluateBilinear (k := k) I M) (by
    intro a m n
    induction n using Finsupp.induction_linear with
    | zero => simp only [smul_zero,map_zero]
    | add x y hx hy => simp only [smul_add,map_add,hx,hy]
    | single i x =>
      rw [Finsupp.smul_single,evaluateBilinear_single,evaluateBilinear_single]
      change Finsupp.single i (MulOpposite.op x • (MulOpposite.op a • m)) =
        Finsupp.single i (MulOpposite.op (a*x) • m)
      rw [← mul_smul,MulOpposite.op_mul])

@[simp] theorem evaluation_single (i : I) (a : A) (m : M) :
    evaluation (k := k) I M (mk k A M (I →₀ A) m (Finsupp.single i a)) =
      Finsupp.single i (MulOpposite.op a • m) := evaluateBilinear_single I M i a m

def insertion : (I →₀ M) →ₗ[k] Tensor k A M (I →₀ A) :=
  Finsupp.lsum k (fun i => (mk k A M (I →₀ A)).flip (Finsupp.single i 1))

omit [IsScalarTower k Aᵐᵒᵖ M] in
@[simp] theorem insertion_single (i : I) (m : M) :
    insertion (k := k) (A := A) I M (Finsupp.single i m) =
      mk k A M (I →₀ A) m (Finsupp.single i 1) := by
  simp only [insertion,Finsupp.lsum_single,LinearMap.flip_apply]

theorem evaluation_insertion (z : I →₀ M) :
    evaluation (k := k) (A := A) I M (insertion I M z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single i m => rw [insertion_single,evaluation_single,MulOpposite.op_one,one_smul]

theorem insertion_evaluation (z : Tensor k A M (I →₀ A)) :
    insertion I M (evaluation (k := k) I M z) = z := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n =>
    induction n using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add,hx,hy]
    | single i a =>
      rw [evaluation_single,insertion_single,balance]
      congr 1
      rw [Finsupp.smul_single,smul_eq_mul,mul_one]
  | ha x y hx hy => simp only [map_add,hx,hy]

/-- Tensor with an arbitrary free left module is the direct sum of the right module. -/
def equivalence : Tensor k A M (I →₀ A) ≃ₗ[k] (I →₀ M) where
  __ := evaluation (k := k) I M
  invFun := insertion I M
  left_inv := insertion_evaluation I M
  right_inv := evaluation_insertion I M

variable {M} {M' M'' : Type u}
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable [AddCommGroup M''] [Module k M''] [Module Aᵐᵒᵖ M''] [IsScalarTower k Aᵐᵒᵖ M'']

theorem evaluation_naturality (f : M →ₗ[Aᵐᵒᵖ] M') (z : Tensor k A M (I →₀ A)) :
    evaluation (k := k) I M' (mapLeft (I →₀ A) f z) =
      Finsupp.mapRange.linearMap (f.restrictScalars k) (evaluation (k := k) I M z) := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n =>
    induction n using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add,hx,hy]
    | single i a =>
      simp only [mapLeft_mk,evaluation_single]
      ext j
      change (Finsupp.single i (MulOpposite.op a • f m)) j =
        (Finsupp.mapRange f f.map_zero (Finsupp.single i (MulOpposite.op a • m))) j
      rw [Finsupp.mapRange_single, f.map_smul]
  | ha x y hx hy => simp only [map_add,hx,hy]

/-- Free left tensor preserves exact sequences of right modules. -/
theorem tensor_exact (f : M →ₗ[Aᵐᵒᵖ] M') (g : M' →ₗ[Aᵐᵒᵖ] M'')
    (h : Function.Exact f g) :
    Function.Exact (mapLeft (k := k) (I →₀ A) f) (mapLeft (k := k) (I →₀ A) g) := by
  intro z
  constructor
  · intro hz
    have hz' : Finsupp.mapRange.linearMap (g.restrictScalars k) (evaluation (k := k) I M' z) = 0 := by
      rw [← evaluation_naturality,hz,map_zero]
    obtain ⟨y,hy⟩ := (Free.finsupp_exact (k := k) I f g h _).mp hz'
    refine ⟨(equivalence (k := k) (A := A) I M).symm y, ?_⟩
    apply (equivalence (k := k) (A := A) I M').injective
    change evaluation (k := k) I M' (mapLeft (I →₀ A) f
      ((equivalence (k := k) (A := A) I M).symm y)) = _
    rw [evaluation_naturality]
    change Finsupp.mapRange.linearMap (f.restrictScalars k)
      ((equivalence (k := k) (A := A) I M) ((equivalence (k := k) (A := A) I M).symm y)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y,rfl⟩
    induction y using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n =>
      rw [mapLeft_mk,mapLeft_mk,(h (f m)).mpr ⟨m,rfl⟩,map_zero,LinearMap.zero_apply]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
end LittleFinitistic.BalancedTensor.FreeLeft

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_BalancedVertexImage
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
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

abbrev F := BalancedTensor.tensorFunctor k B N

end LittleFinitistic.BalancedVertexImage

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_IdempotentTensorMaps
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.IdempotentTensor
universe u v w
variable {A : Type v} [Ring A] {e e' : A}

/-- An element of e'Ae acts by left multiplication on the right projectives. -/
def leftMultiply (b : A) (hb : e'*b=b) : rightIdeal e →ₗ[Aᵐᵒᵖ] rightIdeal e' where
  toFun m := ⟨b*m.val, by change e'*(b*m.val)=b*m.val; rw [← mul_assoc,hb]⟩
  map_add' m n := Subtype.ext (mul_add b m.val n.val)
  map_smul' a m := by apply Subtype.ext; exact (mul_assoc b m.val a.unop).symm

@[simp] theorem leftMultiply_apply (b : A) (hb : e'*b=b) (m : rightIdeal e) :
    (leftMultiply b hb m).val = b*m.val := rfl

end LittleFinitistic.IdempotentTensor

end

end OAI
end


