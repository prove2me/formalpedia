-- Prove2me | Definitions.Def_OAIQ023F009
-- name    : OAIQ023F009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:47:08.821489+00:00
-- url     : https://prove2.me/theorems/8cc37605-6e3a-4894-87e8-0c7768b7115b
-- title:
--   Definitions bundle OAIQ023F009 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 59 declarations of OpenAI's Lean: 16 definitions, 1 instance and 42 theorems. The definitions and types are `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.complexDifferential`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.complexTermMap`, `OAI.LittleFinitistic.OrdinarySimulation.shiftSignIso`, `OAI.LittleFinitistic.ProductModules.intoFirst`, `OAI.LittleFinitistic.ProductModules.joinTo`, `OAI.LittleFinitistic.ProductModules.outOfFirst`, `OAI.LittleFinitistic.ProductModules.pairObject`, `OAI.LittleFinitistic.ProductModules.secondObject`, `OAI.LittleFinitistic.ProductModules.splitTo`, `OAI.LittleFinitistic.ProductModules.splitting`, `OAI.LittleFinitistic.RetainedBimodule.congr`, `OAI.LittleFinitistic.RetainedBimodule.map`, `OAI.LittleFinitistic.RetainedBimodule.rightEquiv`, `OAI.LittleFinitistic.RetainedBimodule.scalarEquiv`, `OAI.LittleFinitistic.SingleBimoduleTensor.coefficientEquivAt`, `OAI.LittleFinitistic.SingleBimoduleTensor.zeroCoefficientEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Encoding_ThreeVertexAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Encoding/ThreeVertexAlgebra.lean), [`Finitistic_Ordinary_OrdinaryOffDiagonalComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryOffDiagonalComplex.lean), [`Finitistic_Ordinary_OrdinaryOffDiagonalComplexMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryOffDiagonalComplexMaps.lean), [`Finitistic_Ordinary_OrdinaryProductComponent`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryProductComponent.lean), [`Finitistic_Ordinary_OrdinaryProductProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryProductProjective.lean), [`Finitistic_Ordinary_OrdinaryProductSplitting`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryProductSplitting.lean), [`Finitistic_Ordinary_OrdinaryRetainedBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryRetainedBimodule.lean), [`Finitistic_Ordinary_OrdinaryRetainedCongruence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryRetainedCongruence.lean), [`Finitistic_Ordinary_OrdinaryRetainedRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryRetainedRestriction.lean), [`Finitistic_Ordinary_OrdinaryShiftDerivedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryShiftDerivedTensor.lean), [`Finitistic_Ordinary_OrdinaryShiftSign`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryShiftSign.lean), [`Finitistic_Ordinary_OrdinarySingleTensorTerms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinarySingleTensorTerms.lean).
--
--   **Imports.** It imports the bundles `OAIQ023F000`, `OAIQ023F001`, `OAIQ023F002` and `OAIQ023F004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ023F015`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F000
import Definitions.Def_OAIQ023F001
import Definitions.Def_OAIQ023F002
import Definitions.Def_OAIQ023F004

section
-- module Solutions.OAIQ023_Fin.Compat
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_ThreeVertexAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u v
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

namespace ThreeVertexAlgebra
variable (μ : W →ₗ[k] V →ₗ[k] U)

instance instFiniteDimensional [FiniteDimensional k V] [FiniteDimensional k W] [FiniteDimensional k U] :
    FiniteDimensional k (ThreeVertexAlgebra μ) :=
  inferInstanceAs (FiniteDimensional k (k × k × k × V × W × U))

open CategoryTheory
end ThreeVertexAlgebra
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryRetainedBimodule
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
namespace RetainedBimodule
variable (k S A M : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]

variable {k S A M} {M' : Type u}
variable [AddCommGroup M'] [Module k M'] [Module S M'] [Module Aᵐᵒᵖ M']
  [IsScalarTower k S M'] [IsScalarTower k Aᵐᵒᵖ M'] [SMulCommClass S Aᵐᵒᵖ M']

def map (f : M →ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m) :
    RetainedBimodule k S A M →ₗ[S ⊗[k] Aᵐᵒᵖ] RetainedBimodule k S A M' where
  __ := f.toAddHom
  map_smul' x m := by
    change f (action k S A M x m) = action k S A M' x (f m)
    induction x using OAI.tensorInductionOn with
    | tmul s a =>
      change f (s • (a • (m : M))) = s • (a • f (m : M))
      exact (hf s (a • (m : M))).trans (congrArg (s • ·) (f.map_smul a (m : M)))
    | add x y hx hy =>
      rw [map_add, map_add]
      exact (f.map_add _ _).trans (congrArg₂ (· + ·) hx hy)
end RetainedBimodule
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ)
variable (T : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ)

def complexDifferential (n : ℤ) :=
  RetainedBimodule.map (k := k) (S := L × R) (A := L × R)
    (map (BimoduleCoefficients.map k R L (O.d n (n+1)))
      (BimoduleCoefficients.map k L R (T.d n (n+1))))
    (map_left (BimoduleCoefficients.map k R L (O.d n (n+1)))
      (BimoduleCoefficients.map_left k R L (O.d n (n+1)))
      (BimoduleCoefficients.map k L R (T.d n (n+1)))
      (BimoduleCoefficients.map_left k L R (T.d n (n+1))))

theorem complexDifferential_square (n : ℤ) :
    (complexDifferential k L R O T (n+1)).comp (complexDifferential k L R O T n) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun f => f.hom x.1) (O.d_comp_d n (n+1) ((n+1)+1))
  · exact congrArg (fun f => f.hom x.2) (T.d_comp_d n (n+1) ((n+1)+1))

end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalComplexMaps
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable {O O' : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ}
variable {T T' : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ}

def complexTermMap (f : O ⟶ O') (g : T ⟶ T') (n : ℤ) :=
  RetainedBimodule.map (k := k) (S := L × R) (A := L × R)
    (map (BimoduleCoefficients.map k R L (f.f n)) (BimoduleCoefficients.map k L R (g.f n)))
    (map_left (BimoduleCoefficients.map k R L (f.f n))
      (BimoduleCoefficients.map_left k R L (f.f n))
      (BimoduleCoefficients.map k L R (g.f n))
      (BimoduleCoefficients.map_left k L R (g.f n)))

end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductComponent
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]
variable (M : ModuleCat.{v} (L × R))

variable {M} {N : ModuleCat.{v} (L × R)}

/-- Surjections remain surjections on the selected component, by projecting a preimage. -/
theorem firstMap_surjective (f : M ⟶ N) (hf : Function.Surjective f.hom) :
    Function.Surjective (firstMap L R f) := by
  intro y
  obtain ⟨x,hx⟩ := hf y.val
  refine ⟨⟨((1,0) : L × R) • x,?_⟩,?_⟩
  · change ((1,0) : L × R) • (((1,0) : L × R) • x) = ((1,0) : L × R) • x
    rw [← mul_smul]
    have h : ((1,0) : L × R) * (1,0) = (1,0) := by ext <;> simp
    rw [h]
  · apply Subtype.ext
    change f.hom (((1,0) : L × R) • x) = y.val
    rw [f.hom.map_smul,hx,y.property]
end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductProjective
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ProductModules.firstFunctor_additive _root_.OAI.LittleFinitistic.ProductModules.firstFunctor_preservesFiniteColimits _root_.OAI.LittleFinitistic.ProductModules.firstFunctor_preservesFiniteLimits _root_.OAI.LittleFinitistic.ProductModules.firstFunctor_preservesHomology _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

variable {P : ModuleCat.{v} L} {M : ModuleCat.{v} (L × R)}

def intoFirst (g : (firstInflation L R).obj P ⟶ M) : P ⟶ firstObject L R M :=
  ModuleCat.ofHom
    { toFun := fun x => ⟨g.hom x, by
        have h := g.hom.map_smul ((1,0) : L × R) x
        change g.hom ((1:L) • x) = ((1,0) : L × R) • g.hom x at h
        rw [one_smul] at h
        exact h.symm⟩
      map_add' := fun x y => Subtype.ext (g.hom.map_add x y)
      map_smul' := fun r x => Subtype.ext (g.hom.map_smul ((r,0) : L × R) x) }

theorem firstSpace_product_smul (d : L × R) (x : firstSpace L R M) :
    d • x.val = ((d.1,0) : L × R) • x.val := by
  have he : d * ((1,0) : L × R) = (d.1,0) := by ext <;> simp
  calc
    d • x.val = d • (((1,0) : L × R) • x.val) := by rw [x.property]
    _ = (d * ((1,0) : L × R)) • x.val := (mul_smul _ _ _).symm
    _ = _ := by rw [he]

def outOfFirst (g : P ⟶ firstObject L R M) : (firstInflation L R).obj P ⟶ M := by
  letI : Module (L × R) P := Module.compHom P (RingHom.fst L R)
  exact ModuleCat.ofHom (show (firstInflation L R).obj P →ₗ[L × R] M from
    { toFun := fun x => (g.hom x).val
      map_add' := fun x y => congrArg Subtype.val (g.hom.map_add x y)
      map_smul' := fun d x => by
        have h := congrArg Subtype.val (g.hom.map_smul d.1 x)
        exact h.trans (firstSpace_product_smul L R d (g.hom x)).symm })

/-- Inflation from one factor preserves actual projective objects. -/
theorem firstInflation_projective (P : ModuleCat.{v} L) [Projective P] :
    Projective ((firstInflation L R).obj P) := by
  refine ⟨fun g E he => ?_⟩
  let e : firstObject L R _ ⟶ firstObject L R _ := (firstFunctor L R).map E
  let g' := intoFirst L R g
  let : Epi e := (ModuleCat.epi_iff_surjective e).mpr
    (firstMap_surjective L R E ((ModuleCat.epi_iff_surjective E).mp he))
  let h := Projective.factorThru g' e
  refine ⟨outOfFirst L R h,?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hh := congrArg (fun f => f.hom x) (Projective.factorThru_comp g' e)
  exact congrArg Subtype.val hh
end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductSplitting
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

abbrev secondObject (M : ModuleCat.{v} (L × R)) : ModuleCat.{v} R :=
  firstObject R L (swapModule L R M)

abbrev pairObject (M : ModuleCat.{v} (L × R)) : ModuleCat.{v} (L × R) := ModuleCat.of (L × R)
  (((firstInflation L R).obj (firstObject L R M)) × ((secondInflation L R).obj (secondObject L R M)))

variable (M : ModuleCat.{v} (L × R))

def splitTo : M →ₗ[L × R] pairObject L R M where
  toFun m := (⟨((1,0) : L × R) • m, by
    change ((1,0) : L × R) • (((1,0) : L × R) • m) = ((1,0) : L × R) • m
    rw [← mul_smul]
    have h : ((1,0) : L × R) * (1,0) = (1,0) := by ext <;> simp
    rw [h]⟩, ⟨((0,1) : L × R) • m, by
    change ((0,1) : L × R) • (((0,1) : L × R) • m) = ((0,1) : L × R) • m
    rw [← mul_smul]
    have h : ((0,1) : L × R) * (0,1) = (0,1) := by ext <;> simp
    rw [h]⟩)
  map_add' x y := Prod.ext (Subtype.ext (smul_add _ _ _)) (Subtype.ext (smul_add _ _ _))
  map_smul' d m := by
    apply Prod.ext
    · apply Subtype.ext
      change ((1,0) : L × R) • (d • m) = ((d.1,0) : L × R) • (((1,0) : L × R) • m)
      rw [← mul_smul,← mul_smul]
      congr 1
      ext <;> simp
    · apply Subtype.ext
      change ((0,1) : L × R) • (d • m) = ((0,d.2) : L × R) • (((0,1) : L × R) • m)
      rw [← mul_smul,← mul_smul]
      congr 1
      ext <;> simp

def joinTo : pairObject L R M →ₗ[L × R] M where
  toFun x := x.1.val + (show M from x.2.val)
  map_add' x y := by
    change (x.1.val+y.1.val) + ((show M from x.2.val)+(show M from y.2.val)) =
      (x.1.val+(show M from x.2.val)) + (y.1.val+(show M from y.2.val))
    abel
  map_smul' d x := by
    have h₁ := firstSpace_product_smul L R d x.1
    have h₂ := firstSpace_product_smul R L (M := swapModule L R M) (d.2,d.1) x.2
    change ((d.1,0) : L × R) • x.1.val + ((0,d.2) : L × R) • (show M from x.2.val) = d • (x.1.val + (show M from x.2.val))
    rw [smul_add,← h₁]
    exact congrArg (fun y : swapModule L R M => d • x.1.val + (show M from y)) h₂.symm

/-- Every module over a product ring splits into its two actual central-idempotent components. -/
def splitting : M ≃ₗ[L × R] pairObject L R M where
  __ := splitTo L R M
  invFun := joinTo L R M
  left_inv m := by
    change ((1,0) : L × R) • m + ((0,1) : L × R) • m = m
    rw [← add_smul]
    have h : ((1,0) : L × R) + (0,1) = 1 := by ext <;> simp
    rw [h,one_smul]
  right_inv x := by
    have h₁ : ((1,0) : L × R) • x.1.val = x.1.val := x.1.property
    have h₂ : ((0,1) : L × R) • (show M from x.2.val) = (show M from x.2.val) := x.2.property
    have hz₁ : ((0,1) : L × R) • x.1.val = 0 := by
      calc
        _ = ((0,1) : L × R) • (((1,0) : L × R) • x.1.val) := by rw [h₁]
        _ = 0 := by
          rw [← mul_smul]
          have h : ((0,1) : L × R) * (1,0) = 0 := by ext <;> simp
          rw [h,zero_smul]
    have hz₂ : ((1,0) : L × R) • (show M from x.2.val) = 0 := by
      calc
        _ = ((1,0) : L × R) • (((0,1) : L × R) • (show M from x.2.val)) := by rw [h₂]
        _ = 0 := by
          rw [← mul_smul]
          have h : ((1,0) : L × R) * (0,1) = 0 := by ext <;> simp
          rw [h,zero_smul]
    apply Prod.ext
    · apply Subtype.ext
      change ((1,0) : L × R) • (x.1.val + (show M from x.2.val)) = x.1.val
      rw [smul_add,h₁,hz₂,add_zero]
    · apply Subtype.ext
      change ((0,1) : L × R) • (x.1.val + (show M from x.2.val)) = (show M from x.2.val)
      rw [smul_add,hz₁,h₂,zero_add]
end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryRetainedRestriction
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.RetainedBimodule
universe u
variable (k S A M : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]

/-- Recover the exact original right action after packaging the ordinary bimodule. -/
def rightEquiv : BimoduleCoefficients k S A (object k S A M) ≃ₗ[Aᵐᵒᵖ] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change action k S A M ((1:S) ⊗ₜ[k] r) x = _
    unfold action
    erw [Algebra.TensorProduct.lift_tmul]
    change (1:S) • (r • (show M from x)) = r • (show M from x)
    exact one_smul _ _

theorem rightEquiv_left (s : S) (x : BimoduleCoefficients k S A (object k S A M)) :
    rightEquiv k S A M (s • x) = s • rightEquiv k S A M x := by
  change action k S A M (s ⊗ₜ[k] (1:Aᵐᵒᵖ)) x = _
  unfold action
  erw [Algebra.TensorProduct.lift_tmul]
  change s • ((1:Aᵐᵒᵖ) • (show M from x)) = s • (show M from x)
  rw [one_smul]

/-- Recover the exact original scalar module after retaining both actions. -/
def scalarEquiv : (ModuleCat.restrictScalars (algebraMap k (S ⊗[k] Aᵐᵒᵖ))).obj
    (object k S A M) ≃ₗ[k] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    have h (y : RetainedBimodule k S A M) :
        (algebraMap k (S ⊗[k] Aᵐᵒᵖ) r) • y = r • y := algebraMap_smul _ r y
    exact h x
end LittleFinitistic.RetainedBimodule

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryRetainedCongruence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RetainedBimodule
universe u
variable {k S A M N : Type u} [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module S N] [Module Aᵐᵒᵖ N]
  [IsScalarTower k S N] [IsScalarTower k Aᵐᵒᵖ N] [SMulCommClass S Aᵐᵒᵖ N]

/-- An actual right-linear, left-equivariant equivalence retains both actions. -/
def congr (f : M ≃ₗ[Aᵐᵒᵖ] N) (hf : ∀ (s : S) x, f (s • x) = s • f x) :
    RetainedBimodule k S A M ≃ₗ[S ⊗[k] Aᵐᵒᵖ] RetainedBimodule k S A N where
  __ := map (k := k) f.toLinearMap hf
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv
end LittleFinitistic.RetainedBimodule

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryShiftSign
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The source's degree-n sign (-1)^(b*n), for all integers b and n. -/
def shiftSignIso (P : CochainComplex C ℤ) (b : ℤ) : unsignedShift P b ≅ P⟦b⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => integerUnitIso (P.X (n+b)) (b*n).negOnePow) (by
      intro n m h
      change n+1=m at h
      subst m
      change ((b*n).negOnePow • 𝟙 _) ≫ (b.negOnePow • P.d (n+b) (n+1+b)) =
        P.d (n+b) (n+1+b) ≫ ((b*(n+1)).negOnePow • 𝟙 _)
      simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.id_comp,
        Category.comp_id, smul_smul]
      rw [← Int.negOnePow_add]
      congr 2
      simp [mul_add, add_comm])
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryShiftDerivedTensor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

omit [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]
  [HasDerivedCategory.{u+1} (ModuleCat.{u} B)] in
theorem shifted_support (a : ℤ) (hb : a+(l:ℤ)=b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) (n : ℤ) (hn : n < -(l:ℤ) ∨ 0 < n) :
    IsZero ((P⟦b⟧).X n) := by
  change IsZero (P.X (n+b))
  apply hP
  omega
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySingleTensorTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

def zeroCoefficientEquiv : BimoduleCoefficients k S A ((complex k S A N).X 0) ≃ₗ[Aᵐᵒᵖ] N :=
  (BimoduleCoefficients.equiv k S A (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RetainedBimodule.object k S A N))).trans
    (RetainedBimodule.rightEquiv k S A N)

theorem zeroCoefficientEquiv_left (s : S) (x : BimoduleCoefficients k S A ((complex k S A N).X 0)) :
    zeroCoefficientEquiv k S A N (s • x) = s • zeroCoefficientEquiv k S A N x := by
  simp only [zeroCoefficientEquiv,LinearEquiv.trans_apply,BimoduleCoefficients.equiv_left,RetainedBimodule.rightEquiv_left]

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p) (i₀ : Fin l) (h₀ : p i₀ = 0)

def coefficientEquivAt (q : ℤ) (hq : q = 0) :
    BimoduleCoefficients k S A ((complex k S A N).X q) ≃ₗ[Aᵐᵒᵖ] N := by
  subst q
  exact zeroCoefficientEquiv k S A N

theorem coefficientEquivAt_left (q : ℤ) (hq : q = 0) (s : S)
    (x : BimoduleCoefficients k S A ((complex k S A N).X q)) :
    coefficientEquivAt k S A N q hq (s • x) = s • coefficientEquivAt k S A N q hq x := by
  subst q
  exact zeroCoefficientEquiv_left k S A N s x

end LittleFinitistic.SingleBimoduleTensor

end

end OAI
end


