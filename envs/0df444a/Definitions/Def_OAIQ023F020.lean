-- Prove2me | Definitions.Def_OAIQ023F020
-- name    : OAIQ023F020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T16:11:14.303366+00:00
-- url     : https://prove2.me/theorems/2df57605-6a38-4ce7-addd-5df661886a3e
-- title:
--   Definitions bundle OAIQ023F020 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 1 definition, 1 instance and 3 theorems. The definitions and types are `OAI.LittleFinitistic.TwoSidedTensor.congrLeft`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Ordinary_OrdinaryChainAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryChainAlgebra.lean), [`Finitistic_Ordinary_OrdinarySingleTensorTerms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinarySingleTensorTerms.lean), [`Finitistic_Ordinary_OrdinarySingleTensorTotal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinarySingleTensorTotal.lean), [`Finitistic_Ordinary_OrdinaryTwoSidedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryTwoSidedTensor.lean).
--
--   **Imports.** It imports the bundles `OAIQ023F012` and `OAIQ023F014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F023` and `OAIQ023F024`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F012
import Definitions.Def_OAIQ023F014

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

instance instAlgebra : Algebra k (ChainAlgebra k l) where
  algebraMap :=
    { toFun := fun c => (fun _ => c, fun _ => 0)
      map_one' := rfl
      map_mul' := by
        intro x y
        change ( ((fun _ => x*y), (0 : Fin l → k)) : ChainAlgebra k l) = mul k l (fun _ => x, 0) (fun _ => y, 0)
        apply Prod.ext <;> funext i <;> simp [mul]
      map_zero' := rfl
      map_add' := by
        intro x y
        change ((fun _ => x+y), (0 : Fin l → k)) = ((fun _ => x)+(fun _ => y), (0 : Fin l → k)+(0 : Fin l → k))
        apply Prod.ext <;> funext i <;> simp }
  commutes' c x := by
    apply Prod.ext <;> funext i
    · exact mul_comm c (x.1 i)
    · change c * x.2 i + 0 * x.1 i.castSucc = x.1 i.succ * 0 + x.2 i * c
      ring
  smul_def' c x := by
    apply Prod.ext <;> funext i
    · rfl
    · change c * x.2 i = c * x.2 i + 0 * x.1 i.castSucc
      ring

end ChainAlgebra

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySingleTensorTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

include hp h₀ in
theorem otherTerm_subsingleton (n : ℤ) (i : Fin l) (hi : i ≠ i₀) :
    Subsingleton (term k S A (complex k S A N) Z (p i) (n + -(p i))) := by
  have hz : p i ≠ 0 := by
    intro h
    exact hi (hp.injective (h.trans h₀.symm))
  have : Subsingleton (BimoduleCoefficients k S A ((complex k S A N).X (p i))) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (RetainedBimodule.object k S A N) (p i) hz)
  exact inferInstanceAs (Subsingleton (BalancedTensor.Tensor k A
    (BimoduleCoefficients k S A ((complex k S A N).X (p i))) (ComplexTensor.leftTerm k A Z (n + -(p i)))))

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

include hp h₀ in
theorem entry_selected_zero (n : ℤ) (z : totalTerm k S A (complex k S A N) Z p n) (i : Fin l) :
    entry k S A (complex k S A N) Z p n i i₀ (z i) = 0 := by
  by_cases hi : i = i₀
  · subst i
    unfold entry
    rw [dite_eq_right (show ¬ p i₀ + 1 = p i₀ by omega)]
    rfl
  · have hs := otherTerm_subsingleton k S A N Z p hp i₀ h₀ n i hi
    rw [hs.elim (z i) 0,map_zero]

include hp h₀ in
theorem differential_selected (n : ℤ) (z : totalTerm k S A (complex k S A N) Z p n) :
    differential k S A (complex k S A N) Z p n z i₀ =
      ((-(p i₀)).negOnePow • map k S A (complex k S A N) Z (𝟙 _)
        (Z.d (n + -(p i₀)) ((n+1) + -(p i₀)))) (z i₀) := by
  simp only [differential,LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply]
  rw [Finset.sum_eq_zero (fun i _ => entry_selected_zero k S A N Z p hp i₀ h₀ n z i),add_zero]

end LittleFinitistic.SingleBimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTwoSidedTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

variable {k A S T M N}
variable {M' : Type u} [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
  [Module S M'] [IsScalarTower k S M'] [SMulCommClass S Aᵐᵒᵖ M']

/-- Actual equivalences of the right factor on the left preserve the outside bimodule. -/
def congrLeft (e : M ≃ₗ[Aᵐᵒᵖ] M') (he : ∀ (s : S) m, e (s • m) = s • e m) :
    TwoSidedTensor k A S T M N ≃ₗ[S ⊗[k] T] TwoSidedTensor k A S T M' N where
  __ := map (T := T) (N := N) e.toLinearMap he
  invFun := map (T := T) (N := N) e.symm.toLinearMap (fun s m => by
    apply e.injective
    change e (e.symm (s • m)) = e (s • e.symm m)
    rw [LinearEquiv.apply_symm_apply,he,LinearEquiv.apply_symm_apply])
  left_inv z := by
    change BalancedTensor.mapLeft (k := k) N e.symm.toLinearMap
      (BalancedTensor.mapLeft (k := k) N e.toLinearMap z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n =>
      change mk k A S T M N (e.symm (e m)) n = mk k A S T M N m n
      rw [LinearEquiv.symm_apply_apply]
    | ha x y hx hy => simp only [map_add,hx,hy]
  right_inv z := by
    change BalancedTensor.mapLeft (k := k) N e.toLinearMap
      (BalancedTensor.mapLeft (k := k) N e.symm.toLinearMap z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n =>
      change mk k A S T M' N (e (e.symm m)) n = mk k A S T M' N m n
      rw [LinearEquiv.apply_symm_apply]
    | ha x y hx hy => simp only [map_add,hx,hy]
end TwoSidedTensor
end LittleFinitistic

end

end OAI
end


