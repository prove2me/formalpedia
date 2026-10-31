-- Prove2me | Definitions.Def_OAIQ023F015
-- name    : OAIQ023F015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:52:58.537409+00:00
-- url     : https://prove2.me/theorems/f8f23676-5657-4732-8a8d-0a756504c1d8
-- title:
--   Definitions bundle OAIQ023F015 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 51 definitions, 12 instances and 33 theorems. The definitions and types are `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.complex`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.complexMap`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.forgetIso`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.forgetTermIso`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.objectIso`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.objectMap`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.singleIso`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.singleTermIso`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.singles`, `OAI.LittleFinitistic.OrdinarySimulation.SecondBlockTensor.forward`, `OAI.LittleFinitistic.OrdinarySimulation.SecondBlockTensor.inverse`, `OAI.LittleFinitistic.OrdinarySimulation.SecondBlockTensor.source`, `OAI.LittleFinitistic.OrdinarySimulation.SecondBlockTensor.target`, `OAI.LittleFinitistic.OrdinarySimulation.TensorDirected.directedSystem`, `OAI.LittleFinitistic.PDBarQuotient.barQuotientIso`, `OAI.LittleFinitistic.PDBarQuotient.equiv`, `OAI.LittleFinitistic.PDBarQuotient.forward`, `OAI.LittleFinitistic.PDBarQuotient.inverse`, `OAI.LittleFinitistic.PDBarQuotient.nativeScalarEquiv`, `OAI.LittleFinitistic.PDBarQuotient.objectIso`, `OAI.LittleFinitistic.PDBarQuotient.scalarEquiv`, `OAI.LittleFinitistic.PDResidueAssociativity.barIso`, `OAI.LittleFinitistic.PDResidueAssociativity.coefficient`, `OAI.LittleFinitistic.PDResidueAssociativity.equiv`, `OAI.LittleFinitistic.PDResidueAssociativity.forward`, `OAI.LittleFinitistic.PDResidueAssociativity.inner`, `OAI.LittleFinitistic.PDResidueAssociativity.inverse`, `OAI.LittleFinitistic.PDResidueAssociativity.objectIso`, `OAI.LittleFinitistic.PDResidueAssociativity.pair`, `OAI.LittleFinitistic.PDResidueAssociativity.scalarTensorEquiv`, `OAI.LittleFinitistic.PDResidueAssociativity.unit`, `OAI.LittleFinitistic.PDResidueProjection.InflatedResidue`, `OAI.LittleFinitistic.PDResidueProjection.equiv`, `OAI.LittleFinitistic.PDResidueProjection.map`, `OAI.LittleFinitistic.PDResidueProjection.resolutionIso`, `OAI.LittleFinitistic.PDResidueProjection.rightEquiv`, `OAI.LittleFinitistic.PDResidueProjection.tensorEquiv`, `OAI.LittleFinitistic.PDResidueProjection.tensorNatIso`, `OAI.LittleFinitistic.PDResidueProjection.torIso`, `OAI.LittleFinitistic.PDResidueScalar.moduleK` and 11 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Dimension_PDBalancedRight`, `Finitistic_Dimension_PDBarQuotient`, `Finitistic_Dimension_PDBarQuotientAction`, `Finitistic_Dimension_PDBarTensorComparison`, `Finitistic_Dimension_PDResidueAssociativity`, `Finitistic_Dimension_PDResidueBaseBar`, `Finitistic_Dimension_PDResidueProjection`, `Finitistic_Dimension_PDResidueScalar`, `Finitistic_Dimension_PDResidueTensor`, `Finitistic_Dimension_PDTensorFunctor`, `Finitistic_Dimension_PDTor`, `Finitistic_Localization_VerdierEvaluationExact`, `Finitistic_Ordinary_OrdinaryBlockComplexes`, `Finitistic_Ordinary_OrdinaryChainAlgebra`, `Finitistic_Ordinary_OrdinaryFirstBlockTensor`, `Finitistic_Ordinary_OrdinaryOffDiagonalComplex`, `Finitistic_Ordinary_OrdinaryOffDiagonalComplexMaps`, `Finitistic_Ordinary_OrdinaryOffDiagonalForget`, `Finitistic_Ordinary_OrdinaryOffDiagonalObjects`, `Finitistic_Ordinary_OrdinaryOffDiagonalProjective`, `Finitistic_Ordinary_OrdinaryOffDiagonalSingle`, `Finitistic_Ordinary_OrdinaryProductDimension`, `Finitistic_Ordinary_OrdinaryProductSecondDimension`, `Finitistic_Ordinary_OrdinaryRightProjective`, `Finitistic_Ordinary_OrdinarySecondBlockTensor`, `Finitistic_Ordinary_OrdinaryTensorDirected`, `Finitistic_Selection_SelectionIteration`.
--
--   **Imports.** It imports the bundles `OAIQ023F007`, `OAIQ023F008` and `OAIQ023F009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ023F019`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F007
import Definitions.Def_OAIQ023F008
import Definitions.Def_OAIQ023F009

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDBalancedRight
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.Free.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.Free.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_add _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_comp _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_id _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRightTo_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_tensorInv _root_.OAI.LittleFinitistic.IdempotentTensor.tensorInv_tensorEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open LinearMap Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]
variable {M N : Type u} [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def mapRight (f : M →ₗ[A] N) : BalancedTensor.Tensor k A U M →ₗ[k]
    BalancedTensor.Tensor k A U N :=
  BalancedTensor.lift
    ((BalancedTensor.mk k A U N).compl₁₂ LinearMap.id (f.restrictScalars k)) (by
      intro a u m
      change BalancedTensor.mk k A U N (MulOpposite.op a • u) (f m) =
        BalancedTensor.mk k A U N u (f (a • m))
      rw [f.map_smul, BalancedTensor.balance])

@[simp] theorem mapRight_mk (f : M →ₗ[A] N) (u : U) (m : M) :
    mapRight (k := k) U f (BalancedTensor.mk k A U M u m) =
      BalancedTensor.mk k A U N u (f m) := rfl

omit [Algebra k A] [IsScalarTower k A N] in
/-- Radical multiplication is killed by tensor with any right module
annihilated by the ring radical. -/
theorem mk_radical_zero
    (hU : ∀ a ∈ Ring.jacobson A, ∀ u : U, MulOpposite.op a • u = 0)
    (n : N) (hn : n ∈ Ring.jacobson A • (⊤ : Submodule A N)) (u : U) :
    BalancedTensor.mk k A U N u n = 0 := by
  let K : Submodule A N :=
    { carrier := {n | ∀ u : U, BalancedTensor.mk k A U N u n = 0}
      zero_mem' := fun u => map_zero _
      add_mem' := fun hx hy u => by rw [map_add, hx, hy, add_zero]
      smul_mem' := fun a x hx u => by rw [← BalancedTensor.balance]; exact hx _ }
  have hK : Ring.jacobson A • (⊤ : Submodule A N) ≤ K := by
    apply Submodule.smul_le.mpr
    intro a ha x _ u
    rw [← BalancedTensor.balance, hU a ha u]
    exact LinearMap.congr_fun (map_zero (BalancedTensor.mk k A U N)) x
  exact hK hn u

theorem mapRight_radical_zero
    (hU : ∀ a ∈ Ring.jacobson A, ∀ u : U, MulOpposite.op a • u = 0)
    (f : M →ₗ[A] N)
    (hf : LinearMap.range f ≤ Ring.jacobson A • (⊤ : Submodule A N)) :
    mapRight (k := k) U f = 0 := by
  apply BalancedTensor.ext
  intro u m
  exact mk_radical_zero (k := k) U hU (f m) (hf (mem_range_self f m)) u

end LittleFinitistic.PDTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDTensorFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

/-- Tensor with a fixed right module, on actual left modules over A. -/
def tensorFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} k where
  obj M := ModuleCat.of k (BalancedTensor.Tensor k A U (ScalarModule k A M))
  map {M N} f := ModuleCat.ofHom
    (mapRight (k := k) (M := ScalarModule k A M) (N := ScalarModule k A N) U f.hom)
  map_id M := by apply ModuleCat.hom_ext; apply BalancedTensor.ext; intros; rfl
  map_comp f g := by apply ModuleCat.hom_ext; apply BalancedTensor.ext; intros; rfl

instance tensorFunctorAdditive : (tensorFunctor k A U).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro u m
    exact map_add (BalancedTensor.mk k A U (ScalarModule k A N) u) (f.hom m) (g.hom m)
end LittleFinitistic.PDTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDBarQuotient
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.Free.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.Free.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_add _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_comp _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_id _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRightTo_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_tensorInv _root_.OAI.LittleFinitistic.IdempotentTensor.tensorInv_tensorEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)

variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- Quotient map from the detector tensor to the actual left D-linear bar quotient. -/
def forward : BalancedTensor.Tensor k A (RightBase f) V →ₗ[k] DerivedBar.Balanced.tensor f V :=
  BalancedTensor.lift
    ((TensorProduct.mk k (RightBase f) V).compr₂
      ((DerivedBar.Balanced.quotient f V).restrictScalars k))
    (fun a d v => DerivedBar.Balanced.balanced f V d a v)

omit [IsScalarTower k A V] in
/-- Every D-linear balancing relation lies in the detector's k-linear relation
space; the proof retains all left D multiples, rather than assuming the quotients equal. -/
theorem relations_kill : (DerivedBar.Balanced.relations f V).restrictScalars k ≤
    (BalancedTensor.relations k A (RightBase f) V).mkQ.ker := by
  intro z hz
  change (BalancedTensor.relations k A (RightBase f) V).mkQ z = 0
  have h : ∀ d : D, (BalancedTensor.relations k A (RightBase f) V).mkQ (d • z) = 0 := by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b,a,v,rfl⟩ := hx
      intro d
      rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      change (BalancedTensor.relations k A (RightBase f) V).mkQ
        ((d*(b*f a)) ⊗ₜ[k] v - (d*b) ⊗ₜ[k] (a • v)) = 0
      erw [← mul_assoc, map_sub]
      exact sub_eq_zero.mpr (BalancedTensor.balance (k := k) (M := RightBase f) a (d*b) v)
    | zero => intro d; rw [smul_zero]; exact map_zero _
    | add x y hx hy ihx ihy =>
      intro d
      rw [smul_add]
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) (ihx d) (ihy d)).trans (add_zero _))
    | smul c x hx ih => intro d; simpa [smul_smul] using ih (d*c)
  simpa only [one_smul] using h 1

def inverse : DerivedBar.Balanced.tensor f V →ₗ[k] BalancedTensor.Tensor k A (RightBase f) V :=
  ((DerivedBar.Balanced.relations f V).restrictScalars k).liftQ
    (BalancedTensor.relations k A (RightBase f) V).mkQ (relations_kill f V)

omit [IsScalarTower k A V] in
@[simp] theorem forward_mk (d : RightBase f) (v : V) :
    forward f V (BalancedTensor.mk k A (RightBase f) V d v) =
      DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v) := rfl

omit [IsScalarTower k A V] in
@[simp] theorem inverse_quotient (d : D) (v : V) :
    inverse f V (DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v)) =
      BalancedTensor.mk k A (RightBase f) V d v := rfl

/-- Canonical actual quotient equivalence, on representatives d tensor v. -/
def equiv : BalancedTensor.Tensor k A (RightBase f) V ≃ₗ[k] DerivedBar.Balanced.tensor f V :=
  LinearEquiv.ofLinearMap (forward f V) (inverse f V) (by
    apply ((DerivedBar.Balanced.relations f V).restrictScalars k).linearMap_qext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro d
    apply LinearMap.ext
    intro v
    rfl) (by
    apply BalancedTensor.ext
    intro base vector
    rfl)

end LittleFinitistic.PDBarQuotient

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDBarQuotientAction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The actual exterior D-action transferred through the proved quotient equivalence. -/
instance leftModule : Module D (BalancedTensor.Tensor k A (RightBase f) V) :=
  (equiv f V).toAddEquiv.module D

instance leftTower : IsScalarTower k D (BalancedTensor.Tensor k A (RightBase f) V) :=
  (equiv f V).isScalarTower (A := D)

end LittleFinitistic.PDBarQuotient

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDResidueTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.Free.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.Free.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_add _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_comp _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_id _root_.OAI.LittleFinitistic.BalancedTensor.mapLeft_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRightTo_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_tensorInv _root_.OAI.LittleFinitistic.IdempotentTensor.tensorInv_tensorEval _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open LinearMap Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def residueEval : BalancedTensor.Tensor k A (Residue (A := A)) N →ₗ[k] Top (A := A) N :=
  BalancedTensor.lift (residuePair (k := k) N) (by
    intro a s n
    induction s using Submodule.Quotient.induction_on with
    | _ b => change (radicalProduct N).mkQ ((b*a) • n) = _; rw [mul_smul]; rfl)

def residueInverse : Top (A := A) N →ₗ[k] BalancedTensor.Tensor k A (Residue (A := A)) N :=
  ((radicalProduct (A := A) N).restrictScalars k).liftQ
    (BalancedTensor.mk k A (Residue (A := A)) N (Submodule.Quotient.mk (1 : A))) (by
      intro n hn
      exact mk_radical_zero (k := k) (Residue (A := A)) residue_annihilated n hn _)

@[simp] theorem residueEval_mk (a : A) (n : N) :
    residueEval (k := k) N (BalancedTensor.mk k A (Residue (A := A)) N
      (Submodule.Quotient.mk a) n) = (radicalProduct N).mkQ (a • n) := rfl

@[simp] theorem residueInverse_mk (n : N) :
    residueInverse (k := k) N ((radicalProduct N).mkQ n) =
      BalancedTensor.mk k A (Residue (A := A)) N (Submodule.Quotient.mk (1 : A)) n := rfl

/-- The actual noncommutative tensor/quotient identification in cor:pd-detection. -/
def residueTensorEquiv : BalancedTensor.Tensor k A (Residue (A := A)) N ≃ₗ[k] Top (A := A) N where
  __ := residueEval (k := k) N
  invFun := residueInverse (k := k) N
  left_inv z := by
    change residueInverse (k := k) N (residueEval (k := k) N z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht s n =>
      induction s using Submodule.Quotient.induction_on with
      | _ a =>
        rw [residueEval_mk, residueInverse_mk, ← BalancedTensor.balance]
        congr 2
        change Submodule.Quotient.mk ((1 : A)*a) = Submodule.Quotient.mk a
        rw [one_mul]
    | ha x y hx hy => simp [hx,hy]
  right_inv z := by
    induction z using Submodule.Quotient.induction_on with
    | _ n =>
      change residueEval (k := k) N (residueInverse (k := k) N ((radicalProduct N).mkQ n)) = _
      rw [residueInverse_mk, residueEval_mk, one_smul]
      rfl

end LittleFinitistic.PDTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDTor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

/-- Tor is the left derived functor of the actual balanced tensor functor. -/
abbrev Tor (M : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} k :=
  ((tensorFunctor k A U).leftDerived n).obj M

variable [FiniteDimensional k A] (M : PDMinimal.FiniteModule k A)

def model : ChainComplex (ModuleCat k) ℕ :=
  ((tensorFunctor k A U).mapHomologicalComplex _).obj (PDMinimal.complex M)

/-- The chosen minimal resolution computes this actual derived functor. -/
def torIsoModel (n : ℕ) : Tor (k := k) U M.cat n ≅ (model U M).homology n :=
  (PDMinimal.resolution M).isoLeftDerivedObj (tensorFunctor k A U) n

variable (hU : ∀ a ∈ Ring.jacobson A, ∀ u : U, MulOpposite.op a • u = 0)

include hU in
/-- Minimality annihilates every tensor differential, including non-adjacent ones. -/
theorem model_d_zero (i j : ℕ) : (model U M).d i j = 0 := by
  change (tensorFunctor k A U).map ((PDMinimal.complex M).d i j) = 0
  by_cases h : i = j+1
  · subst i
    rw [PDMinimal.complex_d]
    apply ModuleCat.hom_ext
    exact @mapRight_radical_zero k A _ _ _ U _ _ _
      (ScalarModule k A (PDMinimal.term M (j+1)).cat)
      (ScalarModule k A (PDMinimal.term M j).cat)
      _ _ _ (scalarModuleTower k A (PDMinimal.term M (j+1)).cat)
      _ _ _ (scalarModuleTower k A (PDMinimal.term M j).cat)
      hU (PDMinimal.differential M j) (PDMinimal.differential_radical M j)
  · rw [(PDMinimal.complex M).shape i j (by change ¬ j+1=i; exact Ne.symm h)]
    exact Functor.map_zero _ _ _

/-- Homology of the tensor of a minimal resolution is its term, because all
its differentials have been proved zero. -/
def torIsoTerm (n : ℕ) : Tor (k := k) U M.cat n ≅
    (tensorFunctor k A U).obj (PDMinimal.term M n).cat :=
  torIsoModel U M n ≪≫
    (ShortComplex.LeftHomologyData.ofZeros ((model U M).sc n)
      (model_d_zero U M hU _ _) (model_d_zero U M hU _ _)).homologyIso
end LittleFinitistic.PDTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDBarTensorComparison
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The restricted scalar convention in the detector agrees with the original
compatible k action by actual tensor maps in both directions. -/
def scalarEquiv :
    (PDTensor.tensorFunctor k A (RightBase f)).obj (ModuleCat.of A V) ≃ₗ[k]
      BalancedTensor.Tensor k A (RightBase f) V :=
  LinearEquiv.ofLinearMap
    (PDTensor.mapRight (k := k) (M := PDTensor.ScalarModule k A (ModuleCat.of A V))
      (N := V) (RightBase f) LinearMap.id)
    (PDTensor.mapRight (k := k) (M := V)
      (N := PDTensor.ScalarModule k A (ModuleCat.of A V)) (RightBase f) LinearMap.id)
    (by apply BalancedTensor.ext; intros; rfl)
    (by apply BalancedTensor.ext; intros; rfl)

def nativeScalarEquiv : DerivedBar.Balanced.tensor f V ≃ₗ[k]
    (ModuleCat.restrictScalars (algebraMap k D)).obj
      (ModuleCat.of D (DerivedBar.Balanced.tensor f V)) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' c z := (IsScalarTower.algebraMap_smul D c z).symm

def objectIso :
    (PDTensor.tensorFunctor k A (RightBase f)).obj (ModuleCat.of A V) ≅
      (ModuleCat.restrictScalars (algebraMap k D)).obj
        (ModuleCat.of D (DerivedBar.Balanced.tensor f V)) :=
  (((scalarEquiv f V).trans (equiv f V)).trans (nativeScalarEquiv f V)).toModuleIso

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
theorem objectIso_natural (h : V →ₗ[A] W) :
    (PDTensor.tensorFunctor k A (RightBase f)).map (ModuleCat.ofHom h) ≫ (objectIso f W).hom =
      (objectIso f V).hom ≫ (ModuleCat.restrictScalars (algebraMap k D)).map
        (ModuleCat.ofHom (DerivedBar.Balanced.map f V W h)) := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.ext
  intro d v
  rfl

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The detector's tensor of the actual bar resolution is the bar worker's
balanced complex, after restricting only its exterior scalars. -/
def barQuotientIso :
    ((PDTensor.tensorFunctor k A (RightBase f)).mapHomologicalComplex _).obj
      (DerivedBar.projectiveResolution k A N).complex ≅
    ((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj
      (DerivedBar.tensorBarComplex k A D N f) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => objectIso f (DerivedBar.term k A N (n+1))) (by
      intro i j hij
      change j+1=i at hij
      subst i
      simpa only [DerivedBar.tensorBarComplex, DerivedBar.projectiveResolution, DerivedBar.complex, ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d] using (objectIso_natural f (DerivedBar.differential k A N (j+1))).symm)

end LittleFinitistic.PDBarQuotient

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDResidueProjection
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.PDResidueProjection
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D) (hf : Function.Surjective f)
variable (hsq : ∀ a ∈ RingHom.ker f.toRingHom, ∀ b ∈ RingHom.ker f.toRingHom, a*b=0)

def InflatedResidue (_f : A →ₐ[k] D) := PDTensor.Residue (A := D)
instance instAddCommGroupInflatedResidue : AddCommGroup (InflatedResidue f) := inferInstanceAs (AddCommGroup (PDTensor.Residue (A := D)))
instance instModuleInflatedResidue : Module k (InflatedResidue f) := inferInstanceAs (Module k (PDTensor.Residue (A := D)))
instance instModuleMulOppositeInflatedResidue : Module Aᵐᵒᵖ (InflatedResidue f) :=
  Module.compHom (PDTensor.Residue (A := D)) f.toRingHom.op
instance (priority := 50) instModuleMulOppositeInflatedResidue_1 : Module Dᵐᵒᵖ (InflatedResidue f) :=
  inferInstanceAs (Module Dᵐᵒᵖ (PDTensor.Residue (A := D)))
instance (priority := 50) instIsScalarTowerMulOppositeInflatedResidue : IsScalarTower k Dᵐᵒᵖ (InflatedResidue f) :=
  inferInstanceAs (IsScalarTower k Dᵐᵒᵖ (PDTensor.Residue (A := D)))
instance instIsScalarTowerMulOppositeInflatedResidue_1 : IsScalarTower k Aᵐᵒᵖ (InflatedResidue f) where
  smul_assoc c a s := by
    change MulOpposite.op (f (c • a.unop)) • (s : PDTensor.Residue (A := D)) =
      c • (MulOpposite.op (f a.unop) • (s : PDTensor.Residue (A := D)))
    rw [map_smul, MulOpposite.op_smul, smul_assoc]

def map : PDTensor.Residue (A := A) →ₗ[k] InflatedResidue f :=
  ((PDTensor.rightRadical (A := A)).restrictScalars k).liftQ
    (((PDTensor.rightRadical (A := D)).restrictScalars k).mkQ.comp f.toLinearMap) (by
      intro a ha
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have he := PDSquareZero.comap_jacobson f.toRingHom hf hsq
      change a ∈ Ring.jacobson A at ha
      rw [← he] at ha
      exact ha)

@[simp] theorem map_mk (a : A) : map f hf hsq (Submodule.Quotient.mk a) =
    (Submodule.Quotient.mk (f a) : PDTensor.Residue (A := D)) := rfl

/-- The radical quotient-ring comparison also respects the actual k action. -/
def equiv : PDTensor.Residue (A := A) ≃ₗ[k] InflatedResidue f :=
  LinearEquiv.ofBijective (map f hf hsq) (by
    have he : (fun s => map f hf hsq s) =
        (fun s => PDSquareZero.residueQuotientEquiv f.toRingHom hf hsq s) := by
      funext s
      induction s using Submodule.Quotient.induction_on with
      | _ a => exact (PDSquareZero.residueQuotientEquiv_mk f.toRingHom hf hsq a).symm
    change Function.Bijective (fun s => map f hf hsq s)
    rw [he]
    exact (PDSquareZero.residueQuotientEquiv f.toRingHom hf hsq).bijective)

/-- Its right A action is precisely restriction through the canonical projection. -/
def rightEquiv : PDTensor.Residue (A := A) ≃ₗ[Aᵐᵒᵖ] InflatedResidue f where
  __ := (equiv f hf hsq).toAddEquiv
  map_smul' a s := by
    induction s using Submodule.Quotient.induction_on with
    | _ b =>
      change (Submodule.Quotient.mk (f (b*a.unop)) : PDTensor.Residue (A := D)) =
        Submodule.Quotient.mk (f b * f a.unop)
      rw [map_mul]

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N]

def tensorEquiv : BalancedTensor.Tensor k A (PDTensor.Residue (A := A)) N ≃ₗ[k]
    BalancedTensor.Tensor k A (InflatedResidue f) N :=
  LinearEquiv.ofLinearMap
    (BalancedTensor.mapLeft (k := k) N (rightEquiv f hf hsq).toLinearMap)
    (BalancedTensor.mapLeft (k := k) N (rightEquiv f hf hsq).symm.toLinearMap)
    (by
      apply BalancedTensor.ext
      intro s n
      simp only [LinearMap.comp_apply, BalancedTensor.mapLeft_mk, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply])
    (by
      apply BalancedTensor.ext
      intro s n
      simp only [LinearMap.comp_apply, BalancedTensor.mapLeft_mk, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.id_apply])

/-- The residue projection comparison is natural on all actual left A-modules. -/
def tensorNatIso : PDTensor.tensorFunctor k A (PDTensor.Residue (A := A)) ≅
    PDTensor.tensorFunctor k A (InflatedResidue f) :=
  NatIso.ofComponents (fun M => (tensorEquiv f hf hsq (PDTensor.ScalarModule k A M)).toModuleIso)
    (by
      intro M L h
      apply ModuleCat.hom_ext
      apply BalancedTensor.ext
      intro s n
      rfl)

variable (M : ModuleCat.{u} A) (P : ProjectiveResolution M)
def resolutionIso :
    ((PDTensor.tensorFunctor k A (PDTensor.Residue (A := A))).mapHomologicalComplex _).obj P.complex ≅
    ((PDTensor.tensorFunctor k A (InflatedResidue f)).mapHomologicalComplex _).obj P.complex :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (tensorNatIso f hf hsq).app (P.complex.X n))
    (fun i j _ => ((tensorNatIso f hf hsq).hom.naturality (P.complex.d i j)).symm)

/-- Actual derived residue tensor is unchanged by the proved right-module identification. -/
def torIso (n : ℕ) : PDTensor.Tor (k := k) (PDTensor.Residue (A := A)) M n ≅
    PDTensor.Tor (k := k) (InflatedResidue f) M n :=
  P.isoLeftDerivedObj (PDTensor.tensorFunctor k A (PDTensor.Residue (A := A))) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (resolutionIso f hf hsq M P) ≪≫
    (P.isoLeftDerivedObj (PDTensor.tensorFunctor k A (InflatedResidue f)) n).symm
end LittleFinitistic.PDResidueProjection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDResidueAssociativity
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.Free.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.Free.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRightTo_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_mk _root_.OAI.LittleFinitistic.IdempotentTensor.tensorEval_tensorInv _root_.OAI.LittleFinitistic.IdempotentTensor.tensorInv_tensorEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDResidueAssociativity
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
local notation "S" => PDTensor.Residue (A := D)
local notation "SA" => PDResidueProjection.InflatedResidue f
local notation "T" => BalancedTensor.Tensor k A SA V
local notation "DV" => DerivedBar.Balanced.tensor f V

def coefficient (s : S) : PDBarQuotient.RightBase f →ₗ[k] V →ₗ[k] T where
  toFun d := BalancedTensor.mk k A SA V (MulOpposite.op (show D from d) • s)
  map_add' a b := by
    ext v
    exact (congrArg (fun x : SA => BalancedTensor.mk k A SA V x v)
      (add_smul (MulOpposite.op (show D from a))
        (MulOpposite.op (show D from b)) s)).trans
      (LinearMap.congr_fun ((BalancedTensor.mk k A SA V).map_add _ _) v)
  map_smul' c d := by
    ext v
    change BalancedTensor.mk k A SA V (MulOpposite.op (c • (show D from d)) • s) v = _
    rw [MulOpposite.op_smul, smul_assoc]
    exact LinearMap.congr_fun ((BalancedTensor.mk k A SA V).map_smul c _) v

def inner (s : S) : DV →ₗ[k] T :=
  (BalancedTensor.lift (coefficient f V s) (by
    intro a d v
    change BalancedTensor.mk k A SA V (MulOpposite.op ((show D from d)*f a) • s) v =
      BalancedTensor.mk k A SA V (MulOpposite.op (show D from d) • s) (a • v)
    rw [MulOpposite.op_mul, mul_smul]
    exact BalancedTensor.balance (k := k) (M := SA) a _ v)).comp (PDBarQuotient.inverse f V)

omit [IsScalarTower k A V] in
@[simp] theorem inner_mk (s : S) (d : D) (v : V) :
    inner f V s (DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v)) =
      BalancedTensor.mk k A SA V (MulOpposite.op d • s) v := rfl

def pair : S →ₗ[k] DV →ₗ[k] T where
  toFun := inner f V
  map_add' s t := by
    apply ((DerivedBar.Balanced.relations f V).restrictScalars k).linearMap_qext
    apply TensorProduct.ext
    ext d v
    change BalancedTensor.mk k A SA V (MulOpposite.op d • (s+t)) v =
      BalancedTensor.mk k A SA V (MulOpposite.op d • s) v + BalancedTensor.mk k A SA V (MulOpposite.op d • t) v
    rw [smul_add]
    exact LinearMap.congr_fun ((BalancedTensor.mk k A SA V).map_add _ _) v
  map_smul' c s := by
    apply ((DerivedBar.Balanced.relations f V).restrictScalars k).linearMap_qext
    apply TensorProduct.ext
    ext d v
    change BalancedTensor.mk k A SA V (MulOpposite.op d • (c • s)) v =
      c • BalancedTensor.mk k A SA V (MulOpposite.op d • s) v
    rw [smul_comm]
    exact LinearMap.congr_fun ((BalancedTensor.mk k A SA V).map_smul c _) v

def forward : BalancedTensor.Tensor k D S DV →ₗ[k] T :=
  BalancedTensor.lift (pair f V) (by
    intro d s z
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      induction z using OAI.tensorInductionOn with
      | tmul b v =>
        change inner f V (MulOpposite.op d • s) (DerivedBar.Balanced.quotient f V (b ⊗ₜ[k] v)) =
          inner f V s (d • DerivedBar.Balanced.quotient f V (b ⊗ₜ[k] v))
        rw [inner_mk, ← LinearMap.map_smul, TensorProduct.smul_tmul', inner_mk]
        rw [← mul_smul, ← MulOpposite.op_mul]
        rfl
      | add x y hx hy => simpa only [Submodule.Quotient.mk_add, map_add, smul_add] using congrArg₂ (·+·) hx hy)

def unit : V →ₗ[k] DV :=
  ((DerivedBar.Balanced.quotient f V).restrictScalars k).comp (TensorProduct.mk k D V 1)

def inverse : T →ₗ[k] BalancedTensor.Tensor k D S DV :=
  BalancedTensor.lift ((BalancedTensor.mk k D S DV).compl₁₂ LinearMap.id (unit f V)) (by
    intro a s v
    change BalancedTensor.mk k D S DV (MulOpposite.op (f a) • s) (unit f V v) =
      BalancedTensor.mk k D S DV s (unit f V (a • v))
    erw [BalancedTensor.balance (k := k) (A := D) (M := S) (N := DV)
      (f a) (show S from s) (unit f V v)]
    congr 1
    change f a • DerivedBar.Balanced.quotient f V ((1 : D) ⊗ₜ[k] v) =
      DerivedBar.Balanced.quotient f V ((1 : D) ⊗ₜ[k] (a • v))
    rw [← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simpa only [one_mul] using DerivedBar.Balanced.balanced f V (1 : D) a v)

omit [IsScalarTower k A V] in
@[simp] theorem inverse_mk (s : SA) (v : V) :
    inverse f V (BalancedTensor.mk k A SA V s v) = BalancedTensor.mk k D S DV s (unit f V v) := rfl

/-- Actual balanced associativity S tensor_D (D tensor_A V) = S tensor_A V,
with the right A action restricted along f. -/
def equiv : BalancedTensor.Tensor k D S DV ≃ₗ[k] T :=
  LinearEquiv.ofLinearMap (forward f V) (inverse f V) (by
    apply BalancedTensor.ext
    intro s v
    change BalancedTensor.mk k A SA V (MulOpposite.op (1 : D) • s) v = _
    rw [MulOpposite.op_one, one_smul]
    rfl) (by
    apply BalancedTensor.ext
    intro s z
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      induction z using OAI.tensorInductionOn with
      | tmul d v =>
        change BalancedTensor.mk k D S DV (MulOpposite.op d • s) (unit f V v) =
          BalancedTensor.mk k D S DV s (DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v))
        rw [BalancedTensor.balance]
        congr 1
        change d • DerivedBar.Balanced.quotient f V ((1 : D) ⊗ₜ[k] v) = _
        rw [← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy => simpa only [Submodule.Quotient.mk_add, map_add] using congrArg₂ (·+·) hx hy)
end LittleFinitistic.PDResidueAssociativity

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDResidueBaseBar
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- Scalar restriction coherence for an arbitrary right tensor factor. -/
def scalarTensorEquiv {R : Type u} [Ring R] [Algebra k R]
    (U V : Type u) [AddCommGroup U] [Module k U] [Module Rᵐᵒᵖ U]
    [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V] :
    (PDTensor.tensorFunctor k R U).obj (ModuleCat.of R V) ≃ₗ[k] BalancedTensor.Tensor k R U V :=
  LinearEquiv.ofLinearMap
    (PDTensor.mapRight (k := k) (M := PDTensor.ScalarModule k R (ModuleCat.of R V)) (N := V) U LinearMap.id)
    (PDTensor.mapRight (k := k) (M := V) (N := PDTensor.ScalarModule k R (ModuleCat.of R V)) U LinearMap.id)
    (by apply BalancedTensor.ext; intros; rfl) (by apply BalancedTensor.ext; intros; rfl)

variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
local notation "S" => PDTensor.Residue (A := D)
local notation "SA" => PDResidueProjection.InflatedResidue f

def objectIso : (PDTensor.tensorFunctor k A SA).obj (ModuleCat.of A V) ≅
    (PDTensor.tensorFunctor k D S).obj (ModuleCat.of D (DerivedBar.Balanced.tensor f V)) :=
  (((scalarTensorEquiv SA V).trans (equiv f V).symm).trans
    (scalarTensorEquiv S (DerivedBar.Balanced.tensor f V)).symm).toModuleIso

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
theorem objectIso_natural (h : V →ₗ[A] W) :
    (PDTensor.tensorFunctor k A SA).map (ModuleCat.ofHom h) ≫ (objectIso f W).hom =
      (objectIso f V).hom ≫ (PDTensor.tensorFunctor k D S).map
        (ModuleCat.ofHom (DerivedBar.Balanced.map f V W h)) := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.ext
  intro s v
  rfl

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def barIso :
    ((PDTensor.tensorFunctor k A SA).mapHomologicalComplex _).obj (DerivedBar.projectiveResolution k A N).complex ≅
      ((PDTensor.tensorFunctor k D S).mapHomologicalComplex _).obj (DerivedBar.tensorBarComplex k A D N f) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => objectIso f (DerivedBar.term k A N (n+1))) (by
    intro i j hij
    change j+1=i at hij
    subst i
    simpa only [DerivedBar.tensorBarComplex, DerivedBar.projectiveResolution, DerivedBar.complex,
      ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d] using
      (objectIso_natural f (DerivedBar.differential k A N (j+1))).symm)

end LittleFinitistic.PDResidueAssociativity

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDResidueScalar
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDResidueScalar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- Name the generic residue scalar structure so concrete square-zero algebras
need not unfold their entire construction during typeclass search. -/
@[instance_reducible] def moduleK : Module k (PDTensor.Residue (A := A)) := inferInstance

attribute [local instance] moduleK

end LittleFinitistic.PDResidueScalar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_VerdierEvaluationExact
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.TwoConeVerdier.ConePair
variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable (T : ConePair C)
variable {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  [IsIso (F.map T.first.mor₁)] [IsIso (F.map T.second.mor₁)]

instance evaluationFacShift : NatTrans.CommShift (T.evaluation_fac F).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization T.q T.Sigma ℤ F (T.evaluation F)

/-- The actual factor through the Verdier quotient is exact. -/
instance evaluationExact : (T.evaluation F).IsTriangulated := by
  let := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions T.q T.Sigma
  exact Functor.isTriangulated_of_precomp_iso (T.evaluation_fac F)

end LittleFinitistic.TwoConeVerdier.ConePair

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryChainAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
instance instFiniteDimensional : FiniteDimensional k (ChainAlgebra k l) :=
  inferInstanceAs (FiniteDimensional k ((Fin (l+1) → k) × (Fin l → k)))

end ChainAlgebra

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- Actual off-diagonal complex with both actions of the product algebra retained. -/
def complex : CochainComplex (ModuleCat.{u} ((L × R) ⊗[k] (L × R)ᵐᵒᵖ)) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of _ (complexTerm k L R O T n))
    (fun n => ModuleCat.ofHom (complexDifferential k L R O T n))
    (fun n => ModuleCat.hom_ext (complexDifferential_square k L R O T n))
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalComplexMaps
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

theorem complex_d (n : ℤ) : (complex k L R O T).d n (n+1) =
    ModuleCat.ofHom (complexDifferential k L R O T n) :=
  CochainComplex.of_d (fun n => ModuleCat.of _ (complexTerm k L R O T n))
    (fun n => ModuleCat.ofHom (complexDifferential k L R O T n)) n

/-- An actual map of off-diagonal complexes retaining both product-ring actions. -/
def complexMap (f : O ⟶ O') (g : T ⟶ T') : complex k L R O T ⟶ complex k L R O' T' where
  f n := ModuleCat.ofHom (complexTermMap k L R f g n)
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d,complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact congrArg (fun h => h.hom x.1) (f.comm n (n+1))
    · exact congrArg (fun h => h.hom x.2) (g.comm n (n+1))
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalObjects
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) (T : ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ))

variable {O T} {O' : ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)} {T' : ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)}

def objectMap (f : O ⟶ O') (g : T ⟶ T') : object k L R O T ⟶ object k L R O' T' :=
  ModuleCat.ofHom (RetainedBimodule.map (k := k) (S := L × R) (A := L × R)
    (map (BimoduleCoefficients.map k R L f) (BimoduleCoefficients.map k L R g))
    (map_left (BimoduleCoefficients.map k R L f) (BimoduleCoefficients.map_left k R L f)
      (BimoduleCoefficients.map k L R g) (BimoduleCoefficients.map_left k L R g)))

def objectIso (f : O ≅ O') (g : T ≅ T') : object k L R O T ≅ object k L R O' T' where
  hom := objectMap k L R f.hom g.hom
  inv := objectMap k L R f.inv g.inv
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (congrArg (fun h => h.hom x.1) f.hom_inv_id)
      (congrArg (fun h => h.hom x.2) g.hom_inv_id)
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (congrArg (fun h => h.hom x.1) f.inv_hom_id)
      (congrArg (fun h => h.hom x.2) g.inv_hom_id)

theorem object_isZero (hO : IsZero O) (hT : IsZero T) : IsZero (object k L R O T) := by
  have := ModuleCat.isZero_iff_subsingleton.mp hO
  have := ModuleCat.isZero_iff_subsingleton.mp hT
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact inferInstanceAs (Subsingleton (O × T))
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBlockComplexes
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

theorem complex_d_all (n m : ℤ) : (complex k L R O T).d n m = objectMap k L R (O.d n m) (T.d n m) := by
  by_cases h : n+1=m
  · subst m
    rw [complex_d]
    rfl
  · have hh : ¬ (ComplexShape.up ℤ).Rel n m := h
    rw [(complex k L R O T).shape n m hh,O.shape n m hh,T.shape n m hh]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFirstBlockTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

omit [Algebra k L] [Algebra k R] [Module R O] [IsScalarTower k R O]
  [IsScalarTower k Lᵐᵒᵖ O] [SMulCommClass R Lᵐᵒᵖ O] [Module L T]
  [IsScalarTower k L T] [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T]
  [IsScalarTower k L Z] in
theorem other_block_zero (t : T) (z : BlockModule.First k L R Z) :
    BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z) (0,t) z = 0 := by
  have h := BalancedTensor.balance (k := k) (A := L × R) (M := OffDiagonal O T)
    (N := BlockModule.First k L R Z) (0,1) (0,t) z
  change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z)
      ((0:Lᵐᵒᵖ) • (0:O),(1:Rᵐᵒᵖ) • t) z =
    BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z) (0,t) ((0:L) • (show Z from z)) at h
  erw [zero_smul, one_smul, zero_smul, map_zero] at h
  exact h

end LittleFinitistic.OrdinarySimulation.FirstBlockTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalForget
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

def forgetTermIso (n : ℤ) : (underlyingComplex (k := k) (complex k L R O T)).X n ≅
    (PairComplex.complex (underlyingComplex (k := k) O) (underlyingComplex (k := k) T)).X n :=
  (RetainedBimodule.scalarEquiv k (L × R) (L × R)
    (OffDiagonal (BimoduleCoefficients k R L (O.X n)) (BimoduleCoefficients k L R (T.X n)))).toModuleIso

/-- Forgetting the two outside actions gives the actual coordinate direct-sum complex. -/
def forgetIso : underlyingComplex (k := k) (complex k L R O T) ≅
    PairComplex.complex (underlyingComplex (k := k) O) (underlyingComplex (k := k) T) :=
  HomologicalComplex.Hom.isoOfComponents (forgetTermIso k L R O T) (by
    intro n m h
    change n+1=m at h
    subst m
    change (forgetTermIso k L R O T n).hom ≫ _ =
      (ModuleCat.restrictScalars (algebraMap k ((L × R) ⊗[k] (L × R)ᵐᵒᵖ))).map
        ((complex k L R O T).d n (n+1)) ≫ (forgetTermIso k L R O T (n+1)).hom
    rw [complex_d,PairComplex.complex_d]
    rfl)

variable {O T} {O' : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ}
variable {T' : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ}

theorem forgetIso_natural (f : O ⟶ O') (g : T ⟶ T') :
    ((ModuleCat.restrictScalars (algebraMap k ((L × R) ⊗[k] (L × R)ᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map
      (complexMap k L R f g) ≫ (forgetIso k L R O' T').hom =
    (forgetIso k L R O T).hom ≫ PairComplex.map
      (((ModuleCat.restrictScalars (algebraMap k (R ⊗[k] Lᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map f)
      (((ModuleCat.restrictScalars (algebraMap k (L ⊗[k] Rᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map g) := by
  ext n x
  rfl

/-- The actual off-diagonal map is a quasi-isomorphism when its two components are. -/
theorem complexMap_quasiIso (f : O ⟶ O') (g : T ⟶ T') [QuasiIso f] [QuasiIso g] :
    QuasiIso (complexMap k L R f g) := by
  apply (RestrictionHomology.quasiIso_iff (algebraMap k ((L × R) ⊗[k] (L × R)ᵐᵒᵖ)) _).mp
  let f' := ((ModuleCat.restrictScalars (algebraMap k (R ⊗[k] Lᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map f
  let g' := ((ModuleCat.restrictScalars (algebraMap k (L ⊗[k] Rᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map g
  have : QuasiIso f' := (RestrictionHomology.quasiIso_iff (algebraMap k (R ⊗[k] Lᵐᵒᵖ)) f).mpr inferInstance
  have : QuasiIso g' := (RestrictionHomology.quasiIso_iff (algebraMap k (L ⊗[k] Rᵐᵒᵖ)) g).mpr inferInstance
  have := PairComplex.map_quasiIso f' g'
  let h := ((ModuleCat.restrictScalars (algebraMap k ((L × R) ⊗[k] (L × R)ᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map
    (complexMap k L R f g)
  have hh : QuasiIso (h ≫ (forgetIso k L R O' T').hom) := by
    dsimp only [h]
    rw [forgetIso_natural]
    exact inferInstanceAs (QuasiIso ((forgetIso k L R O T).hom ≫ PairComplex.map f' g'))
  exact (quasiIso_iff_comp_right h (forgetIso k L R O' T').hom).mp hh
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductDimension
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R] [Small.{v} L] [Small.{v} R]

omit [Small.{v} R] in
/-- Inflation from a factor preserves finite projective-dimension bounds, via actual projective covers. -/
theorem firstInflation_dimensionLE (n : ℕ) (M : ModuleCat.{v} L) [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE ((firstInflation L R).obj M) n := by
  induction n generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLT_one (X := M)).mpr inferInstance
    have := firstInflation_projective L R M
    infer_instance
  | succ n ih =>
    let S := M.projectiveShortComplex
    have hS := M.shortExact_projectiveShortComplex
    have : HasProjectiveDimensionLT S.X₁ (n+1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    have hk := ih S.X₁
    have hp := firstInflation_projective L R S.X₂
    have := firstInflation_preservesHomology.{u,v} L R
    have : Mono ((firstInflation L R).map S.f) :=
      (ModuleCat.mono_iff_injective _).mpr ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
    have : Epi ((firstInflation L R).map S.g) :=
      (ModuleCat.epi_iff_surjective _).mpr ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)
    have hs : (S.map (firstInflation L R)).ShortExact := hS.map (firstInflation L R)
    exact (hs.hasProjectiveDimensionLT_X₃_iff n hp).mpr hk
end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductSecondDimension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

attribute [local instance] RingHomInvPair.of_ringEquiv

variable [Small.{v} L] [Small.{v} R]

theorem secondInflation_dimensionLE (n : ℕ) (P : ModuleCat.{v} R) [HasProjectiveDimensionLE P n] :
    HasProjectiveDimensionLE ((secondInflation L R).obj P) n := by
  have := firstInflation_dimensionLE R L n P
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv
    (RingEquiv.prodComm : R × L ≃+* L × R) (swapInflationEquiv L R P) n

end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalProjective
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (L R O T : Type u) [Ring L] [Ring R]
variable [AddCommGroup O] [AddCommGroup T] [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T]
open ProductModules

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Off-diagonal right projectivity follows from the actual two product-factor modules. -/
theorem right_projective [Module.Projective Lᵐᵒᵖ O] [Module.Projective Rᵐᵒᵖ T] :
    Module.Projective (L × R)ᵐᵒᵖ (OffDiagonal O T) := by
  let P := ModuleCat.of Lᵐᵒᵖ O
  let Q := ModuleCat.of Rᵐᵒᵖ T
  have : Projective P := ModuleCat.projective_of_categoryTheory_projective P
  have : Projective Q := ModuleCat.projective_of_categoryTheory_projective Q
  have : HasProjectiveDimensionLE P 0 := (projective_iff_hasProjectiveDimensionLT_one (X := P)).mp inferInstance
  have : HasProjectiveDimensionLE Q 0 := (projective_iff_hasProjectiveDimensionLT_one (X := Q)).mp inferInstance
  have := firstInflation_dimensionLE Lᵐᵒᵖ Rᵐᵒᵖ 0 P
  have := secondInflation_dimensionLE Lᵐᵒᵖ Rᵐᵒᵖ 0 Q
  let e := ModuleCat.biprodIsoProd ((firstInflation Lᵐᵒᵖ Rᵐᵒᵖ).obj P)
    ((secondInflation Lᵐᵒᵖ Rᵐᵒᵖ).obj Q)
  have : HasProjectiveDimensionLT (inflatedPair L R O T) 1 := hasProjectiveDimensionLT_of_iso e 1
  have : HasProjectiveDimensionLE (ModuleCat.of (L × R)ᵐᵒᵖ (OffDiagonal O T)) 0 :=
    ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv (oppositeEquiv L R).symm
      (rightPairEquiv L R O T).symm 0
  have : Projective (ModuleCat.of (L × R)ᵐᵒᵖ (OffDiagonal O T)) :=
    (projective_iff_hasProjectiveDimensionLT_one (X := ModuleCat.of (L × R)ᵐᵒᵖ (OffDiagonal O T))).mpr inferInstance
  exact ModuleCat.projective_of_module_projective (ModuleCat.of (L × R)ᵐᵒᵖ (OffDiagonal O T))
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalSingle
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) (T : ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ))

abbrev singles : CochainComplex (ModuleCat.{u} ((L × R) ⊗[k] (L × R)ᵐᵒᵖ)) ℤ :=
  complex k L R ((HomologicalComplex.single _ (.up ℤ) 0).obj O)
    ((HomologicalComplex.single _ (.up ℤ) 0).obj T)

theorem singles_isZero (n : ℤ) (hn : n ≠ 0) : IsZero ((singles k L R O T).X n) :=
  object_isZero k L R (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 O n hn)
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 T n hn)

def singleTermIso (n : ℤ) : (singles k L R O T).X n ≅
    ((HomologicalComplex.single _ (.up ℤ) 0).obj (object k L R O T)).X n := by
  by_cases hn : n = 0
  · subst n
    exact objectIso k L R (HomologicalComplex.singleObjXSelf (.up ℤ) 0 O)
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T) ≪≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (object k L R O T)).symm
  · exact (singles_isZero k L R O T n hn).iso
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (object k L R O T) n hn)

/-- The off-diagonal direct sum of two ordinary modules is their ordinary bimodule in degree zero. -/
def singleIso : singles k L R O T ≅
    (HomologicalComplex.single _ (.up ℤ) 0).obj (object k L R O T) :=
  HomologicalComplex.Hom.isoOfComponents (singleTermIso k L R O T) (by
    intro n m h
    change n+1=m at h
    by_cases hn : n = 0
    · have hm : m ≠ 0 := by omega
      exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (object k L R O T) m hm).eq_of_tgt _ _
    · exact (singles_isZero k L R O T n hn).eq_of_src _ _)
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryRightProjective
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u v w

open CategoryTheory
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

theorem ordinaryO_right_projective (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ)
    (a : ℤ) (l : ℕ)
    [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)] :
    Module.Projective Bᵐᵒᵖ (BimoduleO P a l) := by
  let V : Fin (l+1) → Type u := fun i => (underlyingRightComplex P).X (a+(i.val:ℤ))
  have : Module.Projective Bᵐᵒᵖ (∀ i, V i) := finitePi_projective V
  exact Module.Projective.of_equiv (show (∀ i, V i) ≃ₗ[Bᵐᵒᵖ] BimoduleO P a l from LinearEquiv.refl _ _)
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySecondBlockTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

abbrev source := LeftTensor k (L × R) (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z)
abbrev target := BlockModule.First k L R (LeftTensor k R L T Z)

def forward : source k L R O T Z →ₗ[k] target k L R T Z :=
  BalancedTensor.lift ((BalancedTensor.mk k R T Z).compl₁₂
    (show OffDiagonal O T →ₗ[k] T from LinearMap.snd k O T)
    (show BlockModule.Second k L R Z →ₗ[k] Z from LinearMap.id)) (by
      intro d x z
      exact BalancedTensor.balance (k := k) (A := R) (M := T) (N := Z) d.2 x.2 (show Z from z))

def inverse : target k L R T Z →ₗ[k] source k L R O T Z :=
  BalancedTensor.lift ((BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z)).compl₁₂
    (show T →ₗ[k] OffDiagonal O T from LinearMap.inr k O T)
    (show Z →ₗ[k] BlockModule.Second k L R Z from LinearMap.id)) (by
      intro a t z
      have h := BalancedTensor.balance (k := k) (A := L × R) (M := OffDiagonal O T)
        (N := BlockModule.Second k L R Z) (0,a) (0,t) z
      change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z)
          ((0:Lᵐᵒᵖ) • (0:O),MulOpposite.op a • t) (show BlockModule.Second k L R Z from z) =
        BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z) (0,t)
          (show BlockModule.Second k L R Z from a • z) at h
      rw [smul_zero] at h
      exact h)

omit [Algebra k L] [Algebra k R] [Module R O] [IsScalarTower k R O]
  [IsScalarTower k Lᵐᵒᵖ O] [SMulCommClass R Lᵐᵒᵖ O] [Module L T]
  [IsScalarTower k L T] [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T]
  [IsScalarTower k R Z] in
theorem other_block_zero (o : O) (z : BlockModule.Second k L R Z) :
    BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z) (o,0) z = 0 := by
  have h := BalancedTensor.balance (k := k) (A := L × R) (M := OffDiagonal O T)
    (N := BlockModule.Second k L R Z) (1,0) (o,0) z
  change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z)
      ((1:Lᵐᵒᵖ) • o,(0:Rᵐᵒᵖ) • (0:T)) z =
    BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z) (o,0) ((0:R) • (show Z from z)) at h
  erw [one_smul, zero_smul, zero_smul, map_zero] at h
  exact h

omit [Module R O] [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O]
  [SMulCommClass R Lᵐᵒᵖ O] [Module L T] [IsScalarTower k L T]
  [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T] [IsScalarTower k R Z] in
theorem inverse_forward (x : source k L R O T Z) :
    inverse k L R O T Z (forward k L R O T Z x) = x := by
  let F := (inverse k L R O T Z).comp (forward k L R O T Z)
  have h : F = LinearMap.id := by
    apply BalancedTensor.ext
    intro x z
    change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z) (0,x.2) z =
      BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z) x z
    let q := (BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z)).flip z
    have hx : x = (x.1,0) + (0,x.2) := Prod.ext (add_zero _).symm (zero_add _).symm
    exact ((congrArg q hx).trans ((q.map_add _ _).trans
      ((congrArg (· + q (0,x.2)) (other_block_zero k L R O T Z x.1 z)).trans (zero_add _)))).symm
  exact congrArg (fun f => f x) h

omit [Module R O] [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O]
  [SMulCommClass R Lᵐᵒᵖ O] [Module L T] [IsScalarTower k L T]
  [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T] [IsScalarTower k R Z] in
theorem forward_inverse (x : target k L R T Z) :
    forward k L R O T Z (inverse k L R O T Z x) = x := by
  have h : (forward k L R O T Z).comp (inverse k L R O T Z) = LinearMap.id := by
    apply BalancedTensor.ext
    intro t z
    rfl
  exact congrArg (fun f => f x) h

end LittleFinitistic.OrdinarySimulation.SecondBlockTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorDirected
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorDirected
universe u
variable {k B C : Type u} [Field k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]
variable {n : ℕ} (DB : DirectedBound.DirectedSystem k B 3) (DC : DirectedBound.DirectedSystem k C n)

theorem vertex_idempotent (i : Fin (n*3)) : vertex DB DC i * vertex DB DC i = vertex DB DC i := by
  simp only [vertex,Algebra.TensorProduct.tmul_mul_tmul,DB.idem,DC.idem]

theorem vertex_orthogonal (i j : Fin (n*3)) (hij : i ≠ j) : vertex DB DC i * vertex DB DC j = 0 := by
  simp only [vertex,Algebra.TensorProduct.tmul_mul_tmul]
  by_cases hb : bIndex i = bIndex j
  · have hc : cIndex i ≠ cIndex j := by
      intro h
      apply hij
      apply Fin.ext
      have hi := index_value i
      have hj := index_value j
      rw [hb,h] at hi
      omega
    rw [DC.orthogonal _ _ hc,TensorProduct.tmul_zero]
  · rw [DB.orthogonal _ _ hb,TensorProduct.zero_tmul]

theorem vertex_complete : ∑ i : Fin (n*3), vertex DB DC i = 1 := by
  have h := Equiv.sum_comp (finProdFinEquiv : Fin n × Fin 3 ≃ Fin (n*3)) (vertex DB DC)
  rw [← h]
  simp only [vertex,bIndex,cIndex,Equiv.symm_apply_apply,Fintype.sum_prod_type]
  have ht (x : Fin n) : (∑ j : Fin 3, DB.e j ⊗ₜ[k] DC.e x) = (1:B) ⊗ₜ[k] DC.e x := by
    rw [← TensorProduct.sum_tmul,DB.complete]
  simp_rw [ht]
  rw [← TensorProduct.tmul_sum,DC.complete]
  rfl

theorem vertex_diagonal (i : Fin (n*3)) (x : B ⊗[k] C) :
    ∃ r : k, vertex DB DC i * x * vertex DB DC i = r • vertex DB DC i := by
  induction x using OAI.tensorInductionOn with
  | tmul b c =>
    obtain ⟨r,hr⟩ := DB.diagonal (bIndex i) b
    obtain ⟨s,hs⟩ := DC.diagonal (cIndex i) c
    refine ⟨r*s,?_⟩
    simp only [vertex,Algebra.TensorProduct.tmul_mul_tmul,hr,hs,
      TensorProduct.smul_tmul,TensorProduct.tmul_smul,smul_smul,mul_comm s r]
  | add x y hx hy =>
    obtain ⟨r,hr⟩ := hx
    obtain ⟨s,hs⟩ := hy
    exact ⟨r+s,by rw [mul_add,add_mul,hr,hs,add_smul]⟩

theorem vertex_directed (i j : Fin (n*3)) (hij : j < i) (x : B ⊗[k] C) :
    vertex DB DC j * x * vertex DB DC i = 0 := by
  have hi := index_value i
  have hj := index_value j
  have hbi := (bIndex i).isLt
  have hbj := (bIndex j).isLt
  change j.val < i.val at hij
  have hc : cIndex j < cIndex i ∨ (cIndex j = cIndex i ∧ bIndex j < bIndex i) := by
    by_cases h : cIndex j < cIndex i
    · exact Or.inl h
    · right
      have he : cIndex j = cIndex i := Fin.ext (by change ¬(cIndex j).val < (cIndex i).val at h; omega)
      exact ⟨he,by change (bIndex j).val < (bIndex i).val; rw [he] at hj; omega⟩
  induction x using OAI.tensorInductionOn with
  | tmul b c =>
    simp only [vertex,Algebra.TensorProduct.tmul_mul_tmul]
    rcases hc with h | ⟨h,hb⟩
    · rw [DC.directed _ _ h,TensorProduct.tmul_zero]
    · rw [DB.directed _ _ hb,TensorProduct.zero_tmul]
  | add x y hx hy => rw [mul_add,add_mul,hx,hy,add_zero]

/-- A concrete linear extension of the source's product order, with exactly 3n vertices. -/
def directedSystem : DirectedBound.DirectedSystem k (B ⊗[k] C) (n*3) where
  e := vertex DB DC
  idem := vertex_idempotent DB DC
  orthogonal := vertex_orthogonal DB DC
  complete := vertex_complete DB DC
  diagonal := vertex_diagonal DB DC
  directed := vertex_directed DB DC
end LittleFinitistic.OrdinarySimulation.TensorDirected

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_SelectionIteration
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace LittleFinitistic
open CategoryTheory

noncomputable def selectionIterate (M : ModuleCat SelectionRing) : ℕ → ModuleCat SelectionRing
  | 0 => M
  | n+1 => selectionStep (selectionIterate M n)

def ZeroAt (M : ModuleCat SelectionRing) (q : ℕ) : Prop :=
  ∀ x : M, selectionIdempotent q • x = 0

end LittleFinitistic

end OAI
end


