-- Prove2me | Definitions.Def_OAIQ031A185
-- name    : OAIQ031A185
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:04:10.682648+00:00
-- url     : https://prove2.me/theorems/dd998a2c-2eff-4b3e-84f2-247f27ac74d8
-- title:
--   Definitions bundle OAIQ031A185 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 2 definitions and 4 theorems. The definitions and types are `OAI.ArExplicit.T.fiberZeroClassOfBranches`, `OAI.ArExplicit.T.fiberZeroScalarEquivOfBranches`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Fibers_ConcreteFiberRow`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberRow.lean), [`AuslanderReiten_Fibers_FiberBranchConsequences`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberBranchConsequences.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A181` and `OAIQ031A182` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A187` and `OAIQ031A188`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A181
import Definitions.Def_OAIQ031A182

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberRow
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "HC" => HomotopyCategory (ModuleCat (A k q)) (ComplexShape.up ℤ)
local notation "X₀" => simpleHomotopyObject q
local notation "T₀" => fiberProductTriangle q H₁ H₂

theorem fiberProductSecond_zero (hq1 : 1+q ≠ 0)
    (m : TriangleGradedSequence.Middle T₀ X₀ 0) :
    TriangleGradedSequence.second k T₀ X₀ 0 m =
      (fiberProductMiddleScalarEquiv q H₁ H₂ hq1 m).1 • branchZeroHom q H₁ +
      (fiberProductMiddleScalarEquiv q H₁ H₂ hq1 m).2 • branchZeroHom q H₂ := by
  have h₁ := congrArg (fun v => v ≫ (branchHom q H₁)⟦(0 : ℤ)⟧')
    (simpleHom_eq_scalar_unit q hq1 (fiberProductMiddleEquiv q H₁ H₂ 0 m).1)
  have h₂ := congrArg (fun v => v ≫ (branchHom q H₂)⟦(0 : ℤ)⟧')
    (simpleHom_eq_scalar_unit q hq1 (fiberProductMiddleEquiv q H₁ H₂ 0 m).2)
  refine (fiberProductSecond_row q H₁ H₂ 0 m).trans ((congrArg₂ (· + ·) h₁ h₂).trans ?_)
  rw [Linear.smul_comp, Linear.smul_comp, simpleZeroUnit_postcomp, simpleZeroUnit_postcomp]
  rfl

theorem fiberProductSecond_zero_common (hq1 : 1+q ≠ 0)
    (e : BranchHom q 0 ≃ₗ[k] k) (hg : branchHom q H₁ = branchHom q H₂)
    (m : TriangleGradedSequence.Middle T₀ X₀ 0) :
    e (TriangleGradedSequence.second k T₀ X₀ 0 m) =
      e (branchZeroHom q H₁) *
        ((fiberProductMiddleScalarEquiv q H₁ H₂ hq1 m).1 +
          (fiberProductMiddleScalarEquiv q H₁ H₂ hq1 m).2) := by
  have hz : branchZeroHom q H₁ = branchZeroHom q H₂ :=
    congrArg (fun f => f ≫ (shiftFunctorZero HC ℤ).inv.app (branchTargetObject q)) hg
  rw [fiberProductSecond_zero q H₁ H₂ hq1, ← hz, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberBranchConsequences
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "T₀" => fiberProductTriangle q H₁ H₂
local notation "X₀" => simpleHomotopyObject q
local notation "P₀" => A.simpleComplete q

variable (hq1 : 1+q ≠ 0) (e : BranchHom q 0 ≃ₗ[k] k)
variable (hg : branchHom q H₁ = branchHom q H₂) (hn : branchHom q H₁ ≠ 0)

include hq1 e hg hn

theorem fiberSecondZero_surjective :
    Function.Surjective (TriangleGradedSequence.second k T₀ X₀ 0) :=
  TriangleGradedSequence.second_zero_surjective k T₀ X₀
    (fiberProductMiddleScalarEquiv q H₁ H₂ hq1) e
    (e (branchZeroHom q H₁)) (branchScalar_ne_zero q H₁ e hn)
    (fiberProductSecond_zero_common q H₁ H₂ hq1 e hg)

variable [Subsingleton (BranchHom q (-1))]

attribute [local instance] OAI.ArExplicit.T.instSubsingletonTopHomotopyCategoryIntModuleCatAUpFiberProductTriangleSimpleHomotopyObjectNegOfNat
def fiberZeroScalarEquivOfBranches : FiberHom q H₁ H₂ 0 ≃ₗ[k] k :=
  TriangleGradedSequence.zeroScalarEquiv k T₀
    (fiberProductTriangle_distinguished q H₁ H₂) X₀
    (fiberProductMiddleScalarEquiv q H₁ H₂ hq1) e
    (e (branchZeroHom q H₁)) (branchScalar_ne_zero q H₁ e hn)
    (fiberProductSecond_zero_common q H₁ H₂ hq1 e hg)

def fiberZeroClassOfBranches : CohomologyClass P₀ (fiberComplete q H₁ H₂) 0 :=
  (fiberFullHomEquiv q H₁ H₂ 0).symm
    ((fiberZeroScalarEquivOfBranches q H₁ H₂ hq1 e hg hn).symm 1)

theorem fiberZeroClassOfBranches_spans
    (x : CohomologyClass P₀ (fiberComplete q H₁ H₂) 0) :
    ∃ c : k, x = c • fiberZeroClassOfBranches q H₁ H₂ hq1 e hg hn := by
  let f := (fiberFullHomEquiv q H₁ H₂ 0).trans
    (fiberZeroScalarEquivOfBranches q H₁ H₂ hq1 e hg hn)
  refine ⟨f x, f.injective ?_⟩
  rw [map_smul]
  change f x = f x • f (f.symm 1)
  rw [f.apply_symm_apply]
  exact (mul_one _).symm

end ArExplicit.T

end

end OAI
end


