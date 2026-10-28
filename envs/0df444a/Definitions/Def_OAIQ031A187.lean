-- Prove2me | Definitions.Def_OAIQ031A187
-- name    : OAIQ031A187
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:17:18.759436+00:00
-- url     : https://prove2.me/theorems/506884e0-bdb2-4096-9f0c-56dbeaa9c63b
-- title:
--   Definitions bundle OAIQ031A187 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 4 definitions and 6 theorems. The definitions and types are `OAI.ArExplicit.T.branchPlainScalarEquiv`, `OAI.ArExplicit.T.branchZeroScalarEquiv`, `OAI.ArExplicit.T.fiberDiagonalClass`, `OAI.ArExplicit.diagonalClass`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_BranchHomProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/BranchHomProfile.lean), [`AuslanderReiten_Coordinates_ConcreteComparisonPositive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteComparisonPositive.lean), [`AuslanderReiten_Fibers_ConcreteFiberProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberProfile.lean), [`AuslanderReiten_Fibers_FiberBranchConsequences`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberBranchConsequences.lean), [`AuslanderReiten_Main`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Main.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A183`, `OAIQ031A184`, `OAIQ031A185` and `OAIQ031A186` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A189` and `OAIQ031A190`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A183
import Definitions.Def_OAIQ031A184
import Definitions.Def_OAIQ031A185
import Definitions.Def_OAIQ031A186

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_BranchHomProfile
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q)
include hq hq1 h

def branchZeroScalarEquiv : BranchHom q 0 ≃ₗ[k] k :=
  (branchHomEquiv q 0).trans (twoConeTopScalarEquiv q hq hq1 h)

def branchPlainScalarEquiv :
    (evaluatedSimpleObject q ⟶ branchTargetObject q) ≃ₗ[k] k :=
  (branchPlainHomEquiv q).trans (twoConeTopScalarEquiv q hq hq1 h)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ConcreteComparisonPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : Resolution.NoPositivePowerOne q)
variable (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0)
variable (hg : fiberFullRhoPair q H₁ H₂ 0 g =
  (CompleteComparison.fullHomIdentity (A.simpleComplete q),
    CompleteComparison.fullHomIdentity (A.simpleComplete q)))
variable (hrho : ∀ n : ℤ, 0 < n → Function.Bijective (fiberFullRhoPair q H₁ H₂ n))
variable (hsep : ∀ m : ℕ, 0 < m → (((H₁⁻¹ : kˣ) : k)^m) ≠ (((H₂⁻¹ : kˣ) : k)^m))
include hq hq1 hp hg hrho hsep

theorem tensorFiberComparison_positive_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) (n : ℤ)) := by
  by_cases hd : 3 ∣ n
  · obtain ⟨m,rfl⟩ := hd
    have hm : 0 < m := by omega
    apply TriangularInduction.tensorComparison_bijective_of_coordinates
      (tensorFiberMap q H₁ H₂ g) _
      (tensorFiberRhoEquiv q H₁ H₂ _ (hrho _ (by omega)))
      (((H₁⁻¹ : kˣ) : k)^m) (((H₂⁻¹ : kˣ) : k)^m) (hsep m hm)
    intro x
    exact (tensorFiberRhoEquiv_apply q H₁ H₂ _ (hrho _ (by omega)) _).trans
      (tensorFiberComparison_rows q H₁ H₂ hq hq1 hp g hg m hm x)
  · let : Subsingleton (CohomologyClass (A.simpleComplete q) (A.simpleComplete q) (n : ℤ)) :=
      (A.positiveTateModel q hq hq1 hp).outside (n : ℤ) (by omega) (by
        intro m hm
        apply hd
        exact ⟨m, by exact_mod_cast hm⟩)
    apply TriangularInduction.tensorComparison_bijective_of_coordinates
      (tensorFiberMap q H₁ H₂ g) _
      (tensorFiberRhoEquiv q H₁ H₂ _ (hrho _ (by omega)))
      (0 : k) 1 zero_ne_one
    intro x
    exact Subsingleton.elim _ _

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

variable [Subsingleton (BranchHom q (-1))]

attribute [local instance] OAI.ArExplicit.T.instSubsingletonTopHomotopyCategoryIntModuleCatAUpFiberProductTriangleSimpleHomotopyObjectNegOfNat
theorem fiberZeroClassOfBranches_image :
    fiberFullRhoPair q H₁ H₂ 0 (fiberZeroClassOfBranches q H₁ H₂ hq1 e hg hn) =
      (fullHomIdentity P₀, fullHomIdentity P₀) := by
  apply ((A.fullHomZeroScalarEquiv q hq1).prodCongr (A.fullHomZeroScalarEquiv q hq1)).injective
  rw [fiberFullRhoPair_zero_coordinates]
  simp only [LinearEquiv.prodCongr_apply, fullHomIdentity, A.fullHomZeroScalarEquiv_identity]
  rw [fiberZeroClassOfBranches, LinearEquiv.apply_symm_apply]
  change fiberProductMiddleScalarEquiv q H₁ H₂ hq1
    (TriangleGradedSequence.first k T₀ X₀ 0
      ((fiberZeroScalarEquivOfBranches q H₁ H₂ hq1 e hg hn).symm 1)) = (1, 1)
  exact TriangleGradedSequence.diagonalGenerator_image k T₀
    (fiberProductTriangle_distinguished q H₁ H₂) X₀
    (fiberProductMiddleScalarEquiv q H₁ H₂ hq1) e
    (e (branchZeroHom q H₁)) (branchScalar_ne_zero q H₁ e hn)
    (fiberProductSecond_zero_common q H₁ H₂ hq1 e hg)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberProfile
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q)
variable (H₁ H₂ : kˣ)
local notation "P₀" => A.simpleComplete q

include hq hq1 h

theorem normalizedBranches_equal : branchHom q H₁ = branchHom q H₂ :=
  branchHom_common_of_scalarCoordinate q hq1 (branchPlainScalarEquiv q hq hq1 h) H₁ H₂

theorem normalizedBranch_ne_zero (H : kˣ) : branchHom q H ≠ 0 :=
  branchHom_ne_zero_of_scalarCoordinate q hq1 (branchPlainScalarEquiv q hq hq1 h) H

def fiberDiagonalClass : CohomologyClass P₀ (fiberComplete q H₁ H₂) 0 := by
  letI := branchHom_subsingleton q hq hq1 h (-1) (by omega) (by omega)
  exact fiberZeroClassOfBranches q H₁ H₂ hq1 (branchZeroScalarEquiv q hq hq1 h)
    (normalizedBranches_equal q hq hq1 h H₁ H₂)
    (normalizedBranch_ne_zero q hq hq1 h H₁)

theorem fiberDiagonalClass_image :
    fiberFullRhoPair q H₁ H₂ 0 (fiberDiagonalClass q hq hq1 h H₁ H₂) =
      (fullHomIdentity P₀, fullHomIdentity P₀) := by
  let := branchHom_subsingleton q hq hq1 h (-1) (by omega) (by omega)
  exact fiberZeroClassOfBranches_image q H₁ H₂ hq1 (branchZeroScalarEquiv q hq hq1 h)
    (normalizedBranches_equal q hq hq1 h H₁ H₂)
    (normalizedBranch_ne_zero q hq hq1 h H₁)

theorem fiberDiagonalClass_spans (x : CohomologyClass P₀ (fiberComplete q H₁ H₂) 0) :
    ∃ c : k, x = c • fiberDiagonalClass q hq hq1 h H₁ H₂ := by
  let := branchHom_subsingleton q hq hq1 h (-1) (by omega) (by omega)
  exact fiberZeroClassOfBranches_spans q H₁ H₂ hq1 (branchZeroScalarEquiv q hq hq1 h)
    (normalizedBranches_equal q hq hq1 h H₁ H₂)
    (normalizedBranch_ne_zero q hq hq1 h H₁) x

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit
universe v

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

attribute [local instance] OAI.ArExplicit.instHasDerivedCategoryModuleCatTBaseFieldQ
attribute [local instance] OAI.ArExplicit.instHasDerivedCategoryModuleCatABaseFieldQ
def diagonalClass := T.fiberDiagonalClass q q_ne_zero one_add_q_ne_zero q_noPositivePowerOne
  (parameterUnit 1) (parameterUnit 2)

end ArExplicit

end

end OAI
end


