-- Prove2me | Definitions.Def_OAIQ031A186
-- name    : OAIQ031A186
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:07:31.039697+00:00
-- url     : https://prove2.me/theorems/7b69b3e0-bd75-4513-b586-65979c94c103
-- title:
--   Definitions bundle OAIQ031A186 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Fibers_FiberBranchConsequences`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberBranchConsequences.lean), [`AuslanderReiten_Fibers_FiberProductCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberProductCoordinates.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A182` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A187` and `OAIQ031A188`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A182

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberProductCoordinates
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
local notation "R₀" => A k q
local notation "X₀" => simpleHomotopyObject q
local notation "τ₀" => AFrobeniusTrace k q
local notation "T₀" => fiberProductTriangle q H₁ H₂
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

theorem fiberProductFirst_coordinates (n : ℤ) (v : FiberHom q H₁ H₂ n) :
    fiberProductMiddleEquiv q H₁ H₂ n
      (TriangleGradedSequence.first k T₀ X₀ n v) = fiberHomRhoPair q H₁ H₂ n v := by
  erw [TriangleGradedSequence.first_eq_shift]
  apply Prod.ext
  · change (v ≫ (T₀).mor₁⟦n⟧') ≫ biprod.fst⟦n⟧' =
      v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₁ q H₁ H₂)))⟦n⟧'
    erw [Category.assoc, ← Functor.map_comp, fiberProductTriangle_first_fst]
  · change (v ≫ (T₀).mor₁⟦n⟧') ≫ biprod.snd⟦n⟧' =
      v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₂ q H₁ H₂)))⟦n⟧'
    erw [Category.assoc, ← Functor.map_comp, fiberProductTriangle_first_snd]

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

omit e hg hn [Subsingleton (BranchHom q (-1))] in
theorem fiberFullRhoPair_zero_coordinates
    (x : CohomologyClass P₀ (fiberComplete q H₁ H₂) 0) :
    ((A.fullHomZeroScalarEquiv q hq1).prodCongr (A.fullHomZeroScalarEquiv q hq1))
      (fiberFullRhoPair q H₁ H₂ 0 x) =
    fiberProductMiddleScalarEquiv q H₁ H₂ hq1
      (TriangleGradedSequence.first k T₀ X₀ 0 (fiberFullHomEquiv q H₁ H₂ 0 x)) := by
  change _ = ((simpleZeroScalarEquiv q hq1).prodCongr (simpleZeroScalarEquiv q hq1))
    (fiberProductMiddleEquiv q H₁ H₂ 0 _)
  rw [fiberProductFirst_coordinates]
  rfl

end ArExplicit.T

end

end OAI
end


