-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
-- name    : Submission_Weighted_Global_TernaryArenaPrefixStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T18:25:11.61599+00:00
-- url     : https://prove2.me/theorems/98b65c2b-a6c4-41a1-b563-0c5ed615c497
-- title:
--   Ternary Arena Prefix Step
-- statement:
--   Definitions and structural lemmas for Ternary Arena Prefix Step, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixStep.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrefixStep
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs WeightedGlobalArenaPrefixPotential
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction TernaryOriginalRowMenu
open TernaryExtensionEncoding
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
abbrev PhysicalIndex {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (K : ℕ) :=
  Σ j : Fin S.front.count, Fin K→WeightedGlobalNativePairMoments.Pair S j.val
def physicalMatrix {N K : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (L R : ℕ→Fin Λ→ℤ) (x : PhysicalIndex S K) : Matrix (Fin (K+K)) (Fin Λ) ℤ :=
  fun i => Sum.elim (fun k => L (x.2 k).val.1.1) (fun k => R (x.2 k).val.2.1) (finSumFinEquiv.symm i)
end ThreeSum.WeightedGlobalArenaPrefixStep


