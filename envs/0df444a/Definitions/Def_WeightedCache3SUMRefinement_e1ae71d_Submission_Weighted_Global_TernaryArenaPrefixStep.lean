-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixStep
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:33:57.485541+00:00
-- url     : https://prove2.me/theorems/25958caf-b661-4e3b-98dc-ad385a463aa5
-- title:
--   TernaryArenaPrefixStep
-- statement:
--   Definitions and structural lemmas for TernaryArenaPrefixStep, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrefixStep.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


