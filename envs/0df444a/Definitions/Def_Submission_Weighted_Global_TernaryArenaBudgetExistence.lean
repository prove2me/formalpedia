-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaBudgetExistence
-- name    : Submission_Weighted_Global_TernaryArenaBudgetExistence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:18:07.453825+00:00
-- url     : https://prove2.me/theorems/99a4d3e2-a603-4f67-a791-0d9de48aac20
-- title:
--   Ternary Arena Budget Existence
-- statement:
--   Definitions and structural lemmas for Ternary Arena Budget Existence, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaBudgetExistence.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaBudgetExistence
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open TernaryOriginalRowMenu TernaryExtensionEncoding WeightedGlobalArenaSeedData
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
def pairFactor (m F K : ℕ) : ℕ := F*(vertices (fixedLength m) (fixedPi m)).card*
  (2^(fixedPi m 1)*3^(fixedPi m 2))^K
def scale (m r K : ℕ) : ℕ := 2^(((r+1)*fixedPi m 2)*K)
def current (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (A : Inputs)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p) (L R O : ℕ→ℕ→ℤ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (r K : ℕ) : ℕ :=
  WeightedGlobalArenaPrefixPotential.value maps τ cap I (fun i t => L i t.val) (fun i t => R i t.val)
    row (root row (fun i t => O i t.val)) Q r K
def nextValue (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (A : Inputs)
    (ℓ : E→ₗ[ZMod p] ZMod p) (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (Q : WeightedGlobalGoodOutputCatalog.Output m) (r K : ℕ) (seed : E×E) : ℕ :=
  current maps τ cap I A (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) L R O Q (r+1) K
def collisions (A : Inputs) (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L : ℕ→ℕ→ℤ) (r n : ℕ) : ℕ :=
  (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => hash row r (fun i t => L i t.val) i.val)).card
def nextCollision (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p) (L : ℕ→ℕ→ℤ) (r n : ℕ) (seed : E×E) : ℕ :=
  TernaryOriginalCollisions.nextCollisions ℓ (fun i : Fin n => fun t : Fin (A.J+2) => (L i.val t.val : ZMod p))
    (fun i : Fin n => hash row r (fun i t => L i t.val) i.val) seed
end ThreeSum.WeightedGlobalArenaBudgetExistence


