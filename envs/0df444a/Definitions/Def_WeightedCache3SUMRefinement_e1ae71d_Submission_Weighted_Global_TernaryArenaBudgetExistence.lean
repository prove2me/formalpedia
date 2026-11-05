-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaBudgetExistence
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaBudgetExistence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:47:17.149273+00:00
-- url     : https://prove2.me/theorems/32d9b389-f9f3-435f-a5fd-13e6f24b14e3
-- title:
--   TernaryArenaBudgetExistence
-- statement:
--   Definitions and structural lemmas for TernaryArenaBudgetExistence, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaBudgetExistence.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedData
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


