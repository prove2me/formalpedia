-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:12:33.894656+00:00
-- url     : https://prove2.me/theorems/af47a329-f096-4eb4-bdb4-36ed944fadf0
-- title:
--   LightTernaryPrefixInit
-- statement:
--   Definitions and structural lemmas for LightTernaryPrefixInit, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixInit.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixPhases
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalPrefixInit
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixLoop
open LightWeightedGlobalPrefixPhases
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
def Initialized (C : Config) (seed : ℕ) (values : List ℤ) (μ ν : ℕ→ℤ) : Prop :=
  Seg ν seed values ∧ (∀i<C.nB,ν (C.Bold+i)=0) ∧ (∀i<C.nC,ν (C.Cold+i)=0) ∧
    (∀i<C.nO,ν (C.Oold+i)=0) ∧ (∀i<C.J,ν (C.catalog+i)=0) ∧
    (∀x,(x<seed ∨ seed+48≤x)→(x<C.Bold ∨ C.Oold+C.nO≤x)→
      (x<C.catalog ∨ C.catalog+C.J≤x)→ν x=μ x)
def time (C : Config) (rounds T : ℕ) : ℕ :=
  copyTime 48+LightTernaryInitialKeys.time C.nB C.nC C.nO+fillTime C.J+LightWeightedGlobalPrefixLoop.time rounds T+1000
end ThreeSum.LightWeightedGlobalPrefixInit
end
end WeightedCache3SUMRefinement_e1ae71d


