-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontendResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontendResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:21:13.579071+00:00
-- url     : https://prove2.me/theorems/f3e55ec8-1dd9-4af1-a650-c1ff92e1d8f5
-- title:
--   TernaryArenaFrontendResources
-- statement:
--   Definitions and structural lemmas for TernaryArenaFrontendResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFrontendResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_FrontendResources
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaFrontendResources
open Light WeightedGlobalArenaLayout TernaryJointType WeightedGlobalBank TernaryEuler
open WeightedGlobalFrontendResources LightWeightedNearPair LightWeightedQueryPlan
open LightWeightedPreparedWanted WeightedBankStageModel TernaryCodeSemantics
set_option maxHeartbeats 6000000
def config (free C N A bank nb bv T h wsSlot : ℕ) : Config where
  a:=addr free C 54; powers:=addr free C 57; bank:=bank; nb:=nb; bv:=bv
  L:=2*N; T:=T; activeBase:=addr free C 56
  ws:=addr free C wsSlot; rankBase:=addr free C (wsSlot+1)
  vals:=addr free C (wsSlot+2); h:=h
  pcount:=addr free C (wsSlot+3); fr:=addr free C (wsSlot+3)
  U:=sourceZeta N A; V:=eulerBound N A
end ThreeSum.WeightedGlobalArenaFrontendResources
end
end WeightedCache3SUMRefinement_e1ae71d


