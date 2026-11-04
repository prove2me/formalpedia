-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontendResources
-- name    : Submission_Weighted_Global_TernaryArenaFrontendResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:33:26.332003+00:00
-- url     : https://prove2.me/theorems/14bed41e-947f-447b-933a-627132401dbf
-- title:
--   Ternary Arena Frontend Resources
-- statement:
--   Definitions and structural lemmas for Ternary Arena Frontend Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontendResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_FrontendResources
set_option autoImplicit false
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


