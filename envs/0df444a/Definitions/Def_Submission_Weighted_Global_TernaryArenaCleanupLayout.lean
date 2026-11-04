-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupLayout
-- name    : Submission_Weighted_Global_TernaryArenaCleanupLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:21:35.685755+00:00
-- url     : https://prove2.me/theorems/dabc211c-fff4-4e1a-810b-67c2d999d011
-- title:
--   Ternary Arena Cleanup Layout
-- statement:
--   Definitions and structural lemmas for Ternary Arena Cleanup Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCleanupLayout.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaCleanupLayout
open Light WeightedGlobalArenaLayout LightOriginalSurvivors LightOriginalSurvivorPair
set_option maxHeartbeats 2000000
def layout (free C aBase nA bBase nB cBase nC q L : ℕ) : Layout where
  aBase:=aBase
  nA:=nA
  bBase:=bBase
  nB:=nB
  cBase:=cBase
  nC:=nC
  keyB:=addr free C 4
  keyC:=addr free C 5
  histB:=addr free C 7
  histC:=addr free C 8
  q:=q
  powers:=addr free C 6
  L:=L
  outB:=addr free C 9
  valueB:=addr free C 10
  packedB:=addr free C 16
  lengthB:=addr free C 16+nB
  outC:=addr free C 16+nB+1
  valueC:=addr free C 16+nB+1+2*nC
  packedC:=addr free C 17
  lengthC:=addr free C 17+nC
end ThreeSum.WeightedGlobalArenaCleanupLayout


