-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupLayout
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:57:18.621315+00:00
-- url     : https://prove2.me/theorems/14fb3a00-e2e3-4b09-9530-7fd600870369
-- title:
--   TernaryArenaCleanupLayout
-- statement:
--   Definitions and structural lemmas for TernaryArenaCleanupLayout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCleanupLayout.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


