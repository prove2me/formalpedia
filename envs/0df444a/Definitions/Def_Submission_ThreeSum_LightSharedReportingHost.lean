-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSharedReportingHost
-- name    : Submission_ThreeSum_LightSharedReportingHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:49:36.358208+00:00
-- url     : https://prove2.me/theorems/46095930-755d-456d-9f70-1c461c748c72
-- title:
--   Light Shared Reporting Host
-- statement:
--   Definitions and structural lemmas for Light Shared Reporting Host, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingHost.lean

import Definitions.Def_Submission_ThreeSum_LightSharedReportingBank
import Definitions.Def_Submission_ThreeSum_LightSharedReportingCounts
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
import Definitions.Def_Submission_ThreeSum_SourceControlLayout
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSharedReportingHost
open Light GlobalEncoding SharedReportingBankLayout SharedReportingBankRows
open SharedReportingBankHeader
set_option maxHeartbeats 3900000
set_option maxRecDepth 16000
def body (pDepth pCounts pBank : ℕ) : Stmt :=
  .set 7 (M (v 2 +' k 1)) ;;
  .set 8 (M (v 3 +' k 1)) ;;
  .set 9 (M (v 3 +' k 3)) ;;
  .set 10 (M (v 4)) ;;
  .set 11 (M (v 4 +' k 2)) ;;
  .call pDepth [v 1] 6 ;;
  .set 6 (v 6 +' k 1) ;;
  .set 12 (v 5 +' k 9) ;;
  .call pCounts [v 0,v 5 +' k 7,v 12] 13 ;;
  .set 14 (M (v 5 +' k 7)) ;;
  .set 15 (v 7 *' v 8 *' v 9) ;;
  .set 16 (v 12 +' k 5 *' v 6 *' v 15) ;;
  .call pBank [v 0,v 1,v 6,v 10,v 11,v 7,v 8,v 9,v 14,v 13,v 12,v 16] 17 ;;
  .set 17 (v 17) ;;
  .store (v 5) (v 12) ;;
  .store (v 5 +' k 1) (v 16) ;;
  .store (v 5 +' k 2) (v 6) ;;
  .store (v 5 +' k 3) (v 7) ;;
  .store (v 5 +' k 4) (v 8) ;;
  .store (v 5 +' k 5) (v 9) ;;
  .store (v 5 +' k 6) (v 17) ;;
  .set 0 (v 17)
def depthPrefix : Program := LightSharedReportingBank.program ++
  LightSwitchDepth.program.map (ReportingHostRelocation.relocate LightSharedReportingBank.program.length)
def countMap : Program :=
  LightSharedReportingCounts.program.map (ReportingHostRelocation.relocate depthPrefix.length)
def program : Program := depthPrefix ++ countMap ++ [body 67 69 66]
def time (h J NB NC g : ℕ) : ℕ :=
  LightSwitchDepth.time J+LightSharedReportingCounts.time h+
    LightSharedReportingBank.time h J (levels J) NB NC g+3000
def space (free h J NB NC g : ℕ) : ℕ :=
  max (records free+LightPascal.tableSize (512*h)) (finish free h J NB NC g)
structure Resources (lim : Limits) (free h J NB NC g d : ℕ) : Prop where
  space : space free h J NB NC g ≤ lim.space
  control : (LightSharedReportingBank.controlWord h J (levels J) NB NC g : ℤ) ≤ lim.word
  span : (SourceBandBankLayout.span h J (2*h*J) : ℤ) ≤ lim.word
  powers : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word
  pairs : (localPairs h : ℤ) ≤ lim.word
  depthWord : (LightSwitchDepth.word J : ℤ) ≤ lim.word
  depth : d+512*h+4 ≤ lim.depth
  bank : ∀ q < total h J NB NC g,
    LightSharedReportingLevels.Resources lim
      (rowBase (payload free h J NB NC g) h J (levels J) q) h J (levels J) g g (d+3)
end ThreeSum.LightSharedReportingHost


