-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
-- name    : Submission_ThreeSum_SharedReportingBankHeader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:26:53.672901+00:00
-- url     : https://prove2.me/theorems/3a07f3e3-f484-41ae-a71a-eb51f5dcdad9
-- title:
--   Shared Reporting Bank Header
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Header, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankHeader.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
set_option autoImplicit false
namespace ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000
def levels (J : ℕ) : ℕ := LightSwitchDepth.depth J+1
def records (free : ℕ) : ℕ := free+9
def payload (free h J NB NC g : ℕ) : ℕ :=
  records free+5*levels J*total h J NB NC g
def finish (free h J NB NC g : ℕ) : ℕ :=
  rowBase (payload free h J NB NC g) h J (levels J) (total h J NB NC g)
def header (free h J NB NC g : ℕ) : List ℕ :=
  [records free,payload free h J NB NC g,levels J,LightBlockSourceCatalog.count h J,
    BandPartition.size NB g,BandPartition.size NC g,finish free h J NB NC g,
    localChoose h,localPairs h]
structure Stored (μ : ℕ → ℤ) (free h J NB NC g : ℕ) (fB fC : ℕ → ℤ) (p shift : ℤ) : Prop where
  heads : SegN μ free (header free h J NB NC g)
  rows : Done μ (records free) (payload free h J NB NC g) h J (levels J) NB NC g
    (total h J NB NC g) fB fC p shift
end ThreeSum.SharedReportingBankHeader


