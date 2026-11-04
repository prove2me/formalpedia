-- Prove2me | Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
-- name    : Submission_ThreeSum_OutputDecodeRecords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:12:12.685296+00:00
-- url     : https://prove2.me/theorems/0b90856d-7271-49ca-ab52-855cfbc9e17b
-- title:
--   Output Decode Records
-- statement:
--   Definitions and structural lemmas for Output Decode Records, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
set_option autoImplicit false
namespace ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
def layerCount (h : ℕ) : ℕ := outputCount (512*h) h
def localCount (h : ℕ) : ℕ := scheduleSize h*layerCount h
theorem layerCount_pos (h : ℕ) : 0 < layerCount h := Nat.choose_pos (by omega)
theorem schedule_pos (h : ℕ) : 0 < scheduleSize h := by
  unfold scheduleSize scheduleLength
  positivity
def blockDefault (h : ℕ) : OutputBlock h :=
  (⟨0,schedule_pos h⟩,layerRecord h ⟨0,layerCount_pos h⟩)
def outputDefault (h J : ℕ) : GlobalOutput h J := fun _ => blockDefault h
def localIndex (h J k j : ℕ) : ℕ := (indices (localCount h) J k).getD j 0
def occurrenceIndex (h J k j : ℕ) : ℕ := localIndex h J k j/layerCount h
def maskIndex (h J k j : ℕ) : ℕ := localIndex h J k j%layerCount h
end ThreeSum.OutputDecodeRecords


