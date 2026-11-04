-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
-- name    : Submission_ThreeSum_BlockSourceOccurrenceOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:38:19.735978+00:00
-- url     : https://prove2.me/theorems/b39f2989-7e8a-4b21-9d68-d021a5cbb310
-- title:
--   Block Source Occurrence Order
-- statement:
--   Definitions and structural lemmas for Block Source Occurrence Order, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean

import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_getD_lt

set_option autoImplicit false
namespace ThreeSum.BlockSourceOccurrenceOrder
open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration
def occurrences (h J k : ℕ) : Occurrences h J := fun j =>
  ⟨(indices (scheduleSize h) J k).getD j.val 0,indices_getD_lt (schedule_pos h) j.isLt⟩
def representative (h J k : ℕ) : GlobalOutput h J :=
  fun j => (occurrences h J k j,(blockDefault h).2)
end ThreeSum.BlockSourceOccurrenceOrder


