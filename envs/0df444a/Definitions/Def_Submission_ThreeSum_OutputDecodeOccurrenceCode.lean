-- Prove2me | Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
-- name    : Submission_ThreeSum_OutputDecodeOccurrenceCode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:16:12.619848+00:00
-- url     : https://prove2.me/theorems/a0dc8922-fff5-4c63-86e0-fa8dc1a7c045
-- title:
--   Output Decode Occurrence Code
-- statement:
--   Definitions and structural lemmas for Output Decode Occurrence Code, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOccurrenceCode.lean

import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
namespace ThreeSum.OutputDecodeOccurrenceCode
open OutputDecodeOrder OutputDecodeRecords GlobalEncoding
set_option maxHeartbeats 1500000
def code (T M : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | J+1,k => (k%(T*M))/M+T*code T M J (k/(T*M))
end ThreeSum.OutputDecodeOccurrenceCode


