-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
-- name    : Submission_ThreeSum_TernaryWantedBatchCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:08:28.498193+00:00
-- url     : https://prove2.me/theorems/7588befd-a9fd-4742-9cd8-23381cc522a9
-- title:
--   Ternary Wanted Batch Count
-- statement:
--   Definitions and structural lemmas for Ternary Wanted Batch Count, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchCount.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
set_option autoImplicit false
namespace ThreeSum.TernaryWantedBatchCount
open LightTernaryWantedBatch TernaryWantedLittleEndian LightTernaryWantedCanonical
def count (p R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) : ℕ → ℕ
  | 0 => 0
  | n+1 => count p R S J raws words maps targets n+
      (wantedCodes (p : ℤ) raws words maps J (targets n) R S 0 1 0 1).length
end ThreeSum.TernaryWantedBatchCount


