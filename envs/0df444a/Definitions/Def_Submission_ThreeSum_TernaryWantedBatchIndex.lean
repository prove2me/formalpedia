-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
-- name    : Submission_ThreeSum_TernaryWantedBatchIndex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:13:22.852486+00:00
-- url     : https://prove2.me/theorems/1301b7ee-b2db-426d-ae64-132c3905a6d1
-- title:
--   Ternary Wanted Batch Index
-- statement:
--   Definitions and structural lemmas for Ternary Wanted Batch Index, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Theorems.Thm_Light_Seg_get
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian
abbrev Entry :=
  ℕ × ℕ × ℕ
def entries (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ) : ℕ → List Entry
  | 0 => []
  | n + 1 =>
    entries P R S J raws words maps targets positions n ++
      (wantedCodes (P : ℤ) raws words maps J (targets n) R S 0 1 0 1).map (fun wg => (positions n, wg.1, wg.2))
def cells (xs : List Entry) : List ℤ :=
  xs.flatMap fun e => [(e.1 : ℤ), e.2.1, e.2.2]
def get (xs : List Entry) (i : ℕ) : Entry :=
  xs.getD i (0, 0, 0)
end ThreeSum.TernaryWantedBatchIndex


