-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
-- name    : Submission_ThreeSum_LightReportingSuffixBoxes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:33:39.021424+00:00
-- url     : https://prove2.me/theorems/144d6c01-780b-4819-8552-a117e5acb1e0
-- title:
--   Light Reporting Suffix Boxes
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Boxes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixBoxes.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixBoxes
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostSuffix
variable {lim : Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
def localLeaf {h J k : ℕ} (hk : k ≤ J) (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) : Finset (Fin (suffixStage J (512*h) k)) → ℤ :=
  leafWeight (block_fit hk) (leftSource pMod B b q) (rightSource pMod shift C c q)
    (suffixStage J (512*h) k) (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
end ThreeSum.LightReportingSuffixBoxes


