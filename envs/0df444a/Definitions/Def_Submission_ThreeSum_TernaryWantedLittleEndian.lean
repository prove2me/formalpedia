-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
-- name    : Submission_ThreeSum_TernaryWantedLittleEndian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:25:12.993256+00:00
-- url     : https://prove2.me/theorems/122a9bf3-d1a6-477a-a7e5-e27b8d582487
-- title:
--   Ternary Wanted Little Endian
-- statement:
--   Definitions and structural lemmas for Ternary Wanted Little Endian, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
set_option autoImplicit false
namespace ThreeSum.TernaryWantedLittleEndian
open TernaryWantedRadix
def encode (digits : List ℕ) (R code scale : ℕ) : List ℕ → ℕ
  | [] => code
  | i::is => encode digits R (code+scale*digits.getD i 0) (scale*R) is
def wantedCodes (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (R S code scale mapCode mapScale : ℕ) : List (ℕ × ℕ) :=
  (wantedOutputs p raws j x).map fun is =>
    (encode words R code scale is,encode maps S mapCode mapScale is)
end ThreeSum.TernaryWantedLittleEndian


