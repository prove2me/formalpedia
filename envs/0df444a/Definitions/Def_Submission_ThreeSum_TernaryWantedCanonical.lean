-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
-- name    : Submission_ThreeSum_TernaryWantedCanonical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:18:41.606714+00:00
-- url     : https://prove2.me/theorems/2abedfdb-eda3-489d-9a53-9233ec38257c
-- title:
--   Ternary Wanted Canonical
-- statement:
--   Definitions and structural lemmas for Ternary Wanted Canonical, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonical.lean

import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
set_option autoImplicit false
namespace ThreeSum.TernaryWantedCanonical
open TernaryWantedRadix
def encode (digits : List ℕ) (R code : ℕ) : List ℕ → ℕ
  | [] => code
  | i::is => encode digits R (code*R+digits.getD i 0) is
def wantedCodes (p : ℤ) (raws : List ℤ) (digits : List ℕ) (j : ℕ)
    (x : ℤ) (code R : ℕ) : List ℕ :=
  (wantedOutputs p raws j x).map (encode digits R code)
def codeLimit (N code R j : ℕ) : ℕ := (code+R)*(2*(N+R))^j
end ThreeSum.TernaryWantedCanonical


