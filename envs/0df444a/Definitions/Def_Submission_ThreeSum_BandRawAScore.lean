-- Prove2me | Definitions.Def_Submission_ThreeSum_BandRawAScore
-- name    : Submission_ThreeSum_BandRawAScore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:37:23.415106+00:00
-- url     : https://prove2.me/theorems/e8c09875-c840-4b32-940c-d6469478f814
-- title:
--   Band Raw AScore
-- statement:
--   Definitions and structural lemmas for Band Raw AScore, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
namespace ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
def valueAt (n g : ℕ) (rs : List Record) (A : ℕ → ℤ) (i : ℕ) : ℤ :=
  (values A (items n g rs)).getD i 0
end ThreeSum.BandRawA


