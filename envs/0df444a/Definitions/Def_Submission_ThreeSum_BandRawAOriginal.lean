-- Prove2me | Definitions.Def_Submission_ThreeSum_BandRawAOriginal
-- name    : Submission_ThreeSum_BandRawAOriginal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:41:17.884845+00:00
-- url     : https://prove2.me/theorems/3f02c943-ce5b-4b96-b494-34de8883f509
-- title:
--   Band Raw AOriginal
-- statement:
--   Definitions and structural lemmas for Band Raw AOriginal, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAOriginal.lean

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_LightSortedBands
set_option autoImplicit false
namespace ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
def sortedRecords (A B C : List ℤ) (g : ℕ) (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : List Record :=
  records (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
    (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
    (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC))
end ThreeSum.BandRawA


