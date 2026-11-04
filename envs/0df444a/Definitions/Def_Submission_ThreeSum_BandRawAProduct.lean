-- Prove2me | Definitions.Def_Submission_ThreeSum_BandRawAProduct
-- name    : Submission_ThreeSum_BandRawAProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:33:04.070459+00:00
-- url     : https://prove2.me/theorems/787ed1a6-f261-4c69-bfb7-3419c80672ee
-- title:
--   Band Raw AProduct
-- statement:
--   Definitions and structural lemmas for Band Raw AProduct, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
set_option autoImplicit false
namespace ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
def aIndices (n g : ℕ) (rs : List Record) (s : ℕ) : Finset ℕ :=
  (range (row n g s (rs.getD s default)).length).image (fun j => count n g rs s+j)
def bandPositions (n g a : ℕ) : Finset ℕ :=
  (range (bandLength n g a)).image (fun j => BandPartition.start g a+j)
def ownerProduct (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  aIndices nA g rs s ×ˢ (bandPositions nB g (rs.getD s default).b ×ˢ
    bandPositions nC g (rs.getD s default).c)
def allProducts (nA nB nC g : ℕ) (rs : List Record) : Finset (ℕ × ℕ × ℕ) :=
  (range rs.length).biUnion (ownerProduct nA nB nC g rs)
end ThreeSum.BandRawA


