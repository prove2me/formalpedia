-- Prove2me | Definitions.Def_Submission_ThreeSum_WantedPairs
-- name    : Submission_ThreeSum_WantedPairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:56:01.120712+00:00
-- url     : https://prove2.me/theorems/379d5afb-aa37-424c-ad7b-1733cc36c624
-- title:
--   Wanted Pairs
-- statement:
--   Definitions and structural lemmas for Wanted Pairs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
set_option autoImplicit false
namespace ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000
def count (left right : ℕ → ℕ) (NR NL : ℕ) : ℕ :=
  ∑ i ∈ Finset.range NL, LightHistogram.count right (left i) NR
def row (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) (i : ℕ) : List (ℕ × ℕ) :=
  (SourceBucketView.indices μ offsets flat (left i)).map (fun j => (i, j))
def pairs (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (row μ offsets flat left)
def cells (ps : List (ℕ × ℕ)) : List ℤ :=
  ps.flatMap (fun p => [p.1, p.2])
end ThreeSum.WantedPairs


