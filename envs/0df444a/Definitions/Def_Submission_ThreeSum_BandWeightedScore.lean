-- Prove2me | Definitions.Def_Submission_ThreeSum_BandWeightedScore
-- name    : Submission_ThreeSum_BandWeightedScore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:15:56.324838+00:00
-- url     : https://prove2.me/theorems/a8a20517-e2f8-495d-8413-26865a02b6a5
-- title:
--   Band Weighted Score
-- statement:
--   Definitions and structural lemmas for Band Weighted Score, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
namespace ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
def length (n g a : ℕ) : ℕ := min g (n-a*g)
def block (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (r : Record) : ℕ :=
  if r.flag=1 then
    WeightedScore.score primes s q (length nA g r.a) (length nB g r.b) (length nC g r.c)
      (fun i => A (r.a*g+i)) (fun i => B (r.b*g+i)) (fun i => C (r.c*g+i))
  else 0
def partialScore (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (k : ℕ) : ℕ :=
  ∑ i ∈ range k, block primes s q nA nB nC g A B C (rs.getD i default)
def score (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  partialScore primes s q nA nB nC g A B C rs rs.length
end ThreeSum.BandWeightedScore


