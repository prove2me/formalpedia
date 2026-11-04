-- Prove2me | Definitions.Def_Submission_ThreeSum_WeightedScore
-- name    : Submission_ThreeSum_WeightedScore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:28.388202+00:00
-- url     : https://prove2.me/theorems/e4e44988-21cc-49c4-bb55-c321aba3b4aa
-- title:
--   Weighted Score
-- statement:
--   Definitions and structural lemmas for Weighted Score, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedScore.lean

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
set_option autoImplicit false
namespace ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators
def auxiliarySet (primes : ℕ → ℕ) (s : ℕ) : Finset ℕ :=
  (range s).image primes
def corrections (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) : ℕ :=
  ∑ j ∈ range i, count (joint q (primes j)) nA nB nC a b c
def remaining (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) : ℕ :=
  s * count q nA nB nC a b c - corrections primes q nA nB nC a b c i
def score (primes : ℕ → ℕ) (s q nA nB nC : ℕ) (a b c : ℕ → ℤ) : ℕ :=
  weightedFalseCount (triples nA nB nC) (difference a b c)
    (Auxiliary.moduli (auxiliarySet primes s)) q
end ThreeSum.WeightedScore


