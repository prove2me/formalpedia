-- Prove2me | Definitions.Def_Submission_ThreeSum_BandPrimeChoice
-- name    : Submission_ThreeSum_BandPrimeChoice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:19:10.52717+00:00
-- url     : https://prove2.me/theorems/031f508e-1386-4309-a28b-3e99eaf0fb92
-- title:
--   Band Prime Choice
-- statement:
--   Definitions and structural lemmas for Band Prime Choice, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
set_option autoImplicit false
namespace ThreeSum.BandPrimeChoice
open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000
def candidateScore (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (i : ℕ) : ℤ :=
  (score primes s (q*primes i) nA nB nC g A B C rs : ℤ)
def chosenIndex (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  LightMinimum.least (candidateScore primes s q nA nB nC g A B C rs) s
def chosenPrime (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  primes (chosenIndex primes s q nA nB nC g A B C rs)
def modulus (primes : ℕ → ℕ) (s nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ → ℕ
  | 0 => 1
  | r+1 =>
    let q := modulus primes s nA nB nC g A B C rs r
    q*chosenPrime primes s q nA nB nC g A B C rs
end ThreeSum.BandPrimeChoice


