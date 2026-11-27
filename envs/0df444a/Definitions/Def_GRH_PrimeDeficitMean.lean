-- Prove2me | Definitions.Def_GRH_PrimeDeficitMean
-- name    : GRH_PrimeDeficitMean
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-27T02:21:18.637797+00:00
-- url     : https://prove2.me/theorems/304fc398-8b6a-46e5-aac0-e2debab066d4
-- title:
--   Positive prime deficit and its Mellin weight on square cutoffs
-- statement:
--   At x and modulus q, the deficit is the positive part of x minus φ(q) times the sum of log p for ordinary primes p≤x congruent to 1 modulo q. At positive squares u² the series uses weight u^(−2θ−1). The cofinal condition asks for convergence at arbitrarily large q=(k+2)! with θ=1/2+1/(k+3).
-- source:
--   The exact Möbius target is https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 . Its previously verified one-class reduction is https://prove2.me/submissions/413f71d4-395a-4e35-87f9-cfe99ce96800 .

import Definitions.Def_GRH_SplitPrimeLower
import Mathlib.Analysis.PSeries

namespace GRH.PrimeDeficitMean
noncomputable section
open GRH.SplitPrimeLower

/-- Positive shortfall in the normalized log-weight of ordinary primes in class one. -/
def deficit (q : ℕ) (x : ℝ) : ℝ :=
  max (x - (q.totient:ℝ) * primeWeight q ⌊x⌋₊) 0

/-- The square cutoff is (n+1)², starting with 1. -/
def deficitTerm (q : ℕ) (θ : ℝ) (n : ℕ) : ℝ :=
  deficit q (((n+1:ℕ):ℝ)^2) * ((n+1:ℕ):ℝ)^(-2*θ-1)

def squareMean (q : ℕ) (θ : ℝ) : Prop := Summable (deficitTerm q θ)

def cofinalMean : Prop := ∀ B : ℕ, ∃ k : ℕ, B ≤ k ∧
  squareMean (FactorialMoebius.level k) (FactorialMoebius.exponent k)

end
end GRH.PrimeDeficitMean


