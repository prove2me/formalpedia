-- Prove2me | Definitions.Def_PrimePairSieve_ReciprocalLiteralWeight
-- name    : PrimePairSieve_ReciprocalLiteralWeight
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T16:02:47.009982+00:00
-- url     : https://prove2.me/theorems/8bd7a400-706f-42cd-a3f7-4ffdbd8b74fa
-- title:
--   Literal reciprocal sieve weight on squarefree indices
-- statement:
--   For a natural number $n$, the **literal reciprocal sieve weight** is zero unless $n$ is squarefree. If $n$ is squarefree, it is the product over prime divisors $p$ of $2/(p-2)$, with the factor $1$ at $p=2$. This matches the weight used in the explicit reciprocal denominator expansion on the Tao five-primes mission.
-- source:
--   T. Tao, arXiv:1201.6656, Proposition 4.10 (Riesel--Vaughan normalization)

import Mathlib

open scoped BigOperators
set_option autoImplicit false

namespace PrimePairSieve
noncomputable section

/-- Literal reciprocal sieve weight on squarefree indices (Riesel--Vaughan normalization). -/
def reciprocal_literal_weight (n : ℕ) : ℝ :=
  if Squarefree n then
    ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
  else 0

end
end PrimePairSieve


