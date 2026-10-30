-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch07_deltaTrunc
-- name    : RamanujanLostNotebook_PartIII_ch07_deltaTrunc
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:19:23.019929+00:00
-- url     : https://prove2.me/theorems/ea115851-5e34-4434-9f97-af951a7523c7
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 7: deltaTrunc
-- statement:
--   Truncated discriminant: the polynomial `X · ∏_{k=1}^{N} (1 - X^k)^24` with integer
--   coefficients.  Ramanujan's `Δ(τ) = q (q; q)_∞^24` (p. 205) is the formal power series
--   `q ∏_{k ≥ 1} (1 - q^k)^24`.  The factors with `k > N` are `1` modulo `q^{N+1}`, so this
--   polynomial agrees with `Δ` in every degree `m ≤ N + 1`.
--   Reference: `deltaTrunc 2 = X - 24 X^2 + 252 X^3 - 1448 X^4 + …` (`Δ` itself has
--   `- 1472 q^4`, the first coefficient beyond the exact range).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 7.

import Mathlib

namespace RamanujanLostNotebook.PartIII

/-- Truncated discriminant: the polynomial `X · ∏_{k=1}^{N} (1 - X^k)^24` with integer
coefficients.  Ramanujan's `Δ(τ) = q (q; q)_∞^24` (p. 205) is the formal power series
`q ∏_{k ≥ 1} (1 - q^k)^24`.  The factors with `k > N` are `1` modulo `q^{N+1}`, so this
polynomial agrees with `Δ` in every degree `m ≤ N + 1`.
Reference: `deltaTrunc 2 = X - 24 X^2 + 252 X^3 - 1448 X^4 + …` (`Δ` itself has
`- 1472 q^4`, the first coefficient beyond the exact range). -/
noncomputable def deltaTrunc (N : ℕ) : Polynomial ℤ :=
  Polynomial.X * ∏ k ∈ Finset.Icc 1 N, (1 - Polynomial.X ^ k) ^ 24

end RamanujanLostNotebook.PartIII


