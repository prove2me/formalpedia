-- Prove2me | Definitions.Def_WeightedCongestionBR_bitLen
-- name    : WeightedCongestionBR_bitLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:09.856197+00:00
-- url     : https://prove2.me/theorems/3e7f1692-2c6c-4057-a063-0f3b00b54384
-- title:
--   Bit length $\ell(q)$ of a rational
-- statement:
--   For a rational $q=a/b$ in lowest terms,
--
--   $$
--   \ell(q)=1+\operatorname{size}|a|+\operatorname{size} b ,
--   $$
--
--   where $\operatorname{size}$ is the number of binary digits. It measures the number of bits of the representation of a number.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 4, p.18

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- The bit length of a rational number `q = a/b` in lowest terms, `ℓ(q) := 1 + size|a| + size b`,
used for the input size of Theorem 4 (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Theorem 4, p.18). -/
def bitLen (q : ℚ) : ℕ := 1 + Nat.size q.num.natAbs + Nat.size q.den

end WeightedCongestionBR


