-- Prove2me | Definitions.Def_LL_Decomp1526a_rep
-- name    : LL_Decomp1526a_rep
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:02:57.328084+00:00
-- url     : https://prove2.me/theorems/2a99510f-c23b-4d72-9065-78630cab2a17
-- title:
--   Weighted representation function
-- statement:
--   For $N\in\mathbb N$, $r(N)=\sum_{p\le N,\ p\text{ prime},\ N-p\text{ prime}}\log p\,\log(N-p)$, a real number, summing over ordered pairs and using natural subtraction, with the term $0$ when $N-p$ is not prime.

import Mathlib

namespace LL_Decomp1526a

noncomputable section

open Finset Real
open scoped Chebyshev Classical

def rep (N : ℕ) : ℝ :=
  ∑ p ∈ (range (N + 1)).filter Nat.Prime,
    if (N - p).Prime then Real.log p * Real.log ((N - p : ℕ) : ℝ) else 0

end

end LL_Decomp1526a


