-- Prove2me | Definitions.Def_LL_Decomp1526a_gcount
-- name    : LL_Decomp1526a_gcount
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:03:11.589425+00:00
-- url     : https://prove2.me/theorems/f9f2c253-ee14-4895-8aff-8fb0b23ed67c
-- title:
--   Unweighted Goldbach count
-- statement:
--   For $N\in\mathbb N$, the natural number $g(N)=\#\{p\le N : p \text{ and } N-p \text{ are both prime}\}$, counting ordered pairs.

import Mathlib

namespace LL_Decomp1526a

noncomputable section

open Finset Real
open scoped Chebyshev Classical

def gcount (N : ℕ) : ℕ := #{p ∈ range (N + 1) | p.Prime ∧ (N - p).Prime}

end

end LL_Decomp1526a


