-- Prove2me | Definitions.Def_FourierRankQLB_boolSign
-- name    : FourierRankQLB_boolSign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:12.06519+00:00
-- url     : https://prove2.me/theorems/feff8f33-13d4-4f2d-9446-22552f1b4cfc
-- title:
--   The coding of $\{-1,+1\}$ by Booleans
-- statement:
--   The map sending `true` to $+1$ and `false` to $-1$. It codes both the entries of a sign vector and a two-outcome prediction in $\{-1,+1\}$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §4.3, p.28 and Theorem 3.3, p.18

import Mathlib

namespace FourierRankQLB

/-- The coding `true ↦ +1`, `false ↦ -1` of a sign, or of a prediction in `{-1, +1}`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §4.3, p. 28 and Theorem 3.3, p. 18. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

end FourierRankQLB


