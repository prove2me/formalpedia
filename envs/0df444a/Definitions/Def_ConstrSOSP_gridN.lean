-- Prove2me | Definitions.Def_ConstrSOSP_gridN
-- name    : ConstrSOSP_gridN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:46.729678+00:00
-- url     : https://prove2.me/theorems/b8d061e8-18d9-4af8-9460-9b8cfd21deb4
-- title:
--   Grid size $N=6\cdot2^n+6$
-- statement:
--   For an Iter instance on $[2^n]$ the construction uses the square $[0,N]^2$ with $N=6\cdot2^n+6$ and the grid $\mathcal G=\{(a,b): a,b\in\{0,\dots,N\}\}$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.1, p.22

import Mathlib

namespace ConstrSOSP

/-- **The grid size `N = 6 · 2ⁿ + 6`** (arXiv:2604.02285, 2 Nov 2026, §5.1, p.22: "We define
N = 6 · 2^n + 6, where 2^n represents the domain of Iter"). The construction lives on the square
`[0, N]²` with grid `G = {(a, b) | a, b ∈ {0, 1, …, N}}` (12). -/
def gridN (n : ℕ) : ℕ :=
  6 * 2 ^ n + 6

end ConstrSOSP


