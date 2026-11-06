-- Prove2me | Definitions.Def_LawLocalComp_cellKey
-- name    : LawLocalComp_cellKey
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:14.133491+00:00
-- url     : https://prove2.me/theorems/ba82f3cf-0256-4ae4-8f8f-59297138803a
-- title:
--   The cells of Lemma 7.2
-- statement:
--   For a baseline $b$, an active mean $\nu$, $r\ge1$, $0<\delta<1$ and $\rho>1$, the residual $R=x-b$ of an atom $x$ is placed in one of the cells
--   $$\{0\},\quad(0,\delta\nu),\quad[\delta\nu\rho^i,\min\{\delta\nu\rho^{i+1},3\nu r\})\ (i\ge0,\ \delta\nu\rho^i<3\nu r),\quad[3\nu r,\infty).$$
--
--   **Formalization Note** The ratio-$\rho$ intervals are anchored at $\delta\nu$, reading "ratio-$\rho$ intervals in $[\delta\nu,3\nu r)$".
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 7.2, p.13

import Mathlib
open Classical

namespace LawLocalComp

/-- **The cells of Lemma 7.2.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 7.2, p.13 ("Partition each residual into {0}, (0, δν), ratio-ρ intervals in [δν, 3νr),
and one tail cell [3νr, ∞)").

For baseline `b`, active mean `ν` and residual `R = x − b`, `cellKey r δ ρ b ν x` is `−2` on `R ≤ 0`,
`−1` on `0 < R < δν`, `−3` on `R ≥ 3νr`, and otherwise the `i ≥ 0` with
`δνρ^i ≤ R < δνρ^{i+1}`, i.e. the cell `[δνρ^i, min{δνρ^{i+1}, 3νr})`.

**Formalization Note.** The ratio-`ρ` intervals are anchored at `δν` (a reading of "ratio-ρ intervals in
[δν, 3νr)"). -/
noncomputable def cellKey (r : ℕ) (δ ρ b ν : ℝ) (x : ℝ) : ℤ :=
  if x - b ≤ 0 then -2
  else if x - b < δ * ν then -1
  else if 3 * ν * r ≤ x - b then -3
  else ⌊Real.logb ρ ((x - b) / (δ * ν))⌋

end LawLocalComp


