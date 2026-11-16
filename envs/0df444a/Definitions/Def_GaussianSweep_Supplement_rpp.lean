-- Prove2me | Definitions.Def_GaussianSweep_Supplement_rpp
-- name    : GaussianSweep_Supplement_rpp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:34:37.335618+00:00
-- url     : https://prove2.me/theorems/7bdf92da-f7c7-4e49-9095-23785400fc29
-- title:
--   The correlation level $r_{pp} = 2\sqrt{p-1}/p$
-- statement:
--   For an integer $p \ge 3$,
--   $$
--   r_{pp} = \frac{2\sqrt{p-1}}{p},
--   $$
--   so that $r_{33} = 2\sqrt2/3$, $r_{44} = \sqrt3/2$ and $r_{55} = 4/5$. It is the edge-correlation level of the padded Gaussian labels for graphs of maximum degree $p$.
--
--   **Formalization Note** $p$ is a natural number cast to $\mathbb R$; the paper uses it only for $p \ge 3$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3.5, p.20 (PDF p.22)

import Mathlib

namespace GaussianSweep.Supplement

/-- The correlation bound `r_pp = 2√(p − 1)/p` for maximum degree `p`
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3.5, p.20 (PDF p.22)); `r₃₃ = 2√2/3`, `r₄₄ = √3/2`,
`r₅₅ = 4/5`.

**Formalization Note** `p : ℕ`, cast to `ℝ`; the paper uses integers `p ≥ 3`, so the real
subtraction `p − 1` and the division by `p` are on their intended domain there. -/
noncomputable def rpp (p : ℕ) : ℝ := 2 * Real.sqrt ((p : ℝ) - 1) / (p : ℝ)

end GaussianSweep.Supplement


