-- Prove2me | Definitions.Def_LocalDOvS_SUS_alphaSUS
-- name    : LocalDOvS_SUS_alphaSUS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:09.831628+00:00
-- url     : https://prove2.me/theorems/8466a918-93d7-4bc3-a80b-1d43c1ca40df
-- title:
--   Confidence level $\alpha=\delta/(2T_{\max})$, $T_{\max}=N^2$ (corrected)
-- statement:
--   The confidence parameter of each interval used by the shrinking uniform sampling algorithm is
--
--   $$
--   \alpha:=\frac{\delta}{2T_{\max}},\qquad T_{\max}:=N^2 ,
--   $$
--
--   so that $\log(2/\alpha)=\log(4N^2/\delta)$.
--
--   **Formalization Note** The paper prints $T_{\max}\leftarrow N$ (Algorithm 2, line 2). The union bound of the correctness proof covers up to $N$ points at up to $N-1$ active-set sizes, so $T_{\max}=N^2$ is used; this is one of the two corrections of the algorithm.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, lines 2 and 6, p.15 (corrected)

import Mathlib

namespace LocalDOvS.SUS

/-- The confidence parameter `α := δ/(2 T_max)` of the corrected shrinking uniform sampling
algorithm, with `T_max := N²` (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Algorithm 2, lines 2 and
6, p.15, which print `T_max ← N`).

**Formalization Note (correction).** The printed `T_max = N` does not pay for the union bound of
the proof: one test per active-set size touches up to `N` points at up to `N − 1` sizes, so
`T_max = N²` is used; then `log(2/α) = log(4N²/δ)`. -/
noncomputable def alphaSUS (N : ℕ) (δ : ℝ) : ℝ :=
  δ / (2 * (N : ℝ) ^ 2)

end LocalDOvS.SUS


