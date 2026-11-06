-- Prove2me | Definitions.Def_MatchedUCLB_center
-- name    : MatchedUCLB_center
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:26.476197+00:00
-- url     : https://prove2.me/theorems/6413afa9-dd8d-4ee3-8133-25701a30f377
-- title:
--   The phase centers $c_j=\sum_{k<j}h_k$
-- statement:
--   Given phase displacements $h_0,h_1,\dots\in\mathbb R^d$, the **phase centers** are
--
--   $$
--   c_j=\sum_{k<j}h_k ,\qquad j\ge0,
--   $$
--
--   so that $c_0=0$ and $h_j=c_{j+1}-c_j$. Phase $j$ of the construction is anchored at $c_j$ and ends at $c_{j+1}$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Step 1.1, p.5; Eq. (4.15), p.9

import Mathlib

namespace MatchedUCLB

/-- **The phase centers `c_j = ∑_{k<j} h_k`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Step 1.1, p.5 ("we anchor phase `j` at a
center `c_j`, with endpoint `c_{j+1}` and `c_0 = 0`. We define its phase displacement by
`h_j = c_{j+1} − c_j`"), and (4.15), p.9: `c_j = ∑_{k<j} h_k`.

**Formalization Note.** The displacements are a sequence `h : ℕ → ℝ^d`; only `h_0, …, h_{L−1}` are
used by the construction. `center h 0 = 0`. -/
def center {d : ℕ} (h : ℕ → EuclideanSpace ℝ (Fin d)) (j : ℕ) : EuclideanSpace ℝ (Fin d) :=
  ∑ k ∈ Finset.range j, h k

end MatchedUCLB


