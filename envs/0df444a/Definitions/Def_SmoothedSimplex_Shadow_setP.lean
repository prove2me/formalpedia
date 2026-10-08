-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_setP
-- name    : SmoothedSimplex_Shadow_setP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:47:13.457974+00:00
-- url     : https://prove2.me/theorems/4771fd89-587c-4090-ae75-074bd1567e3a
-- title:
--   Definition 4.0.4 — the set $P=\{\|a_i\|\le 2\ \forall i\}$
-- statement:
--   $P$ is the set of tuples $(a_1,\dots,a_n)$ of vectors in $\mathbb R^d$ for which
--
--   $$
--   \|a_i\|\le 2\quad\text{for all } i .
--   $$
--
--   When the centers have norm at most $1$ and $\sigma\le 1/(3\sqrt{d\ln n})$, the perturbed data lie in $P$ with overwhelming probability, and the analysis of Section 4 conditions on this event.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Definition 4.0.4, printed p. 38 (PDF p. 38)

import Mathlib

namespace SmoothedSimplex.Shadow

/-- The set `P` (Spielman & Teng, arXiv:cs/0111050v7, Definition 4.0.4, printed p. 38,
PDF p. 38): the set of `(a₁, …, aₙ)` for which `‖aᵢ‖ ≤ 2` for all `i`. -/
def setP {d n : ℕ} : Set (Fin n → EuclideanSpace ℝ (Fin d)) :=
  {a | ∀ i, ‖a i‖ ≤ 2}

end SmoothedSimplex.Shadow


