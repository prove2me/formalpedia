-- Prove2me | Definitions.Def_FourierRankQLB_innerParallel
-- name    : FourierRankQLB_innerParallel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:25.637461+00:00
-- url     : https://prove2.me/theorems/1522194a-fd2c-4507-a9f0-18c1178ca99a
-- title:
--   The inner parallel set $K^{-\delta}$
-- statement:
--   For $\delta>0$,
--   $$
--   K^{-\delta}=\{x: B_2(x,\delta)\subseteq K\},
--   $$
--   the points of $K$ at distance at least $\delta$ from its boundary, with $B_2$ the closed Euclidean ball.
--
--   It is the comparison set of approximately feasible optimization.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (5), p.13

import Mathlib
import Definitions.Def_FourierRankQLB_Ambient

namespace FourierRankQLB

/-- The inner parallel set `K^{-δ} = {x : B₂(x, δ) ⊆ K}` of Eq. (5).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (5), p. 13.

**Formalization Note.** `B₂` is the closed ball, as on p. 12. -/
def innerParallel {n : ℕ} (K : Set (Ambient n)) (δ : ℝ) : Set (Ambient n) :=
  {x | Metric.closedBall x δ ⊆ K}

end FourierRankQLB


