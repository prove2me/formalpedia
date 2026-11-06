-- Prove2me | Definitions.Def_FourierRankQLB_approxSuccess
-- name    : FourierRankQLB_approxSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:56.740118+00:00
-- url     : https://prove2.me/theorems/87eb6885-eb31-49ef-9f30-db26a8bb19c7
-- title:
--   The success event (8) of approximately feasible optimization
-- statement:
--   For a body $K$, a unit objective $c$ and a tolerance $\delta$, the set of outputs $y$ with
--   $$
--   \operatorname{dist}(y,K)\le\delta,\qquad c^Ty\ge h_{K^{-\delta}}(c)-\delta .
--   $$
--   An approximately feasible optimizer must return a point of this set with probability at least $2/3$. The output may leave $K$ by $\delta$, while the comparison set moves inward by $\delta$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Definition 2.6, Eq. (8), p.14

import Mathlib
import Definitions.Def_FourierRankQLB_supportFn
import Definitions.Def_FourierRankQLB_innerParallel

namespace FourierRankQLB

/-- The success event (8) of an approximately feasible optimizer: `dist(y, K) ≤ δ` and
`cᵀy ≥ h_{K^{-δ}}(c) - δ`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Definition 2.6, Eq. (8), p. 14.

**Formalization Note.** `Metric.infDist y K` is `dist(y, K)` for nonempty `K`. -/
def approxSuccess {n : ℕ} (K : Set (Ambient n)) (c : Ambient n) (δ : ℝ) : Set (Ambient n) :=
  {y | Metric.infDist y K ≤ δ ∧ supportFn (innerParallel K δ) c - δ ≤ inner ℝ c y}

end FourierRankQLB


