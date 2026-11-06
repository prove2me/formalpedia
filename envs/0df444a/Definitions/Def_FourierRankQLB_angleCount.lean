-- Prove2me | Definitions.Def_FourierRankQLB_angleCount
-- name    : FourierRankQLB_angleCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:44:28.427194+00:00
-- url     : https://prove2.me/theorems/3639e7b5-db78-4a4d-9c15-8667deb383e1
-- title:
--   The number of eigenangles in a set
-- statement:
--   For $Q\in O(d)$ and $J\subseteq[0,\pi]$, the number of positive eigenangles of $Q$ in $J$, with multiplicity.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 3.7, p.21

import Mathlib
import Definitions.Def_FourierRankQLB_eigenangles

namespace FourierRankQLB

open scoped Classical in
/-- The number of positive eigenangles of `Q` in the set `J`, with multiplicity.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 3.7, p. 21. -/
noncomputable def angleCount {d : ℕ} (Q : Od d) (J : Set ℝ) : ℕ :=
  Multiset.card ((eigenangles Q).filter fun θ => θ ∈ J)

end FourierRankQLB


