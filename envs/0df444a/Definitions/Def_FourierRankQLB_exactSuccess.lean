-- Prove2me | Definitions.Def_FourierRankQLB_exactSuccess
-- name    : FourierRankQLB_exactSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:07.602417+00:00
-- url     : https://prove2.me/theorems/a17f3d34-8a38-4c92-a014-59950b811070
-- title:
--   The success event (7) of exactly feasible optimization
-- statement:
--   For a body $K$, a unit objective $c$ and an accuracy $\varepsilon$, the set of outputs $\hat x$ with
--   $$
--   \hat x\in K,\qquad c^T\hat x\ge h_K(c)-\varepsilon .
--   $$
--   An exactly feasible optimizer must return a point of this set with probability at least $2/3$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Definition 2.5, Eq. (7), p.14

import Mathlib
import Definitions.Def_FourierRankQLB_supportFn

namespace FourierRankQLB

/-- The success event (7) of an exactly feasible optimizer: `x̂ ∈ K` and `cᵀx̂ ≥ h_K(c) - ε`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Definition 2.5, Eq. (7), p. 14. -/
def exactSuccess {n : ℕ} (K : Set (Ambient n)) (c : Ambient n) (ε : ℝ) : Set (Ambient n) :=
  {x | x ∈ K ∧ supportFn K c - ε ≤ inner ℝ c x}

end FourierRankQLB


