-- Prove2me | Definitions.Def_FourierRankQLB_signObj
-- name    : FourierRankQLB_signObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:21.654986+00:00
-- url     : https://prove2.me/theorems/78f5bd25-c377-406b-b5db-85c81e7176d0
-- title:
--   The normalized sign vector $v=d^{-1/2}\sigma$
-- statement:
--   For a sign vector $\sigma\in\{-1,+1\}^d$,
--   $$
--   v=d^{-1/2}(\sigma_1,\dots,\sigma_d),
--   $$
--   a unit vector of $\mathbb R^d$. It is the random objective of the determinant predictor.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §4.3, p.28

import Mathlib
import Definitions.Def_FourierRankQLB_SignVec
import Definitions.Def_FourierRankQLB_boolSign

namespace FourierRankQLB

/-- The normalized sign vector `v = d^{-1/2}(σ₁, …, σ_d)`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §4.3, p. 28. -/
noncomputable def signObj {d : ℕ} (σ : SignVec d) : Fin d → ℝ :=
  fun i => boolSign (σ i) / √(d : ℝ)

end FourierRankQLB


