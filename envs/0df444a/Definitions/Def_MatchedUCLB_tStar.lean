-- Prove2me | Definitions.Def_MatchedUCLB_tStar
-- name    : MatchedUCLB_tStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:28.239021+00:00
-- url     : https://prove2.me/theorems/29bd2648-c930-49c5-a08e-a476b92698f4
-- title:
--   The endpoint coordinate $t^\star_j=\sqrt m\,(m+1)\tau_j$
-- statement:
--   For a chain length $m$ and a scale $\tau>0$, the **endpoint coordinate** is $t^\star=\sqrt m\,(m+1)\,\tau$, the coordinate of the phase endpoint along the starting direction.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.10), p.8

import Mathlib

namespace MatchedUCLB

/-- **The endpoint coordinate `t⋆_j = √m (m+1) τ_j`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.10), p.8. -/
noncomputable def tStar (m : ℕ) (τ : ℝ) : ℝ :=
  Real.sqrt m * (m + 1) * τ

end MatchedUCLB


