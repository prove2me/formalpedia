-- Prove2me | Definitions.Def_MatchedUCLB_alphaC
-- name    : MatchedUCLB_alphaC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:28.653332+00:00
-- url     : https://prove2.me/theorems/0d562eea-f154-4775-aafe-670938588c06
-- title:
--   The regularizer coefficient $\alpha=\lambda m^{1-3q/2}$
-- statement:
--   For $\lambda>0$ and a chain length $m$, the **regularizer coefficient** is $\alpha=\lambda\,m^{1-3q/2}$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.12b), p.8

import Mathlib

namespace MatchedUCLB

/-- **The regularizer coefficient `α = λ m^{1−3q/2}`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.12b), p.8. -/
noncomputable def alphaC (q : ℝ) (m : ℕ) (lam : ℝ) : ℝ :=
  lam * (m : ℝ) ^ (1 - 3 * q / 2)

end MatchedUCLB


