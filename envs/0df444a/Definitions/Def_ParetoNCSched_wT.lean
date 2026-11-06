-- Prove2me | Definitions.Def_ParetoNCSched_wT
-- name    : ParetoNCSched_wT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:39.510198+00:00
-- url     : https://prove2.me/theorems/3c9581e4-85d4-4186-98f3-0e0b985460b6
-- title:
--   The threshold $\tilde w=W(\tilde\xi)$ of (15)
-- statement:
--   $$\tilde w=W(\tilde\xi)=1-\frac{1}{(1-\tilde\xi)K^{\gamma}} .$$
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, Eq. (15), p.28

import Mathlib
import Definitions.Def_ParetoNCSched_Wp
import Definitions.Def_ParetoNCSched_xiT

namespace ParetoNCSched

/-- **The threshold `w̃ = W(ξ̃)`** of (15). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, (15), p.28:
"w̃ = W(ξ̃) = 1 − 1/((1 − ξ̃)K^γ)". -/
noncomputable def wT (R : ℝ) : ℝ :=
  Wp R (xiT R)

end ParetoNCSched


