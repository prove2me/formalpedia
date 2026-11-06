-- Prove2me | Definitions.Def_ParetoNCSched_hFun
-- name    : ParetoNCSched_hFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:36.1552+00:00
-- url     : https://prove2.me/theorems/bc4f82bc-d6b6-4997-9a5f-e5b47e60a590
-- title:
--   The function $h(\xi)=\xi-\frac{1+R}{2}\xi^2$ of (9)
-- statement:
--   $$h(\xi)=\xi-\frac{1+R}{2}\,\xi^2 .$$
--   It is concave with maximum $h(\tilde\xi)=\frac{1}{2(1+R)}$ at $\tilde\xi=1/(1+R)$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.2, Eq. (9), p.24

import Mathlib

namespace ParetoNCSched

/-- **The function `h`** of (9). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.2, (9), p.24: "h(ξ) = ξ − ((1 + R)/2) ξ²". -/
noncomputable def hFun (R ξ : ℝ) : ℝ :=
  ξ - (1 + R) / 2 * ξ ^ 2

end ParetoNCSched


