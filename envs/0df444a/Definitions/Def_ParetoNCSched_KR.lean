-- Prove2me | Definitions.Def_ParetoNCSched_KR
-- name    : ParetoNCSched_KR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:32.6626+00:00
-- url     : https://prove2.me/theorems/85941c90-2007-484a-8b06-4f976f33d916
-- title:
--   The constant $K=1+\tilde\xi/\beta=R^2/((R+1)(R-2))$ of (14)
-- statement:
--   $$K=1+\frac{\tilde\xi}{\beta}=\frac{R^2}{(R+1)(R-2)} .$$
--
--   **Formalization Note** Defined by the closed form; for $R>2$ it equals $1+\tilde\xi/\beta$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, Eq. (14), p.28

import Mathlib

namespace ParetoNCSched

/-- **The constant `K = 1 + ξ̃/β = R²/((R + 1)(R − 2))`** of (14). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, (14), p.28.

**Formalization Note.** Defined by the closed form `R²/((R + 1)(R − 2))`; for `R > 2` it equals
`1 + ξ̃/β`. -/
noncomputable def KR (R : ℝ) : ℝ :=
  R ^ 2 / ((R + 1) * (R - 2))

end ParetoNCSched


