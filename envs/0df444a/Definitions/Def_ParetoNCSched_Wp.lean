-- Prove2me | Definitions.Def_ParetoNCSched_Wp
-- name    : ParetoNCSched_Wp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:30.361547+00:00
-- url     : https://prove2.me/theorems/6c0f2445-1192-4307-ab6e-3f8247410afb
-- title:
--   The function $W(\xi)=1-\frac{1}{(1-\xi)(1+\xi/\beta)^\gamma}$ of (15)
-- statement:
--   On $[0,\tilde\xi]$,
--   $$W(\xi)=1-\frac{1}{(1-\xi)\,(1+\xi/\beta)^{\gamma}} .$$
--
--   **Formalization Note** The same formula on all of $\mathbb R$ (real power); only $[0,\tilde\xi]$ is used.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, Eq. (15), p.28

import Mathlib
import Definitions.Def_ParetoNCSched_betR
import Definitions.Def_ParetoNCSched_gamR

namespace ParetoNCSched

/-- **The function `W`** of (15). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, (15), p.28: "Define on [0, ξ̃]
W(ξ) = 1 − 1/((1 − ξ)(1 + ξ/β)^γ)".

**Formalization Note.** Defined on all of `ℝ` by the same formula (`Real.rpow`); only `[0, ξ̃]` is
used. -/
noncomputable def Wp (R ξ : ℝ) : ℝ :=
  1 - 1 / ((1 - ξ) * (1 + ξ / betR R) ^ gamR R)

end ParetoNCSched


