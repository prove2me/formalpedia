-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_Bfun
-- name    : ParetoNCSched_Supplement_Bfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:34:37.183298+00:00
-- url     : https://prove2.me/theorems/fd72fc2f-5320-4e78-ab20-0dfb5f089ce0
-- title:
--   The random fraction $B$
-- statement:
--   For $\rho>0$ and $V\in(0,1)$,
--
--   $$B=\frac{V^2}{V^2+3\rho V+\rho^2}\in(0,1).$$
--
--   $\mathrm{RT}_\rho$ draws $V$ uniformly in $(0,1)$ and uses the level $L=w_y^{-1}(B)$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13; (23), p.39

import Mathlib

namespace ParetoNCSched.Supplement

/-- **The random fraction `B`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, line 1, p.13, and (23), p.39:
"B = V²/(V² + 3ρV + ρ²)", where `V` is drawn uniformly in `(0, 1)`.

**Formalization Note.** For `ρ > 0` and `V ∈ (0, 1)`, `B ∈ (0, 1)`. -/
noncomputable def Bfun (ρ V : ℝ) : ℝ :=
  V ^ 2 / (V ^ 2 + 3 * ρ * V + ρ ^ 2)

end ParetoNCSched.Supplement


