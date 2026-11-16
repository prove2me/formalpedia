-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rtCost
-- name    : ParetoNCSched_Supplement_rtCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:42:28.985903+00:00
-- url     : https://prove2.me/theorems/357272c8-734b-445d-a282-2a356be87ca1
-- title:
--   The expected cost of $\mathrm{RT}_\rho$
-- statement:
--   The randomized algorithm $\mathrm{RT}_\rho$ (Algorithm 2) draws $V$ uniformly in $(0,1)$, sets $B=V^2/(V^2+3\rho V+\rho^2)$ and $L=w_y^{-1}(B)$, and runs $\mathrm{RT}_L$. The instance and the prediction are fixed before $V$ is drawn (oblivious adversary), and the cost is the expected total completion time
--
--   $$\mathbb E\big[\mathrm{RT}_\rho(p,y)\big]=\int_0^1 \mathrm{RT}_{L(V)}(p,y)\,dV.$$
--
--   **Formalization Note** The expectation is the Lebesgue integral in $[0,\infty]$ over $V\in(0,1)$, an interval of length $1$ (a lower integral, equal to the expectation when the cost is measurable in $V$).
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13; Appendix H, pp.39–40; Appendix A, Model, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_rtRate
import Definitions.Def_ParetoNCSched_Supplement_levelOf
import Definitions.Def_ParetoNCSched_Supplement_Bfun
import Definitions.Def_ParetoNCSched_totalCompletion
open scoped ENNReal
open MeasureTheory

namespace ParetoNCSched.Supplement

/-- **Expected cost of `RTρ`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13, and Appendix H, pp.39–40: "RTρ draws V
uniformly in (0, 1)", sets `B = V²/(V² + 3ρV + ρ²)` and `L = w_y⁻¹(B)`, and runs the two stages;
its consistency and robustness use "the expected total completion time in place of the total
completion time" (p.39), the instance and prediction being fixed first (oblivious adversary,
Appendix A, p.15).

`rtCost ρ p y = E_V[RT_{L(V)}(p, y)] = ∫⁻_{(0,1)} totalCompletion p (rtRate L(V) p y) dV`.

**Formalization Note.** The expectation is the Lebesgue lower integral over `V ∈ (0, 1)`, an
interval of length `1`, in `ℝ≥0∞`; it equals the paper's expectation when the cost is measurable in
`V`, and needs no integrability side condition. -/
noncomputable def rtCost {n : ℕ} (ρ : ℝ) (p y : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ V in Set.Ioo (0 : ℝ) 1, totalCompletion p (rtRate (levelOf y (Bfun ρ V)) p y)

end ParetoNCSched.Supplement


