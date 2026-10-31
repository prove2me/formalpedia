-- Prove2me | Definitions.Def_FullPriceTime_IsOptimalPlan
-- name    : FullPriceTime_IsOptimalPlan
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:15.480784+00:00
-- url     : https://prove2.me/theorems/968f153f-8c1d-4e41-b04b-29ddb06661d5
-- title:
--   Optimal plan of (PC) for a fixed purchase decision
-- statement:
--   A plan $p=(t_l,c_l,t_w,c_O)$ is **optimal** for problem (PC) with a fixed purchase decision $y$ (at price $r$ and time commitment $\delta$) when it is feasible for that problem and
--   $$U(q_{t_l},q_{c_l})\le U(t_l,c_l)\quad\text{for every plan } q \text{ feasible for the same problem.}$$
--   With $y=1$ this is an optimal plan of a buyer ($j=B$), with $y=0$ of a non-buyer ($j=NB$).
--
--   **Formalization Note** With $y$ fixed, the term $Vy$ of the objective of (PC) is constant, so the service value $V$ does not appear. An optimal plan is a maximizer over all four variables; that the constraints bind at the optimum is not built in.
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, §3.1, p.8 (optimal actions (t^j_w, c^j_O), j ∈ {NB, B}); Appendix A.2, p.32

import Mathlib
import Definitions.Def_FullPriceTime_IsFeasiblePlan

namespace FullPriceTime

/-- **Optimal plan of (PC) for a fixed purchase decision.**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, §3.1, p.8 (PDF p.8): "consumers' optimal actions (t^j_w, c^j_O) …
where j ∈ {NB, B} denotes a non-buyer's and a buyer's decision respectively"; Appendix A.2, p.32
(PDF p.32).

`IsOptimalPlan T U O comp r δ y p` holds when `p` is feasible for (PC) with purchase decision `y`
and `U(q.t_l, q.c_l) ≤ U(p.t_l, p.c_l)` for every plan `q` feasible for the same problem. With
`y = 1` this is an optimal plan of a buyer (`j = B`), with `y = 0` of a non-buyer (`j = NB`).

**Formalization Note** With `y` fixed, the term `V·y` of the objective of (PC) is a constant, so a
maximizer of `U(t_l, c_l) + V·y` is a maximizer of `U(t_l, c_l)`; `V` does not appear. An optimal
plan is a maximizer over all four variables; the binding of the constraints that the paper uses on
p.32 is not built in. -/
def IsOptimalPlan (T : ℝ) (U : ℝ × ℝ → ℝ) (O : ℝ → ℝ) (comp : ℝ → ℝ) (r δ y : ℝ)
    (p : Plan) : Prop :=
  IsFeasiblePlan T O comp r δ y p ∧
    ∀ q : Plan, IsFeasiblePlan T O comp r δ y q → U (q.tl, q.cl) ≤ U (p.tl, p.cl)

end FullPriceTime


