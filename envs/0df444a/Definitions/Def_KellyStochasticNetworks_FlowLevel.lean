-- Prove2me | Definitions.Def_KellyStochasticNetworks_FlowLevel
-- name    : KellyStochasticNetworks_FlowLevel
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T16:47:42.754785+00:00
-- url     : https://prove2.me/theorems/2f57d501-e0d7-403b-8d37-ec97750b59ae
-- title:
--   The weighted $\alpha$-fair objective
-- statement:
--   The objective of the **weighted $\alpha$-fair** rate allocation of Chapter 8 of Kelly and
--   Yudovina, *Stochastic Networks*, written in the aggregate variables of problem (8.4).
--
--   Let $n_r$ be the number of flows active on route $r$, each allocated rate $x_r$, so that route $r$
--   consumes $X_r = n_r x_r$ at every resource it uses. Given weights $w_r > 0$ and a parameter
--   $\alpha \in (0, \infty)$, the weighted $\alpha$-fair allocation maximizes
--   $$G(X) = \sum_r w_r n_r^{\alpha}\,\frac{X_r^{1-\alpha}}{1-\alpha} \qquad (\alpha \ne 1),
--     \qquad\qquad G(X) = \sum_r w_r n_r \log X_r \qquad (\alpha = 1),$$
--   subject to $\sum_{r : j \in r} X_r \le C_j$ for every resource $j$, over $X \ge 0$.
--
--   The two cases are the same function in disguise: the derivative is $w_r n_r^{\alpha}X_r^{-\alpha}$
--   for every $\alpha \in (0,\infty)$, which is the point of Exercise 8.3, and the $\alpha = 1$ branch
--   is the natural continuation of the family through the removable singularity at $\alpha = 1$.
--
--   The family interpolates between the fairness notions of Chapter 7. As $\alpha \to 0$ with
--   $w \equiv 1$ the total throughput approaches its maximum; at $\alpha = 1$ the rates are weighted
--   proportionally fair; at $\alpha = 2$ with $w_r = 1/T_r^2$ they are TCP fair; and as
--   $\alpha \to \infty$ with $w \equiv 1$ they approach max-min fairness.
--
--   **Formalization Note** The objective is written in the aggregate rates $X_r = n_r x_r$ of problem
--   (8.4) rather than the per-flow rates of (8.1). The two problems are equivalent, but in (8.4) the
--   feasible set does not depend on $n$, which is the form the stability argument uses; that feasible
--   set is the `networkFeasible` published in mission VII of this series. Powers are real exponents,
--   so the objective is meaningful where the flow counts and rates are positive. The case split at
--   $\alpha = 1$ is explicit, exactly as the book defines it.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, ch. 8, pp. 188 and 190 (PDF pp. 196 and 198): the weighted alpha-fair allocation problem (8.1) p. 188, and its rewriting (8.4) in the variables X_r = n_r x_r p. 190. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

/-- The objective of the **weighted α-fair** allocation problem, written in the variables
`X_r = n_r x_r` of problem (8.4):
`G(X) = ∑_r w_r n_r^α X_r^{1-α}/(1-α)` for `α ≠ 1`, and `∑_r w_r n_r log X_r` for `α = 1`.
Kelly–Yudovina, *Stochastic Networks*, pp. 188 and 190. -/
noncomputable def alphaFairObjective {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (X : Fin R → ℝ) : ℝ :=
  if α = 1 then ∑ r, w r * n r * Real.log (X r)
  else ∑ r, w r * n r ^ α * (X r ^ (1 - α) / (1 - α))

end KellyStochasticNetworks


