-- Prove2me | Definitions.Def_RoslingAssembly_discCost
-- name    : RoslingAssembly_discCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:41:17.375304+00:00
-- url     : https://prove2.me/theorems/854b510f-5c42-4a10-86ae-01129ec02326
-- title:
--   Discounted cost $J_\beta$ of a policy in problem P
-- statement:
--   For a discount factor $\beta<1$, the objective of problem P for a policy $\pi$ is
--   $$J_\beta(\pi)=\sum_{t\ge1}\beta^{t-1}\,\mathbb E[c_t]-\sum_{i=1}^Nh_i\lambda(l_i+1)\frac{\beta^{l_i}}{1-\beta},$$
--   the expected discounted cost (2) plus the constant (4), with $c_t$ the period cost.
--
--   **Formalization Note** The expectation of the infinite sum is written as a sum of expectations; the two agree for policies with finite discounted cost, and every use of $J_\beta$ in this mission is guarded by that condition.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 567, Problem P, (2) and (4)

import Mathlib
import Definitions.Def_RoslingAssembly_periodCost
import Definitions.Def_RoslingAssembly_pathMeasure
import Definitions.Def_RoslingAssembly_K4
open MeasureTheory

namespace RoslingAssembly

/-- **Discounted cost of a policy in problem P**, (2) with constant (4) (p. 567). Rosling,
*Optimal Inventory Policies for Assembly Systems under Random Demands*, Operations Research
37(4), 1989, p. 567, Problem P: "Min_Y E{ Σ_{t=1}^∞ α^{t−1} ( Σ_{i=1}^N α^{l_i} · h_i · Y_it +
α^{l_1}(p + H_1) ∫_{Y_1t}^∞ (ξ − Y_1t) φ_1^{l_1+1}(ξ) dξ ) } + constant (2)" and "− Σ_{i=1}^N h_i
· λ · (l_i + 1) α^{l_i}/(1 − α) if α < 1 (4)".

For a discount factor `β < 1`,
$$J_\beta(\pi)=\sum_{t\ge1}\beta^{t-1}\,\mathbb E[c_t]-\sum_i h_i\lambda(l_i+1)\beta^{l_i}/(1-\beta),$$
the objective of problem P for the policy `pol`, where `c_t = periodCost … β ω t`.

**Formalization Note.** The expectation of the infinite sum is written as the sum of the
expectations; the two agree, and are finite, for policies that are `Admissible` (every use of
`discCost` in this mission is guarded by `Admissible`, since an unguarded `∫` or `∑'` would read
`0` on a non-integrable or non-summable input). Sum index `n : ℕ` is paper period `n + 1`. -/
noncomputable def discCost {N : ℕ} [NeZero N] (net : Network N) (ℓ : Fin N → ℕ) (H : Fin N → ℝ)
    (p : ℝ) (μ : Measure ℝ) (Yh : ℤ → Fin N → ℝ) (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) (β : ℝ) : ℝ :=
  (∑' n : ℕ, β ^ n * ∫ ω, periodCost net ℓ H p μ Yh pol β ω ((n : ℤ) + 1) ∂(pathMeasure μ)) +
    K4 net ℓ H μ β

end RoslingAssembly


