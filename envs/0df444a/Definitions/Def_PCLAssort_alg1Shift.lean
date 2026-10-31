-- Prove2me | Definitions.Def_PCLAssort_alg1Shift
-- name    : PCLAssort_alg1Shift
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:23.551802+00:00
-- url     : https://prove2.me/theorems/6f1cd870-d592-4e09-8657-fbc558395559
-- title:
--   The vector $x'$ of Algorithm 1, equation (10)
-- statement:
--   Let $x$ have coordinates in $\{0,\delta,\tfrac12,1-\delta,1\}$ with $0<\delta<\tfrac12$, and let $V_1=\{i: x_i=\delta\}$, $V_2=\{i:x_i=1-\delta\}$, $S(V_1)=\sum_{i\in V_1}s_i$, $S(V_2)=\sum_{i\in V_2}s_i$. The vector $x'$ is
--
--   $$
--   x'_i=\begin{cases}\min\{1,\ \delta+(1-\delta)S(V_2)/S(V_1)\}, & i\in V_1,\\ \max\{0,\ (1-\delta)-(1-\delta)S(V_1)/S(V_2)\}, & i\in V_2,\\ x_i, & \text{otherwise.}\end{cases}
--   $$
--
--   It moves mass from the coordinates at $1-\delta$ to those at $\delta$ while keeping the knapsack constraint tight (Lemma 10).
--
--   **Formalization Note** A division by $S(V_1)$ is evaluated only on $V_1$, and by $S(V_2)$ only on $V_2$, where these sums are positive when sizes are positive.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Algorithm 1, step 2, equation (10), p.795 (PDF p.11)

import Mathlib

namespace PCLAssort

/-- The vector `x′` of step 2 of Algorithm 1, equation (10) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.795). With
`V₁ = {i | x_i = δ}`, `V₂ = {i | x_i = 1 − δ}`, `S(V₁) = ∑_{i ∈ V₁} s_i`, `S(V₂) = ∑_{i ∈ V₂} s_i`:
`x′_i = min{1, δ + (1 − δ) S(V₂)/S(V₁)}` on `V₁`, `max{0, (1 − δ) − (1 − δ) S(V₁)/S(V₂)}` on `V₂`,
and `x′_i = x_i` on `V₃ ∪ V₄` (the coordinates equal to `1/2`, `0` or `1`).

**Formalization Note.** Every other coordinate is left unchanged. A division by `S(V₁)` occurs only
on `V₁`, where `S(V₁) > 0` when sizes are positive; the same holds for `V₂`. Lean's `a / 0 = 0` is
reached only in cases the formula never evaluates. -/
noncomputable def alg1Shift {V : Type} [Fintype V] (s : V → ℝ) (x : V → ℝ) (δ : ℝ) : V → ℝ :=
  fun i =>
    if x i = δ then
      min 1 (δ + (1 - δ) * (∑ k ∈ Finset.univ.filter (fun k => x k = 1 - δ), s k) /
        (∑ k ∈ Finset.univ.filter (fun k => x k = δ), s k))
    else if x i = 1 - δ then
      max 0 ((1 - δ) - (1 - δ) * (∑ k ∈ Finset.univ.filter (fun k => x k = δ), s k) /
        (∑ k ∈ Finset.univ.filter (fun k => x k = 1 - δ), s k))
    else x i

end PCLAssort


