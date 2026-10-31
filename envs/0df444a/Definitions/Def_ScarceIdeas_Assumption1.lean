-- Prove2me | Definitions.Def_ScarceIdeas_Assumption1
-- name    : ScarceIdeas_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:03.10345+00:00
-- url     : https://prove2.me/theorems/1b61892a-2169-475c-9d3a-37842bb1abf0
-- title:
--   Assumption 1: the prior $h_0$ is continuous, bounded, has finite moments, and $h_0(0)>0$
-- statement:
--   The social planner's prior belief about the Poisson arrival rate $\lambda$ of ideas is a density $h_0$ on $[0,\infty)$. **Assumption 1** requires:
--
--   1. $h_0(\lambda)\ge0$ for $\lambda\ge0$ and $\int_0^\infty h_0(\lambda)\,d\lambda=1$;
--   2. $h_0$ is continuous on $[0,\infty)$;
--   3. $h_0$ is bounded on $[0,\infty)$;
--   4. every moment is finite: $\int_0^\infty\lambda^k h_0(\lambda)\,d\lambda<\infty$ for $k=0,1,2,\dots$;
--   5. $h_0(0)>0$.
--
--   The last condition fixes the decay rate of the posterior moments (Lemma 2) and hence the constant $2/r$ in Theorem 3.
--
--   **Formalization Note** The arrival rate is written `lam`; integrals are over $(0,\infty)$.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §2, Assumption 1, p.11

import Mathlib

namespace ScarceIdeas

/-- **Assumption 1 on the prior density `h₀` of the arrival rate.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§2, p.11: "the social planner's initial beliefs about λ … are given by a probability density
h0(λ) defined on λ ∈ R+. … Assumption 1 h0 is continuous and bounded, has finite moments, and
h0(0) > 0."

`Assumption1 h0` says:
1. `h0` is a probability density on `[0, ∞)`: `h0 λ ≥ 0` for `λ ≥ 0` and `∫_0^∞ h0 = 1`;
2. `h0` is continuous on `[0, ∞)`;
3. `h0` is bounded on `[0, ∞)`;
4. every moment is finite: `λ ↦ λ^k h0(λ)` is integrable on `(0, ∞)` for every `k : ℕ`;
5. `h0 0 > 0`.

**Formalization Note** The arrival rate is written `lam` (`λ` is reserved in Lean). Only the
values of `h0` on `[0, ∞)` enter any statement; all integrals over `λ` are over `Ioi 0`, which
differs from `[0, ∞)` by a null set. "Has finite moments" is read as all moments `k = 1, 2, …`
(the proof of Lemma 2, p.34, uses every `k`); `k = 0` is integrability of `h0` itself. -/
def Assumption1 (h0 : ℝ → ℝ) : Prop :=
  (∀ lam, 0 ≤ lam → 0 ≤ h0 lam) ∧ (∫ lam in Set.Ioi 0, h0 lam) = 1 ∧
    ContinuousOn h0 (Set.Ici 0) ∧ (∃ B : ℝ, ∀ lam, 0 ≤ lam → h0 lam ≤ B) ∧
    (∀ k : ℕ, MeasureTheory.IntegrableOn (fun lam => lam ^ k * h0 lam) (Set.Ioi 0)) ∧ 0 < h0 0

end ScarceIdeas


