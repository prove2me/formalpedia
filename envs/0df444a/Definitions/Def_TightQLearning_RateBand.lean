-- Prove2me | Definitions.Def_TightQLearning_RateBand
-- name    : TightQLearning_RateBand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:20.488485+00:00
-- url     : https://prove2.me/theorems/c008197b-174d-49aa-9674-ad7c48299dfb
-- title:
--   (16a) — the learning-rate band
-- statement:
--   The learning rates obey **condition (16a)** if, for every $0\le t\le T$,
--   $$\frac{1}{1+\frac{c_1(1-\gamma)T}{\log^3T}}\le\eta_t\le\frac{1}{1+\frac{c_2(1-\gamma)t}{\log^3T}}.$$
--   It covers constant rates and rescaled linear rates at once.
--
--   **Formalization Note** $\log$ is the natural logarithm. The condition is meaningful only for $T\ge2$, and every statement of the mission that uses it assumes $T\ge2$.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), (16a), p.9

import Mathlib

namespace TightQLearning

/-- The learning-rate condition (16a) of Theorem 2 (arXiv:2102.06548v4, p.9): for all `0 ≤ t ≤ T`,
`1/(1 + c₁(1−γ)T/log³T) ≤ η_t ≤ 1/(1 + c₂(1−γ)t/log³T)`.

**Formalization Note.** `log` is the natural logarithm. The condition divides by `log³T`, so it is
meaningful only for `T ≥ 2`; every statement using `RateBand` carries `2 ≤ T`. -/
def RateBand (c₁ c₂ γ : ℝ) (T : ℕ) (η : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, t ≤ T →
    1 / (1 + c₁ * (1 - γ) * (T : ℝ) / Real.log T ^ 3) ≤ η t ∧
      η t ≤ 1 / (1 + c₂ * (1 - γ) * (t : ℝ) / Real.log T ^ 3)

end TightQLearning


