-- Prove2me | Definitions.Def_MPBSelect_Problem_IsOptimal
-- name    : MPBSelect_Problem_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:47.066099+00:00
-- url     : https://prove2.me/theorems/76daacb5-bc6f-4ac3-ab89-7eb678f8b426
-- title:
--   Optimality for the relaxed OCBA problem (20)
-- statement:
--   The relaxed OCBA problem (20) is
--   $$
--   \max_{\boldsymbol\alpha}\ \min_{(i,\theta_b)\in\Xi}W_i(\theta_b)G_i(\theta_b)\quad\text{subject to}\quad\sum_{i=1}^k\sum_{b=1}^B\alpha_i(\theta_b)=1,\ \ \alpha_i(\theta_b)\ge0 .
--   $$
--   An allocation $\boldsymbol\alpha$ is **optimal** for (20) if it is feasible and its objective value is at least that of every feasible allocation.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, §4.2, p.17, (20)

import Mathlib
import Definitions.Def_MPBSelect_feasibleSet
import Definitions.Def_MPBSelect_Problem_ldr

namespace MPBSelect

/-- **Optimality for problem (20).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, (20), p.17.

`α` is optimal for (20) when it is feasible (in the `kB`-simplex) and its objective value
`LDR(α)` is at least that of every feasible allocation. -/
def Problem.IsOptimal {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ) : Prop :=
  α ∈ feasibleSet k B ∧ ∀ α' ∈ feasibleSet k B, P.ldr α' ≤ P.ldr α

end MPBSelect


