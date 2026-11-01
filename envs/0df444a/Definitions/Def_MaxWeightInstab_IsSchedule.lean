-- Prove2me | Definitions.Def_MaxWeightInstab_IsSchedule
-- name    : MaxWeightInstab_IsSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:28.817372+00:00
-- url     : https://prove2.me/theorems/3ce4951a-b289-4d68-a340-63897c48cac2
-- title:
--   Feasible schedules $\mathcal S$ of display (3)
-- statement:
--   For $\nu\in\mathbb N$, a vector $\sigma\in\mathbb Z_+^{2J+2}$ is a **feasible schedule**, $\sigma\in\mathcal S$, when
--
--   $$
--   \sigma_{\mathcal A_0}+\frac1\nu\sum_{j=1}^J\sigma_{\mathcal A_j}\le 1
--   \qquad\text{and}\qquad
--   \sigma_{\mathcal B_0}+\frac1\nu\sum_{j=1}^J\sigma_{\mathcal B_j}\le 1 .
--   $$
--
--   In each time unit, each component either serves up to $\nu$ jobs from its externally fed queues or a single job from its internally fed queue.
--
--   **Formalization Note** Both inequalities are multiplied by $\nu$ and read $\nu\sigma_{\mathcal A_0}+\sum_{j\ge1}\sigma_{\mathcal A_j}\le\nu$ over $\mathbb N$; for $\nu\ge1$ this is the same set.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (3), p.3

import Mathlib
import Definitions.Def_MaxWeightInstab_State

namespace MaxWeightInstab

/-- The feasible schedules `𝒮` of the network of Figure 1, display (3) (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.3):
`σ_{𝒜₀} + (1/ν) ∑_{j=1}^J σ_{𝒜_j} ≤ 1` and `σ_{ℬ₀} + (1/ν) ∑_{j=1}^J σ_{ℬ_j} ≤ 1`.

**Formalization Note.** Both inequalities are multiplied by `ν`, so they read
`ν σ_{𝒜₀} + ∑ σ_{𝒜_j} ≤ ν` over `ℕ`; for `ν ≥ 1` this is the same set. The set is downward
closed, as the paper's standing assumption on `𝒮` (p.1) requires. -/
def IsSchedule {J : ℕ} (ν : ℕ) (σ : State J) : Prop :=
  ν * σ (Sum.inl 0) + ∑ j : Fin J, σ (Sum.inl j.succ) ≤ ν ∧
    ν * σ (Sum.inr 0) + ∑ j : Fin J, σ (Sum.inr j.succ) ≤ ν

end MaxWeightInstab


