-- Prove2me | Definitions.Def_AggStatePG_objective
-- name    : AggStatePG_objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:03.170773+00:00
-- url     : https://prove2.me/theorems/9e09e158-2630-442d-a6d1-9e04c02e45c3
-- title:
--   Policy gradient objective $J(\pi)$, display (2)
-- statement:
--   For a finite MDP with initial distribution $\rho$ and discount factor $\gamma$, the **policy gradient objective** is
--   $$J(\pi)=(1-\gamma)\sum_{s\in\mathcal S}\rho(s)V_\pi(s),\qquad(2)$$
--   the expected discounted reward from a random initial state, normalized so that it is an average per-period reward.
--
--   **Formalization Note** $\sum_s\rho(s)V_\pi(s)$ is the published `valueAt`.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, display (2), p.5

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

open PolicyGradTheory.ProjGA

namespace AggStatePG

/-- The **policy gradient objective** (2) (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, display (2), p.5):
`J(π) = (1 - γ) ∑_{s ∈ S} ρ(s) V_π(s)`, the normalized expected discounted reward from an initial
state drawn from `ρ`.

**Formalization Note.** `valueAt π P r γ ρ = ∑_s ρ(s) V_π(s)` is the published
`PolicyGradTheory.ProjGA.valueAt`. -/
noncomputable def objective {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (ρ : S → ℝ) (π : S → A → ℝ) : ℝ :=
  (1 - γ) * valueAt π P r γ ρ

end AggStatePG


