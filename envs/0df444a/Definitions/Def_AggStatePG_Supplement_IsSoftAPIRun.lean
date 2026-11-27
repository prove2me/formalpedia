-- Prove2me | Definitions.Def_AggStatePG_Supplement_IsSoftAPIRun
-- name    : AggStatePG_Supplement_IsSoftAPIRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:23:55.495423+00:00
-- url     : https://prove2.me/theorems/7e4e63a0-1eee-4e9a-b060-043939674ff6
-- title:
--   Algorithm 4 (soft API with on-policy state weights)
-- statement:
--   **Algorithm 4 (Soft API with adaptive weighting).** Input: a step size $\alpha$, an initial policy $\pi_1\in\Pi$ and an aggregation $\phi$. For $t=1,2,\dots$:
--
--   1. (occupancy weighted policy evaluation) $\hat Q_t\in\arg\min_{\hat Q\in\mathcal Q_\phi}\|\hat Q-Q_{\pi_t}\|_{2,\eta_{\pi_t}\times1}$;
--   2. (policy improvement) $\tilde\pi_{t+1}(s)\in\arg\max_{a\in\mathcal A}\hat Q_t(s,a)$ for every $s$;
--   3. (soft policy update) $\pi_{t+1}=\alpha\tilde\pi_{t+1}+(1-\alpha)\pi_t$.
--
--   Here $\eta_\pi(s)=(1-\gamma)\sum_{t\ge0}\gamma^t\,\mathbb P_\rho^\pi(s_t=s)$ is the discounted state occupancy measure of $\pi$ from the initial distribution $\rho$. Sequences $(\pi_t,\tilde\pi_t,\hat Q_t)$ form a **run** if $\pi_1$ is the input policy and the three steps hold at every $t\ge1$.
--
--   With $\alpha=1$ this is API with on-policy state-relevance weights (Algorithm 2). Theorem 8 shows that it coincides with Frank-Wolfe policy gradient (Algorithm 3).
--
--   **Formalization Note** Policies are stacked vectors read as tables; $\eta_\pi$ is the published `visitation`. The greedy policy $\tilde\pi_{t+1}$ is the indicator vector of a maximizing action at each state. Any element of the argmin and any maximizing action are allowed. Iterations are indexed from $t=1$; earlier entries are unconstrained and unused.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, Algorithm 4, p.17

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
import Definitions.Def_AggStatePG_Supplement_IsWLSFit
import Definitions.Def_AggStatePG_Supplement_IsGreedy

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG.Supplement

/-- **Algorithm 4** (Soft API with adaptive weighting; Russo, *Approximation Benefits of Policy
Gradient Methods with Aggregated States*, arXiv:2007.11684v3, Algorithm 4, p.17).
Input `α`, `π_1 ∈ Π`, `φ`. For `t = 1, 2, …`:
(2) `Q̂_t ∈ argmin_{Q̂ ∈ Q_φ} ‖Q̂ − Q_{π_t}‖_{2,η_{π_t}×1}`;
(3) `π̃_{t+1}(s) ∈ argmax_{a ∈ A} Q̂_t(s,a)` for all `s`;
(4) `π_{t+1} = α π̃_{t+1} + (1 − α) π_t`.
`IsSoftAPIRun P r γ ρ φ α y₁ y ỹ Q̂` says that `y` (the policies `π_t`), `ỹ` (the greedy policies
`π̃_t`) and `Q̂` are a run of Algorithm 4 with these inputs: `y 1 = y₁` and, for every `t ≥ 1`,
`Q̂ t` is a least-squares fit of `Q_{π_t}` in `Q_φ` with the on-policy weights `η_{π_t}`, `ỹ (t+1)`
is greedy with respect to `Q̂ t`, and `y (t+1) = α ỹ (t+1) + (1 − α) y t`.

**Formalization Note.** Policies are stacked vectors in `EuclideanSpace ℝ (S × A)`, read as tables
by the published `asPolicy`. `η_π` is the published `visitation π P γ ρ` (the discounted state
occupancy measure from the initial distribution `ρ`), `Q_π` is `QFunction`. The greedy policy
`π̃_{t+1}` is the indicator vector of a maximizing action at each state. Any element of the argmin
and any maximizing action is allowed. Iterations are indexed from `t = 1`; the values at `0` (and
`ỹ 1`) are unconstrained and never used. -/
def IsSoftAPIRun {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (ρ : S → ℝ) (φ : S → ι) (α : ℝ)
    (y₁ : EuclideanSpace ℝ (S × A)) (y yt : ℕ → EuclideanSpace ℝ (S × A))
    (Qhat : ℕ → S → A → ℝ) : Prop :=
  y 1 = y₁ ∧
    ∀ t : ℕ, 1 ≤ t →
      IsWLSFit (visitation (asPolicy (y t)) P γ ρ) φ (QFunction (asPolicy (y t)) P r γ) (Qhat t) ∧
      IsGreedy (Qhat t) (asPolicy (yt (t + 1))) ∧
      y (t + 1) = α • yt (t + 1) + (1 - α) • y t

end AggStatePG.Supplement


