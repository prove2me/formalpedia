-- Prove2me | Definitions.Def_AggStatePG_Supplement_IsAPIRun
-- name    : AggStatePG_Supplement_IsAPIRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:22:34.603794+00:00
-- url     : https://prove2.me/theorems/50ebd367-44d1-554e-b338-78899baee643
-- title:
--   Algorithm 1 (approximate policy iteration with state aggregation)
-- statement:
--   **Algorithm 1 (API).** Input: state weights $w\in\Delta(\mathcal S)$, an initial policy $\pi_1\in\Pi$ and an aggregation $\phi$. For $t=1,2,\dots$:
--
--   1. (approximate policy evaluation) $\hat Q_t\in\arg\min_{\hat Q\in\mathcal Q_\phi}\|\hat Q-Q_{\pi_t}\|_{2,w\times1}$;
--   2. (policy improvement) $\pi_{t+1}(s)\in\arg\max_{a\in\mathcal A}\hat Q_t(s,a)$ for every $s$.
--
--   Here $Q_\pi(s,a)=r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V_\pi(s')$ is the state-action value function of $\pi$. A pair of sequences $(\pi_t,\hat Q_t)_{t\ge1}$ is a **run** of Algorithm 1 if $\pi_1$ is the input policy and both steps hold at every $t\ge1$.
--
--   This is the classical policy iteration algorithm with a regression-based policy evaluation step over the aggregated class $\mathcal Q_\phi$. Theorem 7 is a lower bound on its limiting per-period regret.
--
--   **Formalization Note** Policies are tables; iterations are indexed from $t=1$, and the entries at index $0$ are unconstrained and unused. Any element of each argmin and any maximizing action at each state is allowed, so the predicate describes every sequence the algorithm can generate.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, Algorithm 1, p.12

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_AggStatePG_Supplement_IsWLSFit
import Definitions.Def_AggStatePG_Supplement_IsGreedy

open FoundationsML.ReinforcementLearning

namespace AggStatePG.Supplement

/-- **Algorithm 1** (API, approximate policy iteration; Russo, *Approximation Benefits of Policy
Gradient Methods with Aggregated States*, arXiv:2007.11684v3, Algorithm 1, p.12).
Input `w ∈ Δ(S)`, `π_1 ∈ Π`, `φ`. For `t = 1, 2, …`:
(2) `Q̂_t ∈ argmin_{Q̂ ∈ Q_φ} ‖Q̂ − Q_{π_t}‖_{2,w×1}`;
(3) `π_{t+1}(s) ∈ argmax_{a ∈ A} Q̂_t(s,a)` for all `s`.
`IsAPIRun P r γ w φ π₁ π Q̂` says that the sequences `π, Q̂` are a run of Algorithm 1 with these
inputs: `π 1 = π₁` and, for every `t ≥ 1`, `Q̂ t` is a weighted least-squares fit of `Q_{π t}` in `Q_φ`
and `π (t+1)` is greedy with respect to `Q̂ t`.

**Formalization Note.** Iterations are indexed from `t = 1` as on the page; the values `π 0`, `Q̂ 0`
are unconstrained and never used. Policies are tables `S → A → ℝ`; `Q_π` is the published
`QFunction`. Any element of each argmin and any maximizing action at each state is allowed: the
predicate describes every sequence the algorithm can generate. -/
def IsAPIRun {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (w : S → ℝ) (φ : S → ι)
    (π₁ : S → A → ℝ) (π Qhat : ℕ → S → A → ℝ) : Prop :=
  π 1 = π₁ ∧
    ∀ t : ℕ, 1 ≤ t →
      IsWLSFit w φ (QFunction (π t) P r γ) (Qhat t) ∧ IsGreedy (Qhat t) (π (t + 1))

end AggStatePG.Supplement


