-- Prove2me | Definitions.Def_AggStatePG_bellmanPol
-- name    : AggStatePG_bellmanPol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:55.089203+00:00
-- url     : https://prove2.me/theorems/7ef62edf-9f1a-47ca-86a0-d93887d4c798
-- title:
--   Bellman operator $T_\pi$ of a policy
-- statement:
--   For a policy $\pi$ of a finite MDP with rewards $r(s,a)$, transition probabilities $P(s'\mid s,a)$ and discount factor $\gamma$, the **Bellman operator** $T_\pi:\mathbb R^{\mathcal S}\to\mathbb R^{\mathcal S}$ maps a value function $V$ to
--   $$(T_\pi V)(s)=r(s,\pi(s))+\gamma\sum_{s'\in\mathcal S}P(s'\mid s,\pi(s))\,V(s'),$$
--   where for a randomized policy $r(s,\pi(s))=\sum_a\pi(s,a)r(s,a)$ and $P(s'\mid s,\pi(s))=\sum_a\pi(s,a)P(s'\mid s,a)$.
--
--   Its unique fixed point is $V_\pi$; it appears in Lemma 6 and in the relations (1) between $Q$ functions and Bellman operators.
--
--   **Formalization Note** A policy is a table $\pi(s,a)$; the operator is written with the published `InducedReward` and `InducedTransition`.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, §2, p.5 (definition of T_π); notation r(s,d), P(s'|s,d) p.4

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition

open FoundationsML.ReinforcementLearning

namespace AggStatePG

/-- The **Bellman operator of a policy** `T_π` (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, §2, p.5):
`(T_π V)(s) = r(s, π(s)) + γ ∑_{s'} P(s'|s, π(s)) V(s')`, where for a randomized policy
`r(s, π(s)) = ∑_a π(s,a) r(s,a)` and `P(s'|s, π(s)) = ∑_a π(s,a) P(s'|s,a)` (p.4).

**Formalization Note.** A policy is a table `π : S → A → ℝ` (`π s a = π(s,a)`); `P s a s'` is
`P(s'|s,a)`; value functions are `V : S → ℝ`. The operator is defined for every table; the paper
applies it to policies `π ∈ Π`. -/
noncomputable def bellmanPol {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (V : S → ℝ) (s : S) : ℝ :=
  InducedReward π r s + γ * ∑ s' : S, InducedTransition π P s s' * V s'

end AggStatePG


