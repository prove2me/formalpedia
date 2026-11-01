-- Prove2me | Definitions.Def_SelfGuidedALP_MDP
-- name    : SelfGuidedALP_MDP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:41.249317+00:00
-- url     : https://prove2.me/theorems/267f4091-397f-4b60-92fa-444ed3d4999c
-- title:
--   Discounted-cost MDP $(\mathcal S,\mathcal A_s,c,P,\gamma)$ with compact state space
-- statement:
--   A **discounted-cost Markov decision process** with continuous state space consists of a nonempty compact state space $\mathcal S\subset\mathbb R^d$, a nonempty compact feasible action set $\mathcal A_s\subset\mathbb R^m$ for each $s\in\mathcal S$, an immediate cost $c(s,a)\in\mathbb R$, a transition distribution $P(\cdot\mid s,a)$ on $\mathcal S$ for each feasible pair, and a discount factor $\gamma\in[0,1)$.
--
--   This is the model in which all the linear programs of the mission are posed. It is independent of the random-basis layer.
--
--   **Formalization Note** Assumption 1 lets each $\mathcal A_s$ be compact or finite. A finite subset of $\mathbb R^m$ is compact, so one field covers both. $P(\cdot\mid s,a)$ is a probability measure concentrated on $\mathcal S$ for every feasible pair, and no regularity of $P$ or $c$ in $(s,a)$ is imposed: every use in the mission is at a fixed pair.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §2, pp.6–7, and Assumption 1, p.7

import Mathlib

open MeasureTheory

namespace SelfGuidedALP

/-- Discounted-cost Markov decision process with a compact state space
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §2, pp.6–7, Assumption 1, p.7).

`S` is the state space, `A s` the feasible action set at `s`, `c s a` the immediate cost,
`P s a` the next-state distribution `P(·|s,a)` and `γ ∈ [0,1)` the discount factor.

**Formalization Note.** States live in `ℝᵈ` and actions in `ℝᵐ`. Assumption 1 lets each `A s` be
compact or finite; a finite subset of `ℝᵐ` is compact, so both cases are one field. `P s a` is a
probability measure concentrated on `S` for every feasible pair. `P` and `c` carry no further
regularity: every use below is at a fixed pair `(s,a)`. -/
structure MDP (d m : ℕ) where
  /-- The state space `𝒮`. -/
  S : Set (EuclideanSpace ℝ (Fin d))
  /-- The feasible action sets `𝒜ₛ`. -/
  A : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin m))
  /-- The immediate cost `c(s,a)`. -/
  c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → ℝ
  /-- The transition distribution `P(·|s,a)`. -/
  P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → Measure (EuclideanSpace ℝ (Fin d))
  /-- The discount factor. -/
  γ : ℝ
  isCompact_S : IsCompact S
  nonempty_S : S.Nonempty
  isCompact_A : ∀ s ∈ S, IsCompact (A s)
  nonempty_A : ∀ s ∈ S, (A s).Nonempty
  isProbabilityMeasure_P : ∀ s ∈ S, ∀ a ∈ A s, IsProbabilityMeasure (P s a)
  P_S : ∀ s ∈ S, ∀ a ∈ A s, P s a S = 1
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

end SelfGuidedALP


