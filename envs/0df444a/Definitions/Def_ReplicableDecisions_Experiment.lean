-- Prove2me | Definitions.Def_ReplicableDecisions_Experiment
-- name    : ReplicableDecisions_Experiment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:23.563706+00:00
-- url     : https://prove2.me/theorems/ccf1eb97-1f95-4b07-a6ff-64307e047cd5
-- title:
--   Known finite experiments, product laws and finite probabilities
-- statement:
--   A **known finite experiment** is a family $\mathcal P=\{P_1,\dots,P_M\}$ of distinct probability distributions on a finite observation space $\mathcal Z$. For a model $P$, the product law on samples $x\in\mathcal Z^n$ is
--
--   $$
--   P^n(x)=\prod_{j} P(x_j).
--   $$
--
--   The probability of an event $s$ under a finite law $p$ is $\sum_{a\in s}p(a)$.
--
--   The experiment is the common input of every statement of the mission; it is known to the algorithm, and only the identity of the true model is unknown.
--
--   **Formalization Note** The family is an injective table `P : ι → Z → ℝ` of points of `stdSimplex ℝ Z` over a finite index type, and $M$ is the cardinality of the index type.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), §2 "Experiments and validity", p.8 (PDF p.10)

import Mathlib

namespace ReplicableDecisions

/-- **A known finite experiment.** Chen, *Replicable Decisions in Finite Experiments*, STOC 2027
submission (sha256 52d181db…), §2 "Experiments and validity", p.8 (PDF p.10): "Let
P = {P1, . . . , PM} be a known family of distinct distributions on a finite observation space Z."

**Formalization Note.** The family is the indexed table `P : ι → Z → ℝ` of probability vectors,
with `Function.Injective P` for "distinct"; `M = Fintype.card ι`, and models are referred to by
their index. `Z` lives in `Type` (the reused Bhattacharyya coefficient requires it), which loses no
finite observation space. -/
structure Experiment (ι : Type*) (Z : Type) [Fintype Z] where
  /-- The probability table of each model. -/
  P : ι → Z → ℝ
  /-- Each model is a probability vector on `Z`. -/
  mem_simplex : ∀ i, P i ∈ stdSimplex ℝ Z
  /-- The models are distinct. -/
  distinct : Function.Injective P

/-- **The product law** `Pⁿ(x) = ∏ⱼ P(xⱼ)` on samples `x : Fin n → Z`. Chen, STOC 2027 submission
(sha256 52d181db…), §2, p.8 (PDF p.10). -/
noncomputable def productLaw {Z : Type} (P : Z → ℝ) {n : ℕ} (x : Fin n → Z) : ℝ :=
  ∏ j, P (x j)

/-- **Probability of an event under a finite law:** `∑_{a ∈ s} p(a)`. Used for `Pr_{S∼Pⁿ}` and for
`Pr_{f∼µ}` (§2, pp.8–9).

**Formalization Note.** `Set.indicator` carries no decidability instance. -/
noncomputable def finProb {α : Type*} [Fintype α] (p : α → ℝ) (s : Set α) : ℝ :=
  ∑ a, s.indicator p a

end ReplicableDecisions


