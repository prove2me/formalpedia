-- Prove2me | Definitions.Def_AggStatePG_IsAggErrorBound
-- name    : AggStatePG_IsAggErrorBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:44:13.229972+00:00
-- url     : https://prove2.me/theorems/59f12e84-3a46-466d-9cb0-cc644b26d5ad
-- title:
--   Definition 2: bound on the inherent state aggregation error
-- statement:
--   **Definition 2 (Inherent state aggregation error).** $\epsilon_\phi\in\mathbb R$ is the smallest scalar satisfying
--   $$|Q_\pi(s,a)-Q_\pi(s',a)|\le\epsilon_\phi$$
--   for every $\pi\in\Pi_\phi$, $a\in\mathcal A$, and all $s,s'\in\mathcal S$ such that $\phi(s)=\phi(s')$.
--
--   This item is the predicate "$\varepsilon$ satisfies the inequality of Definition 2": $\varepsilon$ bounds the gap between the state-action values of two states of a common segment, uniformly over the aggregated policy class. $\epsilon_\phi$ is the least such $\varepsilon$; the bounds of Theorem 3 are stated in terms of it.
--
--   **Formalization Note** Theorems quantify over every $\varepsilon$ satisfying the predicate, which includes $\epsilon_\phi$. The set of such $\varepsilon$ is the half-line $[\epsilon_\phi,\infty)$.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, Definition 2, p.8

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
import Definitions.Def_AggStatePG_aggSet

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA

namespace AggStatePG

/-- **Definition 2** (Inherent state aggregation error; Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, Definition 2, p.8). `ϵ_φ ∈ ℝ` is
the smallest scalar satisfying `|Q_π(s,a) - Q_π(s',a)| ≤ ϵ_φ` for every `π ∈ Π_φ`, `a ∈ A`, and all
`s, s' ∈ S` such that `φ(s) = φ(s')`. `IsAggErrorBound P r γ φ ε` says that `ε` satisfies this
inequality, i.e. `ε` is an upper bound for the within-segment state-action value gaps over `Π_φ`.

**Formalization Note.** The predicate is the defining inequality of Definition 2; `ϵ_φ` is its least
solution. Theorems are stated for every `ε` with `IsAggErrorBound P r γ φ ε`, which includes `ε = ϵ_φ`
(the set of such `ε` is a closed half-line `[ϵ_φ, ∞)`: it is nonempty because `Q_π` is bounded over
`Π_φ`). Policies of `Π_φ` are stacked vectors (`aggSet φ`) read as tables through `asPolicy`. -/
def IsAggErrorBound {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (φ : S → ι) (ε : ℝ) : Prop :=
  ∀ x ∈ (aggSet φ : Set (EuclideanSpace ℝ (S × A))), ∀ (a : A) (s s' : S), φ s = φ s' →
    |QFunction (asPolicy x) P r γ s a - QFunction (asPolicy x) P r γ s' a| ≤ ε

end AggStatePG


