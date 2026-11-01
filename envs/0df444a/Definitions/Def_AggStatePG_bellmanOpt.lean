-- Prove2me | Definitions.Def_AggStatePG_bellmanOpt
-- name    : AggStatePG_bellmanOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:00.701482+00:00
-- url     : https://prove2.me/theorems/071ff2dd-b500-41a8-a5da-b2a1e2a5ec4b
-- title:
--   Bellman optimality operator $T$
-- statement:
--   For a finite MDP with rewards $r(s,a)$, transition probabilities $P(s'\mid s,a)$ and discount factor $\gamma$, the **Bellman optimality operator** is
--   $$TV(s)=\max_{d\in\Delta(\mathcal A)}\;r(s,d)+\gamma\sum_{s'\in\mathcal S}P(s'\mid s,d)\,V(s'),$$
--   with $r(s,d)=\sum_a r(s,a)d_a$ and $P(s'\mid s,d)=\sum_a P(s'\mid s,a)d_a$, and $\Delta(\mathcal A)$ the probability vectors on the action set. Its unique fixed point is the optimal value function $V^*$.
--
--   **Formalization Note** The maximum is written as a supremum (`sSup`) of the image of $\Delta(\mathcal A)$; for a nonempty finite action set the image is a nonempty compact set and the supremum is attained. For an empty action set the value is Lean's $\sup\emptyset=0$; the paper's MDP always has actions.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, §2, p.5 (definition of T)

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

open PolicyGradTheory.ProjGA

namespace AggStatePG

/-- The **Bellman optimality operator** `T` (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, §2, p.5):
`TV(s) = max_{d ∈ Δ(A)} r(s,d) + γ ∑_{s'} P(s'|s,d) V(s')`, with `r(s,d) = ∑_a r(s,a) d_a` and
`P(s'|s,d) = ∑_a P(s'|s,a) d_a` (p.4).

**Formalization Note.** `Δ(A)` is `{d : A → ℝ | IsDist d}` (nonnegative weights summing to one). The
maximum is written as `sSup` of the image of `Δ(A)`; for a nonempty finite `A` this image is a
nonempty compact subset of `ℝ`, so the supremum is attained and equals the paper's maximum. (For an
empty action type `Δ(A) = ∅` and the value is Lean's `sSup ∅ = 0`; the paper's MDP always has actions.) -/
noncomputable def bellmanOpt {S A : Type*} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (V : S → ℝ) (s : S) : ℝ :=
  sSup ((fun d : A → ℝ => ∑ a : A, d a * (r s a + γ * ∑ s' : S, P s a s' * V s')) ''
    {d : A → ℝ | IsDist d})

end AggStatePG


