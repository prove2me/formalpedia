-- Prove2me | Definitions.Def_PConeEB_IsUniformHolderianEB
-- name    : PConeEB_IsUniformHolderianEB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:14.099453+00:00
-- url     : https://prove2.me/theorems/91e8075c-e44c-4b45-b7b7-7800c2055985
-- title:
--   Uniform Hölderian error bound with exponent $\gamma$
-- statement:
--   Let $C_1,C_2\subseteq\mathcal E$ be closed convex sets with $C_1\cap C_2\ne\emptyset$. They satisfy a **uniform Hölderian error bound with exponent** $\gamma\in(0,1]$ if for every bounded set $B\subset\mathcal E$ there is a constant $\kappa_B>0$ such that
--   $$
--   \operatorname{dist}(x,C_1\cap C_2)\le\kappa_B\max\{\operatorname{dist}(x,C_1),\operatorname{dist}(x,C_2)\}^\gamma\qquad\forall x\in B.
--   $$
--   If $\gamma=1$, the error bound is **Lipschitzian**.
--
--   The definition estimates the distance to an intersection through the distances to the two sets, and it is the target of every result in the mission.
--
--   **Formalization Note** The conditions $C_1\cap C_2\ne\emptyset$ and $\gamma\in(0,1]$ are conjuncts of the predicate. Closedness and convexity of $C_1,C_2$ are properties of the sets to which the predicate is applied.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Definition 2.1, p.3

import Mathlib

namespace PConeEB

/-- Definition 2.1 (Lipschitzian and Hölderian error bounds). The sets `C₁, C₂`, with
`C₁ ∩ C₂ ≠ ∅`, satisfy a uniform Hölderian error bound with exponent `γ ∈ (0, 1]` if for every
bounded set `B` there is `κ > 0` with
`dist(x, C₁ ∩ C₂) ≤ κ * max{dist(x, C₁), dist(x, C₂)} ^ γ` for all `x ∈ B`. The case `γ = 1` is a
Lipschitzian error bound. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Definition 2.1, p.3.

**Formalization Note.** `C₁ ∩ C₂ ≠ ∅` and `γ ∈ (0, 1]` are conjuncts, so that `Metric.infDist` is
never taken to the empty set and `rpow` never has exponent `0`. The constant `κ` depends on `B`.
The paper's closed convex `C₁, C₂` are hypotheses of the statements that use this predicate. -/
def IsUniformHolderianEB {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C₁ C₂ : Set E) (γ : ℝ) : Prop :=
  (C₁ ∩ C₂).Nonempty ∧ 0 < γ ∧ γ ≤ 1 ∧
    ∀ B : Set E, Bornology.IsBounded B → ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ B,
      Metric.infDist x (C₁ ∩ C₂) ≤
        κ * (max (Metric.infDist x C₁) (Metric.infDist x C₂)) ^ γ

end PConeEB


