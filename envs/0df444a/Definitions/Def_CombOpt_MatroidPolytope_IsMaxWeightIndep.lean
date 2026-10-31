-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_IsMaxWeightIndep
-- name    : CombOpt_MatroidPolytope_IsMaxWeightIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:37.355083+00:00
-- url     : https://prove2.me/theorems/437bcbdd-a2e3-4e83-b7b1-7162ae546a4c
-- title:
--   Maximum-weight independent set
-- statement:
--   Let $\mathcal I$ be a family of subsets of $S$ and $c\in\mathbb R^S$. A set $J$ is a **maximum-weight independent set** (an optimal independent set) with respect to $c$ if $J\in\mathcal I$ and $c(J)\ge c(J')$ for every $J'\in\mathcal I$.
--
--   Weights may be negative; then a maximum-weight independent set avoids negative elements.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, pp. 273–276 (PDF pp. 280–283)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_weight

namespace CombOpt.MatroidPolytope

/-- **Maximum-weight independent set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, pp. 273–276 (PDF pp. 280–283): an independent set `J` is a *maximum-weight*
(optimal) independent set with respect to `c ∈ ℝ^S` if `c(J) ≥ c(J')` for every independent
set `J'`.

**Formalization Note.** Weights are arbitrary reals (negative weights allowed), as in the book's
`c ∈ ℝ^S`. -/
def IsMaxWeightIndep {α : Type*} (I : Finset α → Prop) (c : α → ℝ) (J : Finset α) : Prop :=
  I J ∧ ∀ J' : Finset α, I J' → weight c J' ≤ weight c J

end CombOpt.MatroidPolytope


