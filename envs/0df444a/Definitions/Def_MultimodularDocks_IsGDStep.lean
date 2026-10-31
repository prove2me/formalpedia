-- Prove2me | Definitions.Def_MultimodularDocks_IsGDStep
-- name    : MultimodularDocks_IsGDStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:56.086159+00:00
-- url     : https://prove2.me/theorems/eba36c2f-b7ac-4438-971e-0b10b00ddebb
-- title:
--   A gradient-descent step (Algorithm 2)
-- statement:
--   Given an allocation $a$, Algorithm 2 looks at the best allocation in the neighborhood $N(a)$. A **gradient-descent step** from $a$ to $a'$ is either
--
--   1. a move to a feasible neighbor $a'$ of $a$ that has the least objective among all feasible neighbors of $a$ and is strictly better than $a$; or
--   2. staying put, $a'=a$, when no feasible neighbor of $a$ has a smaller objective than $a$.
--
--   **Formalization Note** The page's arg min over $N(a)$ of an objective that is $+\infty$ off the band is the minimum over the feasible neighbors; ties among minimizers may be broken arbitrarily.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Algorithm 2, p.35

import Mathlib
import Definitions.Def_MultimodularDocks_Feasible
import Definitions.Def_MultimodularDocks_cost
import Definitions.Def_MultimodularDocks_Neighbor

namespace MultimodularDocks

/-- **A gradient-descent step** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, Algorithm 2,
p.35, with the neighborhood of Definition 3): either `a'` is a feasible neighbor of `a` that
minimizes the objective over the feasible neighbors and is strictly better than `a`
(line 3), or no feasible neighbor is strictly better than `a` and `a' = a` (line 5).

**Formalization Note** The page's `arg min` over `N(d⃗, b⃗)` of a cost that is `+∞` off the band
is the minimum over the feasible neighbors. The step is a relation, so every tie-breaking is
covered. -/
def IsGDStep {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S) (a a' : Alloc S) : Prop :=
  (Feasible I a' ∧ Neighbor a a' ∧
      (∀ n, Feasible I n → Neighbor a n → cost I a' ≤ cost I n) ∧ cost I a' < cost I a) ∨
    (a' = a ∧ ∀ n, Feasible I n → Neighbor a n → cost I a ≤ cost I n)

end MultimodularDocks


