-- Prove2me | Definitions.Def_MethodFulfillment_IsPolicy
-- name    : MethodFulfillment_IsPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:54.500338+00:00
-- url     : https://prove2.me/theorems/e19cf79e-394a-4ec2-80bc-d7f6747ab152
-- title:
--   Method-acceptance strategy (step 2 of Algorithm 1)
-- statement:
--   A **method-acceptance strategy** is a family of probability distributions, one for each period $t$, history, arriving order and drawn method $m$, over the set $A$ of pairs made available; the order is then served by $m\cap A$. Accepting $m$ is choosing some $A\supseteq m$, and rejecting it in favour of a submethod $\tilde m\subsetneq m$ is choosing $A=\tilde m$, so every rule of step 2 of Algorithm 1 has this form. The strategy is **non-anticipating**: the distribution in period $t$ depends on the run only through the periods before $t$, i.e. on the history $h_t$ of Definition 3, together with the arriving order and the drawn method.
--
--   **Formalization Note** A randomized strategy is represented by its behaviour kernel. The run records every past decision, so this loses no strategy. Feasibility with respect to the inventory is not part of the definition.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Algorithm 1, p.13; Definition 3, p.14

import Mathlib
import Definitions.Def_MethodFulfillment_Run

namespace MethodFulfillment

/-- A (possibly randomized) method-acceptance strategy for step 2 of Algorithm 1 (Amil, Makhdoumi
& Wei, manuscript, PDF sha256 197c13b9…, Algorithm 1, p.13, and Definition 3, p.14).
`σ t r a m A` is the probability that, at Lean time `t`, given the run `r`, the arriving order
`a` and the drawn method `m`, the strategy makes exactly the pairs in `A` available (so it uses
`m ∩ A`). It is a probability distribution over `A`, and it is **non-anticipating**: it depends on
the run only through the periods before `t` (the history `h_t` of Definition 3).

**Formalization Note.** Choosing to accept `m` is choosing some `A ⊇ m`; rejecting it in favour of
a submethod `m̃ ⊊ m` is choosing `A = m̃`; so every rule of Algorithm 1's step 2 is of this form.
The strategy may use the history, the arriving order type and the drawn method, which is what
`π_t(h_t, m)` of Definition 3 sees (a method determines its order type in the paper). A
randomized strategy is represented by its behaviour kernel; the run records every past decision,
so this loses no strategy's law. Feasibility of the inventory is not part of this definition. -/
structure IsPolicy {I K Q : Type} [Fintype I] [Fintype K] {T : ℕ}
    (σ : Fin T → Run I K Q T → Option Q → Finset (I × K) → Finset (I × K) → ℝ) : Prop where
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ t r a m A, 0 ≤ σ t r a m A
  /-- Probabilities sum to one over the available set. -/
  sum_one : ∀ t r a m, ∑ A, σ t r a m A = 1
  /-- The decision at `t` depends on the run only through the periods before `t`. -/
  nonanticipating : ∀ t (r r' : Run I K Q T), (∀ s, s < t → r s = r' s) → σ t r = σ t r'

end MethodFulfillment


