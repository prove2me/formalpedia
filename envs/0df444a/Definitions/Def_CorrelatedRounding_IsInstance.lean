-- Prove2me | Definitions.Def_CorrelatedRounding_IsInstance
-- name    : CorrelatedRounding_IsInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:37.466916+00:00
-- url     : https://prove2.me/theorems/a5710cc7-fac1-4705-b48d-121c7b748ec2
-- title:
--   Instance of the rounding scheme problem
-- statement:
--   An instance consists of $q$ marginal distributions over $K$ fulfillment centres (FCs), given by numbers $u_{ki}\ge 0$ with
--   $$\sum_{k=1}^K u_{ki}=1\quad\text{for every item } i.$$
--   The number $u_{ki}$ is the probability with which item $i$ must be assigned to FC $k$. Every statement of the mission is quantified over such instances.
--
--   **Formalization Note.** FCs are `Fin K` and items are `Fin q`. Nonnegativity is written out because the page calls the $u_{ki}$ probabilities. A row of zeros, which is an FC with $y_k=0$, is allowed.
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, Definition 1, p.9

import Mathlib

namespace CorrelatedRounding

/-- **Instance of the rounding scheme problem.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4,
Definition 1, p.9: "q marginal distributions over K FC's, given by probabilities u_ki satisfying
∑_{k=1}^K u_ki = 1 for all i".

`u k i` is the probability that item `i` is assigned to fulfillment centre (FC) `k`.

**Formalization Note.** FCs are `Fin K` and items are `Fin q`, both 0-based. Nonnegativity is written
out because the page calls the `u_ki` probabilities. The number of items `q ≥ 1` is a hypothesis of each
theorem that needs it; with `q ≥ 1` the sum condition forces `K ≥ 1`, so no `NeZero K` is assumed. A row
of zeros (an FC with `y_k = 0`) is allowed; see `IsAlg1Draw`. -/
def IsInstance {q K : ℕ} (u : Fin K → Fin q → ℝ) : Prop :=
  (∀ k i, 0 ≤ u k i) ∧ ∀ i, ∑ k, u k i = 1

end CorrelatedRounding


