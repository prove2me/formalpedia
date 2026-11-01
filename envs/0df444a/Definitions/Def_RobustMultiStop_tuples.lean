-- Prove2me | Definitions.Def_RobustMultiStop_tuples
-- name    : RobustMultiStop_tuples
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:51.69412+00:00
-- url     : https://prove2.me/theorems/59f57311-3846-4f07-b3ea-488fb50fa97a
-- title:
--   Exercise-date tuples $t\le j_1<\dots<j_L\le N$
-- statement:
--   For a horizon $N$, a start date $t$ and a number of rights $L$, the **exercise-date tuples** are the strictly increasing integer vectors
--
--   $$t\le j_1<j_2<\dots<j_L\le N .$$
--
--   They index the pathwise maximum in the dual representations (3.1)–(3.3). For $L\ge1$ there is such a tuple exactly when $t+L\le N+1$.
--
--   **Formalization Note** $0$-based vectors `Fin L → Fin (N + 1)`; for $L=0$ the only tuple is the empty one.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, index set of the maximum in (3.1)–(3.3), p.8

import Mathlib

namespace RobustMultiStop

/-- The exercise-date tuples `t ≤ j_1 < j_2 < ⋯ < j_L ≤ N`, Laeven, Schoenmakers, Schweizer &
Stadje, *Robust Multiple Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, the index set
of the maximum in (3.1)–(3.3), p.8.

`tuples N t L` is the finite set of strictly increasing `j : Fin L → Fin (N + 1)` with `t ≤ j k`
for all `k`.

**Formalization Note** `0`-based indexing: the paper's `j_k` is `j (k-1)`. Dates are bounded by the
exercise horizon `N`. For `L ≥ 1` the set is nonempty exactly when `t + L ≤ N + 1`; for `L = 0` it
consists of the empty tuple. -/
def tuples (N t L : ℕ) : Finset (Fin L → Fin (N + 1)) :=
  Finset.univ.filter (fun j => (∀ a b : Fin L, a < b → j a < j b) ∧ ∀ k, t ≤ (j k : ℕ))

end RobustMultiStop


