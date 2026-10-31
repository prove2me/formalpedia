-- Prove2me | Definitions.Def_MultimodularDocks_IsBikeOptimal
-- name    : MultimodularDocks_IsBikeOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:21.389911+00:00
-- url     : https://prove2.me/theorems/a0a343d2-9b78-4963-be79-5138fe9d7725
-- title:
--   Bike-optimal allocation (Definition 4)
-- statement:
--   A feasible allocation $(\vec d,\vec b)$ is **bike-optimal** if it minimizes the objective among the feasible allocations $(\vec d',\vec b')$ with the same number of docks at every station,
--
--   $$
--   d'_i+b'_i=d_i+b_i\ \text{ for all } i,\qquad |\vec b'|_1=B .
--   $$
--
--   In words: given the docks at each station, the bikes are placed optimally.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Definition 4, p.18

import Mathlib
import Definitions.Def_MultimodularDocks_Feasible
import Definitions.Def_MultimodularDocks_cost

namespace MultimodularDocks

/-- **Bike-optimality** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, Definition 4, p.18):
`a` is feasible and minimizes the objective among feasible allocations with the same number of
docks `d_i + b_i` at every station (and hence `|b⃗′|₁ = B`). -/
def IsBikeOptimal {S : Type*} [Fintype S] (I : Instance S) (a : Alloc S) : Prop :=
  Feasible I a ∧
    ∀ y, Feasible I y → (∀ i, dockCount y i = dockCount a i) → cost I a ≤ cost I y

end MultimodularDocks


