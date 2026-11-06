-- Prove2me | Definitions.Def_FlexibleNRM_Feasible
-- name    : FlexibleNRM_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:24:37.721748+00:00
-- url     : https://prove2.me/theorems/b80d2af5-2dd2-4d8a-b7df-3aee76c5c9bb
-- title:
--   Feasible route assignments $\mathcal F(x)$, Eq. (1)
-- statement:
--   Let $x\in\mathbb Z_+^{|\mathcal J|}$, where $x_j$ counts the customers with a purchase of product $j$. A **feasible route assignment** is a vector $y$ of nonnegative integers, with $y_{jp}$ the number of those customers assigned to route $p\in\mathcal R_j$, such that
--   $$\sum_{p\in\mathcal R_j}y_{jp}=x_j\quad\forall j,\qquad \sum_{j\in\mathcal J}\sum_{p\in\mathcal R_j}a_{ip}\,y_{jp}\le c_i\quad\forall i.$$
--   The set of these is $\mathcal F(x)$. The state $x$ is **feasible** if $\mathcal F(x)\ne\emptyset$.
--
--   Routes are assigned at the end of the selling horizon, so the seller only has to keep $\mathcal F(x)$ nonempty along the way.
--
--   **Formalization Note** `y` is a total function, and its values at $p\notin\mathcal R_j$ play no role.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Eq. (1), p.7

import Mathlib
import Definitions.Def_FlexibleNRM_Network

namespace FlexibleNRM

/-- The set `F(x)` of feasible route assignments of the purchase vector `x`, Eq. (1):
`y ∈ Z₊` with `∑_{p ∈ R_j} y_jp = x_j` for all `j` and `∑_j ∑_{p ∈ R_j} a_ip y_jp ≤ c_i` for
all `i`.

Zhu, Topaloglu, manuscript of November 16, 2022, Eq. (1), p.7.

**Formalization Note** `y` is a total function on `Fin n × Fin r`. The constraints read `y j p` only
at `p ∈ R j`, so its values elsewhere play no role. -/
def routeAssignments {n m r : ℕ} (N : Network n m r) (x : Fin n → ℕ) :
    Set (Fin n → Fin r → ℕ) :=
  {y | (∀ j, ∑ p ∈ N.R j, y j p = x j) ∧
    ∀ i, ∑ j, ∑ p ∈ N.R j, N.a i p * y j p ≤ N.c i}

/-- `F(x) ≠ ∅`: the purchases `x` admit a feasible route assignment (p.7). -/
def Feasible {n m r : ℕ} (N : Network n m r) (x : Fin n → ℕ) : Prop :=
  (routeAssignments N x).Nonempty

end FlexibleNRM


