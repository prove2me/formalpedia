-- Prove2me | Definitions.Def_RadioInitBits_collidingNodes
-- name    : RadioInitBits_collidingNodes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:11.663627+00:00
-- url     : https://prove2.me/theorems/044332a1-41db-4843-8749-20de51f313a6
-- title:
--   Collision events and colliding nodes (Definition 32)
-- statement:
--   List the $m$ nodes that participate in a phase as $v_1,\dots,v_m$, and let $x_j$ be the bin chosen by $v_j$.
--
--   1. The **collision event** $A_j$ of $v_j$ is the event that $v_j$ chooses the same bin as some earlier node $v_{j'}$, $j'<j$. Its indicator is $Y_j$.
--   2. The **number of collision events** is $X=\sum_j Y_j$.
--   3. The **number of colliding nodes** is the number of $j$ for which some other node $v_{j'}$, $j'\ne j$, chose the same bin $x_j$.
--
--   A bin with $k\ge2$ nodes contributes $k-1$ collision events and $k$ colliding nodes. So the number of colliding nodes is at most $2X$. Lemma 33 bounds the number of colliding nodes in a phase.
--
--   **Formalization Note** Nodes are indexed by `Fin m` (from $0$), in the same order.
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version Definition 32 and Lemma 33, p.29 (PDF p.50)

import Mathlib

set_option autoImplicit false

namespace RadioInitBits

/-- **Collision event** `A^i_j` (Definition 32). The participating nodes of a phase are listed
as `v_0, v_1, …, v_{m−1}`, and `x j` is the bin chosen by `v_j`. The collision event of `v_j` is
that `v_j` chooses the same bin as some `v_{j'}` with `j' < j`.
D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version Definition 32, p.29 (PDF p.50):
"Let Vi = {v1, v2, . . . , vFi−1n} be the set of uninitialized nodes participating in phase i. Then
the collision event A^i_j is the event that vj chooses the same bin as vj′ for some j′ < j in phase
i and Y^i_j is the corresponding indicator random variable."

**Formalization Note** Nodes are indexed from `0` (`Fin m`) instead of `1`; the order is the same. -/
def collisionEvent {m T : ℕ} (x : Fin m → Fin T) (j : Fin m) : Prop :=
  ∃ j' : Fin m, j' < j ∧ x j' = x j

/-- `X_i = ∑_j Y^i_j`, the number of collision events (proof of Lemma 33, p.29, PDF p.50). -/
noncomputable def numCollisionEvents {m T : ℕ} (x : Fin m → Fin T) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => collisionEvent x j).card

/-- The number of **colliding nodes**: the nodes that share their bin with at least one other
participating node (Lemma 33, p.29, PDF p.50: "the true number of uninitialized nodes that
collide"). -/
noncomputable def collidingNodes {m T : ℕ} (x : Fin m → Fin T) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => ∃ j' : Fin m, j' ≠ j ∧ x j' = x j).card

end RadioInitBits


