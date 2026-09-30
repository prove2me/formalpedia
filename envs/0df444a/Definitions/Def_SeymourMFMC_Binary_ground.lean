-- Prove2me | Definitions.Def_SeymourMFMC_Binary_ground
-- name    : SeymourMFMC_Binary_ground
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T00:39:47.383669+00:00
-- url     : https://prove2.me/theorems/c00e4920-da8e-47ec-97ce-18137927339b
-- title:
--   E(L): the ground set of a clutter, the union of its members
-- statement:
--   Let $\mathbf L$ be a finite collection of finite subsets of a set $\alpha$. Its **ground set** is the union of its members,
--
--   $$
--   E(\mathbf L) = \bigcup_{A \in \mathbf L} A .
--   $$
--
--   In particular $E(\emptyset) = \emptyset$ and $E(\{\emptyset\}) = \emptyset$. Every other notion of the mission (blocker, weights, criticality) lives on $E(\mathbf L)$.
--
--   **Formalization Note** A clutter is a `Finset (Finset α)` over a type `α` with decidable equality; $E(\mathbf L)$ is the finite supremum `L.sup id`.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 192, Section 1

import Mathlib

namespace SeymourMFMC.Binary

/-- `ground L` is the ground set `E(L) = ⋃ (A ∈ L)` of a finite family `L` of finite sets
(Seymour 1977, p. 192): the union of its members. `ground ∅ = ∅` and `ground {∅} = ∅`. -/
def ground {α : Type*} [DecidableEq α] (L : Finset (Finset α)) : Finset α :=
  L.sup id

end SeymourMFMC.Binary


