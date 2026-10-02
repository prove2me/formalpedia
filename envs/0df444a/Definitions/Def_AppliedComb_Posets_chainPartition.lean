-- Prove2me | Definitions.Def_AppliedComb_Posets_chainPartition
-- name    : AppliedComb_Posets_chainPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:05:08.018+00:00
-- url     : https://prove2.me/theorems/9a740a6a-6a33-4f20-b473-048786caa89b
-- title:
--   Partitions of a poset into chains and into antichains (Section 6.3)
-- statement:
--   Let $\mathbf P = (X, P)$ be a partially ordered set, represented by a type $\alpha$ with a partial order, and let $k \ge 0$. A **chain partition** of $X$ into $k$ parts is a family of finite sets $C_1, \dots, C_k \subseteq X$ with
--   $$X = C_1 \cup C_2 \cup \cdots \cup C_k, \qquad C_i \cap C_j = \emptyset \ (i \ne j),$$
--   where each $C_i$ is a chain (any two distinct points of $C_i$ are comparable). An **antichain partition** into $k$ parts is defined the same way with each $A_i$ an antichain (any two distinct points of $A_i$ are incomparable).
--
--   These are the partitions counted in Dilworth's theorem (Theorem 6.17) and its dual (Theorem 6.18).
--
--   **Formalization Note.** The parts are indexed by `Fin k` (0-based) and are `Finset`s of `α`; the whole type `α` is the ground set, so "cover $X$" is `∀ x, ∃ i, x ∈ C i`. Empty parts are not excluded. For the statements of Theorems 6.17 and 6.18 this does not matter: a partition with an empty part yields one with fewer nonempty parts.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 122, Theorems 6.17 and 6.18 (partition into chains / antichains)

import Mathlib

namespace AppliedComb.Posets

/-- A partition of the ground set `X = α` into `k` chains `C i`, `i : Fin k`
(Keller & Trotter, p. 122, Theorem 6.17): every part is a chain, distinct parts are
disjoint, and every point lies in some part. Empty parts are not excluded. -/
def IsChainPartition {α : Type*} [PartialOrder α] {k : ℕ} (C : Fin k → Finset α) : Prop :=
  (∀ i, IsChain (· ≤ ·) (C i : Set α)) ∧
  (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
  (∀ x : α, ∃ i, x ∈ C i)

/-- A partition of the ground set `X = α` into `k` antichains `A i`, `i : Fin k`
(Keller & Trotter, p. 122, Theorem 6.18): every part is an antichain, distinct parts are
disjoint, and every point lies in some part. Empty parts are not excluded. -/
def IsAntichainPartition {α : Type*} [PartialOrder α] {k : ℕ} (A : Fin k → Finset α) : Prop :=
  (∀ i, IsAntichain (· ≤ ·) (A i : Set α)) ∧
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
  (∀ x : α, ∃ i, x ∈ A i)

end AppliedComb.Posets


