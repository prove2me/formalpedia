-- Prove2me | Definitions.Def_ClawFreeChoosable_IsIntervalType
-- name    : ClawFreeChoosable_IsIntervalType
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:12.046192+00:00
-- url     : https://prove2.me/theorems/174164ea-21af-4485-9d83-2b0520de9a3f
-- title:
--   Graph of interval type
-- statement:
--   A graph $G$ is **of interval type** if its vertex set has an ordered partition into nonempty cliques $C_1, \dots, C_m$, called fibres, such that
--
--   1. (I1) if $u \in C_i$, $v \in C_j$, $w \in C_\ell$ with $i < j < \ell$ and $uw \in E(G)$, then $uv, vw \in E(G)$;
--   2. (I2) each fibre forms an incomplete pair (neither complete nor anticomplete) with at most one other fibre, its incomplete partner.
--
--   $m = 0$ is allowed for the empty graph.
--
--   Graphs of interval type are one outcome of the Chudnovsky–Seymour theorem on rich clique cutsets; they satisfy the precolouring-extension property (Theorem 11.10).
--
--   **Formalization Note** The fibres are indexed by $\{0, \dots, m-1\}$ in their order; (I2) is stated as: two fibres other than $C_i$ that both form an incomplete pair with $C_i$ coincide.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Definition 11.1, p.24

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsAnticomplete

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Graph of interval type** (arXiv:2611.01068v1, Definition 11.1, p.24): the vertex set has an
ordered partition into nonempty cliques `C₁, …, C_m` (the fibers) such that
* (I1) if `u ∈ Cᵢ`, `v ∈ Cⱼ`, `w ∈ C_ℓ` with `i < j < ℓ` and `uw ∈ E(G)`, then `uv, vw ∈ E(G)`;
* (I2) each fiber forms an incomplete pair (neither complete nor anticomplete) with at most one
  other fiber.
`m = 0` is allowed for the empty graph.

**Formalization Note.** The fibers are `C : Fin m → Set V`, ordered by the index; "partition"
is pairwise disjointness plus covering. (I2) says: two fibers `Cⱼ, Cⱼ'` other than `Cᵢ` that
both form an incomplete pair with `Cᵢ` are the same fiber. -/
def IsIntervalType {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (m : ℕ) (C : Fin m → Set V),
    (∀ i, (C i).Nonempty) ∧ (∀ i, G.IsClique (C i)) ∧
    (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧ (∀ v : V, ∃ i, v ∈ C i) ∧
    (∀ i j l : Fin m, i < j → j < l → ∀ u ∈ C i, ∀ v ∈ C j, ∀ w ∈ C l,
      G.Adj u w → G.Adj u v ∧ G.Adj v w) ∧
    (∀ i j j' : Fin m, j ≠ i → j' ≠ i → IsIncompletePair G (C i) (C j) →
      IsIncompletePair G (C i) (C j') → j = j')

end ClawFreeChoosable


