-- Prove2me | Definitions.Def_ClawFreeChoosable_IsAtom
-- name    : ClawFreeChoosable_IsAtom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:38.148981+00:00
-- url     : https://prove2.me/theorems/77142d2d-e8d1-4760-8c0a-7727d47293b2
-- title:
--   Clique cutset and atom
-- statement:
--   Let $G$ be a graph.
--
--   1. A **clique cutset** of $G$ is a clique $D$ whose deletion disconnects the graph: $V(G) \setminus D$ can be partitioned into two nonempty sets $A, B$ with no edge between $A$ and $B$.
--   2. An **atom** is a connected graph without a clique cutset. A connected graph is nonempty.
--
--   Atoms are the pieces of the clique-cutset decomposition; Chvátal and Sbihi described the claw-free perfect atoms.
--
--   **Formalization Note** The paper speaks of clique cutsets of connected graphs; every use in this mission states the connectivity separately. "Deletion disconnects" is encoded by the two nonempty anticomplete sides rather than by non-connectivity of $G - D$, because Lean's notion of connectedness is false for the empty graph, which would make the whole vertex set of a complete graph a clique cutset.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §1 p.1, "clique cutset", "atom"; partition form spelled out in §12.1 p.32

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsAnticomplete

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Clique cutset** (arXiv:2611.01068v1, §1 p.1; spelled out in §12.1 p.32): a clique `D` of
`G` whose deletion disconnects the graph, i.e. `V(G) \ D` is partitioned into two nonempty
anticomplete sets `A, B`.

**Formalization Note.** The paper speaks of clique cutsets of connected graphs only; every use
in this mission carries the connectivity of `G` separately. "Deletion disconnects" is encoded by
the two nonempty anticomplete sides, never as `¬ (G − D).Connected`, which would also hold when
`D = V(G)` because Mathlib's `Connected` is false on the empty graph. -/
def IsCliqueCutset {V : Type} (G : SimpleGraph V) (D : Set V) : Prop :=
  G.IsClique D ∧ ∃ A B : Set V, Disjoint A B ∧ A ∪ B = Dᶜ ∧ A.Nonempty ∧ B.Nonempty ∧
    IsAnticomplete G A B

/-- **Atom** (arXiv:2611.01068v1, §1 p.1): a connected graph without a clique cutset.
Mathlib's `Connected` includes nonemptiness, so an atom is nonempty. -/
def IsAtom {V : Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ¬ ∃ D : Set V, IsCliqueCutset G D

end ClawFreeChoosable


