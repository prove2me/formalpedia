-- Prove2me | Definitions.Def_TwoConnSS_IsShortcutPair
-- name    : TwoConnSS_IsShortcutPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:44:03.909435+00:00
-- url     : https://prove2.me/theorems/8ce539cb-de8d-4139-9e04-2413e081a8a1
-- title:
--   Shortcut pairs of a cycle component
-- statement:
--   Let $D$ be a cycle component of $S$. A **shortcut pair** of $D$ is a pair of distinct vertices $x, y \in V(D)$ such that $G[V(D)]$ contains a path from $x$ to $y$ through all vertices of $D$ whose first and last edges belong to $E(D)$.
--
--   Replacing a cycle by such a path saves one edge when the cycle is reconnected through $x$ and $y$.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Definition 6.6, p.25

import Mathlib

namespace TwoConnSS

variable {V : Type*}

/-- **Shortcut pair of a cycle component.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Definition 6.6, p.25: "Let D be a
cycle component of S. A shortcut pair of D is a pair of distinct vertices x, y ∈ V(D) for which
G[V(D)] contains a spanning x–y path whose first and last edges belong to E(D)."

**Formalization Note.** `D` is the vertex set of the cycle component; a path of `G` whose vertex set
is exactly `D` is a spanning path of `G[V(D)]`, and its first and last edges lie in `E(D)` iff they
lie in `S`. -/
def IsShortcutPair (G : SimpleGraph V) (S : Finset (Sym2 V)) (D : Finset V) (x y : V) : Prop :=
  x ≠ y ∧ x ∈ D ∧ y ∈ D ∧
  ∃ p : G.Walk x y, p.IsPath ∧ (∀ v, v ∈ p.support ↔ v ∈ D) ∧
    (∀ e ∈ p.edges.head?, e ∈ S) ∧ (∀ e ∈ p.edges.getLast?, e ∈ S)

end TwoConnSS


