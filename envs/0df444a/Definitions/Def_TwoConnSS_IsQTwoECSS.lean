-- Prove2me | Definitions.Def_TwoConnSS_IsQTwoECSS
-- name    : TwoConnSS_IsQTwoECSS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:44:50.472997+00:00
-- url     : https://prove2.me/theorems/a7c4d4c9-3623-4952-b984-58df6cd003e0
-- title:
--   2ECSS solutions of the contracted multigraph $G'$
-- statement:
--   Let $P$ be a family of disjoint vertex sets of $G$. The multigraph $G'$ is obtained by contracting each member of $P$ to one vertex, discarding loops, and keeping parallel edges with their original identities.
--
--   An edge set $F \subseteq E(G)$ is a **2ECSS of $G'$** if no edge of $F$ lies inside a member of $P$, the multigraph $(V(G'), F)$ is connected, and none of its edges is a bridge. $\mathrm{opt}_E(G')$ is the minimum size of such an $F$; when $G'$ has one vertex it is $0$.
--
--   **Formalization Note** $G'$ is not built as a type: connectivity and bridges of $(V(G'), F)$ are read in $G$ with free moves inside each member of $P$. Parallel edges of $G'$ are distinct edges of $G$, so two of them form a cycle.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.2.3, p.55

import Mathlib
import Definitions.Def_TwoConnSS_IsTwoECSS

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- The graph joining any two distinct vertices of a common member of `P`. -/
def withinParts (P : Finset (Finset V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ C ∈ P, u ∈ C ∧ v ∈ C
  symm := ⟨fun _ _ h => ⟨h.1.symm, let ⟨C, hC, hu, hv⟩ := h.2; ⟨C, hC, hv, hu⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **A 2ECSS of the contracted multigraph `G'`.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.2.3, p.55: "Contract each V(Ci)
to one vertex, discard loops, and retain parallel edges with their original edge identities. Denote
the resulting multigraph by G′. All vertices outside the contracted components remain as distinct
vertices of G′ … Let q′ := optE(G′); if G′ has one vertex, put q′ = 0."

`IsQTwoECSS G P F` (for the family `P` of contracted vertex sets) says: `F ⊆ E(G)`; no edge of `F`
has both ends in one member of `P` (loops are discarded); the multigraph `(V(G'), F)` is connected;
and no edge of `F` is a bridge of it.

**Formalization Note.** `G'` is never built as a type. A vertex of `G'` is a member of `P` or a
vertex outside `∪P`; an edge of `G'` is an edge of `G` not inside a member of `P`, with its own
identity, so parallel edges of `G'` are distinct elements of `F`. Connectivity and bridges of
`(V(G'), F)` are read in `(V, F)` with free moves inside each member of `P` (`withinParts P`).
When `G'` has one vertex, `F = ∅` is feasible, which is the paper's `q′ = 0`. -/
def IsQTwoECSS (G : SimpleGraph V) (P : Finset (Finset V)) (F : Finset (Sym2 V)) : Prop :=
  (F : Set (Sym2 V)) ⊆ G.edgeSet ∧ (∀ e ∈ F, ∀ C ∈ P, ¬ ∀ v ∈ e, v ∈ C) ∧
  (sg F ⊔ withinParts P).Connected ∧
  ∀ e ∈ F, ∀ u v : V, e = s(u, v) → (sg (F.erase e) ⊔ withinParts P).Reachable u v

end TwoConnSS


