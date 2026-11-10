-- Prove2me | Definitions.Def_TwoConnSS_IsCanonA
-- name    : TwoConnSS_IsCanonA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:22.472088+00:00
-- url     : https://prove2.me/theorems/4fbafbc1-b202-4ead-a75e-95c04eed92a9
-- title:
--   Canonical weak 2-edge-covers for Algorithm A
-- statement:
--   Let $G$ be a graph, $S \subseteq E(G)$ and $M$ a set of edges of $G$. A **pairing** $M$ consists of pairwise disjoint pairs $\{u, v\}$ of isolated vertices of $S$ with $uv \in E(G)$ (the available edge, not in $S$). An isolated vertex in no pair is an **unpaired singleton**.
--
--   $(S, M)$ is a **canonical weak 2-edge-cover for Algorithm A** if $S$ is a weak 2-edge-cover, $M$ is a pairing, and every component of $S$ with at least two vertices is one of:
--
--   1. a cycle of length $4, 5, 6, 7$ or $8$;
--   2. a large 2EC component: a 2EC component that is not a cycle, or a cycle of length at least nine;
--   3. a complex component whose every 2EC block has at least five vertices.
--
--   This is the invariant maintained by every exchange of Algorithm A.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Definitions 8.5–8.6, pp.33–34

import Mathlib
import Definitions.Def_TwoConnSS_IsTwoEdgeCover

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- A family `M` of pairs of singletons (Definition 8.5, p.33): pairwise disjoint pairs `{u, v}` of
isolated vertices of `S` with `uv ∈ E(G)` (the available edge, not in `S`). -/
def IsPairing (G : SimpleGraph V) (S M : Finset (Sym2 V)) : Prop :=
  (M : Set (Sym2 V)) ⊆ G.edgeSet ∧ (∀ m ∈ M, ∀ v ∈ m, deg S v = 0) ∧
  ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → ∀ v ∈ m, v ∉ m'

/-- The unpaired singletons: isolated vertices of `S` in no pair of `M`. -/
noncomputable def unpaired (S M : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter fun v => deg S v = 0 ∧ ∀ m ∈ M, v ∉ m

/-- **Canonical weak 2-edge-cover for Algorithm A.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Definition 8.6, pp.33–34: "(S, M)
is a canonical weak 2-edge-cover for Algorithm A if S is a weak 2-edge-cover, M is a family of pairs
as in Definition 8.5, and each nontrivial connected component of S is one of the following: 1. a
cycle of length 4, 5, 6, 7, or 8; 2. a large 2EC component, meaning a non-cycle 2EC component or a
cycle of length at least nine; 3. a complex component whose every 2EC block has at least five
vertices."

Also defined here: pairings (`IsPairing`, Definition 8.5) and unpaired singletons (`unpaired`).

**Formalization Note.** A nontrivial component is one with at least two vertices. "Large 2EC" is a
2EC component that is not a cycle of length at most eight. -/
def IsCanonA (G : SimpleGraph V) (S M : Finset (Sym2 V)) : Prop :=
  IsWeakCover G S ∧ IsPairing G S M ∧
  ∀ C ∈ comps S, 2 ≤ C.card →
    (∃ t, 4 ≤ t ∧ t ≤ 8 ∧ IsCycleComp S C t) ∨
    (IsTwoECComp S C ∧ ¬ ∃ t, t ≤ 8 ∧ IsCycleComp S C t) ∨
    (IsComplexComp S C ∧ ∀ B ∈ blocksIn S C, 5 ≤ B.card)

end TwoConnSS


