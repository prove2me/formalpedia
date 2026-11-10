-- Prove2me | Definitions.Def_TwoConnSS_IsCanonB
-- name    : TwoConnSS_IsCanonB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:40.203298+00:00
-- url     : https://prove2.me/theorems/171484e1-10d7-4eed-a18d-ffbdede71669
-- title:
--   Canonical 2-edge-covers for Algorithm B, and the phase conditions of its bridge covering
-- statement:
--   A set $S \subseteq E(G)$ is a **canonical 2-edge-cover for Algorithm B** if every vertex has degree at least two, some component has at least ten vertices, and every component is one of:
--
--   1. a 4-cycle or a 5-cycle;
--   2. a large 2EC component: a 2EC component that is not a cycle, or a cycle of length at least six;
--   3. a complex component whose every 2EC block has at least five vertices.
--
--   The predicate `BReady` records the two conditions of Algorithm B's bridge-covering phase: $S$ has no 5-cycle component, and every 4-cycle component has exactly one neighbouring component.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Definition 8.7, p.34; p.39

import Mathlib
import Definitions.Def_TwoConnSS_IsTwoEdgeCover

namespace TwoConnSS

variable {V : Type*} [Fintype V]

/-- **Canonical 2-edge-cover for Algorithm B.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Definition 8.7, p.34: "A spanning
subgraph S is a canonical 2-edge-cover for Algorithm B if it has minimum degree at least two, has a
connected component with at least ten vertices, and each connected component is one of the
following: 1. a 4-cycle or a 5-cycle; 2. a large 2EC component, meaning a non-cycle 2EC component
or a cycle of length at least six; 3. a complex component whose every 2EC block has at least five
vertices."

**Formalization Note.** `S ⊆ E(G)`. "Large 2EC" is a 2EC component that is not a cycle of length
at most five. -/
def IsCanonB (G : SimpleGraph V) (S : Finset (Sym2 V)) : Prop :=
  IsTwoEdgeCover G S ∧ (∃ C ∈ comps S, 10 ≤ C.card) ∧
  ∀ C ∈ comps S, IsCycleComp S C 4 ∨ IsCycleComp S C 5 ∨
    (IsTwoECComp S C ∧ ¬ ∃ t, t ≤ 5 ∧ IsCycleComp S C t) ∨
    (IsComplexComp S C ∧ ∀ B ∈ blocksIn S C, 5 ≤ B.card)

/-- **The phase conditions of Algorithm B's bridge covering** (p.39: "the absence of 5-cycle
components and the unique-neighbor condition on 4-cycles are assumptions of Algorithm B's
bridge-covering phase"): no 5-cycle component, and every 4-cycle component has exactly one
neighbouring component. -/
def BReady (G : SimpleGraph V) (S : Finset (Sym2 V)) : Prop :=
  (∀ C, ¬ IsCycleComp S C 5) ∧ ∀ C, IsCycleComp S C 4 → (nbrComps G S C).card = 1

end TwoConnSS


