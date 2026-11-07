-- Prove2me | Definitions.Def_VDCyclePack_HasDisjointAPaths
-- name    : VDCyclePack_HasDisjointAPaths
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:09.506298+00:00
-- url     : https://prove2.me/theorems/5dd39420-55b4-4996-800e-62528997c2eb
-- title:
--   $F$ contains $M$ vertex-disjoint $A$-paths
-- statement:
--   $F$ **contains $M$ vertex-disjoint $A$-paths** if there are $A$-paths $P_1,\dots,P_M$ of $F$ whose vertex sets, ends included, are pairwise disjoint.
--
--   This is the first alternative of Gallai's theorem (Lemma 3.1) and the hypothesis of Proposition 6.3.
--
--   **Formalization Note** The paths are indexed by $\{0,\dots,M-1\}$; disjoint vertex lists make them distinct.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.10

import Mathlib
import Definitions.Def_VDCyclePack_IsAPath

namespace VDCyclePack

/-- **F contains M vertex-disjoint A-paths.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.10: "When we speak of disjoint A-paths, they are vertex-disjoint
including their ends."

`HasDisjointAPaths F A M` says there are `M` A-paths in `F` whose vertex lists (ends included) are
pairwise disjoint.

**Formalization Note.** The paths are indexed by `Fin M`; disjointness of the supports makes them
distinct. -/
def HasDisjointAPaths {V : Type*} (F : SimpleGraph V) (A : Set V) (M : ℕ) : Prop :=
  ∃ (u v : Fin M → V) (p : ∀ i, F.Walk (u i) (v i)), (∀ i, IsAPath F A (p i)) ∧
    ∀ i j, i ≠ j → List.Disjoint (p i).support (p j).support

end VDCyclePack


