-- Prove2me | Definitions.Def_VDCyclePack_IsCyclePacking
-- name    : VDCyclePack_IsCyclePacking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:23.765213+00:00
-- url     : https://prove2.me/theorems/48378a49-d521-4918-90f7-950678b1e214
-- title:
--   Cycle packing: a family of pairwise vertex-disjoint cycles
-- statement:
--   A **cycle packing** is a finite family $P$ of cycles of $G$ such that any two distinct members of $P$ have disjoint vertex sets. Its size is $|P|$, and $\nu(G)$ is the maximum size.
--
--   The marked packings of Sections 3 and 6 are unions of cycle packings, and Theorems 1.1, 4.2 and Lemma 4.3 output cycle packings.
--
--   **Formalization Note** A finite set of subgraphs, so its members are distinct.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.9

import Mathlib
import Definitions.Def_VDCyclePack_IsCycleSub

namespace VDCyclePack

/-- **Cycle packing: pairwise vertex-disjoint cycles.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.9: "A cycle packing is a family of pairwise vertex-disjoint cycles."

`IsCyclePacking P` says every member of the finite family `P` is a cycle and distinct members have
disjoint vertex sets. Its size is `P.card`.

**Formalization Note.** The family is a `Finset` of subgraphs, so its members are distinct. -/
def IsCyclePacking {V : Type*} {G : SimpleGraph V} (P : Finset G.Subgraph) : Prop :=
  (∀ C ∈ P, IsCycleSub C) ∧ (P : Set G.Subgraph).Pairwise fun C C' => Disjoint C.verts C'.verts

end VDCyclePack


