-- Prove2me | Definitions.Def_VDCyclePack_contacts
-- name    : VDCyclePack_contacts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:12.211586+00:00
-- url     : https://prove2.me/theorems/39d3122d-14c5-42a4-bf51-b875dc4a4c0b
-- title:
--   Number of contacts $c_H(C)=\kappa(C\cap H)$
-- statement:
--   Let $H$ be a marked packing and $C$ a cycle. A **contact** of $C$ with $H$ is a connected component of the intersection $C\cap H$, taken on vertices and on edges:
--   $$
--   c_H(C)=\kappa\bigl((V(C)\cap V(H),\ E(C)\cap E(H))\bigr).
--   $$
--   An isolated common vertex is one contact, a shared path is one contact whatever its length, and an edge of $C$ joining two marked vertices that is not an edge of $H$ does not join contacts.
--
--   The candidate family keeps cycles with few contacts; Lemmas 6.1 and 6.4 relate contacts to $A$-paths.
--
--   **Formalization Note** The number of connected components of the subgraph meet $C\sqcap H$; for an empty intersection it is $0$ ($\kappa(\emptyset)=0$).
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.10

import Mathlib

namespace VDCyclePack

/-- **Number of contacts c_H(C) of a cycle with a marked packing.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.10: "For a cycle C, a contact of C with H is a connected component of
C ∩ H. We write c_H(C) = κ(C ∩ H) = κ((V(C) ∩ A, E(C) ∩ E(H))) for its number of contacts." p.9:
"Unions and intersections of subgraphs are taken on both their vertex sets and their edge sets.
In particular, an intersection may contain isolated vertices."

`contacts H C` is the number of connected components of the subgraph `C ⊓ H` (vertex set
`V(C) ∩ V(H)`, edge set `E(C) ∩ E(H)`).

**Formalization Note.** The intersection is the subgraph meet, so a shared path is one contact,
an isolated common vertex is one contact, and an edge of `C` joining two marked vertices that is
not an edge of `H` does not join contacts. For an empty intersection the vertex type of the
component graph is empty and the count is `0` (κ(∅) = 0). -/
noncomputable def contacts {V : Type*} {G : SimpleGraph V} (H C : G.Subgraph) : ℕ :=
  Nat.card (C ⊓ H).coe.ConnectedComponent

end VDCyclePack


