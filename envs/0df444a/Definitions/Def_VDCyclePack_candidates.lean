-- Prove2me | Definitions.Def_VDCyclePack_candidates
-- name    : VDCyclePack_candidates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:24.355203+00:00
-- url     : https://prove2.me/theorems/aa73fc56-66ec-40e2-b0b7-c5b68e11b59a
-- title:
--   The candidate family $\mathcal C(H,L,c)$
-- statement:
--   For a marked packing $H$ and integers $L\ge 3$, $c\ge 1$,
--   $$
--   \mathcal C(H,L,c)=\{C\ :\ C \text{ a cycle of } G,\ |C|\le L,\ c_H(C)\le c\}.
--   $$
--
--   Lemma 4.3 shows that this family keeps most of the fractional weight and that unions of its members have small cycle rank, so that Theorem 4.2 applies.
--
--   **Formalization Note** The ranges $L\ge3$, $c\ge1$ are hypotheses of the theorems that use the family.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 4.3, p.13

import Mathlib
import Definitions.Def_VDCyclePack_cycles
import Definitions.Def_VDCyclePack_contacts

namespace VDCyclePack

open Classical in
/-- **The candidate family 𝒞(H, L, c).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 4.3, p.13: "For a marked packing H and integers L ≥ 3 and c ≥ 1, define the
candidate family by C(H, L, c) = {C : C is a cycle in G, |C| ≤ L, c_H(C) ≤ c}."

`candidates G H L c` is the set of cycles `C` of `G` with `|V(C)| ≤ L` and `contacts H C ≤ c`.

**Formalization Note.** The ranges `L ≥ 3`, `c ≥ 1` are hypotheses of the theorems that use this
family; `H` is a marked packing there. -/
noncomputable def candidates {V : Type*} [Fintype V] (G : SimpleGraph V) (H : G.Subgraph)
    (L c : ℕ) : Finset G.Subgraph :=
  (cycles G).filter fun C => C.verts.ncard ≤ L ∧ contacts H C ≤ c

end VDCyclePack


