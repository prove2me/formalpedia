-- Prove2me | Definitions.Def_VDCyclePack_nbhd
-- name    : VDCyclePack_nbhd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:12.155064+00:00
-- url     : https://prove2.me/theorems/3f490081-775d-40ff-a154-afe21621daa3
-- title:
--   $N_R[C]$: the members of $R$ meeting $C$
-- statement:
--   For a family $R$ of cycles and a cycle $C$,
--   $$
--   N_R[C]=\{C'\in R\ :\ V(C)\cap V(C')\neq\emptyset\}.
--   $$
--   For $C\in R$ it contains $C$ itself. These are the cycles discarded when the greedy rounding selects $C$.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 5, p.14

import Mathlib

namespace VDCyclePack

open Classical in
/-- **N_R[C]: the members of R meeting C.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 5, p.14: "For a remaining family R ⊆ S and a cycle C ∈ R, define
N_R[C] = {C′ ∈ R : V(C) ∩ V(C′) ≠ ∅} ... The family N_R[C] includes C itself."

`nbhd R C` is the set of members of `R` sharing a vertex with `C`.

**Formalization Note.** For a cycle `C ∈ R` (nonempty vertex set) `C` itself belongs to it. -/
noncomputable def nbhd {V : Type*} {G : SimpleGraph V} (R : Finset G.Subgraph) (C : G.Subgraph) :
    Finset G.Subgraph :=
  R.filter fun C' => (C.verts ∩ C'.verts).Nonempty

end VDCyclePack


