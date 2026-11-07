-- Prove2me | Definitions.Def_VDCyclePack_cycles
-- name    : VDCyclePack_cycles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:31.232196+00:00
-- url     : https://prove2.me/theorems/220ffeae-da5c-457a-b19a-60ce104953fc
-- title:
--   The family $\mathcal C(G)$ of all cycles of $G$
-- statement:
--   For a finite simple graph $G$, $\mathcal C(G)$ is the family of all cycles of $G$ (each cycle taken once, as a subgraph).
--
--   It is the index set of the variables of the natural LP (1) and of the candidate family $\mathcal C(H,L,c)$.
--
--   **Formalization Note** A finite set of subgraphs of $G$; the vertex type is finite.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), (1), p.3

import Mathlib
import Definitions.Def_VDCyclePack_IsCycleSub

namespace VDCyclePack

open Classical in
/-- **The family 𝒞(G) of all cycles of `G`.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), (1), p.3: "Let C(G) be the family of all cycles in G."

`cycles G` is the finite set of subgraphs of `G` that are cycles (`IsCycleSub`).

**Formalization Note.** The vertex type is finite, so `G` has finitely many subgraphs; membership
is decided classically. -/
noncomputable def cycles {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset G.Subgraph :=
  Finset.univ.filter fun C => IsCycleSub C

end VDCyclePack


