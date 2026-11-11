-- Prove2me | Definitions.Def_PlanarDFVSKernel_IsDirectedCut
-- name    : PlanarDFVSKernel_IsDirectedCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:40.139194+00:00
-- url     : https://prove2.me/theorems/4ee9b8e5-7fb4-4d0d-ab48-ac93ce0ad139
-- title:
--   Directed cuts
-- statement:
--   For a nonempty proper vertex set $U$ of a digraph, the arcs with exactly one endpoint in $U$ form a **cut**. It is a **directed cut** if it is nonempty and all its arcs point in the same direction. An arc set **meets** a directed cut if it contains one of its arcs.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §2.3, p.7–8 (PDF 8–9)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **A directed cut** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*,
arXiv:2609.23669 (held version, sha256 75cfca8f…), §2.3, p.7 (PDF 8)): "For a nonempty proper
vertex set U in a digraph J, the arcs with exactly one endpoint in U form a cut. It is a directed cut
if it is nonempty and all its arcs point in the same direction."

`IsDirectedCut G C` holds when the arc set `C` is the set of arcs with exactly one endpoint in some
nonempty proper vertex set `U`, `C` is nonempty, and either every arc of `C` leaves `U` or every arc
of `C` enters `U`.

**Formalization Note** Arcs are arc identities, so parallel arcs are distinct members of a cut;
loops never belong to a cut. -/
def IsDirectedCut {n m : ℕ} (G : Graph n m) (C : Finset (Fin m)) : Prop :=
  ∃ U : Finset (Fin n), U.Nonempty ∧ U ≠ Finset.univ ∧
    (∀ e, e ∈ C ↔ Xor (G.tail e ∈ U) (G.head e ∈ U)) ∧ C.Nonempty ∧
    ((∀ e ∈ C, G.tail e ∈ U) ∨ (∀ e ∈ C, G.head e ∈ U))

/-- An arc set **meets** a directed cut if it contains an arc of that cut (ibid., p.8 (PDF 9)).
`MeetsAllDicuts G A`: `A` meets every directed cut of `G`. -/
def MeetsAllDicuts {n m : ℕ} (G : Graph n m) (A : Finset (Fin m)) : Prop :=
  ∀ C, IsDirectedCut G C → (A ∩ C).Nonempty

end PlanarDFVSKernel


