-- Prove2me | Definitions.Def_PlanarDFVSKernel_dirFacesAt
-- name    : PlanarDFVSKernel_dirFacesAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:29.091399+00:00
-- url     : https://prove2.me/theorems/e68cb2c1-025c-49b3-9df8-296dd33d806e
-- title:
--   The number of directed faces at a vertex
-- statement:
--   A face of a plane digraph is **directed** if its boundary is a nonempty closed walk following the arc directions. For a vertex $v$, this counts the directed faces on whose boundary $v$ appears (Reduction Rule 4). The total number of directed faces $F$ is the number of published `circularFaces`.
--
--   **Formalization Note** A face orbit has all corners alternating exactly when its boundary walk traverses every arc in one direction; the published `circularFaces` (those with $a(f)=0$) are exactly these, since the number of non-alternating corners of a face is even.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §3, p.8 (PDF 9); Reduction Rule 4, p.11 (PDF 12)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **The number of directed faces on whose boundary `v` appears** (Sheng, Xiao, *A Polynomial
Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256
75cfca8f…), §3, p.8 (PDF 9): "A directed face is a face whose boundary is a nonempty closed walk
following the arc directions."; Reduction Rule 4, p.11 (PDF 12): "If a vertex v appears on the
boundaries of more than k(k + 2) directed faces").

Directed faces are the published `circularFaces E`: the dart orbits `f` with `a E f = 0`, i.e.
every corner of `f` is alternating (one arc end enters the corner's vertex and the next leaves it).
`v` appears on the boundary of `f` when some dart of `f` has origin `v`.

**Formalization Note** Along a face walk each non-alternating corner switches between traversing
arcs forwards and backwards, so their number is even; hence `a E f = consistentCount / 2 = 0`
exactly when every corner alternates, and then all arcs of the boundary walk are traversed in one
direction: the boundary is a closed walk following the arc directions (read in one of its two
directions). Conversely a directed face has only alternating corners. The total number of directed
faces `F` of the paper is `(circularFaces E).card`. -/
noncomputable def dirFacesAt {n m : ℕ} {G : Graph n m} (E : Drawing G) (v : Fin n) : ℕ := by
  classical exact ((circularFaces E).filter fun f => ∃ d ∈ f, origin G d = v).card

end PlanarDFVSKernel


