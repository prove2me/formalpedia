-- Prove2me | Definitions.Def_PlanarDFVSKernel_rotationCode
-- name    : PlanarDFVSKernel_rotationCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:35:07.79622+00:00
-- url     : https://prove2.me/theorems/873df79c-dc25-47cd-b841-3ba30ee9613e
-- title:
--   A plane embedding as data: the rotation code of a drawing
-- statement:
--   For a crossing-free drawing of a digraph with $m$ arcs, the **rotation code** is the list of length $2m$ giving, for each arc end, the number of the next arc end counterclockwise around the same vertex. It records the cyclic order of arcs around every vertex, i.e. the combinatorial plane embedding.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §2.2, p.7 (PDF 8); Theorem 6.3, p.29 (PDF 30)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- The number of a dart: `(e, false) ↦ 2e`, `(e, true) ↦ 2e + 1`. -/
def dartCode {m : ℕ} (d : Dart m) : ℕ := 2 * (d.1 : ℕ) + if d.2 then 1 else 0

/-- **A plane embedding as output data: the rotation code of a drawing** (Sheng, Xiao, *A
Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256
75cfca8f…), §2.2, p.7 (PDF 8): "We […] keep it fixed when discussing faces and the cyclic order of
arcs around vertices"; Theorem 6.3, p.29 (PDF 30): "together with a plane embedding").

The list of length `2m` whose entries are, for `e = 0, …, m − 1`, the numbers of the
counterclockwise successors `E.rot (e, false)` and `E.rot (e, true)` of the two ends of `e`. It
records the cyclic order of arc ends around every vertex of the drawing `E`, i.e. the combinatorial
plane embedding.

**Formalization Note** A list `rot` "is a plane embedding of `G`" when `rot = rotationCode E` for
some actual crossing-free drawing `E : Drawing G` (published). -/
def rotationCode {n m : ℕ} {G : Graph n m} (E : Drawing G) : List ℕ :=
  (List.finRange m).flatMap fun e => [dartCode (E.rot (e, false)), dartCode (E.rot (e, true))]

end PlanarDFVSKernel


