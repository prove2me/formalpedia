-- Prove2me | Definitions.Def_PlanarDFVSKernel_DirTree
-- name    : PlanarDFVSKernel_DirTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:23.981579+00:00
-- url     : https://prove2.me/theorems/08fe0470-0b76-450d-a02c-e06e2da6e0e2
-- title:
--   Directed trees and the side $C_e$ of a tree edge
-- statement:
--   A **directed tree** is a tree (a connected undirected graph without cycles) each of whose edges is oriented in exactly one direction; the edges need not point towards or away from a common root. For an edge $e=x\to y$, $C_e$ is the component of $T-e$ containing $x$.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §2.1, p.7 (PDF 8); Lemma 5.3, p.20 (PDF 21)

import Mathlib

set_option autoImplicit false

namespace PlanarDFVSKernel

/-- **A directed tree** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex
Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), §2.1, p.7 (PDF 8)): "A tree is a connected
undirected graph without a cycle. […] A directed tree is obtained by orienting each edge of a tree.
Its edges need not all point towards or away from a common root."

`T` is the underlying tree on the node type `P`; `arc x y` means that the edge `{x, y}` is oriented
`x → y`. Every arc is a tree edge, and every tree edge is oriented in exactly one direction. The
number of edges of the tree is `|P| − 1`. -/
structure DirTree (P : Type*) where
  /-- the underlying undirected tree -/
  T : SimpleGraph P
  /-- it is a tree -/
  isTree : T.IsTree
  /-- the orientation: `arc x y` when the edge `{x, y}` is oriented `x → y` -/
  arc : P → P → Prop
  arc_adj : ∀ x y, arc x y → T.Adj x y
  orient : ∀ x y, T.Adj x y → (arc x y ↔ ¬ arc y x)

/-- **`C_e`: the side of a tree edge** (ibid., Lemma 5.3(ii), p.20 (PDF 21)): "For every edge
e = x → y of T, let C_e be the component of the underlying undirected tree T − e containing x."
`D.side x y` is the set of nodes reachable from `x` in `T` with the edge `{x, y}` deleted. -/
def DirTree.side {P : Type*} (D : DirTree P) (x y : P) : Set P :=
  {z | (D.T.deleteEdges {s(x, y)}).Reachable x z}

end PlanarDFVSKernel


