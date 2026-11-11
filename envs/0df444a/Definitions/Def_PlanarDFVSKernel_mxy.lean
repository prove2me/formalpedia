-- Prove2me | Definitions.Def_PlanarDFVSKernel_mxy
-- name    : PlanarDFVSKernel_mxy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:26.333275+00:00
-- url     : https://prove2.me/theorems/07f9b570-5bcd-4f5f-9408-759d0ad02b71
-- title:
--   $m_{xy}$: the number of edges joining $x$ and $y$
-- statement:
--   For vertices $x,y$ of a digraph, $m_{xy}$ is the number of arcs $x\to y$ plus the number of arcs $y\to x$, i.e. the number of edges of the underlying undirected multigraph joining $x$ and $y$. After Reduction Rule 1, $m_{xy}\in\{0,1,2\}$.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §3.3, p.10 (PDF 11)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **`m_xy`, the number of edges directly joining `x` and `y`** in the underlying multigraph
(Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669
(held version, sha256 75cfca8f…), §3.3, p.10 (PDF 11)): "For distinct x, y ∈ V(G), […] let m_xy be
the number of edges directly joining them."

It counts the arcs `x → y` and the arcs `y → x` (each arc is one edge of the underlying graph,
p.6 (PDF 7)). -/
noncomputable def mxy {n m : ℕ} (G : Graph n m) (x y : Fin n) : ℕ := by
  classical exact (Finset.univ.filter fun e : Fin m =>
    (G.tail e = x ∧ G.head e = y) ∨ (G.tail e = y ∧ G.head e = x)).card

end PlanarDFVSKernel


