-- Prove2me | Definitions.Def_PlanarDFVSKernel_mu
-- name    : PlanarDFVSKernel_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:17.676747+00:00
-- url     : https://prove2.me/theorems/ebc2072f-b21e-44cc-936b-89c76edef139
-- title:
--   $\mu(x,y)$: the number of faces containing both $x$ and $y$
-- statement:
--   For vertices $x,y$ of a plane digraph, $\mu(x,y)$ is the number of distinct faces whose boundaries contain both $x$ and $y$. Faces are counted in the embedding of each component, including its outer face.
--
--   **Formalization Note** Faces are the published dart orbits; a vertex lies on a face when some dart of the orbit starts at it.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §3.3, p.10 (PDF 11)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **`µ(x, y)`, the number of faces whose boundaries contain both `x` and `y`** (Sheng, Xiao,
*A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version,
sha256 75cfca8f…), §3.3, p.10 (PDF 11)): "All face counts are taken separately in the induced
embedding of each strongly connected component, including its outer face. […] For distinct
x, y ∈ V(G), let µ(x, y) be the number of distinct faces whose boundaries contain both vertices".

A face is a published dart orbit `f ∈ faces E`; a vertex lies on its boundary when some dart of
`f` has that vertex as its origin (the orbit passes through every corner of the face).

**Formalization Note** Faces are orbits of the rotation system of the whole drawing, so each face
lies in one connected component of the underlying graph and every component has its own outer
face, as in the paper's per-component count. Isolated vertices lie on no face. -/
noncomputable def mu {n m : ℕ} {G : Graph n m} (E : Drawing G) (x y : Fin n) : ℕ := by
  classical exact ((faces E).filter fun f =>
    (∃ d ∈ f, origin G d = x) ∧ ∃ d ∈ f, origin G d = y).card

end PlanarDFVSKernel


