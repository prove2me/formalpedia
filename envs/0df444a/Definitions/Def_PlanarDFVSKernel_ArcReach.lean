-- Prove2me | Definitions.Def_PlanarDFVSKernel_ArcReach
-- name    : PlanarDFVSKernel_ArcReach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:23.365921+00:00
-- url     : https://prove2.me/theorems/9258e2e9-7e3b-4267-96ec-b237f85a578f
-- title:
--   Reachability and weak connectivity along an arc list
-- statement:
--   A digraph on a vertex type $V$ is given by a list of arcs $(u,v)$. We write $u\rightsquigarrow v$ if $v$ is reachable from $u$ by a directed walk (possibly of length zero). Two vertices are **weakly connected** if they are joined by a path of the underlying undirected graph, i.e. they lie in one weakly connected component.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §2.1, p.6 (PDF 7)

import Mathlib

set_option autoImplicit false

namespace PlanarDFVSKernel

/-- **Reachability `u ⇝ v` along a list of arcs** (Sheng, Xiao, *A Polynomial Kernel for Planar
Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), §2.1, p.6
(PDF 7)): "A directed walk follows the arc directions and may repeat vertices and arcs. […] We write
u ⇝ v if v is reachable from u, allowing a path of length zero."

A digraph on a vertex type `V` is given by its arc list `A : List (V × V)`, an arc `(u, v)` going
from `u` to `v`; repeated entries are repeated arcs. `ArcReach A u v` holds when a directed walk
from `u` to `v` exists (possibly of length zero). -/
def ArcReach {V : Type*} (A : List (V × V)) : V → V → Prop :=
  Relation.ReflTransGen fun u v => (u, v) ∈ A

/-- **Weak connectivity along a list of arcs** (ibid., p.6 (PDF 7)): "A digraph is weakly connected
if its underlying undirected graph is connected […] Its weakly connected components are the
connected components of its underlying graph." `ArcWeakReach A u v` holds when `u` and `v` lie in
one weakly connected component of the digraph with arc list `A`. -/
def ArcWeakReach {V : Type*} (A : List (V × V)) : V → V → Prop :=
  Relation.ReflTransGen fun u v => (u, v) ∈ A ∨ (v, u) ∈ A

end PlanarDFVSKernel


