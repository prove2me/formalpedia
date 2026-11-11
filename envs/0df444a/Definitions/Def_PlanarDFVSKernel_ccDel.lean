-- Prove2me | Definitions.Def_PlanarDFVSKernel_ccDel
-- name    : PlanarDFVSKernel_ccDel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:05.641025+00:00
-- url     : https://prove2.me/theorems/1c7d91c3-1a12-444d-9709-154b76258435
-- title:
--   $\mathrm{cc}(G-\{x,y\})$ inside the strongly connected component of $x$
-- statement:
--   For vertices $x,y$ of a digraph, let $D$ be the strongly connected component of $x$. Then $\mathrm{cc}(G-\{x,y\})$ is the number of weakly connected components of the induced subgraph $D-\{x,y\}$, each isolated vertex counting as one component. Here $G$ is the underlying undirected multigraph of $D$.
--
--   It is the quantity of Reduction Rule 3 and Lemma 3.5, used for distinct $x,y$ in one strongly connected component.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §2.1, p.6–7 (PDF 7–8); §3.2, p.9 (PDF 10)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- The vertex set of the **strongly connected component** of `x` (Sheng, Xiao, *A Polynomial
Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256
75cfca8f…), §2.1, p.7 (PDF 8)): "Its strongly connected components are the maximal sets of mutually
reachable vertices. When a component is used as a set, we mean its vertex set." -/
noncomputable def sccOf {n m : ℕ} (G : Graph n m) (x : Fin n) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun v => SameSCC G x v

/-- Weak reachability inside the induced subgraph `D[S]`: a path in the underlying undirected
graph of `D[S]` (ibid., p.6 (PDF 7): "The underlying undirected graph G of D is obtained by
forgetting arc directions and retaining one edge for every arc."). -/
def InducedWeakReach {n m : ℕ} (G : Graph n m) (S : Finset (Fin n)) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen fun a b => a ∈ S ∧ b ∈ S ∧
    ∃ e, (G.tail e = a ∧ G.head e = b) ∨ (G.tail e = b ∧ G.head e = a)

/-- The number `cc(D[S])` of **weakly connected components** of `D[S]`, counting each isolated
vertex as one component (ibid., p.6 (PDF 7): "We write cc(G) for the number of connected components
of G, counting each isolated vertex as one component."). It is the number of distinct classes
`{w ∈ S : v, w weakly connected in D[S]}` over `v ∈ S`. -/
noncomputable def compCount {n m : ℕ} (G : Graph n m) (S : Finset (Fin n)) : ℕ := by
  classical exact (S.image fun v => S.filter fun w => InducedWeakReach G S v w).card

/-- **`cc(G − {x, y})` inside the strongly connected component of `x`** (Sheng, Xiao,
arXiv:2609.23669 (held version, sha256 75cfca8f…), §3.2, p.9 (PDF 10)): "Fix a strongly connected
component D of the current instance, and let G be its underlying undirected graph […] for any two
distinct vertices x, y, cc(G − {x, y}) = the number of weakly connected components of
D − {x, y}."

`ccDel G x y` is the number of weakly connected components of `D − {x, y}`, where `D` is the
strongly connected component of `x` (isolated vertices count). It is used for `x ≠ y` in one
strongly connected component (Reduction Rule 3, Lemma 3.5).

**Formalization Note** `D − {x, y}` is the induced subgraph on `sccOf G x ∖ {x, y}`. -/
noncomputable def ccDel {n m : ℕ} (G : Graph n m) (x y : Fin n) : ℕ :=
  compCount G (sccOf G x \ {x, y})

end PlanarDFVSKernel


