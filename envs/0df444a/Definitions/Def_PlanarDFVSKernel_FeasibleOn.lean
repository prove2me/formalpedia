-- Prove2me | Definitions.Def_PlanarDFVSKernel_FeasibleOn
-- name    : PlanarDFVSKernel_FeasibleOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:18.618136+00:00
-- url     : https://prove2.me/theorems/ad9ab125-985b-4bee-a4ce-0224156f0a80
-- title:
--   Feasibility of $(D[A],k)$: a DFVS of size $\le k$ inside a kept vertex set
-- statement:
--   For a digraph $D$, a vertex set $A$ and $k\in\mathbb N$, $(D[A],k)$ is a **YES-instance** if there is $Y\subseteq A$ with $|Y|\le k$ such that the induced subgraph $D[A\setminus Y]$ has no directed cycle.
--
--   It expresses the instances $(D-\{x,y\},k-2)$ and $(D-v,k-1)$ produced by the reduction rules without renumbering vertices, since $D-X=D[V(D)\setminus X]$. For $A=V(D)$ it is the published `Feasible`.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §1, p.1 (PDF 2); §2.1, p.6 (PDF 7)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **Feasibility of the instance `(D[A], k)`** (Sheng, Xiao, *A Polynomial Kernel for Planar
Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), §1, p.1
(PDF 2) and §2.1, p.6 (PDF 7)): "Does there exist a set X ⊆ V(D) with |X| ≤ k such that D − X has
no directed cycle?", asked for the induced subgraph `D[A]` (p.6: "the induced subgraph D[X]
contains the vertices of X and all arcs with both endpoints in X").

`FeasibleOn G A k` holds when some `Y ⊆ A` with `|Y| ≤ k` leaves `D[A ∖ Y]` without a directed
cycle. It is how the reduction rules' instances `(D − {x, y}, k − 2)` and `(D − v, k − 1)` are
expressed without re-indexing vertices: `D − X = D[V(D) ∖ X]`.

**Formalization Note** `InducedAcyclic G B` (published) says that no nonempty closed directed
walk has all its arc tails in `B`; such a walk then has all its vertices in `B`, so this is
acyclicity of `D[B]`. `FeasibleOn G Finset.univ k` is the published `Feasible G k`. -/
def FeasibleOn {n m : ℕ} (G : Graph n m) (A : Finset (Fin n)) (k : ℕ) : Prop :=
  ∃ Y ⊆ A, Y.card ≤ k ∧ InducedAcyclic G (A \ Y)

end PlanarDFVSKernel


