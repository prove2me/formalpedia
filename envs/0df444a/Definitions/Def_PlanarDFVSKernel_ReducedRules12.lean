-- Prove2me | Definitions.Def_PlanarDFVSKernel_ReducedRules12
-- name    : PlanarDFVSKernel_ReducedRules12
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:10.559604+00:00
-- url     : https://prove2.me/theorems/0869c50b-35db-4bf7-8e2c-0e88c6006fdb
-- title:
--   The state after Reduction Rules 1 and 2
-- statement:
--   A digraph $D$ is **reduced by Rules 1 and 2** when
--   1. it has no loops;
--   2. no two arcs have the same tail and the same head (opposite arcs are allowed);
--   3. both endpoints of every arc lie in one strongly connected component, so every weakly connected component is strongly connected;
--   4. every vertex has at least two distinct incoming and at least two distinct outgoing neighbours.
--
--   This is the paper's description of the instance "whenever we proceed beyond these two rules" (p.9).
--
--   **Formalization Note** It is a property of the digraph, not a run of the rules; Rule 1's budget outcomes ((iii), (iv)) are not part of it.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Reduction Rules 1–2, p.8–9 (PDF 9–10)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- The set of distinct **incoming neighbours** of `v` (Sheng, Xiao, *A Polynomial Kernel for
Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), §2.1,
p.6 (PDF 7)): "An incoming neighbor of v is a vertex u with an arc u → v." -/
noncomputable def inNbrs {n m : ℕ} (G : Graph n m) (v : Fin n) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun u => ∃ e, G.tail e = u ∧ G.head e = v

/-- The set of distinct **outgoing neighbours** of `v` (ibid., p.6 (PDF 7): "Outgoing neighbors
are defined symmetrically."). -/
noncomputable def outNbrs {n m : ℕ} (G : Graph n m) (v : Fin n) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun w => ∃ e, G.tail e = v ∧ G.head e = w

/-- **The state "Reduction Rules 1 and 2 are no longer applicable"** (Sheng, Xiao,
arXiv:2609.23669 (held version, sha256 75cfca8f…), Reduction Rules 1–2, p.8–9 (PDF 9–10), and the
paragraph after Lemma 3.2, p.9 (PDF 10)): "Whenever we proceed beyond these two rules, every vertex
has at least two distinct incoming neighbors and at least two distinct outgoing neighbors.
Moreover, each weakly connected component of the current instance is strongly connected, because
all arcs between distinct strongly connected components have been removed."

The four clauses are:
1. no loops (Rule 1(i));
2. no two arcs with the same tail and the same head (Rule 1(ii): "Remove repeated arcs with the
   same direction"; opposite arcs stay);
3. both endpoints of every arc lie in one strongly connected component (Rule 1(ii): "arcs between
   distinct strongly connected components"), so every weakly connected component is strongly
   connected;
4. every vertex has at least two distinct incoming and at least two distinct outgoing neighbours
   (Rule 2).

**Formalization Note** The state is a property of the digraph, not a run of the rules. Rule 1's
budget outcomes ((iii), (iv): `k ≥ 2`, a directed cycle exists, `k < |V(D)|`) are not part of
it; the statements using it hold without them. Clause 4 also excludes vertices on no directed
cycle (Rule 1(ii)), since with clause 3 every vertex has an incoming neighbour in its own
strongly connected component. -/
def ReducedRules12 {n m : ℕ} (G : Graph n m) : Prop :=
  Loopless G ∧
  (∀ e e' : Fin m, G.tail e = G.tail e' → G.head e = G.head e' → e = e') ∧
  (∀ e : Fin m, SameSCC G (G.tail e) (G.head e)) ∧
  (∀ v : Fin n, 2 ≤ (inNbrs G v).card ∧ 2 ≤ (outNbrs G v).card)

end PlanarDFVSKernel


