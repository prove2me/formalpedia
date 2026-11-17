-- Prove2me | Definitions.Def_HyperCheeger_Supplement_IsNonCovering
-- name    : HyperCheeger_Supplement_IsNonCovering
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:01:35.569907+00:00
-- url     : https://prove2.me/theorems/0e15ccfb-78f2-4456-bff4-c607911c96c8
-- title:
--   Non-covering hypergraph
-- statement:
--   A hypergraph $H=(V_H,E_H,w_H)$ is **covering** if every pair of vertices is contained in at least one hyperedge; equivalently, its 2-shadow is a complete graph. $H$ is **non-covering** if it is not covering, that is, if there are two distinct vertices $u\ne v$ in $V_H$ such that no hyperedge $e\in E_H$ contains both $u$ and $v$.
--
--   Non-covering hypergraphs are the hypergraph analogue of non-complete graphs, the class on which the second eigenvalue of the normalized Laplacian is at most one and on which the improved Cheeger inequality (Theorem 4.3) holds.
--
--   **Formalization Note.** Only membership in the hyperedge set counts; weights play no role, so a zero-weight hyperedge still covers its pairs, as for the rank and connectedness of the published `HyperCheeger.Hypergraph`. A non-covering hypergraph has at least two vertices.
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), §1, p.1 (definition of covering hypergraph)

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph

namespace HyperCheeger.Supplement

open HyperCheeger

/-- A hypergraph `H` is **non-covering**: some pair of distinct vertices is contained in no
hyperedge. "A hypergraph is called covering if every pair of vertices is contained in at least one
hyperedge [LW21]. Equivalently, its 2-shadow is a complete graph." (Kamal, Bagchi, *A Cheeger
Inequality for Hypergraphs and Its Applications*, STOC 2027 submission, arXiv:2609.16286 (manuscript
sha256 e0942b89…), §1, p.1.) Non-covering is the negation.

**Formalization Note.** "Pair of vertices" means two distinct vertices. Only membership in the
hyperedge set `H.edges` counts; weights play no role, so a zero-weight hyperedge still covers its
pairs, as in the published `Hypergraph.rank` and `Hypergraph.IsConnected`. A non-covering hypergraph
has at least two vertices. -/
def IsNonCovering {V : Type} (H : Hypergraph V) : Prop :=
  ∃ u v : V, u ≠ v ∧ ∀ e ∈ H.edges, ¬(u ∈ e ∧ v ∈ e)

end HyperCheeger.Supplement


