-- Prove2me | Definitions.Def_ProphetBipartite_IsMatching
-- name    : ProphetBipartite_IsMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:15.333453+00:00
-- url     : https://prove2.me/theorems/2e0579c6-7924-4ec2-a997-20bbd4c7103b
-- title:
--   Matchings of a bipartite multigraph
-- statement:
--   Let $G(L,R)$ be a bipartite multigraph: $L$ and $R$ are finite sets of left and right vertices, $E$ is a finite set of multi-edges, and each edge $e\in E$ joins the left vertex $\mathrm{left}(e)\in L$ to the right vertex $\mathrm{right}(e)\in R$. Several edges may join the same pair of vertices.
--
--   A set $S\subseteq E$ is a **matching** when no two distinct edges of $S$ share an endpoint:
--
--   $$
--   e\neq e'\in S\ \Longrightarrow\ \mathrm{left}(e)\neq\mathrm{left}(e')\ \text{and}\ \mathrm{right}(e)\neq\mathrm{right}(e').
--   $$
--
--   Matchings are the feasible sets of the online selection problem and of the prophet's offline problem.
--
--   **Formalization Note** The multigraph is given by the edge type and the two endpoint maps, which need not be injective on pairs; two parallel edges are never in one matching.
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, §2, p.4

import Mathlib

namespace ProphetBipartite

/-- **Matchings of a bipartite multigraph.** Gravin & Wang, *Prophet inequality for bipartite
matching: merits of being simple and non adaptive*, arXiv:1902.06243v1, §2, p.4.

The graph `G(L, R)` has left vertices `L`, right vertices `R` and a finite set of multi-edges `E`;
edge `e` joins `left e ∈ L` to `right e ∈ R`. A set `S` of edges is a matching when distinct edges
of `S` share no endpoint: they have distinct left endpoints and distinct right endpoints.

**Formalization Note.** The graph is a bipartite **multigraph**: edges are elements of a type `E`
with endpoint maps `left`, `right`, which need not be injective on pairs, so parallel edges
between the same `i` and `j` are distinct edges. Two parallel edges never lie in one matching. -/
def IsMatching {L R E : Type*} (left : E → L) (right : E → R) (S : Finset E) : Prop :=
  ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → left e ≠ left e' ∧ right e ≠ right e'

end ProphetBipartite


