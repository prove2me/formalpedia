-- Prove2me | Definitions.Def_PaceSSSP517_Certified_Supplement_GraphOperators
-- name    : PaceSSSP517_Certified_Supplement_GraphOperators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:31:34.416067+00:00
-- url     : https://prove2.me/theorems/679a59de-431e-4539-836b-63cb27001f45
-- title:
--   Whole-graph Bellman–Ford and shortest-path hop diameter
-- statement:
--   Let $G=(V,E,w)$ be the published finite positive-real weighted undirected graph, with source $s_0$. For a real profile $d:V\to\mathbb R$, define the synchronous whole-graph Bellman–Ford operator by
--
--   $$
--   \operatorname{BF}_G(d)(v)=\min\bigl(\{d(v)\}\cup\{d(u)+w(u,v):\{u,v\}\in E\}\bigr).
--   $$
--
--   Both orientations of every undirected edge contribute. The minimum is over a finite nonempty set. For each vertex, take the least number of edges among the shortest source-to-vertex walks, and let $h(G)$ be their maximum. Connectivity and positive weights ensure shortest walks exist; no attainment hypothesis is added to the theorem.
--
--   These are the full-graph operator and source hop diameter used in Theorem 3.7, independent of the stored subgraph. The general graph, walks, weights and distances are imported from the published base definition.
--
--   **Formalization Note** Vertices are numbered by Fin n, a walk lists its endpoints and has $h+1$ vertices when it has $h$ edges, and Nat.sInf selects the least hop count. On disconnected inputs with no shortest walk, the unused default hop count is zero. All theorem uses have connected graphs.
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 5, §3.1 (hop diameter); p. 7, Theorem 3.7(ii); pp. 18–19, A.6

import Definitions.Def_PaceSSSP517_Certified_Graph

set_option autoImplicit false
open Classical

namespace PaceSSSP517.Certified.Supplement

/-- Whole-graph synchronous Bellman–Ford on finite real profiles, Theorem 3.7(ii),
p.7. A non-neighbour contributes the already included value d(v). The canonical
edge lookup permits both orientations of every undirected edge. -/
noncomputable def BF {n : ℕ} (G : WeightedGraph n) (d : Fin n → ℝ)
    (v : Fin n) : ℝ :=
  let candidates := Finset.univ.image (fun u =>
    if edge u v ∈ G.edges then d u + G.weight (edge u v) else d v)
  (insert (d v) candidates).min' (Finset.insert_nonempty _ _)

/-- Least number of edges on a shortest source-to-v walk, §3.1 p.5.
The predicate has a witness on the connected positive-weight graphs used below.
Nat.sInf gives 0 on the empty set, an unused disconnected-input convention. -/
noncomputable def shortestHops {n : ℕ} (G : WeightedGraph n) (s₀ v : Fin n) : ℕ :=
  sInf {h : ℕ | ∃ p : List (Fin n),
    IsWalk G.edges s₀ v p ∧ pathCost G p = distance G G.edges s₀ v ∧
      p.length = h + 1}

/-- Maximum of the minimum hop counts among shortest paths from s₀, §3.1 p.5.
The inserted zero only specifies the unused empty-vertex case. -/
noncomputable def hopDiameter {n : ℕ} (G : WeightedGraph n) (s₀ : Fin n) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup (shortestHops G s₀)

end PaceSSSP517.Certified.Supplement


