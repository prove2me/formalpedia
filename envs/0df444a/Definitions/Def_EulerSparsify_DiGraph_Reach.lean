-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_Reach
-- name    : EulerSparsify_DiGraph_Reach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:32.239525+00:00
-- url     : https://prove2.me/theorems/d74d74e0-0b1f-4326-9640-34eb785d2a87
-- title:
--   Connectivity through edges of positive weight
-- statement:
--   Vertex $v$ is **reachable** from $u$ in a weighted graph if there is a walk from $u$ to $v$ each of whose steps crosses an edge of positive weight, in either direction (that is, in $\mathrm{und}(\vec G)$). A graph is **connected on** a vertex set $U$ if every two vertices of $U$ are reachable from each other, and **connected** if this holds on all of $V$.
--
--   **Formalization Note** Edges of weight $0$ do not connect anything: a subgraph is encoded by setting the weights of the edges outside it to $0$.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, pp.8–10; proof of Proposition 4.3, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph

namespace EulerSparsify

/-- **Connectivity through edges of positive weight** (§3, p.8–10; used in Fact 3.3 and in
`diam_ER`, Proposition 4.3's proof, p.13, PDF p.15).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), p.13: "bK_{i′} is connected as diam_ER(bK_{i′}) ≤ ρ".

`G.Reach u v` holds if `v` can be reached from `u` by a walk whose every step crosses an edge of
positive weight, in either direction (the undirected graph `und(⃗G)`).

**Formalization Note.** Edges of weight zero do not connect: a subgraph is encoded by setting the
weights outside its edge set to zero (`DiGraph.restrict`). -/
def DiGraph.Reach {V E : Type} (G : DiGraph V E) (u v : V) : Prop :=
  Relation.ReflTransGen
    (fun a b => ∃ e, 0 < G.w e ∧
      ((G.head e = a ∧ G.tail e = b) ∨ (G.head e = b ∧ G.tail e = a))) u v

/-- `G.ConnectedOn U`: every two vertices of `U` are joined in `G` by a walk of positive-weight
edges. -/
def DiGraph.ConnectedOn {V E : Type} (G : DiGraph V E) (U : Finset V) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, G.Reach u v

/-- `G.IsConnected`: every two vertices are joined by a walk of positive-weight edges. -/
def DiGraph.IsConnected {V E : Type} (G : DiGraph V E) : Prop :=
  ∀ u v : V, G.Reach u v

end EulerSparsify


