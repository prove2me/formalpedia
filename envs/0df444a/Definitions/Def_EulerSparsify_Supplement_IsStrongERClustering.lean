-- Prove2me | Definitions.Def_EulerSparsify_Supplement_IsStrongERClustering
-- name    : EulerSparsify_Supplement_IsStrongERClustering
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:32:20.524657+00:00
-- url     : https://prove2.me/theorems/4707348c-de4a-4fba-b478-308e42c6a010
-- title:
--   Definition 3.6 — $(\rho,\gamma)$-strong effective resistance clustering
-- statement:
--   Let $G=(V,E,w)$ be a finite weighted graph with weights $w_e$, and write $w(F)=\sum_{e\in F}w_e$ for a set of edges $F$ and $w(E)$ for the total weight. For $U\subseteq V$, $G[U]$ is the induced subgraph on $U$ (all edges with both endpoints in $U$, with their weights) and $E(G[U])$ its edge set. The **effective resistance diameter** of $G[U]$ is $\mathrm{diam}_{\mathrm{ER}}(G[U])=\max_{u,v\in U}\mathrm{ER}_{G[U]}(u,v)$, where $\mathrm{ER}_{H}(u,v)=b_{(u,v)}^\top L_H^\dagger b_{(u,v)}$.
--
--   A family $\{U_i\}_{i\in[I]}$ of vertex sets is a **$(\rho,\gamma)$-strong effective resistance clustering** of $G$ if the $U_i$ are pairwise disjoint, cover $V$, and
--
--   1. **strong effective resistance diameter:** for every $i$, $G[U_i]$ is connected and $\mathrm{diam}_{\mathrm{ER}}(G[U_i])\le\rho$;
--   2. **edge weights cut:**
--   $$w\Bigl(E(G)\setminus\bigcup_{i\in[I]}E(G[U_i])\Bigr)\le\frac{w(E)}{\gamma}.$$
--
--   The clustering splits the graph into pieces of small electrical diameter, measured in each piece's own induced subgraph, while cutting only a $1/\gamma$ fraction of the total weight. It is the output guarantee of Theorem 4.1.
--
--   **Formalization Note** The family is indexed by $\mathrm{Fin}\,I$; empty parts are allowed. The diameter bound is the published `EulerSparsify.DiGraph.DiamERLe` applied to `G.restrict (G.inducedEdges (U i))`, which also requires connectivity through positive-weight edges, because the pseudoinverse formula returns a finite number across components where the true resistance is $+\infty$. Definition 3.6's range $\gamma>1$ is not part of the predicate; theorems state their own range of $\gamma$.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Definition 3.6, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_restrict
import Definitions.Def_EulerSparsify_DiGraph_DiamERLe

namespace EulerSparsify

namespace Supplement

/-- **(ρ, γ)-strong effective resistance clustering** (Definition 3.6, p.10, PDF p.12).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Definition 3.6, p.10
(PDF p.12): "We define the strong effective resistance clustering of a graph by a vertex
partitioning of the following form. We call {U_i}_{i∈[I]} a (ρ, γ)-strong effective resistance
clustering if {U_i}_{i∈[I]} are disjoint and the following hold.
1. Strong effective resistance diameter: For all i ∈ [I], diam_ER(G[U_i]) ≤ ρ.
2. Edge weights cut: w(E(G) ∖ (⋃_{i∈[I]} E(G[U_i]))) ≤ w(E)/γ, for γ > 1."

`IsStrongERClustering G ρ γ U` says that the family `{U_i}_{i ∈ Fin I}` is a vertex partition
(pairwise disjoint and covering every vertex of `G`), that every induced subgraph
`G[U_i] = G.restrict (G.inducedEdges (U i))` is connected on `U_i` through positive-weight edges
with weighted effective resistance at most `ρ` between any two vertices of `U_i`, and that the total
weight of the edges not inside any `G[U_i]` is at most `w(E)/γ`, where `w(E) = Σ_e w_e`.

**Formalization Note.**
* "Vertex partitioning" is read as disjoint and covering; empty parts are allowed (an empty part
  has no induced edges and satisfies the diameter bound vacuously).
* `diam_ER(G[U_i]) ≤ ρ` is the published `DiGraph.DiamERLe`, which includes connectivity of
  `G[U_i]`: the pseudoinverse formula is finite across components, while the true resistance there
  is `+∞`.
* The range `γ > 1` of Definition 3.6 is a parameter condition, not part of the predicate; the
  theorems that use the predicate state their own range of `γ`. -/
def IsStrongERClustering {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (ρ γ : ℝ) {I : ℕ} (U : Fin I → Finset V) : Prop :=
  (∀ i i', i ≠ i' → Disjoint (U i) (U i')) ∧ (∀ v, ∃ i, v ∈ U i) ∧
  (∀ i, (G.restrict (G.inducedEdges (U i))).DiamERLe (U i) ρ) ∧
  (∑ e ∈ Finset.univ.filter (fun e => ∀ i, e ∉ G.inducedEdges (U i)), G.w e) ≤
    (∑ e, G.w e) / γ

end Supplement

end EulerSparsify


