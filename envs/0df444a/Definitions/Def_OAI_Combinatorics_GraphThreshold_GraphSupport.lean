-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
-- name    : OAI_Combinatorics_GraphThreshold_GraphSupport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:11:00.381242+00:00
-- url     : https://prove2.me/theorems/101edd80-5c51-4a57-b753-13a5d95a78e9
-- title:
--   The graph spanned by an edge set without isolated vertices, and its copies
-- statement:
--   Let $[n]=\{0,\dots,n-1\}$, let $E_n$ be the set of unordered pairs of distinct vertices of $[n]$, and for $S\subseteq E_n$ let $G_S$ be the graph on $[n]$ with edge set $S$. The support $\operatorname{supp}(G)$ of a graph $G$ is the set of its vertices that lie on at least one edge, and $E(G)\subseteq E_n$ denotes the edge set of a graph on $[n]$. The symmetric group $S_n$ acts on edge sets by $\sigma\cdot S=\{\{\sigma(u),\sigma(v)\}:\ \{u,v\}\in S\}$.
--
--   1. **Edge subgraph.** For $S\subseteq E_n$, $K_S$ is the subgraph of the complete graph $K_n$ with vertex set $\operatorname{supp}(G_S)$ (the endpoints of the edges in $S$) and edge set $S$. For $S=\emptyset$ it has no vertices at all.
--
--   2. **Support graph.** $\Gamma_S$ is $K_S$ regarded as a graph in its own right, on the vertex set $\operatorname{supp}(G_S)$. It has no isolated vertices: every vertex of $\Gamma_S$ has a neighbour in $\Gamma_S$. Placing $\Gamma_S$ back into $[n]$ along the inclusion $\operatorname{supp}(G_S)\subseteq[n]$ recovers $G_S$, and so does $K_S$ when isolated vertices of $[n]$ are added.
--
--   3. **Supports under isomorphism.** For graphs $G$ and $H$ on arbitrary vertex sets, an isomorphism $\varphi:G\cong H$ restricts to an isomorphism of the induced subgraphs on the supports, $G[\operatorname{supp} G]\cong H[\operatorname{supp} H]$, and the image of $G$ under the vertex bijection $\varphi$ is exactly $H$. In particular $\Gamma_S\cong\Gamma_{\sigma\cdot S}$ for every $\sigma\in S_n$.
--
--   4. **Isomorphic support graphs are related by a permutation.** For $S,T\subseteq E_n$,
--
--      $$\Gamma_S\cong\Gamma_T\ \Longrightarrow\ \sigma\cdot S=T\ \text{ for some }\sigma\in S_n .$$
--
--   5. **Subgraphs without isolated vertices are edge subgraphs.** If $K$ is a subgraph of $K_n$ in which every vertex of $K$ has a neighbour in $K$, then $K=K_{E(K)}$, where $E(K)$ is the set of edges of $K$. This applies in particular whenever $K$, as a graph on its own vertex set, is isomorphic to some $\Gamma_S$.
--
--   6. **Selected edges of a placed graph span a copy.** Let $H$ be a graph on an arbitrary vertex set $V$, let $f:V\to[n]$ be injective, and let $f(H)$ be the graph on $[n]$ whose edges are the pairs $\{f(a),f(b)\}$ with $ab$ an edge of $H$. If $S\subseteq E(f(H))$, then $\Gamma_S$ has a copy in $H$: there is an injective map $\operatorname{supp}(G_S)\to V$ that sends every edge of $\Gamma_S$ to an edge of $H$.
--
--   These facts identify an unlabelled copy of a graph without isolated vertices inside $K_n$ with its edge set: the edge set $S$ determines the subgraph $K_S$, two support graphs are isomorphic exactly when the edge sets lie in one $S_n$-orbit, and any selection of edges of a placed copy of $H$ spans a graph that embeds in $H$. This is what allows copies of subgraphs to be counted as orbits of edge sets.
--
--   **Formalization Note** $K_S$ is `edgeSubgraph S`, a `Subgraph` of `⊤ : SimpleGraph (Fin n)`, and $\Gamma_S$ is `edgeSupportGraph S`, its coercion to a `SimpleGraph` on the subtype `(graphOfEdges S).support`. The isomorphisms in item 3 are `supportIso` (stated with `G.induce G.support`), `map_eq_of_iso` and `edgeSupportGraph_smulIso`; item 4 is `exists_smul_eq_of_edgeSupportGraph_iso`; item 5 is `subgraph_eq_edgeSubgraph` and `subgraph_eq_edgeSubgraph_of_iso`, with $E(K)$ written `graphEdges K.spanningCoe`; item 6 is `edgeSupportGraph_copy_of_subset`, which constructs a Mathlib `Copy` (an injective homomorphism) using classical choice.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphSupport.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphSupport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SecondKahnKalai mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension

namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

variable {n : ℕ}

/-- The subgraph containing exactly the given edges and their incident vertices.
For the empty edge set this has no vertices, as required for internal copies. -/
def edgeSubgraph (S : Finset (Edge n)) : (⊤ : SimpleGraph (Fin n)).Subgraph where
  verts := (graphOfEdges S).support
  Adj := (graphOfEdges S).Adj
  adj_sub h := h.ne
  edge_vert h := ⟨_, h⟩
  symm := (graphOfEdges S).symm

def edgeSupportGraph (S : Finset (Edge n)) :
    SimpleGraph (graphOfEdges S).support := (edgeSubgraph S).coe

@[simp]
theorem edgeSubgraph_spanningCoe (S : Finset (Edge n)) :
    (edgeSubgraph S).spanningCoe = graphOfEdges S := rfl

@[simp]
theorem edgeSupportGraph_map (S : Finset (Edge n)) :
    (edgeSupportGraph S).map (Function.Embedding.subtype
      (fun v => v ∈ (graphOfEdges S).support)) = graphOfEdges S := by
  exact SimpleGraph.Subgraph.spanningCoe_coe (edgeSubgraph S)

theorem edgeSupportGraph_noIsolates (S : Finset (Edge n))
    (v : (graphOfEdges S).support) :
    ∃ w, (edgeSupportGraph S).Adj v w := by
  obtain ⟨w, hw⟩ := v.property
  have hvw : (graphOfEdges S).Adj v w := hw
  exact ⟨⟨w, ⟨v, hvw.symm⟩⟩, hvw⟩

/-- Restriction of a graph isomorphism to its incident vertices. -/
def supportIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.induce G.support ≃g H.induce H.support where
  toFun v := ⟨e v, by
    obtain ⟨w, hw⟩ := v.property
    exact ⟨e w, e.toHom.map_adj hw⟩⟩
  invFun v := ⟨e.symm v, by
    obtain ⟨w, hw⟩ := v.property
    exact ⟨e.symm w, e.symm.toHom.map_adj hw⟩⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v)
  right_inv v := Subtype.ext (e.apply_symm_apply v)
  map_rel_iff' := e.map_rel_iff

def edgeSupportGraph_smulIso (σ : Equiv.Perm (Fin n)) (S : Finset (Edge n)) :
    edgeSupportGraph S ≃g edgeSupportGraph (σ • S) := by
  have e : graphOfEdges S ≃g graphOfEdges (σ • S) := by
    rw [graphOfEdges_smul]
    exact SimpleGraph.Iso.map σ _
  exact supportIso e

theorem map_eq_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.map e.toEquiv.toEmbedding = H := by
  ext a b
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨v, w, hvw, rfl, rfl⟩
    exact e.toHom.map_adj hvw
  · intro hab
    exact ⟨e.symm a, e.symm b, e.symm.toHom.map_adj hab,
      e.apply_symm_apply a, e.apply_symm_apply b⟩

/-- An isomorphism of incident-vertex graphs extends to a permutation of the
full ambient vertex set, hence to equality of the corresponding edge copies. -/
theorem exists_smul_eq_of_edgeSupportGraph_iso {S T : Finset (Edge n)}
    (e : edgeSupportGraph S ≃g edgeSupportGraph T) :
    ∃ σ : Equiv.Perm (Fin n), σ • S = T := by
  let f : (graphOfEdges S).support ↪ Fin n := Function.Embedding.subtype _
  let j : (graphOfEdges T).support ↪ Fin n := Function.Embedding.subtype _
  let g : (graphOfEdges S).support ↪ Fin n := e.toEquiv.toEmbedding.trans j
  obtain ⟨σ, hσ⟩ := exists_perm_comp_embedding f g
  have hfun : (fun v => σ (f v)) = (fun v => j (e v)) := funext hσ
  have hm : ((edgeSupportGraph S).map f).map σ.toEmbedding =
      (edgeSupportGraph T).map j := by
    rw [SimpleGraph.map_map]
    change (edgeSupportGraph S).map (fun v => σ (f v)) = _
    rw [hfun]
    change (edgeSupportGraph S).map (j ∘ e.toEquiv.toEmbedding) = _
    rw [← SimpleGraph.map_map, map_eq_of_iso]
  refine ⟨σ, (graphEdgeEquiv n).injective ?_⟩
  change graphOfEdges (σ • S) = graphOfEdges T
  rw [graphOfEdges_smul]
  simpa only [f, j, edgeSupportGraph_map] using hm

theorem subgraph_eq_edgeSubgraph
    (K : (⊤ : SimpleGraph (Fin n)).Subgraph)
    (hK : ∀ v : K.verts, ∃ w, K.coe.Adj v w) :
    K = edgeSubgraph (graphEdges K.spanningCoe) := by
  apply SimpleGraph.Subgraph.ext
  · change K.verts = (graphOfEdges (graphEdges K.spanningCoe)).support
    rw [graphOfEdges_graphEdges]
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw⟩ := hK ⟨v, hv⟩
      exact ⟨w, hw⟩
    · rintro ⟨w, hw⟩
      exact K.edge_vert hw
  · change K.Adj = (graphOfEdges (graphEdges K.spanningCoe)).Adj
    rw [graphOfEdges_graphEdges]
    rfl

theorem subgraph_eq_edgeSubgraph_of_iso {S : Finset (Edge n)}
    (K : (⊤ : SimpleGraph (Fin n)).Subgraph)
    (e : edgeSupportGraph S ≃g K.coe) :
    K = edgeSubgraph (graphEdges K.spanningCoe) := by
  apply subgraph_eq_edgeSubgraph K
  intro v
  obtain ⟨w, hw⟩ := edgeSupportGraph_noIsolates S (e.symm v)
  refine ⟨e w, ?_⟩
  have hh : K.coe.Adj (e (e.symm v)) (e w) := e.toHom.map_adj hw
  simpa only [e.apply_symm_apply] using hh

/-- A selected edge subset of an embedded graph pulls back to an actual copy
inside the original graph, using only incident vertices of the selection. -/
def edgeSupportGraph_copy_of_subset {V : Type*} (f : V ↪ Fin n)
    (H : SimpleGraph V) (S : Finset (Edge n))
    (hS : S ⊆ graphEdges (H.map f)) : (edgeSupportGraph S).Copy H := by
  have hle : graphOfEdges S ≤ H.map f := by
    simpa only [graphOfEdges_graphEdges] using graphOfEdges_mono hS
  have hrange (v : (graphOfEdges S).support) : ∃ a : V, f a = v.val := by
    obtain ⟨w, hw⟩ := v.property
    obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj f H v w).mp (hle hw)
    exact ⟨a, ha⟩
  let g : (graphOfEdges S).support → V := fun v => Classical.choose (hrange v)
  have hg (v : (graphOfEdges S).support) : f (g v) = v.val :=
    Classical.choose_spec (hrange v)
  refine { toHom := ⟨g, ?_⟩, injective' := ?_ }
  · intro v w hvw
    apply (SimpleGraph.map_adj_apply (f := f)).mp
    rw [hg v, hg w]
    exact hle hvw
  · intro v w hvw
    change g v = g w at hvw
    apply Subtype.ext
    rw [← hg v, ← hg w, hvw]

end LeanBlast.SecondKahnKalai

end

end OAI


