-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
-- name    : OAI_Combinatorics_GraphThreshold_GraphEncoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:08:07.344813+00:00
-- url     : https://prove2.me/theorems/d1c5a56f-8e8a-4635-b6fd-05f9cfcd3fff
-- title:
--   Edge-set encoding of graphs on $n$ labelled vertices and the permutation action on edges
-- statement:
--   Fix $n\in\mathbb{N}$ and the vertex set $[n]=\{0,1,\dots,n-1\}$. Let $E_n$ be the set of unordered pairs $\{u,v\}$ of distinct vertices $u\neq v$ of $[n]$, i.e. the $\binom{n}{2}$ edges of the complete graph $K_n$. For a set $W\subseteq E_n$ write $G_W$ for the simple graph on $[n]$ whose edge set is exactly $W$, and for a simple graph $G$ write $e(G)$ for its number of edges, each unordered edge counted once. This file sets up the dictionary between graphs on $[n]$ and subsets of $E_n$.
--
--   1. **Edge set of a graph.** For a simple graph $G$ on $[n]$, $E(G)=\{e\in E_n:\ e \text{ is an edge of } G\}$.
--
--   2. **Permutation action.** The symmetric group $S_n$ of all permutations of $[n]$ acts on $E_n$ by $\sigma\cdot\{u,v\}=\{\sigma(u),\sigma(v)\}$, and hence on subsets of $E_n$ by $\sigma\cdot W=\{\sigma\cdot e:\ e\in W\}$.
--
--   3. **Encoding bijection.** The maps $W\mapsto G_W$ and $G\mapsto E(G)$ are mutually inverse bijections between subsets of $E_n$ and simple graphs on $[n]$:
--
--      $$E(G_W)=W,\qquad G_{E(G)}=G .$$
--
--      They respect inclusion: if every edge of $G$ is an edge of $H$ (written $G\le H$) then $E(G)\subseteq E(H)$, and $G_S\le G_T$ holds if and only if $S\subseteq T$. At the extremes, $G_\emptyset$ is the edgeless graph, $G_{E_n}=K_n$, the edgeless graph has $E=\emptyset$, and $E(K_n)=E_n$.
--
--   4. **Equivariance.** For every $\sigma\in S_n$ and $W\subseteq E_n$, the graph $G_{\sigma\cdot W}$ is the image of $G_W$ under the relabelling $\sigma$: the pair $\{\sigma(u),\sigma(v)\}$ is an edge of $G_{\sigma\cdot W}$ exactly when $\{u,v\}\in W$.
--
--   5. **Edge counts.** The edges of $G$ correspond bijectively to the elements of $E(G)$, so
--
--      $$|E(G)|=e(G),\qquad e(G_W)=|W| .$$
--
--   Through this encoding, a graph on $[n]$ is the same thing as a subset of the finite set $E_n$, so the random graph $G(n,p)$ becomes the random subset of $E_n$ in which each pair is kept independently with probability $p$, and relabelling the vertices becomes the action of $S_n$ on edge sets. This is the basis for counting copies of a fixed graph as orbits of edge sets.
--
--   **Formalization Note** $E_n$ is the type `Edge n` of non-diagonal elements of `Sym2 (Fin n)`, $G_W$ is `graphOfEdges W`, $E(G)$ is the `Finset` `graphEdges G`, the action is the instance `edgeMulAction` (extended to finsets pointwise), the bijection is `graphEdgeEquiv n`, and $e(G)$ is `edgeCount G`, the cardinality of the edge set; `graphEdgesEquiv G` identifies `graphEdges G` with `G.edgeSet`. The remaining members are simp lemmas recording the identities above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphEncoding.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphEncoding.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

/-- The non-loop edge set of an ordinary graph on `Fin n`. -/
def graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Edge n) := by
  classical
  exact Finset.univ.filter (fun e => e.val ∈ G.edgeSet)

variable {n : ℕ}

/-- Vertex permutations act on unordered non-loop edges. -/
instance edgeMulAction : MulAction (Equiv.Perm (Fin n)) (Edge n) where
  smul σ e := ⟨Sym2.map σ e.val, fun h =>
    e.property ((Sym2.isDiag_map σ.injective).mp h)⟩
  one_smul e := by
    apply Subtype.ext
    change Sym2.map (1 : Equiv.Perm (Fin n)) e.val = e.val
    simp
  mul_smul σ τ e := by
    apply Subtype.ext
    change Sym2.map (σ * τ) e.val = Sym2.map σ (Sym2.map τ e.val)
    rw [Sym2.map_map]
    rfl

@[simp]
theorem edge_smul_val (σ : Equiv.Perm (Fin n)) (e : Edge n) :
    (σ • e).val = Sym2.map σ e.val := rfl

@[simp]
theorem mem_graphEdges (G : SimpleGraph (Fin n)) (e : Edge n) :
    e ∈ graphEdges G ↔ e.val ∈ G.edgeSet := by
  classical
  simp [graphEdges]

theorem edgeSet_graphOfEdges (W : Finset (Edge n)) :
    (graphOfEdges W).edgeSet = Subtype.val '' (W : Set (Edge n)) := by
  rw [graphOfEdges, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact And.left
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, a.property⟩

@[simp]
theorem mem_edgeSet_graphOfEdges (W : Finset (Edge n)) (e : Edge n) :
    e.val ∈ (graphOfEdges W).edgeSet ↔ e ∈ W := by
  classical
  simp [graphOfEdges, e.property, Subtype.val_injective.eq_iff]

@[simp]
theorem graphEdges_graphOfEdges (W : Finset (Edge n)) :
    graphEdges (graphOfEdges W) = W := by
  classical
  ext e
  simp

@[simp]
theorem graphOfEdges_graphEdges (G : SimpleGraph (Fin n)) :
    graphOfEdges (graphEdges G) = G := by
  apply SimpleGraph.edgeSet_injective
  ext e
  by_cases he : e.IsDiag
  · simp [SimpleGraph.not_mem_edgeSet_of_isDiag, he]
  · exact (mem_edgeSet_graphOfEdges (graphEdges G) ⟨e, he⟩).trans
      (mem_graphEdges G ⟨e, he⟩)

/-- No graphs or edge sets are omitted or multiply represented. -/
def graphEdgeEquiv (n : ℕ) : Finset (Edge n) ≃ SimpleGraph (Fin n) where
  toFun := graphOfEdges
  invFun := graphEdges
  left_inv := graphEdges_graphOfEdges
  right_inv := graphOfEdges_graphEdges

theorem graphOfEdges_smul (σ : Equiv.Perm (Fin n)) (W : Finset (Edge n)) :
    graphOfEdges (σ • W) = (graphOfEdges W).map σ.toEmbedding := by
  apply SimpleGraph.edgeSet_injective
  rw [edgeSet_graphOfEdges, SimpleGraph.edgeSet_map, edgeSet_graphOfEdges,
    Finset.smul_finset_def, Finset.coe_image, Set.image_image, Set.image_image]
  rfl

@[simp]
theorem graphOfEdges_empty : graphOfEdges (∅ : Finset (Edge n)) = ⊥ := by
  simp [graphOfEdges]

@[simp]
theorem graphEdges_bot : graphEdges (⊥ : SimpleGraph (Fin n)) = ∅ := by
  classical
  ext e
  simp

@[simp]
theorem graphEdges_top : graphEdges (⊤ : SimpleGraph (Fin n)) = Finset.univ := by
  classical
  ext e
  simp [e.property]

@[simp]
theorem graphOfEdges_univ : graphOfEdges (Finset.univ : Finset (Edge n)) = ⊤ := by
  rw [← graphEdges_top, graphOfEdges_graphEdges]

theorem graphEdges_mono {G H : SimpleGraph (Fin n)} (h : G ≤ H) :
    graphEdges G ⊆ graphEdges H := by
  intro e he
  exact (mem_graphEdges H e).mpr (SimpleGraph.edgeSet_mono h
    ((mem_graphEdges G e).mp he))

theorem graphOfEdges_mono {S T : Finset (Edge n)} (h : S ⊆ T) :
    graphOfEdges S ≤ graphOfEdges T := by
  apply SimpleGraph.fromEdgeSet_mono
  exact Set.image_mono h

@[simp]
theorem graphOfEdges_le_iff {S T : Finset (Edge n)} :
    graphOfEdges S ≤ graphOfEdges T ↔ S ⊆ T := by
  constructor
  · intro h
    simpa using graphEdges_mono h
  · exact graphOfEdges_mono

/-- Edge-set encoding preserves the ordinary unlabelled edge count. -/
def graphEdgesEquiv (G : SimpleGraph (Fin n)) : ↥(graphEdges G) ≃ G.edgeSet where
  toFun e := ⟨e.val.val, (mem_graphEdges G e.val).mp e.property⟩
  invFun e := ⟨⟨e.val, G.not_isDiag_of_mem_edgeSet e.property⟩,
    (mem_graphEdges G _).mpr e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem card_graphEdges (G : SimpleGraph (Fin n)) :
    (graphEdges G).card = edgeCount G := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card, ← Fintype.card_coe]
  exact Fintype.card_congr (graphEdgesEquiv G)

@[simp]
theorem edgeCount_graphOfEdges (W : Finset (Edge n)) :
    edgeCount (graphOfEdges W) = W.card := by
  rw [← card_graphEdges, graphEdges_graphOfEdges]

end LeanBlast.SecondKahnKalai

end

end OAI


