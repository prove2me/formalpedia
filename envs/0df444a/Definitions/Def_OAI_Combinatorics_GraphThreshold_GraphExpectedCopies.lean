-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
-- name    : OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:16:17.994062+00:00
-- url     : https://prove2.me/theorems/0666971c-0322-4dc2-b168-6f301322bc34
-- title:
--   Copies of a graph in $G$ are the copies in $K_n$ whose edges all lie in $G$
-- statement:
--   Let $G$ be a simple graph on $[n]=\{0,\dots,n-1\}$, let $K_n$ be the complete graph on $[n]$, and let $F$ be a simple graph on an arbitrary vertex set $V$. A subgraph $K$ of a graph consists of a set of vertices and a set of edges of that graph between them; it may have isolated vertices. An unlabelled copy of $F$ in $G$ is a subgraph $K$ of $G$ with $F\cong K$, where $K$ is regarded as a graph on its own vertex set.
--
--   1. Every subgraph $K$ of $G$ is also a subgraph of $K_n$, with the same vertex set (isolated vertices included) and the same edges.
--
--   2. Conversely, a subgraph $K$ of $K_n$ all of whose edges are edges of $G$ is a subgraph of $G$, with the same vertices and edges.
--
--   3. These two operations are mutually inverse and give a bijection
--
--      $$\{K\le G:\ F\cong K\}\ \longleftrightarrow\ \{K\le K_n:\ F\cong K,\ E(K)\subseteq E(G)\},$$
--
--      where $K\le G$ means that $K$ is a subgraph of $G$ and $E(\cdot)$ denotes the edge set.
--
--   Consequently the number of unlabelled copies of $F$ in $G$ equals the number of unlabelled copies of $F$ in $K_n$ whose edges are all present in $G$. For the random graph $G(n,p)$ this writes the copy count as a sum of indicator variables indexed by the fixed family of copies of $F$ in $K_n$, which is the key step in computing the expected number of copies. The bijection is between subgraphs themselves; no embeddings are chosen or counted, so automorphisms of $F$ never cause over-counting.
--
--   **Formalization Note** The maps are `subgraphToComplete` and `subgraphFromComplete`, and the bijection is `completeCopyEquiv G F`, whose two sides are the subtypes of `G.Subgraph` and of `(⊤ : SimpleGraph (Fin n)).Subgraph` cut out by `Nonempty (F ≃g K.coe)`; the condition $E(K)\subseteq E(G)$ is written `K.spanningCoe ≤ G`. Mathlib's `G.copyCount F` counts exactly the subgraphs on the left-hand side.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphExpectedCopies.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphExpectedCopies.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits

namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

universe u

variable {n : ℕ} {V : Type u}

/-- Regard an actual subgraph as a subgraph of the complete graph. Its vertex set,
including all isolated vertices, is unchanged. -/
def subgraphToComplete {G : SimpleGraph (Fin n)} (K : G.Subgraph) :
    (⊤ : SimpleGraph (Fin n)).Subgraph where
  verts := K.verts
  Adj := K.Adj
  adj_sub h := h.ne
  edge_vert := K.edge_vert
  symm := K.symm

/-- A complete-graph subgraph whose edges occur in G is the same actual subgraph of G. -/
def subgraphFromComplete (G : SimpleGraph (Fin n))
    (K : (⊤ : SimpleGraph (Fin n)).Subgraph) (hK : K.spanningCoe ≤ G) :
    G.Subgraph where
  verts := K.verts
  Adj := K.Adj
  adj_sub h := hK h
  edge_vert := K.edge_vert
  symm := K.symm

/-- Copies are put in bijection without choosing or counting graph embeddings. -/
def completeCopyEquiv (G : SimpleGraph (Fin n)) (F : SimpleGraph V) :
    {K : G.Subgraph // Nonempty (F ≃g K.coe)} ≃
      {K : (⊤ : SimpleGraph (Fin n)).Subgraph //
        Nonempty (F ≃g K.coe) ∧ K.spanningCoe ≤ G} where
  toFun K := ⟨subgraphToComplete K.val, K.property, fun _ _ h => K.val.adj_sub h⟩
  invFun K := ⟨subgraphFromComplete G K.val K.property.2, K.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end LeanBlast.SecondKahnKalai

end

end OAI


