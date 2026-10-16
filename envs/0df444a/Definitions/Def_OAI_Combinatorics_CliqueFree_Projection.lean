-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
-- name    : OAI_Combinatorics_CliqueFree_Projection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:50:16.219504+00:00
-- url     : https://prove2.me/theorems/4c52d669-1558-458c-9bed-1fabb1600694
-- title:
--   Edge projections: graph homomorphisms that are injective on oriented edges
-- statement:
--   Let $H$ be a simple graph on a finite vertex set $U$, let $G$ be a simple graph on a finite vertex set $V$, and let $\pi:U\to V$ be a map. Write $\sim_H$ and $\sim_G$ for adjacency, and $\vec{E}(\cdot)$ for the set of oriented edges, i.e. ordered pairs of adjacent vertices.
--
--   1. **Edge projection.** The map $\pi$ is an edge projection from $H$ to $G$ if
--
--      (a) it preserves adjacency: $a\sim_H b$ implies $\pi(a)\sim_G\pi(b)$, i.e. $\pi$ is a graph homomorphism; and
--
--      (b) it is injective on oriented edges: for all $a,b,c,d\in U$,
--
--      $$a\sim_H b,\ \ c\sim_H d,\ \ \pi(a)=\pi(c),\ \ \pi(b)=\pi(d)\quad\Longrightarrow\quad a=c\ \text{ and }\ b=d .$$
--
--   2. **Induced edge map.** For an edge projection, the map $\vec{E}(H)\to\vec{E}(G)$, $(a,b)\mapsto\bigl(\pi(a),\pi(b)\bigr)$, which is injective by (b).
--
--   Edge projections model vertex splitting: the vertices of $H$ are copies of vertices of $G$, and a vertex weight $w$ on $G$ is transported to the weight $w\circ\pi$ on $H$, which is the sense in which the projection preserves weights. Since the induced edge map is injective, a sum over oriented edges $(a,b)$ of $H$ of a nonnegative quantity depending only on $\bigl(\pi(a),\pi(b)\bigr)$, such as the weighted edge mass for $w\circ\pi$ with $w\ge 0$, is at most the corresponding sum over oriented edges of $G$. Moreover a homomorphism maps cliques to cliques of the same size, so $H$ has no clique of size $r$ whenever $G$ has none.
--
--   **Formalization Note** `EdgeProjection H G π` is a `Prop`-valued structure with fields `map_adj` and `inj`, and `EdgeProjection.edgeMap` is the induced map from `EdgeState H` to `EdgeState G`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Projection.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Projection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CliqueFreeLog mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

variable {U : Type v} [Fintype U]

/-- A weight-preserving, directed-edge-injective projection. -/
structure EdgeProjection (H : SimpleGraph U) (G : SimpleGraph V) (π : U → V) : Prop where
  map_adj : ∀ a b, H.Adj a b → G.Adj (π a) (π b)
  inj : ∀ a b c d, H.Adj a b → H.Adj c d → π a = π c → π b = π d → a = c ∧ b = d

namespace EdgeProjection
variable {H : SimpleGraph U} {G : SimpleGraph V} {π : U → V}

def edgeMap (h : EdgeProjection H G π) (e : EdgeState H) : EdgeState G :=
  ⟨(π e.src, π e.dst), h.map_adj _ _ e.adj⟩

end EdgeProjection

end CliqueFreeIndependence.WeightedGraph

end

end OAI


