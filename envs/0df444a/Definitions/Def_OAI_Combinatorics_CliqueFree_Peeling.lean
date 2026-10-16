-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_Peeling
-- name    : OAI_Combinatorics_CliqueFree_Peeling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:11:35.955744+00:00
-- url     : https://prove2.me/theorems/0ce1497a-5256-4825-b5e2-3e4cd4c940ab
-- title:
--   Deleting a single edge from a simple graph
-- statement:
--   Let $G$ be a simple graph on a vertex set $V$ with adjacency $\sim_G$, and let $u,v\in V$. The graph $G-uv$ on the same vertex set has adjacency
--
--   $$a\sim_{G-uv}b\iff a\sim_G b\ \text{ and not }\ \bigl[(a=u\text{ and }b=v)\text{ or }(a=v\text{ and }b=u)\bigr].$$
--
--   It removes exactly the edge $\{u,v\}$ when this is an edge of $G$, and equals $G$ otherwise; the relation is symmetric and irreflexive, so $G-uv$ is again a simple graph.
--
--   Single-edge deletion is the basic move of a peeling argument for weighted graphs, with a vertex weight $w>0$ and a threshold $\tau>0$: an edge $\{u,v\}$ whose common neighbourhood mass $\sum_{z\sim u,\,z\sim v}w(z)$ is smaller than $\tau$ is worth deleting, because it carries little weighted triangle mass compared with its weight $w(u)w(v)$. In the surrounding development, comparing an extremal subgraph with such single-edge deletions produces a subgraph $H$ of $G$ in which every edge has common neighbourhood mass at least $\tau$, while the weighted triangle mass $\sum_{\{a,b,c\}}w(a)w(b)w(c)$ drops by at most $\tau$ times the weighted edge mass $\sum_{\{a,b\}\in E(G)}w(a)w(b)$.
--
--   **Formalization Note** The Lean name is `eraseEdge G u v`; symmetry and looplessness of the new adjacency relation are proved inline in the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Peeling.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Peeling.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling
import Definitions.Def_OAI_Combinatorics_CliqueFree_VertexSplitting

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

open FiniteCoupling
/-- Delete exactly one unordered edge. -/
def eraseEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬ (a = u ∧ b = v ∨ a = v ∧ b = u)
  symm := ⟨by
    intro a b h
    refine ⟨h.1.symm,?_⟩
    intro hab
    apply h.2
    rcases hab with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inr ⟨h2,h1⟩
    · exact Or.inl ⟨h2,h1⟩⟩
  loopless := ⟨fun a h ↦ G.irrefl h.1⟩

end CliqueFreeIndependence.WeightedGraph

end

end OAI


