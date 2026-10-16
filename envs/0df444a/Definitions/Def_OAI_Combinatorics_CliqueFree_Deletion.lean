-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
-- name    : OAI_Combinatorics_CliqueFree_Deletion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:45:38.363873+00:00
-- url     : https://prove2.me/theorems/e4cf2bb6-5c4e-4c2b-a244-5d98f511b9d6
-- title:
--   Closed neighbourhood of a vertex
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with adjacency $\sim$ and open neighbourhoods $N(v)=\{u\in V:\ v\sim u\}$. The closed neighbourhood of a vertex $v$ is
--
--   $$N[v]=\{v\}\cup N(v),$$
--
--   and membership is characterised by: $u\in N[v]$ if and only if $u=v$ or $v\sim u$.
--
--   Closed neighbourhoods are what greedy constructions of independent sets delete after selecting a vertex. In the weighted argument, with a vertex weight $w$, the weighted edge mass of $G$ restricted to $N[v]$ splits as $w(v)\,w(N(v))$ plus half of the local triangle mass $T_w(v)=\sum_{u\in N(v)}w(u)\,w\bigl(N(u)\cap N(v)\bigr)$, which is how the cost of deleting $N[v]$ from a weighted graph is measured.
--
--   **Formalization Note** `closedNeighbors G v` is defined as `insert v (neighbors G v)` with classical decidable equality, and `mem_closedNeighbors` is its simp membership lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Deletion.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Deletion.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

noncomputable def closedNeighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact insert v (neighbors G v)

@[simp] lemma mem_closedNeighbors (G : SimpleGraph V) (u v : V) :
    u ∈ closedNeighbors G v ↔ u = v ∨ G.Adj v u := by
  classical
  simp [closedNeighbors]

 -- the two expressions are definitionally the sums

end CliqueFreeIndependence.WeightedGraph

end

end OAI


