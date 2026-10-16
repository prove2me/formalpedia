-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
-- name    : OAI_Combinatorics_CliqueFree_EdgeState
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:47:48.721368+00:00
-- url     : https://prove2.me/theorems/dcf799f4-5f07-474e-b015-c0f5a1a1cbd6
-- title:
--   Oriented edges of a graph and edge reversal
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with adjacency $\sim$ and neighbourhoods $N(u)=\{v:\ u\sim v\}$. The file defines the following.
--
--   1. **Oriented edges (edge states).** The finite set
--
--      $$\vec{E}(G)=\{(u,v)\in V\times V:\ u\sim v\},$$
--
--      which contains every edge $\{u,v\}$ of $G$ twice, once in each direction, so $|\vec{E}(G)|=2|E(G)|$. For $e=(u,v)$ write $\mathrm{src}(e)=u$ and $\mathrm{dst}(e)=v$; always $\mathrm{src}(e)\sim\mathrm{dst}(e)$. Grouping by source gives the disjoint decomposition $\vec{E}(G)=\bigsqcup_{u\in V}\{u\}\times N(u)$ into copies of the neighbourhoods.
--
--   2. **Reversal** $\overline{(u,v)}=(v,u)$. It satisfies $\mathrm{src}(\bar e)=\mathrm{dst}(e)$, $\mathrm{dst}(\bar e)=\mathrm{src}(e)$ and $\bar{\bar e}=e$, and is therefore an involutive permutation of $\vec{E}(G)$.
--
--   The file also records that the growth function $g_x(s)=s\,\bigl(x+\max\{0,\log(1/s)\}\bigr)$ satisfies $g_x(0)=0$ for every real $x$.
--
--   Oriented edges are the state space of the random walk inside neighbourhoods, whose states with source $u$ are the neighbours of $u$, and they are the vertex set of the graph produced by vertex splitting, in which every vertex $u$ is replaced by copies indexed by the oriented edges leaving $u$. Reversal pairs the two orientations of an edge and is used to reindex sums over oriented edges.
--
--   **Formalization Note** `EdgeState G` is the subtype `{e : V × V // G.Adj e.1 e.2}`, with the `Fintype` instance `edgeStateFintype` and a classical `DecidableEq` instance `edgeStateDecEq`. The accessors are `src` and `dst`; `rev` is the reversal and `revEquiv` the corresponding `Equiv`; `adj`, `src_rev`, `dst_rev`, `rev_rev` and `growth_zero` are simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/EdgeState.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/EdgeState.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

/-- Oriented edges, the disjoint union of the neighborhood state spaces. -/
abbrev EdgeState (G : SimpleGraph V) := {e : V × V // G.Adj e.1 e.2}

noncomputable instance edgeStateFintype (G : SimpleGraph V) : Fintype (EdgeState G) :=
  Subtype.fintype _

local instance (priority := 10000) edgeStateDecEq (G : SimpleGraph V) : DecidableEq (EdgeState G) :=
  Classical.decEq _

namespace EdgeState
variable {G : SimpleGraph V}
def src (e : EdgeState G) : V := e.val.1
def dst (e : EdgeState G) : V := e.val.2
omit [Fintype V] in
@[simp] lemma adj (e : EdgeState G) : G.Adj e.src e.dst := e.property

def rev (e : EdgeState G) : EdgeState G := ⟨(e.dst, e.src), e.adj.symm⟩
omit [Fintype V] in
@[simp] lemma src_rev (e : EdgeState G) : e.rev.src = e.dst := rfl
omit [Fintype V] in
@[simp] lemma dst_rev (e : EdgeState G) : e.rev.dst = e.src := rfl
omit [Fintype V] in
@[simp] lemma rev_rev (e : EdgeState G) : e.rev.rev = e := by cases e; rfl

def revEquiv : EdgeState G ≃ EdgeState G where
  toFun := rev
  invFun := rev
  left_inv := rev_rev
  right_inv := rev_rev

end EdgeState

@[simp] lemma growth_zero (x : ℝ) : growth x 0 = 0 := by simp [growth]

end CliqueFreeIndependence.WeightedGraph

end

end OAI


