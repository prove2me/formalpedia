-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
-- name    : OAI_Combinatorics_CliqueFree_LocalWalk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:02:17.996976+00:00
-- url     : https://prove2.me/theorems/4fc4ac9f-c224-408a-b4f7-786fab106e7e
-- title:
--   The neighbourhood random walk on oriented edges and its triangle-weighted law
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with adjacency $\sim$ and neighbourhoods $N(u)$, and let $w:V\to\mathbb{R}$ be a vertex weight (positive in applications). Write $c_w(u,v)=\sum_{z\in N(u)\cap N(v)}w(z)$ for the common neighbourhood mass, and let $\vec{E}(G)=\{(u,v)\in V\times V:\ u\sim v\}$ be the set of oriented edges, with $\mathrm{src}(u,v)=u$ and $\mathrm{dst}(u,v)=v$. The file defines the following.
--
--   1. **Transition kernel** on $\vec{E}(G)$: for $e=(u,v)$ and $f=(u',z)$,
--
--      $$P(e,f)=\begin{cases}\dfrac{w(z)}{c_w(u,v)} & \text{if } u'=u \text{ and } v\sim z,\\ 0 & \text{otherwise.}\end{cases}$$
--
--      From the state $(u,v)$ the walk stays in the neighbourhood of $u$ and moves from $v$ to a neighbour $z$ of $v$ inside $N(u)$, chosen with probability proportional to $w(z)$. Thus $P$ is the disjoint union, over $u\in V$, of weighted random walks on the induced subgraphs $G[N(u)]$.
--
--   2. **Normaliser**
--
--      $$Z=\sum_{(u,v)\in\vec{E}(G)}w(u)\,w(v)\,c_w(u,v),$$
--
--      which equals six times the weighted triangle mass $\sum w(a)w(b)w(c)$ over unordered triangles $\{a,b,c\}$.
--
--   3. **Law** $\mu(u,v)=w(u)\,w(v)\,c_w(u,v)/Z$ on $\vec{E}(G)$.
--
--   4. **Vertex weight on states** $\nu(u,v)=w(v)$, the weight of the current position of the walk.
--
--   5. **Fibre** of a vertex $u$: the set $\{e\in\vec{E}(G):\ \mathrm{src}(e)=u\}$ of states of the walk in the neighbourhood of $u$, with the membership rule $e$ in the fibre of $u$ iff $\mathrm{src}(e)=u$.
--
--   This walk converts weighted triangle sums into one-step expectations: for positive weights with positive common masses on all edges, a sum over ordered triangles of $w(a)w(b)w(c)$ times a function of the corner pair $\bigl((a,b),(a,c)\bigr)$ equals $Z$ times the expectation of that function over a step of the walk started from $\mu$. In the surrounding development $P$ is shown to be stochastic, and $\mu$ reversible for $P$, when $w>0$ and all common masses of adjacent pairs are positive; entropies of the rows of smoothed versions of $P$ are measured against $\nu$.
--
--   **Formalization Note** The Lean names are `LocalWalk.transition G w` (a `Kernel (EdgeState G)`), `normalizer`, `law`, `vertexWeight`, `fiber` and the simp lemma `mem_fiber`. With Lean's division by zero, a state $(u,v)$ with $c_w(u,v)=0$ has a zero row, and $\mu\equiv 0$ if $Z=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/LocalWalk.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/LocalWalk.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable (G : SimpleGraph V) (w : V → ℝ)

/-- The disjoint union of the neighborhood transition kernels. -/
noncomputable def transition : Kernel (EdgeState G) := fun e f ↦
  if e.src = f.src then
    if G.Adj e.dst f.dst then w f.dst / commonMass G w e.src e.dst else 0
  else 0

noncomputable def normalizer : ℝ :=
  ∑ e : EdgeState G, w e.src * w e.dst * commonMass G w e.src e.dst

noncomputable def law : EdgeState G → ℝ := fun e ↦
  (w e.src * w e.dst * commonMass G w e.src e.dst) / normalizer G w

noncomputable def vertexWeight : EdgeState G → ℝ := fun e ↦ w e.dst

noncomputable def fiber (u : V) : Finset (EdgeState G) := by
  classical
  exact univ.filter (fun e ↦ e.src = u)

@[simp] lemma mem_fiber (e : EdgeState G) (u : V) : e ∈ fiber G u ↔ e.src = u := by
  classical
  simp [fiber]

variable {G w}
end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI


