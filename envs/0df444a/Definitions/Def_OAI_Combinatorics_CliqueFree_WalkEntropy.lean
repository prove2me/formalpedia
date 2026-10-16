-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
-- name    : OAI_Combinatorics_CliqueFree_WalkEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:03:54.881366+00:00
-- url     : https://prove2.me/theorems/5d04b334-4622-47f0-8642-3d6a5a7f7c14
-- title:
--   Lifted neighbourhood sets and the average row distance of the smoothed neighbourhood walk
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with adjacency $\sim$ and neighbourhoods $N(u)$, let $w:V\to\mathbb{R}$ be a vertex weight, and let $\vec{E}(G)=\{(u,v):\ u\sim v\}$ be the set of oriented edges with $\mathrm{src}(u,v)=u$, $\mathrm{dst}(u,v)=v$. Let $P$ be the neighbourhood walk on $\vec{E}(G)$, $P\bigl((u,v),(u,z)\bigr)=w(z)/c_w(u,v)$ when $v\sim z$ and $P(e,f)=0$ for all other pairs, where $c_w(u,v)=\sum_{z\in N(u)\cap N(v)}w(z)$. Let $\mu(u,v)=w(u)w(v)c_w(u,v)/Z$ be its law, with $Z=\sum_{(u,v)\in\vec{E}(G)}w(u)w(v)c_w(u,v)$. Write $P^{(n)}=P\bigl(\tfrac12(\mathrm{Id}+P)\bigr)^{n}$ for the smoothed kernels and $d_{\mathrm{TV}}(p,q)=\tfrac12\sum_i|p_i-q_i|$. The file defines:
--
--   1. **Lift** of a set $A\subseteq V$ to the fibre over $u\in V$:
--
--      $$\widehat{A}_u=\{e\in\vec{E}(G):\ \mathrm{src}(e)=u,\ \mathrm{dst}(e)\in A\},$$
--
--      the states of the walk in the neighbourhood of $u$ whose position lies in $A$.
--
--   2. **Row distance** at smoothing level $n\in\mathbb{N}$:
--
--      $$\rho(n)=\sum_{e\in\vec{E}(G)}\mu(e)\sum_{f\in\vec{E}(G)}P(e,f)\;d_{\mathrm{TV}}\bigl(P^{(n)}(e,\cdot),\,P^{(n)}(f,\cdot)\bigr),$$
--
--      the expected total-variation distance between the smoothed rows at the two ends of one step of the walk started from $\mu$.
--
--   A small row distance says that the smoothed rows at adjacent states are nearly equal. This is the quantity controlled by an entropy-smoothing estimate, which yields a level $n$ with $\rho(n)$ of order $\sqrt{\log x/x}$ at scale $x$, and it is what allows the random choices made at the corners of a triangle during vertex splitting to be coupled. Lifted sets transport vertex sets, such as reach sets, into the fibres of the walk in order to bound how much of the walk leaves them.
--
--   **Formalization Note** The Lean names are `LocalWalk.liftSet u A` (with the graph implicit), its simp lemma `mem_liftSet`, and `LocalWalk.rowDistance n` (with `G` and `w` implicit), built from `transition`, `law`, `smoothed` and `tv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/WalkEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/WalkEntropy.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
variable {G : SimpleGraph V} {w : V → ℝ}

noncomputable def liftSet (u : V) (A : Finset V) : Finset (EdgeState G) :=
  univ.filter (fun e ↦ e.src = u ∧ e.dst ∈ A)

@[simp] lemma mem_liftSet (u : V) (A : Finset V) (e : EdgeState G) :
    e ∈ liftSet (G := G) u A ↔ e.src = u ∧ e.dst ∈ A := by simp [liftSet]

noncomputable def rowDistance (n : ℕ) : ℝ :=
  ∑ e : EdgeState G, law G w e * ∑ f, transition G w e f *
    tv (smoothed (transition G w) n e) (smoothed (transition G w) n f)

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI


