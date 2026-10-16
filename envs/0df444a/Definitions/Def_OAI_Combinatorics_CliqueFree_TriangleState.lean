-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
-- name    : OAI_Combinatorics_CliqueFree_TriangleState
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:49:43.171708+00:00
-- url     : https://prove2.me/theorems/b3530de4-d112-471f-a945-16105b5e430b
-- title:
--   Ordered triangles, their symmetries, triangle weights and the corner-pair correspondence
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with adjacency $\sim$, and let $\vec{E}(G)=\{(u,v)\in V\times V:\ u\sim v\}$ be its set of oriented edges, with $\mathrm{src}(u,v)=u$ and $\mathrm{dst}(u,v)=v$. The file defines the following.
--
--   1. **Ordered triangles.** The finite set
--
--      $$\mathcal{T}(G)=\{(a,b,c)\in V^{3}:\ a\sim b,\ a\sim c,\ b\sim c\},$$
--
--      in which every triangle $\{a,b,c\}$ of $G$ appears $6$ times. A triangle $t=(a,b,c)$ has first, second and third vertices $a,b,c$ and oriented edges $e_{12}(t)=(a,b)$, $e_{13}(t)=(a,c)$ and $e_{23}(t)=(b,c)$.
--
--   2. **Symmetries.** The swap $(a,b,c)\mapsto(b,a,c)$, the rotation $(a,b,c)\mapsto(b,c,a)$ and the flip $(a,b,c)\mapsto(a,c,b)$. Each is a bijection of $\mathcal{T}(G)$; the swap and the flip are involutions and the inverse of the rotation is the rotation applied twice.
--
--   3. **Triangle weight.** For $w:V\to\mathbb{R}$, $w(t)=w(a)\,w(b)\,w(c)$, which is invariant under the swap, the rotation and the flip.
--
--   4. **Corner pairs.** The set
--
--      $$\mathcal{C}(G)=\{(e,f)\in\vec{E}(G)^{2}:\ \mathrm{src}(e)=\mathrm{src}(f),\ \mathrm{dst}(e)\sim\mathrm{dst}(f)\}$$
--
--      of pairs of oriented edges leaving a common corner whose endpoints are adjacent.
--
--   5. **Corner correspondence.** The bijection $\mathcal{T}(G)\to\mathcal{C}(G)$, $t\mapsto\bigl(e_{12}(t),e_{13}(t)\bigr)$, with inverse $(e,f)\mapsto\bigl(\mathrm{src}(e),\mathrm{dst}(e),\mathrm{dst}(f)\bigr)$.
--
--   Summing $w(t)$ over $\mathcal{T}(G)$ gives six times the weighted triangle mass $\sum_{\{a,b,c\}}w(a)w(b)w(c)$. The symmetries let a sum over ordered triangles be rewritten with the roles of the corners permuted, and the corner correspondence turns a triangle sum into a sum over pairs of states $\bigl((u,v),(u,z)\bigr)$ with $v\sim z$, i.e. over single steps of a random walk inside the neighbourhood of $u$.
--
--   **Formalization Note** `TriangleState G` is a subtype of `V × V × V` with `Fintype` instance `triangleStateFintype`, accessors `first`, `second`, `third`, adjacency lemmas `adj12`, `adj13`, `adj23` and oriented edges `edge12`, `edge13`, `edge23`. The symmetries are `swap`, `rotate`, `flip` with `Equiv`s `swapEquiv`, `rotateEquiv`, `flipEquiv`; `weight` comes with the simp lemmas `weight_swap`, `weight_rotate`, `weight_flip`. `CornerPairs G` is a subtype of pairs of `EdgeState G`, and `cornerEquiv` is the correspondence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/TriangleState.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/TriangleState.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

abbrev TriangleState (G : SimpleGraph V) :=
  {t : V × V × V // G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2}

noncomputable instance triangleStateFintype (G : SimpleGraph V) : Fintype (TriangleState G) :=
  Subtype.fintype _

namespace TriangleState
variable {G : SimpleGraph V}
def first (t : TriangleState G) : V := t.val.1
def second (t : TriangleState G) : V := t.val.2.1
def third (t : TriangleState G) : V := t.val.2.2

omit [Fintype V] in
@[simp] lemma adj12 (t : TriangleState G) : G.Adj t.first t.second := t.property.1
omit [Fintype V] in
@[simp] lemma adj13 (t : TriangleState G) : G.Adj t.first t.third := t.property.2.1
omit [Fintype V] in
@[simp] lemma adj23 (t : TriangleState G) : G.Adj t.second t.third := t.property.2.2

def edge12 (t : TriangleState G) : EdgeState G := ⟨(t.first, t.second), t.adj12⟩
def edge13 (t : TriangleState G) : EdgeState G := ⟨(t.first, t.third), t.adj13⟩
def edge23 (t : TriangleState G) : EdgeState G := ⟨(t.second, t.third), t.adj23⟩

def swap (t : TriangleState G) : TriangleState G :=
  ⟨(t.second, t.first, t.third), t.adj12.symm, t.adj23, t.adj13⟩
def rotate (t : TriangleState G) : TriangleState G :=
  ⟨(t.second, t.third, t.first), t.adj23, t.adj12.symm, t.adj13.symm⟩

def swapEquiv : TriangleState G ≃ TriangleState G where
  toFun := swap
  invFun := swap
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

def rotateEquiv : TriangleState G ≃ TriangleState G where
  toFun := rotate
  invFun := rotate ∘ rotate
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

noncomputable def weight (w : V → ℝ) (t : TriangleState G) : ℝ :=
  w t.first * w t.second * w t.third

omit [Fintype V] in
@[simp] lemma weight_swap (w : V → ℝ) (t : TriangleState G) :
    weight w (swap t) = weight w t := by unfold weight swap first second third; ring
omit [Fintype V] in
@[simp] lemma weight_rotate (w : V → ℝ) (t : TriangleState G) :
    weight w (rotate t) = weight w t := by unfold weight rotate first second third; ring

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}

def flip (t : TriangleState G) : TriangleState G :=
  ⟨(t.first, t.third, t.second), t.adj13, t.adj12, t.adj23.symm⟩

def flipEquiv : TriangleState G ≃ TriangleState G where
  toFun := flip
  invFun := flip
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

omit [Fintype V] in
@[simp] lemma weight_flip (w : V → ℝ) (t : TriangleState G) :
    weight w (flip t) = weight w t := by unfold weight flip first second third; ring

abbrev CornerPairs (G : SimpleGraph V) :=
  {p : EdgeState G × EdgeState G // p.1.src = p.2.src ∧ G.Adj p.1.dst p.2.dst}

def cornerEquiv : TriangleState G ≃ CornerPairs G where
  toFun t := ⟨(t.edge12, t.edge13), rfl, t.adj23⟩
  invFun p := ⟨(p.val.1.src, p.val.1.dst, p.val.2.dst), p.val.1.adj,
    by rw [p.property.1]; exact p.val.2.adj, p.property.2⟩
  left_inv t := by cases t; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Prod.ext p.property.1 rfl

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}
end TriangleState

end CliqueFreeIndependence.WeightedGraph

end

end OAI


