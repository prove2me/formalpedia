-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
-- name    : OAI_Combinatorics_SecondNeighborhood_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:40:35.065529+00:00
-- url     : https://prove2.me/theorems/d0f5099b-27c6-43b2-97c1-7e323a764727
-- title:
--   Out-images of vertex sets and the second neighbourhood conjecture predicate
-- statement:
--   Let $V$ be a finite set and $r$ a relation on $V$, read as a directed graph with an arc $x\to y$ when $r(x,y)$. It is oriented if it has no loops and no pair of opposite arcs. $N^+(v)=\{w:v\to w\}$ is the first (out-)neighbourhood, and $N^{++}(v)$ is the second neighbourhood: the vertices $w\ne v$ with $w\notin N^+(v)$ that are reached by a path $v\to u\to w$. A vertex $v$ is good if $|N^+(v)|\le|N^{++}(v)|$.
--
--   1. **Out-image.** For $S\subseteq V$, $r(S)=\{y:\exists x\in S,\ x\to y\}$. Then $r(\emptyset)=\emptyset$, $r(\{v\})=N^+(v)$ and $r(S\cup T)=r(S)\cup r(T)$.
--   2. **The conjecture predicate.** The second neighbourhood property of $r$ is the existence of a good vertex.
--   3. **Membership.** $w\in N^+(v)$ iff $v\to w$; $w\in N^{++}(v)$ iff $w\ne v$, $v\not\to w$, and $v\to u\to w$ for some $u$. For an oriented graph, $v\notin N^+(v)$, and always $v\notin N^{++}(v)$.
--
--   Seymour's second neighbourhood conjecture asserts that every finite oriented graph has a good vertex. The set-image operator $r(\cdot)$ lets this be generalized from single vertices to arbitrary vertex sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SeymourSecondNeighborhood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*}

variable [Fintype V] [DecidableEq V]

noncomputable section

def image (r : V → V → Prop) (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun y => ∃ x ∈ S, r x y)

def SecondNeighborhoodConjecture (r : V → V → Prop) : Prop :=
  ∃ v, GoodVertex r v

omit [DecidableEq V] in
@[simp] theorem mem_image {r : V → V → Prop} {S : Finset V} {y : V} :
    y ∈ image r S ↔ ∃ x ∈ S, r x y := by
  classical
  simp [image]

omit [DecidableEq V] in
@[simp] theorem mem_firstNeighbors {r : V → V → Prop} {v w : V} :
    w ∈ firstNeighbors r v ↔ r v w := by
  classical
  simp [firstNeighbors]

@[simp] theorem mem_secondNeighbors {r : V → V → Prop} {v w : V} :
    w ∈ secondNeighbors r v ↔ w ≠ v ∧ ¬ r v w ∧ ∃ u, r v u ∧ r u w := by
  classical
  simp [secondNeighbors]

omit [DecidableEq V] in
@[simp] theorem image_empty (r : V → V → Prop) : image r ∅ = ∅ := by
  classical
  ext y
  simp

omit [DecidableEq V] in
@[simp] theorem image_singleton (r : V → V → Prop) (v : V) :
    image r {v} = firstNeighbors r v := by
  classical
  ext y
  simp

@[simp] theorem image_union (r : V → V → Prop) (S T : Finset V) :
    image r (S ∪ T) = image r S ∪ image r T := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := mem_image.mp hy
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union.mpr (Or.inl (mem_image.mpr ⟨x, hx, hxy⟩))
    · exact Finset.mem_union.mpr (Or.inr (mem_image.mpr ⟨x, hx, hxy⟩))
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨x, hx, hxy⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨x, Finset.mem_union.mpr (Or.inl hx), hxy⟩
    · obtain ⟨x, hx, hxy⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨x, Finset.mem_union.mpr (Or.inr hx), hxy⟩

omit [DecidableEq V] in
@[simp] theorem self_not_mem_firstNeighbors {r : V → V → Prop}
    (hr : IsOriented r) (v : V) : v ∉ firstNeighbors r v := by
  intro hv
  exact hr.loopless v (mem_firstNeighbors.mp hv)

@[simp] theorem self_not_mem_secondNeighbors (r : V → V → Prop) (v : V) :
    v ∉ secondNeighbors r v := by
  intro hv
  exact (mem_secondNeighbors.mp hv).1 rfl

end
end SeymourSecondNeighborhood

end OAI


