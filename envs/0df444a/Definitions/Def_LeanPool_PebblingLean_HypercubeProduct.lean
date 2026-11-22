-- Prove2me | Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
-- name    : LeanPool_PebblingLean_HypercubeProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:53:31.179794+00:00
-- url     : https://prove2.me/theorems/d952a38d-6f3d-41e0-adce-dfcdaf4d439c
-- title:
--   Hypercube Product
-- statement:
--   Definitions and structural lemmas for Hypercube Product, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean

module
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finite.Prod
public import Mathlib.Tactic.Bound.Init
public import Theorems.Thm_PebblingLean_Hypercube_dist_eq_zero_iff
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
def splitVertex (a m : ℕ) (v : HypercubeVertex (a + m)) :
    HypercubeVertex a × HypercubeVertex m :=
  (fun i => v (Fin.castAdd m i), fun j => v (Fin.natAdd a j))
def appendVertex {a m : ℕ}
    (p : HypercubeVertex a × HypercubeVertex m) : HypercubeVertex (a + m) :=
  Fin.append p.1 p.2
def splitVertexEquiv (a m : ℕ) :
    HypercubeVertex (a + m) ≃ HypercubeVertex a × HypercubeVertex m where
  toFun := splitVertex a m
  invFun := appendVertex
  left_inv := by
    intro v
    exact Fin.append_castAdd_natAdd
  right_inv := by
    intro p
    ext i <;> simp [splitVertex, appendVertex]
@[simp]
theorem splitVertexEquiv_apply (a m : ℕ) (v : HypercubeVertex (a + m)) :
    splitVertexEquiv a m v = splitVertex a m v :=
  rfl
@[simp]
theorem splitVertexEquiv_symm_apply {a m : ℕ}
    (p : HypercubeVertex a × HypercubeVertex m) :
    (splitVertexEquiv a m).symm p = appendVertex p :=
  rfl
theorem dist_appendVertex {a m : ℕ}
    (x x' : HypercubeVertex a) (z z' : HypercubeVertex m) :
    dist (appendVertex (x, z)) (appendVertex (x', z')) =
      dist x x' + dist z z' := by
  classical
  let leftDiff : Finset (Fin (a + m)) :=
    (Finset.univ.filter fun i : Fin a => x i ≠ x' i).map (Fin.castAddEmb m)
  let rightDiff : Finset (Fin (a + m)) :=
    (Finset.univ.filter fun j : Fin m => z j ≠ z' j).map (Fin.natAddEmb a)
  have hdiff :
      (Finset.univ.filter fun k : Fin (a + m) =>
        appendVertex (x, z) k ≠ appendVertex (x', z') k) =
        leftDiff ∪ rightDiff := by
    ext k
    induction k using Fin.addCases with
    | left i =>
        have hnot_right : Fin.castAdd m i ∉ rightDiff := by
          intro hk
          rcases Finset.mem_map.mp hk with ⟨j, _hj, hj_eq⟩
          have hlt : ((Fin.castAdd m i : Fin (a + m)) : ℕ) < a := i.isLt
          have hge : a ≤ ((Fin.castAdd m i : Fin (a + m)) : ℕ) := by
            rw [← hj_eq]
            exact Nat.le_add_right a j
          exact (Nat.not_lt_of_ge hge) hlt
        have happend : appendVertex (x, z) (Fin.castAdd m i) = x i :=
          Fin.append_left x z i
        have happend' : appendVertex (x', z') (Fin.castAdd m i) = x' i :=
          Fin.append_left x' z' i
        simp [leftDiff, rightDiff, hnot_right, happend, happend']
    | right j =>
        have hnot_left : Fin.natAdd a j ∉ leftDiff := by
          intro hk
          rcases Finset.mem_map.mp hk with ⟨i, _hi, hi_eq⟩
          have hge : a ≤ ((Fin.natAdd a j : Fin (a + m)) : ℕ) :=
            Nat.le_add_right a j
          have hlt : ((Fin.natAdd a j : Fin (a + m)) : ℕ) < a := by
            rw [← hi_eq]
            exact i.isLt
          exact (Nat.not_lt_of_ge hge) hlt
        have happend : appendVertex (x, z) (Fin.natAdd a j) = z j :=
          Fin.append_right x z j
        have happend' : appendVertex (x', z') (Fin.natAdd a j) = z' j :=
          Fin.append_right x' z' j
        simp [leftDiff, rightDiff, hnot_left, happend, happend']
  have hdisjoint : Disjoint leftDiff rightDiff := by
    rw [Finset.disjoint_left]
    intro k hk_left hk_right
    rcases Finset.mem_map.mp hk_left with ⟨i, _hi, hi_eq⟩
    rcases Finset.mem_map.mp hk_right with ⟨j, _hj, hj_eq⟩
    have hlt : (k : ℕ) < a := by
      rw [← hi_eq]
      exact i.isLt
    have hge : a ≤ (k : ℕ) := by
      rw [← hj_eq]
      exact Nat.le_add_right a j
    exact (Nat.not_lt_of_ge hge) hlt
  unfold dist
  rw [hdiff, Finset.card_union_of_disjoint hdisjoint]
  simp [leftDiff, rightDiff]
theorem appendVertex_adj_iff {a m : ℕ}
    (p q : HypercubeVertex a × HypercubeVertex m) :
    (graph (a + m)).Adj (appendVertex p) (appendVertex q) ↔
      (Graph.cartesianProduct (graph a) (graph m)).Adj p q := by
  constructor
  · intro h
    change dist (appendVertex p) (appendVertex q) = 1 at h
    rw [dist_appendVertex] at h
    rcases Nat.add_eq_one_iff.mp h with hcase | hcase
    · exact Or.inr ⟨dist_eq_zero_iff.mp hcase.1, hcase.2⟩
    · exact Or.inl ⟨hcase.1, dist_eq_zero_iff.mp hcase.2⟩
  · intro h
    change dist (appendVertex p) (appendVertex q) = 1
    rw [dist_appendVertex]
    rcases h with hleft | hright
    · rw [hleft.1, hleft.2, dist_self, Nat.add_zero]
    · rw [hright.1, dist_self, hright.2, Nat.zero_add]
theorem splitVertex_adj_iff {a m : ℕ} {v w : HypercubeVertex (a + m)} :
    (graph (a + m)).Adj v w ↔
      (Graph.cartesianProduct (graph a) (graph m)).Adj
        (splitVertex a m v) (splitVertex a m w) := by
  have hv : appendVertex (splitVertex a m v) = v :=
    (splitVertexEquiv a m).left_inv v
  have hw : appendVertex (splitVertex a m w) = w :=
    (splitVertexEquiv a m).left_inv w
  simpa [hv, hw] using
    appendVertex_adj_iff (p := splitVertex a m v) (q := splitVertex a m w)
def splitGraphIso (a m : ℕ) :
    GraphIso (graph (a + m)) (Graph.cartesianProduct (graph a) (graph m)) where
  toEquiv := splitVertexEquiv a m
  adj_iff := by
    intro v w
    exact splitVertex_adj_iff
end Hypercube
end PebblingLean


