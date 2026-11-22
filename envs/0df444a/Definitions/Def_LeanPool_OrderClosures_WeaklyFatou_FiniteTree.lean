-- Prove2me | Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
-- name    : LeanPool_OrderClosures_WeaklyFatou_FiniteTree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:55:58.647059+00:00
-- url     : https://prove2.me/theorems/1cbb1abb-6bb5-4fe7-a2e4-05bd458f6ac2
-- title:
--   Finite Tree
-- statement:
--   Definitions and structural lemmas for Finite Tree, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FiniteTree.lean

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval
attribute [local simp] Positive.extension_apply
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] coe_toCompletionVecLatHom


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
abbrev TreeNode (n : ℕ) := {t : List ℕ // t.length ≤ n}
namespace TreeNode
abbrev level {n : ℕ} (t : TreeNode n) : ℕ := t.1.length
def root (n : ℕ) : TreeNode n := ⟨[], by simp⟩
def child {n : ℕ} (t : TreeNode n) (h : level t < n) (m : ℕ) : TreeNode n :=
  ⟨t.1 ++ [m], by
    simpa [level] using h⟩
def parent {n : ℕ} (t : TreeNode n) : TreeNode n :=
  ⟨t.1.dropLast, by
    rw [List.length_dropLast]
    exact (Nat.sub_le _ _).trans t.2⟩
def restrict {n : ℕ} (t : TreeNode n) (j : ℕ) : TreeNode n :=
  ⟨t.1.take j, by
    rw [List.length_take]
    exact (min_le_right _ _).trans t.2⟩
end TreeNode
abbrev TreeNonterminal (n : ℕ) := {t : TreeNode n // TreeNode.level t < n}
abbrev TreeProduct (n : ℕ) := TreeNonterminal n → ℕ
def strictPrefix {n : ℕ} (t : TreeNode n) (j : Fin (TreeNode.level t)) :
    TreeNonterminal n :=
  ⟨TreeNode.restrict t j, by
    calc
      (TreeNode.restrict t j).level ≤ j := List.length_take_le _ _
      _ < TreeNode.level t := j.isLt
      _ ≤ n := t.2⟩
def treeCylinder (n : ℕ) (t : TreeNode n) : Set (TreeProduct n) :=
  {α | ∀ j : Fin (TreeNode.level t), α (strictPrefix t j) ≤ t.1.get j}
theorem treeCylinder_isClopen (n : ℕ) (t : TreeNode n) :
    IsClopen (treeCylinder n t) := by
  rw [show treeCylinder n t =
      ⋂ j : Fin (TreeNode.level t),
        {α | α (strictPrefix t j) ≤ t.1.get j} by
    ext α
    simp [treeCylinder]]
  apply isClopen_iInter_of_finite
  intro j
  exact (isClopen_discrete {m : ℕ | m ≤ t.1.get j}).preimage
    (continuous_apply (strictPrefix t j))
noncomputable def treeFunction (n : ℕ) (t : TreeNode n) :
    BoundedContinuousFunction (TreeProduct n) ℝ :=
  BoundedContinuousFunction.indicator (treeCylinder n t) (treeCylinder_isClopen n t)
noncomputable instance boundedContinuousFunctionNormedVectorLattice
    (A : Type u) [TopologicalSpace A] :
    NormedVectorLattice (BoundedContinuousFunction A ℝ) where
  smul_le_smul_of_nonneg_left := by
    intro a ha f g h p
    exact mul_le_mul_of_nonneg_left (h p) ha
def ParentDisjoint {n : ℕ} (A B : Set (TreeNode n)) : Prop :=
  TreeNode.parent '' A ∩ TreeNode.parent '' B = ∅
def finiteCylinderUnion (n : ℕ) (F : Finset (TreeNode n)) : Set (TreeProduct n) :=
  ⋃ t : F, treeCylinder n t.1
noncomputable def finiteTreeSup (n : ℕ) (F : Finset (TreeNode n)) :
    BoundedContinuousFunction (TreeProduct n) ℝ :=
  BoundedContinuousFunction.indicator (finiteCylinderUnion n F) (by
    apply isClopen_iUnion_of_finite
    exact fun t ↦ treeCylinder_isClopen n t.1)
def treeLastLabel {n : ℕ} (t : TreeNode n) : ℕ :=
  if h : 0 < TreeNode.level t then
    t.1.get ⟨TreeNode.level t - 1, Nat.sub_lt h (by omega)⟩ else 0
end OrderClosures


