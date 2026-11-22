-- Prove2me | Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
-- name    : LeanPool_OrderClosures_WeaklyFatou_Bands
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:01:28.421341+00:00
-- url     : https://prove2.me/theorems/e9fdbd22-e5a0-4e42-8011-7c9021fa4d53
-- title:
--   Bands
-- statement:
--   Definitions and structural lemmas for Bands, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
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
public import Theorems.Thm_OrderConvergesTo_sup
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
abbrev TreeBandIndex (n : ℕ) := Option (TreeNonterminal n)
def treeBandSupport (n : ℕ) : TreeBandIndex n → Set (TreeNode n)
  | none => {TreeNode.root n}
  | some u => {t | TreeNode.parent t = u.1 ∧ t ≠ TreeNode.root n}
noncomputable def treeBandProjection (n : ℕ) (B : TreeBandIndex n)
    (w : TreeCoefficients n) : TreeCoefficients n :=
  by
    classical
    exact w.filter fun t ↦ t ∈ treeBandSupport n B
noncomputable def finiteBandProjection (n : ℕ) (Λ : Finset (TreeBandIndex n))
    (w : TreeCoefficients n) : TreeCoefficients n :=
  by
    classical
    exact w.filter fun t ↦ ∃ B ∈ Λ, t ∈ treeBandSupport n B
noncomputable def treeBandOfNode (n : ℕ) (t : TreeNode n) : TreeBandIndex n :=
  by
    classical
    exact if h : t = TreeNode.root n then none else
      some ⟨TreeNode.parent t, by
        have htpos : 0 < TreeNode.level t := Nat.pos_of_ne_zero fun hzero ↦ h (by
          apply Subtype.ext
          have hnil : t.1 = [] := List.length_eq_zero_iff.mp (by
            simpa [TreeNode.level] using hzero)
          simpa [TreeNode.root] using hnil)
        have hp : TreeNode.level (TreeNode.parent t) = TreeNode.level t - 1 := by
          simp [TreeNode.parent, TreeNode.level]
        have htn : TreeNode.level t ≤ n := t.2
        omega⟩
noncomputable def bandsAt (n : ℕ) (w : TreeCoefficients n) :
    Finset (TreeBandIndex n) := by
  classical
  exact w.support.image (treeBandOfNode n)
noncomputable def treeBandParent (n : ℕ) : TreeBandIndex n → TreeNode n
  | none => TreeNode.root n
  | some u => u.1
noncomputable def treeUpshift (n : ℕ) (w : TreeCoefficients n) : TreeCoefficients n :=
  w.mapDomain TreeNode.parent
noncomputable def treeBandParents (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) : Finset (TreeNode n) := by
  classical
  exact Λ.image (treeBandParent n)
def recurrentBands (n : ℕ) (w : ℕ → TreeCoefficients n) : Set (TreeBandIndex n) :=
  {B | Set.Infinite {m | (treeBandProjection n B (w m)).support.Nonempty}}
noncomputable def lastBandOccurrence (n : ℕ)
    (w : ℕ → TreeCoefficients n) (B : TreeBandIndex n) : ℕ := by
  classical
  let S : Set ℕ := {m | (treeBandProjection n B (w m)).support.Nonempty}
  exact if h : S.Finite then h.toFinset.sup id else 0
end OrderClosures


