-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Semantics_Median
-- name    : LeanPool_DeciSigma1_Semantics_Median
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:25:21.205481+00:00
-- url     : https://prove2.me/theorems/ac038ece-c065-4e5f-b284-66f4f2f274a1
-- title:
--   Median
-- statement:
--   Definitions and structural lemmas for Median, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Data.List.Induction
public import Mathlib.Order.MinMax
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike
public import Theorems.Thm_DeciSigma1_Constraints_base_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_dual_eq_bot
public import Theorems.Thm_DeciSigma1_Constraints_dual_eq_top
public import Theorems.Thm_DeciSigma1_Constraints_holdsT_map
public import Theorems.Thm_DeciSigma1_Constraints_holds_false
public import Theorems.Thm_DeciSigma1_Constraints_normalize_false_eq_bot
public import Theorems.Thm_DeciSigma1_Constraints_normalize_false_eq_top
public import Theorems.Thm_DeciSigma1_Constraints_normalize_not
public import Theorems.Thm_DeciSigma1_Constraints_normalized_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Constraints_sat_signed_iff
public import Theorems.Thm_DeciSigma1_Constraints_sign_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_signedDual_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_signedVar_base_sign
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_eq_bot_or_eq_top_or_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_append
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_cons
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_eq_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_eq_top_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_top
public import Theorems.Thm_DeciSigma1_Semantics_bot_treeLe
public import Theorems.Thm_DeciSigma1_Semantics_dual_bot
public import Theorems.Thm_DeciSigma1_Semantics_dual_fn
public import Theorems.Thm_DeciSigma1_Semantics_dual_involutive
public import Theorems.Thm_DeciSigma1_Semantics_dual_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_dual_node
public import Theorems.Thm_DeciSigma1_Semantics_dual_top
public import Theorems.Thm_DeciSigma1_Semantics_isLivePrefix_append_singleton
public import Theorems.Thm_DeciSigma1_Semantics_le_iff_forall_hasLabel
public import Theorems.Thm_DeciSigma1_Semantics_node_treeLe_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_normalize_bot
public import Theorems.Thm_DeciSigma1_Semantics_normalize_false_variance
public import Theorems.Thm_DeciSigma1_Semantics_normalize_fn
public import Theorems.Thm_DeciSigma1_Semantics_normalize_involutive
public import Theorems.Thm_DeciSigma1_Semantics_normalize_node
public import Theorems.Thm_DeciSigma1_Semantics_normalize_top
public import Theorems.Thm_DeciSigma1_Semantics_normalize_true
public import Theorems.Thm_DeciSigma1_Semantics_top_treeLe_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_false_iff_le
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_top
attribute [local simp] DeciSigma1.Constraints.base_signedVar
attribute [local simp] DeciSigma1.Constraints.dual_eq_bot
attribute [local simp] DeciSigma1.Constraints.dual_eq_top
attribute [local simp] DeciSigma1.Constraints.holdsT_map
attribute [local simp] DeciSigma1.Constraints.holds_false
attribute [local simp] DeciSigma1.Constraints.normalize_false_eq_bot
attribute [local simp] DeciSigma1.Constraints.normalize_false_eq_top
attribute [local simp] DeciSigma1.Constraints.normalize_not
attribute [local simp] DeciSigma1.Constraints.normalized_signedVar
attribute [local simp] DeciSigma1.Constraints.sat_false
attribute [local simp] DeciSigma1.Constraints.sat_signed_iff
attribute [local simp] DeciSigma1.Constraints.sign_signedVar
attribute [local simp] DeciSigma1.Constraints.signedDual_signedVar
attribute [local simp] DeciSigma1.Constraints.signedVar_base_sign
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_dual
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_normalize
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.descend_bot
attribute [local simp] DeciSigma1.Semantics.Tree.descend_node
attribute [local simp] DeciSigma1.Semantics.Tree.descend_top
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_bot
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_nil
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_top
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_top
attribute [local simp] DeciSigma1.Semantics.Tree.node_le_node_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff
attribute [local simp] DeciSigma1.Semantics.Tree.trace_bot
attribute [local simp] DeciSigma1.Semantics.Tree.trace_cons
attribute [local simp] DeciSigma1.Semantics.Tree.trace_nil
attribute [local simp] DeciSigma1.Semantics.Tree.trace_top
attribute [local simp] DeciSigma1.Semantics.bot_treeLe
attribute [local simp] DeciSigma1.Semantics.dual_bot
attribute [local simp] DeciSigma1.Semantics.dual_fn
attribute [local simp] DeciSigma1.Semantics.dual_involutive
attribute [local simp] DeciSigma1.Semantics.dual_le_iff
attribute [local simp] DeciSigma1.Semantics.dual_node
attribute [local simp] DeciSigma1.Semantics.dual_top
attribute [local simp] DeciSigma1.Semantics.node_treeLe_node_iff
attribute [local simp] DeciSigma1.Semantics.normalize_bot
attribute [local simp] DeciSigma1.Semantics.normalize_false_variance
attribute [local simp] DeciSigma1.Semantics.normalize_fn
attribute [local simp] DeciSigma1.Semantics.normalize_involutive
attribute [local simp] DeciSigma1.Semantics.normalize_node
attribute [local simp] DeciSigma1.Semantics.normalize_top
attribute [local simp] DeciSigma1.Semantics.normalize_true
attribute [local simp] DeciSigma1.Semantics.top_treeLe_iff
attribute [local simp] DeciSigma1.Semantics.treeLe_bot_iff
attribute [local simp] DeciSigma1.Semantics.treeLe_false_iff_le
attribute [local simp] DeciSigma1.Semantics.treeLe_top


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
def extendedLabel (t : Tree n) (w : List (Fin n)) : Sym :=
  ((Tree.trace t w).fn []).getD .f
@[simp] theorem extendedLabel_bot (w : List (Fin n)) :
    extendedLabel Tree.bot w = .bot := by simp [extendedLabel]
@[simp] theorem extendedLabel_top (w : List (Fin n)) :
    extendedLabel Tree.top w = .top := by simp [extendedLabel]
@[simp] theorem extendedLabel_node_nil (a : Fin n → Tree n) :
    extendedLabel (Tree.node a) [] = .f := rfl
@[simp] theorem extendedLabel_node_cons (a : Fin n → Tree n) (i : Fin n) (w : List (Fin n)) :
    extendedLabel (Tree.node a) (i :: w) = extendedLabel (a i) w := by
  simp [extendedLabel]
theorem extendedLabel_step (t : Tree n) (w : List (Fin n)) (i : Fin n) :
    extendedLabel t (w ++ [i]) = (t.fn (w ++ [i])).getD (extendedLabel t w) := by
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · simp [extendedLabel]
  | cons j w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · simpa using ih (t := a j)
@[simp] theorem hasLabel_top_iff_extendedLabel (w : List (Fin n)) (t : Tree n) :
    t.HasLabel w .top ↔ extendedLabel t w = .top := by
  rw [← Tree.trace_eq_top_iff]
  rcases (Tree.trace t w).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩ <;>
    simp [extendedLabel, h]
@[simp] theorem hasLabel_bot_iff_extendedLabel (w : List (Fin n)) (t : Tree n) :
    t.HasLabel w .bot ↔ extendedLabel t w = .bot := by
  rw [← Tree.trace_eq_bot_iff]
  rcases (Tree.trace t w).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩ <;>
    simp [extendedLabel, h]
theorem le_iff_extendedLabel (t u : Tree n) :
    t ≤ u ↔ ∀ w, extendedLabel t w ≤ extendedLabel u w := by
  rw [le_iff_forall_hasLabel]
  simp only [hasLabel_top_iff_extendedLabel, hasLabel_bot_iff_extendedLabel]
  have hs (a b : Sym) : ((a = .top → b = .top) ∧ (b = .bot → a = .bot)) ↔ a ≤ b := by
    cases a <;> cases b <;> decide
  simp only [hs]
theorem extendedLabel_injective : Function.Injective (@extendedLabel n) := by
  intro a b h
  apply _root_.le_antisymm <;> apply (le_iff_extendedLabel _ _).mpr <;> intro w <;> rw [h]
theorem extendedLabel_absorb (t : Tree n) (w v : List (Fin n)) (h : extendedLabel t w ≠ .f) :
    extendedLabel t (w ++ v) = extendedLabel t w := by
  rcases (Tree.trace t w).eq_bot_or_eq_top_or_node with ht | ht | ⟨a, ht⟩
  · simp [extendedLabel, Tree.trace_append, ht]
  · simp [extendedLabel, Tree.trace_append, ht]
  · simp [extendedLabel, ht] at h
@[simp] theorem extendedLabel_dual (t : Tree n) (w : List (Fin n)) :
    extendedLabel (dual t) w = Sym.flip true (extendedLabel t w) := by
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩ <;> simp [Sym.flip]
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp [Sym.flip]
    · simp [Sym.flip]
    · simp [ih]
def medianSym (a b c : Sym) : Sym := max (min a b) (min (max a b) c)
@[simp] theorem medianSym_self (a c : Sym) : medianSym a a c = a := by
  cases a <;> cases c <;> decide
theorem medianSym_absorb (a b c a' b' c' : Sym)
    (ha : a ≠ .f → a' = a) (hb : b ≠ .f → b' = b) (hc : c ≠ .f → c' = c)
    (h : medianSym a b c ≠ .f) : medianSym a' b' c' = medianSym a b c := by
  cases a <;> cases b <;> cases c <;> simp_all [medianSym]
noncomputable def prune (labels : List (Fin n) → Sym) : Tree n := by
  classical
  exact {
    fn := fun w => if IsLivePrefix labels w then some (labels w) else none
    wf := by
      constructor
      · simp
      · intro w i
        simp only [isLivePrefix_append_singleton]
        by_cases h : IsLivePrefix labels w <;> simp [h]
  }
theorem extendedLabel_prune (labels : List (Fin n) → Sym)
    (h : ∀ w v, labels w ≠ .f → labels (w ++ v) = labels w) :
    extendedLabel (prune labels) = labels := by
  classical
  funext w
  induction w using List.reverseRecOn with
  | nil => simp [extendedLabel, prune]
  | append_singleton w i ih =>
    rw [extendedLabel_step, ih]
    by_cases ha : IsLivePrefix labels (w ++ [i])
    · simp [prune, ha]
    · simp only [prune, if_neg ha, Option.getD_none]
      by_cases hw : labels w = .f
      · obtain ⟨v, hp, hn, hv⟩ := by
          simpa only [IsLivePrefix, not_forall, Classical.not_imp] using ha
        have hvw : v.IsPrefix w := List.prefix_of_prefix_length_le hp
          (List.prefix_append _ _) (by
            have hle := hp.length_le
            have hne : v.length ≠ (w ++ [i]).length := fun he => hn (hp.eq_of_length he)
            simp only [List.length_append, List.length_singleton] at hle hne
            omega)
        obtain ⟨s, rfl⟩ := hvw
        exact False.elim (hv ((h v s hv).symm.trans hw))
      · exact (h w [i] hw).symm
noncomputable def treeMedian (a b c : Tree n) : Tree n :=
  prune (fun w => medianSym (extendedLabel a w) (extendedLabel b w) (extendedLabel c w))
@[simp] theorem extendedLabel_treeMedian (a b c : Tree n) (w : List (Fin n)) :
    extendedLabel (treeMedian a b c) w =
        medianSym (extendedLabel a w) (extendedLabel b w) (extendedLabel c w) := by
  apply congrFun (extendedLabel_prune _ _) w
  intro v s h
  exact medianSym_absorb _ _ _ _ _ _ (extendedLabel_absorb a v s) (extendedLabel_absorb b v s)
    (extendedLabel_absorb c v s) h
@[simp] theorem treeMedian_self (a c : Tree n) : treeMedian a a c = a := by
  apply extendedLabel_injective; funext w; simp
def fullTree : Tree n where
  fn _ := some .f
  wf := by simp
end DeciSigma1.Semantics


