-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Examples_Satisfiability
-- name    : LeanPool_DeciSigma1_Examples_Satisfiability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:32:01.751617+00:00
-- url     : https://prove2.me/theorems/e817ba4d-a3ab-4975-b34b-ae50c51f7298
-- title:
--   Satisfiability
-- statement:
--   Definitions and structural lemmas for Satisfiability, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Satisfiability.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Theorems.Thm_DeciSigma1_Automata_lowerRun_nil
public import Theorems.Thm_DeciSigma1_Automata_lowerRun_snoc
public import Theorems.Thm_DeciSigma1_Automata_mem_down
public import Theorems.Thm_DeciSigma1_Automata_mem_lowerStep
public import Theorems.Thm_DeciSigma1_Automata_mem_up
public import Theorems.Thm_DeciSigma1_Automata_mem_upperStep
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Automata_upperRun_snoc
public import Theorems.Thm_DeciSigma1_Automata_upperStep_empty
public import Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_extend_fresh
public import Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_extend_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_satFin_iff
public import Theorems.Thm_DeciSigma1_Constraints_base_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_dual_eq_bot
public import Theorems.Thm_DeciSigma1_Constraints_dual_eq_top
public import Theorems.Thm_DeciSigma1_Constraints_holdsT_map
public import Theorems.Thm_DeciSigma1_Constraints_holds_false
public import Theorems.Thm_DeciSigma1_Constraints_lowerAt_nil_iff
public import Theorems.Thm_DeciSigma1_Constraints_normalize_false_eq_bot
public import Theorems.Thm_DeciSigma1_Constraints_normalize_false_eq_top
public import Theorems.Thm_DeciSigma1_Constraints_normalize_not
public import Theorems.Thm_DeciSigma1_Constraints_normalized_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_sat_append
public import Theorems.Thm_DeciSigma1_Constraints_sat_cons
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Constraints_sat_lift
public import Theorems.Thm_DeciSigma1_Constraints_sat_signed_iff
public import Theorems.Thm_DeciSigma1_Constraints_sign_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_signedDual_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_signedVar_base_sign
public import Theorems.Thm_DeciSigma1_Constraints_upperAt_nil_iff
public import Theorems.Thm_DeciSigma1_Full_Closure_configSet_assignmentOf
public import Theorems.Thm_DeciSigma1_Full_Closure_flipEmb_apply
public import Theorems.Thm_DeciSigma1_Full_Closure_mem_factList
public import Theorems.Thm_DeciSigma1_Full_Closure_mem_negList
public import Theorems.Thm_DeciSigma1_Full_Models_GroundBound_holds_map
public import Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_nonBottomPrefixes_realize
public import Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_symmetrize_toTree
public import Theorems.Thm_DeciSigma1_Satisfiability_Covariant_satFinB_iff
public import Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_selectedShape_domain
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_fn_nil
public import Theorems.Thm_DeciSigma1_Satisfiability_satFinB_iff
public import Theorems.Thm_DeciSigma1_Satisfiability_satFin_iff
public import Theorems.Thm_DeciSigma1_Satisfiability_satFinite_iff_signed
public import Theorems.Thm_DeciSigma1_Semantics_FTree_height_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_height_top
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
public import Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_extendedLabel_toTree_nil
public import Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_median_toTree
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_mix_fn
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_cons
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_top
public import Theorems.Thm_DeciSigma1_Semantics_bot_treeLe
public import Theorems.Thm_DeciSigma1_Semantics_dual_bot
public import Theorems.Thm_DeciSigma1_Semantics_dual_fn
public import Theorems.Thm_DeciSigma1_Semantics_dual_involutive
public import Theorems.Thm_DeciSigma1_Semantics_dual_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_dual_node
public import Theorems.Thm_DeciSigma1_Semantics_dual_top
public import Theorems.Thm_DeciSigma1_Semantics_fullTree_fn
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
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_refl
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_top
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.lowerRun_nil
attribute [local simp] DeciSigma1.Automata.lowerRun_snoc
attribute [local simp] DeciSigma1.Automata.mem_down
attribute [local simp] DeciSigma1.Automata.mem_lowerStep
attribute [local simp] DeciSigma1.Automata.mem_up
attribute [local simp] DeciSigma1.Automata.mem_upperStep
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Automata.upperRun_snoc
attribute [local simp] DeciSigma1.Automata.upperStep_empty
attribute [local simp] DeciSigma1.Constraints.GroundCompiler.extend_fresh
attribute [local simp] DeciSigma1.Constraints.GroundCompiler.extend_original
attribute [local simp] DeciSigma1.Constraints.base_signedVar
attribute [local simp] DeciSigma1.Constraints.dual_eq_bot
attribute [local simp] DeciSigma1.Constraints.dual_eq_top
attribute [local simp] DeciSigma1.Constraints.holdsT_map
attribute [local simp] DeciSigma1.Constraints.holds_false
attribute [local simp] DeciSigma1.Constraints.lowerAt_nil_iff
attribute [local simp] DeciSigma1.Constraints.normalize_false_eq_bot
attribute [local simp] DeciSigma1.Constraints.normalize_false_eq_top
attribute [local simp] DeciSigma1.Constraints.normalize_not
attribute [local simp] DeciSigma1.Constraints.normalized_signedVar
attribute [local simp] DeciSigma1.Constraints.sat_append
attribute [local simp] DeciSigma1.Constraints.sat_cons
attribute [local simp] DeciSigma1.Constraints.sat_false
attribute [local simp] DeciSigma1.Constraints.sat_lift
attribute [local simp] DeciSigma1.Constraints.sat_signed_iff
attribute [local simp] DeciSigma1.Constraints.sign_signedVar
attribute [local simp] DeciSigma1.Constraints.signedDual_signedVar
attribute [local simp] DeciSigma1.Constraints.signedVar_base_sign
attribute [local simp] DeciSigma1.Constraints.upperAt_nil_iff
attribute [local simp] DeciSigma1.Full.Closure.configSet_assignmentOf
attribute [local simp] DeciSigma1.Full.Closure.flipEmb_apply
attribute [local simp] DeciSigma1.Full.Closure.mem_factList
attribute [local simp] DeciSigma1.Full.Closure.mem_negList
attribute [local simp] DeciSigma1.Full.Models.GroundBound.holds_map
attribute [local simp] DeciSigma1.Full.Models.PrefixPair.nonBottomPrefixes_realize
attribute [local simp] DeciSigma1.Full.Models.Signed.FinitePinning.symmetrize_toTree
attribute [local simp] DeciSigma1.Satisfiability.SignSelection.selectedShape_domain
attribute [local simp] DeciSigma1.Satisfiability.leastShape_fn_nil
attribute [local simp] DeciSigma1.Semantics.FTree.height_bot
attribute [local simp] DeciSigma1.Semantics.FTree.height_top
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_dual
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_normalize
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
attribute [local simp] DeciSigma1.Semantics.FiniteMedian.extendedLabel_toTree_nil
attribute [local simp] DeciSigma1.Semantics.FiniteMedian.median_toTree
attribute [local simp] DeciSigma1.Semantics.SignSelection.mix_fn
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
attribute [local simp] DeciSigma1.Semantics.fullTree_fn
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
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Examples.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Satisfiability DeciSigma1.Semantics
theorem inequality (n : ℕ) (c : Fin n → Bool) :
    satFinB c ([.le false true] : List (LitT n Bool)) = true := by
  apply (satFinB_iff _ _).mpr
  refine ⟨fun _ => .bot, ?_⟩
  simp [SatT, HoldsT, treeLe_refl]
example : satFinB (n := 0) (fun _ => false) ([.le false true] : List (LitT 0 Bool)) = true :=
  inequality 0 _
example : satFinB (n := 1) (fun _ => false) ([.le false true] : List (LitT 1 Bool)) = true :=
  inequality 1 _
theorem inconsistent (n : ℕ) : satFinB (fun _ => false)
    ([.eqTop false, .le false true, .eqBot true] : List (LitT n Bool)) = false := by
  simp only [Bool.eq_false_iff, ne_eq, satFinB_iff]
  rintro ⟨σ, hσ⟩
  have ht : (σ false).toTree = Tree.top := hσ (.eqTop false) (by simp)
  have hb : (σ true).toTree = Tree.bot := hσ (.eqBot true) (by simp)
  have hle : (σ false).toTree ≤ (σ true).toTree :=
    (treeLe_false_iff_le _ _).mp (hσ (.le false true) (by simp))
  rw [ht, hb] at hle
  exact Tree.top_ne_bot ((Tree.le_bot_iff _).mp hle)
example : satFinB (n := 0) (fun _ => false)
    ([.eqTop false, .le false true, .eqBot true] : List (LitT 0 Bool)) = false :=
  inconsistent 0
example : satFinB (n := 1) (fun _ => false)
    ([.eqTop false, .le false true, .eqBot true] : List (LitT 1 Bool)) = false :=
  inconsistent 1
example : satFinB (n := 0) (fun _ => false)
    ([.fLe (fun _ => ()) (), .leF () (fun _ => ())] : List (LitT 0 Unit)) = true := by
  apply (satFinB_iff _ _).mpr
  refine ⟨fun _ => .node (fun i => i.elim0), ?_⟩
  simp [SatT, HoldsT, treeLe_false_iff_le, FTree.toTree]
example : satFinB (n := 1) (fun _ => false)
    ([.fLe (fun _ => ()) (), .leF () (fun _ => ())] : List (LitT 1 Unit)) = false := by
  simp only [Bool.eq_false_iff, ne_eq, satFinB_iff, satFinite_iff_signed, satFin_iff]
  intro h
  apply h.2
  refine ⟨[0], ((), false), ((), false), by simp, ?_, .refl _, ?_⟩
  · exact LowerAt.cons (a := fun _ => ((), false)) (by simp [signed,
    signedLit]) (.refl _) (.nil (.refl _))
  · exact UpperAt.cons (b := fun _ => ((), false)) (.refl _) (by simp [signed,
    signedLit]) (.nil (.refl _))
end DeciSigma1.Examples.Satisfiability


