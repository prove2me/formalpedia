-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Entailment_Logic
-- name    : LeanPool_DeciSigma1_Entailment_Logic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:17:57.375361+00:00
-- url     : https://prove2.me/theorems/76a71630-54a6-4602-9663-2fd2686f2cf3
-- title:
--   Logic
-- statement:
--   Definitions and structural lemmas for Logic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Logic.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
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
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_holds_append
public import Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_selectedShape_domain
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_fn_nil
public import Theorems.Thm_DeciSigma1_Semantics_FTree_height_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_height_top
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
public import Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_extendedLabel_toTree_nil
public import Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_median_toTree
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_positions_toTree
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_eq_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_le_toTree
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
public import Theorems.Thm_DeciSigma1_Semantics_isFiniteTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_isFiniteTree_node
public import Theorems.Thm_DeciSigma1_Semantics_isRegularTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_isRegularTree_node
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
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
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
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Logic.ConjunctiveClause.holds_append
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
attribute [local simp] DeciSigma1.Semantics.PrefixSet.positions_toTree
attribute [local simp] DeciSigma1.Semantics.PrefixSet.toTree_bot
attribute [local simp] DeciSigma1.Semantics.PrefixSet.toTree_eq_bot_iff
attribute [local simp] DeciSigma1.Semantics.PrefixSet.toTree_le_toTree
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
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Entailment.Logic
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
inductive BFTerm (n : ℕ) (V : Type) where
  /-- A variable. -/
  | var (v : V)
  /-- The constant `⊥`. -/
  | bot
  /-- The constructor `f(t₀, …, t_{n-1})`. -/
  | node (t : Fin n → BFTerm n V)
variable {n : ℕ} {V W : Type}
namespace BFTerm
def decEq [DecidableEq V] : (s t : BFTerm n V) → Decidable (s = t)
  | .var v, .var w => decidable_of_iff (v = w) (by simp)
  | .bot, .bot => isTrue rfl
  | .node a, .node b =>
    letI (i : Fin n) : Decidable (a i = b i) := decEq (a i) (b i)
    decidable_of_iff (∀ i, a i = b i) (by simp [funext_iff])
  | .var _, .bot | .var _, .node _ | .bot, .var _ | .bot, .node _ |
    .node _, .var _ | .node _, .bot => isFalse (by intro h; cases h)
instance [DecidableEq V] : DecidableEq (BFTerm n V) := decEq
def eval (ρ : V → PrefixSet n) : BFTerm n V → PrefixSet n
  | .var v => ρ v
  | .bot => PrefixSet.bot
  | .node t => PrefixSet.node fun i => (t i).eval ρ
def subterms : BFTerm n V → List (BFTerm n V)
  | .var v => [.var v]
  | .bot => [.bot]
  | .node a => .node a :: (List.finRange n).flatMap fun i => (a i).subterms
theorem mem_subterms (t : BFTerm n V) : t ∈ t.subterms := by
  cases t <;> simp [subterms]
theorem mem_subterms_node {a : Fin n → BFTerm n V} {s : BFTerm n V} (i : Fin n)
    (hs : s ∈ (a i).subterms) : s ∈ (node a).subterms := by
  simp only [subterms, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and]
  exact Or.inr ⟨i, hs⟩
theorem subterms_trans {s t u : BFTerm n V} (hs : s ∈ t.subterms) (hu : u ∈ s.subterms) :
    u ∈ t.subterms := by
  induction t with
  | var v => simp only [subterms, List.mem_singleton] at hs; exact hs ▸ hu
  | bot => simp only [subterms, List.mem_singleton] at hs; exact hs ▸ hu
  | node a ih =>
    simp only [subterms, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and] at hs
    rcases hs with rfl | ⟨i, hi⟩
    · exact hu
    · exact mem_subterms_node i (ih i hi)
def defs (var : V → W) (name : BFTerm n V → W) (t : BFTerm n V) : List (Lit n W) :=
  match t with
  | .var v => [.le (name t) (var v), .le (var v) (name t)]
  | .bot => [.eqBot (name t)]
  | .node a => [.fLe (fun i => name (a i)) (name t), .leF (name t) (fun i => name (a i))]
theorem holds_defs (var : V → W) (name : BFTerm n V → W) (σ : W → PrefixSet n)
    (t : BFTerm n V) (h : ∀ s ∈ t.subterms, σ (name s) = s.eval (σ ∘ var)) :
    ∀ l ∈ defs var name t, l.Holds σ := by
  have ht := h t t.mem_subterms
  cases t with
  | var v => simp_all [defs, Lit.Holds, eval]
  | bot => simp_all [defs, Lit.Holds, eval]
  | node a =>
    have hc (i : Fin n) := h (a i) (mem_subterms_node i (a i).mem_subterms)
    simp_all [defs, Lit.Holds, eval, Function.comp_def]
theorem eval_of_holds_defs (var : V → W) (name : BFTerm n V → W) (σ : W → PrefixSet n)
    (t : BFTerm n V) (h : ∀ s ∈ t.subterms, ∀ l ∈ defs var name s, l.Holds σ) :
    σ (name t) = t.eval (σ ∘ var) := by
  have ht := h t t.mem_subterms
  induction t with
  | var v =>
    simp only [defs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Lit.Holds] at ht
    exact le_antisymm ht.1 ht.2
  | bot => simpa [defs, Lit.Holds, eval] using ht
  | node a ih =>
    simp only [defs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Lit.Holds] at ht
    rw [le_antisymm ht.2 ht.1]
    simp only [eval]
    congr 1
    funext i
    exact ih i (fun s hs => h s (mem_subterms_node i hs))
        (h _ (mem_subterms_node i (a i).mem_subterms))
end BFTerm
def interpretation (n : ℕ) : DeciSigma1.Logic.Interpretation (BFTerm n) (PrefixSet n) where
  eval ρ t := t.eval ρ
  le := (· ≤ ·)
abbrev BooleanSentence (n : ℕ) : Type := DeciSigma1.Logic.BooleanSentence (BFTerm n)
abbrev BooleanSentence.HoldsIn (C : PrefixSet n → Prop) (φ : BooleanSentence n) : Prop :=
  DeciSigma1.Logic.BooleanSentence.HoldsIn (interpretation n) C φ
def flattening (n : ℕ) : DeciSigma1.Logic.Flattening (interpretation n) where
  Lit := Lit n
  Holds σ l := l.Holds σ
  leLit := .le
  holds_leLit _ _ _ := Iff.rfl
  subterms := BFTerm.subterms
  mem_subterms := BFTerm.mem_subterms
  subterms_trans := BFTerm.subterms_trans
  bot := .bot
  defs := BFTerm.defs
  holds_defs := BFTerm.holds_defs
  eval_of_holds_defs := BFTerm.eval_of_holds_defs
structure BFTermClosed (C : PrefixSet n → Prop) : Prop where
  bot : C PrefixSet.bot
  node : ∀ a : Fin n → PrefixSet n, (∀ i, C (a i)) → C (PrefixSet.node a)
theorem BFTermClosed.eval {C : PrefixSet n → Prop} (hC : BFTermClosed C) :
    (interpretation n).TermClosed C := by
  intro V ρ t hρ
  induction t with
  | var v => exact hρ v
  | bot => exact hC.bot
  | node a ih => exact hC.node _ ih
theorem bfTermClosed_all : BFTermClosed fun _ : PrefixSet n => True :=
  ⟨trivial, fun _ _ => trivial⟩
theorem bfTermClosed_reg : BFTermClosed (@IsRegularTree n) :=
  ⟨isRegularTree_bot, isRegularTree_node⟩
theorem bfTermClosed_fin : BFTermClosed (@IsFiniteTree n) :=
  ⟨isFiniteTree_bot, isFiniteTree_node⟩
inductive TreeClass where
  /-- All trees. -/
  | arbitrary
  /-- The regular trees. -/
  | regular
  /-- The finite trees. -/
  | finite
  deriving DecidableEq
def TreeClass.Contains : TreeClass → PrefixSet n → Prop
  | .arbitrary => fun _ => True
  | .regular => IsRegularTree
  | .finite => IsFiniteTree
theorem TreeClass.bfTermClosed : (C : TreeClass) → BFTermClosed (C.Contains (n := n))
  | .arbitrary => bfTermClosed_all
  | .regular => bfTermClosed_reg
  | .finite => bfTermClosed_fin
variable [Fintype V] [DecidableEq V]
@[instance_reducible] def disjEntailmentDecider :
    (C : TreeClass) → DeciSigma1.Logic.DisjEntailmentDecider (flattening n) C.Contains
  | .arbitrary => fun Γ q => decideDisjEntails Γ q
  | .regular => fun Γ q => decideDisjEntailsReg Γ q
  | .finite => fun Γ q => decideDisjEntailsFin Γ q
def decideBooleanSentence (C : TreeClass) (φ : BooleanSentence n) :
    Decidable (φ.HoldsIn C.Contains) :=
  DeciSigma1.Logic.decideBooleanSentence (flattening n) (C.bfTermClosed.eval)
    (disjEntailmentDecider C) φ
end DeciSigma1.Entailment.Logic


