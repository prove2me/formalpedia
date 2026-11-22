-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Full_Logic
-- name    : LeanPool_DeciSigma1_Full_Logic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:16:50.917729+00:00
-- url     : https://prove2.me/theorems/fabb6361-9364-4fc8-bd34-7c36c2488ff0
-- title:
--   Logic
-- statement:
--   Definitions and structural lemmas for Logic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Logic.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
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
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_holds_append
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_selectedShape_domain
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_fn_nil
public import Theorems.Thm_DeciSigma1_Semantics_Characterization_dom_toTree_finite
public import Theorems.Thm_DeciSigma1_Semantics_Characterization_subtree_nil
public import Theorems.Thm_DeciSigma1_Semantics_Characterization_subtrees_finite_of_dom_finite
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
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_antisymm
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_false_iff_le
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_refl
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_top
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_union
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
namespace DeciSigma1.Full.Logic
open DeciSigma1.Constraints DeciSigma1.Semantics DeciSigma1.Full.Models
inductive Term (n : ℕ) (V : Type) where
  /-- A variable. -/
  | var (v : V)
  /-- The constant `⊥`. -/
  | bot
  /-- The constant `⊤`. -/
  | top
  /-- The constructor `f(t₀, …, t_{n-1})`. -/
  | node (t : Fin n → Term n V)
variable {n : ℕ} {V W : Type}
namespace Term
def decEq [DecidableEq V] : (s t : Term n V) → Decidable (s = t)
  | .var v, .var w => decidable_of_iff (v = w) (by simp)
  | .top, .top => isTrue rfl
  | .bot, .bot => isTrue rfl
  | .node a, .node b =>
    letI (i : Fin n) : Decidable (a i = b i) := decEq (a i) (b i)
    decidable_of_iff (∀ i, a i = b i) (by simp [funext_iff])
  | .top, .var _ | .top, .bot | .top, .node _ |
    .var _, .top | .bot, .top | .node _, .top |
    .var _, .bot | .var _, .node _ | .bot, .var _ | .bot, .node _ |
    .node _, .var _ | .node _, .bot => isFalse (by intro h; cases h)
instance [DecidableEq V] : DecidableEq (Term n V) := decEq
def eval (ρ : V → Tree n) : Term n V → Tree n
  | .var v => ρ v
  | .bot => Tree.bot
  | .top => Tree.top
  | .node t => Semantics.Tree.node fun i => (t i).eval ρ
def subterms : Term n V → List (Term n V)
  | .var v => [.var v]
  | .bot => [.bot]
  | .top => [.top]
  | .node a => .node a :: (List.finRange n).flatMap fun i => (a i).subterms
theorem mem_subterms (t : Term n V) : t ∈ t.subterms := by
  cases t <;> simp [subterms]
theorem mem_subterms_node {a : Fin n → Term n V} {s : Term n V} (i : Fin n)
    (hs : s ∈ (a i).subterms) : s ∈ (node a).subterms := by
  simp only [subterms, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and]
  exact Or.inr ⟨i, hs⟩
theorem subterms_trans {s t u : Term n V} (hs : s ∈ t.subterms) (hu : u ∈ s.subterms) :
    u ∈ t.subterms := by
  induction t with
  | var v => simp only [subterms, List.mem_singleton] at hs; exact hs ▸ hu
  | bot => simp only [subterms, List.mem_singleton] at hs; exact hs ▸ hu
  | top => simp only [subterms, List.mem_singleton] at hs; exact hs ▸ hu
  | node a ih =>
    simp only [subterms, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and] at hs
    rcases hs with rfl | ⟨i, hi⟩
    · exact hu
    · exact mem_subterms_node i (ih i hi)
def defs (var : V → W) (name : Term n V → W) (t : Term n V) : List (LitT n W) :=
  match t with
  | .var v => [.le (name t) (var v), .le (var v) (name t)]
  | .bot => [.eqBot (name t)]
  | .top => [.eqTop (name t)]
  | .node a => [.fLe (fun i => name (a i)) (name t), .leF (name t) (fun i => name (a i))]
variable (c : Fin n → Bool)
theorem holds_defs (var : V → W) (name : Term n V → W) (σ : W → Tree n) (t : Term n V)
    (h : ∀ s ∈ t.subterms, σ (name s) = s.eval (σ ∘ var)) :
    ∀ l ∈ defs var name t, HoldsT c σ l := by
  have ht := h t t.mem_subterms
  cases t with
  | var v => simp_all [defs, HoldsT, eval, treeLe_refl]
  | bot => simp_all [defs, HoldsT, eval]
  | top => simp_all [defs, HoldsT, eval]
  | node a =>
    have hc : (fun i => σ (name (a i))) = fun i => (a i).eval (σ ∘ var) :=
      funext fun i => h (a i) (mem_subterms_node i (a i).mem_subterms)
    simp only [defs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      HoldsT, Function.comp_def, hc, ht, eval]
    exact ⟨treeLe_refl c _, treeLe_refl c _⟩
theorem eval_of_holds_defs (var : V → W) (name : Term n V → W) (σ : W → Tree n)
    (t : Term n V) (h : ∀ s ∈ t.subterms, ∀ l ∈ defs var name s, HoldsT c σ l) :
    σ (name t) = t.eval (σ ∘ var) := by
  have ht := h t t.mem_subterms
  induction t with
  | var v =>
    simp only [defs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      HoldsT] at ht
    exact treeLe_antisymm ht.1 ht.2
  | bot => simpa [defs, HoldsT, eval] using ht
  | top => simpa [defs, HoldsT, eval] using ht
  | node a ih =>
    simp only [defs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      HoldsT] at ht
    rw [treeLe_antisymm ht.2 ht.1]
    simp only [eval]
    congr 1
    funext i
    exact ih i (fun s hs => h s (mem_subterms_node i hs))
      (h _ (mem_subterms_node i (a i).mem_subterms))
end Term
variable (c : Fin n → Bool)
def interpretation : DeciSigma1.Logic.Interpretation (Term n) (Tree n) where
  eval ρ t := t.eval ρ
  le := Tree.Le c
abbrev BooleanSentence (n : ℕ) : Type := DeciSigma1.Logic.BooleanSentence (Term n)
abbrev BooleanSentence.HoldsIn (C : Tree n → Prop) (c : Fin n → Bool) (φ : BooleanSentence n) :
    Prop :=
  DeciSigma1.Logic.BooleanSentence.HoldsIn (interpretation c) C φ
def flattening : DeciSigma1.Logic.Flattening (interpretation (n := n) c) where
  Lit := LitT n
  Holds σ l := HoldsT c σ l
  leLit := .le
  holds_leLit _ _ _ := Iff.rfl
  subterms := Term.subterms
  mem_subterms := Term.mem_subterms
  subterms_trans := Term.subterms_trans
  bot := .bot
  defs := Term.defs
  holds_defs := Term.holds_defs c
  eval_of_holds_defs := Term.eval_of_holds_defs c
structure TermClosed (C : Tree n → Prop) : Prop where
  bot : C Tree.bot
  top : C Tree.top
  node : ∀ a : Fin n → Tree n, (∀ i, C (a i)) → C (Semantics.Tree.node a)
theorem TermClosed.eval {C : Tree n → Prop} (hC : TermClosed C) :
    (interpretation c).TermClosed C := by
  intro V ρ t hρ
  induction t with
  | var v => exact hρ v
  | bot => exact hC.bot
  | top => exact hC.top
  | node a ih => exact hC.node _ ih
theorem termClosed_all : TermClosed fun _ : Tree n => True :=
  ⟨trivial, trivial, fun _ _ => trivial⟩
theorem termClosed_fin : TermClosed (@FiniteTop n) := by
  refine ⟨⟨.bot, rfl⟩, ⟨.top, rfl⟩, fun a ha => ?_⟩
  choose b hb using ha
  exact ⟨.node b, by simp [hb]⟩
theorem regularTop_of_finiteTop {t : Tree n} (ht : FiniteTop t) : RegularTop t := by
  obtain ⟨s, rfl⟩ := ht
  exact Characterization.subtrees_finite_of_dom_finite _ (Characterization.dom_toTree_finite s)
theorem regularTop_node (a : Fin n → Tree n) (ha : ∀ i, RegularTop (a i)) :
    RegularTop (Semantics.Tree.node a) := by
  change (Characterization.subtrees (Semantics.Tree.node a)).Finite
  apply ((Set.finite_singleton (Semantics.Tree.node a)).union
    (Set.finite_iUnion ha)).subset
  rintro u ⟨w, hw⟩
  cases w with
  | nil =>
    left
    simpa only [Set.mem_singleton_iff, Characterization.subtree_nil, Option.some.injEq]
      using hw.symm
  | cons i w =>
    right
    refine Set.mem_iUnion.mpr ⟨i, w, ?_⟩
    have he : (Semantics.Tree.node a).subtree (i :: w) = (a i).subtree w := by
      simp only [Tree.subtree, Tree.node_fn_cons, List.cons_append]
      rfl
    exact he.symm.trans hw
theorem termClosed_reg : TermClosed (@RegularTop n) :=
  ⟨regularTop_of_finiteTop termClosed_fin.bot, regularTop_of_finiteTop termClosed_fin.top,
    regularTop_node⟩
inductive TreeClass where
  /-- All trees. -/
  | arbitrary
  /-- The regular trees. -/
  | regular
  /-- The finite trees. -/
  | finite
  deriving DecidableEq
def TreeClass.Contains : TreeClass → Tree n → Prop
  | .arbitrary => fun _ => True
  | .regular => RegularTop
  | .finite => FiniteTop
theorem TreeClass.termClosed : (C : TreeClass) → TermClosed (C.Contains (n := n))
  | .arbitrary => termClosed_all
  | .regular => termClosed_reg
  | .finite => termClosed_fin
@[instance_reducible] def disjEntailmentDecider :
    (C : TreeClass) → DeciSigma1.Logic.DisjEntailmentDecider (flattening c) C.Contains
  | .arbitrary => fun Γ q => decideDisjEntails c Γ q
  | .regular => fun Γ q => decideDisjEntailsReg c Γ q
  | .finite => fun Γ q => decideDisjEntailsFin c Γ q
def decideBooleanSentence (C : TreeClass) (φ : BooleanSentence n) :
    Decidable (φ.HoldsIn C.Contains c) :=
  DeciSigma1.Logic.decideBooleanSentence (flattening c) (C.termClosed.eval c)
    (disjEntailmentDecider c C) φ
end DeciSigma1.Full.Logic


