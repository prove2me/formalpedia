-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
-- name    : LeanPool_MatchingLogic_EntryIII_Completion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:28:16.101429+00:00
-- url     : https://prove2.me/theorems/64317791-cb9a-4898-9d2c-a84a37621b56
-- title:
--   Completion
-- statement:
--   Definitions and structural lemmas for Completion, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Theorems.Thm_MatchingLogic_AppCtx_plug_comp
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_canonicalStep_iff
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_generatedModel_interp
public import Theorems.Thm_MatchingLogic_generatingContext_nil
public import Theorems.Thm_MatchingLogic_generatingStepContext_plug
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
public import Theorems.Thm_MatchingLogic_mem_generatedInterp
attribute [local simp] MatchingLogic.AppCtx.plug_comp
attribute [local simp] MatchingLogic.CanonicalCarrier.coe_mk
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_box
attribute [local simp] MatchingLogic.FV_boxes
attribute [local simp] MatchingLogic.FV_dia
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.Model.reachWord_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.canonicalModel_interp
attribute [local simp] MatchingLogic.canonicalStep_iff
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.generatedModel_interp
attribute [local simp] MatchingLogic.generatingContext_nil
attribute [local simp] MatchingLogic.generatingStepContext_plug
attribute [local simp] MatchingLogic.mem_canonicalInterp
attribute [local simp] MatchingLogic.mem_generatedInterp


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature}
noncomputable section
local instance instDecidableEqPatternNatCompletion : DecidableEq (Pattern S Nat) :=
  Classical.decEq _
def Missing (root : CanonicalCarrier S) : Prop :=
  ∃ x : Nat, ∀ world : GeneratedCarrier root,
    Pattern.var x ∉ world.val.val
def CompletedCarrier (root : CanonicalCarrier S) :=
  {o : Option (GeneratedCarrier root) // o = none → Missing root}
namespace CompletedCarrier
def isStar {root : CanonicalCarrier S} (point : CompletedCarrier root) : Prop :=
  point.val = none
end CompletedCarrier
def completedEmbed (root : CanonicalCarrier S) (world : GeneratedCarrier root) :
    CompletedCarrier root :=
  ⟨some world, by simp⟩
def completedStar {root : CanonicalCarrier S} (hmissing : Missing root) :
    CompletedCarrier root :=
  ⟨none, fun _ => hmissing⟩
def completedInterp (root : CanonicalCarrier S) (sigma : S.Sym)
    (inputs : Fin (S.arity sigma) → CompletedCarrier root) :
    Set (CompletedCarrier root) :=
  {output | ∃ components : Fin (S.arity sigma) → GeneratedCarrier root,
    (∀ i, inputs i = completedEmbed root (components i)) ∧
      ((∃ world : GeneratedCarrier root,
          output = completedEmbed root world ∧
            world ∈ generatedInterp root sigma components) ∨
       (output.isStar ∧ ∃ i, components i = generatedRoot root))}
abbrev completedModel (root : CanonicalCarrier S) : Model S where
  carrier := CompletedCarrier root
  nonempty := ⟨completedEmbed root (generatedRoot root)⟩
  interp := completedInterp root
def completedValuation (root : CanonicalCarrier S) (x : Nat) :
    CompletedCarrier root := by
  classical
  by_cases h : ∃ world : GeneratedCarrier root,
      Pattern.var x ∈ world.val.val
  · exact completedEmbed root (Classical.choose h)
  · exact ⟨none, fun _ => ⟨x, fun world hx => h ⟨world, hx⟩⟩⟩
end
end MatchingLogic


