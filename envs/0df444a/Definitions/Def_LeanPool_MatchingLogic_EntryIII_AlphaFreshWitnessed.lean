-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_AlphaFreshWitnessed
-- name    : LeanPool_MatchingLogic_EntryIII_AlphaFreshWitnessed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:39:23.016258+00:00
-- url     : https://prove2.me/theorems/0ae89807-0b94-4541-bf4e-40a1794dc01d
-- title:
--   Alpha Fresh Witnessed
-- statement:
--   Definitions and structural lemmas for Alpha Fresh Witnessed, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Tactic.FinCases
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
public import Theorems.Thm_MatchingLogic_Pattern_rename_comp
public import Theorems.Thm_MatchingLogic_Pattern_rename_id
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_canonicalStep_iff
public import Theorems.Thm_MatchingLogic_completedModel_interp
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_generatedModel_interp
public import Theorems.Thm_MatchingLogic_generatingContext_nil
public import Theorems.Thm_MatchingLogic_generatingStepContext_plug
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
public import Theorems.Thm_MatchingLogic_mem_completedInterp
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
attribute [local simp] MatchingLogic.Pattern.rename_comp
attribute [local simp] MatchingLogic.Pattern.rename_id
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.canonicalModel_interp
attribute [local simp] MatchingLogic.canonicalStep_iff
attribute [local simp] MatchingLogic.completedModel_interp
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.generatedModel_interp
attribute [local simp] MatchingLogic.generatingContext_nil
attribute [local simp] MatchingLogic.generatingStepContext_plug
attribute [local simp] MatchingLogic.mem_canonicalInterp
attribute [local simp] MatchingLogic.mem_completedInterp
attribute [local simp] MatchingLogic.mem_generatedInterp


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
open Set
noncomputable section
def AlphaFreshWitnessed {S : Signature}
    (Gamma : Set (Pattern S Nat)) : Prop :=
  ∀ {x : Nat} {p : Pattern S Nat}, Pattern.ex x p ∈ Gamma →
    ∃ (x' : Nat) (p' : Pattern S Nat) (y : Nat),
      Pattern.AlphaEq (Pattern.ex x p) (Pattern.ex x' p') ∧
      y ∉ p'.allVars ∧
      Pattern.imp (Pattern.ex x' p')
        (Pattern.captureAvoidingSubst x' y p') ∈ Gamma
inductive AlphaWitnessSym
  | pair
  deriving DecidableEq
instance : Fintype AlphaWitnessSym where
  elems := {AlphaWitnessSym.pair}
  complete s := by cases s; simp
abbrev AlphaWitnessSig : Signature where
  Sym := AlphaWitnessSym
  arity _ := 2
def pairArgs (p q : Pattern AlphaWitnessSig Nat) :
    Fin 2 → Pattern AlphaWitnessSig Nat
  | ⟨0, _⟩ => p
  | ⟨1, _⟩ => q
def boolPair (p q : Bool) : Fin 2 → Bool
  | ⟨0, _⟩ => p
  | ⟨1, _⟩ => q
abbrev alphaWitnessModel : Model AlphaWitnessSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp _ a := if a 0 = true ∧ a 1 = true then {true} else ∅
def alphaWitnessRho : Nat → alphaWitnessModel.carrier := fun n => n = 0
def alphaWitnessTheory : Set (Pattern AlphaWitnessSig Nat) :=
  pointedTheory alphaWitnessModel alphaWitnessRho true
def alphaBlocked : Pattern AlphaWitnessSig Nat :=
  .ex 1 (.app .pair (pairArgs (.var 1) (.var 0)))
abbrev alphaUnitEmptyModel : Model AlphaWitnessSig where
  carrier := Unit
  nonempty := ⟨()⟩
  interp _ _ := ∅
abbrev alphaUnitFullModel : Model AlphaWitnessSig where
  carrier := Unit
  nonempty := ⟨()⟩
  interp _ _ := {()}
def alphaUnitRho : Nat → alphaUnitEmptyModel.carrier := fun _ => ()
abbrev alphaFirstSelectorModel : Model AlphaWitnessSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp _ a := if a 0 = true ∧ a 1 = false then {true} else ∅
abbrev alphaCornerSelectorModel : Model AlphaWitnessSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp _ a := if a 0 = false ∧ a 1 = true then {true} else ∅
end
end MatchingLogic


