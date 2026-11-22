-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
-- name    : LeanPool_MatchingLogic_EntryIII_SignatureReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:33:26.449646+00:00
-- url     : https://prove2.me/theorems/34865134-7afd-4807-a97b-0eac6e8222d2
-- title:
--   Signature Reduction
-- statement:
--   Definitions and structural lemmas for Signature Reduction, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Mathlib.Tactic.Bound.Init
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
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
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
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace Pattern
def symbolSupportList [DecidableEq S.Sym] (l : List (Pattern S Var)) : Finset S.Sym :=
  l.foldr (fun p support => p.symbolSupport ∪ support) ∅
def restrictList [DecidableEq S.Sym] (F : Finset S.Sym) (l : List (Pattern S Var))
    (h : ∀ p ∈ l, p.symbolSupport ⊆ F) : List (Pattern (S.restrict F) Var) :=
  match l with
  | [] => []
  | p :: l =>
      p.restrictSignature F (h p (by simp)) ::
        restrictList F l (fun q hq => h q (by simp [hq]))
end Pattern
namespace Model
abbrev extendSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (M : Model (S.restrict F)) : Model S where
  carrier := M.carrier
  nonempty := M.nonempty
  interp sigma args := if h : sigma ∈ F then M.interp ⟨sigma, h⟩ args else ∅
end Model
end MatchingLogic


