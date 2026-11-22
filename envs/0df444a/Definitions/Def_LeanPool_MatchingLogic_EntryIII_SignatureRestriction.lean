-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
-- name    : LeanPool_MatchingLogic_EntryIII_SignatureRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:32:49.814802+00:00
-- url     : https://prove2.me/theorems/6cd6e566-50fa-4390-ac34-556a12d229c4
-- title:
--   Signature Restriction
-- statement:
--   Definitions and structural lemmas for Signature Restriction, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
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
public import Theorems.Thm_MatchingLogic_Pattern_argument_symbolSupport_subset
public import Theorems.Thm_MatchingLogic_Pattern_head_mem_symbolSupport
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
namespace Signature
def restrict (F : Finset S.Sym) : Signature where
  Sym := {sigma : S.Sym // sigma ∈ F}
  arity sigma := S.arity sigma.1
end Signature
namespace Pattern
def liftSignature [DecidableEq S.Sym] (F : Finset S.Sym) :
    Pattern (S.restrict F) Var → Pattern S Var
  | .var x => .var x
  | .app sigma args => .app sigma.1 (fun i => (args i).liftSignature F)
  | .imp phi psi => .imp (phi.liftSignature F) (psi.liftSignature F)
  | .bot => .bot
  | .ex x phi => .ex x (phi.liftSignature F)
def restrictSignature [DecidableEq S.Sym] (F : Finset S.Sym) :
    (p : Pattern S Var) → p.symbolSupport ⊆ F → Pattern (S.restrict F) Var
  | .var x, _ => .var x
  | .bot, _ => .bot
  | .app sigma args, h =>
      .app ⟨sigma, h (head_mem_symbolSupport sigma args)⟩
        (fun i => (args i).restrictSignature F
          (fun _ htau => h (argument_symbolSupport_subset sigma args i htau)))
  | .imp phi psi, h =>
      .imp (phi.restrictSignature F (fun _ htau => h (by
        simp [symbolSupport, htau])))
        (psi.restrictSignature F (fun _ htau => h (by
          simp [symbolSupport, htau])))
  | .ex x phi, h => .ex x (phi.restrictSignature F h)
end Pattern
namespace AppCtx
def liftSignature [DecidableEq S.Sym] (F : Finset S.Sym) :
    AppCtx (S.restrict F) Var → AppCtx S Var
  | .hole => .hole
  | .node sigma i args C =>
      .node sigma.1 i (fun j => (args j).liftSignature F) (C.liftSignature F)
end AppCtx
namespace Pattern
noncomputable def signatureNatCode {T : Signature} [Encodable T.Sym] :
    Pattern T Nat → Nat
  | .var x => Nat.pair 0 x
  | .app sigma args => Nat.pair 1 (Nat.pair (Encodable.encode sigma)
      (Encodable.encode (List.ofFn fun i => (args i).signatureNatCode)))
  | .imp phi psi => Nat.pair 2 (Nat.pair phi.signatureNatCode psi.signatureNatCode)
  | .bot => Nat.pair 3 0
  | .ex x phi => Nat.pair 4 (Nat.pair x phi.signatureNatCode)
def signatureNatTag : Pattern T Nat → Nat
  | .var _ => 0
  | .app _ _ => 1
  | .imp _ _ => 2
  | .bot => 3
  | .ex _ _ => 4
end Pattern
end MatchingLogic


