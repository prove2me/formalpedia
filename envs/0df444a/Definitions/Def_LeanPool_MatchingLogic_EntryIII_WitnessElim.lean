-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessElim
-- name    : LeanPool_MatchingLogic_EntryIII_WitnessElim
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:29:59.180197+00:00
-- url     : https://prove2.me/theorems/e56a4bbd-4405-4f6d-8303-68ace71931e1
-- title:
--   Witness Elim
-- statement:
--   Definitions and structural lemmas for Witness Elim, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessElim.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_AvoidsBinder_captureFree
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_complexity_eq
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_exQuant
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_alphaEq
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_avoids
public import Theorems.Thm_MatchingLogic_Pattern_complexity_captureAvoidingSubst
public import Theorems.Thm_MatchingLogic_Provable_imp_trans
public import Theorems.Thm_MatchingLogic_Provable_swap_not
public import Theorems.Thm_MatchingLogic_Provable_weaken_empty
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
variable {S : Signature}
theorem taut_double_neg_intro :
    PForm.Taut (.imp (.atom 0) (.imp (.imp (.atom 0) .bot) .bot)) := by
  intro v
  cases h0 : v 0 <;> simp [PForm.eval, h0]
theorem taut_double_neg_elim :
    PForm.Taut (.imp (.imp (.imp (.atom 0) .bot) .bot) (.atom 0)) := by
  intro v
  cases h0 : v 0 <;> simp [PForm.eval, h0]
theorem Provable.captureAvoidingSubst_theorem {r : Pattern S Nat}
    (h : Provable (∅ : Set (Pattern S Nat)) r) (x y : Nat) :
    Provable (∅ : Set (Pattern S Nat))
      (Pattern.captureAvoidingSubst x y r) := by
  let r' := Pattern.avoidBinder y r
  let q := substVar x y r'
  have hr' : Provable (∅ : Set (Pattern S Nat)) r' :=
    .mp h ((Pattern.avoidBinder_alphaEq y r).forward ∅)
  have hdni : Provable (∅ : Set (Pattern S Nat))
      (.imp r' (Pattern.nt (Pattern.nt r'))) := by
    simpa [PForm.subst] using
      (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
        (θ := fun _ => r') taut_double_neg_intro)
  have hdneg : Provable (∅ : Set (Pattern S Nat))
      (Pattern.nt (Pattern.nt r')) := .mp hr' hdni
  have hall : Provable (∅ : Set (Pattern S Nat))
      (Pattern.nt (.ex x (Pattern.nt r'))) := by
    exact .exGen hdneg (by simp)
  have hcf : CaptureFree x y (Pattern.nt r') := by
    exact ⟨(Pattern.avoidBinder_avoids y r).captureFree, trivial⟩
  have hex : Provable (∅ : Set (Pattern S Nat))
      (.imp (Pattern.nt q) (.ex x (Pattern.nt r'))) := by
    simpa [q, Pattern.nt, substVar] using
      (Provable.exQuant (Γ := (∅ : Set (Pattern S Nat))) hcf)
  have hbdn : Provable (∅ : Set (Pattern S Nat))
      (.imp (.ex x (Pattern.nt r'))
        (Pattern.nt (Pattern.nt (.ex x (Pattern.nt r'))))) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
        (θ := fun _ => .ex x (Pattern.nt r')) taut_double_neg_intro)
  have hcontra : Provable (∅ : Set (Pattern S Nat))
      (.imp (Pattern.nt (.ex x (Pattern.nt r')))
        (Pattern.nt (Pattern.nt q))) := by
    exact (hex.imp_trans hbdn).swap_not
  have hdnq : Provable (∅ : Set (Pattern S Nat))
      (Pattern.nt (Pattern.nt q)) := .mp hall hcontra
  have hde : Provable (∅ : Set (Pattern S Nat))
      (.imp (Pattern.nt (Pattern.nt q)) q) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
        (θ := fun _ => q) taut_double_neg_elim)
  simpa [Pattern.captureAvoidingSubst, r', q] using Provable.mp hdnq hde
theorem Pattern.AlphaEq.captureAvoidingSubst {p q : Pattern S Nat}
    (h : Pattern.AlphaEq p q) (x y : Nat) :
    Pattern.AlphaEq (Pattern.captureAvoidingSubst x y p)
      (Pattern.captureAvoidingSubst x y q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Gamma
    exact (Provable.captureAvoidingSubst_theorem (h.forward ∅) x y).weaken_empty
  · intro Gamma
    exact (Provable.captureAvoidingSubst_theorem (h.backward ∅) x y).weaken_empty
  · rw [Pattern.complexity_captureAvoidingSubst,
      Pattern.complexity_captureAvoidingSubst]
    exact h.complexity_eq
namespace Pattern
def avoidTwo (y z : Nat) : Pattern S Nat -> Pattern S Nat
  | .var a => .var a
  | .bot => .bot
  | .app sigma args => .app sigma (fun i => avoidTwo y z (args i))
  | .imp p q => .imp (avoidTwo y z p) (avoidTwo y z q)
  | .ex a p =>
      let q := avoidTwo y z p
      if _h : a = y ∨ a = z then
        let w := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh
        .ex w (substVar a w q)
      else .ex a q
def witnessBody (sigma : S.Sym)
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (w : Fin (S.arity sigma) -> Nat) : Pattern S Nat :=
  .app sigma (fun i => Pattern.and (Phi i)
    (.imp (.ex x p) (captureAvoidingSubst x (w i) p)))
end Pattern
end MatchingLogic


