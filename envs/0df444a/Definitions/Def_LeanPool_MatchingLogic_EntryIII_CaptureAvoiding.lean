-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
-- name    : LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:23:19.510036+00:00
-- url     : https://prove2.me/theorems/f2f7b361-71d8-42ba-b866-f54dd7083446
-- title:
--   Capture Avoiding
-- statement:
--   Definitions and structural lemmas for Capture Avoiding, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
public import Theorems.Thm_MatchingLogic_Provable_imp_refl
public import Theorems.Thm_MatchingLogic_Provable_imp_trans
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
namespace Pattern
@[simp] theorem substVar_self (x : Nat) (p : Pattern S Nat) : substVar x x p = p := by
  induction p with
  | var z => by_cases h : z = x <;> simp [substVar, h]
  | bot => rfl
  | app sigma args ih =>
      simp only [substVar]
      congr
      funext i
      exact ih i
  | imp phi psi ihphi ihpsi => simp [substVar, ihphi, ihpsi]
  | ex z phi ih => by_cases h : z = x <;> simp [substVar, h, ih]
theorem captureFree_self (x : Nat) (p : Pattern S Nat) : CaptureFree x x p := by
  induction p with
  | var z => trivial
  | bot => trivial
  | app sigma args ih => exact ih
  | imp phi psi ihphi ihpsi => exact ⟨ihphi, ihpsi⟩
  | ex z phi ih =>
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr (Or.inr ⟨hzx, ih⟩)
end Pattern
theorem Provable.ex_mono {Gamma : Set (Pattern S Nat)} {x : Nat}
    {p q : Pattern S Nat} (h : Provable Gamma (.imp p q)) :
    Provable Gamma (.imp (.ex x p) (.ex x q)) := by
  have hq : Provable Gamma (.imp q (.ex x q)) := by
    simpa only [Pattern.substVar_self] using
      (Provable.exQuant (Γ := Gamma) (Pattern.captureFree_self x q))
  exact .exGen (h.imp_trans hq) (by simp)
theorem imp_mono_taut :
    PForm.Taut
      (.imp (.imp (.atom 2) (.atom 0))
        (.imp (.imp (.atom 1) (.atom 3))
          (.imp (.imp (.atom 0) (.atom 1)) (.imp (.atom 2) (.atom 3))))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> cases h3 : v 3 <;>
    simp [PForm.eval, h0, h1, h2, h3]
theorem Provable.imp_mono {Gamma : Set (Pattern S Nat)}
    {p p' q q' : Pattern S Nat}
    (hp : Provable Gamma (.imp p' p)) (hq : Provable Gamma (.imp q q')) :
    Provable Gamma (.imp (.imp p q) (.imp p' q')) := by
  have ht : Provable Gamma
      (.imp (.imp p' p) (.imp (.imp q q') (.imp (.imp p q) (.imp p' q')))) := by
    exact .taut (θ := fun n =>
      if n = 0 then p else if n = 1 then q else if n = 2 then p' else q')
      imp_mono_taut
  exact .mp hq (.mp hp ht)
def replaceOn {n : Nat} (s : Finset (Fin n))
    (args args' : Fin n → Pattern S Nat) : Fin n → Pattern S Nat :=
  fun i => if i ∈ s then args' i else args i
theorem replaceOn_empty {n : Nat}
    (args args' : Fin n → Pattern S Nat) : replaceOn ∅ args args' = args := by
  funext i
  simp [replaceOn]
theorem replaceOn_univ {n : Nat}
    (args args' : Fin n → Pattern S Nat) : replaceOn Finset.univ args args' = args' := by
  funext i
  simp [replaceOn]
theorem Provable.app_mono {Gamma : Set (Pattern S Nat)} {sigma : S.Sym}
    {args args' : Fin (S.arity sigma) → Pattern S Nat}
    (h : ∀ i, Provable Gamma (.imp (args i) (args' i))) :
    Provable Gamma (.imp (.app sigma args) (.app sigma args')) := by
  classical
  have hs : ∀ s : Finset (Fin (S.arity sigma)),
      Provable Gamma (.imp (.app sigma args)
        (.app sigma (replaceOn s args args'))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [replaceOn_empty]
        exact .imp_refl Gamma _
    | @insert i s hi ih =>
        have hstep : Provable Gamma
            (.imp (.app sigma (replaceOn s args args'))
              (.app sigma (replaceOn (insert i s) args args'))) := by
          have hf := Provable.framing (σ := sigma) (i := i)
            (args := replaceOn s args args') (h i)
          have hleft : Function.update (replaceOn s args args') i (args i) =
              replaceOn s args args' := by
            funext j
            by_cases hji : j = i
            · subst j
              simp [replaceOn, hi]
            · simp [hji]
          have hright : Function.update (replaceOn s args args') i (args' i) =
              replaceOn (insert i s) args args' := by
            funext j
            by_cases hji : j = i
            · subst j
              simp [replaceOn]
            · simp [replaceOn, hji]
          simpa only [hleft, hright] using hf
        exact ih.imp_trans hstep
  rw [← replaceOn_univ args args']
  exact hs Finset.univ
namespace Pattern
open scoped BigOperators
def complexity : Pattern S Nat → Nat
  | .var _ => 1
  | .bot => 1
  | .app _ args => 1 + ∑ i, (args i).complexity
  | .imp p q => 1 + p.complexity + q.complexity
  | .ex _ p => 1 + p.complexity
structure AlphaEq (p q : Pattern S Nat) : Prop where
  forward : ∀ Gamma : Set (Pattern S Nat), Provable Gamma (.imp p q)
  backward : ∀ Gamma : Set (Pattern S Nat), Provable Gamma (.imp q p)
  complexity_eq : p.complexity = q.complexity
namespace AlphaEq
theorem imp {p p' q q' : Pattern S Nat} (hp : AlphaEq p p') (hq : AlphaEq q q') :
    AlphaEq (.imp p q) (.imp p' q') :=
  ⟨fun Gamma => .imp_mono (hp.backward Gamma) (hq.forward Gamma),
   fun Gamma => .imp_mono (hp.forward Gamma) (hq.backward Gamma),
   by simp [complexity, hp.complexity_eq, hq.complexity_eq]⟩
theorem app {sigma : S.Sym} {args args' : Fin (S.arity sigma) → Pattern S Nat}
    (h : ∀ i, AlphaEq (args i) (args' i)) :
    AlphaEq (.app sigma args) (.app sigma args') :=
  ⟨fun Gamma => .app_mono (fun i => (h i).forward Gamma),
   fun Gamma => .app_mono (fun i => (h i).backward Gamma),
   by
     simp only [complexity, Nat.add_left_cancel_iff]
     exact Finset.sum_congr rfl (fun i _ => (h i).complexity_eq)⟩
theorem ex (x : Nat) {p q : Pattern S Nat} (h : AlphaEq p q) :
    AlphaEq (.ex x p) (.ex x q) :=
  ⟨fun Gamma => (h.forward Gamma).ex_mono,
   fun Gamma => (h.backward Gamma).ex_mono,
   by simp [complexity, h.complexity_eq]⟩
end AlphaEq
def AvoidsBinder (y : Nat) : Pattern S Nat → Prop
  | .var _ => True
  | .bot => True
  | .app _ args => ∀ i, AvoidsBinder y (args i)
  | .imp p q => AvoidsBinder y p ∧ AvoidsBinder y q
  | .ex z p => z ≠ y ∧ AvoidsBinder y p
def avoidBinder (y : Nat) : Pattern S Nat → Pattern S Nat
  | .var x => .var x
  | .bot => .bot
  | .app sigma args => .app sigma (fun i => avoidBinder y (args i))
  | .imp p q => .imp (avoidBinder y p) (avoidBinder y q)
  | .ex z p =>
      let q := avoidBinder y p
      if _h : z = y then
        let w := (Pattern.ex y q).fresh
        Pattern.ex w (substVar y w q)
      else
        Pattern.ex z q
theorem AvoidsBinder.substVar {y x z : Nat} {p : Pattern S Nat}
    (h : AvoidsBinder y p) : AvoidsBinder y (substVar x z p) := by
  induction p with
  | var a =>
      rw [MatchingLogic.substVar]
      split <;> trivial
  | bot => trivial
  | app sigma args ih => exact fun i => ih i (h i)
  | imp p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | ex a p ih =>
      by_cases hax : a = x
      · rw [MatchingLogic.substVar, if_pos hax]
        exact h
      · rw [MatchingLogic.substVar, if_neg hax]
        change a ≠ y ∧ AvoidsBinder y (MatchingLogic.substVar x z p)
        exact ⟨h.1, ih h.2⟩
def captureAvoidingSubst (x y : Nat) (p : Pattern S Nat) : Pattern S Nat :=
  substVar x y (avoidBinder y p)
def IsCaptureAvoidingSubst (x y : Nat) (p q : Pattern S Nat) : Prop :=
  ∃ p', AlphaEq p p' ∧ CaptureFree x y p' ∧ q = substVar x y p'
end Pattern
namespace Pattern
end Pattern
end MatchingLogic


