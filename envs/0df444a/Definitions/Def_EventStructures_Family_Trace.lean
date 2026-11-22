-- Prove2me | Definitions.Def_EventStructures_Family_Trace
-- name    : EventStructures_Family_Trace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:41:35.788522+00:00
-- url     : https://prove2.me/theorems/3c5fae9e-7768-4120-929f-1276fa4e4535
-- title:
--   Trace
-- statement:
--   Definitions and structural lemmas for Trace, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Theorems.Thm_ConfFamily_Indep_symm

set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
inductive TraceEquiv : List α → List α → Prop
  | refl (t : List α) : TraceEquiv t t
  | swap {e₁ e₂ : α} {t₁ t₂ t₃ : List α} :
      (ind : R e₁ e₂) →
      TraceEquiv (t₁ ++ e₁ :: e₂ :: t₂) t₃ →
      TraceEquiv (t₁ ++ e₂ :: e₁ :: t₂) t₃
local infixr:60 " ≈ₜ " => TraceEquiv R
@[simp] def labels (t : List α) : List L := t.map lbl
namespace Trace
def LabelEquiv (t₁ t₂ : List α) : Prop := labels lbl t₁ = labels lbl t₂
instance labelEquiv_refl : Std.Refl (LabelEquiv lbl) := ⟨fun _ => rfl⟩
instance labelEquiv_symm : Std.Symm (LabelEquiv lbl) := ⟨fun _ _ h => h.symm⟩
instance labelEquiv_trans : IsTrans (List α) (LabelEquiv lbl) :=
  ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
def LabelRespecting : Prop := ∀ {e₁ e₂ : α}, R e₁ e₂ → lbl e₁ = lbl e₂
instance traceEquiv_refl : Std.Refl (TraceEquiv R) :=
  ⟨TraceEquiv.refl⟩
instance traceEquiv_trans : IsTrans (List α) (TraceEquiv R) := by
  refine ⟨fun t₁ t₂ t₃ h₁₂ h₂₃ => ?_⟩
  induction h₁₂ with
  | refl _ => exact h₂₃
  | swap ind _ ih => exact TraceEquiv.swap ind (ih h₂₃)
lemma traceEquiv_symm (hsymm : Std.Symm R) : Std.Symm (TraceEquiv R) := by
  refine ⟨fun t₁ t₂ h => ?_⟩
  induction h with
  | refl _ => exact TraceEquiv.refl _
  | @swap e₁ e₂ t₁' t₂' t₃' ind _ ih =>
    exact _root_.trans ih (TraceEquiv.swap (hsymm.symm _ _ ind) (TraceEquiv.refl _))
theorem traceEquivEquivalence (hsymm : Std.Symm R) : Equivalence (TraceEquiv R) where
  refl := (traceEquiv_refl R).refl
  symm h := (traceEquiv_symm R hsymm).symm _ _ h
  trans h₁ h₂ := _root_.trans h₁ h₂
def traceEquivSetoid (hsymm : Std.Symm R) : Setoid (List α) where
  r := TraceEquiv R
  iseqv := traceEquivEquivalence R hsymm
end Trace
def reach {L : Type*} (F : ConfFamily L) (c : Set F.Event) (t : List F.Event) : Set F.Event :=
  c ∪ {x | x ∈ t}
namespace ConfFamily
variable {L : Type*} {F : ConfFamily L}
inductive TraceEquivFrom (F : ConfFamily L) (c : Set F.Event) :
    List F.Event → List F.Event → Prop
  | refl (t : List F.Event) : TraceEquivFrom F c t t
  | swap {e₁ e₂ : F.Event} {p t t' : List F.Event} :
      F.Indep (reach F c p) e₁ e₂ →
      TraceEquivFrom F c (p ++ e₁ :: e₂ :: t) t' →
      TraceEquivFrom F c (p ++ e₂ :: e₁ :: t) t'
namespace TraceEquivFrom
end TraceEquivFrom
end ConfFamily


