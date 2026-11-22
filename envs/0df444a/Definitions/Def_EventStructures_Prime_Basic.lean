-- Prove2me | Definitions.Def_EventStructures_Prime_Basic
-- name    : EventStructures_Prime_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:35:48.660776+00:00
-- url     : https://prove2.me/theorems/00ec5658-fa75-4449-881a-3109124b91df
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Basic.lean

import Mathlib.Order.Basic
import Mathlib.Data.Set.Finite.Basic
set_option autoImplicit true
structure PES (Label : Type*) where
  Event : Type*
  [poEvent : PartialOrder Event]
  conflict : Event → Event → Prop
  label : Event → Label
  conflict_irrefl : ∀ e, ¬ conflict e e
  conflict_symm : Std.Symm conflict
  conflict_hereditary : ∀ {e₁ e₂ e₃}, conflict e₁ e₂ → e₂ ≤ e₃ → conflict e₁ e₃
namespace PES
variable {L : Type*} (es : PES L)
instance : PartialOrder es.Event := es.poEvent
local infixl:50 " # " => es.conflict
@[simp]
def consistent (e₁ e₂ : es.Event) : Prop := ¬ (e₁ # e₂)
instance consistent_refl : Std.Refl es.consistent := ⟨es.conflict_irrefl⟩
instance consistent_symm : Std.Symm es.consistent :=
  ⟨fun _ _ h h' => h (es.conflict_symm.symm _ _ h')⟩
@[simp]
def concurrent (e₁ e₂ : es.Event) : Prop :=
  es.consistent e₁ e₂ ∧ ¬ (e₁ ≤ e₂) ∧ ¬ (e₂ ≤ e₁)
local infixl:50 " ⋈ " => es.concurrent
instance concurrent_symm : Std.Symm es.concurrent := by
  refine ⟨fun e₁ e₂ h => ?_⟩
  rcases h with ⟨hCons, hNotLe12, hNotLe21⟩
  refine ⟨?_, hNotLe21, hNotLe12⟩
  exact (consistent_symm es).symm _ _ hCons
@[simp]
def minimalConflict (e₁ e₂ : es.Event) : Prop :=
  es.conflict e₁ e₂ ∧
  ∀ e₁' e₂', e₁' ≤ e₁ → e₂' ≤ e₂ → es.conflict e₁' e₂' → e₁' = e₁ ∧ e₂' = e₂
local infixl:50 " ## " => es.minimalConflict
instance minimalConflict_symm : Std.Symm es.minimalConflict := by
  refine ⟨fun e₁ e₂ h => ?_⟩
  obtain ⟨hConf, hMin⟩ := h
  refine ⟨es.conflict_symm.symm _ _ hConf, ?_⟩
  intro e₂' e₁' he₂ he₁ hConf'
  have := hMin e₁' e₂' he₁ he₂ (es.conflict_symm.symm _ _ hConf')
  exact ⟨this.2, this.1⟩
@[simp] def past (e : es.Event) : Set es.Event := {x | x < e}
@[simp] def future (e : es.Event) : Set es.Event := {x | e ≤ x}
end PES
class DecidablePES {L : Type*} (es : PES L) where
  decEq : DecidableEq es.Event
  decLt : DecidableRel ((· < ·) : es.Event → es.Event → Prop)
set_option warn.classDefReducibility false in
attribute [instance] DecidablePES.decEq DecidablePES.decLt
instance PES.decLe {L : Type*} (es : PES L) [DecidablePES es] :
    DecidableRel ((· ≤ ·) : es.Event → es.Event → Prop) := fun a b =>
  if hab : a = b then isTrue (hab ▸ le_refl a)
  else if hlt : a < b then isTrue (le_of_lt hlt)
  else isFalse fun h => (lt_or_eq_of_le h).elim hlt hab


