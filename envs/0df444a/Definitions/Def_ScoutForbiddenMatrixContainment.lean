-- Prove2me | Definitions.Def_ScoutForbiddenMatrixContainment
-- name    : ScoutForbiddenMatrixContainment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:12:26.0213+00:00
-- url     : https://prove2.me/theorems/1f515890-4402-42f1-a927-fe9d300c3b74
-- title:
--   Containment
-- statement:
--   Definitions and structural lemmas for Containment, from Yaël Dillies and the Forbidden Matrix contributors's pinned Forbidden-matrix containment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Containment.lean

module
public import Mathlib.Data.Fintype.Pi
set_option autoImplicit true
@[expose] public section
@[expose] public section
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  {P : α → β → Prop} {M : γ → δ → Prop}
def Contains (P : α → β → Prop) (M : γ → δ → Prop) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)
instance {P : α → β → Prop} {M : γ → δ → Prop} [DecidableRel P] [DecidableRel M]
    [DecidableLT α] [DecidableLT β] [DecidableLT γ] [DecidableLT δ]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] : Decidable (Contains P M) :=
  inferInstanceAs <| Decidable <|
    ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)


