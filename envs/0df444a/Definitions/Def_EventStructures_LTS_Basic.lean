-- Prove2me | Definitions.Def_EventStructures_LTS_Basic
-- name    : EventStructures_LTS_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:35:46.804805+00:00
-- url     : https://prove2.me/theorems/97679ef4-b180-41c6-977c-45fb0239634c
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/LTS/Basic.lean

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
set_option autoImplicit true
variable {L : Type*}
structure LTSI (L : Type*) where
  State : Type*
  init : State
  step : State → L → State → Prop
  indep : State → L → State → L → State → Prop
namespace LTSI
variable (T : LTSI L)
local notation:55 c " -[" a "]→ " c' => T.step c a c'
structure LPV : Prop where
  indep_step_left : ∀ {s a s₁ b s₂}, T.indep s a s₁ b s₂ → (s -[a]→ s₁)
  indep_step_right : ∀ {s a s₁ b s₂}, T.indep s a s₁ b s₂ → (s -[b]→ s₂)
  indep_irrefl : ∀ {s a s'}, ¬ T.indep s a s' a s'
  indep_symm : ∀ {s a s₁ b s₂}, T.indep s a s₁ b s₂ → T.indep s b s₂ a s₁
  square : ∀ {s a s₁ b s₂}, T.indep s a s₁ b s₂ →
    ∃ u, (s₁ -[b]→ u) ∧ (s₂ -[a]→ u)
end LTSI
structure Bisim (S T : LTSI L) (R : S.State → T.State → Prop) : Prop where
  init : R S.init T.init
  forward : ∀ {s t a s'}, R s t → S.step s a s' → ∃ t', T.step t a t' ∧ R s' t'
  backward : ∀ {s t a t'}, R s t → T.step t a t' → ∃ s', S.step s a s' ∧ R s' t'
def Bisimilar (S T : LTSI L) : Prop := ∃ R, Bisim S T R
inductive DirLabel (L : Type*) : Type _
  | fwd : L → DirLabel L
  | bwd : L → DirLabel L
  deriving DecidableEq
namespace DirLabel
@[simp]
def rev : DirLabel L → DirLabel L
  | fwd a => bwd a
  | bwd a => fwd a
@[simp]
def label : DirLabel L → L
  | fwd a => a
  | bwd a => a
def isFwd : DirLabel L → Prop
  | fwd _ => True
  | bwd _ => False
end DirLabel
structure RLTSI (L : Type*) extends LTSI (DirLabel L) where
  step_rev : ∀ {s a s'}, step s (DirLabel.fwd a) s' ↔ step s' (DirLabel.bwd a) s
namespace RLTSI
variable (T : RLTSI L)
local notation:55 c " -[" a "]→ " c' => T.step c a c'
structure LPV : Prop extends LTSI.LPV T.toLTSI where
  BTI : ∀ {s a s₁ b s₂},
    (s -[DirLabel.bwd a]→ s₁) → (s -[DirLabel.bwd b]→ s₂) →
    (a ≠ b ∨ s₁ ≠ s₂) →
    T.indep s (DirLabel.bwd a) s₁ (DirLabel.bwd b) s₂
end RLTSI


