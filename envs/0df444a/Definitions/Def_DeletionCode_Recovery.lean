-- Prove2me | Definitions.Def_DeletionCode_Recovery
-- name    : DeletionCode_Recovery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T04:59:50.401592+00:00
-- url     : https://prove2.me/theorems/860bac9c-0b87-4982-b6a6-8478b30c2188
-- title:
--   Recovery
-- statement:
--   Definitions and structural lemmas for Recovery, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.Recovery
abbrev Slot := Fin 3
def AdjSlot (a b : Slot) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val
inductive Reach {B : Type*} (adj : B → B → Prop) : B → B → Prop
  | refl (b : B) : Reach adj b b
  | tail {a b c : B} : Reach adj a b → adj b c → Reach adj a c
structure Data (B : Type*) where
  rank : B → ℕ
  source : B → Slot → Option B
  earlier : ∀ b w a, source b w = some a → rank a < rank b
  adjacent : B → B → Prop
  root : B → Prop
  rooted : ∀ b, ∃ r, root r ∧ Reach adjacent r b
structure State (B : Type*) where
  seed : B → Option Slot
  filled : Finset (B × Slot)
variable {B : Type*} [DecidableEq B]
namespace State
def Started (s : State B) (b : B) : Prop := s.seed b ≠ none
def Done (s : State B) (b : B) (w : Slot) : Prop := (b, w) ∈ s.filled
def Complete (s : State B) (b : B) : Prop := ∀ w, s.Done b w
def Ready (s : State B) (b : B) (w : Slot) : Prop :=
  s.seed b = some w ∨ ∃ v, s.Done b v ∧ AdjSlot v w
def start (s : State B) (b : B) (w : Slot) : State B :=
  ⟨Function.update s.seed b (some w), s.filled⟩
def fill (s : State B) (b : B) (w : Slot) : State B :=
  ⟨s.seed, insert (b, w) s.filled⟩
def WellFormed (M : Data B) (s : State B) : Prop :=
  (∀ b w, s.Done b w → s.Started b) ∧
  (∀ b, M.root b → s.Complete b)
end State
open State
inductive Step (M : Data B) : State B → State B → Prop
  | startAdjacent (s : State B) (a b : B) (w : Slot)
      (ha : s.Complete a) (hab : M.adjacent a b) (hb : ¬ s.Started b) :
      Step M s (s.start b w)
  | startSupplier (s : State B) (b a : B) (w v : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = some a) (ha : ¬ s.Started a) :
      Step M s (s.start a v)
  | fillBase (s : State B) (b : B) (w : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = none) : Step M s (s.fill b w)
  | fillSupplier (s : State B) (b a : B) (w : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = some a) (ha : s.Complete a) :
      Step M s (s.fill b w)
section Finite
variable [Fintype B]
namespace State
def startedSet (s : State B) : Finset B :=
  Finset.univ.filter (fun b => s.seed b ≠ none)
def score (s : State B) : ℕ := s.startedSet.card + s.filled.card
end State
inductive Trace (M : Data B) : ℕ → State B → State B → Prop
  | nil (s : State B) : Trace M 0 s s
  | cons {m : ℕ} {s s' s'' : State B} :
      Step M s s' → Trace M m s' s'' → Trace M (m + 1) s s''
noncomputable def initial (M : Data B) : State B := by
  classical
  exact ⟨fun b => if M.root b then some 0 else none,
    Finset.univ.filter (fun p : B × Slot => M.root p.1)⟩
end Finite
end DeletionCode.Recovery


