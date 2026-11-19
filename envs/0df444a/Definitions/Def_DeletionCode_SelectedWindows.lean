-- Prove2me | Definitions.Def_DeletionCode_SelectedWindows
-- name    : DeletionCode_SelectedWindows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:00:54.155451+00:00
-- url     : https://prove2.me/theorems/4078fa9a-2c27-42a4-becb-bd07b74b9d2d
-- title:
--   Selected Windows
-- statement:
--   Definitions and structural lemmas for Selected Windows, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
set_option autoImplicit true
namespace DeletionCode.SelectedWindows
open Windows PartialWords Recovery
def windowStart (D : ℕ) (w : Slot) : ℕ :=
  if w.val = 0 then 0 else if w.val = 1 then D / 2 else D
def WindowKnown (s : Memory) (start len : ℕ) : Prop :=
  ∃ bits, readBits s start len = some bits
def SeedKnown (s : Memory) (start L k : ℕ) : Prop :=
  ∃ r bits, r + k ≤ L ∧ readBits s (start + r) k = some bits
variable {B : Type*}
structure Realizes (s : State B) (mem : B → Memory) (D : B → ℕ) (k : ℕ) : Prop where
  seed_known : ∀ b w, s.seed b = some w →
    SeedKnown (mem b) (windowStart (D b) w) (3 * (k + 1)) k
  done_known : ∀ b w, s.Done b w →
    WindowKnown (mem b) (windowStart (D b) w) (3 * (k + 1))
theorem Realizes.start [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot)
    (hseed : SeedKnown (mem b) (windowStart (D b) w) (3 * (k + 1)) k) :
    Realizes (s.start b w) mem D k where
  seed_known a v h := by
    by_cases hab : a = b
    · subst a
      have hv : w = v := by simpa [State.start] using h
      simpa [hv] using hseed
    · have hba : b ≠ a := Ne.symm hab
      exact hreal.seed_known a v (by simpa [State.start, hab, hba] using h)
  done_known a v h := hreal.done_known a v h
theorem Realizes.fill [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot)
    (hwindow : WindowKnown (mem b) (windowStart (D b) w) (3 * (k + 1))) :
    Realizes (s.fill b w) mem D k where
  seed_known a v h := hreal.seed_known a v h
  done_known a v h := by
    have hmem : (a, v) = (b, w) ∨ (a, v) ∈ s.filled := Finset.mem_insert.mp h
    rcases hmem with heq | hold
    · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact hwindow
    · exact hreal.done_known a v hold
end DeletionCode.SelectedWindows


