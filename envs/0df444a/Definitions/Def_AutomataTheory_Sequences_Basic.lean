-- Prove2me | Definitions.Def_AutomataTheory_Sequences_Basic
-- name    : AutomataTheory_Sequences_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:09:08.295293+00:00
-- url     : https://prove2.me/theorems/b3d925b7-5e3b-43f7-a57c-6988e6a9c3fe
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean

import Definitions.Def_AutomataTheory_Mathlib_Imports
set_option autoImplicit true
open Function Set Option Stream'
section List
def List.padDefault [Inhabited X] (xl : List X) : Stream' X :=
  fun k ↦ if h : k < xl.length then xl[k] else default
end List
section Stream'
namespace Stream'
variable {X : Type*}
def extract (xs : Stream' X) (m n : ℕ) : List X :=
  take (n - m) (xs.drop m)
def fixSuffix (xs : Stream' X) (n : ℕ) (x : X) : Stream' X :=
  fun k ↦ if k < n then xs k else x
theorem extract_eq_drop_take {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = take (n - m) (xs.drop m) := by
  rfl
theorem length_extract {xs : Stream' X} {m n : ℕ} :
    (xs.extract m n).length = n - m := by
  simp only [extract_eq_drop_take, length_take]
end Stream'
section Misc
end Misc


