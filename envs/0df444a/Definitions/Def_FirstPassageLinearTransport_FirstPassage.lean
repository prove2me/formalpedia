-- Prove2me | Definitions.Def_FirstPassageLinearTransport_FirstPassage
-- name    : FirstPassageLinearTransport_FirstPassage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:59:19.47697+00:00
-- url     : https://prove2.me/theorems/eae3fba7-71a7-56c5-9989-9fb726793865
-- title:
--   First Passage
-- statement:
--   Definitions and structural lemmas for First Passage, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean

import Definitions.Def_FirstPassageLinearTransport_Parity
set_option autoImplicit true
namespace FirstPassageLinearTransport
def IsFirstPassage (Y n h : ℕ) : Prop :=
  orbit h n ≤ Y ∧ ∀ j : ℕ, j < h → Y < orbit j n
def reverseOddFactor (x : ℕ) : ℚ :=
  1 - 1 / (2 * (x : ℚ))
def reverseStepFactor (n i : ℕ) : ℚ :=
  if (parityBit n i : ℕ) = 1 then reverseOddFactor (orbit (i + 1) n) else 1
def reverseProduct (n h : ℕ) : ℚ :=
  ∏ i ∈ Finset.range h, reverseStepFactor n i
def reverseLoss (n i : ℕ) : ℚ :=
  if (parityBit n i : ℕ) = 1 then
    1 / (2 * (orbit (i + 1) n : ℚ))
  else 0
def reverseScale (n h : ℕ) : ℚ :=
  (2 : ℚ) ^ h * (orbit h n : ℚ) / (3 : ℚ) ^ (oddCount n h)
noncomputable def taggedFiber (M Y h y : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n => IsFirstPassage Y n h ∧ orbit h n = y
end FirstPassageLinearTransport


