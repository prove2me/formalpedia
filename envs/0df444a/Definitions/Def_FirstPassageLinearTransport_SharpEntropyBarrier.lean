-- Prove2me | Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
-- name    : FirstPassageLinearTransport_SharpEntropyBarrier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:12:54.892317+00:00
-- url     : https://prove2.me/theorems/91fa6634-439a-5e62-afed-c9df03ad3059
-- title:
--   Sharp Entropy Barrier
-- statement:
--   Definitions and structural lemmas for Sharp Entropy Barrier, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
def boolSupport {r : ℕ} (v : Fin r → Bool) : Finset (Fin r) :=
  Finset.univ.filter fun i => v i = true
noncomputable def boolWordFinsetEquiv (r : ℕ) :
    (Fin r → Bool) ≃ Finset (Fin r) where
  toFun := boolSupport
  invFun := fun s i => decide (i ∈ s)
  left_inv := by
    intro v
    funext i
    cases h : v i <;> simp [boolSupport, h]
  right_inv := by
    intro s
    ext i
    simp [boolSupport]
def binomialUpperTail (r k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc k r, r.choose j
def stirlingCore (n : ℕ) : ℝ :=
  Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n
def binomialLogWeight (r k : ℕ) : ℝ :=
  (r : ℝ) * Real.log r -
    (k : ℝ) * Real.log k -
      ((r - k : ℕ) : ℝ) * Real.log (r - k)
end
end FirstPassageLinearTransport


