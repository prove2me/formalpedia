-- Prove2me | Definitions.Def_SZ_Slice
-- name    : SZ_Slice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:38:50.034811+00:00
-- url     : https://prove2.me/theorems/d128d494-bd9e-41e5-9683-630b8af10b37
-- title:
--   Slice
-- statement:
--   Definitions and structural lemmas for Slice, from Ralf Stephan (rwst/Square-Roots; see pinned CC0-1.0 LICENSE and source headers)'s pinned Even integral parts of powers of square roots and Dubickas Problem 3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
set_option autoImplicit false
namespace SZ
open Filter Topology
structure Slice where
  /-- the base -/
  m : ℕ
  /-- the modulus: the digit alphabet is the multiples of `p` up to `e` -/
  p : ℤ
  /-- the largest digit -/
  e : ℤ
  /-- the window `M(1+√m)` -/
  U : ℝ
  three_le : 3 ≤ m
  not_square : ¬ IsSquare m
  two_le_p : 2 ≤ p
  p_le_e : p ≤ e
  p_dvd_e : p ∣ e
  e_le : e ≤ (m : ℤ) - 1
  U_def : ((m : ℝ) - 1) * U = (e : ℝ) * (1 + Real.sqrt m)
  p_le_U : (p : ℝ) ≤ U
  gap : (p : ℝ) * Real.sqrt m - (e : ℝ) ≤ U
namespace Slice
variable (S : Slice)
noncomputable def sq : ℝ := Real.sqrt S.m
noncomputable def M : ℝ := (S.e : ℝ) / ((S.m : ℝ) - 1)
def PDigit (d : ℤ) : Prop := S.p ∣ d ∧ 0 ≤ d ∧ d ≤ S.e
noncomputable def val (c : ℤ × ℤ) : ℝ := (c.1 : ℝ) + (c.2 : ℝ) * S.sq
noncomputable def bsel (w : ℝ) : ℤ := min S.e (S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋)
noncomputable def asel (w : ℝ) : ℤ :=
  S.p * max 0 ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉
noncomputable def pick (w : ℝ) : ℤ × ℤ := (S.asel w, S.bsel w)
noncomputable def W (S : Slice) (w₀ : ℝ) : ℕ → ℝ
  | 0 => w₀
  | k + 1 => (S.m : ℝ) * (W S w₀ k - S.val (S.pick (W S w₀ k)))
noncomputable def dA (S : Slice) (w₀ : ℝ) (k : ℕ) : ℤ := S.asel (S.W w₀ k)
noncomputable def dB (S : Slice) (w₀ : ℝ) (k : ℕ) : ℤ := S.bsel (S.W w₀ k)
variable {S}
noncomputable def sigma (S : Slice) (j k₀ : ℤ) : ℝ :=
  ((S.p : ℝ) * (k₀ : ℝ) + S.M) * S.sq - (S.p : ℝ) * (j : ℝ)
noncomputable def w0 (S : Slice) (j k₀ : ℤ) : ℝ := (S.m : ℝ) * S.sigma j k₀
end Slice
end SZ


