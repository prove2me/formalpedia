-- Prove2me | Definitions.Def_ClauseBound_Part_Bits
-- name    : ClauseBound_Part_Bits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:16:04.765426+00:00
-- url     : https://prove2.me/theorems/5418f4c4-c6ba-40db-a35a-e56fc05aeb6d
-- title:
--   Bits
-- statement:
--   Definitions and structural lemmas for Bits, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bits.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_PartitionStatement
import Definitions.Def_ClauseBound_Part_Rec
import Theorems.Thm_ClauseBound_Part_mul_p_eq
import Theorems.Thm_ClauseBound_Part_p_pos
import Theorems.Thm_ClauseBound_Part_p_zero

set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Part.Bits
open Finset Partitions
theorem gauss (E : ℕ) : E * (E + 1) ≤ 2 * ∑ v ∈ Icc 1 E, v := by
  induction E with
  | zero => simp
  | succ E ih =>
    rw [sum_Icc_succ_top (by omega)]
    nlinarith
theorem succ_le_two_mul_p (E : ℕ) : E + 1 ≤ 2 * p E := by
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · rw [p_zero]
    norm_num
  have h1 : ∑ v ∈ Icc 1 E, v ≤ E * p E := by
    rw [mul_p_eq]
    refine sum_le_sum fun v hv => ?_
    have hv' := mem_Icc.1 hv
    have h1 : 1 ∈ Icc 1 (E / v) := mem_Icc.2 ⟨le_rfl, (Nat.le_div_iff_mul_le hv'.1).2 (by omega)⟩
    calc v ≤ v * p (E - 1 * v) := Nat.le_mul_of_pos_right _ (p_pos _)
      _ ≤ _ := single_le_sum (f := fun k => v * p (E - k * v)) (fun _ _ => Nat.zero_le _) h1
  have h2 := gauss E
  have h3 : E * (E + 1) ≤ E * (2 * p E) := by nlinarith
  exact Nat.le_of_mul_le_mul_left h3 hE
end ClauseBound.Part.Bits
namespace ClauseBound.Part
open Finset Partitions
@[expose] def pz (E : ℤ) : ℕ := if 0 ≤ E then p E.toNat else 0
theorem exists_h (lam : ℕ) : ∃ h : ℕ, 2 ≤ h ∧ 2 ^ lam ≤ p h := by
  refine ⟨2 ^ (lam + 1), ?_, ?_⟩
  · have := Nat.one_le_two_pow (n := lam)
    rw [pow_succ]
    omega
  · have h1 := Bits.succ_le_two_mul_p (2 ^ (lam + 1))
    have h2 : 2 ^ (lam + 1) = 2 * 2 ^ lam := pow_succ' 2 lam
    omega
open Classical in
/-- The least h ≥ 2 with p(h) ≥ 2^λ. -/
@[expose] noncomputable def hOf (lam : ℕ) : ℕ := Nat.find (exists_h lam)
@[expose] def Rrow (h : ℕ) (s : ℤ) : ℕ := ∑ i ∈ range (2 * h + 1), pz (s + i)
@[expose] def Rcol (h : ℕ) (s : ℤ) : ℕ := ∑ i ∈ range (2 * h + 1), pz (2 * h - s - i)
end ClauseBound.Part
namespace ClauseBound.Part.Bits
open Finset Partitions Real
end ClauseBound.Part.Bits
namespace ClauseBound.Part
open Finset Partitions
end ClauseBound.Part
namespace ClauseBound.Part.Bits
open Finset Partitions Real
end ClauseBound.Part.Bits
namespace ClauseBound.Part
open Finset Partitions
end ClauseBound.Part


