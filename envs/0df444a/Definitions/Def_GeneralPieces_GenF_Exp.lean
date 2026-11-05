-- Prove2me | Definitions.Def_GeneralPieces_GenF_Exp
-- name    : GeneralPieces_GenF_Exp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:18.705051+00:00
-- url     : https://prove2.me/theorems/2c11e1d6-04d1-420c-87a8-0010aaf277ff
-- title:
--   Exp
-- statement:
--   Definitions and structural lemmas for Exp, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Exp.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
section
namespace GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
noncomputable def expN (N : ℕ) (w : MvPowerSeries X R) : MvPowerSeries X R := ∑ n ∈ range N, ((n.factorial : ℚ)⁻¹) • w ^ n
noncomputable def expW (w : MvPowerSeries X R) : MvPowerSeries X R := fun α => coeff α (expN (α.degree + 1) w)
noncomputable def twF (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (f : MvPowerSeries X ℚ) : MvPowerSeries X R := fun α => algebraMap ℚ R (coeff α f) * ε ^ wt α
theorem coeff_twF (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (f : MvPowerSeries X ℚ) (α : X →₀ ℕ) : coeff α (twF wt ε f) = algebraMap ℚ R (coeff α f) * ε ^ wt α := rfl
noncomputable def tw (wt : (X →₀ ℕ) →+ ℕ) (ε : R) : MvPowerSeries X ℚ →+* MvPowerSeries X R where
  toFun := twF wt ε
  map_one' := by
    classical
    ext α
    rw [coeff_twF, coeff_one, coeff_one]
    split_ifs with h
    · rw [h, map_zero, pow_zero, map_one, mul_one]
    · rw [map_zero, zero_mul]
  map_mul' f g := by
    classical
    ext α
    rw [coeff_twF, coeff_mul, coeff_mul, map_sum, sum_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [coeff_twF, coeff_twF, ← mem_antidiagonal.1 hp, map_add, pow_add, map_mul]
    ring
  map_zero' := by
    ext α
    rw [coeff_twF, map_zero, map_zero, map_zero, zero_mul]
  map_add' f g := by
    ext α
    rw [coeff_twF, map_add, map_add, map_add, add_mul, coeff_twF, coeff_twF]
end GeneralPieces.GenF


