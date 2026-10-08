-- Prove2me | Definitions.Def_MazurN13_FLT_Mathlib_RingTheory_Valuation_ValuationSubring_p0
-- name    : MazurN13_FLT_Mathlib_RingTheory_Valuation_ValuationSubring_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:48:08.790976+00:00
-- url     : https://prove2.me/theorems/0b94f3e3-3b31-4a50-8f34-41fc78fc1388
-- title:
--   FLT.Mathlib.RingTheory.Valuation.ValuationSubring source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Mathlib.RingTheory.Valuation.ValuationSubring

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Mathlib.RingTheory.Valuation.ValuationSubring
Original leading source comments and nonproject imports are retained below. -/
/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology

set_option autoImplicit false




/-!
# Valuation Subring

Material destined for Mathlib.
-/

@[expose] public section

variable {F : Type*} [Field F]

lemma ValuationSubring.subtype_inj {R : ValuationSubring F} {x y : R} :
    R.subtype x = R.subtype y ↔ x = y :=
  R.subtype_injective.eq_iff

theorem ValuationSubring.valued_eq_one_of_isUnit {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : IsUnit x) : Valued.v x.val = 1 := by
  obtain ⟨u, hu⟩ := hx
  apply le_antisymm ((hv.v.mem_valuationSubring_iff _).1 x.2)
  rw [← Valued.v.map_one (R := K), ← Submonoid.coe_one, ← u.mul_inv, hu,
    Submonoid.coe_mul, Valued.v.map_mul]
  nth_rw 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_right ((hv.v.mem_valuationSubring_iff _).1 (u⁻¹.val.property)) _

theorem ValuationSubring.isUnit_of_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : Valued.v x.val = 1) : IsUnit x := by
  have : IsUnit x.val := by rw [isUnit_iff_ne_zero, ne_eq, ← map_eq_zero hv.v, hx]; aesop
  obtain ⟨u, hu⟩ := this
  have hu_inv_le : Valued.v u⁻¹.val ≤ 1 := by
    rw [← one_mul (Valued.v _), ← hx, ← hu, ← Valued.v.map_mul, u.mul_inv, hu, hx, Valued.v.map_one]
  rw [isUnit_iff_exists]
  exact ⟨⟨u⁻¹.val, hu_inv_le⟩,  ⟨by aesop, by aesop⟩⟩

theorem ValuationSubring.isUnit_iff_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring) :
    IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valued_eq_one_of_isUnit x, isUnit_of_valued_eq_one x⟩


