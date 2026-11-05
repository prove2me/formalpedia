-- Prove2me | Definitions.Def_GeneralPieces_GenF_Hahn
-- name    : GeneralPieces_GenF_Hahn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:29:30.50274+00:00
-- url     : https://prove2.me/theorems/dfd51f29-c1b9-463c-acdb-48622fec9d1d
-- title:
--   Hahn
-- statement:
--   Definitions and structural lemmas for Hahn, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Hahn.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
set_option autoImplicit false
section
section
namespace GeneralPieces.GenF
open Finset HahnSeries
variable {A : Type} [CommRing A] [Algebra ℚ A]
noncomputable def hmap (d : Derivation ℚ A A) : HahnSeries ℤ A →ₗ[ℚ] HahnSeries ℤ A where
  toFun f := f.map d
  map_add' f g := by
    ext y
    simp
  map_smul' q f := by
    ext y
    simp
theorem coeff_hmap (d : Derivation ℚ A A) (f : HahnSeries ℤ A) (y : ℤ) : (hmap d f).coeff y = d (f.coeff y) := rfl
theorem support_hmap (d : Derivation ℚ A A) (f : HahnSeries ℤ A) : (hmap d f).support ⊆ f.support := fun y hy => by
  rw [mem_support] at hy ⊢
  intro h
  exact hy (by rw [coeff_hmap, h, map_zero])
noncomputable def hder (d : Derivation ℚ A A) : Derivation ℚ (HahnSeries ℤ A) (HahnSeries ℤ A) :=
  Derivation.mk' (hmap d) fun f g => by
    ext y
    rw [coeff_hmap, smul_eq_mul, smul_eq_mul, coeff_add, mul_comm g, coeff_mul, coeff_mul_right' g.isPWO_support (support_hmap d g),
      coeff_mul_left' f.isPWO_support (support_hmap d f), map_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, coeff_hmap, coeff_hmap, mul_comm (g.coeff p.2)]
end GeneralPieces.GenF


