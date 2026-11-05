-- Prove2me | Definitions.Def_GeneralPieces_Series_Deriv
-- name    : GeneralPieces_Series_Deriv
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:28:54.185206+00:00
-- url     : https://prove2.me/theorems/935edc38-8c0b-40f5-9c3d-8a248835e8d3
-- title:
--   Deriv
-- statement:
--   Definitions and structural lemmas for Deriv, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Series_ext_cf
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero


set_option autoImplicit false
section
section
namespace GeneralPieces.Series
open LaurentPolynomial
section Twist
variable {R : Type} [CommRing R]
def twist (D : ℤ → R →+ R) (f : HahnSeries ℤ R) : HahnSeries ℤ R where
  coeff y := D y (f.coeff y)
  isPWO_support' := f.isPWO_support.mono fun y hy h => hy (by simp [h])
theorem support_twist (D : ℤ → R →+ R) (f : HahnSeries ℤ R) : (twist D f).support ⊆ f.support :=
  fun y hy h => hy (by simp [twist, h])
theorem twist_mul (D : ℤ → R →+ R) (hD : ∀ i j a b, D (i + j) (a * b) = D i a * b + a * D j b) (f g : HahnSeries ℤ R) :
    twist D (f * g) = twist D f * g + f * twist D g := by
  ext y
  rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' f.isPWO_support (support_twist D f),
    HahnSeries.coeff_mul_right' g.isPWO_support (support_twist D g), ← Finset.sum_add_distrib]
  change D y ((f * g).coeff y) = _
  rw [HahnSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have h : ij.1 + ij.2 = y := (Finset.mem_antidiagonal.1 hij).2.2
  rw [← h, hD]
  rfl
end Twist
noncomputable def thI : LaurentPolynomial ℚ →+ LaurentPolynomial ℚ where
  toFun p := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset p.coeff.support (fun x => (x : ℚ) * p.coeff x) fun x h => by
    rw [Finsupp.mem_support_iff]
    exact right_ne_zero_of_mul h)
  map_zero' := by ext x; simp
  map_add' p q := by ext x; simp [mul_add]
theorem coeff_thI (p : LaurentPolynomial ℚ) (x : ℤ) : (thI p).coeff x = x * p.coeff x := rfl
theorem thI_single (a : ℤ) (r : ℚ) : thI (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single a ((a : ℚ) * r) := by
  ext x
  rw [coeff_thI, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]
theorem thI_mul (p q : LaurentPolynomial ℚ) : thI (p * q) = thI p * q + p * thI q := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul, map_add, hf, hg, map_add]; ring
  | single a r =>
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => rw [mul_add, map_add, hf, hg, map_add]; ring
    | single b s =>
      rw [thI_single, thI_single, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, thI_single,
        ← AddMonoidAlgebra.single_add]
      congr 1
      push_cast
      ring
noncomputable def thU (f : S) : S := twist (fun _ => thI) f
noncomputable def thV (f : S) : S := twist (fun y => (y : ℚ) • AddMonoidHom.id _) f
theorem cf_thU (f : S) (x y : ℤ) : cf (thU f) x y = x * cf f x y := rfl
theorem cf_thV (f : S) (x y : ℤ) : cf (thV f) x y = y * cf f x y := rfl
theorem thU_mul (f g : S) : thU (f * g) = thU f * g + f * thU g := twist_mul _ (fun _ _ a b => thI_mul a b) f g
theorem thV_mul (f g : S) : thV (f * g) = thV f * g + f * thV g :=
  twist_mul _ (fun i j a b => by
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
    push_cast
    rw [add_smul, smul_mul_assoc, mul_smul_comm]) f g
theorem thU_add (f g : S) : thU (f + g) = thU f + thU g := ext_cf fun x y => by simp [cf_thU, mul_add]
theorem thV_add (f g : S) : thV (f + g) = thV f + thV g := ext_cf fun x y => by simp [cf_thV, mul_add]
theorem thU_smul (r : ℚ) (f : S) : thU (r • f) = r • thU f := ext_cf fun x y => by simp [cf_thU, mul_left_comm]
theorem thV_smul (r : ℚ) (f : S) : thV (r • f) = r • thV f := ext_cf fun x y => by simp [cf_thV, mul_left_comm]
noncomputable def du : Derivation ℚ S S :=
  Derivation.mk'
    { toFun := fun f => mo (-1) 0 * thU f
      map_add' := fun f g => by rw [thU_add, mul_add]
      map_smul' := fun r f => by rw [thU_smul, mul_smul_comm, RingHom.id_apply] }
    fun a b => by
      change mo (-1) 0 * thU (a * b) = a • (mo (-1) 0 * thU b) + b • (mo (-1) 0 * thU a)
      rw [thU_mul, smul_eq_mul, smul_eq_mul]
      ring
noncomputable def dv : Derivation ℚ S S :=
  Derivation.mk'
    { toFun := fun f => mo 0 (-1) * thV f
      map_add' := fun f g => by rw [thV_add, mul_add]
      map_smul' := fun r f => by rw [thV_smul, mul_smul_comm, RingHom.id_apply] }
    fun a b => by
      change mo 0 (-1) * thV (a * b) = a • (mo 0 (-1) * thV b) + b • (mo 0 (-1) * thV a)
      rw [thV_mul, smul_eq_mul, smul_eq_mul]
      ring
noncomputable def d1P : Derivation ℚ Lp Lp := du
noncomputable def d2P : Derivation ℚ Lp Lp := dv
noncomputable def d1M : Derivation ℚ Lm Lm := dv
noncomputable def d2M : Derivation ℚ Lm Lm := du
section Abstract
variable {A : Type} [CommRing A] [Algebra ℚ A]
end Abstract
noncomputable def ser (p q : ℕ) (c : ℤ → ℚ) : S := diag (-((p : ℤ) + q)) (fun y => c (y + q)) (1 - q)
noncomputable def sumP (j n : ℕ) (c : ℤ → ℚ) : Lp := ser j n c
noncomputable def sumM (j n : ℕ) (c : ℤ → ℚ) : Lm := ser n j c
end GeneralPieces.Series


