-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExistsPeriodRingDataHolds
-- name    : Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExistsPeriodRingDataHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:38.833939+00:00
-- url     : https://prove2.me/theorems/de5d9dd4-ca2d-475b-a31d-6d313bc4aad9
-- title:
--   Exists Period Ring Data Holds
-- statement:
--   Definitions and structural lemmas for Exists Period Ring Data Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExistsPeriodRingDataHolds.lean

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
open LaurentPolynomial
def lpScaleF (c : ℚˣ) : Multiplicative ℤ →* LaurentPolynomial ℚ where
  toFun m := ((c ^ m.toAdd : ℚˣ) : ℚ) • T m.toAdd
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, zpow_add, Units.val_mul, T_add, smul_mul_smul_comm]
@[simp] lemma lpScaleF_apply (c : ℚˣ) (m : Multiplicative ℤ) :
    lpScaleF c m = ((c ^ m.toAdd : ℚˣ) : ℚ) • T m.toAdd := rfl
def lpScale (c : ℚˣ) : LaurentPolynomial ℚ →ₐ[ℚ] LaurentPolynomial ℚ :=
  AddMonoidAlgebra.lift ℚ (LaurentPolynomial ℚ) ℤ (lpScaleF c)
lemma lpScale_coeff (c : ℚˣ) (f : LaurentPolynomial ℚ) (m : ℤ) :
    (lpScale c f).coeff m = ((c ^ m : ℚˣ) : ℚ) * f.coeff m := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hp, hq, mul_add]
  | C_mul_T n a =>
    have h1 : lpScale c (T n) = ((c ^ n : ℚˣ) : ℚ) • T n := by
      unfold lpScale T
      rw [AddMonoidAlgebra.lift_single, one_smul, lpScaleF_apply]
      rfl
    have h2 : (C a * T n : LaurentPolynomial ℚ) = a • T n := by
      rw [C_eq_algebraMap, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [h2, map_smul, h1, smul_smul, AddMonoidAlgebra.coeff_smul_apply,
      AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, smul_eq_mul]
    by_cases h : n = m
    · subst h
      simp only [if_true]
      ring
    · simp [h]
def lpScaleE (c : ℚˣ) : LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ :=
  AlgEquiv.ofAlgHom (lpScale c) (lpScale c⁻¹)
    (AlgHom.ext fun f => LaurentPolynomial.ext fun m => by
      simp [lpScale_coeff, ← mul_assoc]
      rw [mul_inv_cancel₀ (zpow_ne_zero _ c.ne_zero), one_mul])
    (AlgHom.ext fun f => LaurentPolynomial.ext fun m => by
      simp [lpScale_coeff, ← mul_assoc]
      rw [inv_mul_cancel₀ (zpow_ne_zero _ c.ne_zero), one_mul])
lemma lpScaleE_coeff (c : ℚˣ) (f : LaurentPolynomial ℚ) (m : ℤ) :
    (lpScaleE c f).coeff m = ((c ^ m : ℚˣ) : ℚ) * f.coeff m := by
  show (lpScale c f).coeff m = _
  rw [lpScale_coeff]
def lpScaleHom : ℚˣ →* (LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ) where
  toFun := lpScaleE
  map_one' := AlgEquiv.ext fun f => LaurentPolynomial.ext fun m => by simp [lpScaleE_coeff]
  map_mul' c d := AlgEquiv.ext fun f => LaurentPolynomial.ext fun m => by
    simp [lpScaleE_coeff, AlgEquiv.mul_apply, mul_zpow, mul_assoc]
@[simp] lemma lpScaleHom_apply (c : ℚˣ) : lpScaleHom c = lpScaleE c := rfl
def lpTwo : ℚˣ := Units.mk0 2 (by norm_num)
@[simp] lemma lpTwo_val : (lpTwo : ℚ) = 2 := rfl
@[simp] lemma lpTwo_zpow (m : ℤ) : ((lpTwo ^ m : ℚˣ) : ℚ) = (2 : ℚ) ^ m := by
  rw [Units.val_zpow_eq_zpow_val, lpTwo_val]
def lpFil (a : ℤ) : Submodule ℚ (LaurentPolynomial ℚ) where
  carrier := {f | ∀ m < a, f.coeff m = 0}
  add_mem' {x y} hx hy m hm := by simp [AddMonoidAlgebra.coeff_add, hx m hm, hy m hm]
  zero_mem' m _ := by simp
  smul_mem' c x hx m hm := by simp [hx m hm]
end Formalism.WeaklyAdmissibleFiltrations


