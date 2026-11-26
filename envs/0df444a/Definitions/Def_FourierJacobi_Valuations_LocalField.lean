-- Prove2me | Definitions.Def_FourierJacobi_Valuations_LocalField
-- name    : FourierJacobi_Valuations_LocalField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:26:46.544807+00:00
-- url     : https://prove2.me/theorems/6f36b9db-9a62-4206-9a08-1e7332e92363
-- title:
--   Local Field
-- statement:
--   Definitions and structural lemmas for Local Field, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalField.lean

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
noncomputable section
open scoped WithZero
namespace FourierJacobi.Valuations
def extendedNegLog (x : ℤᵐ⁰) : WithTop ℤ :=
  WithZero.expRecOn x ⊤ (fun n => ((-n : ℤ) : WithTop ℤ))
@[simp] theorem extendedNegLog_zero : extendedNegLog 0 = ⊤ := rfl
@[simp] theorem extendedNegLog_exp (n : ℤ) :
    extendedNegLog (WithZero.exp n) = ((-n : ℤ) : WithTop ℤ) := rfl
@[simp] theorem extendedNegLog_one : extendedNegLog 1 = 0 := by
  change ((-(0 : ℤ) : ℤ) : WithTop ℤ) = 0
  simp only [neg_zero, WithTop.coe_zero]
theorem extendedNegLog_mul (x y : ℤᵐ⁰) :
    extendedNegLog (x * y) = extendedNegLog x + extendedNegLog y := by
  induction x using WithZero.expRecOn with
  | zero => simp
  | exp a =>
    induction y using WithZero.expRecOn with
    | zero => simp
    | exp b =>
      rw [← WithZero.exp_add]
      change ((-(a + b) : ℤ) : WithTop ℤ) = ((-a : ℤ) : WithTop ℤ) + ((-b : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      congr 1
      omega
theorem extendedNegLog_antitone : Antitone extendedNegLog := by
  intro x y h
  induction x using WithZero.expRecOn with
  | zero => simp
  | exp a =>
    induction y using WithZero.expRecOn with
    | zero => simp at h
    | exp b =>
      change ((-b : ℤ) : WithTop ℤ) ≤ ((-a : ℤ) : WithTop ℤ)
      exact WithTop.coe_le_coe.mpr (neg_le_neg (WithZero.exp_le_exp.mp h))
theorem extendedNegLog_max (x y : ℤᵐ⁰) :
    extendedNegLog (max x y) = min (extendedNegLog x) (extendedNegLog y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, min_eq_right (extendedNegLog_antitone h)]
  · rw [max_eq_left h, min_eq_left (extendedNegLog_antitone h)]
section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
def discreteValuation : Valuation K ℤᵐ⁰ :=
  Valuation.congr (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
    (ValuativeRel.valuation K)
def localFieldValuation : AddValuation K (WithTop ℤ) :=
  AddValuation.of (fun x => extendedNegLog (discreteValuation K x))
    (by simp) (by simp)
    (fun x y => by
      rw [← extendedNegLog_max]
      exact extendedNegLog_antitone ((discreteValuation K).map_add x y))
    (fun x y => by rw [map_mul, extendedNegLog_mul])
end LocalField
end FourierJacobi.Valuations


