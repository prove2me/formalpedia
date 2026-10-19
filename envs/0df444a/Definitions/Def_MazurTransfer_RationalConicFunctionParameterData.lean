-- Prove2me | Definitions.Def_MazurTransfer_RationalConicFunctionParameterData
-- name    : MazurTransfer_RationalConicFunctionParameterData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T16:03:10.625974+00:00
-- url     : https://prove2.me/theorems/64d7d7cd-dcf2-4b93-8ea0-693f34582ff4
-- title:
--   Rational conic function parametrization and its inverse
-- statement:
--   Over a characteristic-zero field, the original functions conicU(t), conicV(t), and slope(u,v) give the original rational conic parametrization and inverse on the specified open charts. All denominator hypotheses, the conic equation and characteristic-zero assumption of the original certificates are retained. Eight full original types and three data values are checked. Named downstream consumer: Order13ActualConicFunctionParameter.
-- source:
--   Unchanged original MazurTheorem conic/quotient declarations and proofs, Apache-2.0, Vas and contributors; formulas from XOneThirteenDescent at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Eight complete types and three data values kernel-compared with the original source.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The formulas reuse MazurTheorem XOneThirteenDescent.lean. Design boundary:
field-valued rational parametrization of the quotient conic in characteristic
zero, without ordered-field assumptions. Named downstream consumer: the
literal order-thirteen invariant function field and its Picard trace.
Public data boundary: original quotient formulas and their unchanged certificates.
Named downstream consumer: MazurTransfer.Order13ActualConicFunctionParameter,
then the actual cubic fixed-field identification.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.RationalConicFunctionParameter
variable {F : Type*} [Field F] [CharZero F]

def conicU (t : F) : F := (t ^ 2 + 4 * t - 1) / (1 - t ^ 2)
def conicV (t : F) : F := 2 * (1 + t ^ 2) / (1 - t ^ 2)
def slope (u v : F) : F := (v - 2) / (u + 1)

theorem parameter_equation (t : F) (ht : t ^ 2 ≠ 1) :
    conicV t ^ 2 = conicU t ^ 2 + 2 * conicU t + 5 := by
  have hden : 1 - t ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  simp only [conicU, conicV]
  field_simp [hden]
  ring

theorem ordinate_sub_two_ne_zero (u v : F) (hu : u + 1 ≠ 0)
    (hc : v ^ 2 = u ^ 2 + 2 * u + 5) : v - 2 ≠ 0 := by
  intro hv
  have hv2 : v = 2 := sub_eq_zero.mp hv
  have hz : (u + 1) ^ 2 = 0 := by
    rw [hv2] at hc
    linear_combination -hc
  exact (pow_ne_zero 2 hu) hz

theorem slope_sq_ne_one (u v : F) (hu : u + 1 ≠ 0)
    (hc : v ^ 2 = u ^ 2 + 2 * u + 5) : slope u v ^ 2 ≠ 1 := by
  intro ht
  simp only [slope] at ht
  field_simp [hu] at ht
  have hz : (4 : F) * (v - 2) = 0 := by linear_combination hc - ht
  exact (mul_ne_zero (by norm_num : (4 : F) ≠ 0)
    (ordinate_sub_two_ne_zero u v hu hc)) hz

theorem raw_denominator_ne_zero (u v : F) (hu : u + 1 ≠ 0)
    (hc : v ^ 2 = u ^ 2 + 2 * u + 5) : (u + 1) ^ 2 - (v - 2) ^ 2 ≠ 0 := by
  have hr : (u + 1) ^ 2 - (v - 2) ^ 2 = 4 * (v - 2) := by
    linear_combination -hc
  rw [hr]
  exact mul_ne_zero (by norm_num) (ordinate_sub_two_ne_zero u v hu hc)

theorem parameter_inverse (u v : F) (hu : u + 1 ≠ 0)
    (hc : v ^ 2 = u ^ 2 + 2 * u + 5) :
    slope u v ^ 2 ≠ 1 ∧ conicU (slope u v) = u ∧ conicV (slope u v) = v := by
  have hr := raw_denominator_ne_zero u v hu hc
  refine ⟨slope_sq_ne_one u v hu hc, ?_, ?_⟩
  · simp only [conicU, slope]
    field_simp [hu, hr]
    linear_combination (u + 1) * hc
  · simp only [conicV, slope]
    field_simp [hu, hr]
    linear_combination (v - 2) * hc

end MazurTransfer.RationalConicFunctionParameter
#print axioms MazurTransfer.RationalConicFunctionParameter.parameter_inverse


