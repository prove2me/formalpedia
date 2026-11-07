-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:38:47.52035+00:00
-- url     : https://prove2.me/theorems/7113a154-f962-4628-9e59-4dc850938606
-- title:
--   Arithmetic
-- statement:
--   Definitions and structural lemmas for Arithmetic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/Arithmetic.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def integralArithmeticToFunctionField (P : BasePrime) :
    IntegralArithmeticRing P →+* FunctionField P :=
  IsLocalization.Away.lift
    (1 + Polynomial.X : PolynomialRing P)
    (S := IntegralArithmeticRing P)
    (g := algebraMap (PolynomialRing P) (FunctionField P)) (by
      rw [isUnit_iff_ne_zero]
      apply RatFunc.algebraMap_ne_zero
      intro h
      have := congrArg (Polynomial.eval (0 : BaseField P)) h
      simp at this)
@[simp] theorem integralArithmeticToFunctionField_algebraMap
    (P : BasePrime) (f : PolynomialRing P) :
    integralArithmeticToFunctionField P
        (algebraMap (PolynomialRing P) (IntegralArithmeticRing P) f) =
      algebraMap (PolynomialRing P) (FunctionField P) f := by
  exact IsLocalization.Away.lift_eq _ _ _
noncomputable def integralArithmeticToBuildingIntegerRing (P : BasePrime) :
    IntegralArithmeticRing P →+* BuildingIntegerRing P :=
  IsLocalization.Away.lift
    (1 + Polynomial.X : PolynomialRing P)
    (S := IntegralArithmeticRing P)
    (g := Polynomial.coeToPowerSeries.ringHom) (by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp)
noncomputable def integralArithmeticY (P : BasePrime) :
    IntegralArithmeticRing P :=
  algebraMap (PolynomialRing P) (IntegralArithmeticRing P) Polynomial.X
noncomputable def integralArithmeticOnePlusYInv (P : BasePrime) :
    IntegralArithmeticRing P :=
  IsLocalization.Away.invSelf
    (1 + Polynomial.X : PolynomialRing P)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


