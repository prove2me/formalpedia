-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisSeedSeparable
-- name    : QEC_Coding_AlgebraicGeometry_Towers_GaloisSeedSeparable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:19:57.514837+00:00
-- url     : https://prove2.me/theorems/aee9b78f-fe9e-4b85-8841-250f4d8217bc
-- title:
--   Galois Seed Separable
-- statement:
--   Definitions and structural lemmas for Galois Seed Separable, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GaloisSeedSeparable.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBaseField
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin
noncomputable def galoisSeedBasePolynomial : Polynomial F256 :=
  (Polynomial.X ^ 16 + Polynomial.X) ^ 15
theorem galoisBaseZ_eq_seedPolynomial :
    galoisBaseZ = algebraMap (Polynomial F256) (RatFunc F256)
      galoisSeedBasePolynomial := by
  simp [galoisBaseZ, galoisBaseW, galoisSeedBasePolynomial,
    RatFunc.algebraMap_X]
theorem galoisBaseZ_num :
    galoisBaseZ.num = galoisSeedBasePolynomial := by
  rw [galoisBaseZ_eq_seedPolynomial, RatFunc.num_algebraMap]
theorem galoisBaseZ_denom :
    galoisBaseZ.denom = 1 := by
  rw [galoisBaseZ_eq_seedPolynomial, RatFunc.denom_algebraMap]
theorem galoisSeedBasePolynomial_derivative :
    galoisSeedBasePolynomial.derivative =
      (Polynomial.X ^ 16 + Polynomial.X) ^ 14 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  rw [galoisSeedBasePolynomial, Polynomial.derivative_pow,
    Polynomial.derivative_add, Polynomial.derivative_X_pow,
    Polynomial.derivative_X]
  reduce_mod_char!
  simp
theorem galoisBaseZ_ne_constant :
    ¬ ∃ c : F256, galoisBaseZ = RatFunc.C c := by
  rintro ⟨c, hc⟩
  apply galoisBaseZ_transcendental
  rw [hc]
  exact isAlgebraic_algebraMap c
theorem galoisBaseMinpolyX_derivative_ne_zero :
    (galoisBaseZ.minpolyX GaloisBaseField).derivative ≠ 0 := by
  rw [RatFunc.minpolyX, galoisBaseZ_num, galoisBaseZ_denom,
    Polynomial.derivative_sub, Polynomial.derivative_map,
    galoisSeedBasePolynomial_derivative]
  simp only [Polynomial.map_one, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, Polynomial.derivative_one,
    mul_zero, add_zero, sub_zero]
  apply Polynomial.map_ne_zero
  apply pow_ne_zero
  exact Polynomial.monic_X_pow_add (by norm_num) |>.ne_zero
theorem galoisBaseField_X_isSeparable :
    IsSeparable GaloisBaseField (RatFunc.X : RatFunc F256) := by
  have hirreducible :
      Irreducible (galoisBaseZ.minpolyX GaloisBaseField) :=
    galoisBaseZ.irreducible_minpolyX galoisBaseZ_ne_constant
  have hseparable :
      (galoisBaseZ.minpolyX GaloisBaseField).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero hirreducible).2
      galoisBaseMinpolyX_derivative_ne_zero
  exact hseparable.of_dvd
    (minpoly.dvd GaloisBaseField (RatFunc.X : RatFunc F256)
      galoisBaseZ.minpolyX_aeval_X)
noncomputable instance galoisBaseFieldRatFuncSeparable :
    Algebra.IsSeparable GaloisBaseField (RatFunc F256) := by
  letI : Algebra.IsSeparable GaloisBaseField
      GaloisBaseField⟮(RatFunc.X : RatFunc F256)⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := GaloisBaseField) (E := RatFunc F256)).2
      galoisBaseField_X_isSeparable
  exact AlgEquiv.Algebra.isSeparable
    (RatFunc.IntermediateField.adjoinXEquiv (F256⟮galoisBaseZ⟯))
noncomputable instance galoisBaseFieldSeedSeparable (m : ℕ) :
    Algebra.IsSeparable GaloisBaseField (Field m) :=
  Algebra.IsSeparable.trans GaloisBaseField (RatFunc F256) (Field m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


