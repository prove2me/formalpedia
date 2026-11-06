-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBaseField
-- name    : QEC_Coding_AlgebraicGeometry_Towers_GaloisBaseField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:18:41.781496+00:00
-- url     : https://prove2.me/theorems/5d567372-8900-4c5c-98bc-9f02a72324c9
-- title:
--   Galois Base Field
-- statement:
--   Definitions and structural lemmas for Galois Base Field, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GaloisBaseField.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BaseParameter
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Mathlib.FieldTheory.RatFunc.Luroth
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
noncomputable def galoisBasePolynomial : Polynomial F256 :=
  (Polynomial.X ^ 16 + Polynomial.X) ^ 15
theorem galoisBaseW_eq_algebraMap :
    galoisBaseW = algebraMap (Polynomial F256) (RatFunc F256)
      (Polynomial.X ^ 16 + Polynomial.X) := by
  simp [galoisBaseW, RatFunc.algebraMap_X]
theorem galoisBaseZ_transcendental : Transcendental F256 galoisBaseZ := by
  have hdegree :
      (Polynomial.X ^ 16 + Polynomial.X : Polynomial F256).natDegree = 16 := by
    calc
      (Polynomial.X ^ 16 + Polynomial.X : Polynomial F256).natDegree =
          (Polynomial.X ^ 16 : Polynomial F256).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt (by norm_num)
      _ = 16 := by norm_num
  have hmonic :
      (Polynomial.X ^ 16 + Polynomial.X : Polynomial F256).Monic :=
    Polynomial.monic_X_pow_add (by norm_num)
  have hw : Transcendental F256 galoisBaseW := by
    rw [galoisBaseW_eq_algebraMap]
    simpa only [RatFunc.aeval_X_left_eq_algebraMap] using
      RatFunc.transcendental_X.aeval
        (Polynomial.X ^ 16 + Polynomial.X : Polynomial F256)
        (by simp [hdegree])
        (by simp [hmonic.leadingCoeff])
  rw [galoisBaseZ]
  exact hw.pow (by norm_num)
abbrev GaloisBaseField : Type := F256⟮galoisBaseZ⟯
noncomputable def galoisBaseFieldEquivRatFunc :
    RatFunc F256 ≃ₐ[F256] GaloisBaseField :=
  RatFunc.algEquivOfTranscendental galoisBaseZ galoisBaseZ_transcendental
noncomputable instance galoisBaseFieldRatFuncFiniteDimensional :
    FiniteDimensional GaloisBaseField (RatFunc F256) :=
  FunctionField.finiteDimensional_of_adjoin_transcendental
    galoisBaseZ_transcendental
noncomputable def galoisBaseFieldSeedEmbedding (m : ℕ) :
    GaloisBaseField →ₐ[F256] Field m :=
  (IsScalarTower.toAlgHom F256 (RatFunc F256) (Field m)).comp
    (F256⟮galoisBaseZ⟯).val
noncomputable instance galoisBaseFieldSeedFiniteDimensional (m : ℕ) :
    FiniteDimensional GaloisBaseField (Field m) :=
  FiniteDimensional.trans GaloisBaseField (RatFunc F256) (Field m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


