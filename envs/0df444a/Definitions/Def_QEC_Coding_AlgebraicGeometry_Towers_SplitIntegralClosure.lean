-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:57:15.399439+00:00
-- url     : https://prove2.me/theorems/88dd39af-21ed-4696-b110-d4e6fa0b7576
-- title:
--   Split Integral Closure
-- statement:
--   Definitions and structural lemmas for Split Integral Closure, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplitIntegralClosure.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ResidualPolynomial
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryCoordinate_artinSchreier
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
abbrev SplitIntegralClosure
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :=
  integralClosure Q.place.valuationRing (StepField P x hx)
instance splitFieldValuationRingScalarTower
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsScalarTower Q.place.valuationRing K (StepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable instance splitIntegralClosureIsTorsionFree
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Module.IsTorsionFree Q.place.valuationRing
      (SplitIntegralClosure Q P x hx) := by
  letI : Module.IsTorsionFree Q.place.valuationRing (StepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      Q.place.valuationRing K (StepField P x hx)
  exact IsIntegralClosure.isTorsionFree
    Q.place.valuationRing (StepField P x hx)
noncomputable instance splitIntegralClosureFinite
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Module.Finite Q.place.valuationRing
      (SplitIntegralClosure Q P x hx) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite Q.place.valuationRing K
    (StepField P x hx) (SplitIntegralClosure Q P x hx)
noncomputable instance splitIntegralClosureIsFractionRing
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsFractionRing (SplitIntegralClosure Q P x hx) (StepField P x hx) :=
  integralClosure.isFractionRing_of_finite_extension K (StepField P x hx)
noncomputable instance splitIntegralClosureIsDedekindDomain
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsDedekindDomain (SplitIntegralClosure Q P x hx) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain Q.place.valuationRing K
    (StepField P x hx)
noncomputable def splitBaseCoordinate
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Q.place.valuationRing :=
  ⟨x, (GlobalPlace.mem_valuationRing_iff Q.place x).mpr hregular⟩
theorem algebraMap_splitBaseCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    algebraMap Q.place.valuationRing (StepField P x hx)
        (splitBaseCoordinate Q x hregular) =
      stepFieldEmbedding P x hx x :=
  rfl
noncomputable def splitAuxiliaryIntegralPolynomial
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Q.place.valuationRing[X] :=
  X ^ 16 + (X - C ((splitBaseCoordinate Q x hregular) ^ 17))
theorem splitAuxiliaryIntegralPolynomial_monic
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (splitAuxiliaryIntegralPolynomial Q x hregular).Monic := by
  rw [splitAuxiliaryIntegralPolynomial]
  apply Monic.add_of_left (monic_X_pow 16)
  calc
    ((X : Q.place.valuationRing[X]) -
        C ((splitBaseCoordinate Q x hregular) ^ 17)).degree ≤
        max (X : Q.place.valuationRing[X]).degree
          (C ((splitBaseCoordinate Q x hregular) ^ 17)).degree :=
      degree_sub_le _ _
    _ ≤ (1 : WithBot ℕ) :=
      max_le (by simp) (degree_C_le.trans (by norm_num))
    _ < ((X : Q.place.valuationRing[X]) ^ 16).degree := by
      rw [degree_X_pow]
      norm_num
noncomputable def splitIntegralAuxiliaryCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    SplitIntegralClosure Q P x hx := by
  refine ⟨stepAuxiliaryCoordinate P x hx, ?_⟩
  refine ⟨splitAuxiliaryIntegralPolynomial Q x hregular,
    splitAuxiliaryIntegralPolynomial_monic Q x hregular, ?_⟩
  rw [splitAuxiliaryIntegralPolynomial]
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_sub, eval₂_C]
  change stepAuxiliaryCoordinate P x hx ^ 16 +
      (stepAuxiliaryCoordinate P x hx -
        algebraMap Q.place.valuationRing (StepField P x hx)
          ((splitBaseCoordinate Q x hregular) ^ 17)) = 0
  rw [map_pow, algebraMap_splitBaseCoordinate]
  linear_combination stepAuxiliaryCoordinate_artinSchreier P x hx
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


