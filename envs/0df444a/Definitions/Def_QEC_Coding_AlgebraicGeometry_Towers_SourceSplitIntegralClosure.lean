-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitIntegralClosure
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceSplitIntegralClosure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:58:25.692176+00:00
-- url     : https://prove2.me/theorems/e77869da-37d0-4d24-b553-4e0e6db8c360
-- title:
--   Source Split Integral Closure
-- statement:
--   Definitions and structural lemmas for Source Split Integral Closure, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitIntegralClosure.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepCoordinate_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_eq_zero_iff
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
abbrev SourceSplitIntegralClosure
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :=
  integralClosure Q.place.valuationRing (SourceStepField P x hx)
instance sourceSplitFieldValuationRingScalarTower
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsScalarTower Q.place.valuationRing K (SourceStepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable instance sourceSplitIntegralClosureIsTorsionFree
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Module.IsTorsionFree Q.place.valuationRing
      (SourceSplitIntegralClosure Q P x hx) := by
  letI : Module.IsTorsionFree Q.place.valuationRing
      (SourceStepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      Q.place.valuationRing K (SourceStepField P x hx)
  exact IsIntegralClosure.isTorsionFree
    Q.place.valuationRing (SourceStepField P x hx)
noncomputable instance sourceSplitIntegralClosureFinite
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Module.Finite Q.place.valuationRing
      (SourceSplitIntegralClosure Q P x hx) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite Q.place.valuationRing K
    (SourceStepField P x hx) (SourceSplitIntegralClosure Q P x hx)
noncomputable instance sourceSplitIntegralClosureIsFractionRing
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsFractionRing (SourceSplitIntegralClosure Q P x hx)
      (SourceStepField P x hx) :=
  integralClosure.isFractionRing_of_finite_extension K (SourceStepField P x hx)
noncomputable instance sourceSplitIntegralClosureIsDedekindDomain
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsDedekindDomain (SourceSplitIntegralClosure Q P x hx) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain Q.place.valuationRing K
    (SourceStepField P x hx)
noncomputable def sourceSplitBaseCoordinate
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Q.place.valuationRing :=
  ⟨x, (GlobalPlace.mem_valuationRing_iff Q.place x).mpr hregular⟩
noncomputable def sourceSplitBaseDenominator
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Q.place.valuationRing :=
  sourceSplitBaseCoordinate Q x hregular ^ 15 + 1
theorem sourceSplitBaseDenominator_evaluate
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Q.evaluate (sourceSplitBaseDenominator Q x hregular) =
      Q.evaluateRegular x hregular ^ 15 + 1 := by
  simp only [sourceSplitBaseDenominator, map_add, map_pow, map_one]
  rfl
theorem sourceSplitBaseDenominator_evaluate_ne_zero
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Q.evaluate (sourceSplitBaseDenominator Q x hregular) ≠ 0 := by
  rw [sourceSplitBaseDenominator_evaluate]
  intro hzero
  apply hsplit
  rw [galoisBaseWValue_eq]
  calc
    Q.evaluateRegular x hregular ^ 16 + Q.evaluateRegular x hregular =
        Q.evaluateRegular x hregular *
          (Q.evaluateRegular x hregular ^ 15 + 1) := by ring
    _ = 0 := by rw [hzero, mul_zero]
theorem sourceSplitBaseDenominator_inv_mem
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    ((sourceSplitBaseDenominator Q x hregular : K)⁻¹) ∈
      Q.place.valuationRing := by
  let d := sourceSplitBaseDenominator Q x hregular
  have hunit : IsUnit d := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmaximal
    exact sourceSplitBaseDenominator_evaluate_ne_zero Q x hregular hsplit
      ((Q.evaluate_eq_zero_iff d).2 hmaximal)
  change ((d : K)⁻¹) ∈ Q.place.valuationRing
  rw [← hunit.unit_spec]
  change (Q.place.valuationRing.subtype
    (↑hunit.unit : Q.place.valuationRing))⁻¹ ∈ Q.place.valuationRing
  rw [← map_units_inv Q.place.valuationRing.subtype hunit.unit]
  exact (↑(hunit.unit⁻¹) : Q.place.valuationRing).property
theorem sourceStepRhs_regularAt_of_splitValue
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    GlobalPlace.RegularAt Q.place (sourceStepRhs x) := by
  rw [GlobalPlace.regularAt_iff_mem_valuationRing, sourceStepRhs,
    div_eq_mul_inv]
  let xO := sourceSplitBaseCoordinate Q x hregular
  have hxpow : x ^ 16 ∈ Q.place.valuationRing := by
    exact (xO ^ 16).property
  exact Q.place.valuationRing.mul_mem _ _ hxpow
    (sourceSplitBaseDenominator_inv_mem Q x hregular hsplit)
noncomputable def sourceSplitBaseRhs
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Q.place.valuationRing :=
  ⟨sourceStepRhs x,
    (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
      (sourceStepRhs_regularAt_of_splitValue Q x hregular hsplit)⟩
noncomputable def sourceSplitIntegralPolynomial
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Q.place.valuationRing[X] :=
  X ^ 16 + (X - C (sourceSplitBaseRhs Q x hregular hsplit))
theorem sourceSplitIntegralPolynomial_monic
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    (sourceSplitIntegralPolynomial Q x hregular hsplit).Monic := by
  rw [sourceSplitIntegralPolynomial]
  apply Monic.add_of_left (monic_X_pow 16)
  calc
    ((X : Q.place.valuationRing[X]) -
        C (sourceSplitBaseRhs Q x hregular hsplit)).degree ≤
        max (X : Q.place.valuationRing[X]).degree
          (C (sourceSplitBaseRhs Q x hregular hsplit)).degree :=
      degree_sub_le _ _
    _ ≤ (1 : WithBot ℕ) :=
      max_le (by simp) (degree_C_le.trans (by norm_num))
    _ < ((X : Q.place.valuationRing[X]) ^ 16).degree := by
      rw [degree_X_pow]
      norm_num
noncomputable def sourceSplitIntegralCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    SourceSplitIntegralClosure Q P x hx := by
  refine ⟨sourceStepCoordinate P x hx, ?_⟩
  refine ⟨sourceSplitIntegralPolynomial Q x hregular hsplit,
    sourceSplitIntegralPolynomial_monic Q x hregular hsplit, ?_⟩
  rw [sourceSplitIntegralPolynomial]
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_sub, eval₂_C]
  change sourceStepCoordinate P x hx ^ 16 +
      (sourceStepCoordinate P x hx -
        sourceStepEmbedding P x hx (sourceStepRhs x)) = 0
  linear_combination sourceStepCoordinate_equation P x hx
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


