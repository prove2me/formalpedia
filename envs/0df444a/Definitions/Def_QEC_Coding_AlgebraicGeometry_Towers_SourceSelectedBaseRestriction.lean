-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:23:25.513581+00:00
-- url     : https://prove2.me/theorems/73d12cbe-74b1-4d5d-983f-a5ff3baebe77
-- title:
--   Source Selected Base Restriction
-- statement:
--   Definitions and structural lemmas for Source Selected Base Restriction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedBaseRestriction.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaceOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisBaseParameter_sub_one_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRationalPlace_order_galoisBaseParameter_sub_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
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
open Polynomial
open scoped RatFunc WithZero
open MonoidWithZeroHom
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
noncomputable def sourceSelectedRatFuncEmbedding (m : ℕ) :
    RatFunc F256 →ₐ[F256] SourceField m :=
  (sourceGaloisBaseFieldEmbedding m).comp
    galoisBaseFieldEquivRatFunc.toAlgHom
theorem sourceSelectedRatFuncEmbedding_X (m : ℕ) :
    sourceSelectedRatFuncEmbedding m RatFunc.X =
      sourceGaloisBaseParameter m := by
  simp [sourceSelectedRatFuncEmbedding, sourceGaloisBaseFieldEmbedding,
    galoisBaseFieldEquivRatFunc, sourceGaloisBaseParameter]
noncomputable def sourceSelectedRestrictedBaseValuation
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    Valuation (RatFunc F256) ℤᵐ⁰ :=
  (sourceSelectedRationalPlace m index).place.valuation.comap
    (sourceSelectedRatFuncEmbedding m).toRingHom
theorem sourceSelectedRestrictedBaseValuation_X_sub_one
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSelectedRestrictedBaseValuation m index (RatFunc.X - 1) =
      WithZero.exp (-1 : ℤ) := by
  let Q := (sourceSelectedRationalPlace m index).place
  have horder :=
    sourceSelectedRationalPlace_order_galoisBaseParameter_sub_one m index
  have hmap :
      sourceSelectedRatFuncEmbedding m (RatFunc.X - 1) =
        sourceGaloisBaseParameter m - 1 := by
    rw [map_sub, map_one, sourceSelectedRatFuncEmbedding_X]
  have hne : Q.valuation (sourceGaloisBaseParameter m - 1) ≠ 0 :=
    Q.valuation.ne_zero_iff.mpr
      (sourceGaloisBaseParameter_sub_one_ne_zero m)
  have hlog :
      WithZero.log (Q.valuation (sourceGaloisBaseParameter m - 1)) = -1 := by
    unfold GlobalPlace.order at horder
    linarith
  change Q.valuation
      (sourceSelectedRatFuncEmbedding m (RatFunc.X - 1)) = _
  rw [hmap, ← WithZero.exp_log hne, hlog]
theorem sourceSelectedRestrictedBaseValuation_surjective
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    Function.Surjective (sourceSelectedRestrictedBaseValuation m index) := by
  intro γ
  by_cases hγ : γ = 0
  · subst γ
    exact ⟨0, map_zero _⟩
  · refine ⟨(RatFunc.X - 1) ^ (-WithZero.log γ), ?_⟩
    rw [map_zpow₀,
      sourceSelectedRestrictedBaseValuation_X_sub_one,
      ← WithZero.exp_zsmul]
    simp only [smul_eq_mul]
    rw [neg_mul_neg, mul_one, WithZero.exp_log hγ]
noncomputable def sourceSelectedRestrictedBasePlace
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    GlobalPlace F256 (RatFunc F256) where
  valuation := sourceSelectedRestrictedBaseValuation m index
  normalized := sourceSelectedRestrictedBaseValuation_surjective m index
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


