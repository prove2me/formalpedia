-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:02:48.900259+00:00
-- url     : https://prove2.me/theorems/5244e28e-a6ca-4976-b0a5-8d8fd4d594cd
-- title:
--   Split Evaluation
-- statement:
--   Definitions and structural lemmas for Split Evaluation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplitEvaluation.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluateRegular_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_constants
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_eq_zero_iff
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
theorem splitAbovePlace_stepEmbedding_regular
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier)
    (f : K) (hf : GlobalPlace.RegularAt Q.place f) :
    GlobalPlace.RegularAt (splitAbovePlace Q P x hx c)
      (stepFieldEmbedding P x hx f) := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  let fO : O :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  have hle := H.valuation_le_one (K := L) (algebraMap O S fO)
  change H.valuation L (stepFieldEmbedding P x hx f) ≤ 1
  exact hle
theorem splitUpperRationalPlace_evaluate_stepEmbedding
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier)
    (f : K) (hf : GlobalPlace.RegularAt Q.place f) :
    (splitUpperRationalPlace Q P x hx hregular c).evaluateRegular
        (stepFieldEmbedding P x hx f)
        (splitAbovePlace_stepEmbedding_regular Q P x hx c f hf) =
      Q.evaluateRegular f hf := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  let U := splitUpperRationalPlace Q P x hx hregular c
  let m : Ideal O := IsLocalRing.maximalIdeal O
  letI : H.asIdeal.LiesOver m := by
    change ((splitUpperPrime Q P x hx c).1).LiesOver m
    infer_instance
  let fO : O :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  let a : F256 := Q.evaluateRegular f hf
  let fU : U.place.valuationRing :=
    ⟨stepFieldEmbedding P x hx f,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr
        (splitAbovePlace_stepEmbedding_regular Q P x hx c f hf)⟩
  let aU : U.place.valuationRing :=
    GlobalPlace.constantsToValuationRing U.place a
  have hbase : fO - GlobalPlace.constantsToValuationRing Q.place a ∈
      IsLocalRing.maximalIdeal O := by
    rw [← Q.evaluate_eq_zero_iff, map_sub, Q.evaluate_constants]
    change a - a = 0
    exact sub_self a
  have hupper : algebraMap O S
      (fO - GlobalPlace.constantsToValuationRing Q.place a) ∈ H.asIdeal := by
    rw [← Ideal.mem_under]
    rw [← (inferInstance : H.asIdeal.LiesOver m).over]
    exact hbase
  have hlt : H.valuation L
      (algebraMap S L
        (algebraMap O S
          (fO - GlobalPlace.constantsToValuationRing Q.place a))) < 1 :=
    (H.valuation_lt_one_iff_mem (K := L) _).2 hupper
  change U.constantsEquiv.symm (U.place.residue fU) = a
  apply U.constantsEquiv.injective
  rw [U.constantsEquiv.apply_symm_apply, U.constantsEquiv_apply]
  change U.place.residue fU = U.place.residue aU
  rw [← sub_eq_zero, ← map_sub, GlobalPlace.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  change H.valuation L
    (stepFieldEmbedding P x hx f - algebraMap F256 L a) < 1
  simp only [map_sub, IsScalarTower.algebraMap_apply] at hlt ⊢
  exact hlt
theorem splitAbovePlace_auxiliaryCoordinate_regular
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    GlobalPlace.RegularAt (splitAbovePlace Q P x hx c)
      (stepAuxiliaryCoordinate P x hx) := by
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  have hle := H.valuation_le_one (K := L)
    (splitIntegralAuxiliaryCoordinate Q P x hx hregular)
  change H.valuation L (stepAuxiliaryCoordinate P x hx) ≤ 1
  exact hle
theorem splitAbovePlace_embeddedCoordinate_valuation_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hvalue : Q.evaluateRegular x hregular ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    (splitAbovePlace Q P x hx c).valuation
        (stepFieldEmbedding P x hx x) = 1 := by
  let U := splitUpperRationalPlace Q P x hx hregular c
  have hxregular := splitAbovePlace_stepEmbedding_regular
    Q P x hx c x hregular
  have hxevaluate := splitUpperRationalPlace_evaluate_stepEmbedding
    Q P x hx hregular c x hregular
  have hxevaluate_ne : U.evaluateRegular
      (stepFieldEmbedding P x hx x) hxregular ≠ 0 := by
    rw [hxevaluate]
    exact hvalue
  have hxnotlt : ¬U.place.valuation (stepFieldEmbedding P x hx x) < 1 := by
    intro hxlt
    apply hxevaluate_ne
    erw [U.evaluateRegular_eq_zero_iff]
    rw [Valuation.mem_maximalIdeal_iff]
    exact hxlt
  exact le_antisymm hxregular (not_lt.mp hxnotlt)
theorem splitAbovePlace_stepDistinguishedCoordinate_regular
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hvalue : Q.evaluateRegular x hregular ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    GlobalPlace.RegularAt (splitAbovePlace Q P x hx c)
      (stepDistinguishedCoordinate P x hx) := by
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  have hz := splitAbovePlace_auxiliaryCoordinate_regular
    Q P x hx hregular c
  have hxval := splitAbovePlace_embeddedCoordinate_valuation_eq_one
    Q P x hx hregular hvalue c
  have hxval' : H.valuation L (stepFieldEmbedding P x hx x) = 1 := hxval
  have hz' : H.valuation L (stepAuxiliaryCoordinate P x hx) ≤ 1 := hz
  change H.valuation L
    (stepAuxiliaryCoordinate P x hx /
      stepFieldEmbedding P x hx x) ≤ 1
  rw [div_eq_mul_inv, (H.valuation L).map_mul, (H.valuation L).map_inv,
    hxval',
    inv_one, mul_one]
  exact hz'
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


