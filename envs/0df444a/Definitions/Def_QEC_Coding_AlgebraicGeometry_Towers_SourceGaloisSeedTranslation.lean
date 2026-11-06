-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSeedTranslation
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSeedTranslation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:10:48.178104+00:00
-- url     : https://prove2.me/theorems/5ee8e840-02a2-45a4-8202-d354dc09bc96
-- title:
--   Source Galois Seed Translation
-- statement:
--   Definitions and structural lemmas for Source Galois Seed Translation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSeedTranslation.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceGaloisWFieldGenerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivRatFunc_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepReciprocalRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceGaloisWFieldGenerator
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldEquivRatFunc_X
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepDistinguishedCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepReciprocalRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
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
local instance sourceGaloisSeedTranslation_f256CharTwo : CharP F256 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
attribute [local instance] sourceGaloisSeedTranslation_f256CharTwo
local instance sourceGaloisSeedTranslation_ratFuncCharTwo : CharP (RatFunc F256) 2 :=
  charP_of_injective_algebraMap
    (algebraMap F256 (RatFunc F256)).injective 2
attribute [local instance] sourceGaloisSeedTranslation_ratFuncCharTwo
theorem sourceGaloisSeedTranslation_ratFunc_X_add_one_transcendental :
    Transcendental F256 ((RatFunc.X : RatFunc F256) + 1) := by
  have hmonic :
      (Polynomial.X + 1 : Polynomial F256).Monic := by
    simpa only [← Polynomial.C_1] using
      Polynomial.monic_X_add_C (1 : F256)
  have htrans := RatFunc.transcendental_X.aeval
    (Polynomial.X + 1 : Polynomial F256)
    (by rw [← Polynomial.C_1, Polynomial.natDegree_X_add_C]; norm_num)
    (by simp [hmonic.leadingCoeff])
  convert htrans using 1
  simp [RatFunc.aeval_X_left_eq_algebraMap, RatFunc.algebraMap_X]
noncomputable def sourceGaloisSeedTranslation_sourceSeedOneTranslationPolynomialHom :
    Polynomial F256 →ₐ[F256] RatFunc F256 :=
  Polynomial.aeval (RatFunc.X + 1)
theorem sourceGaloisSeedTranslation_sourceSeedOneTranslationPolynomialHom_injective :
    Function.Injective sourceGaloisSeedTranslation_sourceSeedOneTranslationPolynomialHom := by
  exact transcendental_iff_injective.mp sourceGaloisSeedTranslation_ratFunc_X_add_one_transcendental
theorem sourceGaloisSeedTranslation_sourceSeedOneTranslationPolynomialHom_nonZeroDivisors :
    nonZeroDivisors (Polynomial F256) ≤
      (nonZeroDivisors (RatFunc F256)).comap
        sourceGaloisSeedTranslation_sourceSeedOneTranslationPolynomialHom :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    sourceGaloisSeedTranslation_sourceSeedOneTranslationPolynomialHom_injective
noncomputable def sourceGaloisSeedTranslation_sourceSeedOneTranslationHom :
    RatFunc F256 →ₐ[F256] RatFunc F256 :=
  RatFunc.liftAlgHom sourceGaloisSeedTranslation_sourceSeedOneTranslationPolynomialHom
    sourceGaloisSeedTranslation_sourceSeedOneTranslationPolynomialHom_nonZeroDivisors
theorem sourceGaloisSeedTranslation_sourceSeedOneTranslationHom_apply_algebraMap
    (p : Polynomial F256) :
    sourceGaloisSeedTranslation_sourceSeedOneTranslationHom
        (algebraMap (Polynomial F256) (RatFunc F256) p) =
      Polynomial.aeval (RatFunc.X + 1) p := by
  exact RatFunc.liftRingHom_algebraMap
    sourceGaloisSeedTranslation_sourceSeedOneTranslationPolynomialHom.toRingHom
    sourceGaloisSeedTranslation_sourceSeedOneTranslationPolynomialHom_nonZeroDivisors p
theorem sourceGaloisSeedTranslation_sourceSeedOneTranslationHom_apply_X :
    sourceGaloisSeedTranslation_sourceSeedOneTranslationHom RatFunc.X = RatFunc.X + 1 := by
  change sourceGaloisSeedTranslation_sourceSeedOneTranslationHom
      (algebraMap (Polynomial F256) (RatFunc F256) Polynomial.X) = _
  rw [sourceGaloisSeedTranslation_sourceSeedOneTranslationHom_apply_algebraMap]
  simp only [aeval_X]
theorem sourceGaloisSeedTranslation_sourceSeedOneTranslationHom_comp_self :
    sourceGaloisSeedTranslation_sourceSeedOneTranslationHom.comp sourceGaloisSeedTranslation_sourceSeedOneTranslationHom =
      AlgHom.id F256 (RatFunc F256) := by
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := Polynomial F256)
  intro p
  change sourceGaloisSeedTranslation_sourceSeedOneTranslationHom
      (sourceGaloisSeedTranslation_sourceSeedOneTranslationHom
        (algebraMap (Polynomial F256) (RatFunc F256) p)) =
    algebraMap (Polynomial F256) (RatFunc F256) p
  calc
    sourceGaloisSeedTranslation_sourceSeedOneTranslationHom
        (sourceGaloisSeedTranslation_sourceSeedOneTranslationHom
          (algebraMap (Polynomial F256) (RatFunc F256) p)) =
        sourceGaloisSeedTranslation_sourceSeedOneTranslationHom
          (Polynomial.aeval (RatFunc.X + 1) p) := by
            rw [sourceGaloisSeedTranslation_sourceSeedOneTranslationHom_apply_algebraMap]
    _ = Polynomial.aeval
          (sourceGaloisSeedTranslation_sourceSeedOneTranslationHom (RatFunc.X + 1)) p := by
            rw [Polynomial.aeval_algHom_apply]
    _ = Polynomial.aeval RatFunc.X p := by
      rw [map_add, sourceGaloisSeedTranslation_sourceSeedOneTranslationHom_apply_X, map_one,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = algebraMap (Polynomial F256) (RatFunc F256) p :=
      RatFunc.aeval_X_left_eq_algebraMap p
noncomputable def sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256 :
    RatFunc F256 ≃ₐ[F256] RatFunc F256 :=
  AlgEquiv.ofAlgHom sourceGaloisSeedTranslation_sourceSeedOneTranslationHom sourceGaloisSeedTranslation_sourceSeedOneTranslationHom
    sourceGaloisSeedTranslation_sourceSeedOneTranslationHom_comp_self
    sourceGaloisSeedTranslation_sourceSeedOneTranslationHom_comp_self
theorem sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256_apply_X :
    sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256 RatFunc.X = RatFunc.X + 1 :=
  sourceGaloisSeedTranslation_sourceSeedOneTranslationHom_apply_X
theorem sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256_apply_galoisBaseW :
    sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256 galoisBaseW = galoisBaseW := by
  letI : CharP (RatFunc F256) 2 := inferInstance
  rw [galoisBaseW, map_add, map_pow,
    sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256_apply_X]
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, add_pow_char_pow]
  have hones : (1 : RatFunc F256) + 1 = 0 :=
    CharTwo.add_self_eq_zero 1
  linear_combination hones
theorem sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256_apply_galoisBaseZ :
    sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256 galoisBaseZ = galoisBaseZ := by
  rw [galoisBaseZ, map_pow,
    sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256_apply_galoisBaseW]
theorem sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256_fixes_galoisBase :
    sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256.toAlgHom.comp
        (IntermediateField.adjoin F256
          ({galoisBaseZ} : Set (RatFunc F256))).val =
      (IntermediateField.adjoin F256
        ({galoisBaseZ} : Set (RatFunc F256))).val := by
  apply IntermediateField.adjoin_algHom_ext
  intro x hx
  have hx' : x = galoisBaseZ := Set.mem_singleton_iff.mp hx
  subst x
  exact sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256_apply_galoisBaseZ
noncomputable def sourceSeedOneTranslation :
    RatFunc F256 ≃ₐ[GaloisBaseField] RatFunc F256 where
  __ := sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256.toRingEquiv
  commutes' a := by
    exact DFunLike.congr_fun
      sourceGaloisSeedTranslation_sourceSeedOneTranslationOverF256_fixes_galoisBase a
noncomputable def sourceGaloisSeedOneTranslation (m : ℕ) :
    SourceGaloisClosureField m ≃ₐ[GaloisBaseField]
      SourceGaloisClosureField m := by
  let seedAlgebra : Algebra (RatFunc F256) (SourceGaloisClosureField m) :=
    (sourceGaloisSeedRatFuncToClosure m).toRingHom.toAlgebra
  letI seedSMul : SMul (RatFunc F256) (SourceGaloisClosureField m) :=
    seedAlgebra.toSMul
  letI seedAlgebraInstance : Algebra (RatFunc F256)
      (SourceGaloisClosureField m) := seedAlgebra
  letI seedModule : Module (RatFunc F256) (SourceGaloisClosureField m) :=
    @Algebra.toModule (RatFunc F256) (SourceGaloisClosureField m) _ _
      seedAlgebraInstance
  letI seedTower : IsScalarTower GaloisBaseField (RatFunc F256)
      (SourceGaloisClosureField m) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro a
      change algebraMap GaloisBaseField (SourceGaloisClosureField m) a =
        sourceGaloisSeedRatFuncToClosure m
          (algebraMap GaloisBaseField (RatFunc F256) a)
      exact (sourceGaloisSeedRatFuncToClosure m).commutes a |>.symm)
  exact sourceSeedOneTranslation.liftNormal (SourceGaloisClosureField m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


