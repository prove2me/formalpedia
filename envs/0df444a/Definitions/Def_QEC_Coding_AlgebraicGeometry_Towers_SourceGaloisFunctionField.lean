-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:23:09.734068+00:00
-- url     : https://prove2.me/theorems/fe22d5c1-2503-45ba-9a12-b822015b774c
-- title:
--   Source Galois Function Field
-- statement:
--   Definitions and structural lemmas for Source Galois Function Field, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisFunctionField.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
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
noncomputable def sourceGaloisClosureConstantMap (m : ℕ) :
    F256 →+* SourceGaloisClosureField m :=
  (algebraMap GaloisBaseField (SourceGaloisClosureField m)).comp
    (algebraMap F256 GaloisBaseField)
noncomputable instance sourceGaloisClosureConstantAlgebra (m : ℕ) :
    Algebra F256 (SourceGaloisClosureField m) :=
  (sourceGaloisClosureConstantMap m).toAlgebra
noncomputable instance (priority := 2000) sourceGaloisClosureConstantSMul
    (m : ℕ) : SMul F256 (SourceGaloisClosureField m) :=
  (sourceGaloisClosureConstantAlgebra m).toSMul
noncomputable instance (priority := 2000) sourceGaloisClosureConstantModule
    (m : ℕ) : Module F256 (SourceGaloisClosureField m) :=
  @Algebra.toModule F256 (SourceGaloisClosureField m) _ _
    (sourceGaloisClosureConstantAlgebra m)
noncomputable instance sourceGaloisClosureConstantBaseScalarTower (m : ℕ) :
    IsScalarTower F256 GaloisBaseField (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable def sourceGaloisClosureRatFuncEmbedding (m : ℕ) :
    RatFunc F256 →ₐ[F256] SourceGaloisClosureField m :=
  (IsScalarTower.toAlgHom F256 GaloisBaseField
    (SourceGaloisClosureField m)).comp
      galoisBaseFieldEquivRatFunc.toAlgHom
noncomputable instance sourceGaloisClosureRatFuncAlgebra (m : ℕ) :
    Algebra (RatFunc F256) (SourceGaloisClosureField m) :=
  (sourceGaloisClosureRatFuncEmbedding m).toRingHom.toAlgebra
noncomputable instance (priority := 2000) sourceGaloisClosureRatFuncSMul
    (m : ℕ) : SMul (RatFunc F256) (SourceGaloisClosureField m) :=
  (sourceGaloisClosureRatFuncAlgebra m).toSMul
noncomputable instance (priority := 2000) sourceGaloisClosureRatFuncModule
    (m : ℕ) : Module (RatFunc F256) (SourceGaloisClosureField m) :=
  @Algebra.toModule (RatFunc F256) (SourceGaloisClosureField m) _ _
    (sourceGaloisClosureRatFuncAlgebra m)
noncomputable instance sourceGaloisClosureRatFuncScalarTower (m : ℕ) :
    IsScalarTower F256 (RatFunc F256) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq'
    (sourceGaloisClosureRatFuncEmbedding m).comp_algebraMap.symm
theorem sourceGaloisClosureBaseRatFunc_compatibility (m : ℕ) :
    (algebraMap (RatFunc F256) (SourceGaloisClosureField m)).comp
        galoisBaseFieldEquivRatFunc.symm.toRingEquiv.toRingHom =
      algebraMap GaloisBaseField (SourceGaloisClosureField m) := by
  ext x
  simp [sourceGaloisClosureRatFuncEmbedding,
    RingHom.algebraMap_toAlgebra]
noncomputable instance sourceGaloisClosureFunctionField (m : ℕ) :
    FunctionField F256 (SourceGaloisClosureField m) := by
  exact @Module.Finite.of_equiv_equiv
    GaloisBaseField (SourceGaloisClosureField m)
    (RatFunc F256) (SourceGaloisClosureField m)
    _ _ _ _ (sourceGaloisClosureFieldAlgebra m)
    (sourceGaloisClosureRatFuncAlgebra m)
    galoisBaseFieldEquivRatFunc.symm.toRingEquiv
    (RingEquiv.refl (SourceGaloisClosureField m))
    (sourceGaloisClosureBaseRatFunc_compatibility m)
    (sourceGaloisClosureFieldFiniteDimensional m)
noncomputable instance sourceGaloisClosureRatFuncIsGalois (m : ℕ) :
    IsGalois (RatFunc F256) (SourceGaloisClosureField m) := by
  exact IsGalois.of_equiv_equiv
    (F := GaloisBaseField) («E» := SourceGaloisClosureField m)
    (f := galoisBaseFieldEquivRatFunc.symm.toRingEquiv)
    (g := RingEquiv.refl (SourceGaloisClosureField m))
    (sourceGaloisClosureBaseRatFunc_compatibility m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


