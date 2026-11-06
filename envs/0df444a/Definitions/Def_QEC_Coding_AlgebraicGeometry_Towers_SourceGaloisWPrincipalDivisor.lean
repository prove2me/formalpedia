-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:13:05.565212+00:00
-- url     : https://prove2.me/theorems/afe1ca75-8a01-4d36-940c-788e0ca44984
-- title:
--   Source Galois WPrincipal Divisor
-- statement:
--   Definitions and structural lemmas for Source Galois WPrincipal Divisor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPrincipalDivisor.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibreDivisors
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityFibreDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPlaceOfPrime_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPrime_nonempty
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityRamificationIndex_pos
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroFibreDivisor_apply
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_apply
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityFibreDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroFibreDivisor_apply
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_apply
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
open IntermediateField
open scoped Polynomial RatFunc
noncomputable section
abbrev sourceGaloisWPrincipalDivisor_E (m : ℕ) := SourceGaloisClosureField m
abbrev sourceGaloisWPrincipalDivisor_ClosurePlace (m : ℕ) :=
  @GlobalPlace F256 (sourceGaloisWPrincipalDivisor_E m) _ _ _ (sourceGaloisClosureConstantAlgebra m)
noncomputable local instance sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra (m : ℕ) :
    Algebra (Polynomial F256) (sourceGaloisWPrincipalDivisor_E m) :=
  ((algebraMap (RatFunc F256) (sourceGaloisWPrincipalDivisor_E m)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
attribute [local instance] sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra
noncomputable local instance sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower
    (m : ℕ) : IsScalarTower (Polynomial F256) (RatFunc F256) (sourceGaloisWPrincipalDivisor_E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower
noncomputable local instance sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (sourceGaloisWPrincipalDivisor_E m) :=
  IsGalois.to_isSeparable
attribute [local instance] sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable
abbrev sourceGaloisWPrincipalDivisor_DirectClosurePlace (m : ℕ) :=
  @GlobalPlace F256 (sourceGaloisWPrincipalDivisor_E m) _ _ _
    (@AffinePlace.constantAlgebra F256 (sourceGaloisWPrincipalDivisor_E m) _ _
      (sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra m))
abbrev sourceGaloisWPrincipalDivisor_directClosureOrder (m : ℕ)
    (P : sourceGaloisWPrincipalDivisor_DirectClosurePlace m) (x : sourceGaloisWPrincipalDivisor_E m) : ℤ :=
  @GlobalPlace.order F256 (sourceGaloisWPrincipalDivisor_E m) _ _ _
    (@AffinePlace.constantAlgebra F256 (sourceGaloisWPrincipalDivisor_E m) _ _
      (sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra m)) P x
abbrev sourceGaloisWPrincipalDivisor_closureOrder (m : ℕ)
    (P : sourceGaloisWPrincipalDivisor_ClosurePlace m) (x : sourceGaloisWPrincipalDivisor_E m) : ℤ :=
  @GlobalPlace.order F256 (sourceGaloisWPrincipalDivisor_E m) _ _ _ (sourceGaloisClosureConstantAlgebra m) P x
noncomputable abbrev sourceGaloisWPrincipalDivisor_directClosureResidueDegree (m : ℕ) :
    sourceGaloisWPrincipalDivisor_DirectClosurePlace m → ℕ :=
  fun P => GlobalPlace.residueDegree
    (π := sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra m)
    (ρ := sourceGaloisClosureRatFuncAlgebra m)
    (τ := sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower m)
    (φ := sourceGaloisClosureFunctionField m)
    (σ := sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable m)
    (κ := @AffinePlace.constantAlgebra F256 (sourceGaloisWPrincipalDivisor_E m) _ _
      (sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra m)) P
noncomputable abbrev sourceGaloisWPrincipalDivisor_closureResidueDegree (m : ℕ) :
    sourceGaloisWPrincipalDivisor_ClosurePlace m → ℕ :=
  fun P => GlobalPlace.residueDegree
    (π := sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra m)
    (ρ := sourceGaloisClosureRatFuncAlgebra m)
    (τ := sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower m)
    (φ := sourceGaloisClosureFunctionField m)
    (σ := sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable m)
    (κ := sourceGaloisClosureConstantAlgebra m) P
noncomputable def sourceGaloisWPrincipalDivisor_closurePlaceEquiv (m : ℕ) :
    sourceGaloisWPrincipalDivisor_DirectClosurePlace m ≃ sourceGaloisWPrincipalDivisor_ClosurePlace m :=
  GlobalPlace.repackageEquiv
    (@AffinePlace.constantAlgebra F256 (sourceGaloisWPrincipalDivisor_E m) _ _
      (sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra m))
    (sourceGaloisClosureConstantAlgebra m)
noncomputable def sourceGaloisWPrincipalDivisor_polarDivisorOnClosure (m : ℕ) (x : sourceGaloisWPrincipalDivisor_E m) :
    Divisor (sourceGaloisWPrincipalDivisor_ClosurePlace m) := by
  classical
  exact if hx : x = 0 then 0
    else (-GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisWPrincipalDivisor_E m)
      (Units.mk0 x hx)) ⊔ 0
noncomputable def sourceGaloisWPrincipalDivisor_polarDivisorOnDirectClosure (m : ℕ) (x : sourceGaloisWPrincipalDivisor_E m) :
    Divisor (sourceGaloisWPrincipalDivisor_DirectClosurePlace m) :=
  GlobalPlace.polarDivisor
    (π := sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra m)
    (ρ := sourceGaloisClosureRatFuncAlgebra m)
    (τ := sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower m)
    (φ := sourceGaloisClosureFunctionField m)
    (s := sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable m)
    (k := F256) (F := sourceGaloisWPrincipalDivisor_E m) x
noncomputable def sourceGaloisWPrincipalDivisor_transportedDirectPolarDivisor (m : ℕ) (x : sourceGaloisWPrincipalDivisor_E m) :
    Divisor (sourceGaloisWPrincipalDivisor_ClosurePlace m) :=
  Finsupp.equivMapDomain (sourceGaloisWPrincipalDivisor_closurePlaceEquiv m)
    (sourceGaloisWPrincipalDivisor_polarDivisorOnDirectClosure m x)
theorem sourceGaloisWClosureGenerator_ne_zero (m : ℕ) :
    ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m) ≠ 0 := by
  let P : SourceGaloisWInfinityPrime m :=
    Classical.choice (sourceGaloisWInfinityPrime_nonempty m)
  have horder := sourceGaloisWInfinityPlaceOfPrime_order_generator m P
  intro hzero
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder
  have hpositive := sourceGaloisWInfinityRamificationIndex_pos m
  omega
noncomputable def sourceGaloisWClosureGeneratorPoleDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (sourceGaloisWPrincipalDivisor_E m)) :=
  sourceGaloisWPrincipalDivisor_polarDivisorOnClosure m
    ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


