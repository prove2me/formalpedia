-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:40:03.531687+00:00
-- url     : https://prove2.me/theorems/ef2f7a8f-342b-4be2-a47b-33ddf6ecb871
-- title:
--   Source Galois WNormal
-- statement:
--   Definitions and structural lemmas for Source Galois WNormal, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWNormal.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureFiniteCompositum
import Mathlib.FieldTheory.KummerExtension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceGaloisWFieldGenerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivRatFunc_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWField_finrank
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
import Theorems.Thm_QEC_Coding_f256_card
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceGaloisWFieldGenerator
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldEquivRatFunc_X
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
theorem f256_has_primitive_root_two_hundred_fifty_five :
    ∃ zeta : F256, IsPrimitiveRoot zeta 255 := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := F256ˣ)
  refine ⟨(u : F256), ?_⟩
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hu,
    Nat.card_eq_fintype_card, Fintype.card_units, QEC.Coding.f256_card]
theorem sourceGaloisBaseField_primitiveRoots_fifteen_nonempty :
    (primitiveRoots 15 GaloisBaseField).Nonempty := by
  obtain ⟨zeta, hzeta⟩ := f256_has_primitive_root_two_hundred_fifty_five
  have hzeta15 : IsPrimitiveRoot (zeta ^ 17) 15 :=
    hzeta.pow (by norm_num : 0 < 255) (by norm_num : 255 = 17 * 15)
  let zetaBase : GaloisBaseField :=
    algebraMap F256 GaloisBaseField (zeta ^ 17)
  refine ⟨zetaBase, (mem_primitiveRoots (by norm_num : 0 < 15)).2 ?_⟩
  exact hzeta15.map_of_injective (algebraMap F256 GaloisBaseField).injective
theorem sourceGaloisWField_adjoin_generator_over_constants_eq_top :
    F256⟮sourceGaloisWFieldGenerator⟯ = ⊤ := by
  let e := sourceGaloisWFieldEquivRatFunc
  calc
    F256⟮sourceGaloisWFieldGenerator⟯ =
        (F256⟮(RatFunc.X : RatFunc F256)⟯).map e.toAlgHom := by
      rw [← sourceGaloisWFieldEquivRatFunc_X,
        IntermediateField.adjoin_map]
      simp only [Set.image_singleton]
      change F256⟮sourceGaloisWFieldEquivRatFunc RatFunc.X⟯ =
        F256⟮sourceGaloisWFieldEquivRatFunc RatFunc.X⟯
      rfl
    _ = (⊤ : IntermediateField F256 (RatFunc F256)).map e.toAlgHom := by
      rw [RatFunc.adjoin_X]
    _ = e.toAlgHom.fieldRange :=
      (AlgHom.fieldRange_eq_map e.toAlgHom).symm
    _ = ⊤ := AlgHom.fieldRange_eq_top.mpr e.surjective
theorem sourceGaloisWField_adjoin_generator_eq_top :
    GaloisBaseField⟮sourceGaloisWFieldGenerator⟯ = ⊤ :=
  IntermediateField.adjoin_eq_top_of_adjoin_eq_top F256
    sourceGaloisWField_adjoin_generator_over_constants_eq_top
theorem sourceGaloisWFieldGenerator_pow_fifteen :
    sourceGaloisWFieldGenerator ^ 15 =
      algebraMap GaloisBaseField SourceGaloisWField
        (AdjoinSimple.gen F256 galoisBaseZ) := by
  apply Subtype.ext
  change galoisBaseW ^ 15 = galoisBaseZ
  rfl
theorem sourceGaloisWField_isGalois_and_isCyclic :
    IsGalois GaloisBaseField SourceGaloisWField ∧
      IsCyclic Gal(SourceGaloisWField / GaloisBaseField) := by
  let z : GaloisBaseField := AdjoinSimple.gen F256 galoisBaseZ
  have hpow : sourceGaloisWFieldGenerator ^
        Module.finrank GaloisBaseField SourceGaloisWField =
      algebraMap GaloisBaseField SourceGaloisWField z := by
    rw [sourceGaloisWField_finrank]
    exact sourceGaloisWFieldGenerator_pow_fifteen
  have hirreducible : Irreducible
      (Polynomial.X ^ Module.finrank GaloisBaseField SourceGaloisWField -
        Polynomial.C z) :=
    irreducible_X_pow_sub_C_of_root_adjoin_eq_top hpow
      sourceGaloisWField_adjoin_generator_eq_top
  have hroots :
      (primitiveRoots (Module.finrank GaloisBaseField SourceGaloisWField)
        GaloisBaseField).Nonempty := by
    rw [sourceGaloisWField_finrank]
    exact sourceGaloisBaseField_primitiveRoots_fifteen_nonempty
  letI : IsSplittingField GaloisBaseField SourceGaloisWField
      (Polynomial.X ^ Module.finrank GaloisBaseField SourceGaloisWField -
        Polynomial.C z) :=
    isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
      hroots hpow
        sourceGaloisWField_adjoin_generator_eq_top
  have hne : NeZero (Module.finrank GaloisBaseField SourceGaloisWField) :=
    ⟨by rw [sourceGaloisWField_finrank]; norm_num⟩
  letI := hne
  exact ⟨
    isGalois_of_isSplittingField_X_pow_sub_C
      hroots hirreducible
        SourceGaloisWField,
    isCyclic_of_isSplittingField_X_pow_sub_C
      hroots hirreducible
        SourceGaloisWField⟩
noncomputable instance sourceGaloisWFieldIsGalois :
    IsGalois GaloisBaseField SourceGaloisWField :=
  sourceGaloisWField_isGalois_and_isCyclic.1
noncomputable instance sourceGaloisWFieldAutIsCyclic :
    IsCyclic Gal(SourceGaloisWField / GaloisBaseField) :=
  sourceGaloisWField_isGalois_and_isCyclic.2
noncomputable def sourceGaloisWFieldToSource (m : ℕ) :
    SourceGaloisWField →ₐ[GaloisBaseField] SourceField m :=
  (IsScalarTower.toAlgHom GaloisBaseField (RatFunc F256) (SourceField m)).comp
    (IntermediateField.extendScalars
      galoisBaseField_le_sourceGaloisWField).val
noncomputable def sourceGaloisWFieldToAmbient (m : ℕ) :
    SourceGaloisWField →ₐ[GaloisBaseField] SourceGaloisClosureAmbient :=
  (sourceGaloisSeedSeparableEmbedding m).comp
    (sourceGaloisWFieldToSource m)
abbrev SourceGaloisWAmbientField (m : ℕ) :
    IntermediateField GaloisBaseField SourceGaloisClosureAmbient :=
  (sourceGaloisWFieldToAmbient m).fieldRange
noncomputable instance (priority := 3000)
    sourceGaloisWAmbientFieldAlgebra (m : ℕ) :
    Algebra GaloisBaseField (SourceGaloisWAmbientField m) :=
  (SourceGaloisWAmbientField m).toSubalgebra.algebra'
noncomputable instance (priority := 3000)
    sourceGaloisWAmbientFieldSMul (m : ℕ) :
    SMul GaloisBaseField (SourceGaloisWAmbientField m) :=
  (sourceGaloisWAmbientFieldAlgebra m).toSMul
noncomputable instance (priority := 3000)
    sourceGaloisWAmbientFieldModule (m : ℕ) :
    Module GaloisBaseField (SourceGaloisWAmbientField m) :=
  @Algebra.toModule GaloisBaseField (SourceGaloisWAmbientField m) _ _
    (sourceGaloisWAmbientFieldAlgebra m)
noncomputable def sourceGaloisWFieldEquivAmbientField (m : ℕ) :
    SourceGaloisWField ≃ₐ[GaloisBaseField] SourceGaloisWAmbientField m :=
  AlgEquiv.ofInjectiveField (sourceGaloisWFieldToAmbient m)
noncomputable instance sourceGaloisWAmbientFieldIsGalois (m : ℕ) :
    IsGalois GaloisBaseField (SourceGaloisWAmbientField m) :=
  IsGalois.of_algEquiv (sourceGaloisWFieldEquivAmbientField m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


