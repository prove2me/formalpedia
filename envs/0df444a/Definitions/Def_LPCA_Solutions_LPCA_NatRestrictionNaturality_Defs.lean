-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionNaturality_Defs
-- name    : LPCA_Solutions_LPCA_NatRestrictionNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:44:11.564965+00:00
-- url     : https://prove2.me/theorems/d903bdd0-3a3b-44ba-820b-4e1be8d03e4f
-- title:
--   Naturality of restriction to nonnegative cochain degrees
-- statement:
--   These module-category constructions compare short complexes and their homology under restriction from integer degrees to nonnegative degrees. Naturality of the resulting homology isomorphism retains its degree-minus-one zero-object hypotheses. The included inverse-square identity is categorical.
--
--   The included constructions and necessary compatibility results are:
--
--   - The already fixed restriction comparison is natural, including the degree-zero augmentation boundary handled by its actual short-complex map.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_NatRestrictionNaturality.lean, selected declarations in lines 16–144; source SHA-256 0d361b4bb6e4aa17b2ad4af33d0ba1132602f55001b1018cc20b5d99b8c8d1d1; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_redRestrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_dLin_idxCongr_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_restrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientFieldScalars_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CanonicalFaceOffset_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceOffsetNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterActualComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCohomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterIncidence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterLinkTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterNonfaceVanishing_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterSigns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDegreeSeparation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable (R : Type u) [Ring R]

@[reassoc] theorem homologyIsoScNat_naturality
    {A B : CochainComplex (ModuleCat.{u} R) ℕ} (f : A ⟶ B)
    (i j l : ℕ) (hi : (ComplexShape.up ℕ).prev j = i)
    (hl : (ComplexShape.up ℕ).next j = l) :
    homologyMap f j ≫ (B.homologyIsoSc' i j l hi hl).hom =
      (A.homologyIsoSc' i j l hi hl).hom ≫ ShortComplex.homologyMap
        ((shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℕ) i j l).map f) := by
  change ShortComplex.homologyMap
      ((shortComplexFunctor (ModuleCat R) (ComplexShape.up ℕ) j).map f) ≫
      ShortComplex.homologyMap (B.isoSc' i j l hi hl).hom =
    ShortComplex.homologyMap (A.isoSc' i j l hi hl).hom ≫ ShortComplex.homologyMap _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  apply congrArg (fun z : A.sc j ⟶ B.sc' i j l => ShortComplex.homologyMap z)
  exact (natIsoSc' (ModuleCat R) (ComplexShape.up ℕ) i j l hi hl).hom.naturality f

@[reassoc] theorem iso_inverse_square {C : Type*} [Category* C]
    {A B X Y : C} (e : A ≅ X) (f : B ≅ Y) (a : A ⟶ B) (b : X ⟶ Y)
    (h : a ≫ f.hom = e.hom ≫ b) : b ≫ f.inv = e.inv ≫ a := by
  have hn := congrArg (fun z => e.inv ≫ z ≫ f.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using hn.symm

noncomputable def natRestrictionZeroShortMap (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (K.restriction ComplexShape.embeddingUpNat).sc' 0 0 1 ⟶ K.sc' (-1) 0 1 where
  τ₁ := 0
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    change (0 : K.X 0 ⟶ K.X (-1)) ≫ K.d (-1) 0 = K.d 0 0 ≫ 𝟙 _
    rw [zero_comp, K.shape 0 0 (by decide), zero_comp]
  comm₂₃ := by
    change (𝟙 (K.X 0)) ≫ K.d 0 1 = K.d 0 1 ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

theorem natRestrictionZeroShortMap_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    (shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℕ) 0 0 1).map
        (restrictionMap f ComplexShape.embeddingUpNat) ≫ natRestrictionZeroShortMap R L =
      natRestrictionZeroShortMap R K ≫
        (shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℤ) (-1) 0 1).map f := by
  apply ShortComplex.hom_ext
  · change f.f 0 ≫ (0 : L.X 0 ⟶ L.X (-1)) = (0 : K.X 0 ⟶ K.X (-1)) ≫ f.f (-1)
    rw [comp_zero, zero_comp]
  · change f.f 0 ≫ 𝟙 _ = 𝟙 _ ≫ f.f 0
    rw [Category.comp_id, Category.id_comp]
  · change f.f 1 ≫ 𝟙 _ = 𝟙 _ ≫ f.f 1
    rw [Category.comp_id, Category.id_comp]

noncomputable def natRestrictionSuccShortIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℕ) :
    (K.restriction ComplexShape.embeddingUpNat).sc' p (p + 1) (p + 2) ≅
      K.sc' (p : ℤ) ((p + 1 : ℕ) : ℤ) ((p + 2 : ℕ) : ℤ) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

theorem natRestrictionSuccShortIso_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (p : ℕ) :
    (shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℕ) p (p + 1) (p + 2)).map
        (restrictionMap f ComplexShape.embeddingUpNat) ≫ (natRestrictionSuccShortIso R L p).hom =
      (natRestrictionSuccShortIso R K p).hom ≫
        (shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℤ)
          (p : ℤ) ((p + 1 : ℕ) : ℤ) ((p + 2 : ℕ) : ℤ)).map f := by
  apply ShortComplex.hom_ext
  · change f.f (p : ℤ) ≫ 𝟙 _ = 𝟙 _ ≫ f.f (p : ℤ)
    rw [Category.comp_id, Category.id_comp]
  · change f.f ((p + 1 : ℕ) : ℤ) ≫ 𝟙 _ = 𝟙 _ ≫ f.f ((p + 1 : ℕ) : ℤ)
    rw [Category.comp_id, Category.id_comp]
  · change f.f ((p + 2 : ℕ) : ℤ) ≫ 𝟙 _ = 𝟙 _ ≫ f.f ((p + 2 : ℕ) : ℤ)
    rw [Category.comp_id, Category.id_comp]

/-- The already fixed restriction comparison is natural, including the
degree-zero augmentation boundary handled by its actual short-complex map. -/
@[reassoc] theorem natRestrictionHomologyIso_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hK : CategoryTheory.Limits.IsZero (K.X (-1)))
    (hL : CategoryTheory.Limits.IsZero (L.X (-1))) (q : ℕ) :
    homologyMap (restrictionMap f ComplexShape.embeddingUpNat) q ≫
        (natRestrictionHomologyIso R L hL q).hom =
      (natRestrictionHomologyIso R K hK q).hom ≫ homologyMap f (q : ℤ) := by
  cases q with
  | zero =>
    have h₀ := homologyIsoScNat_naturality R
      (restrictionMap f ComplexShape.embeddingUpNat) 0 0 1 (by simp) (by simp)
    have h₁ := congrArg (fun z :
        (K.restriction ComplexShape.embeddingUpNat).sc' 0 0 1 ⟶ L.sc' (-1) 0 1 =>
        ShortComplex.homologyMap z) (natRestrictionZeroShortMap_naturality R f)
    rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h₁
    have h₂ := iso_inverse_square
      (K.homologyIsoSc' (-1) 0 1 (by simp) (by simp))
      (L.homologyIsoSc' (-1) 0 1 (by simp) (by simp)) _ _
      (homologyIsoSc_naturality R f (-1) 0 1 (by simp) (by simp))
    change homologyMap (restrictionMap f ComplexShape.embeddingUpNat) 0 ≫
        ((L.restriction ComplexShape.embeddingUpNat).homologyIsoSc' 0 0 1 (by simp) (by simp)).hom ≫
          ShortComplex.homologyMap (natRestrictionZeroShortMap R L) ≫
            (L.homologyIsoSc' (-1) 0 1 (by simp) (by simp)).inv =
      (((K.restriction ComplexShape.embeddingUpNat).homologyIsoSc' 0 0 1 (by simp) (by simp)).hom ≫
          ShortComplex.homologyMap (natRestrictionZeroShortMap R K) ≫
            (K.homologyIsoSc' (-1) 0 1 (by simp) (by simp)).inv) ≫ homologyMap f (0 : ℤ)
    rw [reassoc_of% h₀, reassoc_of% h₁, h₂]
    simp only [Category.assoc]
  | succ p =>
    have h₀ := homologyIsoScNat_naturality R
      (restrictionMap f ComplexShape.embeddingUpNat) p (p + 1) (p + 2)
        (by simp) (by simp)
    have h₁ := congrArg (fun z :
        (K.restriction ComplexShape.embeddingUpNat).sc' p (p + 1) (p + 2) ⟶
          L.sc' (p : ℤ) ((p + 1 : ℕ) : ℤ) ((p + 2 : ℕ) : ℤ) => ShortComplex.homologyMap z)
      (natRestrictionSuccShortIso_naturality R f p)
    rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h₁
    have h₂ := iso_inverse_square
      (K.homologyIsoSc' (p : ℤ) ((p + 1 : ℕ) : ℤ) ((p + 2 : ℕ) : ℤ)
        (by simp) (by simp [add_assoc]))
      (L.homologyIsoSc' (p : ℤ) ((p + 1 : ℕ) : ℤ) ((p + 2 : ℕ) : ℤ)
        (by simp) (by simp [add_assoc])) _ _
      (homologyIsoSc_naturality R f (p : ℤ) ((p + 1 : ℕ) : ℤ) ((p + 2 : ℕ) : ℤ)
        (by simp) (by simp [add_assoc]))
    change homologyMap (restrictionMap f ComplexShape.embeddingUpNat) (p + 1) ≫
        ((L.restriction ComplexShape.embeddingUpNat).homologyIsoSc' p (p + 1) (p + 2)
          (by simp) (by simp)).hom ≫
          ShortComplex.homologyMap (natRestrictionSuccShortIso R L p).hom ≫
            (L.homologyIsoSc' (p : ℤ) ((p + 1 : ℕ) : ℤ) ((p + 2 : ℕ) : ℤ)
              (by simp) (by simp [add_assoc])).inv =
      (((K.restriction ComplexShape.embeddingUpNat).homologyIsoSc' p (p + 1) (p + 2)
          (by simp) (by simp)).hom ≫
          ShortComplex.homologyMap (natRestrictionSuccShortIso R K p).hom ≫
            (K.homologyIsoSc' (p : ℤ) ((p + 1 : ℕ) : ℤ) ((p + 2 : ℕ) : ℤ)
              (by simp) (by simp [add_assoc])).inv) ≫ homologyMap f ((p + 1 : ℕ) : ℤ)
    rw [reassoc_of% h₀, reassoc_of% h₁, h₂]
    simp only [Category.assoc]

end LPCA


