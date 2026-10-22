-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FaceOffsetNaturality_Defs
-- name    : LPCA_Solutions_LPCA_FaceOffsetNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:39:55.2848+00:00
-- url     : https://prove2.me/theorems/fe1a1a31-f0a9-4c83-a621-74fe0aa7f074
-- title:
--   Face Offset Naturality for localized persistent commutative algebra
-- statement:
--   This bundle supplies face Offset Naturality for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The specified offset comparison commutes with ordinary cohomology restriction. The earlier existence-only comparison is left unchanged.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_FaceOffsetNaturality.lean, selected declarations in lines 13–112; source SHA-256 3edc7b52cef62bcf095a577766397fd2e7bdfbef5465a98f3822d1b3ab8a0439; source certificate Sapelo2 job 49172236.

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

open CategoryTheory

universe u

@[reassoc] theorem homologyIsoSc_naturality (R : Type u) [Ring R]
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B)
    (i j l : ℤ) (hi : (ComplexShape.up ℤ).prev j = i)
    (hl : (ComplexShape.up ℤ).next j = l) :
    HomologicalComplex.homologyMap f j ≫ (B.homologyIsoSc' i j l hi hl).hom =
      (A.homologyIsoSc' i j l hi hl).hom ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℤ) i j l).map f) := by
  change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) j).map f) ≫
      ShortComplex.homologyMap (B.isoSc' i j l hi hl).hom =
    ShortComplex.homologyMap (A.isoSc' i j l hi hl).hom ≫
      ShortComplex.homologyMap _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  apply congrArg (fun z : A.sc j ⟶ B.sc' i j l => ShortComplex.homologyMap z)
  exact (HomologicalComplex.natIsoSc' (ModuleCat R) (ComplexShape.up ℤ) i j l hi hl).hom.naturality f

@[reassoc] theorem homologyMap_index_naturality (R : Type u) [Ring R]
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B)
    {n n' : ℤ} (h : n = n') :
    HomologicalComplex.homologyMap f n ≫
        (eqToIso (congrArg (fun j => B.homology j) h)).hom =
      (eqToIso (congrArg (fun j => A.homology j) h)).hom ≫
        HomologicalComplex.homologyMap f n' := by
  subst n'
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

theorem offsetFaceTermIsoReduced_naturality (rank : V ↪ ℕ) {K L : Complex V}
    (hKL : K.faces ⊆ L.faces) (m n r : ℤ) (h : r - (-1) = n - m) :
    (offsetFaceRestriction k rank hKL m).f n ≫
        (offsetFaceTermIsoReduced k rank K m n r h).hom =
      (offsetFaceTermIsoReduced k rank L m n r h).hom ≫
        (reducedFaceRestriction k rank hKL).f r := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem offsetFaceShortIsoReduced_naturality (rank : V ↪ ℕ) {K L : Complex V}
    (hKL : K.faces ⊆ L.faces) (m a b : ℤ) (h : b - (-1) = a - m) :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat k) (ComplexShape.up ℤ)
        a (a + 1) (a + 1 + 1)).map (offsetFaceRestriction k rank hKL m) ≫
        (offsetFaceShortIsoReduced k rank K m a b h).hom =
      (offsetFaceShortIsoReduced k rank L m a b h).hom ≫
        (HomologicalComplex.shortComplexFunctor' (ModuleCat k) (ComplexShape.up ℤ)
          b (b + 1) (b + 1 + 1)).map (reducedFaceRestriction k rank hKL) := by
  apply ShortComplex.hom_ext
  · exact offsetFaceTermIsoReduced_naturality k rank hKL m a b h
  · exact offsetFaceTermIsoReduced_naturality k rank hKL m (a + 1) (b + 1) (by omega)
  · exact offsetFaceTermIsoReduced_naturality k rank hKL m (a + 1 + 1) (b + 1 + 1) (by omega)

/-- The specified offset comparison commutes with ordinary cohomology
restriction. The earlier existence-only comparison is left unchanged. -/
theorem faceOffsetHomologyIsoReduced_naturality (rank : V ↪ ℕ) {K L : Complex V}
    (hKL : K.faces ⊆ L.faces) (m n r : ℤ) (h : r - (-1) = n - m) :
    HomologicalComplex.homologyMap (offsetFaceRestriction k rank hKL m) n ≫
        (faceOffsetHomologyIsoReduced k rank K m n r h).hom =
      (faceOffsetHomologyIsoReduced k rank L m n r h).hom ≫
        HomologicalComplex.homologyMap (reducedFaceRestriction k rank hKL) r := by
  let a := n - 1
  let b := r - 1
  have hn : n = a + 1 := by dsimp [a]; omega
  have hr : r = b + 1 := by dsimp [b]; omega
  have h₀ : b - (-1) = a - m := by dsimp [a, b]; omega
  dsimp only [faceOffsetHomologyIsoReduced]
  simp only [Iso.trans_hom, Iso.symm_hom, ShortComplex.homologyMapIso_hom,
    Category.assoc]
  rw [homologyMap_index_naturality_assoc k (offsetFaceRestriction k rank hKL m) hn,
    homologyIsoSc_naturality_assoc k (offsetFaceRestriction k rank hKL m)
      a (a + 1) (a + 1 + 1) (by simp) (by simp)]
  have hs := congrArg (fun z :
      (offsetFaceComplex k rank L m).sc' a (a + 1) (a + 1 + 1) ⟶
        (reducedFaceComplex k rank K).sc' b (b + 1) (b + 1 + 1) =>
      ShortComplex.homologyMap z)
    (offsetFaceShortIsoReduced_naturality k rank hKL m a b h₀)
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at hs
  apply (cancel_epi (eqToIso (congrArg
    (fun j => (offsetFaceComplex k rank L m).homology j) hn)).hom).mpr
  apply (cancel_epi ((offsetFaceComplex k rank L m).homologyIsoSc'
    a (a + 1) (a + 1 + 1) (by simp) (by simp)).hom).mpr
  rw [← Category.assoc, hs, Category.assoc]
  apply (cancel_epi
    (ShortComplex.homologyMap (offsetFaceShortIsoReduced k rank L m a b h₀).hom)).mpr
  apply (cancel_mono (eqToIso (congrArg
    (fun j => (reducedFaceComplex k rank K).homology j) hr)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [homologyMap_index_naturality k (reducedFaceRestriction k rank hKL) hr]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply (cancel_mono
    ((reducedFaceComplex k rank K).homologyIsoSc' b (b + 1) (b + 1 + 1)
      (by simp) (by simp)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [homologyIsoSc_naturality k (reducedFaceRestriction k rank hKL)
    b (b + 1) (b + 1 + 1) (by simp) (by simp)]
  dsimp only [b]
  simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc,
    Category.id_comp, Category.comp_id]

end LPCA


