-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_HochsterPersistence_Defs
-- name    : LPCA_Solutions_LPCA_HochsterPersistence_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:51:33.792119+00:00
-- url     : https://prove2.me/theorems/65734d24-30e7-4715-8617-419227e57590
-- title:
--   Natural Hochster identifications for reversed-real persistence
-- statement:
--   This bundle supplies natural Hochster identifications for reversed-real persistence. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The specified face reindexing, rather than an independently chosen homology isomorphism, commutes with ordinary reduced restriction.
--   - Hochster's comparison using the fixed coefficient/sign cochain map and specified offset reindexing. It covers void links and degree -1.
--   - The source is the actual homogeneous subspace of the original Ext-colimit local cohomology object, with its original structure maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_HochsterPersistence.lean, selected declarations in lines 19–91; source SHA-256 2f6255c92a8bc5b4f5eb9197bbdd9d796fae0ebbd38c630f75b61560fe348752; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCoordinates_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterActualComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainNaturality_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_KoszulModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyModuleNaturality_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory HomologicalComplex

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- The specified face reindexing, rather than an independently chosen
homology isomorphism, commutes with ordinary reduced restriction. -/
@[reassoc] theorem canonicalOffsetFaceHomologyIsoReduced_restriction
    (rank : V ↪ ℕ) {K L : Complex V} (h : K.faces ⊆ L.faces) (m n : ℤ) :
    homologyMap (offsetFaceRestriction k rank h m) n ≫
        (canonicalOffsetFaceHomologyIsoReduced k rank K m n).hom =
      (canonicalOffsetFaceHomologyIsoReduced k rank L m n).hom ≫
        reducedFaceCohomologyRestriction k rank h (n - m - 1) :=
  faceOffsetHomologyIsoReduced_naturality k rank h m n (n - m - 1) (by omega)

/-- Hochster's comparison using the fixed coefficient/sign cochain map
and specified offset reindexing. It covers void links and degree -1. -/
noncomputable def canonicalHochsterCechLinkCohomologyIso (rank : V ↪ ℕ)
    (K : Complex V) (a : V → ℤ) (q : ℕ) (ha : positiveSupport a = ∅) :
    localizedCechCohomology k rank K Finset.univ a q ≅
      reducedFaceCohomology k rank (link K (negativeSupport a))
        ((q : ℤ) - ((negativeSupport a).card : ℤ) - 1) :=
  (homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) q).mapIso
      (hochsterActualComplexIso k rank K a ha) ≪≫
    natRestrictionHomologyIso k
      (offsetFaceComplex k rank (link K (negativeSupport a)) (negativeSupport a).card)
      (offsetFaceComplex_isZero_below k rank (link K (negativeSupport a))
        (negativeSupport a).card (-1) (by omega)) q ≪≫
    canonicalOffsetFaceHomologyIsoReduced k rank (link K (negativeSupport a))
      (negativeSupport a).card (q : ℤ)

@[reassoc] theorem canonicalHochsterCechLinkCohomologyIso_restriction
    (rank : V ↪ ℕ) {K L : Complex V} (h : K.faces ⊆ L.faces)
    (a : V → ℤ) (q : ℕ) (ha : positiveSupport a = ∅) :
    localizedCechCohomologyRestriction k rank h Finset.univ a q ≫
        (canonicalHochsterCechLinkCohomologyIso k rank K a q ha).hom =
      (canonicalHochsterCechLinkCohomologyIso k rank L a q ha).hom ≫
        reducedFaceCohomologyRestriction k rank (link_faces_mono h (negativeSupport a))
          ((q : ℤ) - ((negativeSupport a).card : ℤ) - 1) := by
  have h₀ := congrArg (fun z => homologyMap z q)
    (hochsterActualComplexIso_restriction k rank h a ha)
  rw [homologyMap_comp, homologyMap_comp] at h₀
  have h₁ := natRestrictionHomologyIso_naturality k
    (offsetFaceRestriction k rank (link_faces_mono h (negativeSupport a))
      (negativeSupport a).card)
    (offsetFaceComplex_isZero_below k rank (link L (negativeSupport a))
      (negativeSupport a).card (-1) (by omega))
    (offsetFaceComplex_isZero_below k rank (link K (negativeSupport a))
      (negativeSupport a).card (-1) (by omega)) q
  have h₂ := canonicalOffsetFaceHomologyIsoReduced_restriction k rank
    (link_faces_mono h (negativeSupport a)) (negativeSupport a).card (q : ℤ)
  dsimp only [canonicalHochsterCechLinkCohomologyIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  dsimp only [localizedCechCohomologyRestriction, localizedCechCohomology, homologyFunctor]
  rw [reassoc_of% h₀, reassoc_of% h₁, h₂]

/-- The source is the actual homogeneous subspace of the original
Ext-colimit local cohomology object, with its original structure maps. -/
noncomputable def canonicalHochsterSupportPieceIso (rank : V ↪ ℕ)
    (K : Complex V) (a : V → ℤ) (q : ℕ) (ha : positiveSupport a = ∅) :
    ModuleCat.of k (supportCohomologyPiece k rank K Finset.univ a q) ≅
      reducedFaceCohomology k rank (link K (negativeSupport a))
        ((q : ℤ) - ((negativeSupport a).card : ℤ) - 1) :=
  supportCohomologyPieceIso k rank K Finset.univ a q ≪≫
    canonicalHochsterCechLinkCohomologyIso k rank K a q ha

@[reassoc] theorem canonicalHochsterSupportPieceIso_restriction
    (rank : V ↪ ℕ) {K L : Complex V} (h : K.faces ⊆ L.faces)
    (a : V → ℤ) (q : ℕ) (ha : positiveSupport a = ∅) :
    supportCohomologyPieceRestriction k rank h Finset.univ a q ≫
        (canonicalHochsterSupportPieceIso k rank K a q ha).hom =
      (canonicalHochsterSupportPieceIso k rank L a q ha).hom ≫
        reducedFaceCohomologyRestriction k rank (link_faces_mono h (negativeSupport a))
          ((q : ℤ) - ((negativeSupport a).card : ℤ) - 1) := by
  dsimp only [canonicalHochsterSupportPieceIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [supportCohomologyPieceIso_restriction_assoc k rank h Finset.univ a q,
    canonicalHochsterCechLinkCohomologyIso_restriction k rank h a q ha]





end LPCA


