-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_Defs
-- name    : LPCA_Solutions_LPCA_GradedSupportRestriction_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:42:53.723871+00:00
-- url     : https://prove2.me/theorems/15e37b4f-0453-485c-b044-39e9167e54bf
-- title:
--   Graded Support Restriction for localized persistent commutative algebra
-- statement:
--   This bundle supplies graded Support Restriction for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual homogeneous inclusions into the original Ext-colimit objects commute with the original quotient-induced structure maps.
--   - Restrict the original Ext map to its actual homogeneous subspaces. The underlying map is unchanged, rather than transported from a Cech model.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_GradedSupportRestriction.lean, selected declarations in lines 18–141; source SHA-256 14198a3f71e8081a01477d88860499512b165f5f7f15c0a09437272a3b163f80; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
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

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

noncomputable def supportCohomologyFieldRestriction {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) (q : ℕ) :
    supportCohomologyField k L T q ⟶ supportCohomologyField k K T q :=
  (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).map
    (supportCohomologyRestriction k h T q)

@[reassoc] theorem ambientCechHomologyFieldIso_inv_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (T : Finset V) (q : ℕ) :
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).map
        (homologyMap (ambientCechRestriction k rank h T) q) ≫
        (ambientCechHomologyFieldIso k rank K T q).inv =
      (ambientCechHomologyFieldIso k rank L T q).inv ≫
        homologyMap (ambientCechFieldRestriction k rank h T) q := by
  exact ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} (MvPolynomial V k))
      (ComplexShape.up ℕ) q).map (ambientCechRestriction k rank h T))
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k))

@[reassoc] theorem supportCohomologyFieldCechIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (T : Finset V) (q : ℕ) :
    supportCohomologyFieldRestriction k h T q ≫
        (supportCohomologyFieldCechIso k rank K T q).hom =
      (supportCohomologyFieldCechIso k rank L T q).hom ≫
        homologyMap (ambientCechFieldRestriction k rank h T) q := by
  change (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).map
      (supportCohomologyRestriction k h T q) ≫
      ((ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).map
        (supportCohomologyCechIso k rank K T q).hom ≫
        (ambientCechHomologyFieldIso k rank K T q).inv) = _
  rw [← Category.assoc, ← Functor.map_comp, supportCohomologyCechIso_restriction,
    Functor.map_comp, Category.assoc, ambientCechHomologyFieldIso_inv_restriction]
  rfl

@[reassoc] theorem supportCohomologyFieldCechIso_inv_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (T : Finset V) (q : ℕ) :
    (supportCohomologyFieldCechIso k rank L T q).inv ≫
        supportCohomologyFieldRestriction k h T q =
      homologyMap (ambientCechFieldRestriction k rank h T) q ≫
        (supportCohomologyFieldCechIso k rank K T q).inv := by
  have hn := congrArg (fun g =>
    (supportCohomologyFieldCechIso k rank L T q).inv ≫ g ≫
      (supportCohomologyFieldCechIso k rank K T q).inv)
    (supportCohomologyFieldCechIso_restriction k rank h T q)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using hn

/-- The actual homogeneous inclusions into the original Ext-colimit
objects commute with the original quotient-induced structure maps. -/
@[reassoc] theorem supportCohomologyDegreeInclusion_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces)
    (T : Finset V) (a : V → ℤ) (q : ℕ) :
    supportCohomologyDegreeInclusion k rank L T a q ≫
        supportCohomologyFieldRestriction k h T q =
      localizedCechCohomologyRestriction k rank h T a q ≫
        supportCohomologyDegreeInclusion k rank K T a q := by
  rw [supportCohomologyDegreeInclusion_actual, supportCohomologyDegreeInclusion_actual]
  rw [Category.assoc, supportCohomologyFieldCechIso_inv_restriction]
  rw [← Category.assoc, localizedCechDegreeInclusion_homology_restriction, Category.assoc]

theorem supportCohomologyRestriction_piece (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces)
    (T : Finset V) (a : V → ℤ) (q : ℕ)
    {x : supportCohomologyField k L T q}
    (hx : x ∈ supportCohomologyPiece k rank L T a q) :
    supportCohomologyFieldRestriction k h T q x ∈
      supportCohomologyPiece k rank K T a q := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨localizedCechCohomologyRestriction k rank h T a q y, ?_⟩
  exact (congrArg (fun g => g y)
    (supportCohomologyDegreeInclusion_restriction k rank h T a q)).symm

/-- Restrict the original Ext map to its actual homogeneous subspaces.
The underlying map is unchanged, rather than transported from a Cech model. -/
noncomputable def supportCohomologyPieceRestriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces)
    (T : Finset V) (a : V → ℤ) (q : ℕ) :
    ModuleCat.of k (supportCohomologyPiece k rank L T a q) ⟶
      ModuleCat.of k (supportCohomologyPiece k rank K T a q) :=
  ModuleCat.ofHom {
    toFun x := ⟨supportCohomologyFieldRestriction k h T q x.1,
      supportCohomologyRestriction_piece k rank h T a q x.property⟩
    map_add' x y := Subtype.ext
      ((supportCohomologyFieldRestriction k h T q).hom.map_add x.1 y.1)
    map_smul' c x := Subtype.ext
      ((supportCohomologyFieldRestriction k h T q).hom.map_smul c x.1) }

theorem supportCohomologyPieceRestriction_refl (rank : V ↪ ℕ)
    (K : Complex V) (T : Finset V) (a : V → ℤ) (q : ℕ) :
    supportCohomologyPieceRestriction k rank (Finset.Subset.refl K.faces) T a q = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change supportCohomologyRestriction k (Finset.Subset.refl K.faces) T q x.1 = x.1
  rw [supportCohomologyRestriction_refl]
  rfl

theorem supportCohomologyPieceRestriction_comp (rank : V ↪ ℕ)
    {K L M : Complex V} (hKL : K.faces ⊆ L.faces) (hLM : L.faces ⊆ M.faces)
    (T : Finset V) (a : V → ℤ) (q : ℕ) :
    supportCohomologyPieceRestriction k rank hLM T a q ≫
        supportCohomologyPieceRestriction k rank hKL T a q =
      supportCohomologyPieceRestriction k rank (hKL.trans hLM) T a q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun g => g x.1) (supportCohomologyRestriction_comp k hKL hLM T q)

@[reassoc] theorem supportCohomologyPieceIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces)
    (T : Finset V) (a : V → ℤ) (q : ℕ) :
    supportCohomologyPieceRestriction k rank h T a q ≫
        (supportCohomologyPieceIso k rank K T a q).hom =
      (supportCohomologyPieceIso k rank L T a q).hom ≫
        localizedCechCohomologyRestriction k rank h T a q := by
  haveI : Mono (supportCohomologyDegreeInclusion k rank K T a q) :=
    (ModuleCat.mono_iff_injective _).mpr
      (supportCohomologyDegreeInclusion_injective k rank K T a q)
  apply (cancel_mono (supportCohomologyDegreeInclusion k rank K T a q)).mp
  rw [Category.assoc, supportCohomologyPieceIso_hom_inclusion]
  rw [Category.assoc, ← supportCohomologyDegreeInclusion_restriction,
    ← Category.assoc, supportCohomologyPieceIso_hom_inclusion]
  rfl





end LPCA


