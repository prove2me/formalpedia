-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
-- name    : LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:38:47.241632+00:00
-- url     : https://prove2.me/theorems/d630a5e5-d846-4f35-a1bf-a6b4deb86f9b
-- title:
--   Graded Face Restriction Čech for localized persistent commutative algebra
-- statement:
--   This bundle supplies graded Face Restriction Čech for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual homogeneous-subcomplex restriction, with no basis replacement and no identification with Ext structure maps assumed.
--   - The degree inclusions commute with actual face restriction before taking cohomology. This is the concrete grading square on Cech models.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_GradedFaceRestrictionCech.lean, selected declarations in lines 20–156; source SHA-256 eb10b68e5b0c2fbd5fd47973054979a23636e51ae70aa7daad4a2ae72d3ad194; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
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

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule

noncomputable def localizedCechTermRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    (localizedCechComplex k rank L T a).X p →ₗ[k]
      (localizedCechComplex k rank K T a).X p where
  toFun y F := pieceFaceRestriction k h F.1 a (y F)
  map_add' x y := by
    funext F
    exact (pieceFaceRestriction k h F.1 a).map_add (x F) (y F)
  map_smul' c x := by
    funext F
    exact (pieceFaceRestriction k h F.1 a).map_smul c (x F)

theorem localizedCechTermRestriction_differential (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (y : (localizedCechComplex k rank L T a).X p) :
    localizedCechTermRestriction k rank h T a (p + 1)
        (actualDifferential k (cechCoefficient k rank) L T a p y) =
      actualDifferential k (cechCoefficient k rank) K T a p
        (localizedCechTermRestriction k rank h T a p y) := by
  classical
  funext G
  change pieceFaceRestriction k h G.1 a
      (actualDifferential k (cechCoefficient k rank) L T a p y G) =
    actualDifferential k (cechCoefficient k rank) K T a p
      (fun F => pieceFaceRestriction k h F.1 a (y F)) G
  rw [actualDifferential_apply_full, actualDifferential_apply_full, map_sum]
  apply Finset.sum_congr rfl
  intro F _
  by_cases hFG : F.1 ⊆ G.1
  · simp only [dif_pos hFG, map_smul]
    apply congrArg (fun z => (cechCoefficient k rank F.1 G.1) • z)
    apply Subtype.ext
    exact (congrArg (fun g => g (y F).1)
      (localizedFaceRestriction_localization k h F.1 G.1 hFG)).symm
  · simp only [dif_neg hFG, map_zero]

/-- The actual homogeneous-subcomplex restriction, with no basis
replacement and no identification with Ext structure maps assumed. -/
noncomputable def localizedCechRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) (a : V → ℤ) :
    localizedCechComplex k rank L T a ⟶ localizedCechComplex k rank K T a where
  f p := ConcreteCategory.ofHom (C := ModuleCat k)
    (localizedCechTermRestriction k rank h T a p)
  comm' := by
    intro p q hpq
    change p + 1 = q at hpq
    subst q
    rw [localizedCechComplex_d, localizedCechComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact (localizedCechTermRestriction_differential k rank h T a p y).symm





noncomputable def ambientCechFieldRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) :
    ambientCechFieldComplex k rank L T ⟶ ambientCechFieldComplex k rank K T :=
  ((ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (ambientCechRestriction k rank h T)

/-- The degree inclusions commute with actual face restriction before
taking cohomology. This is the concrete grading square on Cech models. -/
theorem localizedCechDegreeInclusion_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) (a : V → ℤ) :
    localizedCechDegreeInclusion k rank L T a ≫ ambientCechFieldRestriction k rank h T =
      localizedCechRestriction k rank h T a ≫ localizedCechDegreeInclusion k rank K T a := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rfl

noncomputable def localizedCechCohomologyRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) (a : V → ℤ) (q : ℕ) :
    localizedCechCohomology k rank L T a q ⟶ localizedCechCohomology k rank K T a q :=
  HomologicalComplex.homologyMap (localizedCechRestriction k rank h T a) q





theorem localizedCechDegreeInclusion_homology_restriction
    (rank : V ↪ ℕ) {K L : Complex V} (h : K.faces ⊆ L.faces)
    (T : Finset V) (a : V → ℤ) (q : ℕ) :
    HomologicalComplex.homologyMap (localizedCechDegreeInclusion k rank L T a) q ≫
        HomologicalComplex.homologyMap (ambientCechFieldRestriction k rank h T) q =
      localizedCechCohomologyRestriction k rank h T a q ≫
        HomologicalComplex.homologyMap (localizedCechDegreeInclusion k rank K T a) q := by
  rw [← HomologicalComplex.homologyMap_comp,
    localizedCechDegreeInclusion_restriction, HomologicalComplex.homologyMap_comp]
  rfl



end LPCA


