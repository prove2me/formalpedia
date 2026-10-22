-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_HochsterActualComparison_Defs
-- name    : LPCA_Solutions_LPCA_HochsterActualComparison_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:30:43.106571+00:00
-- url     : https://prove2.me/theorems/7d6dce0c-72fa-4e05-a598-848c4e680647
-- title:
--   Actual homogeneous Čech terms and reduced face cochains
-- statement:
--   This bundle supplies actual homogeneous Čech terms and reduced face cochains. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The source is the actual localized homogeneous cochain module.
--   - The actual fixed-degree Cech complex is the nonnegative restriction of the intrinsic signed link cochain complex with offset |negativeSupport|.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_HochsterActualComparison.lean, selected declarations in lines 16–74; source SHA-256 a279817268fb23da04550643dd8bea0603a181219eb3d607fe5272c7fd6bb551; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.Embedding.Restriction
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
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
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

theorem offsetFaceComplex_d (rank : V ↪ ℕ) (K : Complex V) (m n : ℤ) :
    (offsetFaceComplex k rank K m).d n (n + 1) =
      ModuleCat.ofHom (offsetFaceDifferential k rank K m n) := by
  letI : LinearOrder V := rankLinearOrder rank
  exact CochainComplex.of_d
    (fun n => ModuleCat.of k (OffsetFaceIndex K m n → k))
    (fun n => ModuleCat.ofHom (offsetFaceDifferential k rank K m n)) n

/-- The source is the actual localized homogeneous cochain module. -/
noncomputable def hochsterOffsetActualTermEquiv (rank : V ↪ ℕ) (K : Complex V)
    (a : V → ℤ) (q : ℕ) (ha : positiveSupport a = ∅) :
    (localizedCechComplex k rank K Finset.univ a).X q ≃ₗ[k]
      (OffsetFaceIndex (link K (negativeSupport a)) (negativeSupport a).card (q : ℤ) → k) := by
  let A := CechBasis K Finset.univ a q
  let B := OffsetFaceIndex (link K (negativeSupport a)) (negativeSupport a).card (q : ℤ)
  let e0 : (localizedCechComplex k rank K Finset.univ a).X q ≃ₗ[k] (A → k) :=
    actualTermEquivModel k K Finset.univ a q
  let e1 : (A → k) ≃ₗ[k] (B → k) := hochsterModelLinkEquiv k rank K a q ha
  exact e0.trans e1

theorem hochsterOffsetActualTermEquiv_differential
    (rank : V ↪ ℕ) (K : Complex V) (a : V → ℤ) (q : ℕ)
    (ha : positiveSupport a = ∅)
    (x : (localizedCechComplex k rank K Finset.univ a).X q) :
    hochsterOffsetActualTermEquiv k rank K a (q + 1) ha
        ((localizedCechComplex k rank K Finset.univ a).d q (q + 1) x) =
      offsetFaceDifferential k rank (link K (negativeSupport a))
        (negativeSupport a).card (q : ℤ)
        (hochsterOffsetActualTermEquiv k rank K a q ha x) := by
  rw [localizedCechComplex_d]
  change hochsterModelLinkEquiv k rank K a (q + 1) ha
      (actualToModel k K Finset.univ a (q + 1)
        (actualDifferential k (cechCoefficient k rank) K Finset.univ a q x)) = _
  rw [actualDifferential_coordinates, incidenceCoefficient_cech]
  exact hochsterModelLinkEquiv_differential k rank K a q ha
    (actualToModel k K Finset.univ a q x)

/-- The actual fixed-degree Cech complex is the nonnegative restriction
of the intrinsic signed link cochain complex with offset |negativeSupport|. -/
noncomputable def hochsterActualComplexIso (rank : V ↪ ℕ) (K : Complex V)
    (a : V → ℤ) (ha : positiveSupport a = ∅) :
    localizedCechComplex k rank K Finset.univ a ≅
      (offsetFaceComplex k rank (link K (negativeSupport a))
        (negativeSupport a).card).restriction ComplexShape.embeddingUpNat := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun q => (hochsterOffsetActualTermEquiv k rank K a q ha).toModuleIso) ?_
  intro p q hpq
  change p + 1 = q at hpq
  subst q
  change (hochsterOffsetActualTermEquiv k rank K a p ha).toModuleIso.hom ≫
      (offsetFaceComplex k rank (link K (negativeSupport a))
        (negativeSupport a).card).d (p : ℤ) ((p : ℤ) + 1) =
    (localizedCechComplex k rank K Finset.univ a).d p (p + 1) ≫
      (hochsterOffsetActualTermEquiv k rank K a (p + 1) ha).toModuleIso.hom
  rw [offsetFaceComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (hochsterOffsetActualTermEquiv_differential k rank K a p ha x).symm

end LPCA


