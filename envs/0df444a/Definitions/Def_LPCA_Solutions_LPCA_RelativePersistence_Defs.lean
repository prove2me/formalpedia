-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_RelativePersistence_Defs
-- name    : LPCA_Solutions_LPCA_RelativePersistence_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:49:12.0222+00:00
-- url     : https://prove2.me/theorems/ee130de0-7881-44c4-b0c4-954aca5d0d12
-- title:
--   Relative cohomology over reversed-real persistence
-- statement:
--   This bundle supplies relative cohomology over reversed-real persistence. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_RelativePersistence.lean, selected declarations in lines 25–95; source SHA-256 b6e8b249ab20d4de59de64364d7c535ab541e491d8b09290526095c498ab60fb; source certificate Sapelo2 job 49172236.

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
import Mathlib.Algebra.Homology.HomologySequenceLemmas
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
import Mathlib.CategoryTheory.Abelian.FunctorCategory
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
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]



noncomputable def reducedFaceFamilyPersistence (rank : V ↪ ℕ)
    (A : ℝ → Complex V) (hA : Monotone (fun t => (A t).faces)) (r : ℤ) :
    OrderDual ℝ ⥤ ModuleCat.{u} k where
  obj t := reducedFaceCohomology k rank (A (OrderDual.ofDual t)) r
  map {s t} h := reducedFaceCohomologyRestriction k rank
    (hA (show OrderDual.ofDual t ≤ OrderDual.ofDual s from leOfHom h)) r
  map_id t := reducedFaceCohomologyRestriction_refl k rank _ r
  map_comp hst htu := (reducedFaceCohomologyRestriction_comp k rank _ _ r).symm

noncomputable def relativeFacePersistence (rank : V ↪ ℕ)
    (A B : ℝ → Complex V) (hA : Monotone (fun t => (A t).faces))
    (hB : Monotone (fun t => (B t).faces)) (h : ∀ t, (B t).faces ⊆ (A t).faces) (r : ℤ) :
    OrderDual ℝ ⥤ ModuleCat.{u} k where
  obj t := relativeFaceCohomology k rank (h (OrderDual.ofDual t)) r
  map {s t} f := relativeFaceCohomologyRestriction k rank (h (OrderDual.ofDual t))
    (h (OrderDual.ofDual s))
    (hB (show OrderDual.ofDual t ≤ OrderDual.ofDual s from leOfHom f))
    (hA (show OrderDual.ofDual t ≤ OrderDual.ofDual s from leOfHom f)) r
  map_id t := relativeFaceCohomologyRestriction_refl k rank _ r
  map_comp hst htu := (relativeFaceCohomologyRestriction_comp k rank _ _ _ _ _ _ _ r).symm

noncomputable def relativeToAbsoluteTransformation (rank : V ↪ ℕ)
    (A B : ℝ → Complex V) (hA : Monotone (fun t => (A t).faces))
    (hB : Monotone (fun t => (B t).faces)) (h : ∀ t, (B t).faces ⊆ (A t).faces) (r : ℤ) :
    relativeFacePersistence k rank A B hA hB h r ⟶ reducedFaceFamilyPersistence k rank A hA r where
  app t := relativeFaceCohomologyToAbsolute k rank (h (OrderDual.ofDual t)) r
  naturality s t f := relativeFaceCohomologyToAbsolute_naturality k rank _ _ _ _ r

noncomputable def pairRestrictionTransformation (rank : V ↪ ℕ)
    (A B : ℝ → Complex V) (hA : Monotone (fun t => (A t).faces))
    (hB : Monotone (fun t => (B t).faces)) (h : ∀ t, (B t).faces ⊆ (A t).faces) (r : ℤ) :
    reducedFaceFamilyPersistence k rank A hA r ⟶ reducedFaceFamilyPersistence k rank B hB r where
  app t := reducedFaceCohomologyRestriction k rank (h (OrderDual.ofDual t)) r
  naturality s t f := by
    change reducedFaceCohomologyRestriction k rank _ r ≫ reducedFaceCohomologyRestriction k rank _ r =
      reducedFaceCohomologyRestriction k rank _ r ≫ reducedFaceCohomologyRestriction k rank _ r
    rw [reducedFaceCohomologyRestriction_comp, reducedFaceCohomologyRestriction_comp]

noncomputable def relativeConnectingTransformation (rank : V ↪ ℕ)
    (A B : ℝ → Complex V) (hA : Monotone (fun t => (A t).faces))
    (hB : Monotone (fun t => (B t).faces)) (h : ∀ t, (B t).faces ⊆ (A t).faces) (r : ℤ) :
    reducedFaceFamilyPersistence k rank B hB r ⟶ relativeFacePersistence k rank A B hA hB h (r + 1) where
  app t := relativeFaceConnecting k rank (h (OrderDual.ofDual t)) r
  naturality s t f := (relativeFaceConnecting_naturality k rank _ _ _ _ r).symm

theorem relativeToAbsolute_pairRestriction_zero (rank : V ↪ ℕ)
    (A B : ℝ → Complex V) (hA : Monotone (fun t => (A t).faces))
    (hB : Monotone (fun t => (B t).faces)) (h : ∀ t, (B t).faces ⊆ (A t).faces) (r : ℤ) :
    relativeToAbsoluteTransformation k rank A B hA hB h r ≫
      pairRestrictionTransformation k rank A B hA hB h r = 0 := by
  apply NatTrans.ext
  funext t
  exact relativeFaceCohomologyToAbsolute_restriction_zero k rank (h (OrderDual.ofDual t)) r

theorem pairRestriction_relativeConnecting_zero (rank : V ↪ ℕ)
    (A B : ℝ → Complex V) (hA : Monotone (fun t => (A t).faces))
    (hB : Monotone (fun t => (B t).faces)) (h : ∀ t, (B t).faces ⊆ (A t).faces) (r : ℤ) :
    pairRestrictionTransformation k rank A B hA hB h r ≫
      relativeConnectingTransformation k rank A B hA hB h r = 0 := by
  apply NatTrans.ext
  funext t
  exact relativeFaceRestriction_connecting_zero k rank (h (OrderDual.ofDual t)) r

theorem relativeConnecting_toAbsolute_zero (rank : V ↪ ℕ)
    (A B : ℝ → Complex V) (hA : Monotone (fun t => (A t).faces))
    (hB : Monotone (fun t => (B t).faces)) (h : ∀ t, (B t).faces ⊆ (A t).faces) (r : ℤ) :
    relativeConnectingTransformation k rank A B hA hB h r ≫
      relativeToAbsoluteTransformation k rank A B hA hB h (r + 1) = 0 := by
  apply NatTrans.ext
  funext t
  exact relativeFaceConnecting_toAbsolute_zero k rank (h (OrderDual.ofDual t)) r







end LPCA


