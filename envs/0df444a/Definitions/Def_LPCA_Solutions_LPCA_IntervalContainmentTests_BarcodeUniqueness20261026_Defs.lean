-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_IntervalContainmentTests_BarcodeUniqueness20261026_Defs
-- name    : LPCA_Solutions_LPCA_IntervalContainmentTests_BarcodeUniqueness20261026_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T05:40:20.022982+00:00
-- url     : https://prove2.me/theorems/3c3a63e9-3e17-4b84-854e-666a02333208
-- title:
--   Interval Containment Tests — finite barcode uniqueness dependencies
-- statement:
--   Selected constructions and proved compatibility results for interval containment tests, used in finite real-interval barcode uniqueness for the original homogeneous Ext persistence. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   Nonempty real intervals; zero summands are excluded for literal uniqueness.
--
--   Finite convex families admit test points detecting all containments.
--
--   Finite cumulative upper sums determine their individual multiplicities.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Theorem3.10, uniqueness of its finite interval decomposition, with formalization dependencies. Certified Lean source: Solutions/LPCA_IntervalContainmentTests.lean, selected declarations in lines 9–72; source SHA-256 ee2488a2030b5ebc5de035d17308df272bf3a755a219c203d4d7c0cc09694cac; exact-source certificate Sapelo2 job 49315795.

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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.UpperLower.CompleteLattice
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
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CriticalIntervalDecomposition_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DiagramSplitKernel_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFiniteLevels_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteCochainHomology_CriticalModel20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteCriticalSkeleton_CriticalModel20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteIntervalDecomposition_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteIntervalSummand_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterActualComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCohomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterIncidence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterLinkTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterNonfaceVanishing_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterSigns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_LinkIdentities_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_OrderedIntervalSplitting_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PersistenceIntervalExistence_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs

set_option autoImplicit false

namespace LPCA

/-- Nonempty real intervals; zero summands are excluded for literal uniqueness. -/
abbrev NonemptyRealInterval := {J : Set ℝ // IsTimeInterval J ∧ J.Nonempty}

/-- Finite cumulative upper sums determine their individual multiplicities. -/
theorem finite_upper_sums_injective {α : Type*} [PartialOrder α] [Fintype α] [DecidableLE α]
    (f g : α → ℕ)
    (h : ∀ x, (∑ y ∈ Finset.univ.filter (fun y => x ≤ y), f y) =
      ∑ y ∈ Finset.univ.filter (fun y => x ≤ y), g y) : f = g := by
  classical
  funext x
  induction x using WellFoundedGT.induction with
  | ind x ih =>
    let S : Finset α := Finset.univ.filter (fun y => x ≤ y)
    have hx : x ∈ S := by simp [S]
    have he : (∑ y ∈ S.erase x, f y) = ∑ y ∈ S.erase x, g y := by
      apply Finset.sum_congr rfl
      intro y hy
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hy
      have hxy : x ≤ y := (Finset.mem_filter.mp hmem).2
      exact ih y (lt_of_le_of_ne hxy hne.symm)
    have hh := h x
    change (∑ y ∈ S, f y) = ∑ y ∈ S, g y at hh
    rw [← Finset.sum_erase_add _ _ hx, ← Finset.sum_erase_add _ _ hx, he] at hh
    exact Nat.add_left_cancel hh

/-- Finite convex families admit test points detecting all containments. -/
theorem finite_interval_containment_tests (A : Finset NonemptyRealInterval)
    (J : NonemptyRealInterval) :
    ∃ a b : ℝ, a ≤ b ∧ a ∈ J.1 ∧ b ∈ J.1 ∧
      ∀ I ∈ A, (a ∈ I.1 ∧ b ∈ I.1) ↔ J.1 ⊆ I.1 := by
  classical
  obtain ⟨c, hc⟩ := J.2.2
  have hwitness : ∀ I : {I : NonemptyRealInterval // I ∈ A},
      ∃ x : ℝ, x ∈ J.1 ∧ (¬ J.1 ⊆ I.1.1 → x ∉ I.1.1) := by
    intro I
    by_cases hJI : J.1 ⊆ I.1.1
    · exact ⟨c, hc, fun h => (h hJI).elim⟩
    · have hn := hJI
      simp only [Set.subset_def, not_forall, _root_.not_imp] at hn
      obtain ⟨x, hxJ, hxI⟩ := hn
      exact ⟨x, hxJ, fun _ => hxI⟩
  choose w hw using hwitness
  let S : Finset ℝ := insert c (A.attach.image w)
  have hS : S.Nonempty := ⟨c, by simp [S]⟩
  have hSJ : ∀ x ∈ S, x ∈ J.1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hc
    · obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hx
      exact (hw I).1
  refine ⟨S.min' hS, S.max' hS, S.min'_le_max' hS,
    hSJ _ (S.min'_mem hS), hSJ _ (S.max'_mem hS), ?_⟩
  intro I hIA
  constructor
  · rintro ⟨haI, hbI⟩
    by_contra hJI
    have hwS : w ⟨I, hIA⟩ ∈ S := by
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨⟨I, hIA⟩, by simp, rfl⟩)
    have hwI : w ⟨I, hIA⟩ ∈ I.1 := I.2.1
      (S.min'_le _ hwS) (S.le_max' _ hwS) haI hbI
    exact (hw ⟨I, hIA⟩).2 hJI hwI
  · intro hJI
    exact ⟨hJI (hSJ _ (S.min'_mem hS)), hJI (hSJ _ (S.max'_mem hS))⟩

end LPCA


