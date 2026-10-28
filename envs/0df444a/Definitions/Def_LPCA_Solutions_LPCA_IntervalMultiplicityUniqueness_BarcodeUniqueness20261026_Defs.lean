-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_IntervalMultiplicityUniqueness_BarcodeUniqueness20261026_Defs
-- name    : LPCA_Solutions_LPCA_IntervalMultiplicityUniqueness_BarcodeUniqueness20261026_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T05:43:47.270772+00:00
-- url     : https://prove2.me/theorems/39e46a47-6385-4203-ac46-bedd395c3e1f
-- title:
--   Interval Multiplicity Uniqueness — finite barcode uniqueness dependencies
-- statement:
--   Selected constructions and proved compatibility results for interval multiplicity uniqueness, used in finite real-interval barcode uniqueness for the original homogeneous Ext persistence. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   Naturally isomorphic finite sums of arbitrary nonempty real interval
--   modules have identical support multisets. Splitting maps need not be unique.
--
--   Equal two-point interval coverage determines arbitrary finite real
--   interval families up to permutation, not just critical-cut families.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Theorem3.10, uniqueness of its finite interval decomposition, with formalization dependencies. Certified Lean source: Solutions/LPCA_IntervalMultiplicityUniqueness.lean, selected declarations in lines 10–120; source SHA-256 3018af3b880d7f8d5b359c9f59427b1d3e057f72151e83214376a3899a820903; exact-source certificate Sapelo2 job 49315795.

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
import Mathlib.Data.List.Count
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
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
import Definitions.Def_LPCA_Solutions_LPCA_IntervalContainmentTests_BarcodeUniqueness20261026_Defs
import Definitions.Def_LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_IntervalRankInvariant_BarcodeUniqueness20261026_Defs
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

open CategoryTheory

noncomputable def realIntervalMultiplicity (js : List NonemptyRealInterval)
    (J : NonemptyRealInterval) : ℕ := by
  classical
  exact js.countP (fun I => decide (I = J))

theorem realIntervalMultiplicity_eq_count [BEq NonemptyRealInterval]
    [LawfulBEq NonemptyRealInterval] (js : List NonemptyRealInterval)
    (J : NonemptyRealInterval) : realIntervalMultiplicity js J = js.count J := by
  classical
  unfold realIntervalMultiplicity List.count
  apply congrArg (fun p : NonemptyRealInterval → Bool => js.countP p)
  funext I
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]

noncomputable def pairMultiplicitySum (A : Finset NonemptyRealInterval)
    (js : List NonemptyRealInterval) (a b : ℝ) : ℕ := by
  classical
  exact ∑ I ∈ A.filter (fun I => a ∈ I.1 ∧ b ∈ I.1), realIntervalMultiplicity js I

noncomputable def upperMultiplicitySum (A : Finset NonemptyRealInterval)
    (js : List NonemptyRealInterval) (J : NonemptyRealInterval) : ℕ := by
  classical
  exact ∑ I ∈ A.filter (fun I => J ≤ I), realIntervalMultiplicity js I

theorem intervalCoverage_eq_sum_multiplicity (A : Finset NonemptyRealInterval)
    (js : List NonemptyRealInterval) (hjs : ∀ I ∈ js, I ∈ A) (a b : ℝ) :
    realIntervalCoverage a b js = pairMultiplicitySum A js a b := by
  classical
  induction js with
  | nil => simp [realIntervalCoverage, pairMultiplicitySum, realIntervalMultiplicity]
  | cons J js ih =>
    have hJA : J ∈ A := hjs J (List.mem_cons_self)
    have htail : ∀ I ∈ js, I ∈ A := fun I hI => hjs I (List.mem_cons_of_mem _ hI)
    have hc : realIntervalCoverage a b (J :: js) =
        (if a ∈ J.1 ∧ b ∈ J.1 then 1 else 0) + realIntervalCoverage a b js := by
      by_cases hp : a ∈ J.1 ∧ b ∈ J.1 <;>
        simp [realIntervalCoverage, List.countP_cons, hp, Nat.add_comm]
    have hm : ∀ I, realIntervalMultiplicity (J :: js) I =
        (if J = I then 1 else 0) + realIntervalMultiplicity js I := by
      intro I
      by_cases hJI : J = I <;> simp [realIntervalMultiplicity, List.countP_cons, hJI, Nat.add_comm]
    rw [hc, ih htail]
    unfold pairMultiplicitySum
    simp_rw [hm]
    rw [Finset.sum_add_distrib]
    congr 1
    simp [eq_comm, hJA]

theorem finset_upper_sums_injective {α : Type*} [PartialOrder α] [DecidableEq α]
    [DecidableLE α] (A : Finset α) (f g : α → ℕ)
    (h : ∀ x ∈ A, (∑ y ∈ A.filter (fun y => x ≤ y), f y) =
      ∑ y ∈ A.filter (fun y => x ≤ y), g y) : ∀ x ∈ A, f x = g x := by
  classical
  have hh : (fun x : A => f x.1) = (fun x : A => g x.1) := by
    apply finite_upper_sums_injective
    intro x
    have hsum (r : α → ℕ) :
        (∑ y ∈ Finset.univ.filter (fun y : A => x ≤ y), r y.1) =
          ∑ y ∈ A.filter (fun y => x.1 ≤ y), r y := by
      rw [Finset.sum_filter, Finset.sum_filter]
      exact Finset.sum_coe_sort (s := A) (f := fun y : α => if x.1 ≤ y then r y else 0)
    exact (hsum f).trans ((h x.1 x.2).trans (hsum g).symm)
  intro x hx
  exact congrFun hh ⟨x, hx⟩

/-- Equal two-point interval coverage determines arbitrary finite real
interval families up to permutation, not just critical-cut families. -/
theorem realIntervalCoverage_unique (js ks : List NonemptyRealInterval)
    (h : ∀ a b : ℝ, a ≤ b → realIntervalCoverage a b js = realIntervalCoverage a b ks) :
    js.Perm ks := by
  classical
  let A : Finset NonemptyRealInterval := js.toFinset ∪ ks.toFinset
  have hjA : ∀ I ∈ js, I ∈ A := by intro I hI; simp [A, hI]
  have hkA : ∀ I ∈ ks, I ∈ A := by intro I hI; simp [A, hI]
  have hupper : ∀ J ∈ A, upperMultiplicitySum A js J = upperMultiplicitySum A ks J := by
    intro J hJA
    obtain ⟨a, b, hab, _, _, htest⟩ := finite_interval_containment_tests A J
    have hh := h a b hab
    rw [intervalCoverage_eq_sum_multiplicity A js hjA,
      intervalCoverage_eq_sum_multiplicity A ks hkA] at hh
    have hfilter : A.filter (fun I => a ∈ I.1 ∧ b ∈ I.1) =
        A.filter (fun I => J ≤ I) := by
      apply Finset.filter_congr
      intro I hI
      exact htest I hI
    simpa only [pairMultiplicitySum, upperMultiplicitySum, hfilter] using hh
  have hcounts : ∀ J ∈ A, realIntervalMultiplicity js J = realIntervalMultiplicity ks J := by
    apply finset_upper_sums_injective A
    intro J hJ
    exact hupper J hJ
  apply List.perm_iff_count.mpr
  intro J
  by_cases hJ : J ∈ A
  · exact (realIntervalMultiplicity_eq_count js J).symm.trans
      ((hcounts J hJ).trans (realIntervalMultiplicity_eq_count ks J))
  · have hj : J ∉ js := fun hmem => hJ (hjA J hmem)
    have hk : J ∉ ks := fun hmem => hJ (hkA J hmem)
    simp [List.count_eq_zero.mpr hj, List.count_eq_zero.mpr hk]

/-- Naturally isomorphic finite sums of arbitrary nonempty real interval
modules have identical support multisets. Splitting maps need not be unique. -/
theorem nonemptyRealIntervalSum_unique (k : Type*) [Field k]
    (js ks : List NonemptyRealInterval)
    (e : nonemptyRealIntervalSum k js ≅ nonemptyRealIntervalSum k ks) : js.Perm ks := by
  apply realIntervalCoverage_unique
  intro a b hab
  have hh := natIso_map_finrank_eq e (homOfLE
    (show OrderDual.toDual b ≤ OrderDual.toDual a from hab))
  simpa only [nonemptyRealIntervalSum_map_rank (k := k) js a b hab,
    nonemptyRealIntervalSum_map_rank (k := k) ks a b hab] using hh

end LPCA


