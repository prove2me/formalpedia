-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinateBasis_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_CoordinateBasis_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:16:03.277536+00:00
-- url     : https://prove2.me/theorems/59101cd7-3f17-4330-a5ee-682d9b5d4def
-- title:
--   Coordinate Basis — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for coordinate basis used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   The basis map retains the exact localization index F, hence its
--   orientation and its incidence coefficients.
--
--   The localization criterion for arbitrary coordinate support, with
--   all uninverted exponents retained until they are proved nonnegative.
--   Removing those exponents leaves exactly Gamma_(positive support).
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_CoordinateBasis.lean, selected declarations in lines 12–114; source SHA-256 d2fb9ee6063c2d42683fed5eb5d28341fee7c965b25cb76ef4341e86eebda275; exact-source certificate Sapelo2 job 49296539.

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
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Ideal
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
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingAction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableMaps_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingAction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateBooleanDiagram_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceOffsetNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCoordinates_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FamilyHochsterPersistence_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_HochsterPersistence_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexAttachmentNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexHochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexPiecePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexTensorTarget_SixOne20261024_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

def eraseCoordinateDegree (U : Finset V) (a : V → ℤ) : V → ℤ :=
  fun v => if v ∈ U then 0 else a v

def coordinatePositivePart (U : Finset V) (a : V → ℤ) : Finset V :=
  U.filter (fun v => 0 < a v)

theorem positiveSupport_eraseCoordinateDegree_union (U : Finset V) (a : V → ℤ) :
    positiveSupport a = positiveSupport (eraseCoordinateDegree U a) ∪ coordinatePositivePart U a := by
  ext v
  simp only [positiveSupport, coordinatePositivePart, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hv : v ∈ U <;> simp [eraseCoordinateDegree, hv]

theorem positiveSupport_eraseCoordinateDegree_disjoint (U : Finset V) (a : V → ℤ) :
    Disjoint (positiveSupport (eraseCoordinateDegree U a)) U := by
  apply Finset.disjoint_left.mpr
  intro v hv hvU
  have hp : 0 < eraseCoordinateDegree U a v := (Finset.mem_filter.mp hv).2
  simp [eraseCoordinateDegree, hvU] at hp

theorem eraseCoordinateDegree_complement (U : Finset V) (a : V → ℤ) :
    eraseCoordinateDegree U a ∘ coordinateComplementEmbedding U = a ∘ coordinateComplementEmbedding U := by
  funext v
  exact if_neg v.property

theorem eraseCoordinateDegree_zero_outside_complement (U : Finset V) (a : V → ℤ) :
    ∀ v, v ∉ Set.range (coordinateComplementEmbedding U) → eraseCoordinateDegree U a v = 0 := by
  intro v hv
  have hvU : v ∈ U := by
    by_contra h
    exact hv ⟨⟨v, h⟩, rfl⟩
  exact if_pos hvU

/-- The localization criterion for arbitrary coordinate support, with
all uninverted exponents retained until they are proved nonnegative.
Removing those exponents leaves exactly Gamma_(positive support). -/
theorem criterion_coordinate_degree (K : Complex V) (U T F : Finset V) (a : V → ℤ)
    (hTU : Disjoint T U) (hFT : F ⊆ T) (ha : ∀ v ∈ U, 0 ≤ a v) :
    LocalizationCriterion K F a ↔
      LocalizationCriterion (coordinateLink K U (coordinatePositivePart U a)) F
        (eraseCoordinateDegree U a) := by
  have hn : (∀ v, v ∉ F → 0 ≤ a v) ↔
      (∀ v, v ∉ F → 0 ≤ eraseCoordinateDegree U a v) := by
    constructor
    · intro h v hv
      by_cases hvU : v ∈ U
      · simp [eraseCoordinateDegree, hvU]
      · simpa only [eraseCoordinateDegree, if_neg hvU] using h v hv
    · intro h v hv
      by_cases hvU : v ∈ U
      · exact ha v hvU
      · simpa only [eraseCoordinateDegree, if_neg hvU] using h v hv
  have hd : Disjoint (positiveSupport (eraseCoordinateDegree U a) ∪ F) U :=
    Finset.disjoint_union_left.mpr
      ⟨positiveSupport_eraseCoordinateDegree_disjoint U a, hTU.mono_left hFT⟩
  have he : (positiveSupport (eraseCoordinateDegree U a) ∪ F) ∪ coordinatePositivePart U a =
      positiveSupport a ∪ F := by
    rw [positiveSupport_eraseCoordinateDegree_union U a]
    ac_rfl
  have hsub : positiveSupport (eraseCoordinateDegree U a) ∪ F ⊆ positiveSupport a ∪ F := by
    rw [positiveSupport_eraseCoordinateDegree_union U a]
    exact Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl F)
  constructor
  · rintro ⟨hnn, hf⟩
    refine ⟨hn.mp hnn, Finset.mem_filter.mpr ⟨K.down_closed hf hsub, hd, ?_⟩⟩
    rwa [he]
  · rintro ⟨hnn, hf⟩
    refine ⟨hn.mpr hnn, ?_⟩
    have hface := (Finset.mem_filter.mp hf).2.2
    rwa [he] at hface

/-- The basis map retains the exact localization index F, hence its
orientation and its incidence coefficients. -/
noncomputable def coordinateDegreeBasisEquiv (K : Complex V) (U T : Finset V)
    (a : V → ℤ) (p : ℕ) (hTU : Disjoint T U) (ha : ∀ v ∈ U, 0 ≤ a v) :
    CechBasis K T a p ≃
      CechBasis (coordinateLink K U (coordinatePositivePart U a)) T (eraseCoordinateDegree U a) p where
  toFun F := ⟨F.1, F.2.1, F.2.2.1, (criterion_coordinate_degree K U T F.1 a hTU F.2.1 ha).mp F.2.2.2⟩
  invFun F := ⟨F.1, F.2.1, F.2.2.1, (criterion_coordinate_degree K U T F.1 a hTU F.2.1 ha).mpr F.2.2.2⟩
  left_inv _F := Subtype.ext rfl
  right_inv _F := Subtype.ext rfl

variable (k : Type u) [Field k]

noncomputable def coordinateDegreeModelTermEquiv (K : Complex V) (U T : Finset V)
    (a : V → ℤ) (p : ℕ) (hTU : Disjoint T U) (ha : ∀ v ∈ U, 0 ≤ a v) :
    (CechBasis K T a p → k) ≃ₗ[k]
      (CechBasis (coordinateLink K U (coordinatePositivePart U a)) T (eraseCoordinateDegree U a) p → k) :=
  LinearEquiv.funCongrLeft k k (coordinateDegreeBasisEquiv K U T a p hTU ha).symm

theorem coordinateDegree_modelDifferential (coefficient : Finset V → Finset V → k)
    (K : Complex V) (U T : Finset V) (a : V → ℤ) (p : ℕ)
    (hTU : Disjoint T U) (ha : ∀ v ∈ U, 0 ≤ a v) (x : CechBasis K T a p → k) :
    coordinateDegreeModelTermEquiv k K U T a (p + 1) hTU ha
        (basisDifferential k coefficient K T a p x) =
      basisDifferential k coefficient (coordinateLink K U (coordinatePositivePart U a)) T
        (eraseCoordinateDegree U a) p (coordinateDegreeModelTermEquiv k K U T a p hTU ha x) := by
  ext G
  change (∑ F : CechBasis K T a p, coefficient F.1 G.1 * x F) =
    ∑ F : CechBasis (coordinateLink K U (coordinatePositivePart U a)) T (eraseCoordinateDegree U a) p,
      coefficient F.1 G.1 * x ((coordinateDegreeBasisEquiv K U T a p hTU ha).symm F)
  exact (Equiv.sum_comp (coordinateDegreeBasisEquiv K U T a p hTU ha).symm
    (fun F : CechBasis K T a p => coefficient F.1 G.1 * x F)).symm

end LPCA


