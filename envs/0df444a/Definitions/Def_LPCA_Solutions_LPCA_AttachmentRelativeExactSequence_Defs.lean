-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_AttachmentRelativeExactSequence_Defs
-- name    : LPCA_Solutions_LPCA_AttachmentRelativeExactSequence_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T01:09:50.058315+00:00
-- url     : https://prove2.me/theorems/ad95039b-24f8-4b86-8568-049ccee3cff0
-- title:
--   Relative exact-sequence maps on original attachment pieces
-- statement:
--   This bundle supplies relative exact-sequence maps on original attachment pieces. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The relative-to-deletion arrow uses the inverse of the same fixed Hochster chart.
--   - Only the arithmetic degree label is transported: q+1-|sigma|-1 equals r+1.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_AttachmentRelativeExactSequence.lean, selected declarations in lines 17–152; source SHA-256 05014f3e748ba5f88f93f1f83454c8531b526e9f7ed05416a5e8c6f7554fe5e9; source certificate Sapelo2 job 49172236.

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
import Mathlib.Algebra.Homology.ShortComplex.Exact
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
import Mathlib.CategoryTheory.Abelian.FunctorCategory
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
import Definitions.Def_LPCA_Solutions_LPCA_AttachmentRelativePersistence_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactnessThroughIsomorphisms_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexAttachmentNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexHochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexPiecePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

noncomputable def attachmentRelativeToReducedDeletion (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (r : ℤ) :
    attachmentRelativePersistence k rank K f hf i σ r ⟶
      vertexDeletionReducedPersistence k rank K f hf i σ r :=
  relativeToAbsoluteTransformation k ((complementEmbedding i).trans rank)
    (attachmentDeletionLinkFamily K f hf i σ) (attachmentLinkLinkFamily K f hf i σ)
    (attachmentDeletionLinkFamily_mono K f hf i σ) (attachmentLinkLinkFamily_mono K f hf i σ)
    (attachmentLinkPair_subset K f hf i σ) r

noncomputable def attachmentReducedRestriction (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (r : ℤ) :
    vertexDeletionReducedPersistence k rank K f hf i σ r ⟶
      vertexLinkReducedPersistence k rank K f hf i σ r :=
  pairRestrictionTransformation k ((complementEmbedding i).trans rank)
    (attachmentDeletionLinkFamily K f hf i σ) (attachmentLinkLinkFamily K f hf i σ)
    (attachmentDeletionLinkFamily_mono K f hf i σ) (attachmentLinkLinkFamily_mono K f hf i σ)
    (attachmentLinkPair_subset K f hf i σ) r

noncomputable def attachmentReducedLinkToRelativeNext (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (r : ℤ) :
    vertexLinkReducedPersistence k rank K f hf i σ r ⟶
      attachmentRelativePersistence k rank K f hf i σ (r + 1) :=
  relativeConnectingTransformation k ((complementEmbedding i).trans rank)
    (attachmentDeletionLinkFamily K f hf i σ) (attachmentLinkLinkFamily K f hf i σ)
    (attachmentDeletionLinkFamily_mono K f hf i σ) (attachmentLinkLinkFamily_mono K f hf i σ)
    (attachmentLinkPair_subset K f hf i σ) r

theorem attachmentReduced_before_zero (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (r : ℤ) :
    attachmentRelativeToReducedDeletion k rank K f hf i σ r ≫
      attachmentReducedRestriction k rank K f hf i σ r = 0 :=
  relativeToAbsolute_pairRestriction_zero k ((complementEmbedding i).trans rank)
    _ _ _ _ (attachmentLinkPair_subset K f hf i σ) r

theorem attachmentReduced_after_zero (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (r : ℤ) :
    attachmentReducedRestriction k rank K f hf i σ r ≫
      attachmentReducedLinkToRelativeNext k rank K f hf i σ r = 0 :=
  pairRestriction_relativeConnecting_zero k ((complementEmbedding i).trans rank)
    _ _ _ _ (attachmentLinkPair_subset K f hf i σ) r

theorem attachmentReduced_next_zero (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (r : ℤ) :
    attachmentReducedLinkToRelativeNext k rank K f hf i σ r ≫
      attachmentRelativeToReducedDeletion k rank K f hf i σ (r + 1) = 0 :=
  relativeConnecting_toAbsolute_zero k ((complementEmbedding i).trans rank)
    _ _ _ _ (attachmentLinkPair_subset K f hf i σ) r

/-- The relative-to-deletion arrow uses the inverse of the same fixed Hochster chart. -/
noncomputable def attachmentRelativeToDeletion (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    attachmentRelativePersistence k rank K f hf i (negativeSupport b)
        ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) ⟶
      vertexDeletionPiecePersistence k rank K f hf i b q :=
  attachmentRelativeToReducedDeletion k rank K f hf i (negativeSupport b)
      ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) ≫
    (vertexDeletionHochsterPersistenceIso k rank K f hf i b q hb).inv

noncomputable def attachmentLinkToRelativeNext (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    vertexLinkPiecePersistence k rank K f hf i b q ⟶
      attachmentRelativePersistence k rank K f hf i (negativeSupport b)
        (((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) + 1) :=
  (vertexLinkHochsterPersistenceIso k rank K f hf i b q hb).hom ≫
    attachmentReducedLinkToRelativeNext k rank K f hf i (negativeSupport b)
      ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1)

/-- Only the arithmetic degree label is transported: q+1-|sigma|-1 equals r+1. -/
noncomputable def attachmentDeletionNextHochsterIso (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    vertexDeletionPiecePersistence k rank K f hf i b (q + 1) ≅
      vertexDeletionReducedPersistence k rank K f hf i (negativeSupport b)
        (((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) + 1) :=
  vertexDeletionHochsterPersistenceIso k rank K f hf i b (q + 1) hb ≪≫
    eqToIso (congrArg (fun r => vertexDeletionReducedPersistence k rank K f hf i
      (negativeSupport b) r) (by omega))

noncomputable def attachmentRelativeNextToDeletionNext (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    attachmentRelativePersistence k rank K f hf i (negativeSupport b)
        (((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) + 1) ⟶
      vertexDeletionPiecePersistence k rank K f hf i b (q + 1) :=
  attachmentRelativeToReducedDeletion k rank K f hf i (negativeSupport b)
      (((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) + 1) ≫
    (attachmentDeletionNextHochsterIso k rank K f hf i b q hb).inv

theorem attachmentRelativeToDeletion_rho_zero (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    attachmentRelativeToDeletion k rank K f hf i b q hb ≫
      vertexAttachmentPieceTransformation k rank K f hf i b q = 0 := by
  apply shortComplexIso_zero _ _
    (attachmentReduced_before_zero k rank K f hf i (negativeSupport b)
      ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1))
    (Iso.refl _) (vertexDeletionHochsterPersistenceIso k rank K f hf i b q hb)
    (vertexLinkHochsterPersistenceIso k rank K f hf i b q hb)
  · simp only [attachmentRelativeToDeletion, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.refl_hom, Category.id_comp]
  · exact vertexAttachmentPieceTransformation_hochster k rank K f hf i b q hb

theorem attachmentRho_linkToRelative_zero (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    vertexAttachmentPieceTransformation k rank K f hf i b q ≫
      attachmentLinkToRelativeNext k rank K f hf i b q hb = 0 := by
  apply shortComplexIso_zero _ _
    (attachmentReduced_after_zero k rank K f hf i (negativeSupport b)
      ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1))
    (vertexDeletionHochsterPersistenceIso k rank K f hf i b q hb)
    (vertexLinkHochsterPersistenceIso k rank K f hf i b q hb) (Iso.refl _)
  · exact vertexAttachmentPieceTransformation_hochster k rank K f hf i b q hb
  · simp only [attachmentLinkToRelativeNext, Iso.refl_hom, Category.comp_id]

theorem attachmentLinkToRelative_next_zero (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    attachmentLinkToRelativeNext k rank K f hf i b q hb ≫
      attachmentRelativeNextToDeletionNext k rank K f hf i b q hb = 0 := by
  apply shortComplexIso_zero _ _
    (attachmentReduced_next_zero k rank K f hf i (negativeSupport b)
      ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1))
    (vertexLinkHochsterPersistenceIso k rank K f hf i b q hb) (Iso.refl _)
    (attachmentDeletionNextHochsterIso k rank K f hf i b q hb)
  · simp only [attachmentLinkToRelativeNext, Iso.refl_hom, Category.comp_id]
  · simp only [attachmentRelativeNextToDeletionNext, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Iso.refl_hom, Category.id_comp]







end LPCA


