-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_AttachmentRelativeAmbient_Defs
-- name    : LPCA_Solutions_LPCA_AttachmentRelativeAmbient_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T01:11:34.089985+00:00
-- url     : https://prove2.me/theorems/3a44f472-fd05-4096-a064-6e7b47d050b0
-- title:
--   Ambient-labelled attachment pairs and their exact-sequence maps
-- statement:
--   This bundle supplies ambient-labelled attachment pairs and their exact-sequence maps. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Equality of both complex families changes only the labels of their actual relative-cohomology persistence diagram.
--   - Exactly the paper's ambient-labelled pair (A_i,sigma^t,B_i,sigma^t).
--   - A natural equivalence induced on the actual relative cochain kernels, followed only by the established deletion/link identities.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_AttachmentRelativeAmbient.lean, selected declarations in lines 18–145; source SHA-256 12bdb1b5416465167658635871a594e40448b808a9ccd305e25dc6eeec238311; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_AmbientHochsterRanks_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AttachmentRelativeExactSequence_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLinkIdentities_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_FaceLabelNaturality_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ImagePersistence_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceLabels_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexAttachmentImage_Defs
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

/-- Equality of both complex families changes only the labels of their actual
relative-cohomology persistence diagram. -/
noncomputable def relativeFacePersistence_congr (rank : V ↪ ℕ)
    (A B A' B' : ℝ → Complex V)
    (hA : Monotone (fun t => (A t).faces)) (hB : Monotone (fun t => (B t).faces))
    (h : ∀ t, (B t).faces ⊆ (A t).faces)
    (hA' : Monotone (fun t => (A' t).faces)) (hB' : Monotone (fun t => (B' t).faces))
    (h' : ∀ t, (B' t).faces ⊆ (A' t).faces)
    (hAA' : ∀ t, A t = A' t) (hBB' : ∀ t, B t = B' t) (r : ℤ) :
    relativeFacePersistence k rank A B hA hB h r ≅
      relativeFacePersistence k rank A' B' hA' hB' h' r := by
  have hAA : A = A' := funext hAA'
  have hBB : B = B' := funext hBB'
  subst A'
  subst B'
  exact Iso.refl _

noncomputable def attachmentAmbientDeletionFamily (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) : ℝ → Complex V :=
  fun t => deletion (link (level K f hf t) (σ.map (complementEmbedding i))) i

noncomputable def attachmentAmbientLinkFamily (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) : ℝ → Complex V :=
  fun t => link (level K f hf t) (σ.map (complementEmbedding i) ∪ {i})

theorem attachmentAmbientDeletionFamily_mono (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) :
    Monotone (fun t => (attachmentAmbientDeletionFamily K f hf i σ t).faces) :=
  fun _s _t h => deletion_faces_mono
    (link_faces_mono (level_faces_mono K f hf h) (σ.map (complementEmbedding i))) i

theorem attachmentAmbientLinkFamily_mono (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) :
    Monotone (fun t => (attachmentAmbientLinkFamily K f hf i σ t).faces) :=
  fun _s _t h => link_faces_mono (level_faces_mono K f hf h)
    (σ.map (complementEmbedding i) ∪ {i})

theorem attachmentAmbientPair_subset (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (t : ℝ) :
    (attachmentAmbientLinkFamily K f hf i σ t).faces ⊆
      (attachmentAmbientDeletionFamily K f hf i σ t).faces :=
  attachmentCrossAmbientInclusion K f hf i σ t t (le_refl t)

/-- Exactly the paper's ambient-labelled pair (A_i,sigma^t,B_i,sigma^t). -/
noncomputable def attachmentAmbientRelativePersistence (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (r : ℤ) : OrderDual ℝ ⥤ ModuleCat.{u} k :=
  relativeFacePersistence k rank
    (attachmentAmbientDeletionFamily K f hf i σ) (attachmentAmbientLinkFamily K f hf i σ)
    (attachmentAmbientDeletionFamily_mono K f hf i σ) (attachmentAmbientLinkFamily_mono K f hf i σ)
    (attachmentAmbientPair_subset K f hf i σ) r

/-- A natural equivalence induced on the actual relative cochain kernels,
followed only by the established deletion/link identities. -/
noncomputable def attachmentRelativeAmbientPersistenceIso (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (r : ℤ) :
    attachmentAmbientRelativePersistence k rank K f hf i σ r ≅
      attachmentRelativePersistence k rank K f hf i σ r :=
  relativeFaceLabelPersistenceIso k rank
    (attachmentAmbientDeletionFamily K f hf i σ) (attachmentAmbientLinkFamily K f hf i σ)
    (attachmentAmbientDeletionFamily_mono K f hf i σ) (attachmentAmbientLinkFamily_mono K f hf i σ)
    (attachmentAmbientPair_subset K f hf i σ) (complementEmbedding i)
    (fun t => link_union_singleton_faces_in_complement (level K f hf t) i (σ.map (complementEmbedding i)))
    (fun _t => deletion_faces_in_complement _ i) r ≪≫
  relativeFacePersistence_congr k ((complementEmbedding i).trans rank)
    _ _ _ _ _ _ _ _ _ _
    (fun t => (link_deletion_complement (level K f hf t) i σ).symm)
    (fun t => (link_link_complement (level K f hf t) i σ).symm) r

noncomputable def attachmentAmbientRelativeToDeletion (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    attachmentAmbientRelativePersistence k rank K f hf i (negativeSupport b)
        ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) ⟶
      vertexDeletionPiecePersistence k rank K f hf i b q :=
  (attachmentRelativeAmbientPersistenceIso k rank K f hf i (negativeSupport b)
      ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1)).hom ≫
    attachmentRelativeToDeletion k rank K f hf i b q hb

noncomputable def attachmentLinkToAmbientRelativeNext (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    vertexLinkPiecePersistence k rank K f hf i b q ⟶
      attachmentAmbientRelativePersistence k rank K f hf i (negativeSupport b)
        (((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) + 1) :=
  attachmentLinkToRelativeNext k rank K f hf i b q hb ≫
    (attachmentRelativeAmbientPersistenceIso k rank K f hf i (negativeSupport b)
      (((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) + 1)).inv

noncomputable def attachmentAmbientRelativeNextToDeletionNext (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    attachmentAmbientRelativePersistence k rank K f hf i (negativeSupport b)
        (((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) + 1) ⟶
      vertexDeletionPiecePersistence k rank K f hf i b (q + 1) :=
  (attachmentRelativeAmbientPersistenceIso k rank K f hf i (negativeSupport b)
      (((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) + 1)).hom ≫
    attachmentRelativeNextToDeletionNext k rank K f hf i b q hb

theorem attachmentAmbient_before_zero (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    attachmentAmbientRelativeToDeletion k rank K f hf i b q hb ≫
      vertexAttachmentPieceTransformation k rank K f hf i b q = 0 := by
  rw [attachmentAmbientRelativeToDeletion, Category.assoc,
    attachmentRelativeToDeletion_rho_zero, comp_zero]

theorem attachmentAmbient_after_zero (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    vertexAttachmentPieceTransformation k rank K f hf i b q ≫
      attachmentLinkToAmbientRelativeNext k rank K f hf i b q hb = 0 := by
  rw [attachmentLinkToAmbientRelativeNext, ← Category.assoc,
    attachmentRho_linkToRelative_zero, zero_comp]

theorem attachmentAmbient_next_zero (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    attachmentLinkToAmbientRelativeNext k rank K f hf i b q hb ≫
      attachmentAmbientRelativeNextToDeletionNext k rank K f hf i b q hb = 0 := by
  simp only [attachmentLinkToAmbientRelativeNext, attachmentAmbientRelativeNextToDeletionNext,
    Category.assoc, Iso.inv_hom_id_assoc, attachmentLinkToRelative_next_zero]







end LPCA


