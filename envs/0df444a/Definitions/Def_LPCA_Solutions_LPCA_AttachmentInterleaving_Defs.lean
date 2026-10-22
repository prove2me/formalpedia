-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_AttachmentInterleaving_Defs
-- name    : LPCA_Solutions_LPCA_AttachmentInterleaving_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T01:09:41.420449+00:00
-- url     : https://prove2.me/theorems/734ce4ff-cb35-4c90-9fbd-8ff39e11d88b
-- title:
--   Original attachment-arrow and image interleaving constructions
-- statement:
--   This bundle supplies original attachment-arrow and image interleaving constructions. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The literal square of original deletion and link Ext-piece restrictions, commuting with the retained original attachment arrow.
--   - The original attachment transformation, expressed as its diagram of actual arrows and actual commuting restriction squares.
--   - Corollary 4.4's arrow interleaving: both sides of every shifted square are original Ext restrictions and the double-shift composites are the original deletion/link persistence squares. No finite-dimensionality is needed.
--   - Images of the actual attachment arrows inherit exactly the same interleaving constant. The modules here are the already fixed literal ranges.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_AttachmentInterleaving.lean, selected declarations in lines 18–109; source SHA-256 40e6b5fb801d662fa650d091aedcd66c4ab0e64f27a6c2fd8aab51408f58af47; source certificate Sapelo2 job 49172236.

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
import Mathlib.CategoryTheory.Comma.Arrow
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
import Mathlib.Order.ConditionallyCompleteLattice.Finset
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
import Definitions.Def_LPCA_Solutions_LPCA_ArrowRangeFunctor_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ComplexRestrictionInterleaving_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_InterleavedFiltrations_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ReversedInterleaving_Defs
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

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- The literal square of original deletion and link Ext-piece restrictions,
commuting with the retained original attachment arrow. -/
noncomputable def vertexAttachmentArrowRestriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) :
    Arrow.mk (vertexAttachmentPieceMap k rank L i b q) ⟶
      Arrow.mk (vertexAttachmentPieceMap k rank K i b q) :=
  Arrow.homMk
    (supportCohomologyPieceRestriction k ((complementEmbedding i).trans rank)
      (restrictComplex_faces_mono (deletion_faces_mono h i) (complementEmbedding i)) Finset.univ b q)
    (supportCohomologyPieceRestriction k ((complementEmbedding i).trans rank)
      (restrictComplex_faces_mono (link_faces_mono h {i}) (complementEmbedding i)) Finset.univ b q)
    (vertexAttachmentPieceMap_naturality k rank h i b q)

theorem vertexAttachmentArrowRestriction_refl (rank : V ↪ ℕ)
    (K : Complex V) (i : V) (b : {v : V // v ≠ i} → ℤ) (q : ℕ) :
    vertexAttachmentArrowRestriction k rank (Finset.Subset.refl K.faces) i b q =
      𝟙 (Arrow.mk (vertexAttachmentPieceMap k rank K i b q)) := by
  apply Arrow.hom_ext
  · exact supportCohomologyPieceRestriction_refl k ((complementEmbedding i).trans rank)
      _ Finset.univ b q
  · exact supportCohomologyPieceRestriction_refl k ((complementEmbedding i).trans rank)
      _ Finset.univ b q

theorem vertexAttachmentArrowRestriction_comp (rank : V ↪ ℕ)
    {K L N : Complex V} (hKL : K.faces ⊆ L.faces) (hLN : L.faces ⊆ N.faces)
    (i : V) (b : {v : V // v ≠ i} → ℤ) (q : ℕ) :
    vertexAttachmentArrowRestriction k rank hLN i b q ≫
        vertexAttachmentArrowRestriction k rank hKL i b q =
      vertexAttachmentArrowRestriction k rank (Finset.Subset.trans hKL hLN) i b q := by
  apply Arrow.hom_ext
  · exact supportCohomologyPieceRestriction_comp k ((complementEmbedding i).trans rank)
      _ _ Finset.univ b q
  · exact supportCohomologyPieceRestriction_comp k ((complementEmbedding i).trans rank)
      _ _ Finset.univ b q

/-- The original attachment transformation, expressed as its diagram of
actual arrows and actual commuting restriction squares. -/
noncomputable def vertexAttachmentArrowPersistence (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f)
    (i : V) (b : {v : V // v ≠ i} → ℤ) (q : ℕ) :
    OrderDual ℝ ⥤ Arrow (ModuleCat.{u} k) :=
  complexRestrictionPersistence (fun A => Arrow.mk (vertexAttachmentPieceMap k rank A i b q))
    (fun {_ _} h => vertexAttachmentArrowRestriction k rank h i b q)
    (fun A => vertexAttachmentArrowRestriction_refl k rank A i b q)
    (fun {_ _ _} h₁ h₂ => vertexAttachmentArrowRestriction_comp k rank h₁ h₂ i b q)
    (fun t => level K f hf t) (fun {_ _} h => level_faces_mono K f hf h)

theorem vertexAttachmentArrowPersistence_eq (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f)
    (i : V) (b : {v : V // v ≠ i} → ℤ) (q : ℕ) :
    vertexAttachmentArrowPersistence k rank K f hf i b q =
      arrowPersistence k (vertexAttachmentPieceTransformation k rank K f hf i b q) := by
  rfl

/-- Corollary 4.4's arrow interleaving: both sides of every shifted square
are original Ext restrictions and the double-shift composites are the original
deletion/link persistence squares. No finite-dimensionality is needed. -/
noncomputable def vertexAttachmentArrowInterleaving (rank : V ↪ ℕ)
    (K : Complex V) (f g : Finset V → ℝ)
    (hf : FiltrationMonotone K f) (hg : FiltrationMonotone K g)
    (i : V) (b : {v : V // v ≠ i} → ℤ) (q : ℕ) :
    ReversedInterleaving (vertexAttachmentArrowPersistence k rank K f hf i b q)
      (vertexAttachmentArrowPersistence k rank K g hg i b q) (filtrationDiscrepancy K f g) := by
  have hb : ∀ F ∈ K.faces, |g F - f F| ≤ filtrationDiscrepancy K f g := by
    intro F hF
    simpa only [abs_sub_comm] using abs_face_difference_le_discrepancy K f g F hF
  exact complexRestrictionInterleaving
    (fun A => Arrow.mk (vertexAttachmentPieceMap k rank A i b q))
    (fun {_ _} h => vertexAttachmentArrowRestriction k rank h i b q)
    (fun A => vertexAttachmentArrowRestriction_refl k rank A i b q)
    (fun {_ _ _} h₁ h₂ => vertexAttachmentArrowRestriction_comp k rank h₁ h₂ i b q)
    (fun t => level K f hf t) (fun t => level K g hg t)
    (fun {_ _} h => level_faces_mono K f hf h) (fun {_ _} h => level_faces_mono K g hg h)
    (filtrationDiscrepancy K f g) (filtrationDiscrepancy_nonneg K f g)
    (level_shift_subset_of_abs_le K f g hf hg _ (abs_face_difference_le_discrepancy K f g))
    (level_shift_subset_of_abs_le K g f hg hf _ hb)

/-- Images of the actual attachment arrows inherit exactly the same
interleaving constant. The modules here are the already fixed literal ranges. -/
noncomputable def vertexAttachmentImageInterleaving (rank : V ↪ ℕ)
    (K : Complex V) (f g : Finset V → ℝ)
    (hf : FiltrationMonotone K f) (hg : FiltrationMonotone K g)
    (i : V) (b : {v : V // v ≠ i} → ℤ) (q : ℕ) :
    ReversedInterleaving (vertexAttachmentImagePersistence k rank K f hf i b q)
      (vertexAttachmentImagePersistence k rank K g hg i b q) (filtrationDiscrepancy K f g) := by
  change ReversedInterleaving
    (imagePersistence k (vertexAttachmentPieceTransformation k rank K f hf i b q))
    (imagePersistence k (vertexAttachmentPieceTransformation k rank K g hg i b q))
    (filtrationDiscrepancy K f g)
  simpa only [vertexAttachmentArrowPersistence_eq, arrowPersistence_comp_rangeFunctor] using
    (vertexAttachmentArrowInterleaving k rank K f g hf hg i b q).map (moduleArrowRangeFunctor k)

end LPCA


