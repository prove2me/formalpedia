-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_AttachmentRelativePersistence_Defs
-- name    : LPCA_Solutions_LPCA_AttachmentRelativePersistence_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T01:07:49.029382+00:00
-- url     : https://prove2.me/theorems/e30fffe1-048b-4642-ac4d-4c7673473293
-- title:
--   Native attachment pairs and the Hochster restriction identity
-- statement:
--   This bundle supplies native attachment pairs and the Hochster restriction identity. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The larger member of the actual attachment pair, on the native complement vertices.
--   - Ordinary reduced-relative cohomology of that pair, with its actual pair restrictions.
--   - This is the already fixed deletion Hochster isomorphism, with the pair-family codomain.
--   - Equality of the actual rho arrow with ordinary pair restriction under the fixed Hochster charts, as natural transformations, not merely equality of image dimensions.
--
--   Headline result `LPCA.vertexAttachmentPieceTransformation_hochster`:
--
--   Let $k$ be a field, $V$ a finite vertex set with a fixed injective ordering rank, $K$ a finite downward-closed face family, and $f$ a face-monotone real filtration. Fix $i\in V$, $W=V\setminus\{i\}$, a nonpositive multidegree $b\in\mathbb Z^W$, and $q\in\mathbb N$. Set $\sigma=\{w:b_w<0\}$ and $r=q-|\sigma|-1$. Form the links of $\sigma$ in the deletion and link of $i$ at each filtration level, on their genuine $W$ vertex labels.
--
--   Under the fixed degree-$b$ Hochster isomorphisms, the original quotient-induced attachment natural transformation is exactly ordinary reduced-cohomology restriction:
--   $$\rho\,;\,H_L=H_D\,;\,\operatorname{res}.$$
--   Here $H_D,H_L$ identify the actual homogeneous Ext-colimit local-cohomology pieces with reduced degree-$r$ cohomology, and the semicolon denotes composition in traversal order. This is equality of natural transformations over $\mathbb R^{\mathrm{op}}$, retaining the actual maps and the inherited ordering orientation. Empty-face degree $-1$, $q=0$, ghost vertices, void complexes and nonface $\sigma$ are allowed.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 4, definition and naturality of the attachment transformation, equations rho-naturality and rho-natural-transformation; natural Hochster identification from the theorem Persistent links--Hochster formula (thm:persistent-hochster), together with the quotient-induced attachment map from Proposition 3.5. Certified Lean source: Solutions/LPCA_AttachmentRelativePersistence.lean, selected declarations in lines 17–94; source SHA-256 6b137a59edee11551f91e3dd56d1bd80cdc70c40b58aa130ac1e33317edb0353; source certificate Sapelo2 job 49172236.

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

/-- The larger member of the actual attachment pair, on the native complement vertices. -/
noncomputable def attachmentDeletionLinkFamily (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) : ℝ → Complex {v : V // v ≠ i} :=
  fun t => link (deletionComplementFamily K f hf i t) σ

noncomputable def attachmentLinkLinkFamily (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) : ℝ → Complex {v : V // v ≠ i} :=
  fun t => link (linkComplementFamily K f hf i t) σ

theorem attachmentDeletionLinkFamily_mono (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) :
    Monotone (fun t => (attachmentDeletionLinkFamily K f hf i σ t).faces) :=
  fun _s _t h => link_faces_mono (deletionComplementFamily_mono K f hf i h) σ

theorem attachmentLinkLinkFamily_mono (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) :
    Monotone (fun t => (attachmentLinkLinkFamily K f hf i σ t).faces) :=
  fun _s _t h => link_faces_mono (linkComplementFamily_mono K f hf i h) σ

theorem attachmentLinkPair_subset (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (t : ℝ) :
    (attachmentLinkLinkFamily K f hf i σ t).faces ⊆
      (attachmentDeletionLinkFamily K f hf i σ t).faces :=
  link_faces_mono (linkComplement_faces_subset_deletion (level K f hf t) i) σ

/-- Ordinary reduced-relative cohomology of that pair, with its actual pair restrictions. -/
noncomputable def attachmentRelativePersistence (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (σ : Finset {v : V // v ≠ i}) (r : ℤ) : OrderDual ℝ ⥤ ModuleCat.{u} k :=
  relativeFacePersistence k ((complementEmbedding i).trans rank)
    (attachmentDeletionLinkFamily K f hf i σ) (attachmentLinkLinkFamily K f hf i σ)
    (attachmentDeletionLinkFamily_mono K f hf i σ) (attachmentLinkLinkFamily_mono K f hf i σ)
    (attachmentLinkPair_subset K f hf i σ) r

/-- This is the already fixed deletion Hochster isomorphism, with the pair-family codomain. -/
noncomputable def attachmentDeletionHochsterIso (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    vertexDeletionPiecePersistence k rank K f hf i b q ≅
      reducedFaceFamilyPersistence k ((complementEmbedding i).trans rank)
        (attachmentDeletionLinkFamily K f hf i (negativeSupport b))
        (attachmentDeletionLinkFamily_mono K f hf i (negativeSupport b))
        ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) :=
  vertexDeletionHochsterPersistenceIso k rank K f hf i b q hb

noncomputable def attachmentLinkHochsterIso (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    vertexLinkPiecePersistence k rank K f hf i b q ≅
      reducedFaceFamilyPersistence k ((complementEmbedding i).trans rank)
        (attachmentLinkLinkFamily K f hf i (negativeSupport b))
        (attachmentLinkLinkFamily_mono K f hf i (negativeSupport b))
        ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) :=
  vertexLinkHochsterPersistenceIso k rank K f hf i b q hb

/-- Equality of the actual rho arrow with ordinary pair restriction under the fixed
Hochster charts, as natural transformations, not merely equality of image dimensions. -/
@[reassoc] theorem vertexAttachmentPieceTransformation_hochster (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    vertexAttachmentPieceTransformation k rank K f hf i b q ≫
        (attachmentLinkHochsterIso k rank K f hf i b q hb).hom =
      (attachmentDeletionHochsterIso k rank K f hf i b q hb).hom ≫
        pairRestrictionTransformation k ((complementEmbedding i).trans rank)
          (attachmentDeletionLinkFamily K f hf i (negativeSupport b))
          (attachmentLinkLinkFamily K f hf i (negativeSupport b))
          (attachmentDeletionLinkFamily_mono K f hf i (negativeSupport b))
          (attachmentLinkLinkFamily_mono K f hf i (negativeSupport b))
          (attachmentLinkPair_subset K f hf i (negativeSupport b))
          ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1) := by
  apply NatTrans.ext
  funext t
  exact vertexAttachmentPieceMap_hochster k rank (level K f hf (OrderDual.ofDual t)) i b q hb

end LPCA


