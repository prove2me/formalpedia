-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_NegativeOnePersistence_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_NegativeOnePersistence_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:48:08.250518+00:00
-- url     : https://prove2.me/theorems/8ef322a8-2186-4775-ad94-8e3ecda0ee5f
-- title:
--   Negative One Persistence — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for negative one persistence, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   Corollary 6.4 for the unchanged original Ext homogeneous piece and
--   every one of its actual quotient-induced persistence maps.
--
--   Corollary 6.4 on the paper's actual labelled reduced-link functor.
--
--   The entire reduced degree minus-one diagram, with its ordinary
--   restriction maps, is one actual interval module (possibly zero).
--
--   The endpoint formula for the actual cohomology of any restricted link.
--   It includes absent faces, infinite right endpoints and zero-length intervals.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_NegativeOnePersistence.lean, selected declarations in lines 17–111; source SHA-256 fbb5977914606a9e5a787f149b4bf7958d9911e068067bd91ab797ffb4810371; exact-source certificate Sapelo2 job 49311470.

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
import Mathlib.Data.Finset.Lattice.Fold
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
import Mathlib.Order.WithBot
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
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingAction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_MinusOne20261025_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLinkIdentities_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLinkIdentities_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateBasis_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateBooleanDiagram_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCechComparison_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCechNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateComplementComparison_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateComplementComparison_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateComplementNaturality_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateLinkIdentity_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceCofaceIntervals_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceOffsetNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCoordinates_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FamilyHochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FamilyHochsterPersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_MinusOne20261025_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedNegativeOne_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexAttachmentNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexDegreeIndices_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexHochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexHochsterPersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexPiecePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexPiecePersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSupportPieces_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexTensorTarget_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

def emptyFaceOnlyTimes (F : ℝ → Complex V) : Set ℝ := {t | EmptyFaceOnly (F t)}

theorem emptyFaceOnlyTimes_isInterval (F : ℝ → Complex V)
    (hF : Monotone (fun t => (F t).faces)) : IsTimeInterval (emptyFaceOnlyTimes F) := by
  intro s t w hst htw hs hw
  change (F s).faces = {∅} at hs
  change (F w).faces = {∅} at hw
  change (F t).faces = {∅}
  exact Finset.Subset.antisymm (by simpa only [hw] using hF htw)
    (by simpa only [hs] using hF hst)

variable (k : Type u) [Field k]

/-- The entire reduced degree minus-one diagram, with its ordinary
restriction maps, is one actual interval module (possibly zero). -/
noncomputable def reducedNegativeOneFamilyIso (rank : V ↪ ℕ)
    (F : ℝ → Complex V) (hF : Monotone (fun t => (F t).faces)) :
    reducedFaceFamilyPersistence k rank F hF (-1) ≅
      intervalPersistence k (emptyFaceOnlyTimes F) (emptyFaceOnlyTimes_isInterval F hF) :=
  NatIso.ofComponents
    (fun t => reducedNegativeOneIndicatorIso k rank (F (OrderDual.ofDual t)))
    (fun h => reducedNegativeOneIndicatorIso_restriction k rank (hF (leOfHom h)))

noncomputable def reducedNegativeOneFamilyIsoTo (rank : V ↪ ℕ)
    (F : ℝ → Complex V) (hF : Monotone (fun t => (F t).faces))
    (J : Set ℝ) (hJ : IsTimeInterval J)
    (h : ∀ t, EmptyFaceOnly (F t) ↔ t ∈ J) :
    reducedFaceFamilyPersistence k rank F hF (-1) ≅ intervalPersistence k J hJ :=
  reducedNegativeOneFamilyIso k rank F hF ≪≫
    intervalPersistenceCongr k _ J _ hJ (Set.ext h)

variable {W : Type u} [DecidableEq W] [Fintype W]

noncomputable def restrictedLinkLevelFamily (K : Complex V) (f : Finset V → ℝ)
    (hf : FiltrationMonotone K f) (B : Finset V) (e : W ↪ V) : ℝ → Complex W :=
  fun t => restrictComplex (link (level K f hf t) B) e

theorem restrictedLinkLevelFamily_mono (K : Complex V) (f : Finset V → ℝ)
    (hf : FiltrationMonotone K f) (B : Finset V) (e : W ↪ V) :
    Monotone (fun t => (restrictedLinkLevelFamily K f hf B e t).faces) :=
  fun _s _t hst => restrictComplex_faces_mono (link_faces_mono
    (level_faces_mono K f hf hst) B) e

/-- The endpoint formula for the actual cohomology of any restricted link.
It includes absent faces, infinite right endpoints and zero-length intervals. -/
noncomputable def restrictedLinkNegativeOneIntervalIso (rank : W ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f)
    (B : Finset V) (e : W ↪ V) :
    reducedFaceFamilyPersistence k rank (restrictedLinkLevelFamily K f hf B e)
        (restrictedLinkLevelFamily_mono K f hf B e) (-1) ≅
      intervalPersistence k (faceCofaceInterval K f B (Finset.univ.map e))
        (faceCofaceInterval_isInterval K f B (Finset.univ.map e)) :=
  reducedNegativeOneFamilyIsoTo k rank _ _ _ _
    (emptyFaceOnly_restrict_link_level_iff K f hf B e)

/-- Corollary 6.4 on the paper's actual labelled reduced-link functor. -/
noncomputable def coordinateReducedNegativeOneIntervalIso (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f)
    (U A : Finset V) (σ : Finset {v : V // v ∉ U}) :
    coordinateReducedPersistence k rank K f hf U A σ (-1) ≅
      intervalPersistence k
        (faceCofaceInterval K f (A ∪ σ.map (coordinateComplementEmbedding U))
          (Finset.univ.map (coordinateComplementEmbedding U)))
        (faceCofaceInterval_isInterval K f
          (A ∪ σ.map (coordinateComplementEmbedding U))
          (Finset.univ.map (coordinateComplementEmbedding U))) :=
  restrictedLinkNegativeOneIntervalIso k ((coordinateComplementEmbedding U).trans rank)
    K f hf (A ∪ σ.map (coordinateComplementEmbedding U)) (coordinateComplementEmbedding U)

/-- Corollary 6.4 for the unchanged original Ext homogeneous piece and
every one of its actual quotient-induced persistence maps. -/
noncomputable def coordinateNegativeOneIntervalIso (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f)
    (U : Finset V) (a : V → ℤ)
    (ha : ∀ v ∈ U, 0 ≤ a v)
    (hb : positiveSupport (a ∘ coordinateComplementEmbedding U) = ∅) :
    supportCohomologyPiecePersistence k rank K f hf (coordinateCechSupport U) a
        (negativeSupport (a ∘ coordinateComplementEmbedding U)).card ≅
      intervalPersistence k
        (faceCofaceInterval K f
          (coordinatePositivePart U a ∪
            (negativeSupport (a ∘ coordinateComplementEmbedding U)).map
              (coordinateComplementEmbedding U))
          (Finset.univ.map (coordinateComplementEmbedding U)))
        (faceCofaceInterval_isInterval K f
          (coordinatePositivePart U a ∪
            (negativeSupport (a ∘ coordinateComplementEmbedding U)).map
              (coordinateComplementEmbedding U))
          (Finset.univ.map (coordinateComplementEmbedding U))) := by
  let σ := negativeSupport (a ∘ coordinateComplementEmbedding U)
  have hr : ((σ.card : ℕ) : ℤ) - (σ.card : ℤ) - 1 = -1 := by omega
  exact coordinateHochsterPersistenceIso k rank K f hf U a σ.card ha hb ≪≫
    eqToIso (congrArg (fun r => coordinateReducedPersistence k rank K f hf U
      (coordinatePositivePart U a) σ r) hr) ≪≫
    coordinateReducedNegativeOneIntervalIso k rank K f hf U (coordinatePositivePart U a) σ

end LPCA


