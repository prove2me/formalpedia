-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUChainNaturality_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_CoordinateFixedUChainNaturality_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T21:48:00.151435+00:00
-- url     : https://prove2.me/theorems/8fda18d7-607a-4967-bd66-2be17a754f49
-- title:
--   Coordinate Fixed UChain Naturality — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for coordinate fixed uchain naturality used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   The native chart commutes with the original quotient restriction maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_CoordinateFixedUChainNaturality.lean, selected declarations in lines 16–122; source SHA-256 d77f8063acfa8b720186a2a1c8436c4f038951a9935fbaea8f91de2dc3f8a72b; exact-source certificate Sapelo2 job 49296539.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
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
import Definitions.Def_LPCA_Solutions_LPCA_CategoryHomogeneousAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingAction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNativeAmbientFieldComplex_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNativeRestrictionLegs_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNativeTermFamilies_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNativeTermLegHom_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCechVariables_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateBasis_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateBooleanDiagram_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCechComparison_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCechNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateComplementComparison_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateComplementVariableAction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateDegreeAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateDegreeIndices_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateExtendedComplementAction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedExponentCechComplex_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedExponentDifferential_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedExponentVariables_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedSupportComparison_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUFieldComplex_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUFieldVariables_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUNativeChain_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUNativeComplexField_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUNativeComplex_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUNativeField_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUNativeTermIso_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUNativeTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedURangeVariables_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedURestrictions_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUTermChart_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUTermDifferentialLegs_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUTermDifferential_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateFixedUTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateNativeAmbientDifferential_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateNativeAmbientTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateNativeChainDegreeLegs_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateSupportAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumChartAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumChartHomExt_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumChartPieces_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumEmbedding_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumGeneratorEquations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumIndexedMap_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceOffsetNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCoordinates_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaithfulComparisonSquare_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FamilyHochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedPolynomialComplex_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedPolynomialFieldPieces_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedPolynomialModuleCat_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ModuleLinearMapSquare_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativeLegAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativeLegHomExt_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialFieldIsoUpgradeSquare_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialFieldIsoUpgrade_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialLinearity_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialStableSubmodule_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RestrictedSubmoduleFieldIso_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexAttachmentNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplementAction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexHochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexPiecePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexTensorTarget_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

noncomputable def coordinateFixedUFieldRestrictionHom (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (c : {v : V // v ∈ U} → ℤ) (p : ℕ) :
    ModuleCat.of k (coordinateFixedUTermPiece k L U c p) ⟶ ModuleCat.of k (coordinateFixedUTermPiece k K U c p) :=
  ModuleCat.ofHom (R := k)
    (X := ModuleCat.of k (coordinateFixedUTermPiece k L U c p))
    (Y := ModuleCat.of k (coordinateFixedUTermPiece k K U c p))
    (((cechNativeAmbientFieldRestrictionHom k h (coordinateCechSupport U) p).hom.comp
      (coordinateFixedUTermPiece k L U c p).subtype).codRestrict _
        (fun x => coordinateFixedUTermPiece_restriction k rank h U c p x.1 x.2))

theorem coordinateFixedUNativeFieldIso_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (c : {v : V // v ∈ U} → ℤ) (p : ℕ) :
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial {v : V // v ∉ U} k)).map
        (coordinateFixedUNativeRestrictionHom k rank h U c p) ≫ (coordinateFixedUNativeFieldIso k K U c p).hom =
      (coordinateFixedUNativeFieldIso k L U c p).hom ≫ coordinateFixedUFieldRestrictionHom k rank h U c p := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact moduleSquare_apply k _ _ _ _ _ _ _ _ (coordinateNativeAmbientFieldIso_restriction k h U p) x.1

theorem coordinateFixedUTermLeg_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (c : {v : V // v ∈ U} → ℤ) (p : ℕ)
    (b : {v : V // v ∉ U} → ℤ) :
    ModuleCat.ofHom (coordinateFixedUTermLeg k L U c p b) ≫ coordinateFixedUFieldRestrictionHom k rank h U c p =
      cechNativeTermRestrictionHom k rank h (coordinateCechSupport U) p (extendCoordinateDegree U c b) ≫
        ModuleCat.ofHom (coordinateFixedUTermLeg k K U c p b) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  change cechNativeAmbientFieldRestrictionHom k h (coordinateCechSupport U) p
      (coordinateFixedUTermLeg k L U c p b y).1 =
    (coordinateFixedUTermLeg k K U c p b
      (cechNativeTermRestrictionHom k rank h (coordinateCechSupport U) p (extendCoordinateDegree U c b) y)).1
  rw [coordinateFixedUTermLeg_val, coordinateFixedUTermLeg_val]
  exact moduleSquare_apply k _ _ _ _ _ _ _ _
    (cechNativeTermForgetHom_restriction k rank h (coordinateCechSupport U) p (extendCoordinateDegree U c b)) y

attribute [local irreducible] coordinateFixedUExponentTermEquiv coordinateFixedExponentTermIso

theorem coordinateFixedUExponentTermEquiv_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (c : {v : V // v ∈ U} → ℕ) (p : ℕ) :
    ModuleCat.ofHom (coordinateFixedUExponentTermEquiv k rank L U c p).toLinearMap ≫
        cechNativeAmbientFieldRestrictionHom k
          (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p =
      coordinateFixedUFieldRestrictionHom k rank h U (fun v => (c v : ℤ)) p ≫
        ModuleCat.ofHom (coordinateFixedUExponentTermEquiv k rank K U c p).toLinearMap := by
  classical
  apply directSumChartHom_ext k
    (fun b => cechNativeTermFamily k L (coordinateCechSupport U) p
      (extendCoordinateDegree U (fun v => (c v : ℤ)) b))
    (ModuleCat.of k (coordinateFixedUTermPiece k L U (fun v => (c v : ℤ)) p)) _
    (coordinateFixedUTermSumEquiv k L U (fun v => (c v : ℤ)) p)
  intro b
  exact (categoryHomogeneousAssembly
    (ModuleCat.ofHom (coordinateFixedUExponentTermEquiv k rank K U c p).toLinearMap)
    (ModuleCat.ofHom (coordinateFixedUExponentTermEquiv k rank L U c p).toLinearMap)
    (ModuleCat.ofHom (coordinateFixedUTermLeg k K U (fun v => (c v : ℤ)) p b))
    (ModuleCat.ofHom (coordinateFixedUTermLeg k L U (fun v => (c v : ℤ)) p b))
    (coordinateFixedUFieldRestrictionHom k rank h U (fun v => (c v : ℤ)) p)
    (cechNativeTermRestrictionHom k rank h (coordinateCechSupport U) p (extendCoordinateDegree U (fun v => (c v : ℤ)) b))
    (coordinateFixedExponentTermIso k rank K U c b p).hom
    (coordinateFixedExponentTermIso k rank L U c b p).hom
    (cechNativeTermForgetHom k (coordinateComplementComplex K U (coordinateExponentSupport U c)) Finset.univ p b)
    (cechNativeTermForgetHom k (coordinateComplementComplex L U (coordinateExponentSupport U c)) Finset.univ p b)
    (cechNativeTermRestrictionHom k ((coordinateComplementEmbedding U).trans rank)
      (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p b)
    (cechNativeAmbientFieldRestrictionHom k
      (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p)
    (coordinateFixedUTermLeg_restriction k rank h U (fun v => (c v : ℤ)) p b)
    (coordinateFixedUExponentTermHom_leg k rank K U c p b)
    (coordinateFixedUExponentTermHom_leg k rank L U c p b)
    (coordinateFixedExponentTermIso_restriction k rank h U c b p)
    (cechNativeTermForgetHom_restriction k ((coordinateComplementEmbedding U).trans rank)
      (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p b)).symm

/-- The native chart commutes with the original quotient restriction maps. -/
theorem coordinateFixedUExponentNativeTermIso_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (c : {v : V // v ∈ U} → ℕ) (p : ℕ) :
    (coordinateFixedUExponentNativeTermIso k rank L U c p).hom ≫
        ModuleCat.ofHom (ambientCechTermRestriction k
          (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p) =
      coordinateFixedUNativeRestrictionHom k rank h U (fun v => (c v : ℤ)) p ≫
        (coordinateFixedUExponentNativeTermIso k rank K U c p).hom :=
  faithfulComparisonSquare
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial {v : V // v ∉ U} k))
    (coordinateFixedUNativeFieldIso k L U (fun v => (c v : ℤ)) p)
    (coordinateFixedUNativeFieldIso k K U (fun v => (c v : ℤ)) p)
    (ambientCechTermFieldIso k (coordinateComplementComplex L U (coordinateExponentSupport U c)) Finset.univ p)
    (ambientCechTermFieldIso k (coordinateComplementComplex K U (coordinateExponentSupport U c)) Finset.univ p)
    (coordinateFixedUExponentNativeTermIso k rank L U c p).hom
    (coordinateFixedUExponentNativeTermIso k rank K U c p).hom
    (ModuleCat.ofHom (coordinateFixedUExponentTermEquiv k rank L U c p).toLinearMap)
    (ModuleCat.ofHom (coordinateFixedUExponentTermEquiv k rank K U c p).toLinearMap)
    (coordinateFixedUNativeRestrictionHom k rank h U (fun v => (c v : ℤ)) p)
    (ModuleCat.ofHom (ambientCechTermRestriction k
      (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p))
    (coordinateFixedUFieldRestrictionHom k rank h U (fun v => (c v : ℤ)) p)
    (cechNativeAmbientFieldRestrictionHom k
      (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p)
    (coordinateFixedUExponentNativeTermIso_field k rank L U c p)
    (coordinateFixedUExponentNativeTermIso_field k rank K U c p)
    (coordinateFixedUNativeFieldIso_restriction k rank h U (fun v => (c v : ℤ)) p)
    (cechNativeAmbientFieldIso_restriction k
      (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p)
    (coordinateFixedUExponentTermEquiv_restriction k rank h U c p)

end LPCA


