-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinateGlobalGradedNaturality_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_CoordinateGlobalGradedNaturality_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T22:43:11.293448+00:00
-- url     : https://prove2.me/theorems/f55166bb-b86e-433f-bafb-7ab4a1c033b5
-- title:
--   Coordinate Global Graded Naturality — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for coordinate global graded naturality used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   The independently defined tensor quotient maps are the components of
--   this comparison. Transport is used only to prove their chain property.
--
--   Universal naturality of the global Z^V-graded S_T-linear chain
--   decomposition under the original face-ring quotient maps, reversed in K.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_CoordinateGlobalGradedNaturality.lean, selected declarations in lines 17–161; source SHA-256 61d4881a0bd7675cbd27860e8c84cde429f6806fe4a0cae136f51066d935bf24; exact-source certificate Sapelo2 job 49296539.

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
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
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
import Definitions.Def_LPCA_Solutions_LPCA_CechNativeAmbientGrading_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_CochainSuccessorIso_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCanonicalCechAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCanonicalNativeChain_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCanonicalTensorLegs_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCanonicalTensorMap_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCanonicalTensorSquares_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCechComparison_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCechNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCechTensorComplex_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateCechTensorFieldAssembly_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateGenericTensorAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateGlobalGradedComplex_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateGlobalRestrictionSquares_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateGlobalSourceGrading_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateGlobalTensorGrading_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateIndexedGrading_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateModuleScalars_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateMonomialSpace_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateNativeAmbientDifferential_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateNativeAmbientTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateNativeChainDegreeLegs_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateNativeChainPieces_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateSupportAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateSupportRegrouping_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateTensorTarget_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_InternalGradingTransport_SixOne20261024_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_ModuleIsoPieceSquares_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleLinearMapSquare_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativeLegAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativeLegChartAssembly_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativeLegHomExt_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativePolynomialTensor_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativeTensorSumLegs_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativeTensorSumOperators_SixOne20261024_Defs
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

theorem coordinateCanonicalNativeComplexIso_hom_f (rank : V ↪ ℕ) (K : Complex V) (U : Finset V) (p : ℕ) :
    (coordinateCanonicalNativeComplexIso k rank K U).hom.f p = (coordinateCanonicalNativeTermIso k rank K U p).hom := by
  simp only [coordinateCanonicalNativeComplexIso, cochainSuccessorIso_hom_f]

theorem coordinateCanonicalNativeComplexIso_inv_f (rank : V ↪ ℕ) (K : Complex V) (U : Finset V) (p : ℕ) :
    (coordinateCanonicalNativeComplexIso k rank K U).inv.f p = (coordinateCanonicalNativeTermIso k rank K U p).inv := by
  simp only [coordinateCanonicalNativeComplexIso, cochainSuccessorIso_inv_f]

theorem coordinateGlobalGradedComplexIso_hom_f (rank : V ↪ ℕ) (K : Complex V) (U : Finset V) (p : ℕ) :
    (coordinateGlobalGradedComplexIso k rank K U).hom.f p = (coordinateGlobalGradedTermIso k rank K U p).hom := by
  simp only [coordinateGlobalGradedComplexIso, cochainSuccessorIso_hom_f]

attribute [local irreducible] coordinateCanonicalNativeTermIso coordinateGlobalGradedTermIso

/-- The independently defined tensor quotient maps are the components of
this comparison. Transport is used only to prove their chain property. -/
theorem coordinateCechTensorRestriction_transport_f (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) :
    ((coordinateCanonicalNativeComplexIso k rank L U).inv ≫ coordinateOriginalNativeRestriction k rank h U ≫
      (coordinateCanonicalNativeComplexIso k rank K U).hom).f p = coordinateCechTensorNativeRestrictionHom k h U p := by
  change (coordinateCanonicalNativeComplexIso k rank L U).inv.f p ≫
    (coordinateOriginalNativeRestriction k rank h U).f p ≫ (coordinateCanonicalNativeComplexIso k rank K U).hom.f p = _
  rw [coordinateCanonicalNativeComplexIso_inv_f, coordinateCanonicalNativeComplexIso_hom_f]
  exact isoSquare_factor (coordinateCanonicalNativeTermIso k rank L U p) (coordinateCanonicalNativeTermIso k rank K U p)
    (coordinateNativeAmbientRestrictionHom k h U p) (coordinateCechTensorNativeRestrictionHom k h U p)
    (coordinateCanonicalNativeTermIso_restriction k rank h U p)

noncomputable def coordinateCechTensorNativeRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) : coordinateCechTensorComplex k rank L U ⟶ coordinateCechTensorComplex k rank K U where
  f p := coordinateCechTensorNativeRestrictionHom k h U p
  comm' := by
    intro p q hpq
    change p + 1 = q at hpq
    subst q
    have hs := ((coordinateCanonicalNativeComplexIso k rank L U).inv ≫ coordinateOriginalNativeRestriction k rank h U ≫
      (coordinateCanonicalNativeComplexIso k rank K U).hom).comm p (p + 1)
    rw [coordinateCechTensorRestriction_transport_f, coordinateCechTensorRestriction_transport_f] at hs
    exact hs



theorem coordinateGlobalTensorPiece_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) (a : V → ℤ)
    (y : coordinateCechTensorTerm k L U p) (hy : y ∈ coordinateGlobalTensorPiece k L U p a) :
    coordinateCechTensorNativeRestrictionHom k h U p y ∈ coordinateGlobalTensorPiece k K U p a :=
  moduleIsoPieces_forward_square (MvPolynomial {v : V // v ∉ U} k)
    (coordinateNativeAmbientTerm k L U p) (coordinateNativeAmbientTerm k K U p)
    (coordinateCechTensorTerm k L U p) (coordinateCechTensorTerm k K U p)
    (coordinateCanonicalNativeTermIso k rank L U p) (coordinateCanonicalNativeTermIso k rank K U p)
    (coordinateNativeAmbientRestrictionHom k h U p) (coordinateCechTensorNativeRestrictionHom k h U p)
    (fun x => x ∈ coordinateGlobalSourcePiece k L U p a) (fun x => x ∈ coordinateGlobalSourcePiece k K U p a)
    (fun x => x ∈ coordinateGlobalTensorPiece k L U p a) (fun x => x ∈ coordinateGlobalTensorPiece k K U p a)
    (coordinateCanonicalNativeTermIso_piece k rank L U p a) (coordinateCanonicalNativeTermIso_piece k rank K U p a)
    (fun x hx => coordinateGlobalSourcePiece_restriction k rank h U p a x hx)
    (coordinateCanonicalNativeTermIso_restriction k rank h U p) y hy

noncomputable def coordinateGlobalTensorGradedTermRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) :
    coordinateGlobalTensorGradedTerm k rank L U p ⟶ coordinateGlobalTensorGradedTerm k rank K U p where
  map := coordinateCechTensorNativeRestrictionHom k h U p
  map_piece a y hy := coordinateGlobalTensorPiece_restriction k rank h U p a y hy

noncomputable def coordinateGlobalTensorGradedRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) :
    coordinateGlobalTensorGradedComplex k rank L U ⟶ coordinateGlobalTensorGradedComplex k rank K U where
  f p := coordinateGlobalTensorGradedTermRestriction k rank h U p
  comm' := by
    intro p q hpq
    change p + 1 = q at hpq
    subst q
    rw [coordinateGlobalTensorGradedComplex_d, coordinateGlobalTensorGradedComplex_d]
    apply GradedPolynomialModule.hom_ext
    have hs := (coordinateCechTensorNativeRestriction k rank h U).comm p (p + 1)
    rw [coordinateCechTensorComplex_d, coordinateCechTensorComplex_d] at hs
    exact hs

/-- Universal naturality of the global Z^V-graded S_T-linear chain
decomposition under the original face-ring quotient maps, reversed in K. -/
theorem coordinateGlobalGradedComplexIso_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) :
    coordinateGlobalSourceGradedRestriction k rank h U ≫ (coordinateGlobalGradedComplexIso k rank K U).hom =
      (coordinateGlobalGradedComplexIso k rank L U).hom ≫ coordinateGlobalTensorGradedRestriction k rank h U := by
  apply HomologicalComplex.hom_ext
  intro p
  change coordinateGlobalSourceGradedTermRestriction k rank h U p ≫ (coordinateGlobalGradedComplexIso k rank K U).hom.f p =
    (coordinateGlobalGradedComplexIso k rank L U).hom.f p ≫ coordinateGlobalTensorGradedTermRestriction k rank h U p
  rw [coordinateGlobalGradedComplexIso_hom_f, coordinateGlobalGradedComplexIso_hom_f]
  apply GradedPolynomialModule.hom_ext
  change coordinateNativeAmbientRestrictionHom k h U p ≫ ((coordinateGlobalGradedTermIso k rank K U p).hom).map =
    ((coordinateGlobalGradedTermIso k rank L U p).hom).map ≫ coordinateCechTensorNativeRestrictionHom k h U p
  rw [coordinateGlobalGradedTermIso_hom_map, coordinateGlobalGradedTermIso_hom_map]
  exact (coordinateCanonicalNativeTermIso_restriction k rank h U p).symm

theorem coordinateOriginalNativeRestriction_refl (rank : V ↪ ℕ) (K : Complex V) (U : Finset V) :
    coordinateOriginalNativeRestriction k rank (Finset.Subset.refl K.faces) U = 𝟙 _ := by
  unfold coordinateOriginalNativeRestriction
  rw [ambientCechRestriction_refl]
  exact CategoryTheory.Functor.map_id _ _

theorem coordinateOriginalNativeRestriction_comp (rank : V ↪ ℕ) {K L M : Complex V}
    (hKL : K.faces ⊆ L.faces) (hLM : L.faces ⊆ M.faces) (U : Finset V) :
    coordinateOriginalNativeRestriction k rank hLM U ≫ coordinateOriginalNativeRestriction k rank hKL U =
      coordinateOriginalNativeRestriction k rank (hKL.trans hLM) U := by
  unfold coordinateOriginalNativeRestriction
  rw [← Functor.map_comp, ambientCechRestriction_comp]

theorem coordinateGlobalSourceGradedRestriction_refl (rank : V ↪ ℕ) (K : Complex V) (U : Finset V) :
    coordinateGlobalSourceGradedRestriction k rank (Finset.Subset.refl K.faces) U = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  apply GradedPolynomialModule.hom_ext
  exact congrArg (fun f => f.f p) (coordinateOriginalNativeRestriction_refl k rank K U)

theorem coordinateGlobalSourceGradedRestriction_comp (rank : V ↪ ℕ) {K L M : Complex V}
    (hKL : K.faces ⊆ L.faces) (hLM : L.faces ⊆ M.faces) (U : Finset V) :
    coordinateGlobalSourceGradedRestriction k rank hLM U ≫ coordinateGlobalSourceGradedRestriction k rank hKL U =
      coordinateGlobalSourceGradedRestriction k rank (hKL.trans hLM) U := by
  apply HomologicalComplex.hom_ext
  intro p
  apply GradedPolynomialModule.hom_ext
  exact congrArg (fun f => f.f p) (coordinateOriginalNativeRestriction_comp k rank hKL hLM U)

theorem coordinateGlobalTensorGradedRestriction_refl (rank : V ↪ ℕ) (K : Complex V) (U : Finset V) :
    coordinateGlobalTensorGradedRestriction k rank (Finset.Subset.refl K.faces) U = 𝟙 _ := by
  apply (cancel_epi (coordinateGlobalGradedComplexIso k rank K U).hom).mp
  rw [← coordinateGlobalGradedComplexIso_restriction, coordinateGlobalSourceGradedRestriction_refl,
    Category.id_comp, Category.comp_id]

theorem coordinateGlobalTensorGradedRestriction_comp (rank : V ↪ ℕ) {K L M : Complex V}
    (hKL : K.faces ⊆ L.faces) (hLM : L.faces ⊆ M.faces) (U : Finset V) :
    coordinateGlobalTensorGradedRestriction k rank hLM U ≫ coordinateGlobalTensorGradedRestriction k rank hKL U =
      coordinateGlobalTensorGradedRestriction k rank (hKL.trans hLM) U := by
  apply (cancel_epi (coordinateGlobalGradedComplexIso k rank M U).hom).mp
  rw [← Category.assoc, ← coordinateGlobalGradedComplexIso_restriction, Category.assoc,
    ← coordinateGlobalGradedComplexIso_restriction, ← Category.assoc, coordinateGlobalSourceGradedRestriction_comp]
  exact coordinateGlobalGradedComplexIso_restriction k rank (hKL.trans hLM) U



end LPCA


