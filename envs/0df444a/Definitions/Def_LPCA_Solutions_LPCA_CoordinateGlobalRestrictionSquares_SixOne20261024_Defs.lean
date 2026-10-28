-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinateGlobalRestrictionSquares_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_CoordinateGlobalRestrictionSquares_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T22:23:32.358188+00:00
-- url     : https://prove2.me/theorems/3988cefd-744f-44b1-9c38-a7390a624f02
-- title:
--   Coordinate Global Restriction Squares — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for coordinate global restriction squares used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Independent actual Gamma quotient maps tensored with id on M_A.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_CoordinateGlobalRestrictionSquares.lean, selected declarations in lines 17–143; source SHA-256 33dadf84994305946995a94b82bb631c9fea3e13e7383c3551f7fea91471bda4; exact-source certificate Sapelo2 job 49296539.

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
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateGlobalSourceGrading_SixOne20261024_Defs
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

/-- Independent actual Gamma quotient maps tensored with id on M_A. -/
noncomputable def coordinateCechTensorNativeRestrictionHom {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) :
    coordinateCechTensorTerm k L U p ⟶ coordinateCechTensorTerm k K U p :=
  nativeTensorSumMap k {v : V // v ∉ U}
    (coordinateGammaCechNativeFamily k L U p) (coordinateGammaCechNativeFamily k K U p)
    (coordinateCechMonomialFamily k U)
    (fun s => ModuleCat.ofHom (ambientCechTermRestriction k
      (coordinateComplementComplex_faces_mono h U s.1) Finset.univ p))

noncomputable def coordinateCechTensorFieldRestrictionHom {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) :
    coordinateCechTensorFieldTerm k L U p ⟶ coordinateCechTensorFieldTerm k K U p :=
  nativeTensorSumFieldMap k {v : V // v ∉ U}
    (coordinateGammaCechNativeFamily k L U p) (coordinateGammaCechNativeFamily k K U p)
    (coordinateCechMonomialFamily k U)
    (fun s => ModuleCat.ofHom (ambientCechTermRestriction k
      (coordinateComplementComplex_faces_mono h U s.1) Finset.univ p))

theorem coordinateCechTensorNativeFieldIso_restriction {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) :
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial {v : V // v ∉ U} k)).map
        (coordinateCechTensorNativeRestrictionHom k h U p) ≫ (coordinateCechTensorNativeFieldIso k K U p).hom =
      (coordinateCechTensorNativeFieldIso k L U p).hom ≫ coordinateCechTensorFieldRestrictionHom k h U p :=
  nativeTensorSumFieldIso_map k {v : V // v ∉ U}
    (coordinateGammaCechNativeFamily k L U p) (coordinateGammaCechNativeFamily k K U p)
    (coordinateCechMonomialFamily k U) _

theorem coordinateCechTensorDegreeLeg_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ)
    (c : {v : V // v ∈ U} → ℕ) (b : {v : V // v ∉ U} → ℤ) :
    coordinateCechTensorDegreeLeg k L U p c b ≫ coordinateCechTensorFieldRestrictionHom k h U p =
      cechNativeTermRestrictionHom k ((coordinateComplementEmbedding U).trans rank)
        (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p b ≫
          coordinateCechTensorDegreeLeg k K U p c b :=
  nativeTensorSumLeg_map k {v : V // v ∉ U}
    (coordinateGammaCechNativeFamily k L U p) (coordinateGammaCechNativeFamily k K U p)
    (coordinateCechMonomialFamily k U) _ ⟨coordinateExponentSupport U c, coordinateExponentSupport_subset U c⟩
    _ _ _ _ _ _
    (cechNativeAmbientDegreeLegHom_restriction k ((coordinateComplementEmbedding U).trans rank)
      (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p b)

attribute [local irreducible] coordinateCanonicalTensorHom coordinateCechTensorDegreeLeg
  coordinateFixedExponentTermIso coordinateCanonicalNativeTermIso

theorem coordinateCanonicalTensorHom_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) :
    coordinateCanonicalTensorHom k rank L U p ≫ coordinateCechTensorFieldRestrictionHom k h U p =
      cechNativeAmbientFieldRestrictionHom k h (coordinateCechSupport U) p ≫ coordinateCanonicalTensorHom k rank K U p := by
  apply coordinateCanonicalSourceHom_ext k L U p (coordinateCechTensorFieldTerm k K U p)
  intro c b
  exact (categoryHomogeneousAssembly
    (coordinateCanonicalTensorHom k rank K U p) (coordinateCanonicalTensorHom k rank L U p)
    (cechNativeTermForgetHom k K (coordinateCechSupport U) p (extendCoordinateDegree U (fun v => (c v : ℤ)) b))
    (cechNativeTermForgetHom k L (coordinateCechSupport U) p (extendCoordinateDegree U (fun v => (c v : ℤ)) b))
    (cechNativeAmbientFieldRestrictionHom k h (coordinateCechSupport U) p)
    (cechNativeTermRestrictionHom k rank h (coordinateCechSupport U) p (extendCoordinateDegree U (fun v => (c v : ℤ)) b))
    (coordinateFixedExponentTermIso k rank K U c b p).hom (coordinateFixedExponentTermIso k rank L U c b p).hom
    (coordinateCechTensorDegreeLeg k K U p c b) (coordinateCechTensorDegreeLeg k L U p c b)
    (cechNativeTermRestrictionHom k ((coordinateComplementEmbedding U).trans rank)
      (coordinateComplementComplex_faces_mono h U (coordinateExponentSupport U c)) Finset.univ p b)
    (coordinateCechTensorFieldRestrictionHom k h U p)
    (cechNativeTermForgetHom_restriction k rank h (coordinateCechSupport U) p (extendCoordinateDegree U (fun v => (c v : ℤ)) b))
    (coordinateCanonicalTensorHom_leg k rank K U p c b) (coordinateCanonicalTensorHom_leg k rank L U p c b)
    (coordinateFixedExponentTermIso_restriction k rank h U c b p)
    (coordinateCechTensorDegreeLeg_restriction k rank h U p c b)).symm

theorem coordinateCanonicalNativeTermIso_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) :
    (coordinateCanonicalNativeTermIso k rank L U p).hom ≫ coordinateCechTensorNativeRestrictionHom k h U p =
      coordinateNativeAmbientRestrictionHom k h U p ≫ (coordinateCanonicalNativeTermIso k rank K U p).hom :=
  faithfulComparisonSquare
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial {v : V // v ∉ U} k))
    (coordinateNativeAmbientFieldIso k L U p) (coordinateNativeAmbientFieldIso k K U p)
    (coordinateCechTensorNativeFieldIso k L U p) (coordinateCechTensorNativeFieldIso k K U p)
    (coordinateCanonicalNativeTermIso k rank L U p).hom (coordinateCanonicalNativeTermIso k rank K U p).hom
    (coordinateCanonicalTensorHom k rank L U p) (coordinateCanonicalTensorHom k rank K U p)
    (coordinateNativeAmbientRestrictionHom k h U p) (coordinateCechTensorNativeRestrictionHom k h U p)
    (cechNativeAmbientFieldRestrictionHom k h (coordinateCechSupport U) p) (coordinateCechTensorFieldRestrictionHom k h U p)
    (coordinateCanonicalNativeTermIso_field k rank L U p) (coordinateCanonicalNativeTermIso_field k rank K U p)
    (coordinateNativeAmbientFieldIso_restriction k h U p) (coordinateCechTensorNativeFieldIso_restriction k h U p)
    (coordinateCanonicalTensorHom_restriction k rank h U p)

noncomputable def coordinateOriginalNativeRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) : coordinateOriginalNativeComplex k rank L U ⟶ coordinateOriginalNativeComplex k rank K U :=
  ((ModuleCat.restrictScalars (coordinateComplementPolynomialHom k U)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (ambientCechRestriction k rank h (coordinateCechSupport U))

theorem coordinateGlobalSourceDegreeLeg_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) (a : V → ℤ) :
    coordinateGlobalSourceDegreeLeg k L U p a ≫
        (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial {v : V // v ∉ U} k)).map
          (coordinateNativeAmbientRestrictionHom k h U p) =
      cechNativeTermRestrictionHom k rank h (coordinateCechSupport U) p a ≫ coordinateGlobalSourceDegreeLeg k K U p a := by
  apply (cancel_mono (coordinateNativeAmbientFieldIso k K U p).hom).mp
  simp only [Category.assoc]
  rw [coordinateNativeAmbientFieldIso_restriction, ← Category.assoc, coordinateGlobalSourceDegreeLeg_field,
    cechNativeTermForgetHom_restriction, coordinateGlobalSourceDegreeLeg_field]

theorem coordinateGlobalSourcePiece_restriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) (a : V → ℤ)
    (x : nativePolynomialField k {v : V // v ∉ U} (coordinateNativeAmbientTerm k L U p))
    (hx : x ∈ coordinateGlobalSourcePiece k L U p a) :
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial {v : V // v ∉ U} k)).map
      (coordinateNativeAmbientRestrictionHom k h U p) x ∈ coordinateGlobalSourcePiece k K U p a := by
  rw [coordinateGlobalSourcePiece_eq_range] at hx ⊢
  exact moduleRangeSquare_mem k _ _ _ _ _ _ _ _ (coordinateGlobalSourceDegreeLeg_restriction k rank h U p a) x hx

noncomputable def coordinateGlobalSourceGradedTermRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) (p : ℕ) :
    coordinateGlobalSourceGradedTerm k L U p ⟶ coordinateGlobalSourceGradedTerm k K U p where
  map := coordinateNativeAmbientRestrictionHom k h U p
  map_piece a x hx := coordinateGlobalSourcePiece_restriction k rank h U p a x hx

noncomputable def coordinateGlobalSourceGradedRestriction (rank : V ↪ ℕ) {K L : Complex V}
    (h : K.faces ⊆ L.faces) (U : Finset V) :
    coordinateGlobalSourceGradedComplex k rank L U ⟶ coordinateGlobalSourceGradedComplex k rank K U where
  f p := coordinateGlobalSourceGradedTermRestriction k rank h U p
  comm' := by
    intro p q hpq
    change p + 1 = q at hpq
    subst q
    rw [coordinateGlobalSourceGradedComplex_d, coordinateGlobalSourceGradedComplex_d]
    apply GradedPolynomialModule.hom_ext
    have hs := (coordinateOriginalNativeRestriction k rank h U).comm p (p + 1)
    rw [coordinateOriginalNativeComplex_d, coordinateOriginalNativeComplex_d] at hs
    exact hs

end LPCA


