-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_AvgSliceErrors_Core
-- name    : LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_AvgSliceErrors_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T13:19:37.329891+00:00
-- url     : https://prove2.me/theorems/9e06c7e8-cb97-4a82-96b1-7bb796de672e
-- title:
--   LIDT definitions: LDT / MainInductionStep / Theorems / AvgSliceErrors / Core
-- statement:
--   This bundle provides the averaging and nonnegativity estimates for restricted slice errors in the main induction step. It controls averaged powers, establishes nonnegative slice error quantities, and derives the recursive bounds for self-improvement, the induction parameter, and the final slice error.
--
--   Principal definitions:
--   - `avgOver_uniform_fq_rpow_le_rpow_avg`: bounds an averaged power by the power of an average.
--   - `avgOver_uniform_fq_nonneg`: records nonnegativity of a uniform average.
--   - `restricted_axis_nonneg`: nonnegativity of the restricted axis error.
--   - `restricted_self_nonneg`: nonnegativity of the restricted self-consistency error.
--   - `restricted_diag_nonneg`: nonnegativity of the restricted diagonal error.
--   - `average_sliceSelfImprovementError_le`: bounds the average slice self-improvement error.
--   - `average_sliceMainInductionNu_le`: bounds the averaged slice induction parameter.
--   - `average_sliceError_le`: bounds the averaged recursive slice error.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MainInductionStep/Theorems/AvgSliceErrors/Core.lean#L25-L439

-- Generated from MIPStarRE/LDT/MainInductionStep/Theorems/AvgSliceErrors/Core.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionPMF
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_MainTheorems
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Point
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_SumForm
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Averaging
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_MainError
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Preliminaries
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_AnswerValued
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Axis
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Diagonal
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_AnswerSlice
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_StageDataConstructors
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_ErrorBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_RestrictSome
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_ProjectivizationChain_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_FinalMove
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_HalfSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_StageA0M1
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_MoveLemmas_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_PaperBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_AddInUFullStatement
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUPointConsistency
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Factored
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Transfer
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Variance
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_BoundednessGap
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_Decomposition
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_PointConsistency
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_PointConsistencyLiteral
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Assembly
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_PostDeleteA
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_FinalFields
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_SelfCloseness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimp
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimpAttr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteConicDuality
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Lean.Elab.Tactic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.Attr.Register
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix

namespace LIDT

namespace MIPStarRE.LDT
end MIPStarRE.LDT
namespace MIPStarRE.LDT.Commutativity
end MIPStarRE.LDT.Commutativity
namespace MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace MIPStarRE.LDT.CommutativityPoints
end MIPStarRE.LDT.CommutativityPoints
namespace MIPStarRE.LDT.MainInductionStep
end MIPStarRE.LDT.MainInductionStep
namespace MIPStarRE.LDT.MakingMeasurementsProjective
end MIPStarRE.LDT.MakingMeasurementsProjective
namespace MIPStarRE.LDT.Pasting
end MIPStarRE.LDT.Pasting
namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 6 — Averaged Slice Error Bounds: Core Estimates

This module contains the Jensen and averaging estimates for ordinary and
answer-valued restricted slice errors.
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι uF

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

 lemma avgOver_uniform_fq_rpow_le_rpow_avg
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → Error)
    (n : ℕ)
    (hn : 1 ≤ n)
    (hf : ∀ a, 0 ≤ f a) :
    avgOver (uniformDistribution (Fq params))
        (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
      Real.rpow (avgOver (uniformDistribution (Fq params)) f) (1 / (n : Error)) := by
  simpa using
    avgOver_uniform_rpow_one_div_le_rpow_avg
      (α := Fq params) (f := f) (n := n) hn hf

 lemma avgOver_uniform_fq_nonneg
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → Error)
    (hf : ∀ a, 0 ≤ f a) :
    0 ≤ avgOver (uniformDistribution (Fq params)) f :=
  avgOver_nonneg (uniformDistribution (Fq params)) f hf

private lemma restricted_axis_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.axisParallel x := by
  intro x
  let restricted := xRestrictedStrategy params strategy x
  exact le_trans
    (by
      unfold RestrictedSymStrat.axisParallelFailureProbability
      exact bipartiteConsError_nonneg restricted.state
        (uniformDistribution (AxisParallelTestSample params))
        (RestrictedSymStrat.axisParallelPointAnswerFamily restricted)
        (RestrictedSymStrat.axisParallelLineAnswerFamily restricted))
    (profile.restrictedGood x).axisParallelTest

private lemma restricted_self_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.selfConsistency x := by
  intro x
  let restricted := xRestrictedStrategy params strategy x
  exact le_trans
    (by
      unfold RestrictedSymStrat.selfConsistencyFailureProbability
      exact bipartiteSSCError_nonneg restricted.state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas restricted.pointMeasurement))
    (profile.restrictedGood x).selfConsistencyTest

private lemma restricted_diag_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.diagonal x := by
  intro x
  let restricted := xRestrictedStrategy params strategy x
  exact le_trans
    (by
      unfold RestrictedSymStrat.diagonalFailureProbability
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro j _
        exact bipartiteConsError_nonneg restricted.state
          (uniformDistribution (RestrictedDiagonalSample params j))
          (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily restricted j)
          (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily restricted j))
    (profile.restrictedGood x).diagonalLineTest







/-- Averaging the slice self-improvement errors gives the paper's displayed
bound on `\mathbb{E}_x[\zeta_x]`, i.e. the first inequality from
`inductive_step.tex:555-567`. -/
lemma average_sliceSelfImprovementError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceSelfImprovementError params hrestrict x) ≤
      selfImprovementInInductionError params.next eps delta gamma := by
  let 𝒟 := uniformDistribution (Fq params)
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have haxis_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) ≤
        Real.rpow
          (averageRestrictedAxisParallelError params hrestrict.profile)
          (1 / (32 : Error)) := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        hrestrict.profile.axisParallel 32 (by norm_num)
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) ≤
        Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (32 : Error)) := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        hrestrict.profile.selfConsistency 32 (by norm_num)
        (restricted_self_nonneg params hrestrict.profile)
  have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast Nat.le_succ params.m
  have haxis_nonneg : 0 ≤ averageRestrictedAxisParallelError params hrestrict.profile := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_nonneg params hrestrict.profile.axisParallel
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_nonneg : 0 ≤ averageRestrictedSelfConsistencyError params hrestrict.profile := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_nonneg params hrestrict.profile.selfConsistency
        (restricted_self_nonneg params hrestrict.profile)
  have haxis_rpow_le :
      Real.rpow (averageRestrictedAxisParallelError params hrestrict.profile) (1 / (32 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * eps) (1 / (32 : Error)) := by
    exact Real.rpow_le_rpow haxis_nonneg hrestrict.axisAverageBound (by positivity)
  have hself_rpow_le :
      Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (32 : Error)) ≤
        Real.rpow delta (1 / (32 : Error)) := by
    exact Real.rpow_le_rpow hself_nonneg hrestrict.selfAverageBound (by positivity)
  have haxis_term :
      (params.m : Error) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) ≤
        (params.next.m : Error) * Real.rpow eps (1 / (32 : Error)) := by
    have htmp :=
      mul_le_mul_of_nonneg_left (le_trans haxis_avg haxis_rpow_le) (by positivity : 0
          ≤ (params.m : Error))
    exact le_trans htmp
      (m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow params heps_nonneg (by positivity)
        (by norm_num : (1 / (32 : Error)) ≤ 1))
  have hself_term :
      (params.m : Error) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) ≤
        (params.next.m : Error) * Real.rpow delta (1 / (32 : Error)) := by
    have htmp :
        (params.m : Error) *
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) ≤
          (params.m : Error) * Real.rpow delta (1 / (32 : Error)) := by
      exact mul_le_mul_of_nonneg_left (le_trans hself_avg hself_rpow_le) (by positivity)
    exact le_trans htmp <|
      mul_le_mul_of_nonneg_right hm_le_next (Real.rpow_nonneg hdelta_nonneg _)
  have hratio_term :
      (params.m : Error) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
        (params.next.m : Error) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    exact mul_le_mul_of_nonneg_right hm_le_next (Real.rpow_nonneg hratio_nonneg _)
  have hinner :
      (params.m : Error) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ≤
        (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
    nlinarith [haxis_term, hself_term, hratio_term]
  have hinner' := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ (3000 : Error))
  calc
    avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x)
      = 3000 * (params.m : Error) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simp [sliceSelfImprovementError, selfImprovementInInductionError, avgOver_add,
            avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ 3000 * (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simpa [mul_assoc] using hinner'
    _ = selfImprovementInInductionError params.next eps delta gamma := by
          simp [selfImprovementInInductionError]

/-- Jensen/conditioning estimate controlling the averaged slice induction
parameter `\mathbb{E}_x[\nu_x]` by the next-stage `\nu`, corresponding to the
second displayed inequality in `inductive_step.tex:555-567`. -/
private lemma average_sliceMainInductionNu_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          mainInductionNu params k
            (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x)
            (hrestrict.profile.diagonal x)) ≤
      mainInductionNu params.next k eps delta gamma := by
  let 𝒟 := uniformDistribution (Fq params)
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have haxis_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageRestrictedAxisParallelError params hrestrict.profile)
          (1 / (1024 : Error)) := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        hrestrict.profile.axisParallel 1024 (by norm_num)
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (1024 : Error)) := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        hrestrict.profile.selfConsistency 1024 (by norm_num)
        (restricted_self_nonneg params hrestrict.profile)
  have hdiag_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageRestrictedDiagonalError params hrestrict.profile)
          (1 / (1024 : Error)) := by
    simpa [averageRestrictedDiagonalError, 𝒟] using
      avgOver_uniform_fq_rpow_le_rpow_avg params
        hrestrict.profile.diagonal 1024 (by norm_num)
        (restricted_diag_nonneg params hrestrict.profile)
  have hm_sq_le_next_sq : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.next.m : Error) ^ (2 : ℕ)) := by
    have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
      exact_mod_cast Nat.le_succ params.m
    nlinarith
  have haxis_nonneg : 0 ≤ averageRestrictedAxisParallelError params hrestrict.profile := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_fq_nonneg params hrestrict.profile.axisParallel
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_nonneg : 0 ≤ averageRestrictedSelfConsistencyError params hrestrict.profile := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_fq_nonneg params hrestrict.profile.selfConsistency
        (restricted_self_nonneg params hrestrict.profile)
  have hdiag_nonneg : 0 ≤ averageRestrictedDiagonalError params hrestrict.profile := by
    simpa [averageRestrictedDiagonalError, 𝒟] using
      avgOver_uniform_fq_nonneg params hrestrict.profile.diagonal
        (restricted_diag_nonneg params hrestrict.profile)
  have haxis_rpow_le :
      Real.rpow
          (averageRestrictedAxisParallelError params hrestrict.profile)
          (1 / (1024 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * eps) (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow haxis_nonneg hrestrict.axisAverageBound (by positivity)
  have hself_rpow_le :
      Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (1024 : Error)) ≤
        Real.rpow delta (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow hself_nonneg hrestrict.selfAverageBound (by positivity)
  have hdiag_rpow_le :
      Real.rpow (averageRestrictedDiagonalError params hrestrict.profile) (1 / (1024 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * gamma) (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow hdiag_nonneg hrestrict.diagonalAverageBound (by positivity)
  have haxis_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow eps (1 / (1024 : Error)) := by
    have htmp := mul_le_mul_of_nonneg_left (le_trans haxis_avg haxis_rpow_le)
      (by positivity : 0 ≤ ((params.m : Error) ^ (2 : ℕ)))
    exact le_trans htmp
      (m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow params heps_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1))
  have hself_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟
            (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow delta (1 / (1024 : Error)) := by
    have htmp :
        ((params.m : Error) ^ (2 : ℕ)) *
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) ≤
          ((params.m : Error) ^ (2 : ℕ)) * Real.rpow delta (1 / (1024 : Error)) := by
      exact mul_le_mul_of_nonneg_left (le_trans hself_avg hself_rpow_le) (by positivity)
    exact le_trans htmp <|
      mul_le_mul_of_nonneg_right hm_sq_le_next_sq (Real.rpow_nonneg hdelta_nonneg _)
  have hdiag_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow gamma (1 / (1024 : Error)) := by
    have htmp := mul_le_mul_of_nonneg_left (le_trans hdiag_avg hdiag_rpow_le)
      (by positivity : 0 ≤ ((params.m : Error) ^ (2 : ℕ)))
    exact le_trans htmp
      (m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow params hgamma_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1))
  have hratio_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    exact mul_le_mul_of_nonneg_right hm_sq_le_next_sq (Real.rpow_nonneg hratio_nonneg _)
  have hinner :
      ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
    nlinarith [haxis_term, hself_term, hdiag_term, hratio_term]
  have hinner' := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 1000
      * ((k : Error) ^ (2 : ℕ)))
  calc
    avgOver 𝒟 (fun x =>
        mainInductionNu params k (hrestrict.profile.axisParallel x)
          (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x))
      = 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          simp [mainInductionNu, avgOver_add, avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          simpa [mul_assoc] using hinner'
    _ = mainInductionNu params.next k eps delta gamma := by
          simp [mainInductionNu]

/-- Averaging the recursive slice errors `\sigma_x` and telescoping the slice
main-induction bound yields the paper's `\mathbb{E}_x[\sigma_x]` estimate used
in the final pasting-data record error calculation. -/
lemma average_sliceError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma)
    (hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k) :
    avgOver (uniformDistribution (Fq params)) hinduction.sliceError ≤
      ((params.m : Error) ^ (2 : ℕ)) *
        (mainInductionNu params.next k eps delta gamma +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
  let 𝒟 := uniformDistribution (Fq params)
  have havg := avgOver_mono 𝒟 hinduction.sliceError
    (fun x =>
      mainInductionError params k (hrestrict.profile.axisParallel x)
        (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x))
    hinduction.error_le
  calc
    avgOver 𝒟 hinduction.sliceError
      ≤ avgOver 𝒟 (fun x =>
          mainInductionError params k (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x)) := havg
    _ = ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x =>
              mainInductionNu params k (hrestrict.profile.axisParallel x)
                (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x)) +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
          simp [mainInductionError, avgOver_add, avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ ((params.m : Error) ^ (2 : ℕ)) *
          (mainInductionNu params.next k eps delta gamma +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
          gcongr
          exact average_sliceMainInductionNu_le params strategy eps delta gamma k hgood hrestrict








end MIPStarRE.LDT.MainInductionStep

end

end LIDT


