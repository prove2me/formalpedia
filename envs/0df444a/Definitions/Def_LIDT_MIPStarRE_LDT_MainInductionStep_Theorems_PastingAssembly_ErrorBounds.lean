-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_ErrorBounds
-- name    : LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_ErrorBounds
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T13:31:47.487156+00:00
-- url     : https://prove2.me/theorems/abaed9e8-75b1-40be-8329-5a6e1d44f8e7
-- title:
--   LIDT definitions: LDT / MainInductionStep / Theorems / PastingAssembly / ErrorBounds
-- statement:
--   This bundle provides the scalar error comparison needed in the main induction step. The result telescopes the induction-section pasting error into the next main-induction error under the supplied parameter bounds.
--
--   Principal definitions:
--   - `ldPastingInInductionError_le_mainInductionError_of_bounds`: bounds the induction-side pasted error by the main-induction error.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/ErrorBounds.lean#L23-L214

-- Generated from MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/ErrorBounds.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_AnswerTheorems
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_AvgSliceErrors_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_AvgSliceErrors_Successor
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Averaging
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_MainError
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Preliminaries
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_Basic
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
# Section 6 — Pasting Assembly: Error Bounds

This module contains the scalar absorption and degree-zero answer-valued pasting
constructions for the small-error branch.
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Scalar telescoping from the induction-section pasting error to the next
main-induction error.

The lemma isolates the scalar inequality chain from the assembly of the averaged
slice data: the bound on `κ`, the comparison `ζ ≤ ν`, and the bound on the
pasting-section `ν` term. -/
lemma ldPastingInInductionError_le_mainInductionError_of_bounds
    (params : Parameters)
    [FieldModel params.q]
    (eps delta gamma : Error)
    (k : ℕ)
    (kappa zeta : Error)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hkappa_le :
      kappa ≤
        ((params.m : Error) ^ (2 : ℕ)) *
          (mainInductionNu params.next k eps delta gamma +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))
          + zeta)
    (hzeta_le_nu : zeta ≤ mainInductionNu params.next k eps delta gamma)
    (hnu_le :
      ldPastingInInductionNu params k eps delta gamma zeta ≤
        (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma) :
    ldPastingInInductionError params k eps delta gamma kappa zeta ≤
      mainInductionError params.next k eps delta gamma := by
  let ν : Error := mainInductionNu params.next k eps delta gamma
  let E : Error :=
    Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))
  let E' : Error :=
    Real.exp (-((k : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ)))))
  have hkappa_le' : kappa ≤ ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta := by
    simpa [ν, E] using hkappa_le
  have hzeta_le_nu' : zeta ≤ ν := by
    simpa [ν] using hzeta_le_nu
  have hnu_le' :
      ldPastingInInductionNu params k eps delta gamma zeta ≤
        (1 / (5 : Error)) * ν := by
    simpa [ν] using hnu_le
  have hnu_nonneg : 0 ≤ ν := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    have hratio_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg (by positivity : 0 ≤ ((params.d : Error) / (params.q : Error)))
        (1 / (1024 : Error))
    have hsumnn : 0 ≤ Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow delta (1 / (1024 : Error)) +
        Real.rpow gamma (1 / (1024 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith [heps_root_nonneg, hdelta_root_nonneg, hgamma_root_nonneg, hratio_nonneg]
    dsimp [ν]
    unfold mainInductionNu
    exact mul_nonneg (by positivity) hsumnn
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact le_of_lt (Real.exp_pos _)
  have hE_le : E ≤ E' := by
    dsimp [E, E']
    apply Real.exp_le_exp.mpr
    have hm_sq_le : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.next.m : Error) ^ (2 : ℕ)) := by
      have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
        exact_mod_cast Nat.le_succ params.m
      nlinarith
    have hdenom_pos : 0 < 80000 * ((params.m : Error) ^ (2 : ℕ)) := by
      have hm_pos : (0 : Error) < (params.m : Error) := by
        exact_mod_cast params.hm
      nlinarith
    have hdenom_le :
        80000 * ((params.m : Error) ^ (2 : ℕ)) ≤
          80000 * ((params.next.m : Error) ^ (2 : ℕ)) := by
      nlinarith [hm_sq_le]
    have h_one_div :
        (1 / (80000 * ((params.next.m : Error) ^ (2 : ℕ))) : Error) ≤
          1 / (80000 * ((params.m : Error) ^ (2 : ℕ))) := by
      exact one_div_le_one_div_of_le hdenom_pos hdenom_le
    have hdiv :
        (k : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))) ≤
          (k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left h_one_div (by positivity : 0 ≤ (k : Error)))
    have hneg :
        -((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))) ≤
          -((k : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ)))) := by
      nlinarith [hdiv]
    exact hneg
  have hcoef_nu :
      ((((params.m : Error) ^ (2 : ℕ)) + 1) *
          (1 + 1 / (100 * (params.m : Error))) + 2 / 5 : Error) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) := by
    have hm0 : (params.m : Error) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hm_one : (1 : Error) ≤ (params.m : Error) := by
      exact_mod_cast params.hm
    have hnext_eq : (params.next.m : Error) = (params.m : Error) + 1 := by
      norm_num [Parameters.next]
    rw [hnext_eq]
    have hpoly : 0 ≤ 495 * ((params.m : Error) ^ (2 : ℕ)) - 200 * (params.m : Error) - 5 := by
      nlinarith [hm_one]
    field_simp [hm0]
    nlinarith [hpoly]
  have hcoef_E :
      ((((params.m : Error) ^ (2 : ℕ)) *
          (1 + 1 / (100 * (params.m : Error))) + 1 : Error)) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) := by
    have hm0 : (params.m : Error) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hnext_eq : (params.next.m : Error) = (params.m : Error) + 1 := by
      norm_num [Parameters.next]
    rw [hnext_eq]
    have hsq : 0 ≤ ((params.m : Error) ^ (2 : ℕ)) := by
      positivity
    field_simp [hm0]
    nlinarith [hsq]
  have hnu_bound :
      ((((params.m : Error) ^ (2 : ℕ)) + 1) *
          (1 + 1 / (100 * (params.m : Error))) + 2 / 5 : Error) * ν ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * ν := by
    exact mul_le_mul_of_nonneg_right hcoef_nu hnu_nonneg
  have hE_bound :
      ((((params.m : Error) ^ (2 : ℕ)) *
          (1 + 1 / (100 * (params.m : Error))) + 1 : Error)) * E ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * E := by
    exact mul_le_mul_of_nonneg_right hcoef_E hE_nonneg
  have herror_old :
      ((((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
          (1 + 1 / (100 * (params.m : Error))) +
        (2 / 5 : Error) * ν + E) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * (ν + E) := by
    have hrewrite :
        ((((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
              (1 + 1 / (100 * (params.m : Error))) +
            (2 / 5 : Error) * ν + E) =
          ((((params.m : Error) ^ (2 : ℕ)) + 1) *
              (1 + 1 / (100 * (params.m : Error))) + 2 / 5 : Error) * ν +
            ((((params.m : Error) ^ (2 : ℕ)) *
              (1 + 1 / (100 * (params.m : Error))) + 1 : Error) * E) := by
      ring
    rw [hrewrite]
    nlinarith [hnu_bound, hE_bound]
  have hkappa_scaled :
      kappa * (1 + 1 / (100 * (params.m : Error))) ≤
        (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
          (1 + 1 / (100 * (params.m : Error))) := by
    exact mul_le_mul_of_nonneg_right hkappa_le' (by positivity)
  have hnu_scaled :
      2 * ldPastingInInductionNu params k eps delta gamma zeta ≤ (2 / 5 : Error) * ν := by
    nlinarith [hnu_le']
  have hzeta_scaled :
      (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
          (1 + 1 / (100 * (params.m : Error))) ≤
        (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
          (1 + 1 / (100 * (params.m : Error))) := by
    have hadd :
        ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta ≤
          ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left hzeta_le_nu' (((params.m : Error) ^ (2 : ℕ)) * (ν + E))
    exact mul_le_mul_of_nonneg_right hadd (by positivity)
  have hzeta_scaled_add :
      (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
          (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E ≤
        (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
          (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hzeta_scaled ((2 / 5 : Error) * ν + E)
  have hE_scaled :
      ((params.next.m : Error) ^ (2 : ℕ)) * E ≤ ((params.next.m : Error) ^ (2 : ℕ)) * E' := by
    exact mul_le_mul_of_nonneg_left hE_le (by positivity)
  calc
    ldPastingInInductionError params k eps delta gamma kappa zeta
      = kappa * (1 + 1 / (100 * (params.m : Error))) +
          2 * ldPastingInInductionNu params k eps delta gamma zeta + E := by
            dsimp [E]
            simp [ldPastingInInductionError]
    _ ≤ (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
          (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E := by
            nlinarith [hkappa_scaled, hnu_scaled]
    _ ≤ (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
          (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E := by
            exact hzeta_scaled_add
    _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) * (ν + E) := herror_old
    _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) * (ν + E') := by
            nlinarith [hE_scaled]
    _ = mainInductionError params.next k eps delta gamma := by
            dsimp [ν, E']
            simp [mainInductionError, Parameters.next]







end MIPStarRE.LDT.MainInductionStep

end

end LIDT


