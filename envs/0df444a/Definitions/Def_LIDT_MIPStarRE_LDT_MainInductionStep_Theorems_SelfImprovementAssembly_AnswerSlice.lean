-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_AnswerSlice
-- name    : LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_AnswerSlice
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T13:10:56.178397+00:00
-- url     : https://prove2.me/theorems/962f7e4e-82cb-4e5b-a848-01bd1fc06d81
-- title:
--   LIDT definitions: LDT / MainInductionStep / Theorems / SelfImprovementAssembly / AnswerSlice
-- statement:
--   This bundle constructs answer-valued restricted slice data and transports it into the ordinary self-improvement records.
--
--   Principal definitions:
--   - `dummyDiagonalCovariantMeasurement`: the dummy diagonal measurement for unused coordinates.
--   - `answerSelfImprovementCarrier`: the answer carrier used by the restricted strategy.
--   - `restrictAnswerDiagonalAnswerMeasurement`: restricts a diagonal answer measurement to a slice.
--   - `xRestrictedAnswerSymStratOfAnswer`: builds the restricted answer-valued strategy.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean#L30-L786

-- Generated from MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_Core
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
namespace MIPStarRE.LDT.MakingMeasurementsProjective
end MIPStarRE.LDT.MakingMeasurementsProjective
namespace MIPStarRE.LDT.Pasting
end MIPStarRE.LDT.Pasting
namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 6 — Answer-Valued Self-Improvement Slice Transport

This file contains the answer-valued analogues of the Section 6 slice-transport
constructors.  The ordinary construction, including `selfImprovementInInductionSection`,
lives in `SelfImprovementAssembly.Core` and is imported here so that the
answer-valued construction can reuse the same Section 9 self-improvement
theorem.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- A covariant diagonal measurement with a fixed zero polynomial outcome.

This measurement is used only as an inert diagonal component when applying the
axis-parallel/self-consistency form of self-improvement to an answer-valued
slice.  The Section 9 conclusion obtained in this way is independent of the
diagonal-line failure probability. -/
noncomputable def dummyDiagonalCovariantMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] :
    DiagonalCovariantMeasurement params ι where
  toIdxProjMeas := fun _ =>
    ProjMeas.trivialDistinguishedOutcome (default : DiagonalLinePolynomial params)
  transportInvariant := fun _ t =>
    ((ProjMeas.transport_trivialDistinguishedOutcome
      (DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
      (default : DiagonalLinePolynomial params)).trans
        (congrArg (ProjMeas.trivialDistinguishedOutcome (ι := ι))
          (DiagonalLinePolynomial.reparamAt_default t))).symm

/-- Forget the answer-valued diagonal alphabet of a restricted slice, replacing
it by an inert ordinary diagonal measurement.

The point, axis-parallel, state, and normalization data are unchanged.  This is
therefore sufficient for the self-improvement theorem variant whose hypotheses
are exactly the axis-parallel and point self-consistency bounds. -/
noncomputable def answerSelfImprovementCarrier
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := strategy.pointMeasurement
  axisParallelMeasurement := strategy.axisParallelMeasurement
  diagonalMeasurement := dummyDiagonalCovariantMeasurement params ι

/-- Restrict an answer-valued diagonal-line measurement to the slice at height
`x`.

This is the answer-valued analogue of `restrictDiagonalAnswerMeasurement`.
Because the diagonal answer alphabet is the full function space on the line,
restriction is the total map
`DiagonalLineAnswer.restrictAtHeight`; no low-degree support theorem is needed
to define this slice. -/
noncomputable def restrictAnswerDiagonalAnswerMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι :=
  fun ℓ =>
    ProjMeas.postprocess
      (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x))
      (fun f : DiagonalLineAnswer params.next =>
        DiagonalLineAnswer.restrictAtHeight params f x)

/-- Transport covariance for the answer-valued restricted diagonal-line
measurement. -/
private theorem restrictAnswerDiagonalAnswerMeasurement_transportInvariant
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    DiagonalAnswerMeasurementTransportInvariant params
      (restrictAnswerDiagonalAnswerMeasurement params strategy x) := by
  intro ℓ t
  apply ProjMeas.ext
  intro a
  have htransport :=
    MIPStarRE.LDT.DiagonalAnswerCovariantMeasurement.transportInvariant
      strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x) t
  let A := (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas
  let eNext := DiagonalLineAnswer.reparamAtEquiv (params := params.next) t
  let eSlice := DiagonalLineAnswer.reparamAtEquiv (params := params) t
  let f : DiagonalLineAnswer params.next → DiagonalLineAnswer params :=
    fun g => DiagonalLineAnswer.restrictAtHeight params g x
  have hcomm : ∀ g, f (eNext g) = eSlice (f g) := by
    intro g
    funext s
    rfl
  have hpost : postprocess (SubMeas.transport eNext A) f =
      SubMeas.transport eSlice (postprocess A f) :=
    SubMeas.postprocess_transport_equiv eNext eSlice A f f hcomm
  exact congrArg (fun M : SubMeas (DiagonalLineAnswer params) ι => M.outcome a) <| by
    simpa [restrictAnswerDiagonalAnswerMeasurement, DiagonalLine.transportMeasurement,
      ProjMeas.transport, Measurement.transport, A, eNext, eSlice, f,
      DiagonalLine.appendAtHeight_rebaseAt, htransport] using hpost

/-- Evaluating the answer-valued restricted diagonal measurement at the base point
recovers the ambient answer-valued diagonal readout. -/
@[simp] theorem restrictAnswerDiagonalAnswerMeasurement_postprocess_zero
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (ℓ : DiagonalLine params) :
    postprocess ((restrictAnswerDiagonalAnswerMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord) =
      postprocess
        ((strategy.diagonalMeasurement
          (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : DiagonalLineAnswer params.next => f zeroCoord) := by
  simp [restrictAnswerDiagonalAnswerMeasurement, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_comp, DiagonalLineAnswer.restrictAtHeight]
  rfl

/-- The `x`-restricted strategy of an answer-valued successor strategy.

Paper origin: `references/ldt-paper/inductive_step.tex:436-455`, in the
answer-valued strategy interface used for the recursive slice call.

This is the recursive restriction map needed for a simultaneous answer-valued
form of the main induction theorem.  It preserves the state, point
measurement, axis-parallel measurement, and full answer-valued diagonal
measurement on the slice. -/
noncomputable def xRestrictedAnswerSymStratOfAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) : AnswerSymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement :=
    (xRestrictedAnswerSymStrat params
      (answerSelfImprovementCarrier params.next strategy) x).axisParallelMeasurement
  diagonalMeasurement :=
    { toIdxProjMeas := restrictAnswerDiagonalAnswerMeasurement params strategy x
      transportInvariant := by
        exact restrictAnswerDiagonalAnswerMeasurement_transportInvariant params strategy x }

/-- Answer-valued slice restriction does not change the bipartite state. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_state
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).state = strategy.state :=
  rfl

/-- Answer-valued slice restriction reindexes point questions by appending the
slice height. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_pointMeasurement_apply
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (u : Point params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- Answer-valued slice restriction reuses the parent normalization witness. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_isNormalized
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).isNormalized =
      strategy.isNormalized :=
  rfl

/-- The diagonal measurement of an answer-valued slice is the full answer-valued
restriction of the ambient diagonal measurement. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_diagonalMeasurement_apply
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (ℓ : DiagonalLine params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalMeasurement ℓ =
      restrictAnswerDiagonalAnswerMeasurement params strategy x ℓ :=
  rfl

/-- Transport data for producing the answer-valued self-improvement data from
concrete per-slice symmetric strategies.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`; this is the answer-valued
restricted-slice interface for the same self-improvement step.

The answer-valued restriction `xRestrictedAnswerSymStrat` has the paper-faithful
answer-valued diagonal interface, while the existing Section 9 self-improvement
theorem is stated for ordinary `SymStrat`s.  This structure records the
stronger route through concrete ordinary slice strategies, together with the
state and point-measurement transports needed to move the resulting conclusions
back to the answer-valued restricted bookkeeping.

The legacy restricted strategy `xRestrictedStrategy` is not such an ordinary
slice strategy.  It is a `RestrictedSymStrat`, and its diagonal measurement is
only the degree-bounded re-embedding of the sampled base-point value.  Thus it
does not by itself supply the transport-covariant diagonal measurement required
by `SymStrat`.

An ordinary covariant realization is not a formal relabelling of the
answer-valued strategy.  Diagonal covariance after rebasing a line would force
the ordinary polynomial outcome to reproduce all values of the function answer,
not only the value at `zeroCoord` used by the diagonal test.  Thus this route
requires a genuine low-degree support/interpolation theorem for the
answer-valued diagonal measurement.  In the absence of such a theorem, the
mathematically faithful remaining target is an induction-section
self-improvement theorem stated directly for `AnswerSymStrat`.

The Section 9 analytic proof debt is not stored in this record.  The data record
constructor below calls the paper-facing theorem
`selfImprovementInInductionSection`; its proof applies the Section 9 theorem and
then transports the output estimates to the answer-valued induction notation. -/
structure AnswerSelfImprovementData.SliceStrategyTransport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) where
  /-- Concrete symmetric strategies realizing the answer-restricted slice interfaces. -/
  sliceStrategy : Fq params → SymStrat params ι
  /-- Each concrete slice strategy uses the ambient state. -/
  state_eq : ∀ x, (sliceStrategy x).state = strategy.state
  /-- Its point measurement agrees with the answer-valued restricted-slice point interface. -/
  pointMeasurement_eq :
    ∀ x,
      (sliceStrategy x).pointMeasurement =
        (xRestrictedAnswerSymStrat params strategy x).pointMeasurement
  /-- Its averaged point operator is the averaged slice point operator used by
  Section 6. -/
  averagedPoint_eq :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h
  /-- The concrete slice strategy is good with the answer-restricted failure profile. -/
  good :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)

/-- The averaged point-operator compatibility for answer-valued slices follows
from point-measurement transport.

Both sides unfold to the same average over `strategy.pointMeasurement
(appendPoint params u x)` once the concrete slice point measurement is identified
with `xRestrictedAnswerSymStrat`. -/
theorem AnswerSelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (sliceStrategy : Fq params → SymStrat params ι)
    (hpoint :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement) :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h := by
  intro x h
  simp [IdxPolyFamily.averagedPointEvaluationOperator,
    IdxPolyFamily.averagedSlicePointEvaluationOperator, hpoint x,
    xRestrictedAnswerSymStrat_pointMeasurement_apply]







/-- Convert the slice-wise outputs feeding the answer-valued restricted-strategy
self-improvement stage into the bookkeeping object expected by the answer-valued
successor-step construction.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`. -/
noncomputable def AnswerSelfImprovementData.ofSelfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (hslice :
      ∀ x,
        ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
          CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
            ((1 - inductionPkg.sliceError x) -
              answerSliceSelfImprovementError params restrictionPkg x) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params H.toSubMeas)
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          BipartiteSSCRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily H.toSubMeas)
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          SDDRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
            (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          tensorFailureExpectation strategy.state Z H.toSubMeas ≤
            answerSliceSelfImprovementError params restrictionPkg x ∧
          (∀ h : Polynomial params,
            IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z)) :
    AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  let sliceProj : Fq params → ProjSubMeas (Polynomial params) ι :=
    fun x => Classical.choose (hslice x)
  let sliceWitness : Fq params → MIPStarRE.Quantum.Op ι :=
    fun x => Classical.choose (Classical.choose_spec (hslice x))
  have hslice_props :
      ∀ x,
        CompletenessAtLeast strategy.state (sliceProj x).toSubMeas.liftLeft
          ((1 - inductionPkg.sliceError x) -
            answerSliceSelfImprovementError params restrictionPkg x) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas
            (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        BipartiteSSCRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (sliceProj x).toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (sliceProj x).toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (sliceProj x).toSubMeas))
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas ≤
          answerSliceSelfImprovementError params restrictionPkg x ∧
        (∀ h : Polynomial params,
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ sliceWitness x) := by
    intro x
    simpa [sliceProj, sliceWitness] using
      (Classical.choose_spec (Classical.choose_spec (hslice x)))
  exact
    { sliceProj := sliceProj
      sliceWitness := sliceWitness
      completeness := fun x => (hslice_props x).1
      pointConsistency := fun x => (hslice_props x).2.1
      strongSelfConsistency := fun x => (hslice_props x).2.2.1
      selfCloseness := fun x => (hslice_props x).2.2.2.1
      bounded := fun x => (hslice_props x).2.2.2.2.1
      dominatesAveragePointOperator := fun x h => (hslice_props x).2.2.2.2.2 h }



/-- The answer-valued restricted slices directly give the slice-wise Section 9
outputs once self-improvement is applied in its axis-parallel/self-consistency
form.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

The ordinary carrier used in the proof keeps the slice state, point
measurement, and axis-parallel measurement, and replaces only the diagonal
measurement by an inert covariant measurement.  This is sufficient because the
called self-improvement theorem consumes only the axis-parallel and point
self-consistency bounds. -/
theorem AnswerSelfImprovementData.slice_outputs_ofAnswerCarrier
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) :
    ∀ x,
      ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
          ((1 - inductionPkg.sliceError x) -
            answerSliceSelfImprovementError params restrictionPkg x) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas
            (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params H.toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        BipartiteSSCRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily H.toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        tensorFailureExpectation strategy.state Z H.toSubMeas ≤
          answerSliceSelfImprovementError params restrictionPkg x ∧
        (∀ h : Polynomial params,
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z) := by
  classical
  intro x
  let answerSlice := xRestrictedAnswerSymStrat params strategy x
  let carrier := answerSelfImprovementCarrier params answerSlice
  have haxis :
      carrier.axisParallelFailureProbability ≤ restrictionPkg.profile.axisParallel x := by
    have hfail :
        carrier.axisParallelFailureProbability =
          answerSlice.axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability
        AnswerSymStrat.axisParallelFailureProbability
        axisParallelPointAnswerFamily AnswerSymStrat.axisParallelPointAnswerFamily
        axisParallelLineAnswerFamily AnswerSymStrat.axisParallelLineAnswerFamily
      simp [carrier, answerSelfImprovementCarrier]
    simpa [hfail] using (restrictionPkg.profile.restrictedGood x).axisParallelTest
  have hself :
      carrier.selfConsistencyFailureProbability ≤
        restrictionPkg.profile.selfConsistency x := by
    have hfail :
        carrier.selfConsistencyFailureProbability =
          answerSlice.selfConsistencyFailureProbability := by
      unfold SymStrat.selfConsistencyFailureProbability
        AnswerSymStrat.selfConsistencyFailureProbability
      simp [carrier, answerSelfImprovementCarrier]
    simpa [hfail] using (restrictionPkg.profile.restrictedGood x).selfConsistencyTest
  have hconsCarrier :
      ConsRel carrier.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas carrier.pointMeasurement)
        (polynomialEvaluationFamily params (inductionPkg.sliceMeasurement x).toSubMeas)
        (inductionPkg.sliceError x) := by
    simpa [carrier, answerSelfImprovementCarrier, answerSlice] using
      inductionPkg.pointConsistency x
  rcases selfImprovementInInductionSection_of_axisParallel_selfConsistency
      params carrier
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (inductionPkg.sliceError x)
      haxis hself
      (inductionPkg.sliceMeasurement x)
      hconsCarrier with
    ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [carrier, answerSelfImprovementCarrier, answerSlice,
      answerSliceSelfImprovementError] using hH.completeness
  · simpa [carrier, answerSelfImprovementCarrier, answerSlice,
      answerSliceSelfImprovementError] using hH.pointConsistency
  · simpa [carrier, answerSelfImprovementCarrier, answerSlice,
      answerSliceSelfImprovementError] using hH.strongSelfConsistency
  · simpa [carrier, answerSelfImprovementCarrier, answerSlice,
      answerSliceSelfImprovementError] using hH.selfCloseness
  · simpa [carrier, answerSelfImprovementCarrier, answerSlice,
      answerSliceSelfImprovementError] using hH.bounded
  · intro h
    let sliceStrategy : Fq params → SymStrat params ι :=
      fun y => answerSelfImprovementCarrier params (xRestrictedAnswerSymStrat params strategy y)
    have havg_all :=
      AnswerSelfImprovementData.SliceStrategyTransport.averagedPoint_eq_of_pointMeasurement_eq
        params strategy sliceStrategy (by intro y; rfl)
    have havg :
        IdxPolyFamily.averagedPointEvaluationOperator carrier h =
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h := by
      simpa [sliceStrategy, carrier, answerSlice] using havg_all x h
    simpa [havg] using hH.dominatesAveragePointOperator h



/-- Construct the answer-valued Section 6 self-improvement data directly from
the answer-valued restricted slices.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

This removes the ordinary slice-realization assumption from the
self-improvement stage.  The construction uses the ordinary carrier only as a
device for invoking the Section 9 theorem in the form whose hypotheses are the
axis-parallel and point self-consistency estimates. -/
noncomputable def AnswerSelfImprovementData.ofAnswerCarrier
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) :
    AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  exact
    AnswerSelfImprovementData.ofSelfImprovementInInductionSection
      params strategy eps delta gamma k restrictionPkg inductionPkg
      (AnswerSelfImprovementData.slice_outputs_ofAnswerCarrier
        params strategy eps delta gamma k restrictionPkg inductionPkg)

end MIPStarRE.LDT.MainInductionStep

end

end LIDT


