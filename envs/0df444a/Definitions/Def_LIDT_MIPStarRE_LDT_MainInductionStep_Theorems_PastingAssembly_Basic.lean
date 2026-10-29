-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_Basic
-- name    : LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_Basic
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T13:23:45.769358+00:00
-- url     : https://prove2.me/theorems/3387ca81-36e8-4f53-be74-79d4399c0e54
-- title:
--   LIDT definitions: LDT / MainInductionStep / Theorems / PastingAssembly / Basic
-- statement:
--   This bundle provides the averaging interfaces used to assemble a pasted strategy on the induction side. It bounds the pasted error, supplies the small-error premise, and lifts slice-wise properties to indexed polynomial families.
--
--   Principal definitions:
--   - `ldPastingInInductionNu_le_fifth_mainInductionNu`: in the small-parameter regime, the pasted induction error is at most one fifth of `mainInductionNu`.
--   - `selfImprovementInInductionError_le_one_of_mainInductionError_lt_one`: a main-induction error below one implies the self-improvement error is at most one.
--   - `idxPolyFamily_averagedMass_eq_avg`: the mass of an averaged polynomial family equals the average of slice masses.
--   - `idxPolyFamily_complete_of_slice_bounds`: pointwise slice completeness implies completeness of the averaged family.
--   - `family_pointConsistencyError_eq_avg`: the point-consistency error of the family equals the corresponding slice average.
--   - `idxPolyFamily_stronglySelfConsistent_of_slice_bounds`: slice-wise left/right closeness implies strong self-consistency of the indexed family.
--   - `idxPolyFamily_sliceBoundednessInput_of_slice_bounds`: slice-wise boundedness supplies the boundedness input for the induction-section pasting theorem.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/Basic.lean#L30-L771

-- Generated from MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/Basic.lean by skeleton subtraction.
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
# Section 6 — Pasting Assembly: Averaged Family Fields

This module contains the scalar preliminary bound and the averaged family-field
lemmas used by the answer-valued successor route.
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Paper `inductive_step.tex:552-566`: in the small-parameter regime, the
induction-side `ldPastingInInductionNu` constructed from `ζ =
selfImprovementInInductionError` is bounded by `(1/5) · ν` where `ν =
mainInductionNu`. This bound discharges the first factor of the telescoping
derivation inside `assembleAveragedPastingData.error_le`. -/
lemma ldPastingInInductionNu_le_fifth_mainInductionNu
    (params : Parameters)
    [FieldModel params.q]
    (eps delta gamma : Error)
    (k : ℕ)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (heps_le_one : eps ≤ 1)
    (hdelta_le_one : delta ≤ 1)
    (hgamma_le : gamma ≤ 1)
    (hdq_le_q : params.d ≤ params.q) :
    ldPastingInInductionNu params k eps delta gamma
        (selfImprovementInInductionError params.next eps delta gamma) ≤
      (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma := by
  let zeta : Error := selfImprovementInInductionError params.next eps delta gamma
  let n : Error := (params.next.m : Error)
  let A : Error := Real.rpow eps (1 / (1024 : Error))
  let B : Error := Real.rpow delta (1 / (1024 : Error))
  let C : Error := Real.rpow gamma (1 / (1024 : Error))
  let D : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hratio_le_one := dq_ratio_le_one params hdq_le_q
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg heps_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg hdelta_nonneg _
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg hgamma_nonneg _
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact Real.rpow_nonneg hratio_nonneg _
  have heps32_le : Real.rpow eps (1 / (32 : Error)) ≤ A := by
    have htmp :
        Real.rpow eps (1 / (32 : Error)) ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' heps_nonneg heps_le_one
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [A] using htmp
  have hdelta32_le : Real.rpow delta (1 / (32 : Error)) ≤ B := by
    have htmp :
        Real.rpow delta (1 / (32 : Error)) ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' hdelta_nonneg hdelta_le_one
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [B] using htmp
  have hgamma32_le : Real.rpow gamma (1 / (32 : Error)) ≤ C := by
    have htmp :
        Real.rpow gamma (1 / (32 : Error)) ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' hgamma_nonneg hgamma_le
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [C] using htmp
  have hratio32_le :
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤ D := by
    have htmp :
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [D] using htmp
  have hn_two : (2 : Error) ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.succ_le_succ params.hm
  have hzeta32_le : Real.rpow zeta (1 / (32 : Error)) ≤ n * (A + B + D) := by
    let S : Error :=
      Real.rpow eps (1 / (32 : Error)) +
        Real.rpow delta (1 / (32 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      nlinarith [Real.rpow_nonneg heps_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))]
    have hSpow : Real.rpow S (1 / (32 : Error)) ≤ A + B + D := by
      have hsum12 :
          Real.rpow
              (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)))
              (1 / (32 : Error)) ≤
            Real.rpow (Real.rpow eps (1 / (32 : Error))) (1 / (32 : Error)) +
              Real.rpow (Real.rpow delta (1 / (32 : Error))) (1 / (32 : Error)) := by
        exact Real.rpow_add_le_add_rpow (Real.rpow_nonneg heps_nonneg _)
          (Real.rpow_nonneg hdelta_nonneg _)
          (by positivity) (by norm_num : (1 / (32 : Error)) ≤ 1)
      have hsum123 :
          Real.rpow
              ((Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
              (1 / (32 : Error)) ≤
            Real.rpow
                (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)))
                (1 / (32 : Error)) +
              Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
                (1 / (32 : Error)) := by
        exact Real.rpow_add_le_add_rpow
          (add_nonneg (Real.rpow_nonneg heps_nonneg _) (Real.rpow_nonneg hdelta_nonneg _))
          (Real.rpow_nonneg hratio_nonneg _)
          (by positivity) (by norm_num : (1 / (32 : Error)) ≤ 1)
      have heps_id : Real.rpow (Real.rpow eps (1 / (32 : Error))) (1 / (32 : Error)) = A := by
        dsimp [A]
        rw [← Real.rpow_mul heps_nonneg]
        congr 1
        norm_num
      have hdelta_id : Real.rpow (Real.rpow delta (1 / (32 : Error))) (1 / (32 : Error)) = B := by
        dsimp [B]
        rw [← Real.rpow_mul hdelta_nonneg]
        congr 1
        norm_num
      have hratio_id :
          Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
              (1 / (32 : Error)) = D := by
        dsimp [D]
        rw [← Real.rpow_mul hratio_nonneg]
        congr 1
        norm_num
      have hstep :
          Real.rpow S (1 / (32 : Error)) ≤
            (Real.rpow (Real.rpow eps (1 / (32 : Error))) (1 / (32 : Error)) +
                Real.rpow (Real.rpow delta (1 / (32 : Error))) (1 / (32 : Error))) +
              Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
                (1 / (32 : Error)) := by
        have hsum123' :
            Real.rpow S (1 / (32 : Error)) ≤
              Real.rpow
                  (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)))
                  (1 / (32 : Error)) +
                Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
                  (1 / (32 : Error)) := by
          simpa [S, add_assoc] using hsum123
        nlinarith [hsum12, hsum123']
      rw [heps_id, hdelta_id, hratio_id] at hstep
      simpa [add_assoc, add_left_comm, add_comm] using hstep
    have hcoeff_bound : Real.rpow (3000 * n) (1 / (32 : Error)) ≤ n := by
      have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : Error) < 2) hn_two
      have hpow31 : (3000 : Error) ≤ n ^ (31 : ℕ) := by
        have htwo31 : (3000 : Error) ≤ (2 : Error) ^ (31 : ℕ) := by norm_num
        have hmono : (2 : Error) ^ (31 : ℕ) ≤ n ^ (31 : ℕ) := by
          gcongr
        exact le_trans htwo31 hmono
      have hcoeff_le_pow : 3000 * n ≤ n ^ (32 : ℕ) := by
        have hmul := mul_le_mul_of_nonneg_right hpow31 (by positivity : 0 ≤ n)
        calc
          3000 * n ≤ (n ^ (31 : ℕ)) * n := hmul
          _ = n ^ (32 : ℕ) := by ring_nf
      calc
        Real.rpow (3000 * n) (1 / (32 : Error)) ≤
            Real.rpow (n ^ (32 : ℕ)) (1 / (32 : Error)) := by
              exact Real.rpow_le_rpow (by positivity) hcoeff_le_pow (by positivity)
        _ = n := by
              have hn_nonneg : 0 ≤ n := le_trans (by norm_num : (0 : Error) ≤ 2) hn_two
              calc
                Real.rpow (n ^ (32 : ℕ)) (1 / (32 : Error))
                    = Real.rpow (Real.rpow n (32 : Error)) (1 / (32 : Error)) := by
                        rw [show (n ^ (32 : ℕ)) = Real.rpow n (32 : Error) by
                              symm
                              exact Real.rpow_natCast n 32]
                _ = Real.rpow n ((32 : Error) * (1 / (32 : Error))) := by
                        symm
                        exact Real.rpow_mul hn_nonneg (32 : Error) (1 / (32 : Error))
                _ = n := by
                        norm_num
    calc
      Real.rpow zeta (1 / (32 : Error))
          = Real.rpow (3000 * n * S) (1 / (32 : Error)) := by
              dsimp [zeta, n, S]
              simp [selfImprovementInInductionError]
      _ = Real.rpow (3000 * n) (1 / (32 : Error)) * Real.rpow S (1 / (32 : Error)) := by
            calc
              Real.rpow (3000 * n * S) (1 / (32 : Error))
                  = Real.rpow ((3000 * n) * S) (1 / (32 : Error)) := by ring_nf
              _ = Real.rpow (3000 * n) (1 / (32 : Error)) * Real.rpow S (1 / (32 : Error)) := by
                    simpa using (Real.mul_rpow (by positivity : 0 ≤ 3000 * n) hS_nonneg :
                      Real.rpow ((3000 * n) * S) (1 / (32 : Error)) =
                        Real.rpow (3000 * n) (1 / (32 : Error)) * Real.rpow S (1 / (32 : Error)))
      _ ≤ Real.rpow (3000 * n) (1 / (32 : Error)) * (A + B + D) := by
            have hcoeff_nonneg : 0 ≤ Real.rpow (3000 * n) (1 / (32 : Error)) := by
              exact Real.rpow_nonneg (by positivity) _
            exact mul_le_mul_of_nonneg_left hSpow hcoeff_nonneg
      _ ≤ n * (A + B + D) := by
            have habd_nonneg : 0 ≤ A + B + D := by
              nlinarith [hA_nonneg, hB_nonneg, hD_nonneg]
            exact mul_le_mul_of_nonneg_right hcoeff_bound habd_nonneg
  have hzeta32_le' : Real.rpow zeta (1 / (32 : Error)) ≤ n * (A + B + C + D) := by
    have habd_le : A + B + D ≤ A + B + C + D := by
      nlinarith [hC_nonneg]
    exact le_trans hzeta32_le (by gcongr)
  have hsum_noz :
      Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)) +
          Real.rpow gamma (1 / (32 : Error)) +
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
        A + B + C + D := by
    nlinarith [heps32_le, hdelta32_le, hgamma32_le, hratio32_le]
  have hsum_nonneg : 0 ≤ A + B + C + D := by
    nlinarith [hA_nonneg, hB_nonneg, hC_nonneg, hD_nonneg]
  have hsum_le :
      Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)) +
          Real.rpow gamma (1 / (32 : Error)) + Real.rpow zeta (1 / (32 : Error)) +
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
        (2 * n) * (A + B + C + D) := by
    have hone_plus_n : (1 : Error) + n ≤ 2 * n := by
      nlinarith [hn_two]
    nlinarith [hsum_noz, hzeta32_le', hsum_nonneg, hone_plus_n]
  calc
    ldPastingInInductionNu params k eps delta gamma zeta
      = 100 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          dsimp [zeta]
          simp [ldPastingInInductionNu]
    _ ≤ 100 * ((k : Error) ^ (2 : ℕ)) * n * ((2 * n) * (A + B + C + D)) := by
          let sum32 : Error :=
            Real.rpow eps (1 / (32 : Error)) +
              Real.rpow delta (1 / (32 : Error)) +
              Real.rpow gamma (1 / (32 : Error)) +
              Real.rpow zeta (1 / (32 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
          have hm_le_n : (params.m : Error) ≤ n := by
            dsimp [n]
            exact_mod_cast Nat.le_succ params.m
          have heps32_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
            Real.rpow_nonneg heps_nonneg (1 / (32 : Error))
          have hdelta32_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
            Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error))
          have hgamma32_nonneg : 0 ≤ Real.rpow gamma (1 / (32 : Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (32 : Error))
          have hzeta_nonneg : 0 ≤ zeta := by
            dsimp [zeta]
            have hratio32_nonneg' :
                0 ≤ Real.rpow
                  (((params.next.d : Error) / (params.next.q : Error)))
                  (1 / (32 : Error)) :=
              Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
            have hsum_nonneg' :
                0 ≤ Real.rpow eps (1 / (32 : Error)) +
                      Real.rpow delta (1 / (32 : Error)) +
                      Real.rpow
                        (((params.next.d : Error) / (params.next.q : Error)))
                        (1 / (32 : Error)) := by
              exact add_nonneg (add_nonneg heps32_nonneg hdelta32_nonneg) hratio32_nonneg'
            unfold selfImprovementInInductionError
            exact mul_nonneg (by positivity) hsum_nonneg'
          have hzeta32_nonneg : 0 ≤ Real.rpow zeta (1 / (32 : Error)) :=
            Real.rpow_nonneg hzeta_nonneg (1 / (32 : Error))
          have hratio32_nonneg :
              0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
            Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
          have hsum32_nonneg : 0 ≤ sum32 := by
            dsimp [sum32]
            exact add_nonneg
              (add_nonneg
                (add_nonneg
                  (add_nonneg heps32_nonneg hdelta32_nonneg)
                  hgamma32_nonneg)
                hzeta32_nonneg)
              hratio32_nonneg
          have hinner : (params.m : Error) * sum32 ≤ n * ((2 * n) * (A + B + C + D)) := by
            have hstep₁ : (params.m : Error) * sum32 ≤ n * sum32 := by
              exact mul_le_mul_of_nonneg_right hm_le_n hsum32_nonneg
            have hstep₂ : n * sum32 ≤ n * ((2 * n) * (A + B + C + D)) := by
              exact mul_le_mul_of_nonneg_left hsum_le (by positivity : 0 ≤ n)
            exact le_trans hstep₁ hstep₂
          simpa [sum32, mul_assoc] using
            (mul_le_mul_of_nonneg_left hinner
              (by positivity : 0 ≤ 100 * ((k : Error) ^ (2 : ℕ))))
    _ = (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma := by
          dsimp [n, A, B, C, D]
          simp [mainInductionNu]
          ring

/-- The nontrivial main-induction branch supplies the scalar side condition
`ζ ≤ 1` needed by the averaged pasting assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:486-551`, where the
small-error branch is the one in which the averaged self-improvement and
pasting estimates are used. -/
lemma selfImprovementInInductionError_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error}
    {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    selfImprovementInInductionError params.next eps delta gamma ≤ 1 := by
  have heps_le_one :
      eps ≤ 1 := eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hdelta_le_one :
      delta ≤ 1 := delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
  have hdq_le_q :
      params.d ≤ params.q := dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall
  have hzeta_le_nu :
      selfImprovementInInductionError params.next eps delta gamma ≤
        mainInductionNu params.next k eps delta gamma :=
    selfImprovementInInductionError_le_mainInductionNu
      params strategy eps delta gamma k hgood hsmall heps_le_one hdelta_le_one hdq_le_q
  have hnu_lt_one :
      mainInductionNu params.next k eps delta gamma < 1 :=
    mainInductionNu_lt_one_of_mainInductionError_lt_one
      params.next k eps delta gamma hsmall
  exact le_trans hzeta_le_nu (le_of_lt hnu_lt_one)







/-- The mass of the averaged polynomial family is the average of the masses of
the slice measurements.

This is the linearity calculation underlying the completeness part of the
averaged pasting assembly. -/
lemma idxPolyFamily_averagedMass_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) :
    subMeasMass ψ family.averagedSubMeas.liftLeft =
      avgOver (uniformDistribution (Fq params))
        (fun x => subMeasMass ψ ((family.meas x).toSubMeas.liftLeft)) := by
  simp only [subMeasMass, IdxPolyFamily.averagedSubMeas, SubMeas.liftLeft,
    mkLeftPlacedSubMeas_total, averageIdxSubMeas]
  exact ev_leftTensor_averageOperatorOverDistribution ψ (uniformDistribution (Fq params))
    (fun x => (family.meas x).toSubMeas.total)

/-- Averaged completeness of a slice-indexed polynomial family from pointwise
slice completeness.

This is the completeness component of the Section 6 averaging argument.  The
statement is family-level: it does not mention diagonal measurements, and hence
can be reused in the answer-valued successor route. -/
lemma idxPolyFamily_complete_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (sliceError sliceSelfError : Fq params → Error)
    (hcomplete :
      ∀ x,
        CompletenessAtLeast ψ ((family.meas x).toSubMeas.liftLeft)
          ((1 - sliceError x) - sliceSelfError x)) :
    family.Complete ψ
      (avgOver (uniformDistribution (Fq params)) sliceError +
        avgOver (uniformDistribution (Fq params)) sliceSelfError) := by
  classical
  let 𝒟 : Distribution (Fq params) := uniformDistribution (Fq params)
  refine ⟨?_⟩
  refine ⟨?_⟩
  have hmass_eq := idxPolyFamily_averagedMass_eq_avg params ψ family
  have havg_lower :
      1 - (avgOver 𝒟 sliceError + avgOver 𝒟 sliceSelfError) ≤
        avgOver 𝒟
          (fun x => subMeasMass ψ ((family.meas x).toSubMeas.liftLeft)) := by
    have hconst1 : avgOver 𝒟 (fun _ : Fq params => (1 : Error)) = 1 := by
      simpa [𝒟] using (avgOver_uniform_const (α := Fq params) (1 : Error))
    have hnegErr : avgOver 𝒟 (fun a => -sliceError a) = -avgOver 𝒟 sliceError := by
      simpa [avgOver_const_mul] using (avgOver_const_mul 𝒟 (-1) sliceError)
    have hnegZeta :
        avgOver 𝒟 (fun a => -sliceSelfError a) = -avgOver 𝒟 sliceSelfError := by
      simpa [avgOver_const_mul] using (avgOver_const_mul 𝒟 (-1) sliceSelfError)
    calc
      1 - (avgOver 𝒟 sliceError + avgOver 𝒟 sliceSelfError) =
          avgOver 𝒟 (fun x => (1 - sliceError x) - sliceSelfError x) := by
            rw [show (fun x => (1 - sliceError x) - sliceSelfError x) =
                fun x => 1 + (-sliceError x) + (-sliceSelfError x) by
                funext x
                ring]
            rw [avgOver_add, avgOver_add, hconst1, hnegErr, hnegZeta]
            ring
      _ ≤ avgOver 𝒟
          (fun x => subMeasMass ψ ((family.meas x).toSubMeas.liftLeft)) := by
            apply avgOver_mono
            intro x
            exact (hcomplete x).lowerBound
  rw [hmass_eq]
  exact havg_lower

lemma family_pointConsistencyError_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    {hrestrict : SliceRestrictionData params strategy eps delta gamma}
    {hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k}
    (hself : SelfImprovementData params strategy eps delta gamma k hrestrict hinduction) :
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint hself.family) =
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params (hself.sliceProj x).toSubMeas)) := by
  let g : Point params.next → Error := fun u =>
    qBipartiteConsDefect strategy.state
      ((strategy.pointMeasurement u).toSubMeas)
      ((IdxPolyFamily.evaluatedAtNextPoint hself.family) u)
  calc
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint hself.family)
      = avgOver (uniformDistribution (Point params.next)) g := by
          rfl
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
          exact CommutativityPoints.avgOver_uniform_pointNext_decompose params g
    _ = avgOver (uniformDistribution (Fq params))
          (fun x =>
            bipartiteConsError strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
              (polynomialEvaluationFamily params (hself.sliceProj x).toSubMeas)) := by
          unfold bipartiteConsError
          refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro x; refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro u
          simp [g, IdxPolyFamily.evaluatedAtNextPoint, polynomialEvaluationFamily,
            IdxProjMeas.toIdxSubMeas]







/-- Average slice-wise left/right closeness into strong self-consistency of the
slice-indexed family.

This is the strong self-consistency component of the Section 6 averaging
argument.  It depends only on the state and the slice measurements, not on the
diagonal part of a strategy. -/
lemma idxPolyFamily_stronglySelfConsistent_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (sliceError : Fq params → Error)
    (zeta : Error)
    (hself :
      ∀ x,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (family.meas x).toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (family.meas x).toSubMeas))
          (sliceError x))
    (havg : avgOver (uniformDistribution (Fq params)) sliceError ≤ zeta) :
    family.StronglySelfConsistent ψ zeta := by
  refine ⟨?_⟩
  refine ⟨?_⟩
  have hpointwise :
      ∀ x,
        qSDD ψ ((family.meas x).toSubMeas.liftLeft)
          ((family.meas x).toSubMeas.liftRight) ≤ sliceError x := by
    intro x
    simpa [sddError, avgOver_uniform_const, constSubMeasFamily,
      SubMeas.liftLeft, SubMeas.liftRight, leftPlacedSubMeas, rightPlacedSubMeas] using
      (hself x).squaredDistanceBound
  calc
    sddError ψ (uniformDistribution (Fq params))
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
        (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      = avgOver (uniformDistribution (Fq params))
          (fun x =>
            qSDD ψ ((family.meas x).toSubMeas.liftLeft)
              ((family.meas x).toSubMeas.liftRight)) := by
            rfl
    _ ≤ avgOver (uniformDistribution (Fq params)) sliceError := by
          exact avgOver_mono (uniformDistribution (Fq params)) _ _ hpointwise
    _ ≤ zeta := havg

/-- Average slice-wise boundedness into the boundedness input used by the
induction-section pasting theorem.

This is the boundedness component of the Section 6 averaging argument for an
ordinary successor strategy.  The hypotheses are exactly the slice-wise
residual estimate and the paper domination condition
`E_u A^{u,x}_{g(u)} <= Z^x`.

**Lean-only:** This is an internal adapter for the induction-section pasting
interface, tracked in issue #1507.  Paper origin:
`references/ldt-paper/inductive_step.tex:461-551`.  Discharge: proved here by
averaging the slice-wise boundedness estimates and the domination condition. -/
lemma idxPolyFamily_sliceBoundednessInput_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (sliceError : Fq params → Error)
    (zeta : Error)
    (hbounded :
      ∀ x,
        tensorFailureExpectation strategy.state (family.witness x)
          (family.meas x).toSubMeas ≤ sliceError x)
    (havg : avgOver (uniformDistribution (Fq params)) sliceError ≤ zeta)
    (hdom :
      ∀ x, ∀ g : Polynomial params,
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x) :
    IdxPolyFamily.SliceBoundednessInput strategy family zeta := by
  classical
  refine
    { sliceOpPSD := ?_
      sliceBoundedness := ?_
      sliceDominatesAveragedPoint := hdom }
  · intro x
    let g0 : Polynomial params :=
      Classical.choice (inferInstance : Nonempty (Polynomial params))
    have htarget_nonneg :
        0 ≤ IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g0 := by
      unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
      exact Finset.sum_nonneg fun u hu =>
        smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
          ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome_pos (g0 u))
    exact le_trans htarget_nonneg (hdom x g0)
  · have hswap :
        avgOver (uniformDistribution (Fq params))
            (fun x =>
              ev strategy.state
                (leftTensor (ι₂ := ι) (1 - (family.meas x).toSubMeas.total) *
                  rightTensor (ι₁ := ι) (family.witness x))) =
          avgOver (uniformDistribution (Fq params))
            (fun x =>
              tensorFailureExpectation strategy.state (family.witness x)
                (family.meas x).toSubMeas) := by
      apply avgOver_congr
      intro x
      simpa [tensorFailureExpectation, leftTensor_mul_rightTensor_eq_opTensor] using
        (ev_opTensor_swap_of_density_fixed strategy.state
          strategy.permInvState.density_swap
          (1 - (family.meas x).toSubMeas.total) (family.witness x))
    rw [hswap]
    calc
      avgOver (uniformDistribution (Fq params))
          (fun x =>
            tensorFailureExpectation strategy.state (family.witness x)
              (family.meas x).toSubMeas)
        ≤ avgOver (uniformDistribution (Fq params)) sliceError := by
            exact avgOver_mono (uniformDistribution (Fq params)) _ _ hbounded
      _ ≤ zeta := havg

end MIPStarRE.LDT.MainInductionStep

end

end LIDT


