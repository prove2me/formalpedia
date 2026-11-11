-- Prove2me | Definitions.Def_OAIQ254M003
-- name    : OAIQ254M003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:49:40.809534+00:00
-- url     : https://prove2.me/theorems/ff1ccdb5-b8b1-453a-9a1e-6f5f9984ffe9
-- title:
--   Definitions bundle OAIQ254M003 of the split of OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2828 declarations of OpenAI's Lean: 2716 definitions, 2 inductive types or structures, 1 instance and 109 theorems. The definitions and types are `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.logNormalizer`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.orderTotal`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.potential`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupBranchDesignation.nativeBranchDesignated`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.Class`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.Letter`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.Symbol`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.classDesignated`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.classLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.conditionalCount`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.projectedStatistic`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.uniformCompatible`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.childWeight`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.halfLawAt`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.orderPairMixture`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.placedPairMixture`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.statisticComplement`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.supportedHalfLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupDegree`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupTargetRate.groupEntropyRate`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.GroupAssignment.product`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.activeEquivOrders`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.leftChildLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.rightClassChildLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryGroupMasks.projectRaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryGroupedRecovery.groupedAssignment`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryGroupedRecovery.localAssigned`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryGroupedRecovery.projectTarget`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMaskLaws.parentCenter`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMaskLaws.stageBActive`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRecovery.sideWeights`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistorySource.Raw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistorySource.deleteWithPred`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistorySource.marginal`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryStageCIncoming.stageCActive`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistorySupport.fixedBaseLength`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistorySupport.supportRate`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.coarseTripleFintype`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.entropySumBall`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.finSumBall` and 2678 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixFields_CapacityA_CapA1_1_14I0`, `MatrixFields_CapacityA_CapA1_1_14I1`, `MatrixFields_CapacityA_CapA1_1_14I2`, `MatrixFields_CapacityA_CapA1_2_13I0`, `MatrixFields_CapacityA_CapA1_2_13I1`, `MatrixFields_CapacityA_CapA1_2_13I2`, `MatrixFields_CapacityA_CapA1_3_12I0`, `MatrixFields_CapacityA_CapA1_3_12I1`, `MatrixFields_CapacityA_CapA1_3_12I2`, `MatrixFields_CapacityA_CapA1_4_11I0`, `MatrixFields_CapacityA_CapA1_4_11I1`, `MatrixFields_CapacityA_CapA1_4_11I2`, `MatrixFields_CapacityA_CapA1_5_10I0`, `MatrixFields_CapacityA_CapA1_5_10I1`, `MatrixFields_CapacityA_CapA1_5_10I2`, `MatrixFields_CapacityA_CapA1_5_10I2Pair`, `MatrixFields_Certificates_CertificatesReplay`, `MatrixFields_Certificates_Four0_1_7`, `MatrixFields_Certificates_Four0_3_5`, `MatrixFields_Certificates_Four0_4_4`, `MatrixFields_Certificates_Four1_0_7`, `MatrixFields_Certificates_LittleB1_3_4`, `MatrixFields_Certificates_LittleB1_4_3`, `MatrixFields_Certificates_LittleB1_5_2`, `MatrixFields_Certificates_LittleB2_3_3`, `MatrixFields_Certificates_LittleB2_5_1`, `MatrixFields_Certificates_NativeInterior`, `MatrixFields_Certificates_SparseContraction`, `MatrixFields_Certificates_SplitA1_1_14`, `MatrixFields_Certificates_SplitA1_3_12`, `MatrixFields_Certificates_SplitA1_4_11`, `MatrixFields_Certificates_SplitA1_7_8`, `MatrixFields_Certificates_SplitA2_2_12`, `MatrixFields_Certificates_SplitA2_3_11`, `MatrixFields_Certificates_SplitA2_4_10`, `MatrixFields_Certificates_SplitA2_5_9`, `MatrixFields_Certificates_SplitA2_6_8`, `MatrixFields_Certificates_SplitA2_7_7`, `MatrixFields_Certificates_SplitA3_3_10`, `MatrixFields_Certificates_SplitA3_4_9`, `MatrixFields_Certificates_SplitA3_5_8`, `MatrixFields_Certificates_SplitA3_6_7`, `MatrixFields_Certificates_SplitA4_5_7`, `MatrixFields_Certificates_SplitA4_6_6`, `MatrixFields_Certificates_SplitB1_1_6`, `MatrixFields_Certificates_SplitB1_3_4`, `MatrixFields_Certificates_SplitB2_3_3`, `MatrixFields_Certificates_SplitB5_1_2`, `MatrixFields_Certificates_SupportedContraction`, `MatrixFields_Certificates_Terminal1_1_6`, `MatrixFields_Certificates_Terminal1_2_5`, `MatrixFields_Certificates_Terminal1_3_4`, `MatrixFields_Certificates_Terminal1_4_3`, `MatrixFields_Certificates_Terminal1_5_2`, `MatrixFields_Certificates_Terminal1_6_1`, `MatrixFields_Certificates_Terminal2_1_5`, `MatrixFields_Certificates_Terminal2_2_4`, `MatrixFields_Certificates_Terminal2_3_3`, `MatrixFields_Certificates_Terminal2_4_2`, `MatrixFields_Certificates_Terminal2_5_1`, `MatrixFields_Certificates_Terminal3_1_4`, `MatrixFields_Certificates_Terminal3_2_3`, `MatrixFields_Certificates_Terminal3_3_2`, `MatrixFields_Certificates_Terminal3_4_1`, `MatrixFields_Certificates_Terminal4_1_3`, `MatrixFields_Certificates_Terminal4_2_2`, `MatrixFields_Certificates_Terminal4_3_1`, `MatrixFields_Certificates_Terminal5_1_2`, `MatrixFields_Certificates_Terminal5_2_1`, `MatrixFields_Certificates_Zero0_1_7`, `MatrixFields_Construction_ComplexPolynomialWitnessProduct`, `MatrixFields_Construction_ComplexRectangularASI`, `MatrixFields_Construction_GroupAmbientDegree`, `MatrixFields_Construction_GroupBranchDesignation`, `MatrixFields_Construction_InitialFamily`, `MatrixFields_Construction_JointCanonicalMixed`, `MatrixFields_Construction_JointCompatibilityIncidence`, `MatrixFields_Construction_JointCompatibilityScaling`, `MatrixFields_Construction_JointGibbsApproximation`, `MatrixFields_Construction_JointMarginalSupport`, `MatrixFields_Construction_JointMaskedAssignment`, `MatrixFields_Entropy_FiniteAverage`, `MatrixFields_Entropy_GroupBranchLaws`, `MatrixFields_Entropy_GroupProjectedEntropy`, `MatrixFields_Entropy_InitialLeafRates`, `MatrixFields_Entropy_JointAmbientEntropy`, `MatrixFields_Entropy_JointCompatibilityEntropyBound`, `MatrixFields_Entropy_JointCompatibilityRateLimit`, `MatrixFields_Entropy_JointMaskedRates`, `MatrixFields_Entropy_NativeLaws`, `MatrixFields_Entropy_ParametersHalfLaws`, `MatrixFields_Entropy_StageCLaw`, `MatrixFields_Entropy_ZeroLeafRateFormula`, `MatrixFields_Extraction_GroupPairWindows`, `MatrixFields_Extraction_JointMaskedGoodSelection`, `MatrixFields_Extraction_JointMaskedSelection`, `MatrixFields_Extraction_JointPairClassWindows`, `MatrixFields_Extraction_JointTypeCounts`, `MatrixFields_Histories_CWShapePhysicalPermutation`, `MatrixFields_Histories_GroupOrbitCount`, `MatrixFields_Histories_HistoryChildLaws`, `MatrixFields_Histories_HistoryGroupCore`, `MatrixFields_Histories_HistoryIteration`, `MatrixFields_Histories_HistoryPositions`, `MatrixFields_Histories_HistoryRecovery`, `MatrixFields_Histories_HistoryRecoveryBudget`, `MatrixFields_Histories_HistorySourceAssignment`, `MatrixFields_Histories_InheritedMaskMargins`, `MatrixFields_Histories_InverseLinearRecovery`, `MatrixFields_Histories_JointScalarOrbitAdmissibility`, `MatrixFields_Parameters_JointOrdinaryPopulationSelection`, `MatrixFields_Parameters_JointPopulationMixedCompatibility`, `MatrixFields_Parameters_StageCCapacity`, `MatrixFields_Tensors_CWCompleteStatistics`, `MatrixFields_Tensors_CWStageCStatistics`, `MatrixFields_Tensors_CWStrandCompatibility`, `MatrixFields_Tensors_ComplexDotPairing`, `MatrixFields_Tensors_TerminalRelabel`.
--
--   **Imports.** It imports the bundles `OAIQ254M000` and `OAIQ254M001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ254M007`, `OAIQ254M008`, `OAIQ254M009`, `OAIQ254M010` and `OAIQ254M011`; the statements `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialDenominatorBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialRawBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.nativeH0_enclosed`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.weight_enclosed_10`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.weight_enclosed_11`, `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.checkLog_sound`, `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.entropyLookup_sound`, `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.eventually_exists_selection_of_word_support`, `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree_log_upper_of_word_support`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_4_11Den_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_4_11Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_4_11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_6_9Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_6_9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Law_check`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Den_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_3_11Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_3_11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_4_10Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_6_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_7_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_3_10Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_5_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_6_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_4_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_5_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_6_6Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A5_5_6Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.AProbsTable_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_3_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_2_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_3_1Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_6_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_1_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Ttotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U0_2_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U0_2_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_0_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_0_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_2_0ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_2_0EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Ttotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U0_2_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U0_2_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_0_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_0_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_2_0ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_2_0EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_2_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_3_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_2_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I2Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_7_1Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_8_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_0_7Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_7_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_6_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_0_5Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_5_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_0_4Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_4_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_0_3Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_3_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z6_0_2Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z6_2_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z7_0_1Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z8_0_0Four_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.fourRateBalls_sound`; the proofs of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkLog_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.eventually_nonempty`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialDenominatorBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialRawBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.nativeH0_enclosed`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.weight_enclosed_10`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.weight_enclosed_11`, `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.checkLog_sound`, `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.entropyLookup_sound`, `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.normalized_sound`, `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.eventually_exists_selection_of_word_support`, `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree_log_upper_of_word_support`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_4_11Den_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_4_11Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_4_11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_6_9Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_6_9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Law_check`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Den_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_3_11Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_3_11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_4_10Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_6_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_7_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_3_10Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_5_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_6_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_4_8Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_5_7Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_6_6Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A5_5_6Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.AProbsTable_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_3_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_2_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_3_1Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_6_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_1_5Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Ttotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U0_2_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U0_2_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_0_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_0_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_2_0ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_2_0EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Ttotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U0_2_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U0_2_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_0_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_0_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_2_0ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_2_0EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_2_2Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_3_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_2_1Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_0_16`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_1_15`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_2_14`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_3_13`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_4_12`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_5_11`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_6_10`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_1_14`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_2_13`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_3_12`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_4_11`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_5_10` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_sound`.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/LinearAlgebra at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ254M000
import Definitions.Def_OAIQ254M001

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_ComplexDotPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def contract (T : Tensor K X Y Z) [Fintype X] [Fintype Y]
    (a : X → K) (b : Y → K) : Z → K :=
  fun z => ∑ x, ∑ y, T x y z * a x * b y

end Algebra

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointMaskedSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.JointHashing

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {P R : Type*} [Fintype P] [CommRing R]

def survivalEquiv (U : Set R) (I J : P → R) :
    {s : Sample P R // Survives U I J s} ≃ (P → R) × U where
  toFun s := (s.val.1, ⟨xHash s.val I, s.property.2⟩)
  invFun vt := ⟨(vt.1, vt.2.val - dot vt.1 I, vt.2.val - dot vt.1 J), by
    simp [Survives, xHash, yHash, vt.2.property]⟩
  left_inv s := by
    apply Subtype.ext
    rcases s with ⟨⟨v, a, b⟩, hs⟩
    dsimp [Survives, xHash, yHash] at hs ⊢
    congr 1
    apply Prod.ext
    · ring
    · linear_combination hs.1
  right_inv vt := by
    rcases vt with ⟨v, t, ht⟩
    simp [xHash]

@[simp] theorem dot_pivot [DecidableEq P] (d : P → R) (i : P)
    (u : Rˣ) (hu : d i = u) (t : R) : dot (pivot i u t) d = t := by
  simp [dot, pivot, Pi.single_apply, hu, mul_comm, mul_left_comm]

def linearSplitEquiv [DecidableEq P] (d : P → R) (i : P)
    (u : Rˣ) (hu : d i = u) :
    (P → R) ≃ R × {v : P → R // dot v d = 0} where
  toFun v := (dot v d, ⟨v - pivot i u (dot v d), by simp [hu]⟩)
  invFun t := t.2.val + pivot i u t.1
  left_inv v := by simp
  right_inv t := by
    rcases t with ⟨t, v, hv⟩
    apply Prod.ext
    · simp [hv, hu]
    · apply Subtype.ext
      simp [hv, hu]

def collisionEquiv (U : Set R) (I J d : P → R) :
    {s : Sample P R // Survives U I J s ∧ dot s.1 d = 0} ≃
      {v : P → R // dot v d = 0} × U where
  toFun s := (⟨s.val.1, s.property.2⟩, ⟨xHash s.val I, s.property.1.2⟩)
  invFun vt := ⟨(vt.1.val, vt.2.val - dot vt.1.val I, vt.2.val - dot vt.1.val J), by
    exact ⟨by simp [Survives, xHash, yHash, vt.2.property], vt.1.property⟩⟩
  left_inv s := by
    apply Subtype.ext
    exact congrArg (fun t : {s : Sample P R // Survives U I J s} => t.val)
      ((survivalEquiv U I J).left_inv ⟨s.val, s.property.1⟩)
  right_inv vt := by
    rcases vt with ⟨⟨v, hv⟩, ⟨t, ht⟩⟩
    simp [xHash]

end MatrixMultiplication.JointHashing





noncomputable section






namespace MatrixMultiplication.JointMaskedSelection

open JointCoarseHashing JointExtractionRates

attribute [local instance] Classical.propDecidable

variable {P E O V : Type*}

namespace OrbitData

section Finite

variable [Fintype P]

theorem good_eligibility (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) (s : Sample P k)
    (hg : d.Good k U N e s) : d.eligibilityGood k U e s := by
  by_contra h
  exact hg.2 (Or.inl h)

end Finite

end OrbitData

end MatrixMultiplication.JointMaskedSelection

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_TerminalRelabel
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

theorem matrixCoefficients_cyclic [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (x : B × C) (y : C × A) (z : A × B) :
    matrixCoefficients (K := K) A B C z x y = matrixCoefficients B C A x y z := by
  have h : (z.2 = x.1 ∧ x.2 = y.1 ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩
  simp only [matrixCoefficients, h]

end Tensor






namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

theorem directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (T : ι → Tensor K X Y Z) (S : κ → Tensor K U V W) :
    pullback (directSumProductEquiv ι κ X U)
      (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
      (product (directSum T) (directSum S)) =
      directSum (fun i : ι × κ => product (T i.1) (S i.2)) := by
  funext x y z
  change
    (if x.1.1 = y.1.1 ∧ x.1.1 = z.1.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 else 0) *
    (if x.1.2 = y.1.2 ∧ x.1.2 = z.1.2 then
      S x.1.2 x.2.2 y.2.2 z.2.2 else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 * S x.1.2 x.2.2 y.2.2 z.2.2 else 0
  have hguard : (x.1 = y.1 ∧ x.1 = z.1) ↔
      (x.1.1 = y.1.1 ∧ x.1.1 = z.1.1) ∧
      (x.1.2 = y.1.2 ∧ x.1.2 = z.1.2) := by
    constructor
    · intro h
      exact ⟨⟨congrArg Prod.fst h.1, congrArg Prod.fst h.2⟩,
        ⟨congrArg Prod.snd h.1, congrArg Prod.snd h.2⟩⟩
    · intro h
      exact ⟨Prod.ext h.1.1 h.2.1, Prod.ext h.1.2 h.2.2⟩
  by_cases hi : x.1.1 = y.1.1 ∧ x.1.1 = z.1.1
  · by_cases hk : x.1.2 = y.1.2 ∧ x.1.2 = z.1.2
    · simp only [ite_eq_left hi, ite_eq_left hk, ite_eq_left (hguard.mpr ⟨hi, hk⟩)]
    · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hk (hguard.mp h).2
      simp only [ite_eq_left hi, ite_eq_right hk, ite_eq_right hfull, mul_zero]
  · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hi (hguard.mp h).1
    simp only [ite_eq_right hi, ite_eq_right hfull, zero_mul]

theorem cyclic_directSum {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    cyclic (directSum T) = directSum (fun i => cyclic (T i)) := by
  funext x y z
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [cyclic, directSum]
    · simp [cyclic, directSum, hik, Ne.symm hik]
  · by_cases hki : k = i
    · subst k
      simp [cyclic, directSum, hij]
    · simp [cyclic, directSum, hij, hki]

section Rectangular

variable {A B C : Type*}

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem matrixCoefficients_cyclic_product_square :
    pullback (rectangularSquareX A B C) (rectangularSquareY A B C)
      (rectangularSquareZ A B C)
      (product (product (matrixCoefficients (K := K) A B C)
        (matrixCoefficients B C A)) (matrixCoefficients C A B)) =
      matrixCoefficients (A × B × C) (A × B × C) (A × B × C) := by
  funext x y z
  dsimp only [pullback, rectangularSquareX, rectangularSquareY, rectangularSquareZ,
    product, matrixCoefficients]
  simp only [Prod.ext_iff, ite_mul, one_mul, zero_mul, ← ite_and]
  congr 1
  apply propext
  tauto

theorem cyclic_matrixCoefficients :
    cyclic (matrixCoefficients (K := K) A B C) = matrixCoefficients B C A := by
  funext x y z
  exact matrixCoefficients_cyclic x y z

end Rectangular

end Tensor
end MatrixMultiplication.Foundation

end




end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ComplexRectangularASI
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

namespace Tensor

def rectangularPullback
    {FieldType SourceX SourceY SourceZ TargetX TargetY TargetZ : Type*} [Field FieldType]
    {tensor : Tensor FieldType SourceX SourceY SourceZ} {rank shift degree : ℕ}
    (witness : PolynomialApproximation tensor rank shift degree)
    (mapX : TargetX → SourceX) (mapY : TargetY → SourceY) (mapZ : TargetZ → SourceZ) :
    PolynomialApproximation (pullback mapX mapY mapZ tensor) rank shift degree where
  polynomial := pullback mapX mapY mapZ witness.polynomial
  rank_bound := witness.rank_bound.pullback mapX mapY mapZ
  vanishes := fun coordX coordY coordZ coeff bound =>
    witness.vanishes (mapX coordX) (mapY coordY) (mapZ coordZ) coeff bound
  leading := fun coordX coordY coordZ =>
    witness.leading (mapX coordX) (mapY coordY) (mapZ coordZ)
  degree_bound := fun coordX coordY coordZ =>
    witness.degree_bound (mapX coordX) (mapY coordY) (mapZ coordZ)

def PolynomialApproximation.matrixCoefficients_directSum_of_injective
    {F ι κ A B : Type*} [Field F]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq A] [DecidableEq B] {r d D : ℕ}
    (P : PolynomialApproximation
      (directSum (fun _ : ι => matrixCoefficients (K := F) A A A)) r d D)
    (f : κ → ι) (hf : Function.Injective f) (g : B → A) (hg : Function.Injective g) :
    PolynomialApproximation
      (directSum (fun _ : κ => matrixCoefficients (K := F) B B B)) r d D := by
  let coord : κ × (B × B) → ι × (A × A) :=
    fun x => (f x.1, (g x.2.1, g x.2.2))
  have heq : Tensor.pullback coord coord coord
      (directSum (fun _ : ι => matrixCoefficients (K := F) A A A)) =
      directSum (fun _ : κ => matrixCoefficients (K := F) B B B) := by
    funext x y z
    simp only [Tensor.pullback, coord, directSum, matrixCoefficients, hf.eq_iff, hg.eq_iff]
  rw [← heq]
  exact rectangularPullback P coord coord coord

end Tensor

end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ComplexPolynomialWitnessProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.Foundation
namespace Tensor
namespace PolynomialApproximation

variable {F X Y Z U V W X' Y' Z' : Type*} [Field F]
variable {T : Tensor F X Y Z} {S : Tensor F U V W}
variable {r s d e D E : ℕ}

def directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {T : ι → Tensor F X Y Z} {S : κ → Tensor F U V W}
    (A : PolynomialApproximation (Tensor.directSum T) r d D)
    (B : PolynomialApproximation (Tensor.directSum S) s e E) :
    PolynomialApproximation
      (Tensor.directSum (fun i : ι × κ => Tensor.product (T i.1) (S i.2)))
      (r * s) (d + e) (D + E) := by
  have h := (A.product B).pullback (directSumProductEquiv ι κ X U)
    (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
  simpa only [Tensor.directSum_product] using h

def directSum_pullback {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor F X Y Z}
    (A : PolynomialApproximation (Tensor.directSum T) r d D)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    PolynomialApproximation
      (Tensor.directSum (fun i => Tensor.pullback fx fy fz (T i))) r d D :=
  A.pullback (fun x : ι × X' => (x.1, fx x.2))
    (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))

def directSum_cyclic {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor F X Y Z}
    (A : PolynomialApproximation (Tensor.directSum T) r d D) :
    PolynomialApproximation (Tensor.directSum (fun i => Tensor.cyclic (T i))) r d D := by
  simpa only [Tensor.cyclic_directSum] using A.cyclic

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

def matrixCoefficients_directSum_symmetrized {ι : Type*} [DecidableEq ι]
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := F) A B C)) r d D) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : (ι × ι) × ι =>
        matrixCoefficients (K := F) (A × B × C) (A × B × C) (A × B × C)))
      (r ^ 3) (3 * d) (3 * D) := by
  have P₁ : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := F) B C A)) r d D := by
    simpa only [Tensor.cyclic_matrixCoefficients] using P.directSum_cyclic
  have P₂ : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := F) C A B)) r d D := by
    simpa only [Tensor.cyclic_matrixCoefficients] using P₁.directSum_cyclic
  have h := ((P.directSum_product P₁).directSum_product P₂).directSum_pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  have hd : d + d + d = 3 * d := by ring
  have hD : D + D + D = 3 * D := by ring
  simpa only [Tensor.matrixCoefficients_cyclic_product_square,
    pow_succ, pow_zero, one_mul, hd, hD] using h

end PolynomialApproximation
end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_StageCLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem littleLaw_nonnegative (t u : Shape) (w : Fin 3) (i : Fin 6) :
    0 ≤ littleLaw t u w i := by
  obtain ⟨hl, hh⟩ := binaryParameter_bounds t u
  unfold littleLaw
  split_ifs <;> linarith

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

namespace MatrixMultiplication.CompactCertificate

namespace NInterval

def Encloses (S : ℕ) (a : NInterval) (x : ℝ) : Prop :=
  (a.lo : ℝ) / S ≤ x ∧ x ≤ (a.hi : ℝ) / S

noncomputable def oddPolynomial (t : ℝ) (start : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 / (2 * (start : ℝ) + 1) + t * oddPolynomial t (start + 1) n

end NInterval
end MatrixMultiplication.CompactCertificate

namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay
open Foundation.RationalLogCertificate

def checkLog (two a b : Ball) (w : LogData) : Bool :=
  decide (0 < a.lower ∧ 0 < w.denominator ∧ w.denominator ≤ w.numerator ∧
    w.numerator ≤ 2 * w.denominator ∧
    a.center = (w.numerator : ℚ) / w.denominator * (2 : ℚ) ^ w.exponent) &&
  contains (logResult two a w) b

end MatrixMultiplication.CompactCertificate

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def conditional (p : FiniteLaw A) (f : A → B) (b : B) : FiniteLaw A := by
  classical
  exact if hzero : (p.map f).mass b = 0 then p else
    { mass := fun a => (if f a = b then p.mass a else 0) / (p.map f).mass b
      nonneg := fun a => div_nonneg
        (by split_ifs; exact p.nonneg a; exact le_rfl) ((p.map f).nonneg b)
      total := by
        rw [← Finset.sum_div, ← map_mass p f b, div_self hzero] }

end FiniteLaw
end MatrixMultiplication.Foundation

end
end
namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay

inductive EntropyDatum where
  | zero
  | log (input output logarithm : Ball) (witness : LogData)

def EntropyDatum.input : EntropyDatum → Ball
  | .zero => .exact 0
  | .log p _ _ _ => p

def EntropyDatum.output : EntropyDatum → Ball
  | .zero => .exact 0
  | .log _ e _ _ => e

def EntropyDatum.check (two : Ball) : EntropyDatum → Bool
  | .zero => true
  | .log p e l w => checkLog two p l w && contains (Ball.mul (Ball.neg p) l) e

def entropyLookup (cs : List EntropyDatum) (i : ℕ) : EntropyDatum :=
  (cs[i]?).getD .zero

end MatrixMultiplication.CompactCertificate

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

namespace FiniteLaw

variable {A : Type*} [Fintype A]

def pure (a : A) : FiniteLaw A := by
  classical
  exact
    { mass := fun b => if b = a then 1 else 0
      nonneg := fun b => by split_ifs <;> norm_num
      total := by simp }

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldZeroLeafRates

open MatrixMultiplication.Foundation AllFieldParameters
open scoped BigOperators

def fourRate (t : Shape) : ℝ :=
  finiteEntropy (fun s : PairSlot => (zeroPairLaw t s.1 s.2 : ℝ)) +
    ∑ s : PairSlot, (zeroPairLaw t s.1 s.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 : ℕ)

end MatrixMultiplication.AllFieldZeroLeafRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointPairClassWindows
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_symm_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A B I : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

noncomputable def populationWordsEquiv (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) : PopulationWords I counts ≃ ExactWords counts := by
  let e : I ≃ Fin (∑ a, counts a) := Fintype.equivFinOfCardEq h
  exact
    { toFun := fun w =>
        ⟨w.val ∘ e.symm, fun a => (wordPopulation_reindex w.val e.symm a).trans (w.property a)⟩
      invFun := fun w =>
        ⟨w.val ∘ e, fun a => (wordPopulation_reindex w.val e a).trans (w.property a)⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp }

end MatrixMultiplication.Foundation





end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ParametersHalfLaws
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.canonicalChildShape_branchShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decode_encodePhysicalShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decode_encodeShape _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodePhysicalShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.encodeShape_total _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape_complement _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape_source _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem stageBLaw_nonnegative (t u : Shape) : 0 ≤ stageBLaw t u := by
  by_cases hu : u ∈ below t
  · exact (stageBLaw_positive t u hu).le
  · simp [stageBLaw, splitLaw, hu]

theorem positiveHalfLaw_nonnegative (t : Shape) (w : Fin 3) (ij : PairSlot) :
    0 ≤ positiveHalfLaw t w ij := by
  apply list_sum_map_nonnegative
  intro u _
  exact mul_nonneg (mul_nonneg (stageBLaw_nonnegative t u)
    (littleLaw_nonnegative t u w ij.1))
    (littleLaw_nonnegative t (complement t u) w ij.2)

theorem halfLaw_positive_parent (t : Shape) (ht : t ∈ positiveSecond)
    (w : Fin 3) (ij : PairSlot) : halfLaw t w ij = positiveHalfLaw t w ij := by
  have hp : positive t = true := (List.mem_filter.mp ht).2
  simp [halfLaw, hp]

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_FiniteAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem average_indicator_exists_le_sum {I : Type*} [Fintype I]
    (P : I → Ω → Prop) [∀ i ω, Decidable (P i ω)] :
    average (fun ω => if ∃ i, P i ω then (1 : ℝ) else 0) ≤
      ∑ i, average (fun ω => if P i ω then (1 : ℝ) else 0) := by
  classical
  rw [← average_finset_sum]
  apply average_mono
  intro ω
  by_cases h : ∃ i, P i ω
  · rw [ite_eq_left h]
    obtain ⟨i, hi⟩ := h
    calc
      (1 : ℝ) = (if P i ω then (1 : ℝ) else 0) := by simp [hi]
      _ ≤ ∑ j, if P j ω then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if P j ω then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

end

end MatrixMultiplication.PermutationMatching

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InverseLinearRecovery
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.ExactRecovery

variable {K X Y Z I A B C : Type*} [CommSemiring K]

theorem restrict_rectangles
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (Q H : Tensor K X Y Z) (cx : X → A) (cy : Y → B) (cz : Z → C)
    (fx : A × B × C → X → X) (fy : A × B × C → Y → Y)
    (fz : A × B × C → Z → Z)
    (h : ∀ x y z, H (fx (cx x, cy y, cz z) x)
      (fy (cx x, cy y, cz z) y) (fz (cx x, cy y, cz z) z) = Q x y z) :
    Tensor.restrict
      (fun x s => if cx x = s.1.1 ∧ s.2 = fx s.1 x then (1 : K) else 0)
      (fun y s => if cy y = s.1.2.1 ∧ s.2 = fy s.1 y then (1 : K) else 0)
      (fun z s => if cz z = s.1.2.2 ∧ s.2 = fz s.1 z then (1 : K) else 0)
      (Tensor.directSum (fun _ : A × B × C => H)) = Q := by
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
    ite_and, ite_mul, mul_ite, h]

theorem repair_of_cover
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype I] [DecidableEq I] [Nonempty I]
    (Q H : Tensor K X Y Z)
    (px : I → X → Prop) (py : I → Y → Prop) (pz : I → Z → Prop)
    (fx : I → X → X) (fy : I → Y → Y) (fz : I → Z → Z)
    (hshift : ∀ i x y z, H (fx i x) (fy i y) (fz i z) =
      @delete K X Y Z _ Q (px i) (py i) (pz i)
        (Classical.decPred _) (Classical.decPred _) (Classical.decPred _) x y z)
    (hcover : ∀ x y z, Q x y z ≠ 0 → ∃ i, px i x ∧ py i y ∧ pz i z) :
    ∃ (a : X → ((Finset I × Finset I × Finset I) × X) → K)
      (b : Y → ((Finset I × Finset I × Finset I) × Y) → K)
      (c : Z → ((Finset I × Finset I × Finset I) × Z) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : Finset I × Finset I × Finset I => H)) = Q := by
  classical
  let pick : Finset I × Finset I × Finset I → I := fun r =>
    if h : ∃ i, i ∈ r.1 ∧ i ∈ r.2.1 ∧ i ∈ r.2.2 then Classical.choose h
    else Classical.choice inferInstance
  have hpick (r : Finset I × Finset I × Finset I)
      (hr : ∃ i, i ∈ r.1 ∧ i ∈ r.2.1 ∧ i ∈ r.2.2) :
      pick r ∈ r.1 ∧ pick r ∈ r.2.1 ∧ pick r ∈ r.2.2 := by
    simpa [pick, hr] using Classical.choose_spec hr
  let cx := presence px
  let cy := presence py
  let cz := presence pz
  have hrect (x : X) (y : Y) (z : Z) :
      H (fx (pick (cx x, cy y, cz z)) x)
        (fy (pick (cx x, cy y, cz z)) y)
        (fz (pick (cx x, cy y, cz z)) z) = Q x y z := by
    rw [hshift]
    by_cases hq : Q x y z = 0
    · simp [delete, hq]
    · rcases hcover x y z hq with ⟨i, hix, hiy, hiz⟩
      have hp := hpick (cx x, cy y, cz z)
        ⟨i, by simpa [cx] using hix, by simpa [cy] using hiy,
          by simpa [cz] using hiz⟩
      have hpx : px (pick (cx x, cy y, cz z)) x := by simpa [cx] using hp.1
      have hpy : py (pick (cx x, cy y, cz z)) y := by simpa [cy] using hp.2.1
      have hpz : pz (pick (cx x, cy y, cz z)) z := by simpa [cz] using hp.2.2
      simp [delete, hpx, hpy, hpz]
  exact ⟨_, _, _, restrict_rectangles Q H cx cy cz
    (fun r => fx (pick r)) (fun r => fy (pick r)) (fun r => fz (pick r)) hrect⟩

theorem repair_of_counting
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype I]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq I]
    (Q H : Tensor K X Y Z)
    (px : I → X → Prop) (py : I → Y → Prop) (pz : I → Z → Prop)
    (fx : I → X → X) (fy : I → Y → Y) (fz : I → Z → Z)
    (hshift : ∀ i x y z, H (fx i x) (fy i y) (fz i z) =
      @delete K X Y Z _ Q (px i) (py i) (pz i)
        (Classical.decPred _) (Classical.decPred _) (Classical.decPred _) x y z)
    (t L : ℕ) (hL : 0 < L)
    (hbad : ∀ x y z, Q x y z ≠ 0 →
      (@Finset.filter I (fun i => ¬(px i x ∧ py i y ∧ pz i z))
        (Classical.decPred _) Finset.univ).card ≤ t)
    (hbudget : (@Finset.filter (X × Y × Z)
      (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ).card * t ^ L <
        Fintype.card I ^ L) :
    ∃ (a : X → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × X) → K)
      (b : Y → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Y) → K)
      (c : Z → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Z) → K),
      Tensor.restrict a b c
        (Tensor.directSum (fun _ : Finset (Fin L) × Finset (Fin L) × Finset (Fin L) => H)) = Q := by
  classical
  let support : Finset (X × Y × Z) := @Finset.filter (X × Y × Z)
    (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ
  let good (i : I) (p : X × Y × Z) : Prop := px i p.1 ∧ py i p.2.1 ∧ pz i p.2.2
  have hbad' : ∀ p ∈ support, (Finset.univ.filter fun i => ¬good i p).card ≤ t := by
    intro p hp
    have heq : (Finset.univ.filter fun i => ¬good i p) =
        @Finset.filter I (fun i => ¬(px i p.1 ∧ py i p.2.1 ∧ pz i p.2.2))
          (Classical.decPred _) Finset.univ := by
      ext i
      simp only [Finset.mem_filter, good]
    rw [heq]
    apply hbad p.1 p.2.1 p.2.2
    simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  obtain ⟨f, hf⟩ := FiniteCover.exists_cover support good t L hbad' hbudget
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  exact repair_of_cover Q H (fun i => px (f i)) (fun i => py (f i))
    (fun i => pz (f i)) (fun i => fx (f i)) (fun i => fy (f i))
    (fun i => fz (f i)) (fun i => hshift (f i))
    (fun x y z hq => hf (x, y, z) (by simp [support, hq]))

end MatrixMultiplication.ExactRecovery

end




section
open scoped BigOperators

namespace MatrixMultiplication.OrbitCounting

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [DecidableEq X]

theorem card_fiber_eq (x y : X) (hy : y ∈ orbitSet (G := G) x) :
    Fintype.card {g : G // g • x = y} = Fintype.card {g : G // g • x = x} := by
  classical
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hy
  let e : {g : G // g • x = y} ≃ {g : G // g • x = x} :=
    { toFun := fun g => ⟨r⁻¹ * g.1, by
        rw [mul_smul, g.2, ← hr, inv_smul_smul]⟩
      invFun := fun g => ⟨r * g.1, by
        rw [mul_smul, g.2, hr]⟩
      left_inv := by intro g; apply Subtype.ext; simp
      right_inv := by intro g; apply Subtype.ext; simp }
  exact Fintype.card_congr e

theorem card_group (x : X) :
    Fintype.card G = (orbitSet (G := G) x).card *
      Fintype.card {g : G // g • x = x} := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquiv (fun g : G => g • x)
    (fun y => y ∈ orbitSet (G := G) x) (smul_mem_orbitSet x)
  calc
    Fintype.card G = Fintype.card (Σ y : {y // y ∈ orbitSet (G := G) x},
        {g : G // g • x = y.1}) := (Fintype.card_congr e).symm
    _ = ∑ y : {y // y ∈ orbitSet (G := G) x},
        Fintype.card {g : G // g • x = y.1} := Fintype.card_sigma
    _ = ∑ _y : {y // y ∈ orbitSet (G := G) x},
        Fintype.card {g : G // g • x = x} := by
      apply Finset.sum_congr rfl
      intro y _
      exact card_fiber_eq x y.1 y.2
    _ = _ := by simp

theorem bad_shift_count (x : X) (bad : X → Prop) [DecidablePred bad] :
    (Finset.univ.filter fun g : G => bad (g • x)).card =
      ((orbitSet (G := G) x).filter bad).card *
        Fintype.card {g : G // g • x = x} := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquivSubtype (fun g : G => g • x)
    (p := fun g => bad (g • x))
    (q := fun y => y ∈ (orbitSet (G := G) x).filter bad)
    (fun g => by simp)
  calc
    (Finset.univ.filter fun g : G => bad (g • x)).card =
        Fintype.card {g : G // bad (g • x)} := (Fintype.card_subtype _).symm
    _ = Fintype.card (Σ y : {y // y ∈ (orbitSet (G := G) x).filter bad},
        {g : G // g • x = y.1}) := (Fintype.card_congr e).symm
    _ = ∑ y : {y // y ∈ (orbitSet (G := G) x).filter bad},
        Fintype.card {g : G // g • x = y.1} := Fintype.card_sigma
    _ = ∑ _y : {y // y ∈ (orbitSet (G := G) x).filter bad},
        Fintype.card {g : G // g • x = x} := by
      apply Finset.sum_congr rfl
      intro y _
      exact card_fiber_eq x y.1 (Finset.mem_filter.mp y.2).1
    _ = _ := by simp

theorem bad_shift_fraction (x : X) (bad : X → Prop) [DecidablePred bad] :
    ((Finset.univ.filter fun g : G => bad (g • x)).card : ℝ) / Fintype.card G =
      (((orbitSet (G := G) x).filter bad).card : ℝ) / (orbitSet (G := G) x).card := by
  have hsNat : 0 < Fintype.card {g : G // g • x = x} :=
    Fintype.card_pos_iff.mpr ⟨⟨1, one_smul G x⟩⟩
  have hs : (Fintype.card {g : G // g • x = x} : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hsNat)
  rw [bad_shift_count, card_group (G := G) x]
  simp only [Nat.cast_mul]
  exact mul_div_mul_right _ _ hs

end MatrixMultiplication.OrbitCounting

end




section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.OrbitRecovery

variable {G X Y Z : Type*} [Group G] [Fintype G]
    [MulAction G X] [MulAction G Y] [MulAction G Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

theorem badShifts_fraction_le_at (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (γ : ℝ) (x : X) (y : Y) (z : Z)
    (hx : (((OrbitCounting.orbitSet (G := G) x).filter fun v => ¬px v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) x).card ≤ γ)
    (hy : (((OrbitCounting.orbitSet (G := G) y).filter fun v => ¬py v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) y).card ≤ γ)
    (hz : (((OrbitCounting.orbitSet (G := G) z).filter fun v => ¬pz v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) z).card ≤ γ)
    :
    ((badShifts (G := G) px py pz x y z).card : ℝ) / Fintype.card G ≤ 3 * γ := by
  have hg : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hx' := hx
  have hy' := hy
  have hz' := hz
  rw [← OrbitCounting.bad_shift_fraction (G := G) x (fun v => ¬px v)] at hx'
  rw [← OrbitCounting.bad_shift_fraction (G := G) y (fun v => ¬py v)] at hy'
  rw [← OrbitCounting.bad_shift_fraction (G := G) z (fun v => ¬pz v)] at hz'
  have hxc := (div_le_iff₀ hg).mp hx'
  have hyc := (div_le_iff₀ hg).mp hy'
  have hzc := (div_le_iff₀ hg).mp hz'
  have hc : ((badShifts (G := G) px py pz x y z).card : ℝ) ≤
      ((Finset.univ.filter fun g : G => ¬px (g • x)).card : ℝ) +
      ((Finset.univ.filter fun g : G => ¬py (g • y)).card : ℝ) +
      ((Finset.univ.filter fun g : G => ¬pz (g • z)).card : ℝ) := by
    exact_mod_cast badShifts_card_le (G := G) px py pz x y z
  apply (div_le_iff₀ hg).mpr
  linarith

theorem repair_from_orbit_loss
    {K : Type*} [CommSemiring K] [Fintype X] [Fintype Y] [Fintype Z]
    (Q : Tensor K X Y Z)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (hpreserve : ∀ (g : G) x y z, Q (g • x) (g • y) (g • z) = Q x y z)
    (γ : ℝ)
    (hx : ∀ x, (∃ y z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) x).filter fun v => ¬px v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) x).card ≤ γ)
    (hy : ∀ y, (∃ x z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) y).filter fun v => ¬py v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) y).card ≤ γ)
    (hz : ∀ z, (∃ x y, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) z).filter fun v => ¬pz v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) z).card ≤ γ)
    (L : ℕ) (hL : 0 < L)
    (hbudget : (@Finset.filter (X × Y × Z)
      (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ).card *
        Nat.floor (3 * γ * Fintype.card G) ^ L < Fintype.card G ^ L) :
    ∃ (a : X → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × X) → K)
      (b : Y → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Y) → K)
      (c : Z → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Z) → K),
      Tensor.restrict a b c (Tensor.directSum
        (fun _ : Finset (Fin L) × Finset (Fin L) × Finset (Fin L) =>
          ExactRecovery.delete Q px py pz)) = Q := by
  classical
  apply ExactRecovery.repair_of_counting (I := G) Q (ExactRecovery.delete Q px py pz)
    (fun g x => px (g • x)) (fun g y => py (g • y)) (fun g z => pz (g • z))
    (fun g x => g • x) (fun g y => g • y) (fun g z => g • z)
    (fun g x y z => by simp [ExactRecovery.delete, hpreserve])
    (Nat.floor (3 * γ * Fintype.card G)) L hL ?_ hbudget
  intro x y z hq
  have heq : (@Finset.filter G
      (fun g => ¬(px (g • x) ∧ py (g • y) ∧ pz (g • z)))
      (Classical.decPred _) Finset.univ) = badShifts (G := G) px py pz x y z := by
    ext g
    simp only [badShifts, Finset.mem_filter]
  rw [heq]
  apply Nat.le_floor
  have hg : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  exact (div_le_iff₀ hg).mp (badShifts_fraction_le_at (G := G) px py pz γ x y z
    (hx x ⟨y, z, hq⟩) (hy y ⟨x, z, hq⟩) (hz z ⟨x, y, hq⟩))

end MatrixMultiplication.OrbitRecovery

end




end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InheritedMaskMargins
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_symm_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.InheritedMasks

open MatrixMultiplication.Foundation
open scoped BigOperators

section TensorAction

variable {F C : Type*} [CommSemiring F] [Fintype C]
  {P X Y Z : C → Type*} [∀ c, Fintype (P c)]

theorem classProduct_permutation
    (T : ∀ c, Tensor F (X c) (Y c) (Z c))
    (e : ∀ c, Equiv.Perm (P c))
    (x : ∀ c, P c → X c) (y : ∀ c, P c → Y c) (z : ∀ c, P c → Z c) :
    classProduct T (fun c => x c ∘ e c) (fun c => y c ∘ e c)
      (fun c => z c ∘ e c) = classProduct T x y z := by
  apply Finset.prod_congr rfl
  intro c _
  exact Equiv.prod_comp (e c) (fun i => T c (x c i) (y c i) (z c i))

end TensorAction

section EmpiricalWindows

variable {P A B : Type*} [Fintype P] [DecidableEq P]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq P] [Fintype A] in
theorem typeWindow_permutation (ν : A → ℝ) (η : ℝ) (w : P → A)
    (e : Equiv.Perm P) : typeWindow ν η (w ∘ e) ↔ typeWindow ν η w := by
  simp [typeWindow, empiricalLaw, wordPopulation_reindex]

end EmpiricalWindows

end MatrixMultiplication.InheritedMasks

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

section CompleteSymbols

variable {P A S : Type*} [Fintype P] [DecidableEq P] [DecidableEq S]

omit [DecidableEq P] in
theorem statisticPositions_card [Fintype S]
    (w : P → A) (statistic : A → S) (s : S) :
    (statisticPositions w statistic s).card =
      MatrixMultiplication.Foundation.wordPopulation (statistic ∘ w) s := by
  unfold statisticPositions MatrixMultiplication.Foundation.wordPopulation
  rw [Fintype.card_subtype]
  apply congrArg Finset.card
  ext i
  simp

end CompleteSymbols

section OrbitFractions

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [DecidableEq X]

theorem average_bad_shift_eq_orbit_fraction (x : X) (bad : X → Prop)
    [DecidablePred bad] :
    average (fun g : G => if bad (g • x) then 1 else 0) =
      (((OrbitCounting.orbitSet (G := G) x).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card := by
  rw [average_indicator_eq]
  exact OrbitCounting.bad_shift_fraction x bad

end OrbitFractions

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open MatrixMultiplication.InheritedMasks
open Classical

noncomputable section

section CompleteWordStatistics

variable {C : Type*} [Fintype C] [DecidableEq C] {P X Y S T : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)]
  [∀ c, Fintype (T c)] [∀ c, DecidableEq (T c)]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classDensity_statisticPositions (w : ∀ c, P c → X c)
    (statistic : ∀ c, X c → S c) (s : ∀ c, S c) (c : C) :
    classDensity (fun c => statisticPositions (w c) (statistic c) (s c)) c =
      empiricalLaw (statistic c ∘ w c) (s c) := by
  rw [classDensity, statisticPositions_card, empiricalLaw]

end CompleteWordStatistics

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointMaskedAssignment
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section






namespace MatrixMultiplication.JointCanonicalization

open MatrixMultiplication.Foundation JointPopulation InheritedMasks
open PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ)

variable (L R : H → Type*)

theorem typeWindow_reindex {P Q A : Type*}
    [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    [Fintype A] [DecidableEq A]
    (ν : A → ℝ) (η : ℝ) (w : P → A) (p : Q ≃ P) :
    typeWindow ν η (w ∘ p) ↔ typeWindow ν η w := by
  simp only [typeWindow, empiricalLaw, wordPopulation_reindex, Fintype.card_congr p]

section Coefficients

variable {F : Type*} [CommSemiring F]
    (T : ∀ h, Tensor F (L h × R h) (L h × R h) (L h × R h))
    (coarse : Fin 3 → ∀ h, L h × R h → Fin 17)

def coarseWord (s : Fin 3) (w : RawPairs counts L R) : Position counts → Fin 17 :=
  fun p => coarse s p.1 (w p.1 p.2)

omit [DecidableEq H] in
theorem product_pack (e : Target counts)
    (f : ∀ h, Shape → (L h × R h) → (L h × R h) → (L h × R h) → F)
    (x y z : RawPairs counts L R) :
    (∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
      f c.1 c.2
        ((pairEquiv counts L R e x).left c j, (pairEquiv counts L R e x).right c j)
        ((pairEquiv counts L R e y).left c j, (pairEquiv counts L R e y).right c j)
        ((pairEquiv counts L R e z).left c j, (pairEquiv counts L R e z).right c j)) =
      ∏ h, ∏ i, f h ((e h).val i) (x h i) (y h i) (z h i) := by
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h _
  rw [← Fintype.prod_sigma']
  apply Fintype.prod_equiv (positionEquiv counts e h).symm
  intro i
  simp only [pairEquiv, Equiv.coe_fn_mk, Prod.mk.eta, positionEquiv_symm_shape]

end Coefficients

end MatrixMultiplication.JointCanonicalization






namespace MatrixMultiplication.JointAssignmentLoss

open JointExtraction JointCoarseAssignment

attribute [local instance] Classical.propDecidable

variable {A B C I V Ω : Type*}

def ambientXCollision (ambient : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) (e : Triple A B C) : Prop :=
  ∃ f ∈ ambient, f ≠ e ∧ survives hx hy hz f ∧ f.1 = e.1

def targetCompatibleCollision (targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (compatible : Triple A B C → V → Prop) (e : Triple A B C) (v : V) : Prop :=
  ∃ f ∈ targets, f ≠ e ∧ survives hx hy hz f ∧ compatible f v

theorem eligible_of_no_ambientXCollision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) (e : Triple A B C)
    (ha : e ∈ ambient) (ht : e ∈ targets) (hs : survives hx hy hz e)
    (hno : ¬ ambientXCollision ambient hx hy hz e) :
    e ∈ eligible ambient targets hx hy hz := by
  apply (mem_eligible_iff ambient targets hx hy hz e).2
  refine ⟨ha, ht, hs, ?_⟩
  intro f hf hfs hfx
  by_contra hne
  exact hno ⟨f, hf, hne, hfs, hfx⟩

theorem assignUseful_of_no_targetCollision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (compatible useful : Triple A B C → V → Prop) (e : Triple A B C) (v : V)
    (he : e ∈ eligible ambient targets hx hy hz)
    (hc : compatible e v) (hu : useful e v)
    (hno : ¬ targetCompatibleCollision targets hx hy hz compatible e v) :
    assignUseful (eligible ambient targets hx hy hz) compatible useful v = some e := by
  apply assignUseful_of_unique _ _ _ _ _ he hc hu
  intro f hf hcf
  have hfe := (mem_eligible_iff ambient targets hx hy hz f).1 hf
  by_contra hne
  exact hno ⟨f, hfe.2.1, hne, hfe.2.2.1, hcf⟩

end MatrixMultiplication.JointAssignmentLoss






namespace MatrixMultiplication.JointMaskedSelection.OrbitData

open JointCoarseHashing

attribute [local instance] Classical.propDecidable

variable {P E O V : Type*} [Fintype P] [Fintype E]

def actualTargets (d : OrbitData P E O V) : Finset (Triple P) :=
  Finset.univ.image d.coarse

theorem coarse_mem_actualTargets (d : OrbitData P E O V) (e : E) :
    d.coarse e ∈ d.actualTargets :=
  Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩

def xFlag (k : ℕ) (U : Finset (ZMod (37 ^ k))) (s : Sample P k) (I : Word P) : Prop :=
  JointHashing.xHash s (castWord k I) ∈ U

def yFlag (k : ℕ) (U : Finset (ZMod (37 ^ k))) (s : Sample P k) (J : Word P) : Prop :=
  JointHashing.yHash s (castWord k J) ∈ U

def zFlag (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample P k) (K : Word P) : Prop :=
  JointHashing.zHash (twoUnit k) s (fun p => (d.support p : ZMod (37 ^ k))) (castWord k K) ∈ U

omit [Fintype E] in
theorem actual_survival_iff (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample P k) (f : Triple P) (hf : f ∈ d.ambient) :
    JointCoarseAssignment.survives (xFlag k U s) (yFlag k U s) (d.zFlag k U s) f ↔
      Survives k U f s :=
  full_survival_iff k U hAP d.support f (d.support_ambient f hf) s

def actualEligible (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample P k) : Finset (Triple P) :=
  JointCoarseAssignment.eligible d.ambient d.actualTargets
    (xFlag k U s) (yFlag k U s) (d.zFlag k U s)

theorem good_mem_actualEligible (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (s : Sample P k) (hg : d.Good k U N e s) :
    d.coarse e ∈ d.actualEligible k U s := by
  apply JointAssignmentLoss.eligible_of_no_ambientXCollision d.ambient d.actualTargets
    (xFlag k U s) (yFlag k U s) (d.zFlag k U s) (d.coarse e)
    (d.target_mem e) (d.coarse_mem_actualTargets e)
    ((d.actual_survival_iff k U hAP s _ (d.target_mem e)).2 hg.1)
  rintro ⟨f, hf, hne, hs, hx⟩
  exact d.good_eligibility k U N e s hg
    ⟨f, (d.mem_eligibilityCompetitors e f).2 ⟨hf, hne, hx⟩,
      (d.actual_survival_iff k U hAP s f hf).1 hs⟩

def actualAssignment (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (s : Sample P k) (v : V) : Option (Triple P) :=
  JointExtraction.retainAssignment
    (JointCoarseAssignment.assignUseful (d.actualEligible k U s) compatible useful) keep v

theorem model_retained_assigned (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (v : V) (hv : v ∈ JointLossCounts.retained (d.passing e o) (d.variableBad k U e o) s)
    (hc : compatible (d.coarse e) v) (hu : useful (d.coarse e) v) (hk : keep v)
    (hcover : ∀ f ∈ d.actualTargets, f ≠ d.coarse e → compatible f v →
      f ∈ d.competitors e o v) :
    d.actualAssignment k U compatible useful keep s v = some (d.coarse e) := by
  obtain ⟨hpass, hnotbad⟩ := Finset.mem_filter.1 hv
  have hassign := JointAssignmentLoss.assignUseful_of_no_targetCollision
    d.ambient d.actualTargets (xFlag k U s) (yFlag k U s) (d.zFlag k U s)
    compatible useful (d.coarse e) v (d.good_mem_actualEligible k U hAP N e s hg) hc hu
    (by
      rintro ⟨f, hf, hne, hsurv, hcomp⟩
      have hfc := hcover f hf hne hcomp
      have hfa := d.competitor_mem e o ho v hpass f hfc
      exact hnotbad ⟨f, hfc, (d.actual_survival_iff k U hAP s f hfa).1 hsurv⟩)
  simpa only [actualAssignment, actualEligible, JointExtraction.retainAssignment,
    ite_eq_left hk] using hassign

end MatrixMultiplication.JointMaskedSelection.OrbitData

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWCompleteStatistics
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section

namespace MatrixMultiplication.CWCompatibilityTransfer

open MatrixMultiplication.Foundation CWLeafRestrictions InheritedMasks
open scoped BigOperators

def wordWeight {n : ℕ} (w : Fin n → Fin 7) : ℕ := ∑ i, CWLeafStatistics.weight (w i)

def wordComplement {n : ℕ} (w : Fin n → Fin 7) : Fin n → Fin 7 :=
  fun i => complement 5 (w i)

@[simp] theorem wordComplement_involution {n : ℕ} (w : Fin n → Fin 7) :
    wordComplement (wordComplement w) = w := by
  funext i
  exact complement_involution 5 (w i)

theorem weight_eq_zero_iff : ∀ x : Fin 7, CWLeafStatistics.weight x = 0 ↔ x = 0 := by
  decide +kernel

theorem wordWeight_zero {n : ℕ} (w : Fin n → Fin 7) (h : wordWeight w = 0) :
    ∀ i, w i = 0 := by
  intro i
  have hle : CWLeafStatistics.weight (w i) ≤ wordWeight w := by
    unfold wordWeight
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (CWLeafStatistics.weight (w j)))
      (Finset.mem_univ i)
  apply (weight_eq_zero_iff (w i)).mp
  omega

theorem site_nonzero {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0) (i : Fin n) :
    FieldCW.tensor F 5 (x i) (y i) (z i) ≠ 0 := by
  intro hi
  apply h
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem zeroX_word_match {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0)
    (hx : wordWeight x = 0) : z = wordComplement y := by
  funext i
  have hi := site_nonzero x y z h i
  rw [wordWeight_zero x hx i] at hi
  have heq : FieldCW.tensor F 5 0 (y i) (z i) =
      if y i = complement 5 (z i) then 1 else 0 := by
    simpa only [complement_involution] using
      tensor_zero_matching F 5 (y i) (complement 5 (z i))
  have hyz : y i = complement 5 (z i) := by
    by_contra hn
    rw [heq, ite_eq_right hn] at hi
    exact hi rfl
  have hh := congrArg (complement 5) hyz
  simpa only [wordComplement, complement_involution] using hh.symm

end MatrixMultiplication.CWCompatibilityTransfer






namespace MatrixMultiplication.CWStrands

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {F : Type*} [CommRing F]

theorem shapeTensor_support {P : Type*} [Fintype P]
    (g : Fin 3 → ℕ) (x y z : P → Fin 7)
    (h : shapeTensor (F := F) P g x y z ≠ 0) :
    weight x = g 0 ∧ weight y = g 1 ∧ weight z = g 2 := by
  classical
  by_contra hn
  exact h (ite_eq_right hn)

end MatrixMultiplication.CWStrands






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.Staggering

def totalCapacity (a b : Capacity) (base : ℝ) : ℝ :=
  base + (∑ i, (a i + b i)) / 3

def balanceFraction (a b : Capacity) (high base : ℝ) (i : Fin 3) : ℝ :=
  (high - totalCapacity a b base + (a i + b i)) / (3 * (high - base))

end MatrixMultiplication.Staggering

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters CWStrands CWWindowedLeaves
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def leftChildLaw {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) : ActiveStatistic c.1 → ℝ :=
  childLaw c.1.val c.2 side

def rightClassChildLaw {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) : ActiveStatistic c.1 → ℝ :=
  rightChildLaw c.1.val c.2 side

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryPositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
attribute [local instance] Classical.propDecidable Classical.decEq

theorem source_shape {K : ℕ} (w : Work K) : currentShape w.source = w.parentShape := by
  cases w <;> rfl

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCanonicalMixed
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCanonicalMixed

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open CWStrands HistorySymmetry InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ) (sharing : H → Bool)
    (hleft : ∀ h, leftLength h ≤ 8)

abbrev MixedWords := RawPairs counts (Left leftLength) (Right rightLength)

def coarseWord (w : MixedWords counts leftLength rightLength) : Position counts → Fin 17 :=
  JointCanonicalization.coarseWord counts (Left leftLength) (Right rightLength)
    (coarse leftLength rightLength hleft) 0 w

def sideMask (s : Fin 3) (w : MixedWords counts leftLength rightLength) : Prop :=
  ∀ h a, wordPopulation (fun i => coarseWord counts leftLength rightLength hleft w ⟨h, i⟩) a =
    wordPopulation (sideWord counts s (triple counts (canonicalTarget counts)) h) a

omit [Fintype H] [DecidableEq H] in
theorem sideMask_of_target (s : Fin 3) (e : Target counts)
    (w : MixedWords counts leftLength rightLength)
    (he : coarseWord counts leftLength rightLength hleft w =
      fun i => sideWord counts s (triple counts e) i.1 i.2) :
    sideMask counts leftLength rightLength hleft s w := by
  intro h a
  rw [he]
  exact marginal_population_eq counts e (canonicalTarget counts) h s a

end MatrixMultiplication.JointCanonicalMixed

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWStageCStatistics
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

attribute [local instance] Classical.propDecidable Classical.decEq

theorem wordPopulation_of_branchStatistic (counts : Fin 4 → ℕ) (s i : Fin 3)
    (w : Positions counts → Fin 6)
    (hw : ∀ p, w p = branchStatistic s p.1 i) (a : Fin 6) :
    wordPopulation w a =
      ∑ b : Fin 4, if branchStatistic s b i = a then counts b else 0 := by
  let e : {p : Positions counts // w p = a} ≃
      (Σ b : Fin 4, {j : Fin (counts b) // branchStatistic s b i = a}) :=
    { toFun := fun p => ⟨p.val.1, ⟨p.val.2, (hw p.val).symm.trans p.property⟩⟩
      invFun := fun p => ⟨⟨p.1, p.2.val⟩, (hw _).trans p.2.property⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  rw [wordPopulation, Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : branchStatistic s b i = a <;> simp [h]

end MatrixMultiplication.CWStageCProducts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitCount
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativeSplitWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.initialExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistorySupport

open AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem population_dilation {K : ℕ} (allocation : Allocation) (m : ℕ) (h : History K) :
    population allocation m h = m * population allocation 1 h := by
  simp only [population, AllFieldPopulationCounts.count, one_mul]

theorem jointCounts_dilation {K : ℕ} (allocation : Allocation) (m : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    jointCounts allocation m w u = m * jointCounts allocation 1 w u := by
  simp only [jointCounts, shapeCounts, branchPopulation, population,
    AllFieldPopulationCounts.count, one_mul, Finset.mul_sum, mul_ite, mul_zero]

theorem activeCounts_dilation {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape) :
    activeCounts allocation m h u = m * activeCounts allocation 1 h u :=
  jointCounts_dilation allocation m h.val u

theorem activeCounts_pos_iff {K tick m : ℕ} (allocation : Allocation) (hm : 0 < m)
    (h : Active K tick) (u : JointPopulation.Shape) :
    0 < activeCounts allocation m h u ↔ 0 < activeCounts allocation 1 h u := by
  rw [activeCounts_dilation]
  exact Nat.mul_pos_iff_of_pos_left hm

theorem dilation_le_activeCounts {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hpos : 0 < activeCounts allocation 1 h u) : m ≤ activeCounts allocation m h u := by
  rw [activeCounts_dilation]
  calc
    m = m * 1 := (Nat.mul_one m).symm
    _ ≤ m * activeCounts allocation 1 h u := Nat.mul_le_mul_left m hpos

theorem two_le_activeCounts {K tick m : ℕ} (allocation : Allocation) (hm : 2 ≤ m)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hpos : 0 < activeCounts allocation 1 h u) : 2 ≤ activeCounts allocation m h u :=
  hm.trans (dilation_le_activeCounts allocation m h u hpos)

theorem totalLength_dilation {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (l r : Active K tick → ℕ) :
    HistorySupport.totalLength (JointPopulation.Positions (activeCounts allocation m)) l r =
      m * HistorySupport.totalLength (JointPopulation.Positions (activeCounts allocation 1)) l r := by
  simp only [HistorySupport.totalLength, JointPopulation.Positions, Fintype.card_fin,
    activeCounts_dilation allocation m, ← Finset.mul_sum, Nat.mul_assoc]

def fixedBaseLength {K tick : ℕ} (allocation : Allocation) : ℕ :=
  HistorySupport.totalLength
    (JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation 1))
    activeHalfLength activeHalfLength

def supportRate {K tick : ℕ} (allocation : Allocation) : ℝ :=
  RecoverySupport.cw5SupportRate (fixedBaseLength (K := K) (tick := tick) allocation)

theorem supportRate_pos {K tick : ℕ} (allocation : Allocation) :
    0 < supportRate (K := K) (tick := tick) allocation :=
  RecoverySupport.cw5SupportRate_pos _

theorem raw_support_card_le_exp {K tick : ℕ} {F : Type*} [Zero F]
    (allocation : Allocation) (m : ℕ)
    (Q : ActiveRawPairs (K := K) (tick := tick) allocation m →
      ActiveRawPairs (K := K) (tick := tick) allocation m →
      ActiveRawPairs (K := K) (tick := tick) allocation m → F) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp (supportRate (K := K) (tick := tick) allocation * m) := by
  apply HistorySupport.cw5_support_card_le_exp
    (JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation m))
    activeHalfLength activeHalfLength Q (fixedBaseLength (K := K) (tick := tick) allocation) m
  rw [totalLength_dilation]
  exact le_of_eq (Nat.mul_comm _ _)

theorem work_source_amount_pos {K : ℕ} (allocation : Allocation) (w : PlacedWork K) :
    0 < amount allocation (w.1.source, w.2) := by
  rcases w with ⟨w, phi⟩
  unfold amount
  apply div_pos _ (by norm_num)
  cases w with
  | stageA h => exact initialAmount_pos h.val
  | stageB h => exact aAmount_pos h.val
  | stageC h => exact partAmount_pos allocation h

end MatrixMultiplication.AllFieldHistorySupport

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryBranchWeights

open AllFieldHistory AllFieldHistorySupport AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem stageB_branchPopulation_rat {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℚ) =
      (population allocation dilation (.afterA h.val, phi) : ℚ) *
        stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) := by
  simp only [branchPopulation, Work.child, population_cast, amount, canonicalAmount, bAmount]
  ring

theorem stageB_branchPopulation_real {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℝ) =
      (population allocation dilation (.afterA h.val, phi) : ℝ) *
        (stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) : ℝ) := by
  exact_mod_cast stageB_branchPopulation_rat allocation dilation h b phi

theorem shapeCounts_weighted_sum {I : Type*} [Fintype I]
    (code : I → JointPopulation.Shape) (weight : I → ℕ)
    (f : JointPopulation.Shape → ℝ) :
    (∑ u, (shapeCounts code weight u : ℝ) * f u) =
      ∑ b, (weight b : ℝ) * f (code b) := by
  simp only [shapeCounts, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp [ite_mul]

end MatrixMultiplication.AllFieldHistoryBranchWeights

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryStageCIncoming

open AllFieldHistory AllFieldHistorySupport AllFieldParameters
open CWStageCProducts InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def stageCActive (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick) :
    Active K tick := ⟨(.stageC h, phi), ht⟩

end MatrixMultiplication.AllFieldHistoryStageCIncoming

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitCount

open AllFieldHistory AllFieldHistorySupport PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def groupDegree (K tick : ℕ) (sigma : Placement) : ℕ :=
  2 * ∑ c : GroupClasses K tick sigma, 7 ^ activeHalfLength c.1.val

end MatrixMultiplication.AllFieldGroupOrbitCount

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryRecoveryBudget
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open MatrixMultiplication.InheritedMasks
open Classical

noncomputable section

variable {C : Type*} {P X Y : C → Type*}
variable [Fintype C] [DecidableEq C]
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
variable {S T : C → Type*}

def wordPairLeftPositions (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (s : ∀ c, S c) : ∀ c, Finset (P c) :=
  fun c => statisticPositions (w.left c) (sl c) (s c)

def wordPairRightPositions (w : CompleteWordPair P X Y)
    (sr : ∀ c, Y c → T c) (t : ∀ c, T c) : ∀ c, Finset (P c) :=
  fun c => statisticPositions (w.right c) (sr c) (t c)

def selectedWordPairCount (D : Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) : ℝ :=
  ∑ c : D, ∑ i : P c,
    if sl c (w.left c i) = s c ∧ sr c (w.right c i) = t c then 1 else 0

omit [Fintype C] [DecidableEq C] in
theorem selectedWordPairCount_smul (D : Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (g : HalfClassPermutations P) :
    selectedWordPairCount D (g • w) sl sr s t =
      selectedTwoHalfCount D (wordPairLeftPositions w sl s)
        (wordPairRightPositions w sr t) g⁻¹ := by
  unfold selectedWordPairCount selectedTwoHalfCount totalTwoHalfCount
    wordPairLeftPositions wordPairRightPositions
  apply Finset.sum_congr rfl
  intro c _
  rw [twoHalfCount_statisticPositions]
  rfl

theorem average_selectedWordPairCount_shift (D : Finset C)
    (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (f : ℝ → ℝ) :
    average (fun g : HalfClassPermutations P =>
      f (selectedWordPairCount D (g • w) sl sr s t)) =
      average (fun g : HalfClassPermutations P =>
        f (selectedTwoHalfCount D (wordPairLeftPositions w sl s)
          (wordPairRightPositions w sr t) g)) := by
  simp_rw [selectedWordPairCount_smul]
  exact average_equiv (Equiv.inv (HalfClassPermutations P))
    (fun g => f (selectedTwoHalfCount D (wordPairLeftPositions w sl s)
      (wordPairRightPositions w sr t) g))

def selectedWordPairMaskBad (D : Finset C)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (η ν : ℝ)
    (w : CompleteWordPair P X Y) : Prop :=
  η < |selectedWordPairCount D w sl sr s t /
    populationSize (fun c : D => P c) - ν|

section FiniteMasks

variable {I : Type*} [Fintype I] {SL SR : I → C → Type*}

theorem finite_selectedWordPair_orbit_rejection_of_windows_le
    (D : I → Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ i c, X c → SL i c) (sr : ∀ i c, Y c → SR i c)
    (s : ∀ i c, SL i c) (t : ∀ i c, SR i c)
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (hm : ∀ i, 0 < populationSize (fun c : D i => P c))
    (left right : I → C → ℝ) (η τ α ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hright0 : ∀ i c, c ∈ D i → 0 ≤ right i c)
    (hright1 : ∀ i c, c ∈ D i → right i c ≤ 1)
    (hleft : ∀ i c, c ∈ D i →
      |classDensity (wordPairLeftPositions w (sl i) (s i)) c - left i c| ≤ τ i)
    (hright : ∀ i c, c ∈ D i →
      |classDensity (wordPairRightPositions w (sr i) (t i)) c - right i c| ≤ τ i)
    (happrox : ∀ i, |classProductMixture (fun c : D i => P c)
      (fun c => left i c) (fun c => right i c) - ν i| ≤ α i)
    (hτ : ∀ i, τ i ≤ η i / 8) (hα : ∀ i, α i ≤ η i / 4) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (fun v => ∃ i, selectedWordPairMaskBad (D i) (sl i) (sr i)
          (s i) (t i) (η i) (ν i) v)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤
        ∑ i, 1 / (2 * populationSize (fun c : D i => P c) * (η i) ^ 2) := by
  rw [← average_bad_shift_eq_orbit_fraction]
  refine le_trans (average_indicator_exists_le_sum _) ?_
  apply Finset.sum_le_sum
  intro i _
  change average (fun g : HalfClassPermutations P =>
    if η i < |selectedWordPairCount (D i) (g • w) (sl i) (sr i) (s i) (t i) /
      populationSize (fun c : D i => P c) - ν i| then 1 else 0) ≤ _
  rw [average_selectedWordPairCount_shift (D i) w (sl i) (sr i) (s i) (t i)
    (fun k => if η i < |k / populationSize (fun c : D i => P c) - ν i|
      then 1 else 0)]
  exact selectedTwoHalfMask_rejection_of_windows_le (D i) _ _ (hn i) (hm i)
    (left i) (right i) (η i) (τ i) (α i) (ν i) (hη i)
    (hright0 i) (hright1 i) (hleft i) (hright i) (happrox i) (hτ i) (hα i)

theorem finite_selectedWordPair_orbit_inverse_linear_of_windows
    (D : I → Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ i c, X c → SL i c) (sr : ∀ i c, Y c → SR i c)
    (s : ∀ i c, SL i c) (t : ∀ i c, SR i c)
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (mass : I → ℝ) (N : ℝ) (hN : 0 < N) (hmass : ∀ i, 0 < mass i)
    (hsize : ∀ i, populationSize (fun c : D i => P c) = mass i * N)
    (left right : I → C → ℝ) (η τ α ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hright0 : ∀ i c, c ∈ D i → 0 ≤ right i c)
    (hright1 : ∀ i c, c ∈ D i → right i c ≤ 1)
    (hleft : ∀ i c, c ∈ D i →
      |classDensity (wordPairLeftPositions w (sl i) (s i)) c - left i c| ≤ τ i)
    (hright : ∀ i c, c ∈ D i →
      |classDensity (wordPairRightPositions w (sr i) (t i)) c - right i c| ≤ τ i)
    (happrox : ∀ i, |classProductMixture (fun c : D i => P c)
      (fun c => left i c) (fun c => right i c) - ν i| ≤ α i)
    (hτ : ∀ i, τ i ≤ η i / 8) (hα : ∀ i, α i ≤ η i / 4) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (fun v => ∃ i, selectedWordPairMaskBad (D i) (sl i) (sr i)
          (s i) (t i) (η i) (ν i) v)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤
        (∑ i, 1 / (2 * mass i * (η i) ^ 2)) / N := by
  have hm (i : I) : 0 < populationSize (fun c : D i => P c) := by
    rw [hsize]
    exact mul_pos (hmass i) hN
  have h := finite_selectedWordPair_orbit_rejection_of_windows_le D w sl sr s t hn hm
    left right η τ α ν hη hright0 hright1 hleft hright happrox hτ hα
  simpa only [hsize, inverse_linear_mask_constant] using h

end FiniteMasks

end

end MatrixMultiplication.PermutationMatching





noncomputable section

namespace MatrixMultiplication.AllFieldHistoryMasks

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open JointCanonicalization InheritedMasks PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem pairWidth_pos {ε : ℝ} (hε : 0 < ε) (h : Active K tick) :
    0 < pairWidth ε h := by
  unfold pairWidth
  positivity

end MatrixMultiplication.AllFieldHistoryMasks






namespace MatrixMultiplication.AllFieldHistoryMaskLaws

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open AllFieldHistoryMasks AllFieldHistoryBranchWeights AllFieldParameters
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def parentCenter (allocation : Allocation) (side : Fin 3) (h : Active K tick)
    (a b : Statistic h) : ℝ :=
  ∑ u : JointPopulation.Shape,
    (activeCounts allocation 1 h u : ℝ) /
      population allocation 1 (h.val.1.source, h.val.2) *
        (leftLaw h u side a * rightLaw h u side b)

def stageBActive (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick) :
    Active K tick := ⟨(.stageB h, phi), ht⟩

theorem stageB_leftLaw_branch (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (k : BSplit h) (side : Fin 3) (a : Fin 6) :
    leftLaw (stageBActive h phi ht) (branchShape (.stageB h, phi) k) side a =
      (littleLaw (aShape h.val) (bSplit ⟨h, k, false⟩) (phi.symm side) a : ℝ) := by
  change (littleLaw (aShape h.val)
    (canonicalChildShape (.stageB h, phi) (branchShape (.stageB h, phi) k))
    (phi.symm side) a : ℝ) = _
  rw [canonicalChildShape_branchShape (.stageB h, phi) k]
  rfl

theorem stageB_rightLaw_branch (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (k : BSplit h) (side : Fin 3) (b : Fin 6) :
    rightLaw (stageBActive h phi ht) (branchShape (.stageB h, phi) k) side b =
      (littleLaw (aShape h.val) (complement (aShape h.val) (bSplit ⟨h, k, false⟩))
        (phi.symm side) b : ℝ) := by
  change (littleLaw (aShape h.val)
    (complement (aShape h.val)
      (canonicalChildShape (.stageB h, phi) (branchShape (.stageB h, phi) k)))
    (phi.symm side) b : ℝ) = _
  rw [canonicalChildShape_branchShape (.stageB h, phi) k]
  rfl

theorem stageB_sum_laws (h : APositive K) (side : Fin 3) (a b : Fin 6) :
    (∑ k : BSplit h,
      stageBLaw (aShape h.val) (bSplit ⟨h, k, false⟩) *
        littleLaw (aShape h.val) (bSplit ⟨h, k, false⟩) side a *
        littleLaw (aShape h.val) (complement (aShape h.val) (bSplit ⟨h, k, false⟩)) side b) =
      halfLaw (aShape h.val) side (a, b) := by
  rw [halfLaw_positive_parent _ h.property]
  unfold positiveHalfLaw
  change (∑ k : Fin (below (aShape h.val)).length,
    stageBLaw (aShape h.val) (below (aShape h.val))[k.val] *
      littleLaw (aShape h.val) (below (aShape h.val))[k.val] side a *
      littleLaw (aShape h.val) (complement (aShape h.val) (below (aShape h.val))[k.val]) side b) = _
  exact Fin.sum_univ_fun_getElem (below (aShape h.val))
    (fun u => stageBLaw (aShape h.val) u * littleLaw (aShape h.val) u side a *
      littleLaw (aShape h.val) (complement (aShape h.val) u) side b)

end MatrixMultiplication.AllFieldHistoryMaskLaws






namespace MatrixMultiplication.AllFieldHistoryIncomingMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters
open AllFieldHistoryChildLaws AllFieldHistorySupport AllFieldHistoryMasks
open AllFieldHistoryMaskLaws InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem empiricalLaw_congr_decidable {P A : Type*} [Fintype P]
    (d₁ d₂ : DecidableEq A) (w : P → A) (a : A) :
    @empiricalLaw P A _ d₁ w a = @empiricalLaw P A _ d₂ w a := by
  cases Subsingleton.elim d₁ d₂
  rfl

theorem typeWindow_mono_decidable {P A : Type*} [Fintype P]
    (d₁ d₂ : DecidableEq A) (ν : A → ℝ) {η δ : ℝ} (hη : η ≤ δ)
    (w : P → A) (hw : @typeWindow P A _ d₁ ν η w) :
    @typeWindow P A _ d₂ ν δ w := by
  cases Subsingleton.elim d₁ d₂
  intro a
  exact (hw a).trans hη

theorem strand_append {F : Type*} [CommRing F] {m n : ℕ}
    (x y z : (Fin m → Fin 7) × (Fin n → Fin 7)) :
    CWStrands.strand (F := F) (Fin (m + n))
      (Fin.append x.1 x.2) (Fin.append y.1 y.2) (Fin.append z.1 z.2) =
        CWStrands.strand (Fin m) x.1 y.1 z.1 * CWStrands.strand (Fin n) x.2 y.2 z.2 := by
  simp [CWStrands.strand, Fin.prod_univ_add]

@[simp] theorem append_singletons (l r : Fin 1 → Fin 7) :
    Fin.append l r = (Matrix.vecCons (l 0) (Matrix.vecCons (r 0) Matrix.vecEmpty)) := by
  funext i
  fin_cases i <;> rfl

attribute [local irreducible] activeCounts population

end MatrixMultiplication.AllFieldHistoryIncomingMasks

end
end




section
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.EquivOrbitTransport

variable {G X Y : Type*} [Group G] [MulAction G Y]

section Finite

variable [Fintype G] [DecidableEq X] [DecidableEq Y]

theorem orbitSet_map (e : X ≃ Y) (x : X) :
    letI : MulAction G X := action e
    (OrbitCounting.orbitSet (G := G) x).map e.toEmbedding =
      OrbitCounting.orbitSet (G := G) (e x) := by
  let : MulAction G X := action e
  change (Finset.univ.image fun g : G => e.symm (g • e x)).map e.toEmbedding = _
  simp only [Finset.map_eq_image, Finset.image_image, Function.comp_def,
    Equiv.toEmbedding_apply, Equiv.apply_symm_apply, OrbitCounting.orbitSet]

theorem orbitSet_card (e : X ≃ Y) (x : X) :
    letI : MulAction G X := action e
    (OrbitCounting.orbitSet (G := G) x).card =
      (OrbitCounting.orbitSet (G := G) (e x)).card := by
  let : MulAction G X := action e
  simpa only [Finset.card_map] using congrArg Finset.card (orbitSet_map e x)

theorem rejected_card (e : X ≃ Y) (bad : X → Prop) [DecidablePred bad] (x : X) :
    letI : MulAction G X := action e
    ((OrbitCounting.orbitSet (G := G) x).filter bad).card =
      ((OrbitCounting.orbitSet (G := G) (e x)).filter (bad ∘ e.symm)).card := by
  let : MulAction G X := action e
  calc
    ((OrbitCounting.orbitSet (G := G) x).filter bad).card =
        (((OrbitCounting.orbitSet (G := G) x).filter bad).map e.toEmbedding).card :=
      (Finset.card_map _).symm
    _ = _ := by rw [Finset.map_filter, orbitSet_map]

theorem rejected_fraction (e : X ≃ Y) (bad : X → Prop) [DecidablePred bad] (x : X) :
    letI : MulAction G X := action e
    (((OrbitCounting.orbitSet (G := G) x).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card =
      (((OrbitCounting.orbitSet (G := G) (e x)).filter (bad ∘ e.symm)).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) (e x)).card := by
  let : MulAction G X := action e
  rw [rejected_card e bad x, orbitSet_card e x]

end Finite

theorem coefficients_preserved
    {K RX RY RZ CX CY CZ : Type*} [CommSemiring K]
    [MulAction G CX] [MulAction G CY] [MulAction G CZ]
    (ex : RX ≃ CX) (ey : RY ≃ CY) (ez : RZ ≃ CZ)
    (raw : Tensor K RX RY RZ) (canonical : Tensor K CX CY CZ)
    (hcoords : ∀ x y z, raw x y z = canonical (ex x) (ey y) (ez z))
    (hcanonical : ∀ (g : G) x y z,
      canonical (g • x) (g • y) (g • z) = canonical x y z) :
    letI : MulAction G RX := action ex
    letI : MulAction G RY := action ey
    letI : MulAction G RZ := action ez
    ∀ (g : G) x y z, raw (g • x) (g • y) (g • z) = raw x y z := by
  let : MulAction G RX := action ex
  let : MulAction G RY := action ey
  let : MulAction G RZ := action ez
  intro g x y z
  rw [hcoords, hcoords]
  change canonical (ex (ex.symm (g • ex x))) (ey (ey.symm (g • ey y)))
    (ez (ez.symm (g • ez z))) = _
  simpa only [Equiv.apply_symm_apply] using hcanonical g (ex x) (ey y) (ez z)

end MatrixMultiplication.EquivOrbitTransport

end




end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryGroupCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open MatrixMultiplication.Foundation
attribute [local instance] Classical.propDecidable Classical.decEq

def activeEquivOrders (K tick : ℕ) :
    Active K tick ≃ Σ sigma : Placement, ActiveOrder K tick sigma :=
  (Equiv.sigmaFiberEquiv (fun w : Active K tick => w.val.physicalOrder)).symm

theorem prod_active_eq_prod_orders {K tick : ℕ} {M : Type*} [CommMonoid M]
    (f : Active K tick → M) :
    (∏ h, f h) = ∏ sigma : Placement, ∏ h : ActiveOrder K tick sigma, f h.val := by
  calc
    _ = ∏ h : (Σ sigma : Placement, ActiveOrder K tick sigma), f h.2.val :=
      Fintype.prod_equiv (activeEquivOrders K tick) _ _ (fun _ => rfl)
    _ = _ := Fintype.prod_sigma _

namespace GroupAssignment

variable {I : Type*} {V E : I → Type*}

variable {X Y Z : I → Type*}

def product (a : ∀ i, JointExtraction.Assignment (X i) (Y i) (Z i) (E i)) :
    JointExtraction.Assignment (∀ i, X i) (∀ i, Y i) (∀ i, Z i) (∀ i, E i) where
  x := collect (fun i => (a i).x)
  y := collect (fun i => (a i).y)
  z := collect (fun i => (a i).z)

variable [Fintype I] {F : Type*} [CommSemiring F]

theorem product_coherent (T : ∀ i, Tensor F (X i) (Y i) (Z i))
    (a : ∀ i, JointExtraction.Assignment (X i) (Y i) (Z i) (E i))
    (ha : ∀ i, JointExtraction.Coherent (T i) (a i)) :
    JointExtraction.Coherent (CommonDimensions.familyProduct T) (product a) := by
  intro x y z e f g hT hx hy hz
  have hx' := (collect_eq_some (fun i => (a i).x) x e).mp hx
  have hy' := (collect_eq_some (fun i => (a i).y) y f).mp hy
  have hz' := (collect_eq_some (fun i => (a i).z) z g).mp hz
  have hfactor (i : I) : T i (x i) (y i) (z i) ≠ 0 := by
    intro hi
    exact hT (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  constructor
  · funext i
    exact (ha i (x i) (y i) (z i) (e i) (f i) (g i)
      (hfactor i) (hx' i) (hy' i) (hz' i)).1
  · funext i
    exact (ha i (x i) (y i) (z i) (e i) (f i) (g i)
      (hfactor i) (hx' i) (hy' i) (hz' i)).2

end GroupAssignment

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryMasks AllFieldHistoryIncomingMasks
open JointPopulation JointCanonicalization JointCanonicalCW InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def projectRaw (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    GroupRaw (K := K) (tick := tick) allocation m sigma := fun h j => w h.val j

end MatrixMultiplication.AllFieldHistoryGroupMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistorySource

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldHistoryRegrouping AllFieldHistoryIncomingMasks
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

def deleteWithPred {F : Type*} [Field F] {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (source : Tensor F X Y Z) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz] :
    LocalMap source (ExactRecovery.delete source px py pz) := by
  let d := LocalMap.delete source px py pz
  refine ⟨d.x, d.y, d.z, d.coefficient.trans ?_⟩
  funext x y z
  unfold ExactRecovery.delete
  split_ifs <;> rfl

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

abbrev Raw := AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m

def marginal (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  JointCanonicalMixed.sideMask (activeCounts allocation m) activeHalfLength activeHalfLength
    AllFieldHistoryRecovery.halfLength_le_eight side w

end MatrixMultiplication.AllFieldHistorySource

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupedRecovery

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def projectTarget (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m) :
    GroupTarget (K := K) (tick := tick) allocation m sigma := fun h => e h.val

end MatrixMultiplication.AllFieldHistoryGroupedRecovery

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryRecovery
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.PermutationMatching

open MatrixMultiplication.InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

theorem orbitSet_eq_fullOrbitFilter {G V : Type*} [Group G] [Fintype G]
    [MulAction G V] [Fintype V] [DecidableEq V] (v : V) :
    OrbitCounting.orbitSet (G := G) v = fullOrbitFilter G v := by
  ext w
  simp only [OrbitCounting.orbitSet, fullOrbitFilter, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_filter]

theorem fullOrbitFilter_bad_fraction_eq_orbit {G V : Type*}
    [Group G] [Fintype G] [MulAction G V] [Fintype V] [DecidableEq V]
    (w : V) (bad : V → Prop) [DecidablePred bad] :
    ((rejectedFilter (fullOrbitFilter G w) bad).card : ℝ) /
        (fullOrbitFilter G w).card =
      (((OrbitCounting.orbitSet (G := G) w).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) w).card := by
  have horbit := orbitSet_eq_fullOrbitFilter (G := G) w
  have hbad : (OrbitCounting.orbitSet (G := G) w).filter bad =
      rejectedFilter (fullOrbitFilter G w) bad := by
    ext v
    simp only [Finset.mem_filter, rejectedFilter, horbit]
  rw [hbad, horbit]

theorem orbit_bad_fraction_eq_fullOrbitFilter_of_iff {G V : Type*}
    [Group G] [Fintype G] [MulAction G V] [Fintype V] [DecidableEq V]
    (w : V) (bad canonical : V → Prop) [DecidablePred bad]
    (h : ∀ v, bad v ↔ canonical v) :
    (((OrbitCounting.orbitSet (G := G) w).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) w).card =
      ((rejectedFilter (fullOrbitFilter G w) canonical).card : ℝ) /
        (fullOrbitFilter G w).card := by
  rw [← fullOrbitFilter_bad_fraction_eq_orbit (G := G) w bad,
    rejectedFilter_congr (fullOrbitFilter G w) bad canonical h]

variable {C : Type*} {P X Y : C → Type*}
variable [Fintype C] [DecidableEq C]
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [Fintype (CompleteWordPair P X Y)]
variable {I : Type*} [Fintype I] {SL SR : I → C → Type*}

theorem finite_selectedWordPair_full_filter_inverse_linear_of_windows
    (D : I → Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ i c, X c → SL i c) (sr : ∀ i c, Y c → SR i c)
    (s : ∀ i c, SL i c) (t : ∀ i c, SR i c)
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (mass : I → ℝ) (N : ℝ) (hN : 0 < N) (hmass : ∀ i, 0 < mass i)
    (hsize : ∀ i, populationSize (fun c : D i => P c) = mass i * N)
    (left right : I → C → ℝ) (η τ α ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hright0 : ∀ i c, c ∈ D i → 0 ≤ right i c)
    (hright1 : ∀ i c, c ∈ D i → right i c ≤ 1)
    (hleft : ∀ i c, c ∈ D i →
      |classDensity (wordPairLeftPositions w (sl i) (s i)) c - left i c| ≤ τ i)
    (hright : ∀ i c, c ∈ D i →
      |classDensity (wordPairRightPositions w (sr i) (t i)) c - right i c| ≤ τ i)
    (happrox : ∀ i, |classProductMixture (fun c : D i => P c)
      (fun c => left i c) (fun c => right i c) - ν i| ≤ α i)
    (hτ : ∀ i, τ i ≤ η i / 8) (hα : ∀ i, α i ≤ η i / 4) :
    ((rejectedFilter (fullOrbitFilter (HalfClassPermutations P) w)
        (fun v => ∃ i, selectedWordPairMaskBad (D i) (sl i) (sr i)
          (s i) (t i) (η i) (ν i) v)).card : ℝ) /
      (fullOrbitFilter (HalfClassPermutations P) w).card ≤
        (∑ i, 1 / (2 * mass i * (η i) ^ 2)) / N := by
  classical
  have h := finite_selectedWordPair_orbit_inverse_linear_of_windows
    D w sl sr s t hn mass N hN hmass hsize left right η τ α ν hη
    hright0 hright1 hleft hright happrox hτ hα
  exact (fullOrbitFilter_bad_fraction_eq_orbit (G := HalfClassPermutations P) w _).trans_le h

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRecovery

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistoryChildLaws
open AllFieldHistorySupport JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def sideWeights (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  ∀ h j,
    CWStrands.weight (w h j).1 = (shapeSide side ((e h).val j)).val ∧
    CWStrands.weight (w h j).2 = activeParentShape h side -
      (shapeSide side ((e h).val j)).val

theorem support_filter_eq {F X Y Z : Type*} [Zero F]
    [Fintype X] [Fintype Y] [Fintype Z] (Q : Tensor F X Y Z) :
    (@Finset.filter (X × Y × Z) (fun p => Q p.1 p.2.1 p.2.2 ≠ 0)
      (Classical.decPred _) Finset.univ) = RecoverySupport.support Q := by
  ext p
  simp only [RecoverySupport.support, Finset.mem_filter]

end MatrixMultiplication.AllFieldHistoryRecovery

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistorySourceAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.GroupOrbitProjection

open PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

section OrbitFraction

variable {G H X Y : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [MulAction G X] [MulAction H Y]

theorem orbit_fraction_of_uniform_projection (project : X → Y) (shift : G → H)
    (hsmul : ∀ g x, project (g • x) = shift g • project x)
    (huniform : ∀ f : H → ℝ, average (fun g => f (shift g)) = average f)
    (x : X) (bad : Y → Prop) :
    (((OrbitCounting.orbitSet (G := G) x).filter (fun v => bad (project v))).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card =
      (((OrbitCounting.orbitSet (G := H) (project x)).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := H) (project x)).card := by
  rw [← OrbitCounting.bad_shift_fraction (G := G) x (fun v => bad (project v)),
    ← OrbitCounting.bad_shift_fraction (G := H) (project x) bad]
  rw [← average_indicator_eq, ← average_indicator_eq]
  simp_rw [hsmul]
  exact huniform (fun g => if bad (g • project x) then (1 : ℝ) else 0)

theorem rejected_fraction_of_uniform_projection (project : X → Y) (shift : G → H)
    (hsmul : ∀ g x, project (g • x) = shift g • project x)
    (huniform : ∀ f : H → ℝ, average (fun g => f (shift g)) = average f)
    (x : X) (bad : Y → Prop) :
    ((rejectedFilter (OrbitCounting.orbitSet (G := G) x)
      (fun v => bad (project v))).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card =
      ((rejectedFilter (OrbitCounting.orbitSet (G := H) (project x)) bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := H) (project x)).card := by
  simpa only [rejectedFilter, Finset.filter_congr_decidable] using
    orbit_fraction_of_uniform_projection project shift hsmul huniform x bad

end OrbitFraction

section ConjugatedProjection

variable {G H RX RY CX CY : Type*} [Group G] [Group H]
  [MulAction G CX] [MulAction H CY]

theorem conjugated_projection_smul (ex : RX ≃ CX) (ey : RY ≃ CY)
    (raw : RX → RY) (canonical : CX → CY) (shift : G → H)
    (hc : ∀ x, ey (raw x) = canonical (ex x))
    (hs : ∀ g x, canonical (g • x) = shift g • canonical x) :
    letI : MulAction G RX := EquivOrbitTransport.action ex
    letI : MulAction H RY := EquivOrbitTransport.action ey
    ∀ g x, raw (g • x) = shift g • raw x := by
  let : MulAction G RX := EquivOrbitTransport.action ex
  let : MulAction H RY := EquivOrbitTransport.action ey
  intro g x
  apply ey.injective
  rw [hc, EquivOrbitTransport.equiv_smul ex, hs,
    EquivOrbitTransport.equiv_smul ey, hc]

end ConjugatedProjection

theorem transported_projection_fraction {G H RX RY CX CY : Type*}
    [Group G] [Group H] [Fintype G] [Fintype H]
    [MulAction G CX] [MulAction H CY]
    (ex : RX ≃ CX) (ey : RY ≃ CY)
    (raw : RX → RY) (canonical : CX → CY) (shift : G → H)
    (hc : ∀ x, ey (raw x) = canonical (ex x))
    (hs : ∀ g x, canonical (g • x) = shift g • canonical x)
    (huniform : ∀ f : H → ℝ, average (fun g => f (shift g)) = average f)
    (x : RX) (bad : RY → Prop) :
    ((rejectedFilter (transportedOrbit (G := G) ex x)
      (fun v => bad (raw v))).card : ℝ) / (transportedOrbit (G := G) ex x).card =
      ((rejectedFilter (transportedOrbit (G := H) ey (raw x)) bad).card : ℝ) /
        (transportedOrbit (G := H) ey (raw x)).card :=
  @rejected_fraction_of_uniform_projection G H RX RY _ _ _ _
    (EquivOrbitTransport.action ex) (EquivOrbitTransport.action ey)
    raw shift (conjugated_projection_smul ex ey raw canonical shift hc hs) huniform x bad

section CompleteHistories

variable {H S : Type*} [Fintype H] [Fintype S] [DecidableEq H] [DecidableEq S]
  (P X Y : H × S → Type*) [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]

def projectPair (p : H → Prop) (w : CompleteWordPair P X Y) :
    CompleteWordPair (fun c : {h // p h} × S => P (c.1.val, c.2))
      (fun c => X (c.1.val, c.2)) (fun c => Y (c.1.val, c.2)) where
  left c i := w.left (c.1.val, c.2) i
  right c i := w.right (c.1.val, c.2) i

def projectShifts (p : H → Prop) (g : HalfClassPermutations P) :
    HalfClassPermutations (fun c : {h // p h} × S => P (c.1.val, c.2)) :=
  ((fun c => g.1 (c.1.val, c.2)), (fun c => g.2 (c.1.val, c.2)))

omit [Fintype H] [Fintype S] [DecidableEq H] [DecidableEq S]
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)] in
theorem projectPair_smul (p : H → Prop) (g : HalfClassPermutations P)
    (w : CompleteWordPair P X Y) :
    projectPair P X Y p (g • w) = projectShifts P p g • projectPair P X Y p w := rfl

end CompleteHistories

section RawHistories

open JointPopulation JointCanonicalization

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ) (L R : H → Type*)

def groupCounts (p : H → Prop) : {h // p h} → Shape → ℕ := fun h => counts h.val

def projectTarget (p : H → Prop) (e : Target counts) : Target (groupCounts counts p) :=
  fun h => e h.val

def projectRaw (p : H → Prop) (w : RawPairs counts L R) :
    RawPairs (groupCounts counts p) (fun h => L h.val) (fun h => R h.val) :=
  fun h => w h.val

omit [Fintype H] [DecidableEq H] in
theorem pairEquiv_projectRaw (p : H → Prop) [DecidablePred p] (e : Target counts)
    (w : RawPairs counts L R) :
    pairEquiv (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
      (projectTarget counts p e) (projectRaw counts L R p w) =
      projectPair (ClassPositions counts) (fun c => L c.1) (fun c => R c.1) p
        (pairEquiv counts L R e w) := rfl

theorem raw_orbit_projection_fraction (p : H → Prop) [DecidablePred p] (e : Target counts)
    (w : RawPairs counts L R)
    (bad : RawPairs (groupCounts counts p) (fun h => L h.val) (fun h => R h.val) → Prop) :
    ((rejectedFilter (rawOrbit counts L R e w)
      (fun v => bad (projectRaw counts L R p v))).card : ℝ) /
        (rawOrbit counts L R e w).card =
      ((rejectedFilter (rawOrbit (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
        (projectTarget counts p e) (projectRaw counts L R p w)) bad).card : ℝ) /
        (rawOrbit (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
          (projectTarget counts p e) (projectRaw counts L R p w)).card := by
  exact transported_projection_fraction
    (G := HalfClassPermutations (ClassPositions counts))
    (H := HalfClassPermutations (ClassPositions (groupCounts counts p)))
    (RX := RawPairs counts L R)
    (RY := RawPairs (groupCounts counts p) (fun h => L h.val) (fun h => R h.val))
    (CX := CanonicalPairs counts L R)
    (CY := CanonicalPairs (groupCounts counts p) (fun h => L h.val) (fun h => R h.val))
    (pairEquiv counts L R e)
    (pairEquiv (groupCounts counts p) (fun h => L h.val) (fun h => R h.val)
      (projectTarget counts p e))
    (projectRaw counts L R p)
    (projectPair (ClassPositions counts) (fun c => L c.1) (fun c => R c.1) p)
    (projectShifts (ClassPositions counts) p)
    (pairEquiv_projectRaw counts L R p e)
    (projectPair_smul (H := H) (S := Shape) (ClassPositions counts)
      (fun c => L c.1) (fun c => R c.1) p)
    (fun f => average_half_history_restrict (H := H) (S := Shape)
      (X := fun c => Equiv.Perm (ClassPositions counts c)) p f) w bad

theorem raw_group_passing_rejection_fraction_le {I : Type*} [Fintype I] [DecidableEq I]
    (group : H → I) (e : Target counts) (w : RawPairs counts L R)
    (keep : RawPairs counts L R → Prop)
    (localKeep assigned : ∀ i : I, RawPairs (groupCounts counts (fun h => group h = i))
      (fun h => L h.val) (fun h => R h.val) → Prop)
    (hkeep : ∀ v, keep v → ∀ i,
      localKeep i (projectRaw counts L R (fun h => group h = i) v))
    (bound : I → ℝ)
    (hbound : ∀ i,
      ((rejectedFilter (rawOrbit (groupCounts counts (fun h => group h = i))
        (fun h => L h.val) (fun h => R h.val)
        (projectTarget counts (fun h => group h = i) e)
        (projectRaw counts L R (fun h => group h = i) w))
          (fun v => localKeep i v ∧ ¬assigned i v)).card : ℝ) /
        (rawOrbit (groupCounts counts (fun h => group h = i))
          (fun h => L h.val) (fun h => R h.val)
          (projectTarget counts (fun h => group h = i) e)
          (projectRaw counts L R (fun h => group h = i) w)).card ≤ bound i) :
    ((rejectedFilter (rawOrbit counts L R e w)
      (fun v => keep v ∧ ¬∀ i, assigned i
        (projectRaw counts L R (fun h => group h = i) v))).card : ℝ) /
      (rawOrbit counts L R e w).card ≤ ∑ i, bound i := by
  let bad : I → RawPairs counts L R → Prop := fun i v =>
    localKeep i (projectRaw counts L R (fun h => group h = i) v) ∧
      ¬assigned i (projectRaw counts L R (fun h => group h = i) v)
  have hsub : rejectedFilter (rawOrbit counts L R e w)
      (fun v => keep v ∧ ¬∀ i, assigned i
        (projectRaw counts L R (fun h => group h = i) v)) ⊆
      rejectedFilter (rawOrbit counts L R e w) (fun v => ∃ i, bad i v) := by
    intro v hv
    simp only [rejectedFilter, Finset.mem_filter] at hv ⊢
    obtain ⟨hmem, hk, ha⟩ := hv
    obtain ⟨i, hi⟩ := not_forall.mp ha
    exact ⟨hmem, i, hkeep v hk i, hi⟩
  have hlocal (i : I) :
      ((rejectedFilter (rawOrbit counts L R e w) (bad i)).card : ℝ) /
        (rawOrbit counts L R e w).card ≤ bound i :=
    (raw_orbit_projection_fraction counts L R (fun h => group h = i) e w
      (fun v => localKeep i v ∧ ¬assigned i v)).le.trans (hbound i)
  have hunion : ((rejectedFilter (rawOrbit counts L R e w)
      (fun v => ∃ i, bad i v)).card : ℝ) /
      (rawOrbit counts L R e w).card ≤ ∑ i, bound i :=
    rejected_union_fraction_le (rawOrbit counts L R e w) bad bound hlocal
  have hcard : ((rejectedFilter (rawOrbit counts L R e w)
      (fun v => keep v ∧ ¬∀ i, assigned i
        (projectRaw counts L R (fun h => group h = i) v))).card : ℝ) ≤
      ((rejectedFilter (rawOrbit counts L R e w) (fun v => ∃ i, bad i v)).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  exact (div_le_div_of_nonneg_right hcard
    (Nat.cast_nonneg (rawOrbit counts L R e w).card)).trans hunion

end RawHistories

end MatrixMultiplication.GroupOrbitProjection

end
end




section
namespace MatrixMultiplication.RecoveryOrbitDecisions

theorem orbitSet_instances {G X : Type*} [Group G] [MulAction G X]
    (f₁ f₂ : Fintype G) (d₁ d₂ : DecidableEq X) (x : X) :
    @OrbitCounting.orbitSet G X _ _ f₁ d₁ x =
      @OrbitCounting.orbitSet G X _ _ f₂ d₂ x := by
  apply Finset.ext
  intro y
  simp only [OrbitCounting.orbitSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem orbitSet_eq_transportedOrbit {G X Y : Type*} [Group G] [MulAction G Y]
    (fRaw fCanonical : Fintype G) (d : DecidableEq X) (e : X ≃ Y) (x : X) :
    @OrbitCounting.orbitSet G X _ (EquivOrbitTransport.action e) fRaw d x =
      @GroupOrbitProjection.transportedOrbit G X Y _ fCanonical _ e x := by
  unfold GroupOrbitProjection.transportedOrbit
  exact @orbitSet_instances G X _ (EquivOrbitTransport.action e)
    fRaw fCanonical d _ x

end MatrixMultiplication.RecoveryOrbitDecisions





noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupedRecovery

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem project_joinGroupTargets (allocation : Allocation) (m : ℕ)
    (e : ∀ sigma, GroupTarget (K := K) (tick := tick) allocation m sigma)
    (sigma : Placement) :
    projectTarget allocation m sigma (joinGroupTargets (activeCounts allocation m) e) =
      e sigma := by
  funext h
  rcases h with ⟨h, hh⟩
  cases hh
  rfl

def groupedAssignment (allocation : Allocation) (m : ℕ) (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma)) :
    JointExtraction.Assignment (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
      (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) (AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
      (∀ sigma, E sigma) where
  x w := GroupAssignment.collect (fun sigma => (a sigma).x)
    (fun sigma => projectRaw allocation m sigma w)
  y w := GroupAssignment.collect (fun sigma => (a sigma).y)
    (fun sigma => projectRaw allocation m sigma w)
  z w := GroupAssignment.collect (fun sigma => (a sigma).z)
    (fun sigma => projectRaw allocation m sigma w)

def localAssigned (allocation : Allocation) (m : ℕ) (sigma : Placement) {E : Type*}
    (a : JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) E)
    (i : E) (side : Fin 3) (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  AllFieldHistoryRecovery.sideVariable side (a.x w = some i) (a.y w = some i) (a.z w = some i)

theorem grouped_assigned_iff (allocation : Allocation) (m : ℕ)
    (E : Placement → Type*)
    (a : ∀ sigma, JointExtraction.Assignment
      (GroupRaw (K := K) (tick := tick) allocation m sigma)
      (GroupRaw (K := K) (tick := tick) allocation m sigma) (GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (i : ∀ sigma, E sigma) (side : Fin 3)
    (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m) :
    AllFieldHistoryRecovery.sideVariable side
      ((groupedAssignment allocation m E a).x w = some i)
      ((groupedAssignment allocation m E a).y w = some i)
      ((groupedAssignment allocation m E a).z w = some i) ↔
      ∀ sigma, localAssigned allocation m sigma (a sigma) (i sigma) side
        (projectRaw allocation m sigma w) := by
  fin_cases side <;> exact GroupAssignment.collect_eq_some _ _ _

end MatrixMultiplication.AllFieldHistoryGroupedRecovery






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_InitialLeafRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldTerminalRates

open AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def initialRate (g : Shape) : ℝ :=
  Real.log (Contractions.coefficients[shapeMax g]?.getD 0 : ℝ)

def S0 : ℝ :=
  ((sortedInitial.filter (fun g => !positive g)).map
    (fun g => (initialLaw g : ℝ) * initialRate g)).sum

def secondLeafRate (t u : Shape) : ℝ :=
  if shapeMax u = 4 then 0
  else if shapeMax u = 3 then Real.log 10
  else if !positive u then
    binaryEntropyRate (binaryParameter t u) +
      2 * (1 - (binaryParameter t u : ℝ)) * Real.log 5
  else (2 - (binaryParameter t u : ℝ)) * Real.log 5

theorem four_shape_max_lt_five : ∀ u ∈ shapes 4, shapeMax u < 5 := by
  decide +kernel

theorem second_shapeMax_lt_five (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) : shapeMax u < 5 :=
  four_shape_max_lt_five u (stageB_children_size t ht u hu)

end MatrixMultiplication.AllFieldTerminalRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointTypeCounts
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointTypeCounts

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

section FixedClasses

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (P A : C → Type*)
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

def fixedWordsEquiv {I B : Type*} [Fintype I] [DecidableEq I]
    [Fintype B] [DecidableEq B] (counts : B → ℕ)
    (hsize : Fintype.card I = ∑ b, counts b) :
    {w : I → B // ∀ b, wordPopulation w b = counts b} ≃ ExactWords counts := by
  classical
  let e : Fin (∑ b, counts b) ≃ I := Fintype.equivOfCardEq (by simpa using hsize.symm)
  exact
    { toFun := fun w => ⟨w.val ∘ e, fun b => by
        rw [wordPopulation_reindex]
        exact w.property b⟩
      invFun := fun w => ⟨w.val ∘ e.symm, fun b => by
        rw [wordPopulation_reindex]
        exact w.property b⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp }

abbrev ClassExactWords (counts : ∀ c, A c → ℕ) := ∀ c, ExactWords (counts c)

end FixedClasses

end MatrixMultiplication.JointTypeCounts

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityIncidence
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityIncidence

open MatrixMultiplication.Foundation JointTypeCounts
open scoped BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] fixedWordsMulAction

section GroupEntropy

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

def groupedEntropy (p : U → ℝ) (group : U → K) (law : U → A → ℝ) : ℝ :=
  ∑ k, groupMass p group k * finiteEntropy (groupLaw p group law k)

end GroupEntropy

section SideControls

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape Pair A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
  (part : ∀ c, Pair c → A c) (designated : ∀ c, Shape c → Prop)
  (law : ∀ c, Shape c → A c → ℝ) (χ : ℝ)
  (H : (Σ c, Option (Shape c)) → ℝ) (w : FixedClassWords Pos Shape shapeCounts)

structure SideEntropyControl where
  residualLaw : ∀ c, A c → ℝ
  totalTarget : ∀ c, A c → ℝ
  totalError : C → ℝ
  aggregate_window : ∀ c a,
    |((∑ s : {s : Pair c // part c s = a}, pairCounts c s.val : ℕ) : ℝ) -
      totalTarget c a| ≤ totalError c
  mixture_balance : ∀ c a,
    (Fintype.card {i : Pos c // ¬designated c ((w c).val i)} : ℝ) * residualLaw c a =
      totalTarget c a - ∑ u : {u : Shape c // designated c u},
        (shapeCounts c u.val : ℝ) * law c u.val a
  nonneg : ∀ g, 0 ≤ H g
  designated_entropy : ∀ c u, designated c u → ∀ q : A c → ℝ,
    (∀ a, |q a - law c u a| ≤ χ) → finiteEntropy q ≤ H ⟨c, some u⟩
  residual_entropy : ∀ c, ∀ q : A c → ℝ,
    (∀ a, |q a - residualLaw c a| ≤
      (totalError c + (∑ u : {u : Shape c // designated c u},
        (shapeCounts c u.val : ℝ)) * χ) /
          Fintype.card {i : Pos c // ¬designated c ((w c).val i)}) →
      finiteEntropy q ≤ H ⟨c, none⟩

end SideControls

section Compatibility

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape Pair Left Right : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]
variable (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
  (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
  (designatedLeft designatedRight : ∀ c, Shape c → Prop)
  (leftLaw : ∀ c, Shape c → Left c → ℝ)
  (rightLaw : ∀ c, Shape c → Right c → ℝ) (χ : ℝ)

def DesignatedCompatibility (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts) : Prop :=
  (∀ c u, designatedLeft c u → ∀ a,
    |(jointCount (w c).val (z c).val (leftPart c) u a : ℝ) -
      (shapeCounts c u : ℝ) * leftLaw c u a| ≤ (shapeCounts c u : ℝ) * χ) ∧
  (∀ c u, designatedRight c u → ∀ a,
    |(jointCount (w c).val (z c).val (rightPart c) u a : ℝ) -
      (shapeCounts c u : ℝ) * rightLaw c u a| ≤ (shapeCounts c u : ℝ) * χ)

def compatibleStatisticCount (w : FixedClassWords Pos Shape shapeCounts) : ℕ :=
  Fintype.card {z : FixedClassWords Pos Pair pairCounts //
    DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z}

def compatibleCandidateCount (z : FixedClassWords Pos Pair pairCounts) : ℕ :=
  Fintype.card {w : FixedClassWords Pos Shape shapeCounts //
    DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z}

end Compatibility

end MatrixMultiplication.JointCompatibilityIncidence

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWStrandCompatibility
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.CWStrandCompatibility

open MatrixMultiplication.Foundation CWStrands CWCompatibilityTransfer InheritedMasks
open scoped BigOperators

variable {F : Type*} [CommRing F]

theorem shape_nonzero_power {n : ℕ} (g : Fin 3 → ℕ)
    (x y z : Fin n → Fin 7) (h : shapeTensor (F := F) (Fin n) g x y z ≠ 0) :
    Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0 := by
  have hm := shapeTensor_support g x y z h
  simpa only [shapeTensor, ite_eq_left hm, strand, Tensor.power] using h

section Classes

variable {P A : Type*} [Fintype P] [DecidableEq P]
    [Fintype A] [DecidableEq A] {n : ℕ}
    (g : P → Fin 3 → ℕ) (x y z : P → (Fin n → Fin 7))
    (h : (∏ i, shapeTensor (F := F) (Fin n) (g i) (x i) (y i) (z i)) ≠ 0)
    (statistic : (Fin n → Fin 7) → A) (κ : A ≃ A)
    (hstatistic : ∀ w, statistic (wordComplement w) = κ (statistic w))
    (ν : A → ℝ) (η : ℝ)

include h

omit [DecidableEq P] in
theorem class_coefficient_nonzero (i : P) :
    shapeTensor (F := F) (Fin n) (g i) (x i) (y i) (z i) ≠ 0 := by
  intro hi
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) hi)

end Classes

end MatrixMultiplication.CWStrandCompatibility

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointPopulationMixedCompatibility
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationCompatibility

open MatrixMultiplication.Foundation JointPopulation JointTypeCounts InheritedMasks
open JointCompatibilityIncidence
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ)

omit [Fintype H] [DecidableEq H] in
theorem shape_count_window_of_typeWindow {A : Type*} [Fintype A] [DecidableEq A]
    (e : Target counts) (h : H) (u : Shape) (f : Positions counts h → A)
    (law : A → ℝ) (χ : ℝ)
    (hw : 0 < counts h u → typeWindow law χ (fun i : Class counts e h u => f i.val)) :
    ∀ a, |(shapeStatisticCount counts e h u f a : ℝ) -
      (counts h u : ℝ) * law a| ≤ (counts h u : ℝ) * χ := by
  intro a
  by_cases hn : 0 < counts h u
  · apply scaled_count_window (Nat.cast_pos.mpr hn)
    simpa only [empiricalLaw, class_card, shapeStatisticCount] using hw hn a
  · have hn0 : counts h u = 0 := Nat.eq_zero_of_not_pos hn
    have hc : shapeStatisticCount counts e h u f a = 0 := by
      apply Nat.eq_zero_of_le_zero
      let forget : {i : Class counts e h u // f i.val = a} → Class counts e h u :=
        Subtype.val
      have hinj : Function.Injective forget := Subtype.val_injective
      have hbound := Fintype.card_le_of_injective forget hinj
      calc
        shapeStatisticCount counts e h u f a ≤ Fintype.card (Class counts e h u) :=
          hbound
        _ = 0 := (class_card counts e h u).trans hn0
    simp only [hc, hn0, Nat.cast_zero, zero_mul, sub_zero, abs_zero, le_refl]

section Statistics

variable (L R : H → Type*)
  (SL SR : ClassKey (H := H) → Type*)
  [∀ c, Fintype (SL c)] [∀ c, DecidableEq (SL c)]
  [∀ c, Fintype (SR c)] [∀ c, DecidableEq (SR c)]
  (leftStatistic : ∀ c, L c.1 → SL c)
  (rightStatistic : ∀ c, R c.1 → SR c)

def statisticWord (b : Position counts → Fin 17)
    (w : JointCanonicalization.RawPairs counts L R) (c : ClassKey (H := H)) :
    ClassPos counts b c → SL c × SR c :=
  fun i => (leftStatistic c (w c.1 i.val).1, rightStatistic c (w c.1 i.val).2)

def statisticCounts (b : Position counts → Fin 17)
    (w : JointCanonicalization.RawPairs counts L R) (c : ClassKey (H := H)) :
    SL c × SR c → ℕ :=
  wordPopulation (statisticWord counts L R SL SR leftStatistic rightStatistic b w c)

def statisticElement (b : Position counts → Fin 17)
    (w : JointCanonicalization.RawPairs counts L R) :
    FixedClassWords (ClassPos counts b) (fun c => SL c × SR c)
      (statisticCounts counts L R SL SR leftStatistic rightStatistic b w) :=
  fun c => ⟨statisticWord counts L R SL SR leftStatistic rightStatistic b w c, fun _ => rfl⟩

variable (designatedLeft designatedRight : ClassKey (H := H) → Shape → Prop)
  (leftLaw : ∀ c, Shape → SL c → ℝ) (rightLaw : ∀ c, Shape → SR c → ℝ) (χ : ℝ)

def Compatible (s : Fin 3) (e : Target counts)
    (w : JointCanonicalization.RawPairs counts L R) : Prop :=
  (∀ h u, designatedLeft (h, shapeSide s u) u → ∀ a,
    |(shapeStatisticCount counts e h u
        (fun i => leftStatistic (h, shapeSide s u) (w h i).1) a : ℝ) -
      (counts h u : ℝ) * leftLaw (h, shapeSide s u) u a| ≤ (counts h u : ℝ) * χ) ∧
  (∀ h u, designatedRight (h, shapeSide s u) u → ∀ a,
    |(shapeStatisticCount counts e h u
        (fun i => rightStatistic (h, shapeSide s u) (w h i).2) a : ℝ) -
      (counts h u : ℝ) * rightLaw (h, shapeSide s u) u a| ≤ (counts h u : ℝ) * χ)

def compatibleTargetCount (s : Fin 3) (b : Position counts → Fin 17)
    (w : JointCanonicalization.RawPairs counts L R) : ℕ :=
  Fintype.card {e : FixedSideTargets counts s b //
    Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
      leftLaw rightLaw χ s e.val w}

def compatibleByTriple (s : Fin 3)
    (t : JointCoarseHashing.Triple (Position counts))
    (w : JointCanonicalization.RawPairs counts L R) : Prop :=
  ∃ e : Target counts, triple counts e = t ∧
    Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
      leftLaw rightLaw χ s e w

def compatibleWithCoarse
    (ownCoarse : JointCanonicalization.RawPairs counts L R → Position counts → Fin 17)
    (s : Fin 3) (t : JointCoarseHashing.Triple (Position counts))
    (w : JointCanonicalization.RawPairs counts L R) : Prop :=
  (∀ h i, sideWord counts s t h i = ownCoarse w ⟨h, i⟩) ∧
    compatibleByTriple counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ s t w

end Statistics

end MatrixMultiplication.JointPopulationCompatibility






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointMarginalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointAmbientDegree

open MatrixMultiplication.Foundation JointPopulation
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ)

def localWord (t : JointCoarseHashing.Triple (Position counts)) (h : H) :
    Positions counts h → Shape :=
  fun i => (t.1 ⟨h, i⟩, t.2.1 ⟨h, i⟩, t.2.2 ⟨h, i⟩)

def localAllowed (sum : H → ℕ) (h : H) (w : Positions counts h → Shape) : Prop :=
  (∀ i, (w i).1.val + (w i).2.1.val + (w i).2.2.val = sum h) ∧
    ∀ s a, wordPopulation (shapeSide s ∘ w) a =
      wordPopulation (sideWord counts s (triple counts (canonicalTarget counts)) h) a

def sameSide (s : Fin 3) (t e : JointCoarseHashing.Triple (Position counts)) : Prop :=
  ∀ h, sideWord counts s t h = sideWord counts s e h

def sharedAmbient (sum : H → ℕ) (s : Fin 3)
    (e : JointCoarseHashing.Triple (Position counts)) :
    Finset (JointCoarseHashing.Triple (Position counts)) :=
  (ambientSet counts sum).filter (sameSide counts s · e)

def classBound (s : Fin 3) (e : JointCoarseHashing.Triple (Position counts))
    (h : H) (entropyCap : ℝ) : ℝ :=
  ((Fintype.card (Positions counts h) : ℝ) + 1) ^ Fintype.card Shape *
    Real.exp ((Fintype.card (Positions counts h) : ℝ) *
      (entropyCap - finiteEntropy (fun a =>
        (wordPopulation (sideWord counts s e h) a : ℝ) /
          Fintype.card (Positions counts h))) +
      ((Fintype.card Shape : ℝ) + (Fintype.card (Fin 17) : ℝ) + 2) *
        (1 + Real.log (Fintype.card (Positions counts h) + 1 : ℕ)))

def classExponent (s : Fin 3) (e : JointCoarseHashing.Triple (Position counts))
    (h : H) (entropyCap : ℝ) : ℝ :=
  (Fintype.card (Positions counts h) : ℝ) *
      (entropyCap - finiteEntropy (fun a =>
        (wordPopulation (sideWord counts s e h) a : ℝ) /
          Fintype.card (Positions counts h))) +
    ((Fintype.card Shape : ℝ) + (Fintype.card (Fin 17) : ℝ) + 2) *
      (1 + Real.log (Fintype.card (Positions counts h) + 1 : ℕ)) +
    (Fintype.card Shape : ℝ) * Real.log (Fintype.card (Positions counts h) + 1 : ℕ)

def neighbors (sum : H → ℕ) (e : JointCoarseHashing.Triple (Position counts)) :
    Finset (JointCoarseHashing.Triple (Position counts)) :=
  (ambientSet counts sum).filter (fun t => t ≠ e ∧ JointCoarseHashing.SharesSide t e)

end MatrixMultiplication.JointAmbientDegree






namespace MatrixMultiplication.AllFieldGroupDegrees

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData JointPopulation JointCanonicalization
open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev Letter (sigma : Placement) (h : ActiveOrder K tick sigma) :=
  Fin (activeHalfLength h.val) → Fin 7

abbrev Class (sigma : Placement) := ActiveOrder K tick sigma × Fin 17

abbrev Symbol (sigma : Placement) (c : Class (K := K) (tick := tick) sigma) :=
  Statistic c.1.val

def projectedStatistic (sigma : Placement)
    (c : Class (K := K) (tick := tick) sigma) : Letter (K := K) (tick := tick) sigma c.1 → Symbol (K := K) (tick := tick) sigma c :=
  statistic c.1.val

def classDesignated (right : Bool) (side : Fin 3) (sigma : Placement)
    (c : Class (K := K) (tick := tick) sigma) (u : JointPopulation.Shape) : Prop :=
  designated right side sigma c.1 u

def classLaw (right : Bool) (side : Fin 3) (sigma : Placement)
    (c : Class (K := K) (tick := tick) sigma) (u : JointPopulation.Shape) :
    Symbol (K := K) (tick := tick) sigma c → ℝ := compatibilityLaw right side sigma c.1 u

def uniformCompatible (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Prop :=
  JointPopulationCompatibility.compatibleWithCoarse (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (ownWord allocation m sigma) (sigma side) (triple (Counts (K := K) (tick := tick) allocation m sigma) e) w

def conditionalCount (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) : ℕ :=
  JointPopulationCompatibility.compatibleTargetCount (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (sigma side) (ownWord allocation m sigma w) w

end MatrixMultiplication.AllFieldGroupDegrees






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointCompatibilityEntropyBound
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open MatrixMultiplication.Foundation
open MatrixMultiplication.JointTypeCounts MatrixMultiplication.JointCompatibilityIncidence
open scoped BigOperators

namespace MatrixMultiplication.JointCompatibilityEntropyBound

attribute [local instance] Classical.propDecidable

section ClassCounts

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

def classEntropy (counts : ∀ c, A c → ℕ) : ℝ :=
  ∑ c, (Fintype.card (Pos c) : ℝ) *
    finiteEntropy (fun a => (counts c a : ℝ) / Fintype.card (Pos c))

end ClassCounts

section GroupCounts

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable (counts : ∀ c, Shape c → ℕ)
  (designated : ∀ c, Shape c → Prop)
  (H : (Σ c, Option (Shape c)) → ℝ)
  (w : FixedClassWords Pos Shape counts)

def groupedEntropy : ℝ :=
  ∑ g : Σ c, Option (Shape c),
    (Fintype.card (GroupPos (w g.1).val (designated g.1) g.2) : ℝ) * H g

def groupedTypeError : ℝ :=
  ∑ g : Σ c, Option (Shape c),
    wordTypeError (GroupPos (w g.1).val (designated g.1) g.2) (A g.1)

end GroupCounts

section Compatibility

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape Pair Left Right : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]
variable (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
  (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
  (designatedLeft designatedRight : ∀ c, Shape c → Prop)
  (leftLaw : ∀ c, Shape c → Left c → ℝ)
  (rightLaw : ∀ c, Shape c → Right c → ℝ) (χ : ℝ)

def compatibilityExponent (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (w : FixedClassWords Pos Shape shapeCounts) : ℝ :=
  classEntropy Pos Shape shapeCounts - classEntropy Pos Pair pairCounts +
    groupedEntropy Pos Shape shapeCounts designatedLeft HL w +
    groupedEntropy Pos Shape shapeCounts designatedRight HR w +
    classTypeError Pos Shape + classTypeError Pos Pair +
    groupedTypeError Pos Shape Left shapeCounts designatedLeft w +
    groupedTypeError Pos Shape Right shapeCounts designatedRight w

end Compatibility

end MatrixMultiplication.JointCompatibilityEntropyBound

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityScaling

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityEntropyBound Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {Shape : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]

def baseEntropy (base : ∀ c, Shape c → ℕ) : ℝ :=
  ∑ c, (baseSize base c : ℝ) *
    finiteEntropy (fun a => (base c a : ℝ) / baseSize base c)

end MatrixMultiplication.JointCompatibilityScaling

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_NativeLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldNativeCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators

def indexedRationalLaw (support : List Shape) (p : Shape → ℚ)
    (hpos : ∀ u ∈ support, 0 ≤ p u) (htotal : (support.map p).sum = 1) :
    RationalLaw (Fin support.length) where
  mass j := p (support.get j)
  nonneg j := hpos _ (List.get_mem _ _)
  total := by
    simp only [List.get_eq_getElem]
    rw [Fin.sum_univ_fun_getElem]
    exact htotal

def stageASplitLaw (g : Shape) (hg : g ∈ positiveInitial) :
    FiniteLaw (Fin (below g).length) :=
  (indexedRationalLaw (below g) (stageALaw g)
    (fun u hu => (stageALaw_positive g u hu).le) (stageALaw_normalized g hg)).toFiniteLaw

def stageBSplitLaw (t : Shape) (ht : t ∈ positiveSecond) :
    FiniteLaw (Fin (below t).length) :=
  (indexedRationalLaw (below t) (stageBLaw t)
    (fun u hu => (stageBLaw_positive t u hu).le) (stageBLaw_normalized t ht)).toFiniteLaw

def indexedMarginalLaw (support : List Shape) (p : Shape → ℚ)
    (hpos : ∀ u ∈ support, 0 ≤ p u) (htotal : (support.map p).sum = 1)
    (side : Fin 3) (hbound : ∀ u ∈ support, u side < 17) : FiniteLaw (Fin 17) :=
  (indexedRationalLaw support p hpos htotal).toFiniteLaw.map
    (fun j => ⟨support.get j side, hbound _ (List.get_mem _ _)⟩)

def stageAMarginalLaw (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) :
    FiniteLaw (Fin 17) :=
  indexedMarginalLaw (below g) (stageALaw g)
    (fun u hu => (stageALaw_positive g u hu).le) (stageALaw_normalized g hg) side
    (fun _ hu => Nat.lt_succ_of_le ((below_le hu side).trans
      ((positiveInitial_shape_spec g hg).1 side)))

def stageBMarginalLaw (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) :
    FiniteLaw (Fin 17) :=
  indexedMarginalLaw (below t) (stageBLaw t)
    (fun u hu => (stageBLaw_positive t u hu).le) (stageBLaw_normalized t ht) side
    (fun _ hu => Nat.lt_succ_of_le ((below_le hu side).trans
      ((positiveSecond_shape_spec t ht).1 side)))

theorem pairLaw_total {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (q : Shape → A → ℝ)
    (hleft : ∀ u ∈ support, ∑ a, q u a = 1)
    (hright : ∀ u ∈ support, ∑ a, q (complement s u) a = 1) :
    (∑ ij : A × A, pairLaw support s p q ij) = (support.map p).sum := by
  unfold pairLaw
  induction support with
  | nil => simp
  | cons u us ih =>
      have hl := hleft u (by simp)
      have hr := hright u (by simp)
      have hh : (∑ ij : A × A, p u * q u ij.1 * q (complement s u) ij.2) = p u := by
        simp [Fintype.sum_prod_type, ← Finset.mul_sum, hl, hr]
      have ht := ih (fun v hv => hleft v (by simp [hv]))
        (fun v hv => hright v (by simp [hv]))
      simpa only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, hh] using
        congrArg (fun x => p u + x) ht

def pairFiniteLaw {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (q : Shape → A → ℝ)
    (hpos : ∀ u ∈ support, 0 ≤ p u) (htotal : (support.map p).sum = 1)
    (hqpos : ∀ u a, 0 ≤ q u a)
    (hleft : ∀ u ∈ support, ∑ a, q u a = 1)
    (hright : ∀ u ∈ support, ∑ a, q (complement s u) a = 1) : FiniteLaw (A × A) where
  mass := pairLaw support s p q
  nonneg ij := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (mul_nonneg (hpos u hu) (hqpos u ij.1))
      (hqpos (complement s u) ij.2)
  total := (pairLaw_total support s p q hleft hright).trans htotal

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationRates

open MatrixMultiplication.Foundation Filter JointPopulation
open scoped BigOperators Topology

def sideCounts (counts : Shape → ℕ) (s : Fin 3) (a : Fin 17) : ℕ :=
  ∑ u, if shapeSide s u = a then counts u else 0

end MatrixMultiplication.JointPopulationRates






namespace MatrixMultiplication.AllFieldGroupTargetRate

open AllFieldHistory AllFieldActiveLaws MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

def groupEntropyRate (allocation : Allocation) : ℝ :=
  ∑ h : ActiveOrder K tick sigma,
    ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (orderLaw h).mass

end MatrixMultiplication.AllFieldGroupTargetRate






namespace MatrixMultiplication.AllFieldPairConditionalEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldNativeCapacity
open scoped BigOperators

def stageASplitWeight (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) :
    Fin (below g).length → Fin 17 :=
  fun j => ⟨(below g).get j side,
    Nat.lt_succ_of_le ((below_le (List.get_mem _ _) side).trans
      ((positiveInitial_shape_spec g hg).1 side))⟩

def stageBSplitWeight (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) :
    Fin (below t).length → Fin 17 :=
  fun j => ⟨(below t).get j side,
    Nat.lt_succ_of_le ((below_le (List.get_mem _ _) side).trans
      ((positiveSecond_shape_spec t ht).1 side))⟩

end MatrixMultiplication.AllFieldPairConditionalEntropy






namespace MatrixMultiplication.AllFieldGroupNativeLaws

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldActiveLaws
open AllFieldNativeCapacity AllFieldPairConditionalEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def statisticComplement {K : ℕ} (w : Work K) : w.Statistic ≃ w.Statistic :=
  match w with
  | .stageA _ => CWCompleteStatistics.orderedComplementStatistic
  | .stageB _ => CWCompleteStatistics.complementStatistic
  | .stageC _ => Equiv.refl _

def halfLawAt {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) : Statistic h → ℝ :=
  if right then rightLaw h u side else leftLaw h u side

def childWeight {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) : ℕ :=
  if right then activeParentShape h side - (JointPopulation.shapeSide side u).val
  else (JointPopulation.shapeSide side u).val

theorem halfLawAt_eq {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) (a : Statistic h) :
    halfLawAt right h u side a =
      (h.val.1.childLaw
        (halfShape h.val.1.parentShape (canonicalChildShape h.val u) right)
        (h.val.2.symm side) a : ℝ) := by
  cases right <;> rfl

def supportedHalfLaw {K tick : ℕ} (allocation : Allocation) (right : Bool)
    (h : Active K tick) (u : JointPopulation.Shape) (side : Fin 3) : Statistic h → ℝ :=
  if 0 < activeCounts allocation 1 h u then halfLawAt right h u side else fun _ => 0

theorem halfShape_childWeight {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) :
    (halfShape h.val.1.parentShape (canonicalChildShape h.val u) right)
      (h.val.2.symm side) = childWeight right h u side := by
  cases right <;>
    simp [halfShape, canonicalChildShape, childWeight, activeParentShape,
      physicalShape, decodeShape, AllFieldParameters.complement]

def placedPairMixture {K : ℕ} (w : PlacedWork K) (side : Fin 3)
    (a : w.1.Statistic × w.1.Statistic) : ℝ :=
  ∑ u, (placedLaw w).mass u * childLaw w u side a.1 * rightChildLaw w u side a.2

def orderPairMixture {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3)
    (a : Statistic h.val × Statistic h.val) : ℝ :=
  ∑ u, (orderLaw h).mass u * leftLaw h.val u (sigma side) a.1 *
    rightLaw h.val u (sigma side) a.2

end MatrixMultiplication.AllFieldGroupNativeLaws






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointGibbsApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators Topology
open Filter MatrixMultiplication.Foundation

namespace MatrixMultiplication.JointGibbsApproximation

def marginalError {A B : Type*} [Fintype A] [Fintype B]
    (p q : FiniteLaw A) (f : A → B) (v : B → ℝ) : ℝ :=
  ∑ b, |(q.map f).mass b - (p.map f).mass b| * |v b|

end MatrixMultiplication.JointGibbsApproximation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointAmbientEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators Topology
open Filter MatrixMultiplication.Foundation
open MatrixMultiplication.JointPopulation MatrixMultiplication.JointAmbientDegree
open MatrixMultiplication.JointGibbsApproximation

namespace MatrixMultiplication.JointAmbientEntropy

variable {H : Type*}

def canonicalLaw (counts : H → Shape → ℕ) (h : H) : FiniteLaw Shape :=
  if hpos : 0 < Fintype.card (Positions counts h) then
    empiricalFiniteLaw ((canonicalTarget counts) h).val hpos
  else FiniteLaw.pure (0, 0, 0)

def gibbsCap (counts : H → Shape → ℕ) (h : H) (p : FiniteLaw Shape)
    (u v w : Fin 17 → ℝ) : ℝ :=
  finiteEntropy p.mass + marginalError p (canonicalLaw counts h) (shapeSide 0) u +
    marginalError p (canonicalLaw counts h) (shapeSide 1) v +
    marginalError p (canonicalLaw counts h) (shapeSide 2) w

def classScale (counts : H → Shape → ℕ) (h : H) (N : ℕ) : ℝ :=
  (Fintype.card (Positions counts h) : ℝ) / N

end MatrixMultiplication.JointAmbientEntropy

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointOrdinaryPopulationSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section

namespace MatrixMultiplication.JointOrdinaryPopulationSelection

open MatrixMultiplication.Foundation JointPopulation JointPopulationRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {Hist : Type*} [Fintype Hist] [DecidableEq Hist]

def entropyRate (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) : ℝ :=
  ∑ h, mass h * finiteEntropy (p h).mass

def uniformDegree (counts : Hist → Shape → ℕ) (sum : Hist → ℕ) : ℕ :=
  Finset.univ.sup (fun e : Target counts =>
    (JointAmbientDegree.neighbors counts sum (triple counts e)).card)

end MatrixMultiplication.JointOrdinaryPopulationSelection

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropyCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open scoped BigOperators

def weightTrace0 : List Ball := [
  ⟨(45822469347703230916837028446061 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(95761729883054217060631522574569 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1518032241603819172753264716571 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3261876795622354777174156430543 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4095003862446164503471876088913 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(205341225223953618638702205277 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137176467343829037379890181127 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19626959451965561090978938867 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1228161761087584971721304317 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(54637558371312300664525013 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27340322092271316640462777 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2487117682933565567802199 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103687562373860905549233 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15959542323714148962659 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(285109727917665106419 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76054635388880697247 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare0_1 : Ball := ⟨(83987947884848086426829976722031 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare0_2 : Ball := ⟨(70539753899079581546921669791051 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def weightSquare0_3 : Ball := ⟨(49758568801427130276705189494043 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def weightSquare0_4 : Ball := ⟨(12379575845831786800610165591697 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def weightSquare0_5 : Ball := ⟨(61301559249080719838295497489 / 1000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare0_6 : Ball := ⟨(375788116636855394790068879267 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩

def weightTrace1 : List Ball := [
  ⟨(47255022421610958409873827160341 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97229191696542968020629859555673 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49072067803428631784511439365999 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16434031762616588480302150310221 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(164802101549160184047696785151 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(825553916487359822440105826453 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137776428077124469979954185547 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9851051824020091619644825781 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2464686157317462422255187163 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137012571857256431690259327 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13708263777035553765322303 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2493473966999507375380809 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103932227199065796269981 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3198903658586015670193 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(571385949173744347803 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76201768611384910161 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare1_1 : Ball := ⟨(89321485762678176318205827626583 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare1_2 : Ball := ⟨(1595665563770464030669190950117 / 2000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare1_3 : Ball := ⟨(31826857392536410151645281386261 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def weightSquare1_4 : Ball := ⟨(810359081187879632371486932441 / 2000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def weightSquare1_5 : Ball := ⟨(16417046011591612337241268965321 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def weightSquare1_6 : Ball := ⟨(2695193997467160660436803279809 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩

def weightTrace2 : List Ball := [
  ⟨(19462084945085296406442948535709 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(98649101709384577877389230656831 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24774339675450460154475682836493 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16553683043349819604053296423209 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(518006181749542381171965125597 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103695169558496726647696312179 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138349773272399157380263337543 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(308966483173666977262623271 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2472665918923664623838816993 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137411862870134171885457943 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3436146482162016182737377 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(2499530900421064933309269 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208330586210581940821979 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(125217395867685532157 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(143124148124781859341 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19085332337372655453 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare2_1 : Ball := ⟨(94693187602428936210099773718353 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare2_2 : Ball := ⟨(44833998891544005922143607529859 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare2_3 : Ball := ⟨(10050437283034845758507319035581 / 12500000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def weightSquare2_4 : Ball := ⟨(64647225331338785478344935394587 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
def weightSquare2_5 : Ball := ⟨(41792637430408911418759860943933 / 100000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
def weightSquare2_6 : Ball := ⟨(2183280679237019972788253432353 / 12500000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩

def weightTrace3 : List Ball := [
  ⟨(99722261409261526095071612219837 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(99861066332934437727060774889811 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49953678046044862180395545236147 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8327542284069720378328946310521 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(26027187701631258446683248593 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(832947202036967261967421765977 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27766744907223109458809337961 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9917187015432196825563880161 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2479392505329480885756231427 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55099313563992663293648747 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27550353220886312747669859 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2504630327938123105603659 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208722914534389897186987 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8027927063567209908089 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(229372382000523736751 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76458344396867462343 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare3_1 : Ball := ⟨(99445294205770906125170809966217 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare3_2 : Ball := ⟨(9889366539672332554869689802191 / 10000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare3_3 : Ball := ⟨(24449892638997681165967353683633 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def weightSquare3_4 : Ball := ⟨(23911890002340519753388331266581 / 25000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def weightSquare3_5 : Ball := ⟨(45742278678722600142174067342087 / 50000000000000000000000000000000), (11 / 20000000000000000000000000000000)⟩
def weightSquare3_6 : Ball := ⟨(83694242348876807273467974770337 / 100000000000000000000000000000000), (51 / 50000000000000000000000000000000)⟩

def weightTrace4 : List Ball := [
  ⟨(50911410227239288182312346605491 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(20181733256055512038055594758737 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50302432261710796797673490870941 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8371103169920852457012116486571 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2090882745092313740543310965499 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104481089995403957581214526993 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34812028439039215519527827849 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19886161668670775979789845573 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(621286427138617212332161333 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(276071808085179654271380119 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27602641726950831010849701 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2508987275976284863517391 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52264509050953876130863 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16079789645021142467363 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1148457507801906020393 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76557974095447743761 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare4_1 : Ball := ⟨(1036788676530498075661364538317 / 1000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare4_2 : Ball := ⟨(107493075978186177125241613635047 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def weightSquare4_3 : Ball := ⟨(14443451729065132700277449317601 / 12500000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def weightSquare4_4 : Ball := ⟨(133512510623894125738161773133231 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
def weightSquare4_5 : Ball := ⟨(11140994058184651120224401477951 / 6250000000000000000000000000000), (113 / 100000000000000000000000000000000)⟩
def weightSquare4_6 : Ball := ⟨(317751676427534595662029560374059 / 100000000000000000000000000000000), (101 / 25000000000000000000000000000000)⟩

def weightTrace5 : List Ball := [
  ⟨(103600813901653687360089808813237 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(101789792272895755762256079526159 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12648708642372832242092434813847 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16815111505055235854974961283079 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2098160259909105135099570549999 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(167654293436288924565226478201 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(17449236212407383366781122517 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4982337882474756504311598923 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(31124271600418638659055071 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(276551176671687180049383751 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27646203019880523641287881 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2512616138364183427012361 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4186741947709709968707 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8049858753420616865717 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(574892862468114940523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76640711328831368513 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare5_1 : Ball := ⟨(13416410801356349903607034777723 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare5_2 : Ball := ⟨(115200050426080854395202845284257 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare5_3 : Ball := ⟨(132710516181715716422850695559233 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def weightSquare5_4 : Ball := ⟨(176120811052174290165929815923193 / 100000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
def weightSquare5_5 : Ball := ⟨(62037080171351355194935848106531 / 20000000000000000000000000000000), (87 / 50000000000000000000000000000000)⟩
def weightSquare5_6 : Ball := ⟨(962149829046668872508647133711623 / 100000000000000000000000000000000), (27 / 2500000000000000000000000000000)⟩

def weightTrace6 : List Ball := [
  ⟨(52496907097213613827039425021221 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(102476628332481265185663204667291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50822179453251562101591990094477 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16871708672598427120010057088159 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(84152163522076882223784705499 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(840148968827547918893289383799 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69930850267688450018787230643 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(159702309542728519984293019 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2493653488700243236021188337 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(276922068313722247860040669 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27679898912162961846196791 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(503084522465855867187777 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(26194110004123274166153 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3223024873382905372317 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(46032498729593238173 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(9588068402869008441 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare6_1 : Ball := ⟨(11023701019093908391497969098631 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def weightSquare6_2 : Ball := ⟨(121521984158372074423106444564011 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def weightSquare6_3 : Ball := ⟨(18459490792234541766581018912859 / 12500000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def weightSquare6_4 : Ball := ⟨(218081792197498771472088623185963 / 100000000000000000000000000000000), (3 / 4000000000000000000000000000000)⟩
def weightSquare6_5 : Ball := ⟨(237798340440365180199344472936997 / 50000000000000000000000000000000), (41 / 12500000000000000000000000000000)⟩
def weightSquare6_6 : Ball := ⟨(226192202864767271537325845748747 / 10000000000000000000000000000000), (39 / 1250000000000000000000000000000)⟩

def weightTrace7 : List Ball := [
  ⟨(13238388542478214491069816710213 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(102925303898300024346667979534741 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(25485209971305104433142398821633 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(8454286069948186469498114558423 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4214954748496148057251911685369 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(841370296775696005405701232473 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(140035844466856609575439150853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4996131128333977017996839571 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(499213144876440899368362439 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27716305853430552915679447 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27701789454298507636100787 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2517245580029807777294919 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41938605269701210777891 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16125129745665541975627 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1151479177264804137941 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38372970988705270699 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare7_1 : Ball := ⟨(11216315596903581711527855028257 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare7_2 : Ball := ⟨(125805735569342550503356966593139 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def weightSquare7_3 : Ball := ⟨(158270831021433413898498261129081 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def weightSquare7_4 : Ball := ⟨(31312069940268911822779912641567 / 12500000000000000000000000000000), (67 / 100000000000000000000000000000000)⟩
def weightSquare7_5 : Ball := ⟨(125497052664869372826269098660877 / 20000000000000000000000000000000), (337 / 100000000000000000000000000000000)⟩
def weightSquare7_6 : Ball := ⟨(393737755689224923790566075091771 / 10000000000000000000000000000000), (423 / 10000000000000000000000000000000)⟩

def weightTrace8 : List Ball := [
  ⟨(53107840245772877522502511762089 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(103076607534767528536346359585271 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5102036178196093237793563948317 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3384196825616027372211588988827 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(131794605971792912907148072173 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(420890623113675921432978149363 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(70047213901119971249691626091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2498979428084996990116058961 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2496876982418733363454750399 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34655512160242955405574419 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(27709150025502850262332103 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(62946462422495109382441 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(41948028645634175042909 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16128493345257602942617 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(28792582462514276983 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76759847269274455947 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare8_1 : Ball := ⟨(28204426955705333720136269142093 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare8_2 : Ball := ⟨(31819587995988705552098445079421 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare8_3 : Ball := ⟨(161997788837514964265321695821339 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
def weightSquare8_4 : Ball := ⟨(52486567176488175914387270062549 / 20000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
def weightSquare8_5 : Ball := ⟨(344354966746500746353077958219731 / 50000000000000000000000000000000), (83 / 25000000000000000000000000000000)⟩
def weightSquare8_6 : Ball := ⟨(592901715614918174080204664509561 / 12500000000000000000000000000000), (2287 / 50000000000000000000000000000000)⟩

def weightTrace9 : List Ball := [
  ⟨(105769353286979812971192319657867 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(12857213854765865443628769642581 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50948101186729931232361150203779 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16903024110177614037303920285779 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(842769869335374211420370584613 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52574160131711393877303756643 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(140009649991401748572542612153 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19981255379359022718212237153 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(62392573665020423810114129 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(277126818288917152811301887 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27698497726817026655144159 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(39327679210857430103861 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(104835977052347421176833 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16123625401104954019783 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(287844734674196536367 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38369860594472552971 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare9_1 : Ball := ⟨(699197255921621710400340726909 / 625000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare9_2 : Ball := ⟨(31288115372052849022082108910093 / 25000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def weightSquare9_3 : Ball := ⟨(783156930827911832787526073193 / 500000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def weightSquare9_4 : Ball := ⟨(61333477830379467923854252642317 / 25000000000000000000000000000000), (67 / 100000000000000000000000000000000)⟩
def weightSquare9_5 : Ball := ⟨(601887280443143949422394537773243 / 100000000000000000000000000000000), (33 / 10000000000000000000000000000000)⟩
def weightSquare9_6 : Ball := ⟨(3622682983592438129289817987640667 / 100000000000000000000000000000000), (3973 / 100000000000000000000000000000000)⟩

def weightTrace10 : List Ball := [
  ⟨(104643817941585644011055002692351 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(102304343486104167397858997043291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6345650025415076652394745911099 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16857530898254533759977249142099 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2102390764796993902426298307757 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(839678918917955610443536100733 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6989733183295338113197086393 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3990884012883817837828762809 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(623181153966461295253418909 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138414630349275657661540399 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(6917866971559857065203159 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2514720451697499889277579 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(209498895670714520474879 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16111270073369578912207 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(287638905637475131677 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3067543529976875711 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare10_1 : Ball := ⟨(109503286333917215300234963650589 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare10_2 : Ball := ⟨(23981939435855721532382233715047 / 20000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def weightSquare10_3 : Ball := ⟨(143783354776262960787841124947381 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
def weightSquare10_4 : Ball := ⟨(206736531107167007786767430192403 / 100000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
def weightSquare10_5 : Ball := ⟨(427399932942246318664573400014931 / 100000000000000000000000000000000), (49 / 20000000000000000000000000000000)⟩
def weightSquare10_6 : Ball := ⟨(913353513395183249684030644938607 / 50000000000000000000000000000000), (419 / 20000000000000000000000000000000)⟩

def weightTrace11 : List Ball := [
  ⟨(51457318287274132865276567057379 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1014503403334361270220267489773 / 1000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50482287126726561924028897888317 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(3357412966824382785429865106037 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1047680795825287522555360752867 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(418670001796633248356362121959 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69730488017545672562413193419 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3982550427688823527492235683 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1244049333538284529198387107 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69091744539850108590769427 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5525893169158403393733513 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2511221947893666302852981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(209229889795857520126909 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8046031081551623817853 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1149275510972162029753 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76608950208370987967 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare11_1 : Ball := ⟨(105914224212713475942880094061453 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare11_2 : Ball := ⟨(56089114452904707614563249114169 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare11_3 : Ball := ⟨(62919775202220875163649729179661 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
def weightSquare11_4 : Ball := ⟨(9897245278745022430232851573857 / 6250000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
def weightSquare11_5 : Ball := ⟨(250765988115560030064146963919903 / 100000000000000000000000000000000), (7 / 5000000000000000000000000000000)⟩
def weightSquare11_6 : Ball := ⟨(314417903977865971190225770587881 / 50000000000000000000000000000000), (703 / 100000000000000000000000000000000)⟩

def weightTrace12 : List Ball := [
  ⟨(50299565702744265076996558074139 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(50149633731710606664346630250871 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(10019941228855690837754994565271 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16691585754174909970175937448921 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2085824745654684049952040366639 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(834163685934846265222339166067 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69503749014945907528607500637 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1241005922081361949527725719 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1240902916616263466583660047 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(55147578719850151178826729 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(13786145698506878875057519 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(250645847183754706694749 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208863538519519027742349 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(16065898544688539931839 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1147531528860113200627 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7650018722732584753 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare12_1 : Ball := ⟨(50600926197693743461694777077217 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare12_2 : Ball := ⟨(20483629856515592049753749622719 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare12_3 : Ball := ⟨(5244738651234212176799626520019 / 5000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def weightSquare12_4 : Ball := ⟨(110029134079000252453786194910311 / 100000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def weightSquare12_5 : Ball := ⟨(60532051730873073663919899910177 / 50000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
def weightSquare12_6 : Ball := ⟨(29313034293992750986222098316009 / 20000000000000000000000000000000), (173 / 100000000000000000000000000000000)⟩

def weightTrace13 : List Ball := [
  ⟨(97749308384307458995717295526927 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(386212440059808669826807686367 / 390625000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(620284354280447813487395038807 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(16572246608625983214041733343471 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207388417688370545953590935703 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(166036382119894000421479712647 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(138438502963314708257138641127 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1978495383124961248679789739 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(309237476945452854929631139 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274947171450935846495308899 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3437549805329453114224957 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1250233374430986093929039 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(208402594317235319799913 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8016485665633495607099 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(286334057844721094857 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15272567399497273009 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare13_1 : Ball := ⟨(95549272896104404998317042425221 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare13_2 : Ball := ⟨(91296635509742318701678139152337 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare13_3 : Ball := ⟨(41675378276993710444793986953517 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
def weightSquare13_4 : Ball := ⟨(34736743090610384990883814056083 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def weightSquare13_5 : Ball := ⟨(24132826410861366426580373032961 / 50000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
def weightSquare13_6 : Ball := ⟨(23295732423070716039874970270233 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩

def weightTrace14 : List Ball := [
  ⟨(9397419149312240765671878406229 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(96955889088939538910397682022679 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(23916046352232353441792145211 / 48828125000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3282178827443733390859812092909 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(4115406748962183626188354016423 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(412388718459236045682322206297 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(34416317034840072279521000559 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2461023229140385701538388279 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(492627540295271625210502361 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(68467532913805441181202433 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27402422922560608218237489 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2492297689867778508766373 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207773912733602071421357 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(15988047386627809666029 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(571170154415164387469 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38087296400995144381 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare14_1 : Ball := ⟨(88311486667860398901944158266739 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare14_2 : Ball := ⟨(77989186774876849812044262325737 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare14_3 : Ball := ⟨(60823132538066261346053024041467 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def weightSquare14_4 : Ball := ⟨(1156079203669742114596957224833 / 3125000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
def weightSquare14_5 : Ball := ⟨(3421488960403622578089278590681 / 25000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def weightSquare14_6 : Ball := ⟨(117065867061638619900413203703 / 6250000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩

def weightTrace15 : List Ball := [
  ⟨(94147322024652654828833510491163 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(97044248516044896355939512038323 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(49009817859248311627512106727623 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1641837841548993622447410991039 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(823381940790235157278803689397 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(206257164476878098440948109979 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(137701235103513169711025747113 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19692689326920054765335269601 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2463638768430057590648224087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(273920293962133881870515871 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(27406987350225809089504263 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1246339178279343493885119 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(207803214433657946794709 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(1998767697855936571617 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(114247998713503541457 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(76183390027455214293 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare15_1 : Ball := ⟨(44318591222068234326289200916567 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def weightSquare15_2 : Ball := ⟨(61379297747149485991007624471 / 78125000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def weightSquare15_3 : Ball := ⟨(1928918114269813742751307284463 / 3125000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def weightSquare15_4 : Ball := ⟨(2381264058597257105709481658969 / 6250000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def weightSquare15_5 : Ball := ⟨(14516271402923727674314000842103 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def weightSquare15_6 : Ball := ⟨(2107221354433412088486138736011 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩

def weightTrace16 : List Ball := [
  ⟨(96363397544038665735902571610653 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3926818916509623635941208316487 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(24694139865151464166961931335581 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3302690843648775656223451075217 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(165439458394777402989072424451 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(82821546947141128907996775141 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(69078641632151769912138780799 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(19749772217589986559441937981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(154374259625197756705469647 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(274555792962808879841926837 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1373240124245016613661353 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(249749928356493009833667 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(52043563214049462922493 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(8008328294019073421673 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(228849664429048117677 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(38147293777383269777 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4779477332387385297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def weightSquare16_1 : Ball := ⟨(5803690241394023222060139461611 / 6250000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def weightSquare16_2 : Ball := ⟨(17245604054042734355635644885209 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def weightSquare16_3 : Ball := ⟨(116176116870630935339684428353 / 156250000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def weightSquare16_4 : Ball := ⟨(11056652395428657424319758888073 / 20000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def weightSquare16_5 : Ball := ⟨(30562390548334567074915733474673 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def weightSquare16_6 : Ball := ⟨(2335149290072325198800662941033 / 25000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩

def weightBall : Fin 17 → Ball := (Matrix.vecCons (weightSquare0_6) (Matrix.vecCons (weightSquare1_6) (Matrix.vecCons (weightSquare2_6) (Matrix.vecCons (weightSquare3_6) (Matrix.vecCons (weightSquare4_6) (Matrix.vecCons (weightSquare5_6) (Matrix.vecCons (weightSquare6_6) (Matrix.vecCons (weightSquare7_6) (Matrix.vecCons (weightSquare8_6) (Matrix.vecCons (weightSquare9_6) (Matrix.vecCons (weightSquare10_6) (Matrix.vecCons (weightSquare11_6) (Matrix.vecCons (weightSquare12_6) (Matrix.vecCons (weightSquare13_6) (Matrix.vecCons (weightSquare14_6) (Matrix.vecCons (weightSquare15_6) (Matrix.vecCons (weightSquare16_6) Matrix.vecEmpty)))))))))))))))))

def sourceWeightBall (k : ℕ) : Ball := weightBall ⟨k % 17, Nat.mod_lt _ (by decide)⟩

def listSumBall {α : Type*} (xs : List α) (b : α → Ball) : Ball :=
  xs.foldr (fun x a => .add (b x) a) (.exact 0)

def finSumBall : (n : ℕ) → (Fin n → Ball) → Ball
  | 0, _ => .exact 0
  | n+1, b => .add (b 0) (finSumBall n (fun i => b i.succ))

def initialRawBall (s : Shape) : Ball :=
  .mul (.exact (initialMultiplicity s))
    (.mul (sourceWeightBall (s 0))
      (.mul (sourceWeightBall (s 1)) (sourceWeightBall (s 2))))

def initialDenominatorBall : Ball := listSumBall sortedInitial initialRawBall

def initialLawBall (s : Shape) : Ball :=
  .mul (initialRawBall s) (.inv initialDenominatorBall)

def initialMarginalBall (k : Fin 17) : Ball :=
  finSumBall sortedInitial.length (fun g =>
    .mul (initialLawBall (sortedInitial.get g))
      (.exact ((∑ w : Fin 3, if sortedInitial.get g w = k.val then (1 : ℚ) else 0) / 3)))

def roundedMarginal : Fin 17 → Ball := (Matrix.vecCons (⟨(37824257369353410027720060279 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(32277877294971248510635537179 / 6250000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(1311429618383774862762137339319 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(8221633968389025907864338663411 / 100000000000000000000000000000000), (3 / 5000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(3458333166749295114800388945299 / 20000000000000000000000000000000), (1 / 781250000000000000000000000000)⟩) (Matrix.vecCons (⟨(24885489904708998392039676962479 / 100000000000000000000000000000000), (181 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(24112146157967309906901428396197 / 100000000000000000000000000000000), (91 / 50000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(3779863608787839049947557982127 / 25000000000000000000000000000000), (111 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(5764358674456721497871303174559 / 100000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(1226948071890256520646842010821 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(151656043521920341821121947439 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(2239268756742155430560743707 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(484478437366253348343232821 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(3038569022328601883975409 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(7930177818229705654311 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(14180164171909061741993 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(4381963528820193732059 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩) Matrix.vecEmpty)))))))))))))))))

def logTwoTrace : List Ball := [
  ⟨(20794415416798359282516957915099 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(35748693755926167713263106179463 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(5434560950833877354841988903793 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3128838846003916954862320107311 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3056579874686922885058244064393 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2007375097745844772419357263631 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4256848790190598288526447522607 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(7392508992661538424245286176159 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1633145233488461454551893896359 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(1463012983749094267437633302527 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(662505795291976835048297229793 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩,
  ⟨(2421637201939737490310128843981 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4459034852306579173408406148187 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(4131313670759212560675655333689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(240530606468723732046722791867 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(450240571609440969944458529469 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(84626577284090520093573740141 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3192840549545314506413819178039 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(3021279231622116272010086888069 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2867188760274722123766457668297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(340971970693677773852649492219 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2598762377749677766171251244647 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(2458628841607565011820330969267 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩,
  ⟨(531914893617021276595744680851 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩]
def logTwoBall : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
def marginalLogWitness : Fin 17 → LogWitness := (Matrix.vecCons (⟨-11, 37824257369353410027720060279, 24414062500000000000000000000⟩) (Matrix.vecCons (⟨-8, 32277877294971248510635537179, 24414062500000000000000000000⟩) (Matrix.vecCons (⟨-6, 1311429618383774862762137339319, 781250000000000000000000000000⟩) (Matrix.vecCons (⟨-4, 8221633968389025907864338663411, 6250000000000000000000000000000⟩) (Matrix.vecCons (⟨-3, 3458333166749295114800388945299, 2500000000000000000000000000000⟩) (Matrix.vecCons (⟨-3, 24885489904708998392039676962479, 12500000000000000000000000000000⟩) (Matrix.vecCons (⟨-3, 24112146157967309906901428396197, 12500000000000000000000000000000⟩) (Matrix.vecCons (⟨-3, 3779863608787839049947557982127, 3125000000000000000000000000000⟩) (Matrix.vecCons (⟨-5, 5764358674456721497871303174559, 3125000000000000000000000000000⟩) (Matrix.vecCons (⟨-7, 1226948071890256520646842010821, 781250000000000000000000000000⟩) (Matrix.vecCons (⟨-10, 151656043521920341821121947439, 97656250000000000000000000000⟩) (Matrix.vecCons (⟨-14, 2239268756742155430560743707, 1220703125000000000000000000⟩) (Matrix.vecCons (⟨-18, 484478437366253348343232821, 381469726562500000000000000⟩) (Matrix.vecCons (⟨-23, 3038569022328601883975409, 2980232238769531250000000⟩) (Matrix.vecCons (⟨-30, 31720711272918822617244, 23283064365386962890625⟩) (Matrix.vecCons (⟨-33, 28360328343818123483986, 23283064365386962890625⟩) (Matrix.vecCons (⟨-35, 35055708230561549856472, 23283064365386962890625⟩) Matrix.vecEmpty)))))))))))))))))
def marginalLogBall : Fin 17 → Ball := (Matrix.vecCons (⟨(-359341382912849805381766834083483 / 50000000000000000000000000000000), (254109886839 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-526595466063060246707895328811773 / 100000000000000000000000000000000), (38116482823 / 20000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-182045257575976223204856091760809 / 50000000000000000000000000000000), (9264422909 / 6250000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-249840121706468106425374731856733 / 100000000000000000000000000000000), (13234889893 / 12500000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-175494554427421837074873290309581 / 100000000000000000000000000000000), (5293955967 / 6250000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-139088528712395736536901400948077 / 100000000000000000000000000000000), (84703295459 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-27782314111222943517224434997 / 19531250000000000000000000000), (84703295487 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-7556751592875787652219540186071 / 4000000000000000000000000000000), (42351647733 / 50000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-142673814156440611744929044763629 / 50000000000000000000000000000000), (31763735711 / 25000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-440064034235271909031072697214261 / 100000000000000000000000000000000), (169406590279 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-649131037985310617044853658780989 / 100000000000000000000000000000000), (29116757729 / 12500000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-113716727348098189960178186941083 / 12500000000000000000000000000000), (317637364177 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-305940195463298290399109426509441 / 25000000000000000000000000000000), (6286575881 / 1562500000000000000000000000000)⟩) (Matrix.vecCons (⟨(-1592299969457533467596519841341019 / 100000000000000000000000000000000), (508227995949 / 100000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-81940687367260669107912929811931 / 4000000000000000000000000000000), (32861933139 / 5000000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-2267659192418886369231475949409093 / 100000000000000000000000000000000), (90878763719 / 12500000000000000000000000000000)⟩) (Matrix.vecCons (⟨(-1192546955237440450086597482595127 / 50000000000000000000000000000000), (392575236187 / 50000000000000000000000000000000)⟩) Matrix.vecEmpty)))))))))))))))))
def totalMarginalBall : Ball := ⟨(99999999999999999999999999999989 / 100000000000000000000000000000000), (3 / 400000000000000000000000000000)⟩
def totalLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999989, 50000000000000000000000000000000⟩
def totalLogBall : Ball := ⟨(-11 / 100000000000000000000000000000000), (10587912029 / 25000000000000000000000000000000)⟩

def entropySumBall : Ball :=
  finSumBall 17 (fun k => .neg (.mul (roundedMarginal k) (marginalLogBall k)))

def initialEntropyRawBall : Ball := .add
  (.mul totalMarginalBall totalLogBall) entropySumBall

def initialEntropyBall : Ball := ⟨(92057368710548199998533979957297 / 50000000000000000000000000000000), (2107346571 / 1562500000000000000000000000000)⟩

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldVolumeCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldTerminalRates
open scoped BigOperators

def zeroLeafShape (k : Fin 9) : Shape := shape 0 k.val (16-k.val)
def zeroLeafCoefficient (k : Fin 9) : ℕ :=
  Contractions.coefficients[shapeMax (zeroLeafShape k)]?.getD 0

def leafLogWitness0 : LogWitness := ⟨0, 1, 1⟩
def leafRateBall0 : Ball := ⟨0, (10587911841 / 50000000000000000000000000000000)⟩

def leafLogWitness1 : LogWitness := ⟨5, 5, 4⟩
def leafRateBall1 : Ball := ⟨(368887945411393630285245474282633 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩

def leafLogWitness2 : LogWitness := ⟨9, 177, 128⟩
def leafRateBall2 : Ball := ⟨(164061102342342994021143953374117 / 25000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩

def leafLogWitness3 : LogWitness := ⟨12, 455, 256⟩
def leafRateBall3 : Ball := ⟨(889288614119073165342852571257363 / 100000000000000000000000000000000), (275285707879 / 100000000000000000000000000000000)⟩

def leafLogWitness4 : LogWitness := ⟨15, 23989, 16384⟩
def leafRateBall4 : Ball := ⟨(269462446287246686158044077687313 / 25000000000000000000000000000000), (21175823683 / 6250000000000000000000000000000)⟩

def leafLogWitness5 : LogWitness := ⟨17, 26355, 16384⟩
def leafRateBall5 : Ball := ⟨(9577230336694643113727840367767 / 781250000000000000000000000000), (190582413147 / 50000000000000000000000000000000)⟩

def leafLogWitness6 : LogWitness := ⟨19, 38941, 32768⟩
def leafRateBall6 : Ball := ⟨(1334239168137038775559946496265297 / 100000000000000000000000000000000), (423516473659 / 100000000000000000000000000000000)⟩

def leafLogWitness7 : LogWitness := ⟨20, 152675, 131072⟩
def leafRateBall7 : Ball := ⟨(43798463436784910719256790204483 / 3125000000000000000000000000000), (222346148671 / 50000000000000000000000000000000)⟩

def leafLogWitness8 : LogWitness := ⟨20, 1542195, 1048576⟩
def leafRateBall8 : Ball := ⟨(1424871728425409722017918230467949 / 100000000000000000000000000000000), (222346148671 / 50000000000000000000000000000000)⟩

def leafRateBall : Fin 9 → Ball := (Matrix.vecCons (leafRateBall0) (Matrix.vecCons (leafRateBall1) (Matrix.vecCons (leafRateBall2) (Matrix.vecCons (leafRateBall3) (Matrix.vecCons (leafRateBall4) (Matrix.vecCons (leafRateBall5) (Matrix.vecCons (leafRateBall6) (Matrix.vecCons (leafRateBall7) (Matrix.vecCons (leafRateBall8) Matrix.vecEmpty)))))))))
def initialVolumeRawBall : Ball := finSumBall 9 (fun k =>
  .mul (initialLawBall (zeroLeafShape k)) (leafRateBall k))

def initialVolumeBall : Ball := ⟨(3170407140796466915468826036527 / 100000000000000000000000000000000), (249845433 / 25000000000000000000000000000000)⟩
end MatrixMultiplication.AllFieldVolumeCertificate

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

instance designatedDecidable (priority : Placement) (position : Fin 3) (u : Shape) :
    Decidable (designated priority position u) := by
  unfold designated
  infer_instance

def marginalBall (support : List Shape) (p : Shape → Ball) (side : Fin 3) (k : Fin 17) : Ball :=
  listSumBall support fun u => if u side = k.val then p u else .exact 0

def residualBall {A : Type*} (support : List Shape) (p : Shape → Ball)
    (priority : Placement) (position : Fin 3) (q : Shape → A → Ball)
    (k : Fin 17) (a : A) : Ball :=
  listSumBall support fun u =>
    if ¬ designated priority position u ∧ u (priority position) = k.val
    then .mul (p u) (q u a) else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

def sparseTripleBall (a b c : Ball) : Ball :=
  if b = .exact 0 ∨ c = .exact 0 then .exact 0 else .mul (.mul a b) c

def sparsePairLawBall {A : Type*} (support : List Shape) (s : Shape) (p : Shape → Ball)
    (q : Shape → A → Ball) (ij : A × A) : Ball :=
  listSumBall support fun u => sparseTripleBall (p u) (q u ij.1) (q (complement s u) ij.2)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Zero0_1_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_0_8H2H : Ball := ⟨0, 0⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_1_14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A1_1_14Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(36782530045362665672288806008641 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨1, 0⟩
  | 1, 0, 7 => ⟨1, 0⟩
  | 1, 1, 6 => ⟨(36782530045362665672288806008641 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_1_14Den : Ball := ⟨(86782530045362665672288806008641 / 25000000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
def A1_1_14Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(211923586614355608536476757861 / 1000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(288076413385644391463523242139 / 1000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(288076413385644391463523242139 / 1000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(211923586614355608536476757861 / 1000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_1_14Law (u : Shape) : Ball := if u ∈ below (shape 1 1 14) then A1_1_14Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_1_14I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_1_14I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_1_14I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 1 14)) A1_1_14Law ((Equiv.refl (Fin 3)) 0) a
def CA1_1_14I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (47 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823763 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647459 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CA1_1_14I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I0Certificates (CA1_1_14I0CertificateIndex a)).input
def CA1_1_14I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I0Certificates (CA1_1_14I0CertificateIndex a)).output
def CA1_1_14I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823763 / 50000000000000000000000000000000)⟩
def CA1_1_14I0Mass : Ball := ⟨1, (47 / 50000000000000000000000000000000)⟩
def CA1_1_14I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_1_14I0MassTermLog : Ball := ⟨0, (661744493 / 3125000000000000000000000000000)⟩
def CA1_1_14I0MassTerm : Ball := ⟨0, (21175823777 / 100000000000000000000000000000000)⟩
def CA1_1_14I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471303 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB5_1_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B1_5_2Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(56462132148426838393857212178007 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨1, 0⟩
  | 0, 4, 0 => ⟨(2259560185112186440866498136737 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(2259560185112186440866498136737 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨1, 0⟩
  | 1, 3, 0 => ⟨(56462132148426838393857212178007 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_5_2Den : Ball := ⟨(19840211541692378104340463789343 / 6250000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
def B1_5_2Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(17786520329488695683714185635709 / 100000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(31501680246030645200554309297569 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(355899712240329557865752533361 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(355899712240329557865752533361 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(31501680246030645200554309297569 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(17786520329488695683714185635709 / 100000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_5_2Law (u : Shape) : Ball := if u ∈ below (shape 1 5 2) then B1_5_2Table u else .exact 0
def B2_5_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(112833961011546491885255896167 / 200000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(2250539996775325991305899209651 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨1, 0⟩
  | 1, 3, 0 => ⟨1, 0⟩
  | 2, 1, 1 => ⟨(2250539996775325991305899209651 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(112833961011546491885255896167 / 200000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_5_1Den : Ball := ⟨(158667520502548571933933847293151 / 50000000000000000000000000000000), (17 / 12500000000000000000000000000000)⟩
def B2_5_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(3555672914474456486072088812043 / 20000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(354599982032740129828053827979 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(31512435463562237309983448283827 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(31512435463562237309983448283827 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(354599982032740129828053827979 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(3555672914474456486072088812043 / 20000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_5_1Law (u : Shape) : Ball := if u ∈ below (shape 2 5 1) then B2_5_1Table u else .exact 0
def B3_2_3Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => ⟨(512717732641430446854909688781 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(231490015436085315425174308889 / 6250000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(147355736582479520245291292481 / 4000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 1, 2, 1 => ⟨(12896756232056427378688678611447 / 25000000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(12896756232056427378688678611447 / 25000000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 2, 2, 0 => ⟨(147355736582479520245291292481 / 4000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(231490015436085315425174308889 / 6250000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(512717732641430446854909688781 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_2_3Den : Ball := ⟨(79743738161203246507272347694409 / 25000000000000000000000000000000), (11 / 6250000000000000000000000000000)⟩
def B3_2_3Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => ⟨(160739182932759974729119067149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(232233924091318151167807188021 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(230983240785310211157876817529 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(6270084793231563529856005696979 / 20000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(8086375513263140282181216210103 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(8086375513263140282181216210103 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(6270084793231563529856005696979 / 20000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(230983240785310211157876817529 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(232233924091318151167807188021 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(160739182932759974729119067149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_2_3Law (u : Shape) : Ball := if u ∈ below (shape 3 2 3) then B3_2_3Table u else .exact 0
def B5_1_2Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => ⟨(1134875559173888664169867750871 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(11280011590026355871190756294713 / 20000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 3, 0, 1 => ⟨1, 0⟩
  | 3, 1, 0 => ⟨(11280011590026355871190756294713 / 20000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(1134875559173888664169867750871 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B5_1_2Den : Ball := ⟨(158669809068479556684293516975307 / 50000000000000000000000000000000), (1 / 625000000000000000000000000000)⟩
def B5_1_2Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => ⟨(715243539925161855344559597823 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(4443193878631184933728583933647 / 25000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(31511980945550098409741104667589 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(31511980945550098409741104667589 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(4443193878631184933728583933647 / 25000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(715243539925161855344559597823 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B5_1_2Law (u : Shape) : Ball := if u ∈ below (shape 5 1 2) then B5_1_2Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_3_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_3_5H2H : Ball := ⟨(29685281684392957375419947125681 / 25000000000000000000000000000000), (94620828753 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_4_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_4_4H2H : Ball := ⟨(24557687119432730763339027270733 / 20000000000000000000000000000000), (105080949871 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_1_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B1_1_6Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(381491111844670997969310464477 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨1, 0⟩
  | 1, 0, 3 => ⟨1, 0⟩
  | 1, 1, 2 => ⟨(381491111844670997969310464477 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_1_6Den : Ball := ⟨(20381491111844670997969310464477 / 10000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def B1_1_6Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(935876354068540274256216050051 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(49064123645931459725743783949949 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(49064123645931459725743783949949 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(935876354068540274256216050051 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_1_6Law (u : Shape) : Ball := if u ∈ below (shape 1 1 6) then B1_1_6Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_3_12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_2_6H2H : Ball := ⟨(108012340224774987609734627692581 / 100000000000000000000000000000000), (104376823363 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A1_3_12Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(941315424133664770623714468493 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(9520770923350851573363953693631 / 25000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨1, 0⟩
  | 0, 3, 5 => ⟨(1309302249206923385346751762939 / 4000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(1309302249206923385346751762939 / 4000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨1, 0⟩
  | 1, 2, 5 => ⟨(9520770923350851573363953693631 / 25000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(941315424133664770623714468493 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_3_12Den : Ball := ⟨(34539654154368764093674407556997 / 10000000000000000000000000000000), (29 / 10000000000000000000000000000000)⟩
def A1_3_12Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(272531803568913863847155720223 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(1102590185854146714999994489443 / 10000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(5790445935160092149101894313999 / 20000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(9476804858520244376796272095129 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(9476804858520244376796272095129 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(5790445935160092149101894313999 / 20000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(1102590185854146714999994489443 / 10000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(272531803568913863847155720223 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_3_12Law (u : Shape) : Ball := if u ∈ below (shape 1 3 12) then A1_3_12Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB2_3_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A1_2_13Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(13198064446345864393700754481767 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨1, 0⟩
  | 0, 2, 6 => ⟨(102993943547189172179056608068133 / 100000000000000000000000000000000), (1 / 781250000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(102993943547189172179056608068133 / 100000000000000000000000000000000), (1 / 781250000000000000000000000000)⟩
  | 1, 1, 6 => ⟨1, 0⟩
  | 1, 2, 5 => ⟨(13198064446345864393700754481767 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_2_13Den : Ball := ⟨(2161920079935350365727573625499 / 500000000000000000000000000000), (163 / 50000000000000000000000000000000)⟩
def A1_2_13Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(1526197079257959517831418186343 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(11563794717493717482510909886597 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(595500410162416149982883596353 / 2500000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(595500410162416149982883596353 / 2500000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(11563794717493717482510909886597 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(1526197079257959517831418186343 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_2_13Law (u : Shape) : Ball := if u ∈ below (shape 1 2 13) then A1_2_13Table u else .exact 0
def B1_4_3Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => ⟨(604310145779763534924082105259 / 20000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨1, 0⟩
  | 0, 3, 1 => ⟨(313250271201287039100674208231 / 2000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(19874372820681005040666098619 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(19874372820681005040666098619 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(313250271201287039100674208231 / 2000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨1, 0⟩
  | 1, 3, 0 => ⟨(604310145779763534924082105259 / 20000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_4_3Den : Ball := ⟨(118763561780245893649816785332321 / 50000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
def B1_4_3Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => ⟨(636043303940678115759208606101 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(42100455097934397479443978531991 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(5275191590850223000844657229 / 80000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(33468805621467537981782719557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(33468805621467537981782719557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(5275191590850223000844657229 / 80000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(42100455097934397479443978531991 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(636043303940678115759208606101 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_4_3Law (u : Shape) : Ball := if u ∈ below (shape 1 4 3) then B1_4_3Table u else .exact 0
def B2_3_3Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => ⟨(458969575380885935284968818789 / 12500000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(25801251678676229010804343740993 / 50000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(3706063217950154173785426369011 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(511028552803376939474174188057 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 1, 2, 1 => ⟨1, 0⟩
  | 1, 3, 0 => ⟨(511028552803376939474174188057 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(3706063217950154173785426369011 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(25801251678676229010804343740993 / 50000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(458969575380885935284968818789 / 12500000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_3_3Den : Ball := ⟨(79745675865576538308574019294683 / 25000000000000000000000000000000), (61 / 50000000000000000000000000000000)⟩
def B2_3_3Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => ⟨(575541645862465244045460683071 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(16177210487354926739367120056171 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(580919149804010567943683801739 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(80102862515202903466679710933 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(31349662196281715829721231552343 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(31349662196281715829721231552343 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(80102862515202903466679710933 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(580919149804010567943683801739 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(16177210487354926739367120056171 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(575541645862465244045460683071 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_3_3Law (u : Shape) : Ball := if u ∈ below (shape 2 3 3) then B2_3_3Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_3_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A1_5_10Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(4877234139087099097455979049 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(1040730640497417669371234343317 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(24806928903736187010464986272311 / 50000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨1, 0⟩
  | 0, 4, 4 => ⟨(1373466604963415429908322697947 / 5000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(180907807836891972602388433389 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(180907807836891972602388433389 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(1373466604963415429908322697947 / 5000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(24806928903736187010464986272311 / 50000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(1040730640497417669371234343317 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(4877234139087099097455979049 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_5_10Den : Ball := ⟨(180078944695198152019045749315239 / 50000000000000000000000000000000), (73 / 25000000000000000000000000000000)⟩
def A1_5_10Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(1354193336523132042830125793 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(288965109790864128701089625269 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(13775585449883897327311949605707 / 100000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(13882800147632490517692935191451 / 50000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(7627024954461759705584239713517 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(251150694134587410230100795749 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(251150694134587410230100795749 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(7627024954461759705584239713517 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(13882800147632490517692935191451 / 50000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(13775585449883897327311949605707 / 100000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(288965109790864128701089625269 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(1354193336523132042830125793 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_5_10Law (u : Shape) : Ball := if u ∈ below (shape 1 5 10) then A1_5_10Table u else .exact 0
def A1_6_9Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(465206198044103796714339601 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(3519230583945255359012162411 / 1562500000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(2758900617971649586297424581857 / 20000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨1, 0⟩
  | 0, 4, 4 => ⟨(69823469044785918019090333627239 / 100000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(159746720192498137638592631477 / 3125000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(62591248309512292903546658869 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(62591248309512292903546658869 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(159746720192498137638592631477 / 3125000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(69823469044785918019090333627239 / 100000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(2758900617971649586297424581857 / 20000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(3519230583945255359012162411 / 1562500000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(465206198044103796714339601 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_6_9Den : Ball := ⟨(94509077196342079547344730068281 / 25000000000000000000000000000000), (13 / 5000000000000000000000000000000)⟩
def A1_6_9Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(15382325296305947711052937 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(5957913357480485806366775989 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(36489889381736965002937990111 / 1000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(6613121390462484295530342757863 / 25000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(18470043067854755212619808940411 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(1352223299022380417157697666993 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(8278470461027691080983583329 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(8278470461027691080983583329 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(1352223299022380417157697666993 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(18470043067854755212619808940411 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(6613121390462484295530342757863 / 25000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(36489889381736965002937990111 / 1000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(5957913357480485806366775989 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(15382325296305947711052937 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_6_9Law (u : Shape) : Ball := if u ∈ below (shape 1 6 9) then A1_6_9Table u else .exact 0
def B1_3_4Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(21517752334378745292384301617 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(6992394129695647447331751196051 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨1, 0⟩
  | 0, 3, 1 => ⟨(766343960730141034186800786921 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(766343960730141034186800786921 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 1, 2, 1 => ⟨(6992394129695647447331751196051 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(21517752334378745292384301617 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_3_4Den : Ball := ⟨(5854659980349030826099773707151 / 2500000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
def B1_3_4Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(18376602916823826473515371739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(1492912089080617619303408645301 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(21350514021234075570262898364063 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(1308946998292554555787053318931 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(1308946998292554555787053318931 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(21350514021234075570262898364063 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(1492912089080617619303408645301 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(18376602916823826473515371739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_3_4Law (u : Shape) : Ball := if u ∈ below (shape 1 3 4) then B1_3_4Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_3_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_1_6Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 1, 2 => (63 / 1000000)
  | _, _, _ => 0
def B1_1_6LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_1_6Binary u else if i = 3 then B1_1_6Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_1_6Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_1_6LittleRat u w i)
  else .exact (littleLaw (shape 1 1 6) u w i)

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B1_2_5Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(14279668505343149815259750483 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨1, 0⟩
  | 0, 2, 2 => ⟨(11468822577910492362546082899621 / 20000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(11468822577910492362546082899621 / 20000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 1, 2, 1 => ⟨(14279668505343149815259750483 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_2_5Den : Ball := ⟨(157572587585637952209774570505833 / 50000000000000000000000000000000), (19 / 12500000000000000000000000000000)⟩
def B1_2_5Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(396642594740867223667445521291 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(9098047091850119065057057298309 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(9098047091850119065057057298309 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(396642594740867223667445521291 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_2_5Law (u : Shape) : Ball := if u ∈ below (shape 1 2 5) then B1_2_5Table u else .exact 0

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_2_5Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (19531 / 200000)
  | 1, 2, 1 => (10533 / 250000)
  | _, _, _ => 0
def B1_2_5LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_2_5Binary u else if i = 3 then B1_2_5Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_2_5Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_2_5LittleRat u w i)
  else .exact (littleLaw (shape 1 2 5) u w i)

def B1_3_4Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (46483 / 500000)
  | 1, 1, 2 => (301 / 250000)
  | 1, 2, 1 => (10537 / 250000)
  | _, _, _ => 0
def B1_3_4LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_3_4Binary u else if i = 3 then B1_3_4Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_3_4Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_3_4LittleRat u w i)
  else .exact (littleLaw (shape 1 3 4) u w i)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_4_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_4_3Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (23901 / 250000)
  | 1, 1, 2 => (41743 / 1000000)
  | 1, 2, 1 => (3057 / 1000000)
  | _, _, _ => 0
def B1_4_3LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_4_3Binary u else if i = 3 then B1_4_3Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_4_3Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_4_3LittleRat u w i)
  else .exact (littleLaw (shape 1 4 3) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_5_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_5_2Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (109933 / 1000000)
  | 1, 1, 2 => (10523 / 250000)
  | 1, 2, 1 => (3747 / 1000000)
  | _, _, _ => 0
def B1_5_2LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_5_2Binary u else if i = 3 then B1_5_2Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_5_2Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_5_2LittleRat u w i)
  else .exact (littleLaw (shape 1 5 2) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB2_3_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B2_3_3Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (55041 / 500000)
  | 1, 1, 2 => (573 / 125000)
  | 1, 2, 1 => (1687 / 40000)
  | 2, 0, 2 => (104091 / 1000000)
  | 2, 1, 1 => (19419 / 500000)
  | 2, 2, 0 => (102383 / 1000000)
  | _, _, _ => 0
def B2_3_3LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B2_3_3Binary u else if i = 3 then B2_3_3Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B2_3_3Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B2_3_3LittleRat u w i)
  else .exact (littleLaw (shape 2 3 3) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB2_5_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B2_5_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 2, 1 => (3587 / 1000000)
  | 2, 1, 1 => (21083 / 500000)
  | 2, 2, 0 => (55043 / 500000)
  | _, _, _ => 0
def B2_5_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B2_5_1Binary u else if i = 3 then B2_5_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B2_5_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B2_5_1LittleRat u w i)
  else .exact (littleLaw (shape 2 5 1) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_1_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_1_7H2H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four1_0_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z1_0_7H2H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_4_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A1_4_11Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(188090920380700586676163797639 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(7347227310806514247293732489647 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨1, 0⟩
  | 0, 3, 5 => ⟨(1185052529893235166451447015261 / 1562500000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(9124564624877481324080557406303 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(9124564624877481324080557406303 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(1185052529893235166451447015261 / 1562500000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(7347227310806514247293732489647 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(188090920380700586676163797639 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_4_11Den : Ball := ⟨(9992523604001913052911839757997 / 2500000000000000000000000000000), (163 / 50000000000000000000000000000000)⟩
def A1_4_11Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(47057912454010095367492939241 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(4595452811755191797013350101 / 125000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(5003740994914984598991554798533 / 20000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(3795005391970877478082437264067 / 20000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(2282847903712526081651866666959 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(2282847903712526081651866666959 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(3795005391970877478082437264067 / 20000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(5003740994914984598991554798533 / 20000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(4595452811755191797013350101 / 125000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(47057912454010095367492939241 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_4_11Law (u : Shape) : Ball := if u ∈ below (shape 1 4 11) then A1_4_11Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_7_8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A1_7_8Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(64668921862685299795581911 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(8061327816168650758772421803 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(53906227585276956042284318339 / 2500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(10604472274941479671393272450057 / 25000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨1, 0⟩
  | 0, 5, 3 => ⟨(5174982216910474785081875841 / 32000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(230783094467553527628691159093 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 7, 1 => ⟨(1820161921466848777911127321 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(1820161921466848777911127321 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(230783094467553527628691159093 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(5174982216910474785081875841 / 32000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(10604472274941479671393272450057 / 25000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(53906227585276956042284318339 / 2500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(8061327816168650758772421803 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 7, 0 => ⟨(64668921862685299795581911 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_7_8Den : Ball := ⟨(161225531306433004521497958407937 / 50000000000000000000000000000000), (51 / 25000000000000000000000000000000)⟩
def A1_7_8Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(20055422158842954722213457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(500003178829468586018862723 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(167176461285217244558128668051 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(13154829993750939206545618238241 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(49619932619696659353487069911 / 160000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(626909836209048342179201955027 / 12500000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(71571509982781843275618258667 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 7, 1 => ⟨(35279809335985405792837309 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(35279809335985405792837309 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(71571509982781843275618258667 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(626909836209048342179201955027 / 12500000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(49619932619696659353487069911 / 160000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(13154829993750939206545618238241 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(167176461285217244558128668051 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(500003178829468586018862723 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 7, 0 => ⟨(20055422158842954722213457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_7_8Law (u : Shape) : Ball := if u ∈ below (shape 1 7 8) then A1_7_8Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_2_12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A2_2_12Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(1869311508851834494291415094233 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(7549884563595081968144199084631 / 20000000000000000000000000000000), (49 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(30069849903795798682001150038067 / 50000000000000000000000000000000), (19 / 12500000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(3769284113062302699382690041033 / 10000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨1, 0⟩
  | 1, 2, 5 => ⟨(3769284113062302699382690041033 / 10000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(30069849903795798682001150038067 / 50000000000000000000000000000000), (19 / 12500000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(7549884563595081968144199084631 / 20000000000000000000000000000000), (49 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(1869311508851834494291415094233 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_2_12Den : Ball := ⟨(46862818816260467173210402750963 / 12500000000000000000000000000000), (353 / 50000000000000000000000000000000)⟩
def A2_2_12Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(498612641127346285354984562323 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(629320585519500210170837921791 / 6250000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(16041421890184163505612052300387 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(5027018498184156379482942970689 / 50000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(13336799104008174087333670447257 / 50000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(5027018498184156379482942970689 / 50000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(16041421890184163505612052300387 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(629320585519500210170837921791 / 6250000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(498612641127346285354984562323 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_2_12Law (u : Shape) : Ball := if u ∈ below (shape 2 2 12) then A2_2_12Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_3_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A2_3_11Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(186089076496629284671636655033 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(3883263175820951434259740591633 / 25000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(72108374302660701632463080306707 / 100000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(7622712470039063487610425167721 / 20000000000000000000000000000000), (97 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(1423229584278735571932633776199 / 12500000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨1, 0⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(1423229584278735571932633776199 / 12500000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(7622712470039063487610425167721 / 20000000000000000000000000000000), (97 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(72108374302660701632463080306707 / 100000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(3883263175820951434259740591633 / 25000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(186089076496629284671636655033 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_3_11Den : Ball := ⟨(237326915106866338667686875376469 / 50000000000000000000000000000000), (263 / 50000000000000000000000000000000)⟩
def A2_3_11Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(3920521960453472358068863817 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(1636250643578437060137490917283 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(3038356364687540796048396518993 / 20000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(2007439944866403842027423610433 / 25000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(1199383208295499995255418131323 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(21067985473744271817281816227921 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(21067985473744271817281816227921 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(1199383208295499995255418131323 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2007439944866403842027423610433 / 25000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(3038356364687540796048396518993 / 20000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(1636250643578437060137490917283 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(3920521960453472358068863817 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_3_11Law (u : Shape) : Ball := if u ∈ below (shape 2 3 11) then A2_3_11Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_4_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A2_4_10Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(446772032626590449174459001 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(906397801707561174643203706603 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(6854684406764661394145666352671 / 20000000000000000000000000000000), (89 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(46468291928546345537530836954281 / 100000000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(3890053868306385356771126651001 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(221391162680060686462957026073 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(7981096634328140896953939436857 / 25000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(7981096634328140896953939436857 / 25000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(221391162680060686462957026073 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(3890053868306385356771126651001 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(46468291928546345537530836954281 / 100000000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(6854684406764661394145666352671 / 20000000000000000000000000000000), (89 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(906397801707561174643203706603 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(446772032626590449174459001 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_4_10Den : Ball := ⟨(21644187991385360464217363058073 / 6250000000000000000000000000000), (331 / 50000000000000000000000000000000)⟩
def A2_4_10Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(1290103932301626811496829007 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(52346489163067591327869821847 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(1237103973342943767145037824953 / 12500000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(3354559023755106067899108779113 / 25000000000000000000000000000000), (3 / 5000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(2246592636008493490381620329021 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(63929160442568044753234425373 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(288078801942145166747625960087 / 3125000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(14438056078813335419022981654143 / 50000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(288078801942145166747625960087 / 3125000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(63929160442568044753234425373 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2246592636008493490381620329021 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(3354559023755106067899108779113 / 25000000000000000000000000000000), (3 / 5000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(1237103973342943767145037824953 / 12500000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(52346489163067591327869821847 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(1290103932301626811496829007 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_4_10Law (u : Shape) : Ball := if u ∈ below (shape 2 4 10) then A2_4_10Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_5_9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A2_5_9Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(273399354531404847951902717 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(68946518086100053614010604923 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(5026696090772982390642513919 / 39062500000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(34960645180196030788867851759237 / 50000000000000000000000000000000), (21 / 25000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(14646816460940129823291825517243 / 50000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(549758056631767773116973570093 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(20110279532265531872236546511 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(481900057386660180442774113293 / 6250000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(481900057386660180442774113293 / 6250000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(20110279532265531872236546511 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(549758056631767773116973570093 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(14646816460940129823291825517243 / 50000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(34960645180196030788867851759237 / 50000000000000000000000000000000), (21 / 25000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(5026696090772982390642513919 / 39062500000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(68946518086100053614010604923 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(273399354531404847951902717 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_5_9Den : Ball := ⟨(55312489073820944932330853887411 / 12500000000000000000000000000000), (11 / 2500000000000000000000000000000)⟩
def A2_5_9Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(4942814165649309970823409 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(62324548434335428709365572507 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(116324018389450319333620372957 / 4000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(1580142467171247110537433641061 / 10000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(3310015673266902490136717119167 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(248478266769938591622945895033 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(9089393674467454662811780111 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(54451994641697075498935578049 / 3125000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(706214828767994042269955497393 / 3125000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(706214828767994042269955497393 / 3125000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(54451994641697075498935578049 / 3125000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(9089393674467454662811780111 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(248478266769938591622945895033 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(3310015673266902490136717119167 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(1580142467171247110537433641061 / 10000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(116324018389450319333620372957 / 4000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(62324548434335428709365572507 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(4942814165649309970823409 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_5_9Law (u : Shape) : Ball := if u ∈ below (shape 2 5 9) then A2_5_9Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_6_8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A2_6_8Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(21466224447373239265811841 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(4164228830985898487035268579 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(236816107750252950992530912187 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(26588271193898263795134550700049 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(42109365988791183706790041939433 / 100000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(3497925876037468983918864089217 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(43048417256949502222394857087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(152992977510149012892744533 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(591892757125928317262835160377 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(11311535044206459420578689801861 / 50000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(11311535044206459420578689801861 / 50000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(591892757125928317262835160377 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(152992977510149012892744533 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(43048417256949502222394857087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(3497925876037468983918864089217 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(42109365988791183706790041939433 / 100000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(26588271193898263795134550700049 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(236816107750252950992530912187 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(4164228830985898487035268579 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(21466224447373239265811841 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_6_8Den : Ball := ⟨(73683614726356645052910002223033 / 25000000000000000000000000000000), (263 / 50000000000000000000000000000000)⟩
def A2_6_8Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(7283242185896305552952829 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(5651499110692180694905247591 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(642791775701372526766325518709 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(9021093526912582843203331566559 / 100000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(14287221842052441515014217084377 / 100000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(29670146892799120299239106787 / 2500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(182572888731864977572933803 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(830540022111175778026502387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(200822380702981496437118097259 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(1918936639817210417915987511527 / 25000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(33928845772352553367922348016919 / 100000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(1918936639817210417915987511527 / 25000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(200822380702981496437118097259 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(830540022111175778026502387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(182572888731864977572933803 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(29670146892799120299239106787 / 2500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(14287221842052441515014217084377 / 100000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(9021093526912582843203331566559 / 100000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(642791775701372526766325518709 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(5651499110692180694905247591 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(7283242185896305552952829 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_6_8Law (u : Shape) : Ball := if u ∈ below (shape 2 6 8) then A2_6_8Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_7_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A2_7_7Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(997980326700703990907442669 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(110767244555364068131295527073 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(17036705883006141337553720298693 / 100000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(69038904979943881194700567488221 / 100000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(17481972130738693443717668197977 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(60056388144364868734784399473 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 7, 1 => ⟨(2064990167644092904399448839 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(756166967065100758247607 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(71473408038032577228923343497 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(3124339826741735799459034189257 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨1, 0⟩
  | 1, 5, 2 => ⟨(3124339826741735799459034189257 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(71473408038032577228923343497 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 7, 0 => ⟨(756166967065100758247607 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2064990167644092904399448839 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(60056388144364868734784399473 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(17481972130738693443717668197977 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(69038904979943881194700567488221 / 100000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(17036705883006141337553720298693 / 100000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(110767244555364068131295527073 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(997980326700703990907442669 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_7_7Den : Ball := ⟨(8432217523044894851661197558491 / 2000000000000000000000000000000), (199 / 50000000000000000000000000000000)⟩
def A2_7_7Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(236706494815454143359971229 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(6568096959823549410460354727 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(4040860150119596109248067465019 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(4093757353345277543101032118639 / 25000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(2073235431007466414784974589209 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(113956051024980402388261306291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 7, 1 => ⟨(61223223962159475536795967 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(28696298310560545365494143 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(8476229158308448226948659597 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(1482096408544038066251740184659 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(23718553210161909988480210591893 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(23718553210161909988480210591893 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(1482096408544038066251740184659 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(8476229158308448226948659597 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 7, 0 => ⟨(28696298310560545365494143 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(61223223962159475536795967 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(113956051024980402388261306291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(2073235431007466414784974589209 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(4093757353345277543101032118639 / 25000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(4040860150119596109248067465019 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(6568096959823549410460354727 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(236706494815454143359971229 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_7_7Law (u : Shape) : Ball := if u ∈ below (shape 2 7 7) then A2_7_7Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA3_3_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A3_3_10Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(10114049177547547375147291033 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(1631941133917831872522312559669 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(22342041798333750043260090322813 / 100000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(21775166867897778509284039754867 / 100000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(328746702339804911134262473157 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(48051347848878380719513662951177 / 100000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(22503484997364245598597737532479 / 100000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(22503484997364245598597737532479 / 100000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨1, 0⟩
  | 2, 2, 4 => ⟨(48051347848878380719513662951177 / 100000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(328746702339804911134262473157 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(21775166867897778509284039754867 / 100000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(22342041798333750043260090322813 / 100000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(1631941133917831872522312559669 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(10114049177547547375147291033 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_3_10Den : Ball := ⟨(217957830207268558846224302777823 / 50000000000000000000000000000000), (119 / 25000000000000000000000000000000)⟩
def A3_3_10Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(92807394604080247176410297 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(374370843287879533686819841787 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(5125312950924365842644983492711 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(2497635304864997016024994299279 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(377076040382652095214990170031 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(11023083640349972174887924565559 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(22940217358767125771206291343619 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(516234837169290854412959173031 / 10000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(516234837169290854412959173031 / 10000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(22940217358767125771206291343619 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(11023083640349972174887924565559 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(377076040382652095214990170031 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(2497635304864997016024994299279 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(5125312950924365842644983492711 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(374370843287879533686819841787 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(92807394604080247176410297 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_3_10Law (u : Shape) : Ball := if u ∈ below (shape 3 3 10) then A3_3_10Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA3_4_9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A3_4_9Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(52604183508248426299746893 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(107048101953376826039075703437 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(7949191186854819609435816255409 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(29617641665026676343636152910233 / 100000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(2097142753831614220150564409891 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(25538511110736612768307319049 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(1305033413039090422171216880161 / 12500000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(31184557034256196846304679690331 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(1478492526375484315026102985421 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(1478492526375484315026102985421 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(31184557034256196846304679690331 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨1, 0⟩
  | 2, 3, 3 => ⟨(1305033413039090422171216880161 / 12500000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(25538511110736612768307319049 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(2097142753831614220150564409891 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(29617641665026676343636152910233 / 100000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(7949191186854819609435816255409 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(107048101953376826039075703437 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(52604183508248426299746893 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_4_9Den : Ball := ⟨(222064085094079557733888212669047 / 50000000000000000000000000000000), (241 / 50000000000000000000000000000000)⟩
def A3_4_9Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(2961092486317753981806299 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(12051487514068842044483780559 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(1789841698959800118150495751873 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(6668714946065880326404692767049 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(944386280628468031665627187853 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(28751284904892409882235281843 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(1175366482595508974701704124553 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(22516022786312800353724657277333 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(14043043935287673024483191909343 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(665795428265271676282857013551 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(665795428265271676282857013551 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(14043043935287673024483191909343 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(22516022786312800353724657277333 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(1175366482595508974701704124553 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(28751284904892409882235281843 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(944386280628468031665627187853 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(6668714946065880326404692767049 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(1789841698959800118150495751873 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(12051487514068842044483780559 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(2961092486317753981806299 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_4_9Law (u : Shape) : Ball := if u ∈ below (shape 3 4 9) then A3_4_9Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA3_5_8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A3_5_8Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(328669583149386781185709 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(19209894118417149770024794673 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(1723177871786636609721592861297 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(17261354968926351667760393882717 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(445432629432246067049549352859 / 2500000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(855619240745488096141205264161 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(66803408806529843382445509 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(640582734291565687942242590477 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(35260740785769191116135010727999 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(6416822165959928926276575414637 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(174482677080586900029834379827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(174482677080586900029834379827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(6416822165959928926276575414637 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨1, 0⟩
  | 2, 3, 3 => ⟨(35260740785769191116135010727999 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(640582734291565687942242590477 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(66803408806529843382445509 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(855619240745488096141205264161 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(445432629432246067049549352859 / 2500000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(17261354968926351667760393882717 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(1723177871786636609721592861297 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(19209894118417149770024794673 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(328669583149386781185709 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_5_8Den : Ball := ⟨(93616032861888673699101131780679 / 25000000000000000000000000000000), (89 / 25000000000000000000000000000000)⟩
def A3_5_8Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(5617321274602978972531421 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(2564984534587871162395170351 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(14380364892404713617013575761 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(2304807526184103743816886449421 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(951616119194862462941861582207 / 20000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(228491641492590121381678806719 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(1427178801842300281575260073 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(342133027168868932426842786183 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(9416319968874671475112547173063 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(26704827405880776123709349345923 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(1713601284361899518761493331217 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(46595297767531026173741859253 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(46595297767531026173741859253 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(1713601284361899518761493331217 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(26704827405880776123709349345923 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(9416319968874671475112547173063 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(342133027168868932426842786183 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(1427178801842300281575260073 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(228491641492590121381678806719 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(951616119194862462941861582207 / 20000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(2304807526184103743816886449421 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(14380364892404713617013575761 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(2564984534587871162395170351 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(5617321274602978972531421 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_5_8Law (u : Shape) : Ball := if u ∈ below (shape 3 5 8) then A3_5_8Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA3_6_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A3_6_7Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(947695798775862187054385307 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(102230605927328755004795179633 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(2485504917108313710539576690779 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(425575504693914482232192681717 / 1562500000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(500087920163149423759661626633 / 12500000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(14645470457248380324013395549 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(279158785601762653275431827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(63426279861227231827349959449 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(3019453409783584311945978178983 / 25000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(11504431092583276771638604143613 / 20000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(221757384863796084201755173273 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(2211632883128668798193442523 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2211632883128668798193442523 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(221757384863796084201755173273 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(11504431092583276771638604143613 / 20000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨1, 0⟩
  | 2, 4, 2 => ⟨(3019453409783584311945978178983 / 25000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(63426279861227231827349959449 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(279158785601762653275431827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(14645470457248380324013395549 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(500087920163149423759661626633 / 12500000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(425575504693914482232192681717 / 1562500000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(2485504917108313710539576690779 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(102230605927328755004795179633 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(947695798775862187054385307 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_6_7Den : Ball := ⟨(26644870182285812255234624802301 / 6250000000000000000000000000000), (57 / 12500000000000000000000000000000)⟩
def A3_6_7Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(444595804132456643872751423 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(95919594679892889239193974057 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(466413403425162984942828299979 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(159721365419467461928662332981 / 2500000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(938431894660947905675404500739 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(6870680152058435330563692671 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(32740681378342119614199523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(29755389793283097286725257379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(177065826198824108960514164357 / 6250000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(23456672737535644093331931145797 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(52706186556690537444005286707 / 390625000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(416135232310544407998215611629 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(2075101950204864030086128749 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2075101950204864030086128749 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(416135232310544407998215611629 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(52706186556690537444005286707 / 390625000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(23456672737535644093331931145797 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(177065826198824108960514164357 / 6250000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(29755389793283097286725257379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(32740681378342119614199523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(6870680152058435330563692671 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(938431894660947905675404500739 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(159721365419467461928662332981 / 2500000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(466413403425162984942828299979 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(95919594679892889239193974057 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(444595804132456643872751423 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_6_7Law (u : Shape) : Ball := if u ∈ below (shape 3 6 7) then A3_6_7Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA4_5_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A4_5_7Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(320070995306194163489326983 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(111908131966907707297208391469 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(924572162836136938580133522067 / 25000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(1712194403755276647553732402859 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(86252921110897044875603592223 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(563000628202886554057056869 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(17983177592845578600362644283 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(258269201999648166411752129327 / 2000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(32476703126909447167938135835733 / 50000000000000000000000000000000), (1 / 1250000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(1494634153844948446443758553957 / 6250000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(47901191170901796701943780139 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2789428518380002493238768961 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(7319706166566425133179750241413 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨1, 0⟩
  | 2, 3, 3 => ⟨1, 0⟩
  | 2, 4, 2 => ⟨(7319706166566425133179750241413 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(2789428518380002493238768961 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(47901191170901796701943780139 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(1494634153844948446443758553957 / 6250000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(32476703126909447167938135835733 / 50000000000000000000000000000000), (1 / 1250000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(258269201999648166411752129327 / 2000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(17983177592845578600362644283 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(563000628202886554057056869 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(86252921110897044875603592223 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(1712194403755276647553732402859 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(924572162836136938580133522067 / 25000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(111908131966907707297208391469 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(320070995306194163489326983 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A4_5_7Den : Ball := ⟨(44275032369233382034553407713609 / 10000000000000000000000000000000), (247 / 50000000000000000000000000000000)⟩
def A4_5_7Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(72291532762065411961625181 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(50551349588474794800387489967 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(835298915312477561452360781693 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(1546871283549937362097791005049 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(155849320025945821317144591277 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(127159845645672388759135689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(16246788883517155613847561503 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(2916646111580472154804741948879 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(14670436762674140168945445265753 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(5401271367141237916102377734777 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(108190076003621906016955145267 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(1008036672268904292945876487 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(413308911076758019532532898899 / 25000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(11293046515025223285749624084633 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(11293046515025223285749624084633 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(413308911076758019532532898899 / 25000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(1008036672268904292945876487 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(108190076003621906016955145267 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(5401271367141237916102377734777 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(14670436762674140168945445265753 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(2916646111580472154804741948879 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(16246788883517155613847561503 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(127159845645672388759135689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(155849320025945821317144591277 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(1546871283549937362097791005049 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(835298915312477561452360781693 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(50551349588474794800387489967 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(72291532762065411961625181 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A4_5_7Law (u : Shape) : Ball := if u ∈ below (shape 4 5 7) then A4_5_7Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA4_6_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A4_6_6Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 6 => ⟨(37007680233059694261632513727 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(271425459907852890084474170757 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(2973450328881290536063908848299 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(1344967952978413384079961640011 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(7218791470495623248351293593 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(17136753165425385847386480203 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(2777830385098454704554116818579 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(37038954605575141351236241889301 / 100000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(2314240286611235203992770108591 / 6250000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(172110505220792807003863412141 / 6250000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(16859688301886595155585889253 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(9933044295486291664832751 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(557758160866722243028058363771 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(8218402317164102891027245622431 / 25000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨1, 0⟩
  | 2, 4, 2 => ⟨(8218402317164102891027245622431 / 25000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(557758160866722243028058363771 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(9933044295486291664832751 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(16859688301886595155585889253 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(172110505220792807003863412141 / 6250000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(2314240286611235203992770108591 / 6250000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(37038954605575141351236241889301 / 100000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(2777830385098454704554116818579 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(17136753165425385847386480203 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(7218791470495623248351293593 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(1344967952978413384079961640011 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(2973450328881290536063908848299 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(271425459907852890084474170757 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(37007680233059694261632513727 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A4_6_6Den : Ball := ⟨(21473387588672402815433518941063 / 6250000000000000000000000000000), (339 / 50000000000000000000000000000000)⟩
def A4_6_6Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 6 => ⟨(10771379247987724786312094607 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(395002678878428760271589624507 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(346178533382622745572856101671 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(97865901122995442910500291001 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(420217317871148638292284089 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(4987788109427518371238771367 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(202127398799710262270548863881 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(5390240951245195934807849697209 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(5388624121496410916877795150321 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(40075303561228547414201969063 / 5000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(4907146180436727877076230291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(361386428843779882083529413 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(81169971226522625940938278493 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(9568125060877047586886196521351 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(14552897101566282733842513365051 / 50000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(9568125060877047586886196521351 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(81169971226522625940938278493 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(361386428843779882083529413 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(4907146180436727877076230291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(40075303561228547414201969063 / 5000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(5388624121496410916877795150321 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(5390240951245195934807849697209 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(202127398799710262270548863881 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(4987788109427518371238771367 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(420217317871148638292284089 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(97865901122995442910500291001 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(346178533382622745572856101671 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(395002678878428760271589624507 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(10771379247987724786312094607 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A4_6_6Law (u : Shape) : Ball := if u ∈ below (shape 4 6 6) then A4_6_6Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_1_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A4_4_8Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(18292309835383748212700097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(9679647302864801584009674223 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(115294249586007915494116430803 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(49998791258020844658220845781 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(25723673806193141051082939537 / 800000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(9822006849405278656185245843 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(678835129521870795795191707909 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(22454031748889508411675041798339 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(41895154924763898251935527356047 / 100000000000000000000000000000000), (19 / 20000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(253670642551677628600159805953 / 6250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(146442242833390519127469727577 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(1124274470428081998513583312611 / 5000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨1, 0⟩
  | 2, 3, 3 => ⟨(1124274470428081998513583312611 / 5000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(146442242833390519127469727577 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(253670642551677628600159805953 / 6250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(41895154924763898251935527356047 / 100000000000000000000000000000000), (19 / 20000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(22454031748889508411675041798339 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(678835129521870795795191707909 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(9822006849405278656185245843 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(25723673806193141051082939537 / 800000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(49998791258020844658220845781 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(115294249586007915494116430803 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(9679647302864801584009674223 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(18292309835383748212700097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A4_4_8Den : Ball := ⟨(150648199314227147605087079506763 / 50000000000000000000000000000000), (129 / 25000000000000000000000000000000)⟩
def A4_4_8Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(3035600478242196747209827 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(100395816077291183265741961 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(95665140797271696018077340381 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(1327564258600440675632668642677 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(266801996340761781073908742717 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(407489389771853581693404047 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(225304760565353108107595575157 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(1863118166289372952288716397111 / 25000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(869060232620536432990705106057 / 6250000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(53883555187553276131757505307 / 4000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(194416187515041316719536553259 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(7462913433721381544107457287859 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(16594954412866328459781726401447 / 50000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(7462913433721381544107457287859 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(194416187515041316719536553259 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(53883555187553276131757505307 / 4000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(869060232620536432990705106057 / 6250000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(1863118166289372952288716397111 / 25000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(225304760565353108107595575157 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(407489389771853581693404047 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(266801996340761781073908742717 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(1327564258600440675632668642677 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(95665140797271696018077340381 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(100395816077291183265741961 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(3035600478242196747209827 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A4_4_8Law (u : Shape) : Ball := if u ∈ below (shape 4 4 8) then A4_4_8Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def A5_5_6Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 6 => ⟨(598393443808798963104497811 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(269057595129013954010741499 / 100000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(195357478600075867932284843153 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(67997999417353477070680589579 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(11231598536934101059647265467 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(339979024578301882451997256747 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(425430866772270433481086062941 / 2000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(13773826846282937567353855599691 / 100000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(394207840594426910088570909701 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(6044678416630759639672068403 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(1361548977162547525623139130929 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(5734984758757153909776083780903 / 10000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨1, 0⟩
  | 2, 4, 2 => ⟨(4259416902451820897167775843919 / 20000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(6794721161026753944048082769 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(6794721161026753944048082769 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(4259416902451820897167775843919 / 20000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨1, 0⟩
  | 3, 3, 2 => ⟨(5734984758757153909776083780903 / 10000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(1361548977162547525623139130929 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(6044678416630759639672068403 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(394207840594426910088570909701 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(13773826846282937567353855599691 / 100000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(425430866772270433481086062941 / 2000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(339979024578301882451997256747 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(11231598536934101059647265467 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 0, 3 => ⟨(67997999417353477070680589579 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 1, 2 => ⟨(195357478600075867932284843153 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 5, 2, 1 => ⟨(269057595129013954010741499 / 100000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 3, 0 => ⟨(598393443808798963104497811 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A5_5_6Den : Ball := ⟨(110725452045764867598235231213513 / 25000000000000000000000000000000), (1 / 195312500000000000000000000000)⟩
def A5_5_6Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 6 => ⟨(675537368275398796035425779 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(12149762776213706359494656353 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(176434121505623680657566151503 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(30705677042189293652050887643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(10143646586596796759663111597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(614093721537090303603790920153 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(4802767328017229778204193388411 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(621981061797334608261562972731 / 20000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(89005696818355176566211545587 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(272957947109232969209465951 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(614831076327326380909751491957 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(6474329809449298000655312889227 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(22578367970597256891228418236613 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(2404267054093469337759843178867 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(30682742926253173520153038357 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(30682742926253173520153038357 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(2404267054093469337759843178867 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(22578367970597256891228418236613 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(6474329809449298000655312889227 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(614831076327326380909751491957 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(272957947109232969209465951 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(89005696818355176566211545587 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(621981061797334608261562972731 / 20000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(4802767328017229778204193388411 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(614093721537090303603790920153 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(10143646586596796759663111597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 0, 3 => ⟨(30705677042189293652050887643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 1, 2 => ⟨(176434121505623680657566151503 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 5, 2, 1 => ⟨(12149762776213706359494656353 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 3, 0 => ⟨(675537368275398796035425779 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A5_5_6Law (u : Shape) : Ball := if u ∈ below (shape 5 5 6) then A5_5_6Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def AProbsTable (s u : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 14 => A1_1_14Law u
  | 1, 2, 13 => A1_2_13Law u
  | 1, 3, 12 => A1_3_12Law u
  | 1, 4, 11 => A1_4_11Law u
  | 1, 5, 10 => A1_5_10Law u
  | 1, 6, 9 => A1_6_9Law u
  | 1, 7, 8 => A1_7_8Law u
  | 2, 2, 12 => A2_2_12Law u
  | 2, 3, 11 => A2_3_11Law u
  | 2, 4, 10 => A2_4_10Law u
  | 2, 5, 9 => A2_5_9Law u
  | 2, 6, 8 => A2_6_8Law u
  | 2, 7, 7 => A2_7_7Law u
  | 3, 3, 10 => A3_3_10Law u
  | 3, 4, 9 => A3_4_9Law u
  | 3, 5, 8 => A3_5_8Law u
  | 3, 6, 7 => A3_6_7Law u
  | 4, 4, 8 => A4_4_8Law u
  | 4, 5, 7 => A4_5_7Law u
  | 4, 6, 6 => A4_6_6Law u
  | 5, 5, 6 => A5_5_6Law u
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_1_6U0_0_4Mass : Ball := ⟨(3710278844513467307488141523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_1_6U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_1_6U0_1_3Mass : Ball := ⟨(389029125902587733647766048067 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def B1_1_6U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_1_6U1_0_3Mass : Ball := ⟨(389029125902587733647766048067 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def B1_1_6U1_1_2D : Ball := .exact (63 / 1000000)
def B1_1_6U1_1_2OneD : Ball := .exact (999937 / 1000000)
def B1_1_6U1_1_2EDLogWitness : LogWitness := ⟨-14, 16128, 15625⟩
def B1_1_6U1_1_2EDLog : Ball := ⟨(-120904697894659267702651285468121 / 12500000000000000000000000000000), (79409338811 / 25000000000000000000000000000000)⟩
def B1_1_6U1_1_2ED : Ball := ⟨(15233991934727067730534061969 / 25000000000000000000000000000000), (10005577 / 50000000000000000000000000000000)⟩
def B1_1_6U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 999937, 500000⟩
def B1_1_6U1_1_2EOneDLog : Ball := ⟨(-126003969166705876877493883 / 2000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_1_6U1_1_2EOneD : Ball := ⟨(1574950386458104680090632511 / 25000000000000000000000000000000), (42348979213 / 100000000000000000000000000000000)⟩
def B1_1_6U1_1_2BinaryEntropy : Ball := ⟨(35801298261134172545913669541 / 50000000000000000000000000000000), (42371658521 / 100000000000000000000000000000000)⟩
def B1_1_6U1_1_2Leaf : Ball := ⟨(64375488605594348017558361096379 / 20000000000000000000000000000000), (31762734967 / 25000000000000000000000000000000)⟩
def B1_1_6U1_1_2Mass : Ball := ⟨(3710278844513467307488141523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_1_6Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_1_6U0_0_4Leaf
  | 0, 1, 3 => B1_1_6U0_1_3Leaf
  | 1, 0, 3 => B1_1_6U1_0_3Leaf
  | 1, 1, 2 => B1_1_6U1_1_2Leaf
  | _, _, _ => (.exact 0)
def B1_1_6Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_1_6U0_0_4Mass
  | 0, 1, 3 => B1_1_6U0_1_3Mass
  | 1, 0, 3 => B1_1_6U1_0_3Mass
  | 1, 1, 2 => B1_1_6U1_1_2Mass
  | _, _, _ => (.exact 0)
def B1_1_6Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B1_1_6U1_1_2BinaryEntropy
  | _, _, _ => (.exact 0)
def B1_1_6S2 : Ball := ⟨(113464402089716250899384401133 / 6250000000000000000000000000000), (668468917 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_2_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_2_5U0_0_4Leaf : Ball := ⟨0, 0⟩
def B1_2_5U0_0_4Mass : Ball := ⟨(10839580338829366322698124931 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_2_5U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_2_5U0_1_3Mass : Ball := ⟨(1186081054548533539957298951707 / 25000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
def B1_2_5U0_2_2D : Ball := .exact (19531 / 200000)
def B1_2_5U0_2_2OneD : Ball := .exact (180469 / 200000)
def B1_2_5U0_2_2EDLogWitness : LogWitness := ⟨-4, 19531, 12500⟩
def B1_2_5U0_2_2EDLog : Ball := ⟨(-232631441969328242519371516318041 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B1_2_5U0_2_2ED : Ball := ⟨(11358811732757374761614612713019 / 50000000000000000000000000000000), (1033962531 / 10000000000000000000000000000000)⟩
def B1_2_5U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 180469, 100000⟩
def B1_2_5U0_2_2EOneDLog : Ball := ⟨(-2568958716933578869052947578733 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_2_5U0_2_2EOneD : Ball := ⟨(9272348213725720898382327931727 / 100000000000000000000000000000000), (38215797243 / 100000000000000000000000000000000)⟩
def B1_2_5U0_2_2BinaryEntropy : Ball := ⟨(7751780094199723268145106355019 / 20000000000000000000000000000000), (52691272677 / 100000000000000000000000000000000)⟩
def B1_2_5U0_2_2Leaf : Ball := ⟨(164606275545034138422274949480111 / 50000000000000000000000000000000), (33467732881 / 20000000000000000000000000000000)⟩
def B1_2_5U0_2_2Mass : Ball := ⟨(340073829440952693670776139029 / 12500000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
def B1_2_5U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_2_5U1_0_3Mass : Ball := ⟨(340073829440952693670776139029 / 12500000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
def B1_2_5U1_1_2D : Ball := .exact 0
def B1_2_5U1_1_2OneD : Ball := .exact 1
def B1_2_5U1_1_2ED : Ball := .exact 0
def B1_2_5U1_1_2EOneDLog : Ball := .exact 0
def B1_2_5U1_1_2EOneD : Ball := ⟨0, 0⟩
def B1_2_5U1_1_2BinaryEntropy : Ball := ⟨0, 0⟩
def B1_2_5U1_1_2Leaf : Ball := ⟨(40235947810852509365018973782911 / 12500000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B1_2_5U1_1_2Mass : Ball := ⟨(1186081054548533539957298951707 / 25000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
def B1_2_5U1_2_1D : Ball := .exact (10533 / 250000)
def B1_2_5U1_2_1OneD : Ball := .exact (239467 / 250000)
def B1_2_5U1_2_1EDLogWitness : LogWitness := ⟨-5, 21066, 15625⟩
def B1_2_5U1_2_1EDLog : Ball := ⟨(-316694773200784155107075107979101 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B1_2_5U1_2_1ED : Ball := ⟨(21348774695192700836754061519 / 160000000000000000000000000000), (5353078821 / 100000000000000000000000000000000)⟩
def B1_2_5U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 239467, 125000⟩
def B1_2_5U1_2_1EOneDLog : Ball := ⟨(-4304529756115245594727191194021 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_2_5U1_2_1EOneD : Ball := ⟨(824634261686119613466029034927 / 20000000000000000000000000000000), (507091097 / 1250000000000000000000000000000)⟩
def B1_2_5U1_2_1BinaryEntropy : Ball := ⟨(20386523194061197667938115193607 / 100000000000000000000000000000000), (47704726189 / 100000000000000000000000000000000)⟩
def B1_2_5U1_2_1Leaf : Ball := ⟨(157553349337076361610941936324801 / 50000000000000000000000000000000), (124378402689 / 100000000000000000000000000000000)⟩
def B1_2_5U1_2_1Mass : Ball := ⟨(10839580338829366322698124931 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_2_5Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_2_5U0_0_4Leaf
  | 0, 1, 3 => B1_2_5U0_1_3Leaf
  | 0, 2, 2 => B1_2_5U0_2_2Leaf
  | 1, 0, 3 => B1_2_5U1_0_3Leaf
  | 1, 1, 2 => B1_2_5U1_1_2Leaf
  | 1, 2, 1 => B1_2_5U1_2_1Leaf
  | _, _, _ => (.exact 0)
def B1_2_5Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_2_5U0_0_4Mass
  | 0, 1, 3 => B1_2_5U0_1_3Mass
  | 0, 2, 2 => B1_2_5U0_2_2Mass
  | 1, 0, 3 => B1_2_5U1_0_3Mass
  | 1, 1, 2 => B1_2_5U1_1_2Mass
  | 1, 2, 1 => B1_2_5U1_2_1Mass
  | _, _, _ => (.exact 0)
def B1_2_5Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_2_5U0_2_2BinaryEntropy
  | 1, 1, 2 => B1_2_5U1_1_2BinaryEntropy
  | 1, 2, 1 => B1_2_5U1_2_1BinaryEntropy
  | _, _, _ => (.exact 0)
def B1_2_5S2 : Ball := ⟨(41450674273625169102162892218041 / 100000000000000000000000000000000), (16917009863 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_3_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_3_4U0_0_4Leaf : Ball := ⟨0, 0⟩
def B1_3_4U0_0_4Mass : Ball := ⟨(11296930969545920829977701957 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B1_3_4U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_3_4U0_1_3Mass : Ball := ⟨(1835521493311920037404366035991 / 50000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
def B1_3_4U0_2_2D : Ball := .exact (46483 / 500000)
def B1_3_4U0_2_2OneD : Ball := .exact (453517 / 500000)
def B1_3_4U0_2_2EDLogWitness : LogWitness := ⟨-4, 46483, 31250⟩
def B1_3_4U0_2_2EDLog : Ball := ⟨(-59388036101788952339754245697507 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B1_3_4U0_2_2ED : Ball := ⟨(11042136328477823486435186411029 / 50000000000000000000000000000000), (9843158123 / 100000000000000000000000000000000)⟩
def B1_3_4U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 453517, 250000⟩
def B1_3_4U0_2_2EOneDLog : Ball := ⟨(-609845895945556733363202867553 / 6250000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_3_4U0_2_2EOneD : Ball := ⟨(8850415398129313697429749596289 / 100000000000000000000000000000000), (19207192059 / 50000000000000000000000000000000)⟩
def B1_3_4U0_2_2BinaryEntropy : Ball := ⟨(4672325016734818529228545097933 / 12500000000000000000000000000000), (5219480549 / 10000000000000000000000000000000)⟩
def B1_3_4U0_2_2Leaf : Ball := ⟨(65868316325445781613790663942627 / 20000000000000000000000000000000), (83718978921 / 50000000000000000000000000000000)⟩
def B1_3_4U0_2_2Mass : Ball := ⟨(13125128956309370446223832483411 / 50000000000000000000000000000000), (13 / 5000000000000000000000000000000)⟩
def B1_3_4U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_3_4U0_3_1Mass : Ball := ⟨(160933812951551762605775804971 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def B1_3_4U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_3_4U1_0_3Mass : Ball := ⟨(160933812951551762605775804971 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def B1_3_4U1_1_2D : Ball := .exact (301 / 250000)
def B1_3_4U1_1_2OneD : Ball := .exact (249699 / 250000)
def B1_3_4U1_1_2EDLogWitness : LogWitness := ⟨-10, 19264, 15625⟩
def B1_3_4U1_1_2EDLog : Ball := ⟨(-168052648302387693917382182971301 / 25000000000000000000000000000000), (7279189391 / 3125000000000000000000000000000)⟩
def B1_3_4U1_1_2ED : Ball := ⟨(80934155422429913390611259319 / 10000000000000000000000000000000), (28045261 / 10000000000000000000000000000000)⟩
def B1_3_4U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 249699, 125000⟩
def B1_3_4U1_1_2EOneDLog : Ball := ⟨(-1882383422351678894223498981 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_3_4U1_1_2EOneD : Ball := ⟨(120327490093514718261430648847 / 100000000000000000000000000000000), (2643790999 / 6250000000000000000000000000000)⟩
def B1_3_4U1_1_2BinaryEntropy : Ball := ⟨(101312396485723126742137796647 / 10000000000000000000000000000000), (21316049989 / 50000000000000000000000000000000)⟩
def B1_3_4U1_1_2Leaf : Ball := ⟨(6433876123243260184700997177711 / 2000000000000000000000000000000), (7936153439 / 6250000000000000000000000000000)⟩
def B1_3_4U1_1_2Mass : Ball := ⟨(13125128956309370446223832483411 / 50000000000000000000000000000000), (13 / 5000000000000000000000000000000)⟩
def B1_3_4U1_2_1D : Ball := .exact (10537 / 250000)
def B1_3_4U1_2_1OneD : Ball := .exact (239463 / 250000)
def B1_3_4U1_2_1EDLogWitness : LogWitness := ⟨-5, 21074, 15625⟩
def B1_3_4U1_2_1EDLog : Ball := ⟨(-316656804524485588305492584261679 / 100000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B1_3_4U1_2_1ED : Ball := ⟨(13346450997098018575899901441461 / 100000000000000000000000000000000), (53551117 / 1000000000000000000000000000000)⟩
def B1_3_4U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 239463, 125000⟩
def B1_3_4U1_2_1EOneDLog : Ball := ⟨(-4306200146360205403795606812577 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_3_4U1_2_1EOneD : Ball := ⟨(4124702422591415466436429576641 / 100000000000000000000000000000000), (20283305067 / 50000000000000000000000000000000)⟩
def B1_3_4U1_2_1BinaryEntropy : Ball := ⟨(20392630156313491532468080158787 / 100000000000000000000000000000000), (11926689767 / 25000000000000000000000000000000)⟩
def B1_3_4U1_2_1Leaf : Ball := ⟨(315104123573492828661284511435279 / 100000000000000000000000000000000), (124377386249 / 100000000000000000000000000000000)⟩
def B1_3_4U1_2_1Mass : Ball := ⟨(1835521493311920037404366035991 / 50000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
def B1_3_4U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_3_4U1_3_0Mass : Ball := ⟨(11296930969545920829977701957 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B1_3_4Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_3_4U0_0_4Leaf
  | 0, 1, 3 => B1_3_4U0_1_3Leaf
  | 0, 2, 2 => B1_3_4U0_2_2Leaf
  | 0, 3, 1 => B1_3_4U0_3_1Leaf
  | 1, 0, 3 => B1_3_4U1_0_3Leaf
  | 1, 1, 2 => B1_3_4U1_1_2Leaf
  | 1, 2, 1 => B1_3_4U1_2_1Leaf
  | 1, 3, 0 => B1_3_4U1_3_0Leaf
  | _, _, _ => (.exact 0)
def B1_3_4Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_3_4U0_0_4Mass
  | 0, 1, 3 => B1_3_4U0_1_3Mass
  | 0, 2, 2 => B1_3_4U0_2_2Mass
  | 0, 3, 1 => B1_3_4U0_3_1Mass
  | 1, 0, 3 => B1_3_4U1_0_3Mass
  | 1, 1, 2 => B1_3_4U1_1_2Mass
  | 1, 2, 1 => B1_3_4U1_2_1Mass
  | 1, 3, 0 => B1_3_4U1_3_0Mass
  | _, _, _ => (.exact 0)
def B1_3_4Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_3_4U0_2_2BinaryEntropy
  | 1, 1, 2 => B1_3_4U1_1_2BinaryEntropy
  | 1, 2, 1 => B1_3_4U1_2_1BinaryEntropy
  | _, _, _ => (.exact 0)
def B1_3_4S2 : Ball := ⟨(97325307607168493791537301136049 / 50000000000000000000000000000000), (4316662133 / 5000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_4_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_4_3U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_4_3U0_1_3Mass : Ball := ⟨(181419853805933728200300858261 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def B1_4_3U0_2_2D : Ball := .exact (23901 / 250000)
def B1_4_3U0_2_2OneD : Ball := .exact (226099 / 250000)
def B1_4_3U0_2_2EDLogWitness : LogWitness := ⟨-4, 23901, 15625⟩
def B1_4_3U0_2_2EDLog : Ball := ⟨(-234754061879590774959727984514419 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def B1_4_3U0_2_2ED : Ball := ⟨(22443427331936396449249834231517 / 100000000000000000000000000000000), (5061233619 / 50000000000000000000000000000000)⟩
def B1_4_3U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 226099, 125000⟩
def B1_4_3U0_2_2EOneDLog : Ball := ⟨(-2512199035246581498367078978841 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_4_3U0_2_2EOneD : Ball := ⟨(568005689670216830199298190037 / 6250000000000000000000000000000), (4787832559 / 12500000000000000000000000000000)⟩
def B1_4_3U0_2_2BinaryEntropy : Ball := ⟨(38158282671685166868591109420493 / 100000000000000000000000000000000), (10494822921 / 20000000000000000000000000000000)⟩
def B1_4_3U0_2_2Leaf : Ball := ⟨(6585442494448705906921534158549 / 2000000000000000000000000000000), (8369104801 / 5000000000000000000000000000000)⟩
def B1_4_3U0_2_2Mass : Ball := ⟨(12008393707958752871067573302183 / 100000000000000000000000000000000), (27 / 20000000000000000000000000000000)⟩
def B1_4_3U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_4_3U0_3_1Mass : Ball := ⟨(1880816292854954103757064512223 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def B1_4_3U0_4_0Leaf : Ball := ⟨0, 0⟩
def B1_4_3U0_4_0Mass : Ball := ⟨(477318587058984464774530633 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_4_3U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_4_3U1_0_3Mass : Ball := ⟨(477318587058984464774530633 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_4_3U1_1_2D : Ball := .exact (41743 / 1000000)
def B1_4_3U1_1_2OneD : Ball := .exact (958257 / 1000000)
def B1_4_3U1_1_2EDLogWitness : LogWitness := ⟨-5, 41743, 31250⟩
def B1_4_3U1_1_2EDLog : Ball := ⟨(-317622350641322343593845801674799 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B1_4_3U1_1_2ED : Ball := ⟨(13258509782820718588637905299311 / 100000000000000000000000000000000), (5303654449 / 100000000000000000000000000000000)⟩
def B1_4_3U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 958257, 500000⟩
def B1_4_3U1_1_2EOneDLog : Ball := ⟨(-4263926976511183716334593201789 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_4_3U1_1_2EOneD : Ball := ⟨(4085937872730677374463638277767 / 100000000000000000000000000000000), (40583762551 / 100000000000000000000000000000000)⟩
def B1_4_3U1_1_2BinaryEntropy : Ball := ⟨(10118925965681387834100947412289 / 50000000000000000000000000000000), (47655301817 / 100000000000000000000000000000000)⟩
def B1_4_3U1_1_2Leaf : Ball := ⟨(39396163226118301215806980271601 / 12500000000000000000000000000000), (995224919 / 800000000000000000000000000000)⟩
def B1_4_3U1_1_2Mass : Ball := ⟨(1880816292854954103757064512223 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
def B1_4_3U1_2_1D : Ball := .exact (3057 / 1000000)
def B1_4_3U1_2_1OneD : Ball := .exact (996943 / 1000000)
def B1_4_3U1_2_1EDLogWitness : LogWitness := ⟨-9, 24456, 15625⟩
def B1_4_3U1_2_1EDLog : Ball := ⟨(-579032123607343959922323580543109 / 100000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
def B1_4_3U1_2_1ED : Ball := ⟨(44252530046691262137063579643 / 2500000000000000000000000000000), (647344931 / 100000000000000000000000000000000)⟩
def B1_4_3U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 996943, 500000⟩
def B1_4_3U1_2_1EOneDLog : Ball := ⟨(-76542054229892072811856966359 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_4_3U1_2_1EOneD : Ball := ⟨(305232260680445170981084478451 / 100000000000000000000000000000000), (42222178381 / 100000000000000000000000000000000)⟩
def B1_4_3U1_2_1BinaryEntropy : Ball := ⟨(1143614277822635468776237732663 / 50000000000000000000000000000000), (42998992299 / 100000000000000000000000000000000)⟩
def B1_4_3U1_2_1Leaf : Ball := ⟨(321395577316988970435636338251871 / 100000000000000000000000000000000), (6343036931 / 5000000000000000000000000000000)⟩
def B1_4_3U1_2_1Mass : Ball := ⟨(12008393707958752871067573302183 / 100000000000000000000000000000000), (27 / 20000000000000000000000000000000)⟩
def B1_4_3U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_4_3U1_3_0Mass : Ball := ⟨(181419853805933728200300858261 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def B1_4_3Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B1_4_3U0_1_3Leaf
  | 0, 2, 2 => B1_4_3U0_2_2Leaf
  | 0, 3, 1 => B1_4_3U0_3_1Leaf
  | 0, 4, 0 => B1_4_3U0_4_0Leaf
  | 1, 0, 3 => B1_4_3U1_0_3Leaf
  | 1, 1, 2 => B1_4_3U1_1_2Leaf
  | 1, 2, 1 => B1_4_3U1_2_1Leaf
  | 1, 3, 0 => B1_4_3U1_3_0Leaf
  | _, _, _ => (.exact 0)
def B1_4_3Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B1_4_3U0_1_3Mass
  | 0, 2, 2 => B1_4_3U0_2_2Mass
  | 0, 3, 1 => B1_4_3U0_3_1Mass
  | 0, 4, 0 => B1_4_3U0_4_0Mass
  | 1, 0, 3 => B1_4_3U1_0_3Mass
  | 1, 1, 2 => B1_4_3U1_1_2Mass
  | 1, 2, 1 => B1_4_3U1_2_1Mass
  | 1, 3, 0 => B1_4_3U1_3_0Mass
  | _, _, _ => (.exact 0)
def B1_4_3Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_4_3U0_2_2BinaryEntropy
  | 1, 1, 2 => B1_4_3U1_1_2BinaryEntropy
  | 1, 2, 1 => B1_4_3U1_2_1BinaryEntropy
  | _, _, _ => (.exact 0)
def B1_4_3S2 : Ball := ⟨(45043077270396458956602823687649 / 50000000000000000000000000000000), (4986188371 / 12500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_5_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_5_2U0_2_2D : Ball := .exact (109933 / 1000000)
def B1_5_2U0_2_2OneD : Ball := .exact (890067 / 1000000)
def B1_5_2U0_2_2EDLogWitness : LogWitness := ⟨-4, 109933, 62500⟩
def B1_5_2U0_2_2EDLog : Ball := ⟨(-220788418967003649163974598210309 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B1_5_2U0_2_2ED : Ball := ⟨(12135966631149806081771609752527 / 50000000000000000000000000000000), (93116873 / 800000000000000000000000000000)⟩
def B1_5_2U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 890067, 500000⟩
def B1_5_2U0_2_2EOneDLog : Ball := ⟨(-11645853819053979009096802094341 / 100000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def B1_5_2U0_2_2EOneD : Ball := ⟨(1295698771395489741836220418713 / 12500000000000000000000000000000), (9423950929 / 25000000000000000000000000000000)⟩
def B1_5_2U0_2_2BinaryEntropy : Ball := ⟨(1056437458337829421706235965909 / 2500000000000000000000000000000), (53991256491 / 100000000000000000000000000000000)⟩
def B1_5_2U0_2_2Leaf : Ball := ⟨(164379506607404830246102091070317 / 50000000000000000000000000000000), (4176966691 / 2500000000000000000000000000000)⟩
def B1_5_2U0_2_2Mass : Ball := ⟨(27838926089202276630516723591 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def B1_5_2U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_5_2U0_3_1Mass : Ball := ⟨(394443851550199476968409845113 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def B1_5_2U0_4_0Leaf : Ball := ⟨0, 0⟩
def B1_5_2U0_4_0Mass : Ball := ⟨(4456348111125662593963668059 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_5_2U1_1_2D : Ball := .exact (10523 / 250000)
def B1_5_2U1_1_2OneD : Ball := .exact (239477 / 250000)
def B1_5_2U1_1_2EDLogWitness : LogWitness := ⟨-5, 21046, 15625⟩
def B1_5_2U1_1_2EDLog : Ball := ⟨(-15839487900517856513979567611963 / 5000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B1_5_2U1_1_2ED : Ball := ⟨(2666862898834390465545711839691 / 20000000000000000000000000000000), (5347996623 / 100000000000000000000000000000000)⟩
def B1_5_2U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 239477, 125000⟩
def B1_5_2U1_1_2EOneDLog : Ball := ⟨(-537544237821271786708674943729 / 12500000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_5_2U1_1_2EOneD : Ball := ⟨(205967170305159525865013359199 / 5000000000000000000000000000000), (20284490913 / 50000000000000000000000000000000)⟩
def B1_5_2U1_1_2BinaryEntropy : Ball := ⟨(20371253012688064641427839024309 / 100000000000000000000000000000000), (47699643991 / 100000000000000000000000000000000)⟩
def B1_5_2U1_1_2Leaf : Ball := ⟨(315113136425802459623382275685407 / 100000000000000000000000000000000), (124380943787 / 100000000000000000000000000000000)⟩
def B1_5_2U1_1_2Mass : Ball := ⟨(4456348111125662593963668059 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_5_2U1_2_1D : Ball := .exact (3747 / 1000000)
def B1_5_2U1_2_1OneD : Ball := .exact (996253 / 1000000)
def B1_5_2U1_2_1EDLogWitness : LogWitness := ⟨-9, 29976, 15625⟩
def B1_5_2U1_2_1EDLog : Ball := ⟨(-1745874924740808355355881138477 / 312500000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
def B1_5_2U1_2_1ED : Ball := ⟨(2093373869761218850405915720279 / 100000000000000000000000000000000), (396729057 / 50000000000000000000000000000000)⟩
def B1_5_2U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 996253, 500000⟩
def B1_5_2U1_2_1EOneDLog : Ball := ⟨(-750807517979978009641163873 / 200000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B1_5_2U1_2_1EOneD : Ball := ⟨(23374820069065844751219950999 / 6250000000000000000000000000000), (1318529867 / 3125000000000000000000000000000)⟩
def B1_5_2U1_2_1BinaryEntropy : Ball := ⟨(2727093239422083873864071740623 / 100000000000000000000000000000000), (21572552741 / 50000000000000000000000000000000)⟩
def B1_5_2U1_2_1Leaf : Ball := ⟨(32128452610103101750978888588423 / 10000000000000000000000000000000), (25363380933 / 20000000000000000000000000000000)⟩
def B1_5_2U1_2_1Mass : Ball := ⟨(394443851550199476968409845113 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def B1_5_2U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_5_2U1_3_0Mass : Ball := ⟨(27838926089202276630516723591 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def B1_5_2Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_5_2U0_2_2Leaf
  | 0, 3, 1 => B1_5_2U0_3_1Leaf
  | 0, 4, 0 => B1_5_2U0_4_0Leaf
  | 1, 1, 2 => B1_5_2U1_1_2Leaf
  | 1, 2, 1 => B1_5_2U1_2_1Leaf
  | 1, 3, 0 => B1_5_2U1_3_0Leaf
  | _, _, _ => (.exact 0)
def B1_5_2Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_5_2U0_2_2Mass
  | 0, 3, 1 => B1_5_2U0_3_1Mass
  | 0, 4, 0 => B1_5_2U0_4_0Mass
  | 1, 1, 2 => B1_5_2U1_1_2Mass
  | 1, 2, 1 => B1_5_2U1_2_1Mass
  | 1, 3, 0 => B1_5_2U1_3_0Mass
  | _, _, _ => (.exact 0)
def B1_5_2Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B1_5_2U0_2_2BinaryEntropy
  | 1, 1, 2 => B1_5_2U1_1_2BinaryEntropy
  | 1, 2, 1 => B1_5_2U1_2_1BinaryEntropy
  | _, _, _ => (.exact 0)
def B1_5_2S2 : Ball := ⟨(3448608467743772816283012723469 / 100000000000000000000000000000000), (351540337 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_6_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B1_6_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨1, 0⟩
  | 0, 4, 0 => ⟨(7768490128715345018830058107081 / 25000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(7768490128715345018830058107081 / 25000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨1, 0⟩
  | _, _, _ => (.exact 0)
def B1_6_1Den : Ball := ⟨(32768490128715345018830058107081 / 12500000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
def B1_6_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(476830025998288559780831570863 / 1250000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(148169974001711440219168429137 / 1250000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(148169974001711440219168429137 / 1250000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(476830025998288559780831570863 / 1250000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_6_1Law (u : Shape) : Ball := if u ∈ below (shape 1 6 1) then B1_6_1Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_6_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 2, 1 => (41991 / 1000000)
  | _, _, _ => 0
def B1_6_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_6_1Binary u else if i = 3 then B1_6_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_6_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_6_1LittleRat u w i)
  else .exact (littleLaw (shape 1 6 1) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_6_1U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_6_1U0_3_1Mass : Ball := ⟨(2506339406252300091999692633 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B1_6_1U0_4_0Leaf : Ball := ⟨0, 0⟩
def B1_6_1U0_4_0Mass : Ball := ⟨(77881891746725088607012689 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_6_1U1_2_1D : Ball := .exact (41991 / 1000000)
def B1_6_1U1_2_1OneD : Ball := .exact (958009 / 1000000)
def B1_6_1U1_2_1EDLogWitness : LogWitness := ⟨-5, 41991, 31250⟩
def B1_6_1U1_2_1EDLog : Ball := ⟨(-63405999387510370889753295440677 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B1_6_1U1_2_1ED : Ball := ⟨(13312406601404739920158153144247 / 100000000000000000000000000000000), (2667582037 / 50000000000000000000000000000000)⟩
def B1_6_1U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 958009, 500000⟩
def B1_6_1U1_2_1EOneDLog : Ball := ⟨(-857962129667603414297940708059 / 20000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def B1_6_1U1_2_1EOneD : Ball := ⟨(2054838604701827698320389699467 / 50000000000000000000000000000000), (40573259341 / 100000000000000000000000000000000)⟩
def B1_6_1U1_2_1BinaryEntropy : Ball := ⟨(20332678136697661665572831142557 / 100000000000000000000000000000000), (596085143 / 1250000000000000000000000000000)⟩
def B1_6_1U1_2_1Leaf : Ball := ⟨(63025878349743608807433148670163 / 20000000000000000000000000000000), (62193680031 / 50000000000000000000000000000000)⟩
def B1_6_1U1_2_1Mass : Ball := ⟨(77881891746725088607012689 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_6_1U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B1_6_1U1_3_0Mass : Ball := ⟨(2506339406252300091999692633 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B1_6_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B1_6_1U0_3_1Leaf
  | 0, 4, 0 => B1_6_1U0_4_0Leaf
  | 1, 2, 1 => B1_6_1U1_2_1Leaf
  | 1, 3, 0 => B1_6_1U1_3_0Leaf
  | _, _, _ => (.exact 0)
def B1_6_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B1_6_1U0_3_1Mass
  | 0, 4, 0 => B1_6_1U0_4_0Mass
  | 1, 2, 1 => B1_6_1U1_2_1Mass
  | 1, 3, 0 => B1_6_1U1_3_0Mass
  | _, _, _ => (.exact 0)
def B1_6_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B1_6_1U1_2_1BinaryEntropy
  | _, _, _ => (.exact 0)
def B1_6_1S2 : Ball := ⟨(6998203413539342705601595361 / 50000000000000000000000000000000), (5214669 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_1_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B2_1_5Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(143477508024585653583089862491 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(28769707349155561859531613298219 / 50000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨1, 0⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 2, 0, 2 => ⟨(28769707349155561859531613298219 / 50000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(143477508024585653583089862491 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_1_5Den : Ball := ⟨(7891318485718014751311470316071 / 2500000000000000000000000000000), (3 / 2000000000000000000000000000000)⟩
def B2_1_5Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(45454225515120282149964459091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(9114353767758831519889785991183 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(7920096003363024098980124774863 / 25000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(7920096003363024098980124774863 / 25000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(9114353767758831519889785991183 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(45454225515120282149964459091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_1_5Law (u : Shape) : Ball := if u ∈ below (shape 2 1 5) then B2_1_5Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B2_1_5Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 1, 2 => (1 / 1000000)
  | 2, 0, 2 => (50311 / 500000)
  | 2, 1, 1 => (21083 / 500000)
  | _, _, _ => 0
def B2_1_5LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B2_1_5Binary u else if i = 3 then B2_1_5Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B2_1_5Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B2_1_5LittleRat u w i)
  else .exact (littleLaw (shape 2 1 5) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B2_1_5U0_0_4Leaf : Ball := ⟨0, 0⟩
def B2_1_5U0_0_4Mass : Ball := ⟨(11980229688179108495838363 / 195312500000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B2_1_5U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_1_5U0_1_3Mass : Ball := ⟨(153743490797966165833014949619 / 12500000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def B2_1_5U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_1_5U1_0_3Mass : Ball := ⟨(534393655563127546658319620403 / 25000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def B2_1_5U1_1_2D : Ball := .exact (1 / 1000000)
def B2_1_5U1_1_2OneD : Ball := .exact (999999 / 1000000)
def B2_1_5U1_1_2EDLogWitness : LogWitness := ⟨-20, 16384, 15625⟩
def B2_1_5U1_1_2EDLog : Ball := ⟨(-276310211159285482082158898180173 / 20000000000000000000000000000000), (222346148671 / 50000000000000000000000000000000)⟩
def B2_1_5U1_1_2ED : Ball := ⟨(1381551055796427410410794491 / 100000000000000000000000000000000), (444693 / 100000000000000000000000000000000)⟩
def B2_1_5U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 999999, 500000⟩
def B2_1_5U1_1_2EOneDLog : Ball := ⟨(-100000050000033333358332099 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_1_5U1_1_2EOneD : Ball := ⟨(99999949999983333324998741 / 100000000000000000000000000000000), (8470321003 / 20000000000000000000000000000000)⟩
def B2_1_5U1_1_2BinaryEntropy : Ball := ⟨(62034628954096210987100657 / 4000000000000000000000000000000), (2117604603 / 5000000000000000000000000000000)⟩
def B2_1_5U1_1_2Leaf : Ball := ⟨(321887421543028831510114330187393 / 100000000000000000000000000000000), (127054878571 / 100000000000000000000000000000000)⟩
def B2_1_5U1_1_2Mass : Ball := ⟨(534393655563127546658319620403 / 25000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
def B2_1_5U2_0_2D : Ball := .exact (50311 / 500000)
def B2_1_5U2_0_2OneD : Ball := .exact (449689 / 500000)
def B2_1_5U2_0_2EDLogWitness : LogWitness := ⟨-4, 50311, 31250⟩
def B2_1_5U2_0_2EDLog : Ball := ⟨(-229638435735244201494939716178541 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B2_1_5U2_0_2ED : Ball := ⟨(23106678680551742042823824121317 / 100000000000000000000000000000000), (5326884327 / 50000000000000000000000000000000)⟩
def B2_1_5U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 449689, 250000⟩
def B2_1_5U2_0_2EOneDLog : Ball := ⟨(-2651296642407782012789413805853 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_1_5U2_0_2EOneD : Ball := ⟨(4769035743310852342197034819761 / 50000000000000000000000000000000), (7618027981 / 20000000000000000000000000000000)⟩
def B2_1_5U2_0_2BinaryEntropy : Ball := ⟨(39619335727403728419635964891949 / 100000000000000000000000000000000), (53005416021 / 100000000000000000000000000000000)⟩
def B2_1_5U2_0_2Leaf : Ball := ⟨(82279486472308748440293060428841 / 25000000000000000000000000000000), (20909479467 / 12500000000000000000000000000000)⟩
def B2_1_5U2_0_2Mass : Ball := ⟨(153743490797966165833014949619 / 12500000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def B2_1_5U2_1_1D : Ball := .exact (21083 / 500000)
def B2_1_5U2_1_1OneD : Ball := .exact (478917 / 500000)
def B2_1_5U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B2_1_5U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B2_1_5U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
def B2_1_5U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B2_1_5U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_1_5U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
def B2_1_5U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
def B2_1_5U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
def B2_1_5U2_1_1Mass : Ball := ⟨(11980229688179108495838363 / 195312500000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B2_1_5Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B2_1_5U0_0_4Leaf
  | 0, 1, 3 => B2_1_5U0_1_3Leaf
  | 1, 0, 3 => B2_1_5U1_0_3Leaf
  | 1, 1, 2 => B2_1_5U1_1_2Leaf
  | 2, 0, 2 => B2_1_5U2_0_2Leaf
  | 2, 1, 1 => B2_1_5U2_1_1Leaf
  | _, _, _ => (.exact 0)
def B2_1_5Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B2_1_5U0_0_4Mass
  | 0, 1, 3 => B2_1_5U0_1_3Mass
  | 1, 0, 3 => B2_1_5U1_0_3Mass
  | 1, 1, 2 => B2_1_5U1_1_2Mass
  | 2, 0, 2 => B2_1_5U2_0_2Mass
  | 2, 1, 1 => B2_1_5U2_1_1Mass
  | _, _, _ => (.exact 0)
def B2_1_5Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B2_1_5U1_1_2BinaryEntropy
  | 2, 0, 2 => B2_1_5U2_0_2BinaryEntropy
  | 2, 1, 1 => B2_1_5U2_1_1BinaryEntropy
  | _, _, _ => (.exact 0)
def B2_1_5S2 : Ball := ⟨(187018983303151686119192103891 / 1000000000000000000000000000000), (7633330409 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_2_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B2_2_4Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(3985809275202830388494116183 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(1687715475618203929478025269739 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(658685387040686388916222849389 / 2500000000000000000000000000000), (67 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(1687715475618203929478025269739 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 1, 2, 1 => ⟨(1687715475618203929478025269739 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(658685387040686388916222849389 / 2500000000000000000000000000000), (67 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(1687715475618203929478025269739 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(3985809275202830388494116183 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_2_4Den : Ball := ⟨(44944498689662557648179028647651 / 25000000000000000000000000000000), (49 / 25000000000000000000000000000000)⟩
def B2_2_4Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(1877555123344146106224953559491 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(7327764312033444386854140531431 / 50000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(1877555123344146106224953559491 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(6953020038287276387329040621707 / 12500000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(1877555123344146106224953559491 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(7327764312033444386854140531431 / 50000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(1877555123344146106224953559491 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_2_4Law (u : Shape) : Ball := if u ∈ below (shape 2 2 4) then B2_2_4Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B2_2_4Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (51781 / 500000)
  | 1, 1, 2 => (9039 / 1000000)
  | 1, 2, 1 => (42157 / 1000000)
  | 2, 0, 2 => (103577 / 1000000)
  | 2, 1, 1 => (8433 / 200000)
  | 2, 2, 0 => (31791 / 500000)
  | _, _, _ => 0
def B2_2_4LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B2_2_4Binary u else if i = 3 then B2_2_4Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B2_2_4Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B2_2_4LittleRat u w i)
  else .exact (littleLaw (shape 2 2 4) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B2_2_4U0_0_4Leaf : Ball := ⟨0, 0⟩
def B2_2_4U0_0_4Mass : Ball := ⟨(459983845027779558302590723 / 3125000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B2_2_4U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_2_4U0_1_3Mass : Ball := ⟨(1246537282943313726061518292613 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def B2_2_4U0_2_2D : Ball := .exact (51781 / 500000)
def B2_2_4U0_2_2OneD : Ball := .exact (448219 / 500000)
def B2_2_4U0_2_2EDLogWitness : LogWitness := ⟨-4, 51781, 31250⟩
def B2_2_4U0_2_2EDLog : Ball := ⟨(-226758481180942422019326103547823 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B2_2_4U0_2_2ED : Ball := ⟨(1174178091403037955458272496781 / 5000000000000000000000000000000), (5482526631 / 50000000000000000000000000000000)⟩
def B2_2_4U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 448219, 250000⟩
def B2_2_4U0_2_2EOneDLog : Ball := ⟨(-2186522923289837780427151140763 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_2_4U0_2_2EOneD : Ball := ⟨(9800411181540478001052772571617 / 100000000000000000000000000000000), (18982813031 / 50000000000000000000000000000000)⟩
def B2_2_4U0_2_2BinaryEntropy : Ball := ⟨(8092468768183228544720991965183 / 20000000000000000000000000000000), (53316700629 / 100000000000000000000000000000000)⟩
def B2_2_4U0_2_2Leaf : Ball := ⟨(82253651127559039261218997596489 / 25000000000000000000000000000000), (83606789407 / 50000000000000000000000000000000)⟩
def B2_2_4U0_2_2Mass : Ball := ⟨(973002741917034495619167964551 / 10000000000000000000000000000000), (1 / 781250000000000000000000000000)⟩
def B2_2_4U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_2_4U1_0_3Mass : Ball := ⟨(1246537282943313726061518292613 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def B2_2_4U1_1_2D : Ball := .exact (9039 / 1000000)
def B2_2_4U1_1_2OneD : Ball := .exact (990961 / 1000000)
def B2_2_4U1_1_2EDLogWitness : LogWitness := ⟨-7, 18078, 15625⟩
def B2_2_4U1_1_2EDLog : Ball := ⟨(-23531033650829315888782626557599 / 5000000000000000000000000000000), (169406589463 / 100000000000000000000000000000000)⟩
def B2_2_4U1_1_2ED : Ball := ⟨(4253940263396923726374123229083 / 100000000000000000000000000000000), (1531266163 / 100000000000000000000000000000000)⟩
def B2_2_4U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 990961, 500000⟩
def B2_2_4U1_1_2EOneDLog : Ball := ⟨(-56750622588966416224534897681 / 6250000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_2_4U1_1_2EOneD : Ball := ⟨(449901229691077990306250613927 / 50000000000000000000000000000000), (20984415413 / 50000000000000000000000000000000)⟩
def B2_2_4U1_1_2BinaryEntropy : Ball := ⟨(5780278459287214272168860398919 / 100000000000000000000000000000000), (4388291353 / 10000000000000000000000000000000)⟩
def B2_2_4U1_1_2Leaf : Ball := ⟨(320432811557770891591550164247193 / 100000000000000000000000000000000), (15810089661 / 12500000000000000000000000000000)⟩
def B2_2_4U1_1_2Mass : Ball := ⟨(18464861242187634366717571822117 / 50000000000000000000000000000000), (97 / 25000000000000000000000000000000)⟩
def B2_2_4U1_2_1D : Ball := .exact (42157 / 1000000)
def B2_2_4U1_2_1OneD : Ball := .exact (957843 / 1000000)
def B2_2_4U1_2_1EDLogWitness : LogWitness := ⟨-5, 42157, 31250⟩
def B2_2_4U1_2_1EDLog : Ball := ⟨(-316635453477610100398073168374679 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B2_2_4U1_2_1ED : Ball := ⟨(13348400812255609002481570559171 / 100000000000000000000000000000000), (1071251039 / 20000000000000000000000000000000)⟩
def B2_2_4U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 957843, 500000⟩
def B2_2_4U1_2_1EOneDLog : Ball := ⟨(-2153569876567388580629376620277 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_2_4U1_2_1EOneD : Ball := ⟨(128923864455058573764736499381 / 3125000000000000000000000000000), (40566228969 / 100000000000000000000000000000000)⟩
def B2_2_4U1_2_1BinaryEntropy : Ball := ⟨(10198032521952022401931681594393 / 50000000000000000000000000000000), (47707902563 / 100000000000000000000000000000000)⟩
def B2_2_4U1_2_1Leaf : Ball := ⟨(315102675079371637970947370752223 / 100000000000000000000000000000000), (62188407251 / 50000000000000000000000000000000)⟩
def B2_2_4U1_2_1Mass : Ball := ⟨(1246537282943313726061518292613 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def B2_2_4U2_0_2D : Ball := .exact (103577 / 1000000)
def B2_2_4U2_0_2OneD : Ball := .exact (896423 / 1000000)
def B2_2_4U2_0_2EDLogWitness : LogWitness := ⟨-4, 103577, 62500⟩
def B2_2_4U2_0_2EDLog : Ball := ⟨(-2834299976907655511632457381399 / 1250000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def B2_2_4U2_0_2ED : Ball := ⟨(23485463096653138794268403055453 / 100000000000000000000000000000000), (10966641449 / 100000000000000000000000000000000)⟩
def B2_2_4U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 896423, 500000⟩
def B2_2_4U2_0_2EOneDLog : Ball := ⟨(-2733571979905550299613262420469 / 25000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def B2_2_4U2_0_2EOneD : Ball := ⟨(306304599367859139528777442343 / 3125000000000000000000000000000), (37964990787 / 100000000000000000000000000000000)⟩
def B2_2_4U2_0_2BinaryEntropy : Ball := ⟨(40466620828510376790540144377003 / 100000000000000000000000000000000), (3332393051 / 6250000000000000000000000000000)⟩
def B2_2_4U2_0_2Leaf : Ball := ⟨(32901405318409308881068737266019 / 10000000000000000000000000000000), (167213261177 / 100000000000000000000000000000000)⟩
def B2_2_4U2_0_2Mass : Ball := ⟨(973002741917034495619167964551 / 10000000000000000000000000000000), (1 / 781250000000000000000000000000)⟩
def B2_2_4U2_1_1D : Ball := .exact (8433 / 200000)
def B2_2_4U2_1_1OneD : Ball := .exact (191567 / 200000)
def B2_2_4U2_1_1EDLogWitness : LogWitness := ⟨-5, 8433, 6250⟩
def B2_2_4U2_1_1EDLog : Ball := ⟨(-316616478595553215892035736909523 / 100000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B2_2_4U2_1_1ED : Ball := ⟨(1335013381998150134808768684679 / 10000000000000000000000000000000), (2678635817 / 50000000000000000000000000000000)⟩
def B2_2_4U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 191567, 100000⟩
def B2_2_4U2_1_1EOneDLog : Ball := ⟨(-4307974966568354882089913298341 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_2_4U2_1_1EOneD : Ball := ⟨(1031582300525750049621648026029 / 25000000000000000000000000000000), (10141472539 / 25000000000000000000000000000000)⟩
def B2_2_4U2_1_1BinaryEntropy : Ball := ⟨(20399118108915510943732037385873 / 100000000000000000000000000000000), (23854459501 / 50000000000000000000000000000000)⟩
def B2_2_4U2_1_1Leaf : Ball := ⟨(157550693764520845345323845072531 / 50000000000000000000000000000000), (62188153141 / 50000000000000000000000000000000)⟩
def B2_2_4U2_1_1Mass : Ball := ⟨(1246537282943313726061518292613 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def B2_2_4U2_2_0D : Ball := .exact (31791 / 500000)
def B2_2_4U2_2_0OneD : Ball := .exact (468209 / 500000)
def B2_2_4U2_2_0EDLogWitness : LogWitness := ⟨-4, 31791, 31250⟩
def B2_2_4U2_2_0EDLog : Ball := ⟨(-8610702711129322182939633075951 / 3125000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def B2_2_4U2_2_0ED : Ball := ⟨(4379885598232196504285342001881 / 25000000000000000000000000000000), (1683001527 / 25000000000000000000000000000000)⟩
def B2_2_4U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 468209, 250000⟩
def B2_2_4U2_2_0EOneDLog : Ball := ⟨(-1642333024891709491091130987267 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_2_4U2_2_0EOneD : Ball := ⟨(3075820413006089636457149393669 / 50000000000000000000000000000000), (9914711231 / 25000000000000000000000000000000)⟩
def B2_2_4U2_2_0BinaryEntropy : Ball := ⟨(7019587905594302389098077713847 / 25000000000000000000000000000000), (1963346139 / 4000000000000000000000000000000)⟩
def B2_2_4U2_2_0Leaf : Ball := ⟨(82374919459880072618242752497539 / 25000000000000000000000000000000), (33612037649 / 20000000000000000000000000000000)⟩
def B2_2_4U2_2_0Mass : Ball := ⟨(459983845027779558302590723 / 3125000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B2_2_4Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B2_2_4U0_0_4Leaf
  | 0, 1, 3 => B2_2_4U0_1_3Leaf
  | 0, 2, 2 => B2_2_4U0_2_2Leaf
  | 1, 0, 3 => B2_2_4U1_0_3Leaf
  | 1, 1, 2 => B2_2_4U1_1_2Leaf
  | 1, 2, 1 => B2_2_4U1_2_1Leaf
  | 2, 0, 2 => B2_2_4U2_0_2Leaf
  | 2, 1, 1 => B2_2_4U2_1_1Leaf
  | 2, 2, 0 => B2_2_4U2_2_0Leaf
  | _, _, _ => (.exact 0)
def B2_2_4Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B2_2_4U0_0_4Mass
  | 0, 1, 3 => B2_2_4U0_1_3Mass
  | 0, 2, 2 => B2_2_4U0_2_2Mass
  | 1, 0, 3 => B2_2_4U1_0_3Mass
  | 1, 1, 2 => B2_2_4U1_1_2Mass
  | 1, 2, 1 => B2_2_4U1_2_1Mass
  | 2, 0, 2 => B2_2_4U2_0_2Mass
  | 2, 1, 1 => B2_2_4U2_1_1Mass
  | 2, 2, 0 => B2_2_4U2_2_0Mass
  | _, _, _ => (.exact 0)
def B2_2_4Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B2_2_4U0_2_2BinaryEntropy
  | 1, 1, 2 => B2_2_4U1_1_2BinaryEntropy
  | 1, 2, 1 => B2_2_4U1_2_1BinaryEntropy
  | 2, 0, 2 => B2_2_4U2_0_2BinaryEntropy
  | 2, 1, 1 => B2_2_4U2_1_1BinaryEntropy
  | 2, 2, 0 => B2_2_4U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
def B2_2_4S2 : Ball := ⟨(2096023073863630218761879684683 / 1000000000000000000000000000000), (89698574533 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_3_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B2_3_3U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_3_3U0_1_3Mass : Ball := ⟨(466550470537589006566890154189 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def B2_3_3U0_2_2D : Ball := .exact (55041 / 500000)
def B2_3_3U0_2_2OneD : Ball := .exact (444959 / 500000)
def B2_3_3U0_2_2EDLogWitness : LogWitness := ⟨-4, 55041, 31250⟩
def B2_3_3U0_2_2EDLog : Ball := ⟨(-55163243408937486421493177388873 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B2_3_3U0_2_2ED : Ball := ⟨(3036240080471328190125405976661 / 12500000000000000000000000000000), (5827692557 / 50000000000000000000000000000000)⟩
def B2_3_3U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 444959, 250000⟩
def B2_3_3U0_2_2EOneDLog : Ball := ⟨(-5831297766604325579437218806789 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_3_3U0_2_2EOneD : Ball := ⟨(51893768458609882110016108861 / 500000000000000000000000000000), (37689493321 / 100000000000000000000000000000000)⟩
def B2_3_3U0_2_2BinaryEntropy : Ball := ⟨(21149488564266295949066621061427 / 50000000000000000000000000000000), (54007032481 / 100000000000000000000000000000000)⟩
def B2_3_3U0_2_2Leaf : Ball := ⟨(328752530760038539330924883010379 / 100000000000000000000000000000000), (41768878111 / 25000000000000000000000000000000)⟩
def B2_3_3U0_2_2Mass : Ball := ⟨(3278427034394245768597523877587 / 25000000000000000000000000000000), (67 / 50000000000000000000000000000000)⟩
def B2_3_3U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_3_3U0_3_1Mass : Ball := ⟨(14715925893121844557257952283 / 1562500000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def B2_3_3U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_3_3U1_0_3Mass : Ball := ⟨(64933664603666840044717438439 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def B2_3_3U1_1_2D : Ball := .exact (573 / 125000)
def B2_3_3U1_1_2OneD : Ball := .exact (124427 / 125000)
def B2_3_3U1_1_2EDLogWitness : LogWitness := ⟨-8, 18336, 15625⟩
def B2_3_3U1_1_2EDLog : Ball := ⟨(-21540733198278794446444222587871 / 4000000000000000000000000000000), (95291206573 / 50000000000000000000000000000000)⟩
def B2_3_3U1_1_2ED : Ball := ⟨(246856802452274984356250790857 / 10000000000000000000000000000000), (436814891 / 50000000000000000000000000000000)⟩
def B2_3_3U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 124427, 62500⟩
def B2_3_3U1_1_2EOneDLog : Ball := ⟨(-22972693733715313906167338253 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_3_3U1_1_2EOneD : Ball := ⟨(457347738112799258144429343489 / 100000000000000000000000000000000), (8431501483 / 20000000000000000000000000000000)⟩
def B2_3_3U1_1_2BinaryEntropy : Ball := ⟨(1621827215102114015771898184501 / 50000000000000000000000000000000), (43225277149 / 100000000000000000000000000000000)⟩
def B2_3_3U1_1_2Leaf : Ball := ⟨(64229963229552056661686960472001 / 20000000000000000000000000000000), (31690933043 / 25000000000000000000000000000000)⟩
def B2_3_3U1_1_2Mass : Ball := ⟨(25412930157212049388918541585447 / 100000000000000000000000000000000), (239 / 100000000000000000000000000000000)⟩
def B2_3_3U1_2_1D : Ball := .exact (1687 / 40000)
def B2_3_3U1_2_1OneD : Ball := .exact (38313 / 40000)
def B2_3_3U1_2_1EDLogWitness : LogWitness := ⟨-5, 1687, 1250⟩
def B2_3_3U1_2_1EDLog : Ball := ⟨(-316592765055010505433466504472543 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B2_3_3U1_2_1ED : Ball := ⟨(1335229986619506806665644982613 / 10000000000000000000000000000000), (669817773 / 12500000000000000000000000000000)⟩
def B2_3_3U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 38313, 20000⟩
def B2_3_3U1_2_1EOneDLog : Ball := ⟨(-2154509496585081089533142092769 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_3_3U1_2_1EOneD : Ball := ⟨(4127286117133210589164163650013 / 100000000000000000000000000000000), (40565466639 / 100000000000000000000000000000000)⟩
def B2_3_3U1_2_1BinaryEntropy : Ball := ⟨(20402934217339847998287789143041 / 100000000000000000000000000000000), (47710189551 / 100000000000000000000000000000000)⟩
def B2_3_3U1_2_1Leaf : Ball := ⟨(315099778091129256590273089386111 / 100000000000000000000000000000000), (124375671007 / 100000000000000000000000000000000)⟩
def B2_3_3U1_2_1Mass : Ball := ⟨(25412930157212049388918541585447 / 100000000000000000000000000000000), (239 / 100000000000000000000000000000000)⟩
def B2_3_3U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_3_3U1_3_0Mass : Ball := ⟨(64933664603666840044717438439 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def B2_3_3U2_0_2D : Ball := .exact (104091 / 1000000)
def B2_3_3U2_0_2OneD : Ball := .exact (895909 / 1000000)
def B2_3_3U2_0_2EDLogWitness : LogWitness := ⟨-4, 104091, 62500⟩
def B2_3_3U2_0_2EDLog : Ball := ⟨(-56562244060752588474630885788059 / 25000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def B2_3_3U2_0_2ED : Ball := ⟨(23550482186111190747651214130259 / 100000000000000000000000000000000), (2755265829 / 25000000000000000000000000000000)⟩
def B2_3_3U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 895909, 500000⟩
def B2_3_3U2_0_2EOneDLog : Ball := ⟨(-10991643366502651450018611428491 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_3_3U2_0_2EOneD : Ball := ⟨(615469513552501497370920259143 / 6250000000000000000000000000000), (37943222041 / 100000000000000000000000000000000)⟩
def B2_3_3U2_0_2BinaryEntropy : Ball := ⟨(40613032720117741425840847164349 / 100000000000000000000000000000000), (53372710683 / 100000000000000000000000000000000)⟩
def B2_3_3U2_0_2Leaf : Ball := ⟨(328995014858302227927479117427341 / 100000000000000000000000000000000), (41800594201 / 25000000000000000000000000000000)⟩
def B2_3_3U2_0_2Mass : Ball := ⟨(14715925893121844557257952283 / 1562500000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def B2_3_3U2_1_1D : Ball := .exact (19419 / 500000)
def B2_3_3U2_1_1OneD : Ball := .exact (480581 / 500000)
def B2_3_3U2_1_1EDLogWitness : LogWitness := ⟨-5, 19419, 15625⟩
def B2_3_3U2_1_1EDLog : Ball := ⟨(-40604451627383861448565069676439 / 12500000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B2_3_3U2_1_1ED : Ball := ⟨(3153991384608668821878740352187 / 25000000000000000000000000000000), (2467279921 / 50000000000000000000000000000000)⟩
def B2_3_3U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 480581, 250000⟩
def B2_3_3U2_1_1EOneDLog : Ball := ⟨(-990307745431186665804901172341 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_3_3U2_1_1EOneD : Ball := ⟨(1903692346428260476156740841219 / 50000000000000000000000000000000), (40706794087 / 100000000000000000000000000000000)⟩
def B2_3_3U2_1_1BinaryEntropy : Ball := ⟨(152923162009199294660344707703 / 800000000000000000000000000000), (4728620721 / 10000000000000000000000000000000)⟩
def B2_3_3U2_1_1Leaf : Ball := ⟨(63127369504501703177055472529633 / 20000000000000000000000000000000), (62293831089 / 50000000000000000000000000000000)⟩
def B2_3_3U2_1_1Mass : Ball := ⟨(3278427034394245768597523877587 / 25000000000000000000000000000000), (67 / 50000000000000000000000000000000)⟩
def B2_3_3U2_2_0D : Ball := .exact (102383 / 1000000)
def B2_3_3U2_2_0OneD : Ball := .exact (897617 / 1000000)
def B2_3_3U2_2_0EDLogWitness : LogWitness := ⟨-4, 102383, 62500⟩
def B2_3_3U2_2_0EDLog : Ball := ⟨(-56975864894596222495907774317173 / 25000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def B2_3_3U2_2_0ED : Ball := ⟨(1166671995100689009559705131583 / 5000000000000000000000000000000), (5420110891 / 50000000000000000000000000000000)⟩
def B2_3_3U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 897617, 500000⟩
def B2_3_3U2_2_0EOneDLog : Ball := ⟨(-2160236099982276913212034276979 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_3_3U2_2_0EOneD : Ball := ⟨(1939064647357791456006646571599 / 20000000000000000000000000000000), (7603111731 / 20000000000000000000000000000000)⟩
def B2_3_3U2_2_0BinaryEntropy : Ball := ⟨(40125411917529625532633781163727 / 100000000000000000000000000000000), (1063837383 / 2000000000000000000000000000000)⟩
def B2_3_3U2_2_0Leaf : Ball := ⟨(329057178046601600722235670684489 / 100000000000000000000000000000000), (20904818139 / 12500000000000000000000000000000)⟩
def B2_3_3U2_2_0Mass : Ball := ⟨(466550470537589006566890154189 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
def B2_3_3Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B2_3_3U0_1_3Leaf
  | 0, 2, 2 => B2_3_3U0_2_2Leaf
  | 0, 3, 1 => B2_3_3U0_3_1Leaf
  | 1, 0, 3 => B2_3_3U1_0_3Leaf
  | 1, 1, 2 => B2_3_3U1_1_2Leaf
  | 1, 2, 1 => B2_3_3U1_2_1Leaf
  | 1, 3, 0 => B2_3_3U1_3_0Leaf
  | 2, 0, 2 => B2_3_3U2_0_2Leaf
  | 2, 1, 1 => B2_3_3U2_1_1Leaf
  | 2, 2, 0 => B2_3_3U2_2_0Leaf
  | _, _, _ => (.exact 0)
def B2_3_3Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B2_3_3U0_1_3Mass
  | 0, 2, 2 => B2_3_3U0_2_2Mass
  | 0, 3, 1 => B2_3_3U0_3_1Mass
  | 1, 0, 3 => B2_3_3U1_0_3Mass
  | 1, 1, 2 => B2_3_3U1_1_2Mass
  | 1, 2, 1 => B2_3_3U1_2_1Mass
  | 1, 3, 0 => B2_3_3U1_3_0Mass
  | 2, 0, 2 => B2_3_3U2_0_2Mass
  | 2, 1, 1 => B2_3_3U2_1_1Mass
  | 2, 2, 0 => B2_3_3U2_2_0Mass
  | _, _, _ => (.exact 0)
def B2_3_3Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B2_3_3U0_2_2BinaryEntropy
  | 1, 1, 2 => B2_3_3U1_1_2BinaryEntropy
  | 1, 2, 1 => B2_3_3U1_2_1BinaryEntropy
  | 2, 0, 2 => B2_3_3U2_0_2BinaryEntropy
  | 2, 1, 1 => B2_3_3U2_1_1BinaryEntropy
  | 2, 2, 0 => B2_3_3U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
def B2_3_3S2 : Ball := ⟨(257277205828662462897692981670147 / 100000000000000000000000000000000), (53506556373 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_4_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B2_4_2Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(131106254622443168152919965261 / 500000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(887034541322513256023482129547 / 12500000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(59473180615091031899554539751 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(1420107074792739577725554863013 / 20000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨1, 0⟩
  | 1, 3, 0 => ⟨(1420107074792739577725554863013 / 20000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(59473180615091031899554539751 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(887034541322513256023482129547 / 12500000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(131106254622443168152919965261 / 500000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_4_2Den : Ball := ⟨(2827422994051485268728099341981 / 1562500000000000000000000000000), (51 / 25000000000000000000000000000000)⟩
def B2_4_2Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(14490475834606388578250612343089 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(3921568081556569782136761397233 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(32866269004172783017016141121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(3923921728428956034133711412569 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(6907792021600978205615474676497 / 12500000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(3923921728428956034133711412569 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(32866269004172783017016141121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(3921568081556569782136761397233 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(14490475834606388578250612343089 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_4_2Law (u : Shape) : Ball := if u ∈ below (shape 2 4 2) then B2_4_2Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B2_4_2Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (104793 / 1000000)
  | 1, 1, 2 => (21063 / 500000)
  | 1, 2, 1 => (5907 / 500000)
  | 2, 0, 2 => (31669 / 500000)
  | 2, 1, 1 => (8433 / 200000)
  | 2, 2, 0 => (3277 / 31250)
  | _, _, _ => 0
def B2_4_2LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B2_4_2Binary u else if i = 3 then B2_4_2Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B2_4_2Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B2_4_2LittleRat u w i)
  else .exact (littleLaw (shape 2 4 2) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B2_4_2U0_2_2D : Ball := .exact (104793 / 1000000)
def B2_4_2U0_2_2OneD : Ball := .exact (895207 / 1000000)
def B2_4_2U0_2_2EDLogWitness : LogWitness := ⟨-4, 104793, 62500⟩
def B2_4_2U0_2_2EDLog : Ball := ⟨(-22557683032191364513180248834139 / 10000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B2_4_2U0_2_2ED : Ball := ⟨(23638872779924296614296978160759 / 100000000000000000000000000000000), (11095390457 / 100000000000000000000000000000000)⟩
def B2_4_2U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 895207, 500000⟩
def B2_4_2U0_2_2EOneDLog : Ball := ⟨(-22140060506662698219615744903 / 200000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_4_2U0_2_2EOneD : Ball := ⟨(990996857299399704254377607369 / 10000000000000000000000000000000), (2369593199 / 6250000000000000000000000000000)⟩
def B2_4_2U0_2_2BinaryEntropy : Ball := ⟨(10203134650540032134454188200943 / 25000000000000000000000000000000), (417554983 / 781250000000000000000000000000)⟩
def B2_4_2U0_2_2Leaf : Ball := ⟨(328968555657438867346861076509999 / 100000000000000000000000000000000), (1337500091 / 800000000000000000000000000000)⟩
def B2_4_2U0_2_2Mass : Ball := ⟨(2052429189538757016962171971651 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
def B2_4_2U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_4_2U0_3_1Mass : Ball := ⟨(27772520692964670763404186047 / 5000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def B2_4_2U0_4_0Leaf : Ball := ⟨0, 0⟩
def B2_4_2U0_4_0Mass : Ball := ⟨(2327587120855560415853758489 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B2_4_2U1_1_2D : Ball := .exact (21063 / 500000)
def B2_4_2U1_1_2OneD : Ball := .exact (478937 / 500000)
def B2_4_2U1_1_2EDLogWitness : LogWitness := ⟨-5, 21063, 15625⟩
def B2_4_2U1_1_2EDLog : Ball := ⟨(-316709015171897026732453267991509 / 100000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B2_4_2U1_1_2ED : Ball := ⟨(1334168397313133414813132636741 / 10000000000000000000000000000000), (1338079123 / 25000000000000000000000000000000)⟩
def B2_4_2U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 478937, 250000⟩
def B2_4_2U1_1_2EOneDLog : Ball := ⟨(-2151951683483404577051660903857 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_4_2U1_1_2EOneD : Ball := ⟨(2061298566864982675838782636621 / 50000000000000000000000000000000), (4056754187 / 10000000000000000000000000000000)⟩
def B2_4_2U1_1_2BinaryEntropy : Ball := ⟨(2038423291968812511025992287109 / 10000000000000000000000000000000), (2385198193 / 5000000000000000000000000000000)⟩
def B2_4_2U1_1_2Leaf : Ball := ⟨(78776916084225045920527158276243 / 25000000000000000000000000000000), (124378783853 / 100000000000000000000000000000000)⟩
def B2_4_2U1_1_2Mass : Ball := ⟨(111156756821736540136239317403 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def B2_4_2U1_2_1D : Ball := .exact (5907 / 500000)
def B2_4_2U1_2_1OneD : Ball := .exact (494093 / 500000)
def B2_4_2U1_2_1EDLogWitness : LogWitness := ⟨-7, 23628, 15625⟩
def B2_4_2U1_2_1EDLog : Ball := ⟨(-443847001009709356305572202505481 / 100000000000000000000000000000000), (21175823683 / 12500000000000000000000000000000)⟩
def B2_4_2U1_2_1ED : Ball := ⟨(13109021174821765838485075001 / 250000000000000000000000000000), (2001369449 / 100000000000000000000000000000000)⟩
def B2_4_2U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 494093, 250000⟩
def B2_4_2U1_2_1EOneDLog : Ball := ⟨(-594216992173993420750540540271 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_4_2U1_2_1EOneD : Ball := ⟨(73399614078556232809724206791 / 6250000000000000000000000000000), (8370261001 / 20000000000000000000000000000000)⟩
def B2_4_2U1_2_1BinaryEntropy : Ball := ⟨(7236886374299125448895135111753 / 100000000000000000000000000000000), (44353016817 / 100000000000000000000000000000000)⟩
def B2_4_2U1_2_1Leaf : Ball := ⟨(319986192537070428737598453638203 / 100000000000000000000000000000000), (31576107139 / 25000000000000000000000000000000)⟩
def B2_4_2U1_2_1Mass : Ball := ⟨(7827350401585707164473237434991 / 100000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
def B2_4_2U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_4_2U1_3_0Mass : Ball := ⟨(111156756821736540136239317403 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def B2_4_2U2_0_2D : Ball := .exact (31669 / 500000)
def B2_4_2U2_0_2OneD : Ball := .exact (468331 / 500000)
def B2_4_2U2_0_2EDLogWitness : LogWitness := ⟨-4, 31669, 31250⟩
def B2_4_2U2_0_2EDLog : Ball := ⟨(-275926981399378237867248750022457 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def B2_4_2U2_0_2ED : Ball := ⟨(8738331573936909415017900664461 / 50000000000000000000000000000000), (6706171603 / 100000000000000000000000000000000)⟩
def B2_4_2U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 468331, 250000⟩
def B2_4_2U2_0_2EOneDLog : Ball := ⟨(-817909844265902747909981412881 / 12500000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_4_2U2_0_2EOneD : Ball := ⟨(95763133818723624957857376269 / 1562500000000000000000000000000), (19834589363 / 50000000000000000000000000000000)⟩
def B2_4_2U2_0_2BinaryEntropy : Ball := ⟨(699893983112567810703138425289 / 2500000000000000000000000000000), (49057818971 / 100000000000000000000000000000000)⟩
def B2_4_2U2_0_2Leaf : Ball := ⟨(20593476631985786090186547073947 / 6250000000000000000000000000000), (168065355147 / 100000000000000000000000000000000)⟩
def B2_4_2U2_0_2Mass : Ball := ⟨(2327587120855560415853758489 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B2_4_2U2_1_1D : Ball := .exact (8433 / 200000)
def B2_4_2U2_1_1OneD : Ball := .exact (191567 / 200000)
def B2_4_2U2_1_1EDLogWitness : LogWitness := ⟨-5, 8433, 6250⟩
def B2_4_2U2_1_1EDLog : Ball := ⟨(-316616478595553215892035736909523 / 100000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B2_4_2U2_1_1ED : Ball := ⟨(1335013381998150134808768684679 / 10000000000000000000000000000000), (2678635817 / 50000000000000000000000000000000)⟩
def B2_4_2U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 191567, 100000⟩
def B2_4_2U2_1_1EOneDLog : Ball := ⟨(-4307974966568354882089913298341 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_4_2U2_1_1EOneD : Ball := ⟨(1031582300525750049621648026029 / 25000000000000000000000000000000), (10141472539 / 25000000000000000000000000000000)⟩
def B2_4_2U2_1_1BinaryEntropy : Ball := ⟨(20399118108915510943732037385873 / 100000000000000000000000000000000), (23854459501 / 50000000000000000000000000000000)⟩
def B2_4_2U2_1_1Leaf : Ball := ⟨(157550693764520845345323845072531 / 50000000000000000000000000000000), (62188153141 / 50000000000000000000000000000000)⟩
def B2_4_2U2_1_1Mass : Ball := ⟨(27772520692964670763404186047 / 5000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def B2_4_2U2_2_0D : Ball := .exact (3277 / 31250)
def B2_4_2U2_2_0OneD : Ball := .exact (27973 / 31250)
def B2_4_2U2_2_0EDLogWitness : LogWitness := ⟨-4, 26216, 15625⟩
def B2_4_2U2_2_0EDLog : Ball := ⟨(-56377275161643324031409595775453 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B2_4_2U2_2_0ED : Ball := ⟨(5911946582550565531229735851397 / 25000000000000000000000000000000), (5551453937 / 50000000000000000000000000000000)⟩
def B2_4_2U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 27973, 15625⟩
def B2_4_2U2_2_0EOneDLog : Ball := ⟨(-2769490423601434424009732717579 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_4_2U2_2_0EOneD : Ball := ⟨(9916282319283574418281504423531 / 100000000000000000000000000000000), (37910484217 / 100000000000000000000000000000000)⟩
def B2_4_2U2_2_0BinaryEntropy : Ball := ⟨(40832687243709647035873308745149 / 100000000000000000000000000000000), (53454555241 / 100000000000000000000000000000000)⟩
def B2_4_2U2_2_0Leaf : Ball := ⟨(82241462570157955404899575418567 / 25000000000000000000000000000000), (41796501973 / 25000000000000000000000000000000)⟩
def B2_4_2U2_2_0Mass : Ball := ⟨(2052429189538757016962171971651 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
def B2_4_2Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B2_4_2U0_2_2Leaf
  | 0, 3, 1 => B2_4_2U0_3_1Leaf
  | 0, 4, 0 => B2_4_2U0_4_0Leaf
  | 1, 1, 2 => B2_4_2U1_1_2Leaf
  | 1, 2, 1 => B2_4_2U1_2_1Leaf
  | 1, 3, 0 => B2_4_2U1_3_0Leaf
  | 2, 0, 2 => B2_4_2U2_0_2Leaf
  | 2, 1, 1 => B2_4_2U2_1_1Leaf
  | 2, 2, 0 => B2_4_2U2_2_0Leaf
  | _, _, _ => (.exact 0)
def B2_4_2Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B2_4_2U0_2_2Mass
  | 0, 3, 1 => B2_4_2U0_3_1Mass
  | 0, 4, 0 => B2_4_2U0_4_0Mass
  | 1, 1, 2 => B2_4_2U1_1_2Mass
  | 1, 2, 1 => B2_4_2U1_2_1Mass
  | 1, 3, 0 => B2_4_2U1_3_0Mass
  | 2, 0, 2 => B2_4_2U2_0_2Mass
  | 2, 1, 1 => B2_4_2U2_1_1Mass
  | 2, 2, 0 => B2_4_2U2_2_0Mass
  | _, _, _ => (.exact 0)
def B2_4_2Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B2_4_2U0_2_2BinaryEntropy
  | 1, 1, 2 => B2_4_2U1_1_2BinaryEntropy
  | 1, 2, 1 => B2_4_2U1_2_1BinaryEntropy
  | 2, 0, 2 => B2_4_2U2_0_2BinaryEntropy
  | 2, 1, 1 => B2_4_2U2_1_1BinaryEntropy
  | 2, 2, 0 => B2_4_2U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
def B2_4_2S2 : Ball := ⟨(44625677478615700179775906702917 / 100000000000000000000000000000000), (19080272089 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_5_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B2_5_1U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_5_1U0_3_1Mass : Ball := ⟨(8730128534988305962655873559 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B2_5_1U0_4_0Leaf : Ball := ⟨0, 0⟩
def B2_5_1U0_4_0Mass : Ball := ⟨(348255140010022353957739057 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B2_5_1U1_2_1D : Ball := .exact (3587 / 1000000)
def B2_5_1U1_2_1OneD : Ball := .exact (996413 / 1000000)
def B2_5_1U1_2_1EDLogWitness : LogWitness := ⟨-9, 28696, 15625⟩
def B2_5_1U1_2_1EDLog : Ball := ⟨(-563043908043199152811645612664621 / 100000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
def B2_5_1U1_2_1ED : Ball := ⟨(504909624537738840283843203157 / 25000000000000000000000000000000), (189894199 / 25000000000000000000000000000000)⟩
def B2_5_1U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 996413, 500000⟩
def B2_5_1U1_2_1EOneDLog : Ball := ⟨(-17967243550669688953494441141 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_5_1U1_2_1EOneD : Ball := ⟨(358055900961068735584365131613 / 100000000000000000000000000000000), (5274966501 / 12500000000000000000000000000000)⟩
def B2_5_1U1_2_1BinaryEntropy : Ball := ⟨(2626326292778876479207699037713 / 100000000000000000000000000000000), (10777806041 / 25000000000000000000000000000000)⟩
def B2_5_1U1_2_1Leaf : Ball := ⟨(321310277107629963115782498027451 / 100000000000000000000000000000000), (6341353453 / 5000000000000000000000000000000)⟩
def B2_5_1U1_2_1Mass : Ball := ⟨(30948584829331435076273891283 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def B2_5_1U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B2_5_1U1_3_0Mass : Ball := ⟨(30948584829331435076273891283 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def B2_5_1U2_1_1D : Ball := .exact (21083 / 500000)
def B2_5_1U2_1_1OneD : Ball := .exact (478917 / 500000)
def B2_5_1U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B2_5_1U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B2_5_1U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
def B2_5_1U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B2_5_1U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_5_1U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
def B2_5_1U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
def B2_5_1U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
def B2_5_1U2_1_1Mass : Ball := ⟨(348255140010022353957739057 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B2_5_1U2_2_0D : Ball := .exact (55043 / 500000)
def B2_5_1U2_2_0OneD : Ball := .exact (444957 / 500000)
def B2_5_1U2_2_0EDLogWitness : LogWitness := ⟨-4, 55043, 31250⟩
def B2_5_1U2_2_0EDLog : Ball := ⟨(-22064934004685379356673449299827 / 10000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B2_5_1U2_2_0ED : Ball := ⟨(1518150203024871669911720837263 / 6250000000000000000000000000000), (11655808631 / 100000000000000000000000000000000)⟩
def B2_5_1U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 444957, 250000⟩
def B2_5_1U2_2_0EOneDLog : Ball := ⟨(-583152250691689478453229215219 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B2_5_1U2_2_0EOneD : Ball := ⟨(1297388380055110376320567559581 / 12500000000000000000000000000000), (7537864783 / 20000000000000000000000000000000)⟩
def B2_5_1U2_2_0BinaryEntropy : Ball := ⟨(8460018068150208732480522660599 / 20000000000000000000000000000000), (54007455999 / 100000000000000000000000000000000)⟩
def B2_5_1U2_2_0Leaf : Ball := ⟨(328752356421927043814894573583359 / 100000000000000000000000000000000), (83537713871 / 50000000000000000000000000000000)⟩
def B2_5_1U2_2_0Mass : Ball := ⟨(8730128534988305962655873559 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B2_5_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B2_5_1U0_3_1Leaf
  | 0, 4, 0 => B2_5_1U0_4_0Leaf
  | 1, 2, 1 => B2_5_1U1_2_1Leaf
  | 1, 3, 0 => B2_5_1U1_3_0Leaf
  | 2, 1, 1 => B2_5_1U2_1_1Leaf
  | 2, 2, 0 => B2_5_1U2_2_0Leaf
  | _, _, _ => (.exact 0)
def B2_5_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B2_5_1U0_3_1Mass
  | 0, 4, 0 => B2_5_1U0_4_0Mass
  | 1, 2, 1 => B2_5_1U1_2_1Mass
  | 1, 3, 0 => B2_5_1U1_3_0Mass
  | 2, 1, 1 => B2_5_1U2_1_1Mass
  | 2, 2, 0 => B2_5_1U2_2_0Mass
  | _, _, _ => (.exact 0)
def B2_5_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B2_5_1U1_2_1BinaryEntropy
  | 2, 1, 1 => B2_5_1U2_1_1BinaryEntropy
  | 2, 2, 0 => B2_5_1U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
def B2_5_1S2 : Ball := ⟨(16906386274561049158059689213 / 3125000000000000000000000000000), (220586351 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_1_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B3_1_4Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(59283170615264302211580917627 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(768953964689050330179336197851 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(14976318486789256799246113282771 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 2, 0, 2 => ⟨1, 0⟩
  | 2, 1, 1 => ⟨(14976318486789256799246113282771 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(768953964689050330179336197851 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(59283170615264302211580917627 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_1_4Den : Ball := ⟨(59055708758080361211087519495901 / 25000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
def B3_1_4Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(8138014732824595179881072909 / 625000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(3169955708291305924669541513661 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(21166454967471157448510264727337 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(21166454967471157448510264727337 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(3169955708291305924669541513661 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(8138014732824595179881072909 / 625000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_1_4Law (u : Shape) : Ball := if u ∈ below (shape 3 1 4) then B3_1_4Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B3_1_4Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 1, 2 => (2207 / 1000000)
  | 2, 0, 2 => (5923 / 62500)
  | 2, 1, 1 => (21083 / 500000)
  | _, _, _ => 0
def B3_1_4LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B3_1_4Binary u else if i = 3 then B3_1_4Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B3_1_4Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B3_1_4LittleRat u w i)
  else .exact (littleLaw (shape 3 1 4) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B3_1_4U0_0_4Leaf : Ball := ⟨0, 0⟩
def B3_1_4U0_0_4Mass : Ball := ⟨(3743589784293194240021197981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B3_1_4U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_1_4U0_1_3Mass : Ball := ⟨(194230381197626472204352679303 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def B3_1_4U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_1_4U1_0_3Mass : Ball := ⟨(23642963218565539071319859767 / 2500000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def B3_1_4U1_1_2D : Ball := .exact (2207 / 1000000)
def B3_1_4U1_1_2OneD : Ball := .exact (997793 / 1000000)
def B3_1_4U1_1_2EDLogWitness : LogWitness := ⟨-9, 17656, 15625⟩
def B3_1_4U1_1_2EDLog : Ball := ⟨(-305806057585376885208270506013229 / 50000000000000000000000000000000), (211758236829 / 100000000000000000000000000000000)⟩
def B3_1_4U1_1_2ED : Ball := ⟨(674913969090926785654653006771 / 50000000000000000000000000000000), (46735043 / 10000000000000000000000000000000)⟩
def B3_1_4U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 997793, 500000⟩
def B3_1_4U1_1_2EOneDLog : Ball := ⟨(-55235975344075793717215518041 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_1_4U1_1_2EOneD : Ball := ⟨(220456278185965673761926493571 / 100000000000000000000000000000000), (42258177281 / 100000000000000000000000000000000)⟩
def B3_1_4U1_1_2BinaryEntropy : Ball := ⟨(68930471964695966994384623767 / 4000000000000000000000000000000), (42818997797 / 100000000000000000000000000000000)⟩
def B3_1_4U1_1_2Leaf : Ball := ⟨(80383094884886467241869350690683 / 25000000000000000000000000000000), (12691473697 / 10000000000000000000000000000000)⟩
def B3_1_4U1_1_2Mass : Ball := ⟨(98668120771057680000923112311 / 1562500000000000000000000000000), (3 / 4000000000000000000000000000000)⟩
def B3_1_4U2_0_2D : Ball := .exact (5923 / 62500)
def B3_1_4U2_0_2OneD : Ball := .exact (56577 / 62500)
def B3_1_4U2_0_2EDLogWitness : LogWitness := ⟨-4, 23692, 15625⟩
def B3_1_4U2_0_2EDLog : Ball := ⟨(-235632347944752769756850307028051 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B3_1_4U2_0_2ED : Ball := ⟨(11165203175014165242158594948217 / 50000000000000000000000000000000), (2006790459 / 20000000000000000000000000000000)⟩
def B3_1_4U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 56577, 31250⟩
def B3_1_4U2_0_2EOneDLog : Ball := ⟨(-9956401454401802915036069658881 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_1_4U2_0_2EOneD : Ball := ⟨(1126606650171381607047991426181 / 12500000000000000000000000000000), (38338066449 / 100000000000000000000000000000000)⟩
def B3_1_4U2_0_2BinaryEntropy : Ball := ⟨(9478019188032468262246586216219 / 25000000000000000000000000000000), (26192799831 / 50000000000000000000000000000000)⟩
def B3_1_4U2_0_2Leaf : Ball := ⟨(329295016821838983109105190268493 / 100000000000000000000000000000000), (5231243719 / 3125000000000000000000000000000)⟩
def B3_1_4U2_0_2Mass : Ball := ⟨(98668120771057680000923112311 / 1562500000000000000000000000000), (3 / 4000000000000000000000000000000)⟩
def B3_1_4U2_1_1D : Ball := .exact (21083 / 500000)
def B3_1_4U2_1_1OneD : Ball := .exact (478917 / 500000)
def B3_1_4U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B3_1_4U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B3_1_4U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
def B3_1_4U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B3_1_4U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_1_4U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
def B3_1_4U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
def B3_1_4U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
def B3_1_4U2_1_1Mass : Ball := ⟨(23642963218565539071319859767 / 2500000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
def B3_1_4U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_1_4U3_0_1Mass : Ball := ⟨(194230381197626472204352679303 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def B3_1_4U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_1_4U3_1_0Mass : Ball := ⟨(3743589784293194240021197981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B3_1_4Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B3_1_4U0_0_4Leaf
  | 0, 1, 3 => B3_1_4U0_1_3Leaf
  | 1, 0, 3 => B3_1_4U1_0_3Leaf
  | 1, 1, 2 => B3_1_4U1_1_2Leaf
  | 2, 0, 2 => B3_1_4U2_0_2Leaf
  | 2, 1, 1 => B3_1_4U2_1_1Leaf
  | 3, 0, 1 => B3_1_4U3_0_1Leaf
  | 3, 1, 0 => B3_1_4U3_1_0Leaf
  | _, _, _ => (.exact 0)
def B3_1_4Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B3_1_4U0_0_4Mass
  | 0, 1, 3 => B3_1_4U0_1_3Mass
  | 1, 0, 3 => B3_1_4U1_0_3Mass
  | 1, 1, 2 => B3_1_4U1_1_2Mass
  | 2, 0, 2 => B3_1_4U2_0_2Mass
  | 2, 1, 1 => B3_1_4U2_1_1Mass
  | 3, 0, 1 => B3_1_4U3_0_1Mass
  | 3, 1, 0 => B3_1_4U3_1_0Mass
  | _, _, _ => (.exact 0)
def B3_1_4Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B3_1_4U1_1_2BinaryEntropy
  | 2, 0, 2 => B3_1_4U2_0_2BinaryEntropy
  | 2, 1, 1 => B3_1_4U2_1_1BinaryEntropy
  | _, _, _ => (.exact 0)
def B3_1_4S2 : Ball := ⟨(23579419149144914744355152585039 / 50000000000000000000000000000000), (2089477031 / 10000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_2_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B3_2_3U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_2_3U0_1_3Mass : Ball := ⟨(3000961201670361542477883491 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B3_2_3U0_2_2D : Ball := .exact (20837 / 200000)
def B3_2_3U0_2_2OneD : Ball := .exact (179163 / 200000)
def B3_2_3U0_2_2EDLogWitness : LogWitness := ⟨-4, 20837, 12500⟩
def B3_2_3U0_2_2EDLog : Ball := ⟨(-226158711395997353564112106926423 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B3_2_3U0_2_2ED : Ball := ⟨(23562345346791984281077019860129 / 100000000000000000000000000000000), (11031015953 / 100000000000000000000000000000000)⟩
def B3_2_3U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 179163, 100000⟩
def B3_2_3U0_2_2EOneDLog : Ball := ⟨(-11002136054002092463393093233409 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_2_3U0_2_2EOneD : Ball := ⟨(4927939254607942230047241907443 / 50000000000000000000000000000000), (18969620493 / 50000000000000000000000000000000)⟩
def B3_2_3U0_2_2BinaryEntropy : Ball := ⟨(10159944439167914736833733635741 / 25000000000000000000000000000000), (53382663321 / 100000000000000000000000000000000)⟩
def B3_2_3U0_2_2Leaf : Ball := ⟨(328991502462102384361930710537671 / 100000000000000000000000000000000), (167200386277 / 100000000000000000000000000000000)⟩
def B3_2_3U0_2_2Mass : Ball := ⟨(541968814941377438344242143929 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def B3_2_3U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_2_3U1_0_3Mass : Ball := ⟨(539050071041767176960078266569 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def B3_2_3U1_1_2D : Ball := .exact (947 / 200000)
def B3_2_3U1_1_2OneD : Ball := .exact (199053 / 200000)
def B3_2_3U1_1_2EDLogWitness : LogWitness := ⟨-8, 3788, 3125⟩
def B3_2_3U1_1_2EDLog : Ball := ⟨(-267638677617204774276902959196961 / 50000000000000000000000000000000), (95291206573 / 50000000000000000000000000000000)⟩
def B3_2_3U1_1_2ED : Ball := ⟨(506907655406985842480454204719 / 20000000000000000000000000000000), (902407727 / 100000000000000000000000000000000)⟩
def B3_2_3U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 199053, 100000⟩
def B3_2_3U1_1_2EOneDLog : Ball := ⟨(-474624562523299173208176196821 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_2_3U1_1_2EOneD : Ball := ⟨(472377215219751351623035482529 / 100000000000000000000000000000000), (10537778079 / 25000000000000000000000000000000)⟩
def B3_2_3U1_1_2BinaryEntropy : Ball := ⟨(3335120682249814668034365825217 / 100000000000000000000000000000000), (21627027547 / 50000000000000000000000000000000)⟩
def B3_2_3U1_1_2Leaf : Ball := ⟨(501758615055128950613716142031 / 156250000000000000000000000000), (126754139523 / 100000000000000000000000000000000)⟩
def B3_2_3U1_1_2Mass : Ball := ⟨(14632618547294745801274531434457 / 100000000000000000000000000000000), (153 / 100000000000000000000000000000000)⟩
def B3_2_3U1_2_1D : Ball := .exact (38889 / 1000000)
def B3_2_3U1_2_1OneD : Ball := .exact (961111 / 1000000)
def B3_2_3U1_2_1EDLogWitness : LogWitness := ⟨-5, 38889, 31250⟩
def B3_2_3U1_2_1EDLog : Ball := ⟨(-40588048058701519414271962400259 / 12500000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B3_2_3U1_2_1ED : Ball := ⟨(12627428807638747108012978766269 / 100000000000000000000000000000000), (1235259911 / 25000000000000000000000000000000)⟩
def B3_2_3U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 961111, 500000⟩
def B3_2_3U1_2_1EOneDLog : Ball := ⟨(-1983268599968726397978668862597 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_2_3U1_2_1EOneD : Ball := ⟨(3812282534769085194175352818399 / 100000000000000000000000000000000), (5088079269 / 12500000000000000000000000000000)⟩
def B3_2_3U1_2_1BinaryEntropy : Ball := ⟨(9567645706443701807990502419601 / 50000000000000000000000000000000), (47292687011 / 100000000000000000000000000000000)⟩
def B3_2_3U1_2_1Leaf : Ball := ⟨(315628639389155101973366898777513 / 100000000000000000000000000000000), (124584422277 / 100000000000000000000000000000000)⟩
def B3_2_3U1_2_1Mass : Ball := ⟨(3774266288822559599228366594839 / 50000000000000000000000000000000), (89 / 100000000000000000000000000000000)⟩
def B3_2_3U2_0_2D : Ball := .exact (22013 / 200000)
def B3_2_3U2_0_2OneD : Ball := .exact (177987 / 200000)
def B3_2_3U2_0_2EDLogWitness : LogWitness := ⟨-4, 22013, 12500⟩
def B3_2_3U2_0_2EDLog : Ball := ⟨(-27583552232710530620549709460953 / 12500000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B3_2_3U2_0_2ED : Ball := ⟨(12143934705973138211003215087279 / 50000000000000000000000000000000), (11653585169 / 100000000000000000000000000000000)⟩
def B3_2_3U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 177987, 100000⟩
def B3_2_3U2_0_2EOneDLog : Ball := ⟨(-11660685263090779968348502269377 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_2_3U2_0_2EOneD : Ball := ⟨(5188625969804346635566112183549 / 50000000000000000000000000000000), (37690213299 / 100000000000000000000000000000000)⟩
def B3_2_3U2_0_2BinaryEntropy : Ball := ⟨(42294245794388007741239417784741 / 100000000000000000000000000000000), (6750654067 / 12500000000000000000000000000000)⟩
def B3_2_3U2_0_2Leaf : Ball := ⟨(3287532715147962311153047012527 / 1000000000000000000000000000000), (167075872433 / 100000000000000000000000000000000)⟩
def B3_2_3U2_0_2Mass : Ball := ⟨(3774266288822559599228366594839 / 50000000000000000000000000000000), (89 / 100000000000000000000000000000000)⟩
def B3_2_3U2_1_1D : Ball := .exact (21083 / 500000)
def B3_2_3U2_1_1OneD : Ball := .exact (478917 / 500000)
def B3_2_3U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B3_2_3U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B3_2_3U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
def B3_2_3U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B3_2_3U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_2_3U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
def B3_2_3U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
def B3_2_3U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
def B3_2_3U2_1_1Mass : Ball := ⟨(14632618547294745801274531434457 / 100000000000000000000000000000000), (153 / 100000000000000000000000000000000)⟩
def B3_2_3U2_2_0D : Ball := .exact (25593 / 250000)
def B3_2_3U2_2_0OneD : Ball := .exact (224407 / 250000)
def B3_2_3U2_2_0EDLogWitness : LogWitness := ⟨-4, 25593, 15625⟩
def B3_2_3U2_2_0EDLog : Ball := ⟨(-113957102063378952030784463086693 / 50000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B3_2_3U2_2_0ED : Ball := ⟨(11666016452432230077295467055111 / 50000000000000000000000000000000), (10839057111 / 100000000000000000000000000000000)⟩
def B3_2_3U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 224407, 125000⟩
def B3_2_3U2_2_0EOneDLog : Ball := ⟨(-5399977520216846740471713413351 / 50000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def B3_2_3U2_2_0EOneD : Ball := ⟨(9694342043034415411912286335599 / 100000000000000000000000000000000), (19008012261 / 50000000000000000000000000000000)⟩
def B3_2_3U2_2_0BinaryEntropy : Ball := ⟨(40122261264727147688069307164769 / 100000000000000000000000000000000), (26595352239 / 50000000000000000000000000000000)⟩
def B3_2_3U2_2_0Leaf : Ball := ⟨(41132196019650809737311914794403 / 12500000000000000000000000000000), (41809694511 / 25000000000000000000000000000000)⟩
def B3_2_3U2_2_0Mass : Ball := ⟨(539050071041767176960078266569 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def B3_2_3U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_2_3U3_0_1Mass : Ball := ⟨(541968814941377438344242143929 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def B3_2_3U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_2_3U3_1_0Mass : Ball := ⟨(3000961201670361542477883491 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B3_2_3Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B3_2_3U0_1_3Leaf
  | 0, 2, 2 => B3_2_3U0_2_2Leaf
  | 1, 0, 3 => B3_2_3U1_0_3Leaf
  | 1, 1, 2 => B3_2_3U1_1_2Leaf
  | 1, 2, 1 => B3_2_3U1_2_1Leaf
  | 2, 0, 2 => B3_2_3U2_0_2Leaf
  | 2, 1, 1 => B3_2_3U2_1_1Leaf
  | 2, 2, 0 => B3_2_3U2_2_0Leaf
  | 3, 0, 1 => B3_2_3U3_0_1Leaf
  | 3, 1, 0 => B3_2_3U3_1_0Leaf
  | _, _, _ => (.exact 0)
def B3_2_3Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B3_2_3U0_1_3Mass
  | 0, 2, 2 => B3_2_3U0_2_2Mass
  | 1, 0, 3 => B3_2_3U1_0_3Mass
  | 1, 1, 2 => B3_2_3U1_1_2Mass
  | 1, 2, 1 => B3_2_3U1_2_1Mass
  | 2, 0, 2 => B3_2_3U2_0_2Mass
  | 2, 1, 1 => B3_2_3U2_1_1Mass
  | 2, 2, 0 => B3_2_3U2_2_0Mass
  | 3, 0, 1 => B3_2_3U3_0_1Mass
  | 3, 1, 0 => B3_2_3U3_1_0Mass
  | _, _, _ => (.exact 0)
def B3_2_3Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B3_2_3U0_2_2BinaryEntropy
  | 1, 1, 2 => B3_2_3U1_1_2BinaryEntropy
  | 1, 2, 1 => B3_2_3U1_2_1BinaryEntropy
  | 2, 0, 2 => B3_2_3U2_0_2BinaryEntropy
  | 2, 1, 1 => B3_2_3U2_1_1BinaryEntropy
  | 2, 2, 0 => B3_2_3U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
def B3_2_3S2 : Ball := ⟨(148129463261957605657082804649427 / 100000000000000000000000000000000), (61613453871 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_3_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B3_3_2Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(3703099552999836306590899387483 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(514412495980659443970973192587 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(3223866655228713372649086705233 / 6250000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨1, 0⟩
  | 1, 3, 0 => ⟨(115502198241018120143768739669 / 3125000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(115502198241018120143768739669 / 3125000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 2, 2, 0 => ⟨(3223866655228713372649086705233 / 6250000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(514412495980659443970973192587 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(3703099552999836306590899387483 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_3_2Den : Ball := ⟨(79747724438176244778773929766603 / 25000000000000000000000000000000), (11 / 6250000000000000000000000000000)⟩
def B3_3_2Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(580439689515942428146703134263 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(16126243714309786405990264147 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(1617032550052504124618182388813 / 10000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(15674428440513710546549123442641 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(1158675802272554940366620316593 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(1158675802272554940366620316593 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(15674428440513710546549123442641 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(1617032550052504124618182388813 / 10000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(16126243714309786405990264147 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(580439689515942428146703134263 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_3_2Law (u : Shape) : Ball := if u ∈ below (shape 3 3 2) then B3_3_2Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B3_3_2Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (52157 / 500000)
  | 1, 1, 2 => (9739 / 250000)
  | 1, 2, 1 => (1219 / 250000)
  | 2, 0, 2 => (20479 / 200000)
  | 2, 1, 1 => (21083 / 500000)
  | 2, 2, 0 => (27517 / 250000)
  | _, _, _ => 0
def B3_3_2LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B3_3_2Binary u else if i = 3 then B3_3_2Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B3_3_2Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B3_3_2LittleRat u w i)
  else .exact (littleLaw (shape 3 3 2) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B3_3_2U0_2_2D : Ball := .exact (52157 / 500000)
def B3_3_2U0_2_2OneD : Ball := .exact (447843 / 500000)
def B3_3_2U0_2_2EDLogWitness : LogWitness := ⟨-4, 52157, 31250⟩
def B3_3_2U0_2_2EDLog : Ball := ⟨(-226034969779528798511424963779123 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def B3_3_2U0_2_2ED : Ball := ⟨(4715722367516353417584156734331 / 20000000000000000000000000000000), (11044674359 / 100000000000000000000000000000000)⟩
def B3_3_2U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 447843, 250000⟩
def B3_3_2U0_2_2EOneDLog : Ball := ⟨(-1101653738564778545821473882577 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_3_2U0_2_2EOneD : Ball := ⟨(9867358304801322365926526559899 / 100000000000000000000000000000000), (4741722203 / 12500000000000000000000000000000)⟩
def B3_3_2U0_2_2BinaryEntropy : Ball := ⟨(20338232820838051477251111695703 / 50000000000000000000000000000000), (53396321727 / 100000000000000000000000000000000)⟩
def B3_3_2U0_2_2Leaf : Ball := ⟨(328986666848966028579433299805169 / 100000000000000000000000000000000), (41799413649 / 25000000000000000000000000000000)⟩
def B3_3_2U0_2_2Mass : Ball := ⟨(257837301312875337408670808073 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def B3_3_2U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_3_2U0_3_1Mass : Ball := ⟨(7163443911078640424744493343 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B3_3_2U1_1_2D : Ball := .exact (9739 / 250000)
def B3_3_2U1_1_2OneD : Ball := .exact (240261 / 250000)
def B3_3_2U1_1_2EDLogWitness : LogWitness := ⟨-5, 19478, 15625⟩
def B3_3_2U1_1_2EDLog : Ball := ⟨(-324532247488318424096291773816019 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B3_3_2U1_1_2ED : Ball := ⟨(12642478233154932529095142340777 / 100000000000000000000000000000000), (197982093 / 4000000000000000000000000000000)⟩
def B3_3_2U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 240261, 125000⟩
def B3_3_2U1_1_2EOneDLog : Ball := ⟨(-198675427100083019722202722521 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_3_2U1_1_2EOneD : Ball := ⟨(3818716543239443712118091865249 / 100000000000000000000000000000000), (2543862287 / 6250000000000000000000000000000)⟩
def B3_3_2U1_1_2BinaryEntropy : Ball := ⟨(3832283786596739837715800582899 / 20000000000000000000000000000000), (47301199693 / 100000000000000000000000000000000)⟩
def B3_3_2U1_1_2Leaf : Ball := ⟨(15780892807757089675042853684627 / 5000000000000000000000000000000), (124580165937 / 100000000000000000000000000000000)⟩
def B3_3_2U1_1_2Mass : Ball := ⟨(897878186940305685491830221689 / 25000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
def B3_3_2U1_2_1D : Ball := .exact (1219 / 250000)
def B3_3_2U1_2_1OneD : Ball := .exact (248781 / 250000)
def B3_3_2U1_2_1EDLogWitness : LogWitness := ⟨-8, 19504, 15625⟩
def B3_3_2U1_2_1EDLog : Ball := ⟨(-133085751684077799008056524667789 / 25000000000000000000000000000000), (190582413147 / 100000000000000000000000000000000)⟩
def B3_3_2U1_2_1ED : Ball := ⟨(2595704500846253391853134457121 / 100000000000000000000000000000000), (929279847 / 100000000000000000000000000000000)⟩
def B3_3_2U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 248781, 125000⟩
def B3_3_2U1_2_1EOneDLog : Ball := ⟨(-244396323639087523862893819551 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_3_2U1_2_1EOneD : Ball := ⟨(243204647165023333096538349287 / 50000000000000000000000000000000), (21072570367 / 50000000000000000000000000000000)⟩
def B3_3_2U1_2_1BinaryEntropy : Ball := ⟨(213755772526083086932378340313 / 6250000000000000000000000000000), (21640463607 / 50000000000000000000000000000000)⟩
def B3_3_2U1_2_1Leaf : Ball := ⟨(160551410280358603788748230099313 / 50000000000000000000000000000000), (2534903643 / 2000000000000000000000000000000)⟩
def B3_3_2U1_2_1Mass : Ball := ⟨(6962742902874551343715804077263 / 100000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩
def B3_3_2U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_3_2U1_3_0Mass : Ball := ⟨(257347875542098689266630589041 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def B3_3_2U2_0_2D : Ball := .exact (20479 / 200000)
def B3_3_2U2_0_2OneD : Ball := .exact (179521 / 200000)
def B3_3_2U2_0_2EDLogWitness : LogWitness := ⟨-4, 20479, 12500⟩
def B3_3_2U2_0_2EDLog : Ball := ⟨(-45578347913877226878717459404093 / 20000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B3_3_2U2_0_2ED : Ball := ⟨(23334974673207293231231371278411 / 100000000000000000000000000000000), (10841492331 / 100000000000000000000000000000000)⟩
def B3_3_2U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 179521, 100000⟩
def B3_3_2U2_0_2EOneDLog : Ball := ⟨(-10802517381923768407763481952009 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_3_2U2_0_2EOneD : Ball := ⟨(9696393614601684141650540217533 / 100000000000000000000000000000000), (19007525217 / 50000000000000000000000000000000)⟩
def B3_3_2U2_0_2BinaryEntropy : Ball := ⟨(40128848843152537368659657848333 / 100000000000000000000000000000000), (26596569849 / 50000000000000000000000000000000)⟩
def B3_3_2U2_0_2Leaf : Ball := ⟨(82264188080308667679340626386903 / 25000000000000000000000000000000), (167238291001 / 100000000000000000000000000000000)⟩
def B3_3_2U2_0_2Mass : Ball := ⟨(257347875542098689266630589041 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def B3_3_2U2_1_1D : Ball := .exact (21083 / 500000)
def B3_3_2U2_1_1OneD : Ball := .exact (478917 / 500000)
def B3_3_2U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B3_3_2U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B3_3_2U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
def B3_3_2U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B3_3_2U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_3_2U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
def B3_3_2U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
def B3_3_2U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
def B3_3_2U2_1_1Mass : Ball := ⟨(6962742902874551343715804077263 / 100000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩
def B3_3_2U2_2_0D : Ball := .exact (27517 / 250000)
def B3_3_2U2_2_0OneD : Ball := .exact (222483 / 250000)
def B3_3_2U2_2_0EDLogWitness : LogWitness := ⟨-4, 27517, 15625⟩
def B3_3_2U2_2_0EDLog : Ball := ⟨(-220665692236720985729493316733689 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B3_3_2U2_2_0ED : Ball := ⟨(6072057853277851364318467596561 / 25000000000000000000000000000000), (11653902807 / 100000000000000000000000000000000)⟩
def B3_3_2U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 222483, 125000⟩
def B3_3_2U2_2_0EOneDLog : Ball := ⟨(-5830511183465280787305887930417 / 50000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def B3_3_2U2_2_0EOneD : Ball := ⟨(1297189619630906065402175864423 / 12500000000000000000000000000000), (9422521561 / 25000000000000000000000000000000)⟩
def B3_3_2U2_2_0BinaryEntropy : Ball := ⟨(10573770189286465003046216428573 / 25000000000000000000000000000000), (27002775087 / 50000000000000000000000000000000)⟩
def B3_3_2U2_2_0Leaf : Ball := ⟨(2054707130092541393287658679543 / 625000000000000000000000000000), (83537904453 / 50000000000000000000000000000000)⟩
def B3_3_2U2_2_0Mass : Ball := ⟨(897878186940305685491830221689 / 25000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
def B3_3_2U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_3_2U3_0_1Mass : Ball := ⟨(7163443911078640424744493343 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B3_3_2U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_3_2U3_1_0Mass : Ball := ⟨(257837301312875337408670808073 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def B3_3_2Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B3_3_2U0_2_2Leaf
  | 0, 3, 1 => B3_3_2U0_3_1Leaf
  | 1, 1, 2 => B3_3_2U1_1_2Leaf
  | 1, 2, 1 => B3_3_2U1_2_1Leaf
  | 1, 3, 0 => B3_3_2U1_3_0Leaf
  | 2, 0, 2 => B3_3_2U2_0_2Leaf
  | 2, 1, 1 => B3_3_2U2_1_1Leaf
  | 2, 2, 0 => B3_3_2U2_2_0Leaf
  | 3, 0, 1 => B3_3_2U3_0_1Leaf
  | 3, 1, 0 => B3_3_2U3_1_0Leaf
  | _, _, _ => (.exact 0)
def B3_3_2Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B3_3_2U0_2_2Mass
  | 0, 3, 1 => B3_3_2U0_3_1Mass
  | 1, 1, 2 => B3_3_2U1_1_2Mass
  | 1, 2, 1 => B3_3_2U1_2_1Mass
  | 1, 3, 0 => B3_3_2U1_3_0Mass
  | 2, 0, 2 => B3_3_2U2_0_2Mass
  | 2, 1, 1 => B3_3_2U2_1_1Mass
  | 2, 2, 0 => B3_3_2U2_2_0Mass
  | 3, 0, 1 => B3_3_2U3_0_1Mass
  | 3, 1, 0 => B3_3_2U3_1_0Mass
  | _, _, _ => (.exact 0)
def B3_3_2Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B3_3_2U0_2_2BinaryEntropy
  | 1, 1, 2 => B3_3_2U1_1_2BinaryEntropy
  | 1, 2, 1 => B3_3_2U1_2_1BinaryEntropy
  | 2, 0, 2 => B3_3_2U2_0_2BinaryEntropy
  | 2, 1, 1 => B3_3_2U2_1_1BinaryEntropy
  | 2, 2, 0 => B3_3_2U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
def B3_3_2S2 : Ball := ⟨(70486191644416634713605546718153 / 100000000000000000000000000000000), (14659169619 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_4_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B3_4_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(38409269753660833180056353669 / 1250000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(15831277194442435596433763391 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨1, 0⟩
  | 1, 3, 0 => ⟨(7793756819393451250565121368561 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(7793756819393451250565121368561 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨1, 0⟩
  | 3, 0, 1 => ⟨(15831277194442435596433763391 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(38409269753660833180056353669 / 1250000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_4_1Den : Ball := ⟨(118739411605051981333516919847597 / 50000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
def B3_4_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(80868831238226048857523902691 / 6250000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(520812135624222942175390833 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(21054508913312090338702518135663 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(3281874448442126136287678136153 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(3281874448442126136287678136153 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(21054508913312090338702518135663 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(520812135624222942175390833 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(80868831238226048857523902691 / 6250000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_4_1Law (u : Shape) : Ball := if u ∈ below (shape 3 4 1) then B3_4_1Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B3_4_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 2, 1 => (2953 / 1000000)
  | 2, 1, 1 => (21083 / 500000)
  | 2, 2, 0 => (12 / 125)
  | _, _, _ => 0
def B3_4_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B3_4_1Binary u else if i = 3 then B3_4_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B3_4_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B3_4_1LittleRat u w i)
  else .exact (littleLaw (shape 3 4 1) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B3_4_1U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_4_1U0_3_1Mass : Ball := ⟨(14993443283684725396667285643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B3_4_1U0_4_0Leaf : Ball := ⟨0, 0⟩
def B3_4_1U0_4_0Mass : Ball := ⟨(386243604482581519325542989 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B3_4_1U1_2_1D : Ball := .exact (2953 / 1000000)
def B3_4_1U1_2_1OneD : Ball := .exact (997047 / 1000000)
def B3_4_1U1_2_1EDLogWitness : LogWitness := ⟨-9, 23624, 15625⟩
def B3_4_1U1_2_1EDLog : Ball := ⟨(-582493367622035143525726017920939 / 100000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
def B3_4_1U1_2_1ED : Ball := ⟨(1720102914587869778831468930921 / 100000000000000000000000000000000), (312661037 / 50000000000000000000000000000000)⟩
def B3_4_1U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 997047, 500000⟩
def B3_4_1U1_2_1EOneDLog : Ball := ⟨(-295736870714792481357949825269 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_4_1U1_2_1EOneD : Ball := ⟨(58972711947114339832099959887 / 20000000000000000000000000000000), (5278322869 / 12500000000000000000000000000000)⟩
def B3_4_1U1_2_1BinaryEntropy : Ball := ⟨(1109826418371396663931438659717 / 50000000000000000000000000000000), (21488484721 / 50000000000000000000000000000000)⟩
def B3_4_1U1_2_1Leaf : Ball := ⟨(80353078867819571269883046536241 / 25000000000000000000000000000000), (126867345477 / 100000000000000000000000000000000)⟩
def B3_4_1U1_2_1Mass : Ball := ⟨(487950024168829794196947866917 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def B3_4_1U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_4_1U1_3_0Mass : Ball := ⟨(19014819141945082814976681729 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B3_4_1U2_1_1D : Ball := .exact (21083 / 500000)
def B3_4_1U2_1_1OneD : Ball := .exact (478917 / 500000)
def B3_4_1U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B3_4_1U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B3_4_1U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
def B3_4_1U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B3_4_1U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B3_4_1U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
def B3_4_1U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
def B3_4_1U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
def B3_4_1U2_1_1Mass : Ball := ⟨(19014819141945082814976681729 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B3_4_1U2_2_0D : Ball := .exact (12 / 125)
def B3_4_1U2_2_0OneD : Ball := .exact (113 / 125)
def B3_4_1U2_2_0EDLogWitness : LogWitness := ⟨-4, 192, 125⟩
def B3_4_1U2_2_0EDLog : Ball := ⟨(-117170354375715040678628387801009 / 50000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B3_4_1U2_2_0ED : Ball := ⟨(11248354020068643905148325228897 / 50000000000000000000000000000000), (10164395369 / 100000000000000000000000000000000)⟩
def B3_4_1U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 226, 125⟩
def B3_4_1U2_2_0EOneDLog : Ball := ⟨(-2523147964749013880503657881131 / 25000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def B3_4_1U2_2_0EOneD : Ball := ⟨(912370304053243419190122689817 / 10000000000000000000000000000000), (38285889219 / 100000000000000000000000000000000)⟩
def B3_4_1U2_2_0BinaryEntropy : Ball := ⟨(9568656003511299243150825972199 / 25000000000000000000000000000000), (3282252671 / 6250000000000000000000000000000)⟩
def B3_4_1U2_2_0Leaf : Ball := ⟨(41157624822766318087552565285851 / 12500000000000000000000000000000), (167373710393 / 100000000000000000000000000000000)⟩
def B3_4_1U2_2_0Mass : Ball := ⟨(487950024168829794196947866917 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def B3_4_1U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_4_1U3_0_1Mass : Ball := ⟨(386243604482581519325542989 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B3_4_1U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B3_4_1U3_1_0Mass : Ball := ⟨(14993443283684725396667285643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B3_4_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B3_4_1U0_3_1Leaf
  | 0, 4, 0 => B3_4_1U0_4_0Leaf
  | 1, 2, 1 => B3_4_1U1_2_1Leaf
  | 1, 3, 0 => B3_4_1U1_3_0Leaf
  | 2, 1, 1 => B3_4_1U2_1_1Leaf
  | 2, 2, 0 => B3_4_1U2_2_0Leaf
  | 3, 0, 1 => B3_4_1U3_0_1Leaf
  | 3, 1, 0 => B3_4_1U3_1_0Leaf
  | _, _, _ => (.exact 0)
def B3_4_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B3_4_1U0_3_1Mass
  | 0, 4, 0 => B3_4_1U0_4_0Mass
  | 1, 2, 1 => B3_4_1U1_2_1Mass
  | 1, 3, 0 => B3_4_1U1_3_0Mass
  | 2, 1, 1 => B3_4_1U2_1_1Mass
  | 2, 2, 0 => B3_4_1U2_2_0Mass
  | 3, 0, 1 => B3_4_1U3_0_1Mass
  | 3, 1, 0 => B3_4_1U3_1_0Mass
  | _, _, _ => (.exact 0)
def B3_4_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B3_4_1U1_2_1BinaryEntropy
  | 2, 1, 1 => B3_4_1U2_1_1BinaryEntropy
  | 2, 2, 0 => B3_4_1U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
def B3_4_1S2 : Ball := ⟨(1829846989875417228160241011411 / 50000000000000000000000000000000), (810250403 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal4_1_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B4_1_3Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => ⟨(1986046562779191655644056193 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(3067522357202958037026075746671 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(15612473623271752962591099629173 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨1, 0⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 3, 0, 1 => ⟨(15612473623271752962591099629173 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(3067522357202958037026075746671 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(1986046562779191655644056193 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B4_1_3Den : Ball := ⟨(29689859460746469666460734405891 / 12500000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
def B4_1_3Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => ⟨(33446547050938077933247687037 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(2066377148910784129369940729 / 160000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(3286575346523891131058813407701 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(2631369815114502473693307033871 / 6250000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(2631369815114502473693307033871 / 6250000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(3286575346523891131058813407701 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(2066377148910784129369940729 / 160000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(33446547050938077933247687037 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B4_1_3Law (u : Shape) : Ball := if u ∈ below (shape 4 1 3) then B4_1_3Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B4_1_3Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 1, 2 => (41863 / 1000000)
  | 2, 0, 2 => (95723 / 1000000)
  | 2, 1, 1 => (3031 / 1000000)
  | _, _, _ => 0
def B4_1_3LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B4_1_3Binary u else if i = 3 then B4_1_3Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B4_1_3Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B4_1_3LittleRat u w i)
  else .exact (littleLaw (shape 4 1 3) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B4_1_3U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B4_1_3U0_1_3Mass : Ball := ⟨(1534436237026567284168100653 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B4_1_3U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B4_1_3U1_0_3Mass : Ball := ⟨(59249837730323733309452320717 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B4_1_3U1_1_2D : Ball := .exact (41863 / 1000000)
def B4_1_3U1_1_2OneD : Ball := .exact (958137 / 1000000)
def B4_1_3U1_1_2EDLogWitness : LogWitness := ⟨-5, 41863, 31250⟩
def B4_1_3U1_1_2EDLog : Ball := ⟨(-317335289706930149883438220903761 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B4_1_3U1_1_2ED : Ball := ⟨(6642303616500608432285187120847 / 50000000000000000000000000000000), (2659450521 / 50000000000000000000000000000000)⟩
def B4_1_3U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 958137, 500000⟩
def B4_1_3U1_1_2EOneDLog : Ball := ⟨(-855290099452987341985735013837 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_1_3U1_1_2EOneD : Ball := ⟨(1024356362524483666110232736191 / 25000000000000000000000000000000), (40578680353 / 100000000000000000000000000000000)⟩
def B4_1_3U1_1_2BinaryEntropy : Ball := ⟨(5070938681269312644456165804281 / 25000000000000000000000000000000), (47670548409 / 100000000000000000000000000000000)⟩
def B4_1_3U1_1_2Leaf : Ball := ⟨(19696874534624825032622539566587 / 6250000000000000000000000000000), (62197745789 / 50000000000000000000000000000000)⟩
def B4_1_3U1_1_2Mass : Ball := ⟨(301558202689444043590391085003 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def B4_1_3U2_0_2D : Ball := .exact (95723 / 1000000)
def B4_1_3U2_0_2OneD : Ball := .exact (904277 / 1000000)
def B4_1_3U2_0_2EDLogWitness : LogWitness := ⟨-4, 95723, 62500⟩
def B4_1_3U2_0_2EDLog : Ball := ⟨(-234629667502064329567169639454029 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B4_1_3U2_0_2ED : Ball := ⟨(11229727831150051909579089698729 / 50000000000000000000000000000000), (10135066853 / 100000000000000000000000000000000)⟩
def B4_1_3U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 904277, 500000⟩
def B4_1_3U2_0_2EOneDLog : Ball := ⟨(-10061954959653018265030300181801 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_1_3U2_0_2EOneD : Ball := ⟨(4549397222525076198823402378749 / 50000000000000000000000000000000), (19148810313 / 50000000000000000000000000000000)⟩
def B4_1_3U2_0_2BinaryEntropy : Ball := ⟨(38193262863824220702139553363313 / 100000000000000000000000000000000), (2624335711 / 5000000000000000000000000000000)⟩
def B4_1_3U2_0_2Leaf : Ball := ⟨(82317200073064604397677413451807 / 25000000000000000000000000000000), (5230611753 / 3125000000000000000000000000000)⟩
def B4_1_3U2_0_2Mass : Ball := ⟨(965760487306589437428352637319 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def B4_1_3U2_1_1D : Ball := .exact (3031 / 1000000)
def B4_1_3U2_1_1OneD : Ball := .exact (996969 / 1000000)
def B4_1_3U2_1_1EDLogWitness : LogWitness := ⟨-9, 24248, 15625⟩
def B4_1_3U2_1_1EDLog : Ball := ⟨(-579886268090647095228230969209657 / 100000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
def B4_1_3U2_1_1ED : Ball := ⟨(878817639291375672818384033837 / 50000000000000000000000000000000), (641839217 / 100000000000000000000000000000000)⟩
def B4_1_3U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 996969, 500000⟩
def B4_1_3U2_1_1EOneDLog : Ball := ⟨(-2371564674643973779035589817 / 781250000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_1_3U2_1_1EOneD : Ball := ⟨(151320093575368185248725308433 / 50000000000000000000000000000000), (42223279523 / 100000000000000000000000000000000)⟩
def B4_1_3U2_1_1BinaryEntropy : Ball := ⟨(567592094040301784854645420669 / 25000000000000000000000000000000), (5374185823 / 12500000000000000000000000000000)⟩
def B4_1_3U2_1_1Leaf : Ball := ⟨(40174970231945162387076287528143 / 12500000000000000000000000000000), (63431195167 / 50000000000000000000000000000000)⟩
def B4_1_3U2_1_1Mass : Ball := ⟨(965760487306589437428352637319 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
def B4_1_3U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B4_1_3U3_0_1Mass : Ball := ⟨(301558202689444043590391085003 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def B4_1_3U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B4_1_3U3_1_0Mass : Ball := ⟨(59249837730323733309452320717 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B4_1_3U4_0_0Leaf : Ball := ⟨0, 0⟩
def B4_1_3U4_0_0Mass : Ball := ⟨(1534436237026567284168100653 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B4_1_3Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B4_1_3U0_1_3Leaf
  | 1, 0, 3 => B4_1_3U1_0_3Leaf
  | 1, 1, 2 => B4_1_3U1_1_2Leaf
  | 2, 0, 2 => B4_1_3U2_0_2Leaf
  | 2, 1, 1 => B4_1_3U2_1_1Leaf
  | 3, 0, 1 => B4_1_3U3_0_1Leaf
  | 3, 1, 0 => B4_1_3U3_1_0Leaf
  | 4, 0, 0 => B4_1_3U4_0_0Leaf
  | _, _, _ => (.exact 0)
def B4_1_3Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B4_1_3U0_1_3Mass
  | 1, 0, 3 => B4_1_3U1_0_3Mass
  | 1, 1, 2 => B4_1_3U1_1_2Mass
  | 2, 0, 2 => B4_1_3U2_0_2Mass
  | 2, 1, 1 => B4_1_3U2_1_1Mass
  | 3, 0, 1 => B4_1_3U3_0_1Mass
  | 3, 1, 0 => B4_1_3U3_1_0Mass
  | 4, 0, 0 => B4_1_3U4_0_0Mass
  | _, _, _ => (.exact 0)
def B4_1_3Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B4_1_3U1_1_2BinaryEntropy
  | 2, 0, 2 => B4_1_3U2_0_2BinaryEntropy
  | 2, 1, 1 => B4_1_3U2_1_1BinaryEntropy
  | _, _, _ => (.exact 0)
def B4_1_3S2 : Ball := ⟨(14488912584849512791622540958653 / 100000000000000000000000000000000), (6415572889 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal4_2_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B4_2_2Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(59580328744584746699210039469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(3551332927065966816059043009887 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(7099825355927794995680046054547 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(26216007198693794473744704647899 / 100000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 2, 2, 0 => ⟨(26216007198693794473744704647899 / 100000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(7099825355927794995680046054547 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(3551332927065966816059043009887 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(59580328744584746699210039469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B4_2_2Den : Ball := ⟨(90478078737498107848242046761689 / 50000000000000000000000000000000), (51 / 25000000000000000000000000000000)⟩
def B4_2_2Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(1962537764185601435248786401077 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(980876453031008343288822515281 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(7243745547126854607846925140589 / 50000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(11052400912504742196751447679061 / 20000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(7243745547126854607846925140589 / 50000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(980876453031008343288822515281 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(1962537764185601435248786401077 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B4_2_2Law (u : Shape) : Ball := if u ∈ below (shape 4 2 2) then B4_2_2Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B4_2_2Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (63321 / 1000000)
  | 1, 1, 2 => (1051 / 25000)
  | 1, 2, 1 => (21087 / 500000)
  | 2, 0, 2 => (52331 / 500000)
  | 2, 1, 1 => (593 / 50000)
  | 2, 2, 0 => (52451 / 500000)
  | _, _, _ => 0
def B4_2_2LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B4_2_2Binary u else if i = 3 then B4_2_2Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B4_2_2Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B4_2_2LittleRat u w i)
  else .exact (littleLaw (shape 4 2 2) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B4_2_2U0_2_2D : Ball := .exact (63321 / 1000000)
def B4_2_2U0_2_2OneD : Ball := .exact (936679 / 1000000)
def B4_2_2U0_2_2EDLogWitness : LogWitness := ⟨-4, 63321, 62500⟩
def B4_2_2U0_2_2EDLog : Ball := ⟨(-275953825129554669064816416181401 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def B4_2_2U0_2_2ED : Ball := ⟨(8736836080514265599926620144511 / 50000000000000000000000000000000), (3352185829 / 50000000000000000000000000000000)⟩
def B4_2_2U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 936679, 500000⟩
def B4_2_2U0_2_2EOneDLog : Ball := ⟨(-6541463814935642164057959379121 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_2_2U0_2_2EOneD : Ball := ⟨(1531812946177525591646911333319 / 25000000000000000000000000000000), (2479368669 / 6250000000000000000000000000000)⟩
def B4_2_2U0_2_2BinaryEntropy : Ball := ⟨(13995000603881131630100869964719 / 50000000000000000000000000000000), (1962240761 / 4000000000000000000000000000000)⟩
def B4_2_2U0_2_2Leaf : Ball := ⟨(41186917510491800527041824835183 / 12500000000000000000000000000000), (33613143027 / 20000000000000000000000000000000)⟩
def B4_2_2U0_2_2Mass : Ball := ⟨(491331029136091495330612073 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B4_2_2U1_1_2D : Ball := .exact (1051 / 25000)
def B4_2_2U1_1_2OneD : Ball := .exact (23949 / 25000)
def B4_2_2U1_1_2EDLogWitness : LogWitness := ⟨-5, 4204, 3125⟩
def B4_2_2U1_1_2EDLog : Ball := ⟨(-7922834332433466689101770028001 / 2500000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B4_2_2U1_1_2ED : Ball := ⟨(6661519106710058792196768239543 / 50000000000000000000000000000000), (5341389767 / 100000000000000000000000000000000)⟩
def B4_2_2U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 23949, 12500⟩
def B4_2_2U1_1_2EOneDLog : Ball := ⟨(-4294925553642923666670848622939 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_2_2U1_1_2EOneD : Ball := ⟨(4114366883367775155724006146831 / 100000000000000000000000000000000), (2535699007 / 6250000000000000000000000000000)⟩
def B4_2_2U1_1_2BinaryEntropy : Ball := ⟨(20351395843861902820907585661753 / 100000000000000000000000000000000), (9538607427 / 20000000000000000000000000000000)⟩
def B4_2_2U1_1_2Leaf : Ball := ⟨(157560752751473558472665099815977 / 50000000000000000000000000000000), (7774015451 / 6250000000000000000000000000000)⟩
def B4_2_2U1_1_2Mass : Ball := ⟨(58572354286272772622701551241 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def B4_2_2U1_2_1D : Ball := .exact (21087 / 500000)
def B4_2_2U1_2_1OneD : Ball := .exact (478913 / 500000)
def B4_2_2U1_2_1EDLogWitness : LogWitness := ⟨-5, 21087, 15625⟩
def B4_2_2U1_2_1EDLog : Ball := ⟨(-316595136156031375511358183062789 / 100000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B4_2_2U1_2_1ED : Ball := ⟨(1335208327224446723081602001249 / 10000000000000000000000000000000), (5358415129 / 100000000000000000000000000000000)⟩
def B4_2_2U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 478913, 250000⟩
def B4_2_2U1_2_1EOneDLog : Ball := ⟨(-861782918003896777682762665419 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_2_2U1_2_1EOneD : Ball := ⟨(2063595213050001087451924581919 / 50000000000000000000000000000000), (40565508991 / 100000000000000000000000000000000)⟩
def B4_2_2U1_2_1BinaryEntropy : Ball := ⟨(20402552617637982753656103120033 / 100000000000000000000000000000000), (47710062497 / 100000000000000000000000000000000)⟩
def B4_2_2U1_2_1Leaf : Ball := ⟨(157549969517460250000155274731003 / 50000000000000000000000000000000), (24875146907 / 20000000000000000000000000000000)⟩
def B4_2_2U1_2_1Mass : Ball := ⟨(58548930029721897108600768513 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def B4_2_2U2_0_2D : Ball := .exact (52331 / 500000)
def B4_2_2U2_0_2OneD : Ball := .exact (447669 / 500000)
def B4_2_2U2_0_2EDLogWitness : LogWitness := ⟨-4, 52331, 31250⟩
def B4_2_2U2_0_2EDLog : Ball := ⟨(-14106369804520244990198383124901 / 6250000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B4_2_2U2_0_2ED : Ball := ⟨(11811207011845583049313145396947 / 50000000000000000000000000000000), (2770380073 / 25000000000000000000000000000000)⟩
def B4_2_2U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 447669, 250000⟩
def B4_2_2U2_0_2EOneDLog : Ball := ⟨(-11055397836918052136994139561117 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_2_2U2_0_2EOneD : Ball := ⟨(9898317788510534964232058926371 / 100000000000000000000000000000000), (151676157 / 400000000000000000000000000000)⟩
def B4_2_2U2_0_2BinaryEntropy : Ball := ⟨(40775348833378200660280982551299 / 100000000000000000000000000000000), (53433167659 / 100000000000000000000000000000000)⟩
def B4_2_2U2_0_2Leaf : Ball := ⟨(328973533161962712899139846142051 / 100000000000000000000000000000000), (5224696419 / 3125000000000000000000000000000)⟩
def B4_2_2U2_0_2Mass : Ball := ⟨(86476446627153830691567188243 / 10000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def B4_2_2U2_1_1D : Ball := .exact (593 / 50000)
def B4_2_2U2_1_1OneD : Ball := .exact (49407 / 50000)
def B4_2_2U2_1_1EDLogWitness : LogWitness := ⟨-7, 4744, 3125⟩
def B4_2_2U2_1_1EDLog : Ball := ⟨(-55432298567656970726576300895367 / 12500000000000000000000000000000), (169406589463 / 100000000000000000000000000000000)⟩
def B4_2_2U2_1_1ED : Ball := ⟨(657427061012411672817194928619 / 12500000000000000000000000000000), (251145269 / 12500000000000000000000000000000)⟩
def B4_2_2U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 49407, 25000⟩
def B4_2_2U2_1_1EOneDLog : Ball := ⟨(-149136135849562572644784501963 / 12500000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_2_2U2_1_1EOneD : Ball := ⟨(589469525113547042132869431079 / 50000000000000000000000000000000), (41849356829 / 100000000000000000000000000000000)⟩
def B4_2_2U2_1_1BinaryEntropy : Ball := ⟨(7260428094470482603772135360687 / 100000000000000000000000000000000), (44360809519 / 100000000000000000000000000000000)⟩
def B4_2_2U2_1_1Leaf : Ball := ⟨(319978789122673231875875290147027 / 100000000000000000000000000000000), (31575376573 / 25000000000000000000000000000000)⟩
def B4_2_2U2_1_1Mass : Ball := ⟨(3298612407745390627125647993311 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
def B4_2_2U2_2_0D : Ball := .exact (52451 / 500000)
def B4_2_2U2_2_0OneD : Ball := .exact (447549 / 500000)
def B4_2_2U2_2_0EDLogWitness : LogWitness := ⟨-4, 52451, 31250⟩
def B4_2_2U2_2_0EDLog : Ball := ⟨(-225472869798470476592187191794959 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def B4_2_2U2_2_0ED : Ball := ⟨(946102199503965997418944831747 / 4000000000000000000000000000000), (11106931281 / 100000000000000000000000000000000)⟩
def B4_2_2U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 447549, 250000⟩
def B4_2_2U2_2_0EOneDLog : Ball := ⟨(-692637934343495837134511622293 / 6250000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_2_2U2_2_0EOneD : Ball := ⟨(495983063803995549461941667273 / 5000000000000000000000000000000), (7581774971 / 20000000000000000000000000000000)⟩
def B4_2_2U2_2_0BinaryEntropy : Ball := ⟨(40843468817188999209561100536501 / 100000000000000000000000000000000), (53458578649 / 100000000000000000000000000000000)⟩
def B4_2_2U2_2_0Leaf : Ball := ⟨(32896440012597667463043912769759 / 10000000000000000000000000000000), (41796300803 / 25000000000000000000000000000000)⟩
def B4_2_2U2_2_0Mass : Ball := ⟨(86476446627153830691567188243 / 10000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
def B4_2_2U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B4_2_2U3_0_1Mass : Ball := ⟨(58548930029721897108600768513 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def B4_2_2U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B4_2_2U3_1_0Mass : Ball := ⟨(58572354286272772622701551241 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def B4_2_2U4_0_0Leaf : Ball := ⟨0, 0⟩
def B4_2_2U4_0_0Mass : Ball := ⟨(491331029136091495330612073 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B4_2_2Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B4_2_2U0_2_2Leaf
  | 1, 1, 2 => B4_2_2U1_1_2Leaf
  | 1, 2, 1 => B4_2_2U1_2_1Leaf
  | 2, 0, 2 => B4_2_2U2_0_2Leaf
  | 2, 1, 1 => B4_2_2U2_1_1Leaf
  | 2, 2, 0 => B4_2_2U2_2_0Leaf
  | 3, 0, 1 => B4_2_2U3_0_1Leaf
  | 3, 1, 0 => B4_2_2U3_1_0Leaf
  | 4, 0, 0 => B4_2_2U4_0_0Leaf
  | _, _, _ => (.exact 0)
def B4_2_2Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B4_2_2U0_2_2Mass
  | 1, 1, 2 => B4_2_2U1_1_2Mass
  | 1, 2, 1 => B4_2_2U1_2_1Mass
  | 2, 0, 2 => B4_2_2U2_0_2Mass
  | 2, 1, 1 => B4_2_2U2_1_1Mass
  | 2, 2, 0 => B4_2_2U2_2_0Mass
  | 3, 0, 1 => B4_2_2U3_0_1Mass
  | 3, 1, 0 => B4_2_2U3_1_0Mass
  | 4, 0, 0 => B4_2_2U4_0_0Mass
  | _, _, _ => (.exact 0)
def B4_2_2Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B4_2_2U0_2_2BinaryEntropy
  | 1, 1, 2 => B4_2_2U1_1_2BinaryEntropy
  | 1, 2, 1 => B4_2_2U1_2_1BinaryEntropy
  | 2, 0, 2 => B4_2_2U2_0_2BinaryEntropy
  | 2, 1, 1 => B4_2_2U2_1_1BinaryEntropy
  | 2, 2, 0 => B4_2_2U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
def B4_2_2S2 : Ball := ⟨(18805922951942961214562949931267 / 100000000000000000000000000000000), (402029251 / 5000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal4_3_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B4_3_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(39716959361056311017780307549 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(15598428718166136993941318394257 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(768108580374508289602379874323 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 2, 2, 0 => ⟨1, 0⟩
  | 3, 0, 1 => ⟨(768108580374508289602379874323 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(15598428718166136993941318394257 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(39716959361056311017780307549 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B4_3_1Den : Ball := ⟨(118750296958386282774386398506647 / 50000000000000000000000000000000), (17 / 25000000000000000000000000000000)⟩
def B4_3_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(205241969884719280749621373729 / 3125000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(1293653321378517322144444232489 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(8421031573086763956728433893807 / 20000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(8421031573086763956728433893807 / 20000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(1293653321378517322144444232489 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(205241969884719280749621373729 / 3125000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B4_3_1Law (u : Shape) : Ball := if u ∈ below (shape 4 3 1) then B4_3_1Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B4_3_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 2, 1 => (42189 / 1000000)
  | 2, 1, 1 => (2967 / 1000000)
  | 2, 2, 0 => (48021 / 500000)
  | _, _, _ => 0
def B4_3_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B4_3_1Binary u else if i = 3 then B4_3_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B4_3_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B4_3_1LittleRat u w i)
  else .exact (littleLaw (shape 4 3 1) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B4_3_1U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B4_3_1U0_3_1Mass : Ball := ⟨(136748963356297381050269443 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B4_3_1U1_2_1D : Ball := .exact (42189 / 1000000)
def B4_3_1U1_2_1OneD : Ball := .exact (957811 / 1000000)
def B4_3_1U1_2_1EDLogWitness : LogWitness := ⟨-5, 42189, 31250⟩
def B4_3_1U1_2_1EDLog : Ball := ⟨(-316559575542591669352988093304233 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B4_3_1U1_2_1ED : Ball := ⟨(3338832983141599984583303667103 / 25000000000000000000000000000000), (5360320953 / 100000000000000000000000000000000)⟩
def B4_3_1U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 957811, 500000⟩
def B4_3_1U1_2_1EOneDLog : Ball := ⟨(-4310480648724792521258507583371 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_3_1U1_2_1EOneD : Ball := ⟨(516078222579467781197391550867 / 12500000000000000000000000000000), (10141218429 / 25000000000000000000000000000000)⟩
def B4_3_1U1_2_1BinaryEntropy : Ball := ⟨(5102069088316623863453176716737 / 25000000000000000000000000000000), (47711968321 / 100000000000000000000000000000000)⟩
def B4_3_1U1_2_1Leaf : Ball := ⟨(315097524878051848849748648323579 / 100000000000000000000000000000000), (62187390811 / 50000000000000000000000000000000)⟩
def B4_3_1U1_2_1Mass : Ball := ⟨(26853376888763757073709961953 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B4_3_1U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B4_3_1U1_3_0Mass : Ball := ⟨(2644664994528363790023240491 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B4_3_1U2_1_1D : Ball := .exact (2967 / 1000000)
def B4_3_1U2_1_1OneD : Ball := .exact (997033 / 1000000)
def B4_3_1U2_1_1EDLogWitness : LogWitness := ⟨-9, 23736, 15625⟩
def B4_3_1U2_1_1EDLog : Ball := ⟨(-582020393767345229843310642743373 / 100000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
def B4_3_1U2_1_1ED : Ball := ⟨(86342725415385664847255133851 / 5000000000000000000000000000000), (62828669 / 10000000000000000000000000000000)⟩
def B4_3_1U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 997033, 500000⟩
def B4_3_1U2_1_1EOneDLog : Ball := ⟨(-148570513508735706819130119317 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_3_1U2_1_1EOneD : Ball := ⟨(148129704795155287976997760253 / 50000000000000000000000000000000), (42225990029 / 100000000000000000000000000000000)⟩
def B4_3_1U2_1_1BinaryEntropy : Ball := ⟨(1114385343185079823101595455653 / 50000000000000000000000000000000), (21489967029 / 50000000000000000000000000000000)⟩
def B4_3_1U2_1_1Leaf : Ball := ⟨(5022032222784388708421996016913 / 1562500000000000000000000000000), (31716614023 / 25000000000000000000000000000000)⟩
def B4_3_1U2_1_1Mass : Ball := ⟨(34430874255289519189291326717 / 10000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def B4_3_1U2_2_0D : Ball := .exact (48021 / 500000)
def B4_3_1U2_2_0OneD : Ball := .exact (451979 / 500000)
def B4_3_1U2_2_0EDLogWitness : LogWitness := ⟨-4, 48021, 31250⟩
def B4_3_1U2_2_0EDLog : Ball := ⟨(-234296968318952155799785664084377 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
def B4_3_1U2_2_0ED : Ball := ⟨(2812793678911100368415376843749 / 12500000000000000000000000000000), (10168842291 / 100000000000000000000000000000000)⟩
def B4_3_1U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 451979, 250000⟩
def B4_3_1U2_2_0EOneDLog : Ball := ⟨(-1009723798462591586934335088673 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B4_3_1U2_2_0EOneD : Ball := ⟨(9127479054106473657419876780867 / 100000000000000000000000000000000), (765682209 / 2000000000000000000000000000000)⟩
def B4_3_1U2_2_0BinaryEntropy : Ball := ⟨(38286952636929103345447870437799 / 100000000000000000000000000000000), (26260244829 / 50000000000000000000000000000000)⟩
def B4_3_1U2_2_0Leaf : Ball := ⟨(16462990396327500231505922123031 / 5000000000000000000000000000000), (10460801313 / 6250000000000000000000000000000)⟩
def B4_3_1U2_2_0Mass : Ball := ⟨(34430874255289519189291326717 / 10000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
def B4_3_1U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B4_3_1U3_0_1Mass : Ball := ⟨(2644664994528363790023240491 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B4_3_1U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B4_3_1U3_1_0Mass : Ball := ⟨(26853376888763757073709961953 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B4_3_1U4_0_0Leaf : Ball := ⟨0, 0⟩
def B4_3_1U4_0_0Mass : Ball := ⟨(136748963356297381050269443 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B4_3_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B4_3_1U0_3_1Leaf
  | 1, 2, 1 => B4_3_1U1_2_1Leaf
  | 1, 3, 0 => B4_3_1U1_3_0Leaf
  | 2, 1, 1 => B4_3_1U2_1_1Leaf
  | 2, 2, 0 => B4_3_1U2_2_0Leaf
  | 3, 0, 1 => B4_3_1U3_0_1Leaf
  | 3, 1, 0 => B4_3_1U3_1_0Leaf
  | 4, 0, 0 => B4_3_1U4_0_0Leaf
  | _, _, _ => (.exact 0)
def B4_3_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B4_3_1U0_3_1Mass
  | 1, 2, 1 => B4_3_1U1_2_1Mass
  | 1, 3, 0 => B4_3_1U1_3_0Mass
  | 2, 1, 1 => B4_3_1U2_1_1Mass
  | 2, 2, 0 => B4_3_1U2_2_0Mass
  | 3, 0, 1 => B4_3_1U3_0_1Mass
  | 3, 1, 0 => B4_3_1U3_1_0Mass
  | 4, 0, 0 => B4_3_1U4_0_0Mass
  | _, _, _ => (.exact 0)
def B4_3_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B4_3_1U1_2_1BinaryEntropy
  | 2, 1, 1 => B4_3_1U2_1_1BinaryEntropy
  | 2, 2, 0 => B4_3_1U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
def B4_3_1S2 : Ball := ⟨(2582552552478173297939862688551 / 100000000000000000000000000000000), (285883319 / 25000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal5_1_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B5_1_2U1_1_2D : Ball := .exact (42047 / 1000000)
def B5_1_2U1_1_2OneD : Ball := .exact (957953 / 1000000)
def B5_1_2U1_1_2EDLogWitness : LogWitness := ⟨-5, 42047, 31250⟩
def B5_1_2U1_1_2EDLog : Ball := ⟨(-316896723874678398578307138430309 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
def B5_1_2U1_1_2ED : Ball := ⟨(13324556548758602625022080249579 / 100000000000000000000000000000000), (5342279151 / 100000000000000000000000000000000)⟩
def B5_1_2U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 957953, 500000⟩
def B5_1_2U1_1_2EOneDLog : Ball := ⟨(-4295656275758179541792934076201 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B5_1_2U1_1_2EOneD : Ball := ⟨(4115036816331375366599166577099 / 100000000000000000000000000000000), (811417753 / 2000000000000000000000000000000)⟩
def B5_1_2U1_1_2BinaryEntropy : Ball := ⟨(4070813863038076006825576384973 / 20000000000000000000000000000000), (23846963259 / 50000000000000000000000000000000)⟩
def B5_1_2U1_1_2Leaf : Ball := ⟨(19695023681025525817191748693793 / 6250000000000000000000000000000), (31095950631 / 25000000000000000000000000000000)⟩
def B5_1_2U1_1_2Mass : Ball := ⟨(263347289989209950085958267 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B5_1_2U2_0_2D : Ball := .exact (6867 / 62500)
def B5_1_2U2_0_2OneD : Ball := .exact (55633 / 62500)
def B5_1_2U2_0_2EDLogWitness : LogWitness := ⟨-4, 27468, 15625⟩
def B5_1_2U2_0_2EDLog : Ball := ⟨(-22084392271038164781658598089709 / 10000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B5_1_2U2_0_2ED : Ball := ⟨(38823301561656083854246295829 / 160000000000000000000000000000), (11633150499 / 100000000000000000000000000000000)⟩
def B5_1_2U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 55633, 31250⟩
def B5_1_2U2_0_2EOneDLog : Ball := ⟨(-2327800127447388996729312677817 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B5_1_2U2_0_2EOneD : Ball := ⟨(10360200359222447364403348176399 / 100000000000000000000000000000000), (1178074599 / 3125000000000000000000000000000)⟩
def B5_1_2U2_0_2BinaryEntropy : Ball := ⟨(844810210750114617538725874727 / 2000000000000000000000000000000), (53984797867 / 100000000000000000000000000000000)⟩
def B5_1_2U2_0_2Leaf : Ball := ⟨(32876166056133391052546116649983 / 10000000000000000000000000000000), (167079959367 / 100000000000000000000000000000000)⟩
def B5_1_2U2_0_2Mass : Ball := ⟨(26175208896406964988043914431 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B5_1_2U2_1_1D : Ball := .exact (1993 / 500000)
def B5_1_2U2_1_1OneD : Ball := .exact (498007 / 500000)
def B5_1_2U2_1_1EDLogWitness : LogWitness := ⟨-8, 15944, 15625⟩
def B5_1_2U2_1_1EDLog : Ball := ⟨(-276248352859576703796786793426803 / 50000000000000000000000000000000), (95291206573 / 50000000000000000000000000000000)⟩
def B5_1_2U2_1_1ED : Ball := ⟨(1101125934498272741333992158599 / 50000000000000000000000000000000), (1519323 / 200000000000000000000000000000)⟩
def B5_1_2U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 498007, 250000⟩
def B5_1_2U2_1_1EOneDLog : Ball := ⟨(-399396527142702344795877217257 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B5_1_2U2_1_1EOneD : Ball := ⟨(397804532585511533249520850669 / 100000000000000000000000000000000), (421828337 / 1000000000000000000000000000000)⟩
def B5_1_2U2_1_1BinaryEntropy : Ball := ⟨(1438172433876625608125606907683 / 50000000000000000000000000000000), (43111308867 / 100000000000000000000000000000000)⟩
def B5_1_2U2_1_1Leaf : Ball := ⟨(321246060534923842510835927745293 / 100000000000000000000000000000000), (126801721599 / 100000000000000000000000000000000)⟩
def B5_1_2U2_1_1Mass : Ball := ⟨(46409897166330493680741531629 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B5_1_2U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B5_1_2U3_0_1Mass : Ball := ⟨(46409897166330493680741531629 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B5_1_2U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B5_1_2U3_1_0Mass : Ball := ⟨(26175208896406964988043914431 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B5_1_2U4_0_0Leaf : Ball := ⟨0, 0⟩
def B5_1_2U4_0_0Mass : Ball := ⟨(263347289989209950085958267 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B5_1_2Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B5_1_2U1_1_2Leaf
  | 2, 0, 2 => B5_1_2U2_0_2Leaf
  | 2, 1, 1 => B5_1_2U2_1_1Leaf
  | 3, 0, 1 => B5_1_2U3_0_1Leaf
  | 3, 1, 0 => B5_1_2U3_1_0Leaf
  | 4, 0, 0 => B5_1_2U4_0_0Leaf
  | _, _, _ => (.exact 0)
def B5_1_2Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B5_1_2U1_1_2Mass
  | 2, 0, 2 => B5_1_2U2_0_2Mass
  | 2, 1, 1 => B5_1_2U2_1_1Mass
  | 3, 0, 1 => B5_1_2U3_0_1Mass
  | 3, 1, 0 => B5_1_2U3_1_0Mass
  | 4, 0, 0 => B5_1_2U4_0_0Mass
  | _, _, _ => (.exact 0)
def B5_1_2Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B5_1_2U1_1_2BinaryEntropy
  | 2, 0, 2 => B5_1_2U2_0_2BinaryEntropy
  | 2, 1, 1 => B5_1_2U2_1_1BinaryEntropy
  | _, _, _ => (.exact 0)
def B5_1_2S2 : Ball := ⟨(202798422436966096303225510443 / 50000000000000000000000000000000), (165374319 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal5_2_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B5_2_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => ⟨(453587208715962055977755498999 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 2, 2, 0 => ⟨(1128226781795963371037633404631 / 2000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(1128226781795963371037633404631 / 2000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨1, 0⟩
  | 4, 0, 0 => ⟨(453587208715962055977755498999 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B5_2_1Den : Ball := ⟨(31735855026675595766354089545309 / 10000000000000000000000000000000), (1 / 625000000000000000000000000000)⟩
def B5_2_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(3151010108785313270505790947861 / 10000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(2221908746525876524763592917167 / 12500000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(2221908746525876524763592917167 / 12500000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(3151010108785313270505790947861 / 10000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B5_2_1Law (u : Shape) : Ball := if u ∈ below (shape 5 2 1) then B5_2_1Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B5_2_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 2, 1 => (211 / 5000)
  | 2, 1, 1 => (1917 / 500000)
  | 2, 2, 0 => (55053 / 500000)
  | _, _, _ => 0
def B5_2_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B5_2_1Binary u else if i = 3 then B5_2_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B5_2_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B5_2_1LittleRat u w i)
  else .exact (littleLaw (shape 5 2 1) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B5_2_1U1_2_1D : Ball := .exact (211 / 5000)
def B5_2_1U1_2_1OneD : Ball := .exact (4789 / 5000)
def B5_2_1U1_2_1EDLogWitness : LogWitness := ⟨-5, 844, 625⟩
def B5_2_1U1_2_1EDLog : Ball := ⟨(-158266752897008546545638823852531 / 50000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B5_2_1U1_2_1ED : Ball := ⟨(6678856972253760664225958366577 / 50000000000000000000000000000000), (5361718557 / 100000000000000000000000000000000)⟩
def B5_2_1U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 4789, 2500⟩
def B5_2_1U1_2_1EOneDLog : Ball := ⟨(-431162910736280628338599195593 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B5_2_1U1_2_1EOneD : Ball := ⟨(412967835903209585822710309539 / 10000000000000000000000000000000), (5070550981 / 12500000000000000000000000000000)⟩
def B5_2_1U1_2_1BinaryEntropy : Ball := ⟨(5103118351375646598104934643817 / 25000000000000000000000000000000), (11928341481 / 25000000000000000000000000000000)⟩
def B5_2_1U1_2_1Leaf : Ball := ⟨(315095754496348171339336587488733 / 100000000000000000000000000000000), (124374082821 / 100000000000000000000000000000000)⟩
def B5_2_1U1_2_1Mass : Ball := ⟨(362385426444727423821804449 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B5_2_1U2_1_1D : Ball := .exact (1917 / 500000)
def B5_2_1U2_1_1OneD : Ball := .exact (498083 / 500000)
def B5_2_1U2_1_1EDLogWitness : LogWitness := ⟨-9, 30672, 15625⟩
def B5_2_1U2_1_1EDLog : Ball := ⟨(-69548082929483553739694058747031 / 12500000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
def B5_2_1U2_1_1ED : Ball := ⟨(2133178799613119560303896169889 / 100000000000000000000000000000000), (811881081 / 100000000000000000000000000000000)⟩
def B5_2_1U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 498083, 250000⟩
def B5_2_1U2_1_1EOneDLog : Ball := ⟨(-19206843091090117849948028057 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B5_2_1U2_1_1EOneD : Ball := ⟨(382664081093577566762226546349 / 100000000000000000000000000000000), (42189271151 / 100000000000000000000000000000000)⟩
def B5_2_1U2_1_1BinaryEntropy : Ball := ⟨(2781595509733380158696689438393 / 100000000000000000000000000000000), (43163528449 / 100000000000000000000000000000000)⟩
def B5_2_1U2_1_1Leaf : Ball := ⟨(321270523991192840836529859281353 / 100000000000000000000000000000000), (5072455111 / 4000000000000000000000000000000)⟩
def B5_2_1U2_1_1Mass : Ball := ⟨(15978643995300779447518999591 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B5_2_1U2_2_0D : Ball := .exact (55053 / 500000)
def B5_2_1U2_2_0OneD : Ball := .exact (444947 / 500000)
def B5_2_1U2_2_0EDLogWitness : LogWitness := ⟨-4, 55053, 31250⟩
def B5_2_1U2_2_0EDLog : Ball := ⟨(-110315587041277227232948872211851 / 50000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
def B5_2_1U2_2_0ED : Ball := ⟨(6073204013383435190855534261879 / 25000000000000000000000000000000), (11657926213 / 100000000000000000000000000000000)⟩
def B5_2_1U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 444947, 250000⟩
def B5_2_1U2_2_0EOneDLog : Ball := ⟨(-11665292447264905939613678307427 / 100000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
def B5_2_1U2_2_0EOneD : Ball := ⟨(10380873757066356206226574643709 / 100000000000000000000000000000000), (37688476881 / 100000000000000000000000000000000)⟩
def B5_2_1U2_2_0BinaryEntropy : Ball := ⟨(1692226246274937231740723423409 / 4000000000000000000000000000000), (2700478679 / 5000000000000000000000000000000)⟩
def B5_2_1U2_2_0Leaf : Ball := ⟨(328751484486399694544511642829783 / 100000000000000000000000000000000), (2610546941 / 1562500000000000000000000000000)⟩
def B5_2_1U2_2_0Mass : Ball := ⟨(563360440383799776936723959 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B5_2_1U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B5_2_1U3_0_1Mass : Ball := ⟨(563360440383799776936723959 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B5_2_1U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B5_2_1U3_1_0Mass : Ball := ⟨(15978643995300779447518999591 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B5_2_1U4_0_0Leaf : Ball := ⟨0, 0⟩
def B5_2_1U4_0_0Mass : Ball := ⟨(362385426444727423821804449 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B5_2_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B5_2_1U1_2_1Leaf
  | 2, 1, 1 => B5_2_1U2_1_1Leaf
  | 2, 2, 0 => B5_2_1U2_2_0Leaf
  | 3, 0, 1 => B5_2_1U3_0_1Leaf
  | 3, 1, 0 => B5_2_1U3_1_0Leaf
  | 4, 0, 0 => B5_2_1U4_0_0Leaf
  | _, _, _ => (.exact 0)
def B5_2_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B5_2_1U1_2_1Mass
  | 2, 1, 1 => B5_2_1U2_1_1Mass
  | 2, 2, 0 => B5_2_1U2_2_0Mass
  | 3, 0, 1 => B5_2_1U3_0_1Mass
  | 3, 1, 0 => B5_2_1U3_1_0Mass
  | 4, 0, 0 => B5_2_1U4_0_0Mass
  | _, _, _ => (.exact 0)
def B5_2_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B5_2_1U1_2_1BinaryEntropy
  | 2, 1, 1 => B5_2_1U2_1_1BinaryEntropy
  | 2, 2, 0 => B5_2_1U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
def B5_2_1S2 : Ball := ⟨(69828290229183920558225491291 / 50000000000000000000000000000000), (28471307 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
def B6_1_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 1, 1 => ⟨(19757482365589500963001701230393 / 20000000000000000000000000000000), (63 / 50000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨1, 0⟩
  | 3, 1, 0 => ⟨1, 0⟩
  | 4, 0, 0 => ⟨(19757482365589500963001701230393 / 20000000000000000000000000000000), (63 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B6_1_1Den : Ball := ⟨(39757482365589500963001701230393 / 10000000000000000000000000000000), (63 / 25000000000000000000000000000000)⟩
def B6_1_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 1, 1 => ⟨(124237509457400902736572326499 / 500000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(125762490542599097263427673501 / 500000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(125762490542599097263427673501 / 500000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(124237509457400902736572326499 / 500000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B6_1_1Law (u : Shape) : Ball := if u ∈ below (shape 6 1 1) then B6_1_1Table u else .exact 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B6_1_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 2, 1, 1 => (60257 / 1000000)
  | _, _, _ => 0
def B6_1_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B6_1_1Binary u else if i = 3 then B6_1_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B6_1_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B6_1_1LittleRat u w i)
  else .exact (littleLaw (shape 6 1 1) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B6_1_1U2_1_1D : Ball := .exact (60257 / 1000000)
def B6_1_1U2_1_1OneD : Ball := .exact (939743 / 1000000)
def B6_1_1U2_1_1EDLogWitness : LogWitness := ⟨-5, 60257, 31250⟩
def B6_1_1U2_1_1EDLog : Ball := ⟨(-70228413269685773586736117896293 / 25000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
def B6_1_1U2_1_1ED : Ball := ⟨(4231753498391455659015958256077 / 25000000000000000000000000000000), (7655949647 / 100000000000000000000000000000000)⟩
def B6_1_1U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 939743, 500000⟩
def B6_1_1U2_1_1EOneDLog : Ball := ⟨(-124297690710327487232327528573 / 2000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
def B6_1_1U2_1_1EOneD : Ball := ⟨(5840394238059764191708458434189 / 100000000000000000000000000000000), (39799664151 / 100000000000000000000000000000000)⟩
def B6_1_1U2_1_1BinaryEntropy : Ball := ⟨(26944105197525649278727705902131 / 100000000000000000000000000000000), (25003798507 / 50000000000000000000000000000000)⟩
def B6_1_1U2_1_1Leaf : Ball := ⟨(312189592457865916292919997050341 / 100000000000000000000000000000000), (30806741819 / 25000000000000000000000000000000)⟩
def B6_1_1U2_1_1Mass : Ball := ⟨0, 0⟩
def B6_1_1U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B6_1_1U3_0_1Mass : Ball := ⟨0, 0⟩
def B6_1_1U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
def B6_1_1U3_1_0Mass : Ball := ⟨0, 0⟩
def B6_1_1U4_0_0Leaf : Ball := ⟨0, 0⟩
def B6_1_1U4_0_0Mass : Ball := ⟨0, 0⟩
def B6_1_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 1, 1 => B6_1_1U2_1_1Leaf
  | 3, 0, 1 => B6_1_1U3_0_1Leaf
  | 3, 1, 0 => B6_1_1U3_1_0Leaf
  | 4, 0, 0 => B6_1_1U4_0_0Leaf
  | _, _, _ => (.exact 0)
def B6_1_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 1, 1 => B6_1_1U2_1_1Mass
  | 3, 0, 1 => B6_1_1U3_0_1Mass
  | 3, 1, 0 => B6_1_1U3_1_0Mass
  | 4, 0, 0 => B6_1_1U4_0_0Mass
  | _, _, _ => (.exact 0)
def B6_1_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 1, 1 => B6_1_1U2_1_1BinaryEntropy
  | _, _, _ => (.exact 0)
def B6_1_1S2 : Ball := ⟨0, 0⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
open AllFieldTerminalRates AllFieldVolumeCertificate
def s2ParentBalls (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 6 => B1_1_6S2
  | 1, 2, 5 => B1_2_5S2
  | 1, 3, 4 => B1_3_4S2
  | 1, 4, 3 => B1_4_3S2
  | 1, 5, 2 => B1_5_2S2
  | 1, 6, 1 => B1_6_1S2
  | 2, 1, 5 => B2_1_5S2
  | 2, 2, 4 => B2_2_4S2
  | 2, 3, 3 => B2_3_3S2
  | 2, 4, 2 => B2_4_2S2
  | 2, 5, 1 => B2_5_1S2
  | 3, 1, 4 => B3_1_4S2
  | 3, 2, 3 => B3_2_3S2
  | 3, 3, 2 => B3_3_2S2
  | 3, 4, 1 => B3_4_1S2
  | 4, 1, 3 => B4_1_3S2
  | 4, 2, 2 => B4_2_2S2
  | 4, 3, 1 => B4_3_1S2
  | 5, 1, 2 => B5_1_2S2
  | 5, 2, 1 => B5_2_1S2
  | 6, 1, 1 => B6_1_1S2
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_1_6Ttotal : Ball := ⟨(3710278844513467307488141523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_1_6Btotal : Ball := ⟨(10292390592644662403454216507 / 100000000000000000000000000000000), (1178709 / 12500000000000000000000000000000)⟩
def B1_2_5Ttotal : Ball := ⟨(4755163798532963526151893931759 / 100000000000000000000000000000000), (57 / 100000000000000000000000000000000)⟩
def B1_2_5Btotal : Ball := ⟨(263770662946704051420489805631 / 4000000000000000000000000000000), (4032951479 / 100000000000000000000000000000000)⟩
def B1_3_4Ttotal : Ball := ⟨(7480325224810645241814099259701 / 25000000000000000000000000000000), (151 / 50000000000000000000000000000000)⟩
def B1_3_4Btotal : Ball := ⟨(10623575146720639793993756588557 / 25000000000000000000000000000000), (38286699949 / 100000000000000000000000000000000)⟩
def B1_4_3Ttotal : Ball := ⟨(6944605000406853487412318907203 / 50000000000000000000000000000000), (159 / 100000000000000000000000000000000)⟩
def B1_4_3Btotal : Ball := ⟨(19909829730949708038768839279537 / 100000000000000000000000000000000), (17824415679 / 100000000000000000000000000000000)⟩
def B1_5_2Ttotal : Ball := ⟨(403356547772450802156337181231 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def B1_5_2Btotal : Ball := ⟨(571743387204363003226748332669 / 100000000000000000000000000000000), (516090839 / 100000000000000000000000000000000)⟩
def B1_6_1Ttotal : Ball := ⟨(77881891746725088607012689 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
def B1_6_1Btotal : Ball := ⟨(619013508687338257205025789 / 50000000000000000000000000000000), (1031081 / 100000000000000000000000000000000)⟩
def B2_1_5Ttotal : Ball := ⟨(535927124963214472545786930867 / 25000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
def B2_1_5Btotal : Ball := ⟨(1486547718243755829261660863071 / 50000000000000000000000000000000), (681006439 / 25000000000000000000000000000000)⟩
def B2_2_4Ttotal : Ball := ⟨(20957935808074261818840608407343 / 50000000000000000000000000000000), (113 / 25000000000000000000000000000000)⟩
def B2_2_4Btotal : Ball := ⟨(61259431592020676095074322312553 / 100000000000000000000000000000000), (54088775631 / 100000000000000000000000000000000)⟩
def B2_3_3Ttotal : Ball := ⟨(31969784226000540926113589340621 / 50000000000000000000000000000000), (153 / 25000000000000000000000000000000)⟩
def B2_3_3Btotal : Ball := ⟨(97155091397592012920594654935737 / 100000000000000000000000000000000), (8346926389 / 10000000000000000000000000000000)⟩
def B2_4_2Ttotal : Ball := ⟨(4469292299776841640211258871473 / 50000000000000000000000000000000), (121 / 100000000000000000000000000000000)⟩
def B2_4_2Btotal : Ball := ⟨(13184565128477558357944470754293 / 100000000000000000000000000000000), (11573072161 / 100000000000000000000000000000000)⟩
def B2_5_1Ttotal : Ball := ⟨(31645095109351479784189369397 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
def B2_5_1Btotal : Ball := ⟨(17929724936204266029568343331 / 20000000000000000000000000000000), (20239527 / 25000000000000000000000000000000)⟩
def B3_1_4Ttotal : Ball := ⟨(907559782261289135363984197323 / 12500000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
def B3_1_4Btotal : Ball := ⟨(103669017590719797550293135229 / 1000000000000000000000000000000), (4652487271 / 50000000000000000000000000000000)⟩
def B3_2_3Ttotal : Ball := ⟨(1150430302257331587531431126831 / 3125000000000000000000000000000), (79 / 20000000000000000000000000000000)⟩
def B3_2_3Btotal : Ball := ⟨(55952151483018865110434847256319 / 100000000000000000000000000000000), (12015665981 / 25000000000000000000000000000000)⟩
def B3_3_2Ttotal : Ball := ⟨(8758499276755162714699464520641 / 50000000000000000000000000000000), (209 / 100000000000000000000000000000000)⟩
def B3_3_2Btotal : Ball := ⟨(13315199039969247677694047381629 / 50000000000000000000000000000000), (11435850877 / 50000000000000000000000000000000)⟩
def B3_4_1Ttotal : Ball := ⟨(564009300736610125456854593833 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
def B3_4_1Btotal : Ball := ⟨(202057355425613495053354661181 / 25000000000000000000000000000000), (144745553 / 20000000000000000000000000000000)⟩
def B4_1_3Ttotal : Ball := ⟨(2233079177302622918447096359641 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
def B4_1_3Btotal : Ball := ⟨(64014500780045741535225896199 / 2000000000000000000000000000000), (2865674341 / 100000000000000000000000000000000)⟩
def B4_2_2Ttotal : Ball := ⟨(3767097545009369306050857272327 / 100000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
def B4_2_2Btotal : Ball := ⟨(5557262538143694155705675547867 / 100000000000000000000000000000000), (4877621647 / 100000000000000000000000000000000)⟩
def B4_3_1Ttotal : Ball := ⟨(99503874082605676510083297769 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
def B4_3_1Btotal : Ball := ⟨(570401113257114350350352476201 / 100000000000000000000000000000000), (510740473 / 100000000000000000000000000000000)⟩
def B5_1_2Ttotal : Ball := ⟨(47463286326287333481085364697 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def B5_1_2Btotal : Ball := ⟨(67347402449400564801926883563 / 100000000000000000000000000000000), (60713289 / 100000000000000000000000000000000)⟩
def B5_2_1Ttotal : Ball := ⟨(408525735543637671783520101 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
def B5_2_1Btotal : Ball := ⟨(23171910014948039061690049419 / 100000000000000000000000000000000), (20911247 / 100000000000000000000000000000000)⟩
def B6_1_1Ttotal : Ball := ⟨0, 0⟩
def B6_1_1Btotal : Ball := ⟨0, 0⟩
def BParentBalls (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 6 => B1_1_6Btotal
  | 1, 2, 5 => B1_2_5Btotal
  | 1, 3, 4 => B1_3_4Btotal
  | 1, 4, 3 => B1_4_3Btotal
  | 1, 5, 2 => B1_5_2Btotal
  | 1, 6, 1 => B1_6_1Btotal
  | 2, 1, 5 => B2_1_5Btotal
  | 2, 2, 4 => B2_2_4Btotal
  | 2, 3, 3 => B2_3_3Btotal
  | 2, 4, 2 => B2_4_2Btotal
  | 2, 5, 1 => B2_5_1Btotal
  | 3, 1, 4 => B3_1_4Btotal
  | 3, 2, 3 => B3_2_3Btotal
  | 3, 3, 2 => B3_3_2Btotal
  | 3, 4, 1 => B3_4_1Btotal
  | 4, 1, 3 => B4_1_3Btotal
  | 4, 2, 2 => B4_2_2Btotal
  | 4, 3, 1 => B4_3_1Btotal
  | 5, 1, 2 => B5_1_2Btotal
  | 5, 2, 1 => B5_2_1Btotal
  | 6, 1, 1 => B6_1_1Btotal
  | _, _, _ => (.exact 0)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SupportedContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B3_2_3Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (20837 / 200000)
  | 1, 1, 2 => (947 / 200000)
  | 1, 2, 1 => (38889 / 1000000)
  | 2, 0, 2 => (22013 / 200000)
  | 2, 1, 1 => (21083 / 500000)
  | 2, 2, 0 => (25593 / 250000)
  | _, _, _ => 0
def B3_2_3LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B3_2_3Binary u else if i = 3 then B3_2_3Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B3_2_3Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B3_2_3LittleRat u w i)
  else .exact (littleLaw (shape 3 2 3) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B5_1_2Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 1, 2 => (42047 / 1000000)
  | 2, 0, 2 => (6867 / 62500)
  | 2, 1, 1 => (1993 / 500000)
  | _, _, _ => 0
def B5_1_2LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B5_1_2Binary u else if i = 3 then B5_1_2Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B5_1_2Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B5_1_2LittleRat u w i)
  else .exact (littleLaw (shape 5 1 2) u w i)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_1_14I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_1_14I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 4), (1 / 4000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (7940933911 / 50000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 5000000000000000000000000000000), (15881867787 / 25000000000000000000000000000000)⟩ ⟨-2, 1, 1⟩]
def CA1_1_14I1PairEntropy : Ball := ⟨(6931471805599453094172319305033 / 5000000000000000000000000000000), (7940933911 / 12500000000000000000000000000000)⟩
def CA1_1_14I1PairMass : Ball := ⟨1, (1 / 1000000000000000000000000000000)⟩
def CA1_1_14I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_1_14I1PairMassTermLog : Ball := ⟨0, (10587911891 / 50000000000000000000000000000000)⟩
def CA1_1_14I1PairMassTerm : Ball := ⟨0, (21175823783 / 100000000000000000000000000000000)⟩
def CA1_1_14I1PairH : Ball := ⟨(6931471805599453094172319305033 / 5000000000000000000000000000000), (84703295071 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_1_14I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (47 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823763 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647459 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CA1_1_14I1R0Entropy : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823763 / 100000000000000000000000000000000)⟩
def CA1_1_14I1R0Mass : Ball := ⟨(1 / 2), (47 / 100000000000000000000000000000000)⟩
def CA1_1_14I1R0MassTermLogWitness : LogWitness := ⟨-1, 1, 1⟩
def CA1_1_14I1R0MassTermLog : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647459 / 100000000000000000000000000000000)⟩
def CA1_1_14I1R0MassTerm : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823763 / 100000000000000000000000000000000)⟩
def CA1_1_14I1R0H : Ball := ⟨0, (21175823763 / 50000000000000000000000000000000)⟩
def CA1_1_14I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 4), (1 / 4000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (7940933911 / 50000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 5000000000000000000000000000000), (15881867787 / 25000000000000000000000000000000)⟩ ⟨-2, 1, 1⟩]
def CA1_1_14I1R1Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (7940933911 / 25000000000000000000000000000000)⟩
def CA1_1_14I1R1Mass : Ball := ⟨(1 / 2), (1 / 2000000000000000000000000000000)⟩
def CA1_1_14I1R1MassTermLogWitness : LogWitness := ⟨-1, 1, 1⟩
def CA1_1_14I1R1MassTermLog : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329493 / 20000000000000000000000000000000)⟩
def CA1_1_14I1R1MassTerm : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (2646977971 / 12500000000000000000000000000000)⟩
def CA1_1_14I1R1H : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (13234889853 / 25000000000000000000000000000000)⟩
def CA1_1_14I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R2Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R2Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R2MassTerm : Ball := .exact 0
def CA1_1_14I1R2H : Ball := ⟨0, 0⟩
def CA1_1_14I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R3Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R3Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R3MassTerm : Ball := .exact 0
def CA1_1_14I1R3H : Ball := ⟨0, 0⟩
def CA1_1_14I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R4Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R4Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R4MassTerm : Ball := .exact 0
def CA1_1_14I1R4H : Ball := ⟨0, 0⟩
def CA1_1_14I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R5Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R5Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R5MassTerm : Ball := .exact 0
def CA1_1_14I1R5H : Ball := ⟨0, 0⟩
def CA1_1_14I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R6Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R6Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R6MassTerm : Ball := .exact 0
def CA1_1_14I1R6H : Ball := ⟨0, 0⟩
def CA1_1_14I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R7Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R7Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R7MassTerm : Ball := .exact 0
def CA1_1_14I1R7H : Ball := ⟨0, 0⟩
def CA1_1_14I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R8Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R8Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R8MassTerm : Ball := .exact 0
def CA1_1_14I1R8H : Ball := ⟨0, 0⟩
def CA1_1_14I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R9Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R9Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R9MassTerm : Ball := .exact 0
def CA1_1_14I1R9H : Ball := ⟨0, 0⟩
def CA1_1_14I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R10Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R10Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R10MassTerm : Ball := .exact 0
def CA1_1_14I1R10H : Ball := ⟨0, 0⟩
def CA1_1_14I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R11Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R11Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R11MassTerm : Ball := .exact 0
def CA1_1_14I1R11H : Ball := ⟨0, 0⟩
def CA1_1_14I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R12Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R12Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R12MassTerm : Ball := .exact 0
def CA1_1_14I1R12H : Ball := ⟨0, 0⟩
def CA1_1_14I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R13Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R13Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R13MassTerm : Ball := .exact 0
def CA1_1_14I1R13H : Ball := ⟨0, 0⟩
def CA1_1_14I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R14Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R14Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R14MassTerm : Ball := .exact 0
def CA1_1_14I1R14H : Ball := ⟨0, 0⟩
def CA1_1_14I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R15Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R15Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R15MassTerm : Ball := .exact 0
def CA1_1_14I1R15H : Ball := ⟨0, 0⟩
def CA1_1_14I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I1R16Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I1R16Mass : Ball := ⟨0, 0⟩
def CA1_1_14I1R16MassTerm : Ball := .exact 0
def CA1_1_14I1R16H : Ball := ⟨0, 0⟩
def CA1_1_14I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_1_14I1R0H
  | 1 => CA1_1_14I1R1H
  | 2 => CA1_1_14I1R2H
  | 3 => CA1_1_14I1R3H
  | 4 => CA1_1_14I1R4H
  | 5 => CA1_1_14I1R5H
  | 6 => CA1_1_14I1R6H
  | 7 => CA1_1_14I1R7H
  | 8 => CA1_1_14I1R8H
  | 9 => CA1_1_14I1R9H
  | 10 => CA1_1_14I1R10H
  | 11 => CA1_1_14I1R11H
  | 12 => CA1_1_14I1R12H
  | 13 => CA1_1_14I1R13H
  | 14 => CA1_1_14I1R14H
  | 15 => CA1_1_14I1R15H
  | 16 => CA1_1_14I1R16H
  | _ => (.exact 0)
def CA1_1_14I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA1_1_14I1Singleton : Ball := ⟨0, 0⟩
def CA1_1_14I1Group : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (47645603469 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_1_14I1H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (275285708947 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_1_14I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_1_14I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(99160889261267990055839696027 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(246832658306324730164379568689 / 20000000000000000000000000000000), (419962717 / 100000000000000000000000000000000)⟩ ⟨(-622303460934010062153369001144639 / 100000000000000000000000000000000), (105879118919 / 50000000000000000000000000000000)⟩ ⟨-9, 99160889261267990055839696027, 97656250000000000000000000000⟩,
   .log ⟨(3123764808912903199660529 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(99306653910335874506069959 / 50000000000000000000000000000000), (397 / 625000000000000000000000000000)⟩ ⟨(-198691842986603233560091926417359 / 12500000000000000000000000000000), (101645554311 / 20000000000000000000000000000000)⟩ ⟨-23, 3123764808912903199660529, 2980232238769531250000000⟩,
   .log ⟨(32493265803550027484685499559 / 156250000000000000000000000000), (7 / 20000000000000000000000000000000)⟩ ⟨(1632902986376198777931005263743 / 5000000000000000000000000000000), (880731739 / 5000000000000000000000000000000)⟩ ⟨(-31408488535911439183560405759753 / 20000000000000000000000000000000), (847032949 / 1000000000000000000000000000000)⟩ ⟨-3, 32493265803550027484685499559, 19531250000000000000000000000⟩,
   .log ⟨(288076413385644391463523242139 / 2000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1744371722671518147497689894767 / 6250000000000000000000000000000), (2440102139 / 20000000000000000000000000000000)⟩ ⟨(-24220958629283528807120842185559 / 12500000000000000000000000000000), (4235164739 / 5000000000000000000000000000000)⟩ ⟨-3, 288076413385644391463523242139, 250000000000000000000000000000⟩]
def CA1_1_14I2PairEntropy : Ball := ⟨(9094667866269144492368800187413 / 5000000000000000000000000000000), (10713927161 / 12500000000000000000000000000000)⟩
def CA1_1_14I2PairMass : Ball := ⟨1, (11 / 10000000000000000000000000000000)⟩
def CA1_1_14I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_1_14I2PairMassTermLog : Ball := ⟨0, (1323488987 / 6250000000000000000000000000000)⟩
def CA1_1_14I2PairMassTerm : Ball := ⟨0, (21175823793 / 100000000000000000000000000000000)⟩
def CA1_1_14I2PairH : Ball := ⟨(9094667866269144492368800187413 / 5000000000000000000000000000000), (106887241081 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_1_14I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R0Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R0Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R0MassTerm : Ball := .exact 0
def CA1_1_14I2R0H : Ball := ⟨0, 0⟩
def CA1_1_14I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R1Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R1Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R1MassTerm : Ball := .exact 0
def CA1_1_14I2R1H : Ball := ⟨0, 0⟩
def CA1_1_14I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R2Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R2Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R2MassTerm : Ball := .exact 0
def CA1_1_14I2R2H : Ball := ⟨0, 0⟩
def CA1_1_14I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R3Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R3Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R3MassTerm : Ball := .exact 0
def CA1_1_14I2R3H : Ball := ⟨0, 0⟩
def CA1_1_14I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R4Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R4Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R4MassTerm : Ball := .exact 0
def CA1_1_14I2R4H : Ball := ⟨0, 0⟩
def CA1_1_14I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R5Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R5Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R5MassTerm : Ball := .exact 0
def CA1_1_14I2R5H : Ball := ⟨0, 0⟩
def CA1_1_14I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(99160889261267990055839696027 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(246832658306324730164379568689 / 20000000000000000000000000000000), (419962717 / 100000000000000000000000000000000)⟩ ⟨(-622303460934010062153369001144639 / 100000000000000000000000000000000), (105879118919 / 50000000000000000000000000000000)⟩ ⟨-9, 99160889261267990055839696027, 97656250000000000000000000000⟩,
   .log ⟨(3123764808912903199660529 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(99306653910335874506069959 / 50000000000000000000000000000000), (397 / 625000000000000000000000000000)⟩ ⟨(-198691842986603233560091926417359 / 12500000000000000000000000000000), (101645554311 / 20000000000000000000000000000000)⟩ ⟨-23, 3123764808912903199660529, 2980232238769531250000000⟩,
   .log ⟨(32493265803550027484685499559 / 156250000000000000000000000000), (7 / 20000000000000000000000000000000)⟩ ⟨(1632902986376198777931005263743 / 5000000000000000000000000000000), (880731739 / 5000000000000000000000000000000)⟩ ⟨(-31408488535911439183560405759753 / 20000000000000000000000000000000), (847032949 / 1000000000000000000000000000000)⟩ ⟨-3, 32493265803550027484685499559, 19531250000000000000000000000⟩]
def CA1_1_14I2R6Entropy : Ball := ⟨(17563391768601432101880962620793 / 50000000000000000000000000000000), (9227343627 / 50000000000000000000000000000000)⟩
def CA1_1_14I2R6Mass : Ball := ⟨(211923586614355608536476757861 / 1000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
def CA1_1_14I2R6MassTermLogWitness : LogWitness := ⟨-3, 211923586614355608536476757861, 125000000000000000000000000000⟩
def CA1_1_14I2R6MassTermLog : Ball := ⟨(-155152950978273699515243525338701 / 100000000000000000000000000000000), (3388131797 / 4000000000000000000000000000000)⟩
def CA1_1_14I2R6MassTerm : Ball := ⟨(32880569845117056105244355122547 / 100000000000000000000000000000000), (17950626123 / 100000000000000000000000000000000)⟩
def CA1_1_14I2R6H : Ball := ⟨(2246213692085808098517570119039 / 100000000000000000000000000000000), (36405313377 / 100000000000000000000000000000000)⟩
def CA1_1_14I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R7Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R7Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R7MassTerm : Ball := .exact 0
def CA1_1_14I2R7H : Ball := ⟨0, 0⟩
def CA1_1_14I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R8Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R8Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R8MassTerm : Ball := .exact 0
def CA1_1_14I2R8H : Ball := ⟨0, 0⟩
def CA1_1_14I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R9Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R9Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R9MassTerm : Ball := .exact 0
def CA1_1_14I2R9H : Ball := ⟨0, 0⟩
def CA1_1_14I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R10Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R10Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R10MassTerm : Ball := .exact 0
def CA1_1_14I2R10H : Ball := ⟨0, 0⟩
def CA1_1_14I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R11Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R11Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R11MassTerm : Ball := .exact 0
def CA1_1_14I2R11H : Ball := ⟨0, 0⟩
def CA1_1_14I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R12Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R12Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R12MassTerm : Ball := .exact 0
def CA1_1_14I2R12H : Ball := ⟨0, 0⟩
def CA1_1_14I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R13Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R13Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R13MassTerm : Ball := .exact 0
def CA1_1_14I2R13H : Ball := ⟨0, 0⟩
def CA1_1_14I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R14Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R14Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R14MassTerm : Ball := .exact 0
def CA1_1_14I2R14H : Ball := ⟨0, 0⟩
def CA1_1_14I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R15Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R15Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R15MassTerm : Ball := .exact 0
def CA1_1_14I2R15H : Ball := ⟨0, 0⟩
def CA1_1_14I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_1_14I2R16Entropy : Ball := ⟨0, 0⟩
def CA1_1_14I2R16Mass : Ball := ⟨0, 0⟩
def CA1_1_14I2R16MassTerm : Ball := .exact 0
def CA1_1_14I2R16H : Ball := ⟨0, 0⟩
def CA1_1_14I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_1_14I2R0H
  | 1 => CA1_1_14I2R1H
  | 2 => CA1_1_14I2R2H
  | 3 => CA1_1_14I2R3H
  | 4 => CA1_1_14I2R4H
  | 5 => CA1_1_14I2R5H
  | 6 => CA1_1_14I2R6H
  | 7 => CA1_1_14I2R7H
  | 8 => CA1_1_14I2R8H
  | 9 => CA1_1_14I2R9H
  | 10 => CA1_1_14I2R10H
  | 11 => CA1_1_14I2R11H
  | 12 => CA1_1_14I2R12H
  | 13 => CA1_1_14I2R13H
  | 14 => CA1_1_14I2R14H
  | 15 => CA1_1_14I2R15H
  | 16 => CA1_1_14I2R16H
  | _ => (.exact 0)
def CA1_1_14I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)
def CA1_1_14I2Singleton : Ball := ⟨(1597434829792645590838306169477 / 4000000000000000000000000000000), (24401021369 / 100000000000000000000000000000000)⟩
def CA1_1_14I2Group : Ball := ⟨(10545521109225486967368806088991 / 25000000000000000000000000000000), (30403167373 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_1_14I2H : Ball := ⟨(24382297112894748527106388759083 / 25000000000000000000000000000000), (228499910573 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_2_13I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_2_13I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_2_13I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 2 13)) A1_2_13Law ((Equiv.refl (Fin 3)) 0) a
def CA1_2_13I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (77 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823813 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647519 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CA1_2_13I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I0Certificates (CA1_2_13I0CertificateIndex a)).input
def CA1_2_13I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I0Certificates (CA1_2_13I0CertificateIndex a)).output
def CA1_2_13I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823813 / 50000000000000000000000000000000)⟩
def CA1_2_13I0Mass : Ball := ⟨1, (77 / 50000000000000000000000000000000)⟩
def CA1_2_13I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_2_13I0MassTermLog : Ball := ⟨0, (5293955959 / 25000000000000000000000000000000)⟩
def CA1_2_13I0MassTerm : Ball := ⟨0, (21175823837 / 100000000000000000000000000000000)⟩
def CA1_2_13I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471463 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_2_13I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_2_13I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(510415122544695217681462222771 / 10000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩ ⟨(7592721018162129621059103906471 / 50000000000000000000000000000000), (810634559 / 12500000000000000000000000000000)⟩ ⟨(-297511601157438760339021860675673 / 100000000000000000000000000000000), (127054942529 / 100000000000000000000000000000000)⟩ ⟨-5, 510415122544695217681462222771, 312500000000000000000000000000⟩,
   .log ⟨(427003908687794775861357943063 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(465957963508295875989960509367 / 20000000000000000000000000000000), (813794373 / 100000000000000000000000000000000)⟩ ⟨(-27280661489739575041697282179381 / 5000000000000000000000000000000), (190582413849 / 100000000000000000000000000000000)⟩ ⟨-8, 427003908687794775861357943063, 390625000000000000000000000000⟩,
   .log ⟨(15810100296743071129626219885259 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩ ⟨(29162065027704732871389591738293 / 100000000000000000000000000000000), (669583799 / 5000000000000000000000000000000)⟩ ⟨(-92226059545340794549134603642549 / 50000000000000000000000000000000), (10587911877 / 12500000000000000000000000000000)⟩ ⟨-3, 15810100296743071129626219885259, 12500000000000000000000000000000⟩,
   .log ⟨(11563794717493717482510909886597 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(24946471586450025296435508185089 / 100000000000000000000000000000000), (12243643937 / 100000000000000000000000000000000)⟩ ⟨(-43145822277026388272336325811803 / 20000000000000000000000000000000), (10587911851 / 10000000000000000000000000000000)⟩ ⟨-4, 11563794717493717482510909886597, 6250000000000000000000000000000⟩]
def CA1_2_13I1PairEntropy : Ball := ⟨(4563418876333450428335865153121 / 2000000000000000000000000000000), (6559588193 / 6250000000000000000000000000000)⟩
def CA1_2_13I1PairMass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (117 / 50000000000000000000000000000000)⟩
def CA1_2_13I1PairMassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA1_2_13I1PairMassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (105879119 / 250000000000000000000000000000)⟩
def CA1_2_13I1PairMassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (42351647601 / 100000000000000000000000000000000)⟩
def CA1_2_13I1PairH : Ball := ⟨(228170943816672521416793257656049 / 100000000000000000000000000000000), (147305058689 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_2_13I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(13436205282506282517489090113403 / 50000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩ ⟨(7062446007182092553122167611079 / 20000000000000000000000000000000), (17071362979 / 100000000000000000000000000000000)⟩ ⟨(-32851751381290671558890368327317 / 25000000000000000000000000000000), (15881867817 / 25000000000000000000000000000000)⟩ ⟨-2, 13436205282506282517489090113403, 12500000000000000000000000000000⟩]
def CA1_2_13I1R0Entropy : Ball := ⟨(7062446007182092553122167611079 / 20000000000000000000000000000000), (17071362979 / 100000000000000000000000000000000)⟩
def CA1_2_13I1R0Mass : Ball := ⟨(13436205282506282517489090113403 / 50000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
def CA1_2_13I1R0MassTermLogWitness : LogWitness := ⟨-2, 13436205282506282517489090113403, 12500000000000000000000000000000⟩
def CA1_2_13I1R0MassTermLog : Ball := ⟨(-32851751381290671558890368327317 / 25000000000000000000000000000000), (15881867817 / 25000000000000000000000000000000)⟩
def CA1_2_13I1R0MassTerm : Ball := ⟨(7062446007182092553122167611079 / 20000000000000000000000000000000), (17071362979 / 100000000000000000000000000000000)⟩
def CA1_2_13I1R0H : Ball := ⟨0, (17071362979 / 50000000000000000000000000000000)⟩
def CA1_2_13I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(11563794717493717482510909886597 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩ ⟨(16931059881445265744591999942733 / 50000000000000000000000000000000), (19589830293 / 100000000000000000000000000000000)⟩ ⟨(-29282878665827482083991687201737 / 20000000000000000000000000000000), (42351647409 / 50000000000000000000000000000000)⟩ ⟨-3, 11563794717493717482510909886597, 6250000000000000000000000000000⟩]
def CA1_2_13I1R1Entropy : Ball := ⟨(16931059881445265744591999942733 / 25000000000000000000000000000000), (19589830293 / 50000000000000000000000000000000)⟩
def CA1_2_13I1R1Mass : Ball := ⟨(11563794717493717482510909886597 / 25000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
def CA1_2_13I1R1MassTermLogWitness : LogWitness := ⟨-2, 11563794717493717482510909886597, 6250000000000000000000000000000⟩
def CA1_2_13I1R1MassTermLog : Ball := ⟨(-15419935054628575895647048591671 / 20000000000000000000000000000000), (12705494227 / 20000000000000000000000000000000)⟩
def CA1_2_13I1R1MassTerm : Ball := ⟨(35662592705762024770993966801509 / 100000000000000000000000000000000), (29384745437 / 100000000000000000000000000000000)⟩
def CA1_2_13I1R1H : Ball := ⟨(32061646820019038207374032969423 / 100000000000000000000000000000000), (68564406023 / 100000000000000000000000000000000)⟩
def CA1_2_13I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(510415122544695217681462222771 / 10000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩ ⟨(7592721018162129621059103906471 / 50000000000000000000000000000000), (810634559 / 12500000000000000000000000000000)⟩ ⟨(-297511601157438760339021860675673 / 100000000000000000000000000000000), (127054942529 / 100000000000000000000000000000000)⟩ ⟨-5, 510415122544695217681462222771, 312500000000000000000000000000⟩,
   .log ⟨(427003908687794775861357943063 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(465957963508295875989960509367 / 20000000000000000000000000000000), (813794373 / 100000000000000000000000000000000)⟩ ⟨(-27280661489739575041697282179381 / 5000000000000000000000000000000), (190582413849 / 100000000000000000000000000000000)⟩ ⟨-8, 427003908687794775861357943063, 390625000000000000000000000000⟩,
   .log ⟨(15810100296743071129626219885259 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩ ⟨(29162065027704732871389591738293 / 100000000000000000000000000000000), (669583799 / 5000000000000000000000000000000)⟩ ⟨(-92226059545340794549134603642549 / 50000000000000000000000000000000), (10587911877 / 12500000000000000000000000000000)⟩ ⟨-3, 15810100296743071129626219885259, 12500000000000000000000000000000⟩]
def CA1_2_13I1R2Entropy : Ball := ⟨(64192528735436210115525612457847 / 100000000000000000000000000000000), (2798941767 / 10000000000000000000000000000000)⟩
def CA1_2_13I1R2Mass : Ball := ⟨(5374482113002513006995636045361 / 20000000000000000000000000000000), (19 / 20000000000000000000000000000000)⟩
def CA1_2_13I1R2MassTermLogWitness : LogWitness := ⟨-2, 5374482113002513006995636045361, 5000000000000000000000000000000⟩
def CA1_2_13I1R2MassTermLog : Ball := ⟨(-16425875690645335779445184163659 / 12500000000000000000000000000000), (63527471401 / 100000000000000000000000000000000)⟩
def CA1_2_13I1R2MassTerm : Ball := ⟨(7062446007182092553122167611079 / 20000000000000000000000000000000), (8535681531 / 50000000000000000000000000000000)⟩
def CA1_2_13I1R2H : Ball := ⟨(7220074674881436837478693600613 / 25000000000000000000000000000000), (11265195183 / 25000000000000000000000000000000)⟩
def CA1_2_13I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R3Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R3Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R3MassTerm : Ball := .exact 0
def CA1_2_13I1R3H : Ball := ⟨0, 0⟩
def CA1_2_13I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R4Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R4Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R4MassTerm : Ball := .exact 0
def CA1_2_13I1R4H : Ball := ⟨0, 0⟩
def CA1_2_13I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R5Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R5Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R5MassTerm : Ball := .exact 0
def CA1_2_13I1R5H : Ball := ⟨0, 0⟩
def CA1_2_13I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R6Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R6Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R6MassTerm : Ball := .exact 0
def CA1_2_13I1R6H : Ball := ⟨0, 0⟩
def CA1_2_13I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R7Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R7Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R7MassTerm : Ball := .exact 0
def CA1_2_13I1R7H : Ball := ⟨0, 0⟩
def CA1_2_13I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R8Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R8Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R8MassTerm : Ball := .exact 0
def CA1_2_13I1R8H : Ball := ⟨0, 0⟩
def CA1_2_13I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R9Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R9Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R9MassTerm : Ball := .exact 0
def CA1_2_13I1R9H : Ball := ⟨0, 0⟩
def CA1_2_13I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R10Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R10Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R10MassTerm : Ball := .exact 0
def CA1_2_13I1R10H : Ball := ⟨0, 0⟩
def CA1_2_13I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R11Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R11Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R11MassTerm : Ball := .exact 0
def CA1_2_13I1R11H : Ball := ⟨0, 0⟩
def CA1_2_13I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R12Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R12Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R12MassTerm : Ball := .exact 0
def CA1_2_13I1R12H : Ball := ⟨0, 0⟩
def CA1_2_13I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R13Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R13Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R13MassTerm : Ball := .exact 0
def CA1_2_13I1R13H : Ball := ⟨0, 0⟩
def CA1_2_13I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R14Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R14Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R14MassTerm : Ball := .exact 0
def CA1_2_13I1R14H : Ball := ⟨0, 0⟩
def CA1_2_13I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R15Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R15Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R15MassTerm : Ball := .exact 0
def CA1_2_13I1R15H : Ball := ⟨0, 0⟩
def CA1_2_13I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I1R16Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I1R16Mass : Ball := ⟨0, 0⟩
def CA1_2_13I1R16MassTerm : Ball := .exact 0
def CA1_2_13I1R16H : Ball := ⟨0, 0⟩
def CA1_2_13I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_2_13I1R0H
  | 1 => CA1_2_13I1R1H
  | 2 => CA1_2_13I1R2H
  | 3 => CA1_2_13I1R3H
  | 4 => CA1_2_13I1R4H
  | 5 => CA1_2_13I1R5H
  | 6 => CA1_2_13I1R6H
  | 7 => CA1_2_13I1R7H
  | 8 => CA1_2_13I1R8H
  | 9 => CA1_2_13I1R9H
  | 10 => CA1_2_13I1R10H
  | 11 => CA1_2_13I1R11H
  | 12 => CA1_2_13I1R12H
  | 13 => CA1_2_13I1R13H
  | 14 => CA1_2_13I1R14H
  | 15 => CA1_2_13I1R15H
  | 16 => CA1_2_13I1R16H
  | _ => (.exact 0)
def CA1_2_13I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA1_2_13I1Singleton : Ball := ⟨0, 0⟩
def CA1_2_13I1Group : Ball := ⟨(19501422566254331378332418359 / 32000000000000000000000000000), (147767912713 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_2_13I1H : Ball := ⟨(106287052777582950302215642912299 / 100000000000000000000000000000000), (88568176823 / 20000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_2_13I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_2_13I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(442586390428493077743201299 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(23719548252484822547177113277 / 100000000000000000000000000000000), (1991581 / 25000000000000000000000000000000)⟩ ⟨(-1071860715351892212750556015805041 / 100000000000000000000000000000000), (1799945239 / 500000000000000000000000000000)⟩ ⟨-16, 442586390428493077743201299, 305175781250000000000000000⟩,
   .log ⟨(73487247372078367653150166241 / 5000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1240488635278793899698860727877 / 20000000000000000000000000000000), (2489844827 / 100000000000000000000000000000000)⟩ ⟨(-422008130539299575952973473557267 / 100000000000000000000000000000000), (8470329497 / 5000000000000000000000000000000)⟩ ⟨-7, 73487247372078367653150166241, 39062500000000000000000000000⟩,
   .log ⟨(13559799966062424844924713757 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(407852833492994091090370054029 / 100000000000000000000000000000000), (137827177 / 100000000000000000000000000000000)⟩ ⟨(-751952157321220455269927703992753 / 100000000000000000000000000000000), (254109886039 / 100000000000000000000000000000000)⟩ ⟨-11, 13559799966062424844924713757, 12207031250000000000000000000⟩,
   .log ⟨(602160777172434722019253310913 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(4487430519244414723671769540491 / 50000000000000000000000000000000), (3570350173 / 100000000000000000000000000000000)⟩ ⟨(-186305331124190541737476037081479 / 50000000000000000000000000000000), (29646153239 / 20000000000000000000000000000000)⟩ ⟨-6, 602160777172434722019253310913, 390625000000000000000000000000⟩,
   .log ⟨(93171277412476765128264423973 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(146403261066533712208140456213 / 12500000000000000000000000000000), (86811059 / 20000000000000000000000000000000)⟩ ⟨(-25141355169944859121021011035561 / 4000000000000000000000000000000), (116467030793 / 50000000000000000000000000000000)⟩ ⟨-10, 93171277412476765128264423973, 48828125000000000000000000000⟩,
   .log ⟨(914191579685632782275074881523 / 5000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩ ⟨(3883378495598803084596402029963 / 12500000000000000000000000000000), (7743503921 / 50000000000000000000000000000000)⟩ ⟨(-169915303614334234657882374566849 / 100000000000000000000000000000000), (8470329489 / 10000000000000000000000000000000)⟩ ⟨-3, 914191579685632782275074881523, 625000000000000000000000000000⟩]
def CA1_2_13I2PairEntropy : Ball := ⟨(57993217776972071378920392507767 / 25000000000000000000000000000000), (13065728553 / 12500000000000000000000000000000)⟩
def CA1_2_13I2PairMass : Ball := ⟨(24999999999999999999999999999999 / 25000000000000000000000000000000), (31 / 12500000000000000000000000000000)⟩
def CA1_2_13I2PairMassTermLogWitness : LogWitness := ⟨-1, 24999999999999999999999999999999, 12500000000000000000000000000000⟩
def CA1_2_13I2PairMassTermLog : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175823807 / 50000000000000000000000000000000)⟩
def CA1_2_13I2PairMassTerm : Ball := ⟨(1 / 25000000000000000000000000000000), (8470329523 / 20000000000000000000000000000000)⟩
def CA1_2_13I2PairH : Ball := ⟨(28996608888486035689460196253883 / 12500000000000000000000000000000), (146877476039 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_2_13I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R0Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R0Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R0MassTerm : Ball := .exact 0
def CA1_2_13I2R0H : Ball := ⟨0, 0⟩
def CA1_2_13I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R1Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R1Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R1MassTerm : Ball := .exact 0
def CA1_2_13I2R1H : Ball := ⟨0, 0⟩
def CA1_2_13I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R2Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R2Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R2MassTerm : Ball := .exact 0
def CA1_2_13I2R2H : Ball := ⟨0, 0⟩
def CA1_2_13I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R3Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R3Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R3MassTerm : Ball := .exact 0
def CA1_2_13I2R3H : Ball := ⟨0, 0⟩
def CA1_2_13I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R4Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R4Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R4MassTerm : Ball := .exact 0
def CA1_2_13I2R4H : Ball := ⟨0, 0⟩
def CA1_2_13I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(442586390428493077743201299 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(23719548252484822547177113277 / 100000000000000000000000000000000), (1991581 / 25000000000000000000000000000000)⟩ ⟨(-1071860715351892212750556015805041 / 100000000000000000000000000000000), (1799945239 / 500000000000000000000000000000)⟩ ⟨-16, 442586390428493077743201299, 305175781250000000000000000⟩,
   .log ⟨(73487247372078367653150166241 / 5000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1240488635278793899698860727877 / 20000000000000000000000000000000), (2489844827 / 100000000000000000000000000000000)⟩ ⟨(-422008130539299575952973473557267 / 100000000000000000000000000000000), (8470329497 / 5000000000000000000000000000000)⟩ ⟨-7, 73487247372078367653150166241, 39062500000000000000000000000⟩,
   .log ⟨(13559799966062424844924713757 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(407852833492994091090370054029 / 100000000000000000000000000000000), (137827177 / 100000000000000000000000000000000)⟩ ⟨(-751952157321220455269927703992753 / 100000000000000000000000000000000), (254109886039 / 100000000000000000000000000000000)⟩ ⟨-11, 13559799966062424844924713757, 12207031250000000000000000000⟩]
def CA1_2_13I2R5Entropy : Ball := ⟨(6634015558139448412131850806691 / 50000000000000000000000000000000), (329454791 / 6250000000000000000000000000000)⟩
def CA1_2_13I2R5Mass : Ball := ⟨(1526197079257959517831418186343 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
def CA1_2_13I2R5MassTermLogWitness : LogWitness := ⟨-6, 1526197079257959517831418186343, 781250000000000000000000000000⟩
def CA1_2_13I2R5MassTermLog : Ball := ⟨(-43615549166142176302494797824791 / 12500000000000000000000000000000), (148230766371 / 100000000000000000000000000000000)⟩
def CA1_2_13I2R5MassTerm : Ball := ⟨(2130109559923139878541476166057 / 20000000000000000000000000000000), (4524587317 / 100000000000000000000000000000000)⟩
def CA1_2_13I2R5H : Ball := ⟨(2617483316663197431556320783097 / 100000000000000000000000000000000), (9795863973 / 100000000000000000000000000000000)⟩
def CA1_2_13I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(216432004712731669553203427467 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(663975410196592757437400918067 / 50000000000000000000000000000000), (114578153 / 25000000000000000000000000000000)⟩ ⟨(-76695612910609221632260488966757 / 12500000000000000000000000000000), (211758237753 / 100000000000000000000000000000000)⟩ ⟨-9, 216432004712731669553203427467, 195312500000000000000000000000⟩,
   .log ⟨(13636075369650383155990643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(53889639849187088294317631 / 25000000000000000000000000000000), (69319 / 100000000000000000000000000000000)⟩ ⟨(-1580796186243689579385450323206413 / 100000000000000000000000000000000), (12705677547 / 2500000000000000000000000000000)⟩ ⟨-23, 13636075369650383155990643, 11920928955078125000000000⟩,
   .log ⟨(5673674538352808081287275234243 / 25000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩ ⟨(33657119057436050543472652170287 / 100000000000000000000000000000000), (4805789279 / 25000000000000000000000000000000)⟩ ⟨(-148303885030420906822516939407071 / 100000000000000000000000000000000), (4235164741 / 5000000000000000000000000000000)⟩ ⟨-3, 5673674538352808081287275234243, 3125000000000000000000000000000⟩]
def CA1_2_13I2R6Entropy : Ball := ⟨(36313451815341215069928610383603 / 100000000000000000000000000000000), (10069960489 / 50000000000000000000000000000000)⟩
def CA1_2_13I2R6Mass : Ball := ⟨(2890948679373429370627727471649 / 12500000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
def CA1_2_13I2R6MassTermLogWitness : LogWitness := ⟨-3, 2890948679373429370627727471649, 1562500000000000000000000000000⟩
def CA1_2_13I2R6MassTermLog : Ball := ⟨(-146414393329137410419958436008693 / 100000000000000000000000000000000), (21175823711 / 25000000000000000000000000000000)⟩
def CA1_2_13I2R6MassTerm : Ball := ⟨(6772423952578106297836799977093 / 20000000000000000000000000000000), (4897457577 / 25000000000000000000000000000000)⟩
def CA1_2_13I2R6H : Ball := ⟨(1225666026225341790372305249069 / 50000000000000000000000000000000), (19864875643 / 50000000000000000000000000000000)⟩
def CA1_2_13I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R7Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R7Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R7MassTerm : Ball := .exact 0
def CA1_2_13I2R7H : Ball := ⟨0, 0⟩
def CA1_2_13I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R8Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R8Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R8MassTerm : Ball := .exact 0
def CA1_2_13I2R8H : Ball := ⟨0, 0⟩
def CA1_2_13I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R9Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R9Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R9MassTerm : Ball := .exact 0
def CA1_2_13I2R9H : Ball := ⟨0, 0⟩
def CA1_2_13I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R10Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R10Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R10MassTerm : Ball := .exact 0
def CA1_2_13I2R10H : Ball := ⟨0, 0⟩
def CA1_2_13I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R11Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R11Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R11MassTerm : Ball := .exact 0
def CA1_2_13I2R11H : Ball := ⟨0, 0⟩
def CA1_2_13I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R12Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R12Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R12MassTerm : Ball := .exact 0
def CA1_2_13I2R12H : Ball := ⟨0, 0⟩
def CA1_2_13I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R13Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R13Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R13MassTerm : Ball := .exact 0
def CA1_2_13I2R13H : Ball := ⟨0, 0⟩
def CA1_2_13I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R14Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R14Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R14MassTerm : Ball := .exact 0
def CA1_2_13I2R14H : Ball := ⟨0, 0⟩
def CA1_2_13I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R15Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R15Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R15MassTerm : Ball := .exact 0
def CA1_2_13I2R15H : Ball := ⟨0, 0⟩
def CA1_2_13I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_2_13I2R16Entropy : Ball := ⟨0, 0⟩
def CA1_2_13I2R16Mass : Ball := ⟨0, 0⟩
def CA1_2_13I2R16MassTerm : Ball := .exact 0
def CA1_2_13I2R16H : Ball := ⟨0, 0⟩
def CA1_2_13I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_2_13I2R0H
  | 1 => CA1_2_13I2R1H
  | 2 => CA1_2_13I2R2H
  | 3 => CA1_2_13I2R3H
  | 4 => CA1_2_13I2R4H
  | 5 => CA1_2_13I2R5H
  | 6 => CA1_2_13I2R6H
  | 7 => CA1_2_13I2R7H
  | 8 => CA1_2_13I2R8H
  | 9 => CA1_2_13I2R9H
  | 10 => CA1_2_13I2R10H
  | 11 => CA1_2_13I2R11H
  | 12 => CA1_2_13I2R12H
  | 13 => CA1_2_13I2R13H
  | 14 => CA1_2_13I2R14H
  | 15 => CA1_2_13I2R15H
  | 16 => CA1_2_13I2R16H
  | _ => (.exact 0)
def CA1_2_13I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)
def CA1_2_13I2Singleton : Ball := ⟨(58270157785646687706346512918121 / 100000000000000000000000000000000), (44745661021 / 100000000000000000000000000000000)⟩
def CA1_2_13I2Group : Ball := ⟨(15834743288690142179661861049839 / 25000000000000000000000000000000), (2356781907 / 2500000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_2_13I2H : Ball := ⟨(3290466399948973377449583801011 / 3125000000000000000000000000000), (335420028599 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_3_12I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_3_12I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_3_12I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 3 12)) A1_3_12Law ((Equiv.refl (Fin 3)) 0) a
def CA1_3_12I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (87 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (2117582383 / 10000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647539 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CA1_3_12I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I0Certificates (CA1_3_12I0CertificateIndex a)).input
def CA1_3_12I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I0Certificates (CA1_3_12I0CertificateIndex a)).output
def CA1_3_12I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (2117582383 / 5000000000000000000000000000000)⟩
def CA1_3_12I0Mass : Ball := ⟨1, (87 / 50000000000000000000000000000000)⟩
def CA1_3_12I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_3_12I0MassTermLog : Ball := ⟨0, (1323488991 / 6250000000000000000000000000000)⟩
def CA1_3_12I0MassTerm : Ball := ⟨0, (21175823857 / 100000000000000000000000000000000)⟩
def CA1_3_12I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471517 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_3_12I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_3_12I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(129165067930240297565270841043 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(96206778032876131242691152417 / 6250000000000000000000000000000), (136758839 / 25000000000000000000000000000000)⟩ ⟨(-297934355083792968334169073309091 / 50000000000000000000000000000000), (52939559401 / 25000000000000000000000000000000)⟩ ⟨-9, 129165067930240297565270841043, 97656250000000000000000000000⟩,
   .log ⟨(2162328515383313515631099877419 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩ ⟨(339576107987341944429779096823 / 2500000000000000000000000000000), (549469059 / 10000000000000000000000000000000)⟩ ⟨(-314083734799331057367608445873267 / 100000000000000000000000000000000), (5082197707 / 4000000000000000000000000000000)⟩ ⟨-5, 2162328515383313515631099877419, 1562500000000000000000000000000⟩,
   .log ⟨(427947066201928425852550330863 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2333991611354785982686465723567 / 100000000000000000000000000000000), (407795933 / 50000000000000000000000000000000)⟩ ⟨(-545392595413537266791669348013853 / 100000000000000000000000000000000), (190582413847 / 100000000000000000000000000000000)⟩ ⟨-8, 427947066201928425852550330863, 390625000000000000000000000000⟩,
   .log ⟨(92627022061849000538047060611 / 2500000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩ ⟨(11923793680862421296193265431 / 97656250000000000000000000000), (4707488427 / 100000000000000000000000000000000)⟩ ⟨(-2059665685531922602957388588871 / 625000000000000000000000000000), (7940933903 / 6250000000000000000000000000000)⟩ ⟨-5, 92627022061849000538047060611, 78125000000000000000000000000⟩,
   .log ⟨(162306731564696040567822146153 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1860129390280237914069036106119 / 100000000000000000000000000000000), (8592447 / 1250000000000000000000000000000)⟩ ⟨(-573029033468887186035218542802501 / 100000000000000000000000000000000), (105879118723 / 50000000000000000000000000000000)⟩ ⟨-9, 162306731564696040567822146153, 97656250000000000000000000000⟩,
   .log ⟨(11929677075964259742439654798719 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩ ⟨(12682087884207895773931543275227 / 50000000000000000000000000000000), (12631036993 / 100000000000000000000000000000000)⟩ ⟨(-106307050923948162934637424394289 / 50000000000000000000000000000000), (13234889827 / 12500000000000000000000000000000)⟩ ⟨-4, 11929677075964259742439654798719, 6250000000000000000000000000000⟩]
def CA1_3_12I1PairEntropy : Ball := ⟨(70960708386756988050365654400539 / 25000000000000000000000000000000), (30278123179 / 25000000000000000000000000000000)⟩
def CA1_3_12I1PairMass : Ball := ⟨(12499999999999999999999999999999 / 12500000000000000000000000000000), (21 / 6250000000000000000000000000000)⟩
def CA1_3_12I1PairMassTermLogWitness : LogWitness := ⟨-1, 12499999999999999999999999999999, 6250000000000000000000000000000⟩
def CA1_3_12I1PairMassTermLog : Ball := ⟨(-7 / 100000000000000000000000000000000), (21175823851 / 50000000000000000000000000000000)⟩
def CA1_3_12I1PairMassTerm : Ball := ⟨(7 / 100000000000000000000000000000000), (42351647703 / 100000000000000000000000000000000)⟩
def CA1_3_12I1PairH : Ball := ⟨(283842833547027952201462617602149 / 100000000000000000000000000000000), (163464140419 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_3_12I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(400874738626322884179623341423 / 4000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩ ⟨(11527156286617510553316846465319 / 50000000000000000000000000000000), (10611066103 / 100000000000000000000000000000000)⟩ ⟨(-115020031704842334608420288281259 / 50000000000000000000000000000000), (1654361231 / 1562500000000000000000000000000)⟩ ⟨-4, 400874738626322884179623341423, 250000000000000000000000000000⟩]
def CA1_3_12I1R0Entropy : Ball := ⟨(11527156286617510553316846465319 / 50000000000000000000000000000000), (10611066103 / 100000000000000000000000000000000)⟩
def CA1_3_12I1R0Mass : Ball := ⟨(400874738626322884179623341423 / 4000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
def CA1_3_12I1R0MassTermLogWitness : LogWitness := ⟨-4, 400874738626322884179623341423, 250000000000000000000000000000⟩
def CA1_3_12I1R0MassTermLog : Ball := ⟨(-115020031704842334608420288281259 / 50000000000000000000000000000000), (1654361231 / 1562500000000000000000000000000)⟩
def CA1_3_12I1R0MassTerm : Ball := ⟨(11527156286617510553316846465319 / 50000000000000000000000000000000), (10611066103 / 100000000000000000000000000000000)⟩
def CA1_3_12I1R0H : Ball := ⟨0, (10611066103 / 50000000000000000000000000000000)⟩
def CA1_3_12I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4997266441792740986938677058053 / 25000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩ ⟨(32182091523171578015673626942937 / 100000000000000000000000000000000), (3386279473 / 20000000000000000000000000000000)⟩ ⟨(-80499238678842675556638879701571 / 50000000000000000000000000000000), (10587911859 / 12500000000000000000000000000000)⟩ ⟨-3, 4997266441792740986938677058053, 3125000000000000000000000000000⟩]
def CA1_3_12I1R1Entropy : Ball := ⟨(32182091523171578015673626942937 / 50000000000000000000000000000000), (3386279473 / 10000000000000000000000000000000)⟩
def CA1_3_12I1R1Mass : Ball := ⟨(4997266441792740986938677058053 / 12500000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
def CA1_3_12I1R1MassTermLogWitness : LogWitness := ⟨-2, 4997266441792740986938677058053, 3125000000000000000000000000000⟩
def CA1_3_12I1R1MassTermLog : Ball := ⟨(-22920939825422705042888641588203 / 25000000000000000000000000000000), (63527471189 / 100000000000000000000000000000000)⟩
def CA1_3_12I1R1MassTerm : Ball := ⟨(36653453889259408322891679275017 / 100000000000000000000000000000000), (6349274011 / 25000000000000000000000000000000)⟩
def CA1_3_12I1R1H : Ball := ⟨(27710729157083747708455574610857 / 100000000000000000000000000000000), (29629945387 / 50000000000000000000000000000000)⟩
def CA1_3_12I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(7410161764947920043043764848881 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩ ⟨(9641798361769739933798519412583 / 50000000000000000000000000000000), (7845814037 / 100000000000000000000000000000000)⟩ ⟨(-260231791629113085531458981169017 / 100000000000000000000000000000000), (52939559369 / 50000000000000000000000000000000)⟩ ⟨-4, 7410161764947920043043764848881, 6250000000000000000000000000000⟩,
   .log ⟨(649226926258784162271288584613 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(408781120885075007965636602421 / 12500000000000000000000000000000), (618656181 / 50000000000000000000000000000000)⟩ ⟨(-31482144713305790943343459359501 / 6250000000000000000000000000000), (190582413609 / 100000000000000000000000000000000)⟩ ⟨-8, 649226926258784162271288584613, 390625000000000000000000000000⟩,
   .log ⟨(11929677075964259742439654798719 / 50000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩ ⟨(34190307476441104810110094830853 / 100000000000000000000000000000000), (20209659179 / 100000000000000000000000000000000)⟩ ⟨(-17912422973987724365943956967281 / 12500000000000000000000000000000), (2117582373 / 2500000000000000000000000000000)⟩ ⟨-3, 11929677075964259742439654798719, 6250000000000000000000000000000⟩]
def CA1_3_12I1R2Entropy : Ball := ⟨(79297998857681264672754358119921 / 100000000000000000000000000000000), (38375911977 / 100000000000000000000000000000000)⟩
def CA1_3_12I1R2Mass : Ball := ⟨(19989065767170963947754708232213 / 50000000000000000000000000000000), (99 / 100000000000000000000000000000000)⟩
def CA1_3_12I1R2MassTermLogWitness : LogWitness := ⟨-2, 19989065767170963947754708232213, 12500000000000000000000000000000⟩
def CA1_3_12I1R2MassTermLog : Ball := ⟨(-91683759301690820171554566352807 / 100000000000000000000000000000000), (992616739 / 1562500000000000000000000000000)⟩
def CA1_3_12I1R2MassTerm : Ball := ⟨(36653453889259408322891679275017 / 100000000000000000000000000000000), (25397096127 / 100000000000000000000000000000000)⟩
def CA1_3_12I1R2H : Ball := ⟨(5330568121052732043732834855613 / 12500000000000000000000000000000), (7971626013 / 12500000000000000000000000000000)⟩
def CA1_3_12I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(129165067930240297565270841043 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(96206778032876131242691152417 / 6250000000000000000000000000000), (136758839 / 25000000000000000000000000000000)⟩ ⟨(-297934355083792968334169073309091 / 50000000000000000000000000000000), (52939559401 / 25000000000000000000000000000000)⟩ ⟨-9, 129165067930240297565270841043, 97656250000000000000000000000⟩,
   .log ⟨(2162328515383313515631099877419 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩ ⟨(339576107987341944429779096823 / 2500000000000000000000000000000), (549469059 / 10000000000000000000000000000000)⟩ ⟨(-314083734799331057367608445873267 / 100000000000000000000000000000000), (5082197707 / 4000000000000000000000000000000)⟩ ⟨-5, 2162328515383313515631099877419, 1562500000000000000000000000000⟩,
   .log ⟨(427947066201928425852550330863 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2333991611354785982686465723567 / 100000000000000000000000000000000), (407795933 / 50000000000000000000000000000000)⟩ ⟨(-545392595413537266791669348013853 / 100000000000000000000000000000000), (190582413847 / 100000000000000000000000000000000)⟩ ⟨-8, 427947066201928425852550330863, 390625000000000000000000000000⟩]
def CA1_3_12I1R3Entropy : Ball := ⟨(17456344379374481859760688035159 / 50000000000000000000000000000000), (1714329453 / 12500000000000000000000000000000)⟩
def CA1_3_12I1R3Mass : Ball := ⟨(5010934232829036052245291767787 / 50000000000000000000000000000000), (3 / 5000000000000000000000000000000)⟩
def CA1_3_12I1R3MassTermLogWitness : LogWitness := ⟨-4, 5010934232829036052245291767787, 3125000000000000000000000000000⟩
def CA1_3_12I1R3MassTermLog : Ball := ⟨(-7188751981552645913026268017579 / 3125000000000000000000000000000), (105879119013 / 100000000000000000000000000000000)⟩
def CA1_3_12I1R3MassTerm : Ball := ⟨(23054312573235021106633692930637 / 100000000000000000000000000000000), (10611066179 / 100000000000000000000000000000000)⟩
def CA1_3_12I1R3H : Ball := ⟨(11858376185513942612887683139681 / 100000000000000000000000000000000), (24325701803 / 100000000000000000000000000000000)⟩
def CA1_3_12I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R4Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R4Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R4MassTerm : Ball := .exact 0
def CA1_3_12I1R4H : Ball := ⟨0, 0⟩
def CA1_3_12I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R5Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R5Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R5MassTerm : Ball := .exact 0
def CA1_3_12I1R5H : Ball := ⟨0, 0⟩
def CA1_3_12I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R6Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R6Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R6MassTerm : Ball := .exact 0
def CA1_3_12I1R6H : Ball := ⟨0, 0⟩
def CA1_3_12I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R7Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R7Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R7MassTerm : Ball := .exact 0
def CA1_3_12I1R7H : Ball := ⟨0, 0⟩
def CA1_3_12I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R8Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R8Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R8MassTerm : Ball := .exact 0
def CA1_3_12I1R8H : Ball := ⟨0, 0⟩
def CA1_3_12I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R9Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R9Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R9MassTerm : Ball := .exact 0
def CA1_3_12I1R9H : Ball := ⟨0, 0⟩
def CA1_3_12I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R10Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R10Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R10MassTerm : Ball := .exact 0
def CA1_3_12I1R10H : Ball := ⟨0, 0⟩
def CA1_3_12I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R11Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R11Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R11MassTerm : Ball := .exact 0
def CA1_3_12I1R11H : Ball := ⟨0, 0⟩
def CA1_3_12I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R12Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R12Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R12MassTerm : Ball := .exact 0
def CA1_3_12I1R12H : Ball := ⟨0, 0⟩
def CA1_3_12I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R13Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R13Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R13MassTerm : Ball := .exact 0
def CA1_3_12I1R13H : Ball := ⟨0, 0⟩
def CA1_3_12I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R14Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R14Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R14MassTerm : Ball := .exact 0
def CA1_3_12I1R14H : Ball := ⟨0, 0⟩
def CA1_3_12I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R15Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R15Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R15MassTerm : Ball := .exact 0
def CA1_3_12I1R15H : Ball := ⟨0, 0⟩
def CA1_3_12I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I1R16Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I1R16Mass : Ball := ⟨0, 0⟩
def CA1_3_12I1R16MassTerm : Ball := .exact 0
def CA1_3_12I1R16H : Ball := ⟨0, 0⟩
def CA1_3_12I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_3_12I1R0H
  | 1 => CA1_3_12I1R1H
  | 2 => CA1_3_12I1R2H
  | 3 => CA1_3_12I1R3H
  | 4 => CA1_3_12I1R4H
  | 5 => CA1_3_12I1R5H
  | 6 => CA1_3_12I1R6H
  | 7 => CA1_3_12I1R7H
  | 8 => CA1_3_12I1R8H
  | 9 => CA1_3_12I1R9H
  | 10 => CA1_3_12I1R10H
  | 11 => CA1_3_12I1R11H
  | 12 => CA1_3_12I1R12H
  | 13 => CA1_3_12I1R13H
  | 14 => CA1_3_12I1R14H
  | 15 => CA1_3_12I1R15H
  | 16 => CA1_3_12I1R16H
  | _ => (.exact 0)
def CA1_3_12I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA1_3_12I1Singleton : Ball := ⟨0, 0⟩
def CA1_3_12I1Group : Ball := ⟨(41106825155509773335602968297721 / 50000000000000000000000000000000), (168580732887 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_3_12I1H : Ball := ⟨(23883106584997771771810148882253 / 20000000000000000000000000000000), (500625606193 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_3_12I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_3_12I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(50082087363917606319814311 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1383654904061334667470463697 / 100000000000000000000000000000000), (222719 / 50000000000000000000000000000000)⟩ ⟨(-345346753921994490879955066322143 / 25000000000000000000000000000000), (444693295703 / 100000000000000000000000000000000)⟩ ⟨-20, 50082087363917606319814311, 47683715820312500000000000⟩,
   .log ⟨(19841937830486887774354987443 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(77700835228309911776401415997 / 25000000000000000000000000000000), (6827753 / 6250000000000000000000000000000)⟩ ⟨(-31327922057662556035001420397059 / 4000000000000000000000000000000), (137642855199 / 50000000000000000000000000000000)⟩ ⟨-12, 19841937830486887774354987443, 12207031250000000000000000000⟩,
   .log ⟨(421711917054587868544682972531 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1153087536871705885099378254267 / 50000000000000000000000000000000), (25115899 / 3125000000000000000000000000000)⟩ ⟨(-546860304506142847761138852694761 / 100000000000000000000000000000000), (95291206929 / 50000000000000000000000000000000)⟩ ⟨-8, 421711917054587868544682972531, 390625000000000000000000000000⟩,
   .log ⟨(21865753501080039753838898887 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(184284654016386747338159941657 / 100000000000000000000000000000000), (32411779 / 50000000000000000000000000000000)⟩ ⟨(-84280038191816334236063582536979 / 10000000000000000000000000000000), (59292307227 / 20000000000000000000000000000000)⟩ ⟨-13, 21865753501080039753838898887, 12207031250000000000000000000⟩,
   .log ⟨(13025852419139529812865781 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(753803492690890127858215639 / 100000000000000000000000000000000), (242749 / 100000000000000000000000000000000)⟩ ⟨(-1446745035248690017606643015894427 / 100000000000000000000000000000000), (93174008057 / 20000000000000000000000000000000)⟩ ⟨-21, 13025852419139529812865781, 11920928955078125000000000⟩,
   .log ⟨(64772240606369986691359369003 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(430664225608898488523443421233 / 50000000000000000000000000000000), (75438309 / 25000000000000000000000000000000)⟩ ⟨(-332445057926979506581545013063421 / 50000000000000000000000000000000), (29116757757 / 12500000000000000000000000000000)⟩ ⟨-10, 64772240606369986691359369003, 48828125000000000000000000000⟩,
   .log ⟨(293481350991874384936816552981 / 6250000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩ ⟨(14361909728850320975859891239579 / 100000000000000000000000000000000), (1193224211 / 20000000000000000000000000000000)⟩ ⟨(-152926132277140403151366427085823 / 50000000000000000000000000000000), (25410988509 / 20000000000000000000000000000000)⟩ ⟨-5, 293481350991874384936816552981, 195312500000000000000000000000⟩,
   .log ⟨(37553822772837218665908832711 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(872406659762958900834523798143 / 50000000000000000000000000000000), (318093259 / 50000000000000000000000000000000)⟩ ⟨(-580770874539284580934396306637859 / 100000000000000000000000000000000), (42351647499 / 20000000000000000000000000000000)⟩ ⟨-9, 37553822772837218665908832711, 24414062500000000000000000000⟩,
   .log ⟨(104664532945849915788600593467 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(28729012432813792031117488589 / 4000000000000000000000000000000), (243799363 / 100000000000000000000000000000000)⟩ ⟨(-686216515380555533295159876857727 / 100000000000000000000000000000000), (232934062423 / 100000000000000000000000000000000)⟩ ⟨-10, 104664532945849915788600593467, 97656250000000000000000000000⟩,
   .log ⟨(1060559171328409349906095801 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(42710138192577156114905265117 / 100000000000000000000000000000000), (14373269 / 100000000000000000000000000000000)⟩ ⟨(-1006783481469504726226195381566151 / 100000000000000000000000000000000), (135525281 / 40000000000000000000000000000)⟩ ⟨-15, 1060559171328409349906095801, 762939453125000000000000000⟩,
   .log ⟨(282263577762860498035221176179 / 5000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩ ⟨(8113248465540511183166549320663 / 50000000000000000000000000000000), (224143643 / 3125000000000000000000000000000)⟩ ⟨(-4491174818898312952583896580601 / 1562500000000000000000000000000), (127054942417 / 100000000000000000000000000000000)⟩ ⟨-5, 282263577762860498035221176179, 156250000000000000000000000000⟩,
   .log ⟨(133535008366915836782953 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2543545192383634783147461 / 25000000000000000000000000000000), (3301 / 100000000000000000000000000000000)⟩ ⟨(-1904777798339371339622526189435513 / 100000000000000000000000000000000), (614286103629 / 100000000000000000000000000000000)⟩ ⟨-28, 133535008366915836782953, 93132257461547851562500⟩,
   .log ⟨(17779922212048038852756426829 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(481478496401180235881466494277 / 20000000000000000000000000000000), (423567567 / 50000000000000000000000000000000)⟩ ⟨(-67699747313140740500717943457123 / 12500000000000000000000000000000), (47645603399 / 25000000000000000000000000000000)⟩ ⟨-8, 17779922212048038852756426829, 15625000000000000000000000000⟩,
   .log ⟨(16546391373770617564960410198009 / 50000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩ ⟨(914895457855740294931196810659 / 2500000000000000000000000000000), (21023008089 / 100000000000000000000000000000000)⟩ ⟨(-110585497126102667059592942702409 / 100000000000000000000000000000000), (12705494241 / 20000000000000000000000000000000)⟩ ⟨-2, 16546391373770617564960410198009, 12500000000000000000000000000000⟩]
def CA1_3_12I2PairEntropy : Ball := ⟨(128345077681340811422050948684389 / 50000000000000000000000000000000), (111730573419 / 100000000000000000000000000000000)⟩
def CA1_3_12I2PairMass : Ball := ⟨(24999999999999999999999999999999 / 25000000000000000000000000000000), (93 / 25000000000000000000000000000000)⟩
def CA1_3_12I2PairMassTermLogWitness : LogWitness := ⟨-1, 24999999999999999999999999999999, 12500000000000000000000000000000⟩
def CA1_3_12I2PairMassTermLog : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175823869 / 50000000000000000000000000000000)⟩
def CA1_3_12I2PairMassTerm : Ball := ⟨(1 / 25000000000000000000000000000000), (42351647739 / 100000000000000000000000000000000)⟩
def CA1_3_12I2PairH : Ball := ⟨(128345077681340811422050948684387 / 50000000000000000000000000000000), (77041110579 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_3_12I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R0Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R0Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R0MassTerm : Ball := .exact 0
def CA1_3_12I2R0H : Ball := ⟨0, 0⟩
def CA1_3_12I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R1Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R1Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R1MassTerm : Ball := .exact 0
def CA1_3_12I2R1H : Ball := ⟨0, 0⟩
def CA1_3_12I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R2Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R2Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R2MassTerm : Ball := .exact 0
def CA1_3_12I2R2H : Ball := ⟨0, 0⟩
def CA1_3_12I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R3Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R3Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R3MassTerm : Ball := .exact 0
def CA1_3_12I2R3H : Ball := ⟨0, 0⟩
def CA1_3_12I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(50082087363917606319814311 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1383654904061334667470463697 / 100000000000000000000000000000000), (222719 / 50000000000000000000000000000000)⟩ ⟨(-345346753921994490879955066322143 / 25000000000000000000000000000000), (444693295703 / 100000000000000000000000000000000)⟩ ⟨-20, 50082087363917606319814311, 47683715820312500000000000⟩,
   .log ⟨(19841937830486887774354987443 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(77700835228309911776401415997 / 25000000000000000000000000000000), (6827753 / 6250000000000000000000000000000)⟩ ⟨(-31327922057662556035001420397059 / 4000000000000000000000000000000), (137642855199 / 50000000000000000000000000000000)⟩ ⟨-12, 19841937830486887774354987443, 12207031250000000000000000000⟩,
   .log ⟨(421711917054587868544682972531 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1153087536871705885099378254267 / 50000000000000000000000000000000), (25115899 / 3125000000000000000000000000000)⟩ ⟨(-546860304506142847761138852694761 / 100000000000000000000000000000000), (95291206929 / 50000000000000000000000000000000)⟩ ⟨-8, 421711917054587868544682972531, 390625000000000000000000000000⟩,
   .log ⟨(21865753501080039753838898887 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(184284654016386747338159941657 / 100000000000000000000000000000000), (32411779 / 50000000000000000000000000000000)⟩ ⟨(-84280038191816334236063582536979 / 10000000000000000000000000000000), (59292307227 / 20000000000000000000000000000000)⟩ ⟨-13, 21865753501080039753838898887, 12207031250000000000000000000⟩,
   .log ⟨(13025852419139529812865781 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(753803492690890127858215639 / 100000000000000000000000000000000), (242749 / 100000000000000000000000000000000)⟩ ⟨(-1446745035248690017606643015894427 / 100000000000000000000000000000000), (93174008057 / 20000000000000000000000000000000)⟩ ⟨-21, 13025852419139529812865781, 11920928955078125000000000⟩]
def CA1_3_12I2R4Entropy : Ball := ⟨(3299872176903478118549086862857 / 100000000000000000000000000000000), (230595521 / 20000000000000000000000000000000)⟩
def CA1_3_12I2R4Mass : Ball := ⟨(109012721427565545538862288089 / 20000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CA1_3_12I2R4MassTermLogWitness : LogWitness := ⟨-8, 109012721427565545538862288089, 78125000000000000000000000000⟩
def CA1_3_12I2R4MassTermLog : Ball := ⟨(-130300574169311717901852204431171 / 25000000000000000000000000000000), (190582414981 / 100000000000000000000000000000000)⟩
def CA1_3_12I2R4MassTerm : Ball := ⟨(1420442019377102114439407222067 / 50000000000000000000000000000000), (1038795439 / 100000000000000000000000000000000)⟩
def CA1_3_12I2R4H : Ball := ⟨(458988138149273889670272418723 / 100000000000000000000000000000000), (547943261 / 25000000000000000000000000000000)⟩
def CA1_3_12I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(7993584464142905026220688119 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(75413763494681339490575140203 / 100000000000000000000000000000000), (25390621 / 100000000000000000000000000000000)⟩ ⟨(-471714309350000836969003265641811 / 50000000000000000000000000000000), (158818683877 / 50000000000000000000000000000000)⟩ ⟨-14, 7993584464142905026220688119, 6103515625000000000000000000⟩,
   .log ⟨(663629216363104967231169239211 / 12500000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩ ⟨(3896512666233792155067174842187 / 25000000000000000000000000000000), (1686347451 / 25000000000000000000000000000000)⟩ ⟨(-36697004235926129642552998593163 / 12500000000000000000000000000000), (127054942437 / 100000000000000000000000000000000)⟩ ⟨-5, 663629216363104967231169239211, 390625000000000000000000000000⟩,
   .log ⟨(6122612934429716628887432669 / 3125000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(244324607253148222856294098721 / 20000000000000000000000000000000), (207442203 / 50000000000000000000000000000000)⟩ ⟨(-38970003791833119778586138716087 / 6250000000000000000000000000000), (4235164757 / 2000000000000000000000000000000)⟩ ⟨-9, 6122612934429716628887432669, 6103515625000000000000000000⟩]
def CA1_3_12I2R5Entropy : Ball := ⟨(4220771866173897768510186250639 / 12500000000000000000000000000000), (7185664831 / 50000000000000000000000000000000)⟩
def CA1_3_12I2R5Mass : Ball := ⟨(1102590185854146714999994489443 / 10000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
def CA1_3_12I2R5MassTermLogWitness : LogWitness := ⟨-4, 1102590185854146714999994489443, 625000000000000000000000000000⟩
def CA1_3_12I2R5MassTermLog : Ball := ⟨(-220492296677246871607408894108321 / 100000000000000000000000000000000), (26469779699 / 25000000000000000000000000000000)⟩
def CA1_3_12I2R5MassTerm : Ball := ⟨(24311264237277328434595883551767 / 100000000000000000000000000000000), (11674127821 / 100000000000000000000000000000000)⟩
def CA1_3_12I2R5H : Ball := ⟨(1890982138422770742697121290669 / 20000000000000000000000000000000), (26045457483 / 100000000000000000000000000000000)⟩
def CA1_3_12I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(67735000303981522447707694109 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(400383487869694504550284853249 / 25000000000000000000000000000000), (71717223 / 12500000000000000000000000000000)⟩ ⟨(-2364411226531932936982137556031 / 400000000000000000000000000000), (211758237567 / 100000000000000000000000000000000)⟩ ⟨-9, 67735000303981522447707694109, 48828125000000000000000000000⟩,
   .log ⟨(17070295505220172527691583 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(266012234051902568026482893 / 100000000000000000000000000000000), (21693 / 25000000000000000000000000000000)⟩ ⟨(-1558334089591799040572900800822269 / 100000000000000000000000000000000), (508225626521 / 100000000000000000000000000000000)⟩ ⟨-23, 17070295505220172527691583, 11920928955078125000000000⟩,
   .log ⟨(28410315532777598125582754633957 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩ ⟨(1787602457521536374185190330329 / 5000000000000000000000000000000), (4512088759 / 25000000000000000000000000000000)⟩ ⟨(-62920894189265184004983717878739 / 50000000000000000000000000000000), (63527471143 / 100000000000000000000000000000000)⟩ ⟨-2, 28410315532777598125582754633957, 25000000000000000000000000000000⟩]
def CA1_3_12I2R6Entropy : Ball := ⟨(19477824538928193662621069199179 / 50000000000000000000000000000000), (4799001037 / 25000000000000000000000000000000)⟩
def CA1_3_12I2R6Mass : Ball := ⟨(5790445935160092149101894313999 / 20000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
def CA1_3_12I2R6MassTermLogWitness : LogWitness := ⟨-2, 5790445935160092149101894313999, 5000000000000000000000000000000⟩
def CA1_3_12I2R6MassTermLog : Ball := ⟨(-123952296677246871607408932297361 / 100000000000000000000000000000000), (31763735581 / 50000000000000000000000000000000)⟩
def CA1_3_12I2R6MassTerm : Ball := ⟨(35886953622426097212588200661081 / 100000000000000000000000000000000), (91963097 / 500000000000000000000000000000)⟩
def CA1_3_12I2R6H : Ball := ⟨(3068695455430290112653937737277 / 100000000000000000000000000000000), (9397155887 / 25000000000000000000000000000000)⟩
def CA1_3_12I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R7Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R7Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R7MassTerm : Ball := .exact 0
def CA1_3_12I2R7H : Ball := ⟨0, 0⟩
def CA1_3_12I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R8Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R8Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R8MassTerm : Ball := .exact 0
def CA1_3_12I2R8H : Ball := ⟨0, 0⟩
def CA1_3_12I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R9Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R9Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R9MassTerm : Ball := .exact 0
def CA1_3_12I2R9H : Ball := ⟨0, 0⟩
def CA1_3_12I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R10Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R10Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R10MassTerm : Ball := .exact 0
def CA1_3_12I2R10H : Ball := ⟨0, 0⟩
def CA1_3_12I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R11Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R11Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R11MassTerm : Ball := .exact 0
def CA1_3_12I2R11H : Ball := ⟨0, 0⟩
def CA1_3_12I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R12Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R12Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R12MassTerm : Ball := .exact 0
def CA1_3_12I2R12H : Ball := ⟨0, 0⟩
def CA1_3_12I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R13Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R13Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R13MassTerm : Ball := .exact 0
def CA1_3_12I2R13H : Ball := ⟨0, 0⟩
def CA1_3_12I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R14Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R14Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R14MassTerm : Ball := .exact 0
def CA1_3_12I2R14H : Ball := ⟨0, 0⟩
def CA1_3_12I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R15Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R15Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R15MassTerm : Ball := .exact 0
def CA1_3_12I2R15H : Ball := ⟨0, 0⟩
def CA1_3_12I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_3_12I2R16Entropy : Ball := ⟨0, 0⟩
def CA1_3_12I2R16Mass : Ball := ⟨0, 0⟩
def CA1_3_12I2R16MassTerm : Ball := .exact 0
def CA1_3_12I2R16H : Ball := ⟨0, 0⟩
def CA1_3_12I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_3_12I2R0H
  | 1 => CA1_3_12I2R1H
  | 2 => CA1_3_12I2R2H
  | 3 => CA1_3_12I2R3H
  | 4 => CA1_3_12I2R4H
  | 5 => CA1_3_12I2R5H
  | 6 => CA1_3_12I2R6H
  | 7 => CA1_3_12I2R7H
  | 8 => CA1_3_12I2R8H
  | 9 => CA1_3_12I2R9H
  | 10 => CA1_3_12I2R10H
  | 11 => CA1_3_12I2R11H
  | 12 => CA1_3_12I2R12H
  | 13 => CA1_3_12I2R13H
  | 14 => CA1_3_12I2R14H
  | 15 => CA1_3_12I2R15H
  | 16 => CA1_3_12I2R16H
  | _ => (.exact 0)
def CA1_3_12I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)
def CA1_3_12I2Singleton : Ball := ⟨(56736239042590527820128214119539 / 100000000000000000000000000000000), (47869683083 / 100000000000000000000000000000000)⟩
def CA1_3_12I2Group : Ball := ⟨(17429708332070986383984507682221 / 25000000000000000000000000000000), (56847768579 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_3_12I2H : Ball := ⟨(58626244353056865886112917955503 / 50000000000000000000000000000000), (190736647737 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_4_11I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 4 11)) (fun u => (stageALaw (shape 1 4 11) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_4_11I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 4 11)) A1_4_11Law ((Equiv.refl (Fin 3)) 0) a
def CA1_4_11I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (17 / 20000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823827 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329507 / 20000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
def CA1_4_11I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I0Certificates (CA1_4_11I0CertificateIndex a)).input
def CA1_4_11I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_4_11I0Certificates (CA1_4_11I0CertificateIndex a)).output
def CA1_4_11I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823827 / 50000000000000000000000000000000)⟩
def CA1_4_11I0Mass : Ball := ⟨1, (17 / 10000000000000000000000000000000)⟩
def CA1_4_11I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_4_11I0MassTermLog : Ball := ⟨0, (5293955963 / 25000000000000000000000000000000)⟩
def CA1_4_11I0MassTerm : Ball := ⟨0, (21175823853 / 100000000000000000000000000000000)⟩
def CA1_4_11I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471507 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_4_11I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(11664977189338182042318946841 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(34046911231915542261283174941 / 2000000000000000000000000000000), (123507753 / 20000000000000000000000000000000)⟩ ⟨(-583745869010948486140178427050387 / 100000000000000000000000000000000), (42351647503 / 20000000000000000000000000000000)⟩ ⟨-9, 11664977189338182042318946841, 7812500000000000000000000000⟩,
   .log ⟨(1432041275913219638258759429603 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(6080546489257217219713937617783 / 100000000000000000000000000000000), (1212986169 / 50000000000000000000000000000000)⟩ ⟨(-106151732347582358530726446483411 / 25000000000000000000000000000000), (84703295081 / 50000000000000000000000000000000)⟩ ⟨-7, 1432041275913219638258759429603, 781250000000000000000000000000⟩,
   .log ⟨(72646759446330440509803789261 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(18987449595068623982609898379 / 2000000000000000000000000000000), (338438109 / 100000000000000000000000000000000)⟩ ⟨(-130683390007891982652220310067249 / 20000000000000000000000000000000), (232934061889 / 100000000000000000000000000000000)⟩ ⟨-10, 72646759446330440509803789261, 48828125000000000000000000000⟩,
   .log ⟨(15442796055875565115581455813 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(135522624707020123450557332547 / 100000000000000000000000000000000), (1144549 / 2500000000000000000000000000000)⟩ ⟨(-27424321390834174728384894737699 / 3125000000000000000000000000000), (296461538037 / 100000000000000000000000000000000)⟩ ⟨-13, 15442796055875565115581455813, 12207031250000000000000000000⟩,
   .log ⟨(858584694521010948985622169 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(8633891199949041081299899313 / 20000000000000000000000000000000), (7272501 / 50000000000000000000000000000000)⟩ ⟨(-201119150039489921776711304601741 / 20000000000000000000000000000000), (338813202221 / 100000000000000000000000000000000)⟩ ⟨-15, 858584694521010948985622169, 610351562500000000000000000⟩,
   .log ⟨(137888861593042178984912356271 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1625249205084484155605066075167 / 100000000000000000000000000000000), (583982059 / 100000000000000000000000000000000)⟩ ⟨(-589333027449728988868004776662241 / 100000000000000000000000000000000), (42351647511 / 20000000000000000000000000000000)⟩ ⟨-9, 137888861593042178984912356271, 97656250000000000000000000000⟩,
   .log ⟨(4904076801820583064126827285721 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩ ⟨(7393149139095214348214785328203 / 50000000000000000000000000000000), (3115436013 / 50000000000000000000000000000000)⟩ ⟨(-301510332642041467290155459800419 / 100000000000000000000000000000000), (63527471263 / 50000000000000000000000000000000)⟩ ⟨-5, 4904076801820583064126827285721, 3125000000000000000000000000000⟩,
   .log ⟨(482992777307967784909064602021 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1287881830273238117754698756549 / 50000000000000000000000000000000), (115062413 / 12500000000000000000000000000000)⟩ ⟨(-533292376524319641417441294797923 / 100000000000000000000000000000000), (4764560339 / 2500000000000000000000000000000)⟩ ⟨-8, 482992777307967784909064602021, 390625000000000000000000000000⟩,
   .log ⟨(1593584057043965232702681183837 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(6596138559921701501728336143231 / 100000000000000000000000000000000), (2362181893 / 100000000000000000000000000000000)⟩ ⟨(-82783691651098405640700492998221 / 20000000000000000000000000000000), (74115383141 / 50000000000000000000000000000000)⟩ ⟨-6, 1593584057043965232702681183837, 1562500000000000000000000000000⟩,
   .log ⟨(150556659524634014410605017567 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(978405396237944661934025336967 / 100000000000000000000000000000000), (87674439 / 25000000000000000000000000000000)⟩ ⟨(-649858597638358468854867514767903 / 100000000000000000000000000000000), (232934061841 / 100000000000000000000000000000000)⟩ ⟨-10, 150556659524634014410605017567, 97656250000000000000000000000⟩,
   .log ⟨(5469334159468324195833199519871 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩ ⟨(397348945626970979222896666589 / 2500000000000000000000000000000), (217158107 / 3125000000000000000000000000000)⟩ ⟨(-58120266056751215685901505382233 / 20000000000000000000000000000000), (25410988489 / 20000000000000000000000000000000)⟩ ⟨-5, 5469334159468324195833199519871, 3125000000000000000000000000000⟩,
   .log ⟨(2786939030381170203143835961 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(123719799583554885385098337861 / 100000000000000000000000000000000), (41311021 / 100000000000000000000000000000000)⟩ ⟨(-13872724501107235369479078733497 / 1562500000000000000000000000000), (148230769369 / 50000000000000000000000000000000)⟩ ⟨-13, 2786939030381170203143835961, 2441406250000000000000000000⟩,
   .log ⟨(25388704041102548051955395779 / 5000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2682514024359832963349767317973 / 100000000000000000000000000000000), (241932029 / 25000000000000000000000000000000)⟩ ⟨(-52828888391014939480636882266497 / 10000000000000000000000000000000), (190582413737 / 100000000000000000000000000000000)⟩ ⟨-8, 25388704041102548051955395779, 19531250000000000000000000000⟩,
   .log ⟨(18494448703007788912267876648421 / 100000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩ ⟨(31213073105727158527369908172863 / 100000000000000000000000000000000), (7832703747 / 50000000000000000000000000000000)⟩ ⟨(-168769956904154242112485802872997 / 100000000000000000000000000000000), (84703294931 / 100000000000000000000000000000000)⟩ ⟨-3, 18494448703007788912267876648421, 12500000000000000000000000000000⟩]
def CA1_4_11I1PairEntropy : Ball := ⟨(315335814479301831357444261227387 / 100000000000000000000000000000000), (13046053457 / 10000000000000000000000000000000)⟩
def CA1_4_11I1PairMass : Ball := ⟨(100000000000000000000000000000001 / 100000000000000000000000000000000), (419 / 100000000000000000000000000000000)⟩
def CA1_4_11I1PairMassTermLogWitness : LogWitness := ⟨0, 100000000000000000000000000000001, 100000000000000000000000000000000⟩
def CA1_4_11I1PairMassTermLog : Ball := ⟨(1 / 100000000000000000000000000000000), (21175824101 / 100000000000000000000000000000000)⟩
def CA1_4_11I1PairMassTerm : Ball := ⟨(-1 / 100000000000000000000000000000000), (10587912051 / 50000000000000000000000000000000)⟩
def CA1_4_11I1PairH : Ball := ⟨(78833953619825457839361065306847 / 25000000000000000000000000000000), (9477272417 / 6250000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(11649529080832680885096798031 / 500000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(437945679318023839001681305581 / 5000000000000000000000000000000), (1726818641 / 50000000000000000000000000000000)⟩ ⟨(-375934234147360499072534355300923 / 100000000000000000000000000000000), (148230766209 / 100000000000000000000000000000000)⟩ ⟨-6, 11649529080832680885096798031, 7812500000000000000000000000⟩]
def CA1_4_11I1R0Entropy : Ball := ⟨(437945679318023839001681305581 / 5000000000000000000000000000000), (1726818641 / 50000000000000000000000000000000)⟩
def CA1_4_11I1R0Mass : Ball := ⟨(11649529080832680885096798031 / 500000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
def CA1_4_11I1R0MassTermLogWitness : LogWitness := ⟨-6, 11649529080832680885096798031, 7812500000000000000000000000⟩
def CA1_4_11I1R0MassTermLog : Ball := ⟨(-375934234147360499072534355300923 / 100000000000000000000000000000000), (148230766209 / 100000000000000000000000000000000)⟩
def CA1_4_11I1R0MassTerm : Ball := ⟨(437945679318023839001681305581 / 5000000000000000000000000000000), (1726818641 / 50000000000000000000000000000000)⟩
def CA1_4_11I1R0H : Ball := ⟨0, (1726818641 / 25000000000000000000000000000000)⟩
def CA1_4_11I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1415711825578658801751429150071 / 12500000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩ ⟨(3083556523177856507528997814397 / 12500000000000000000000000000000), (2398309139 / 20000000000000000000000000000000)⟩ ⟨(-217809618275773177236479388037759 / 100000000000000000000000000000000), (105879118671 / 100000000000000000000000000000000)⟩ ⟨-4, 1415711825578658801751429150071, 781250000000000000000000000000⟩]
def CA1_4_11I1R1Entropy : Ball := ⟨(3083556523177856507528997814397 / 6250000000000000000000000000000), (2398309139 / 10000000000000000000000000000000)⟩
def CA1_4_11I1R1Mass : Ball := ⟨(1415711825578658801751429150071 / 6250000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
def CA1_4_11I1R1MassTermLogWitness : LogWitness := ⟨-3, 1415711825578658801751429150071, 781250000000000000000000000000⟩
def CA1_4_11I1R1MassTermLog : Ball := ⟨(-148494900219778646294756194987429 / 100000000000000000000000000000000), (21175823747 / 25000000000000000000000000000000)⟩
def CA1_4_11I1R1MassTerm : Ball := ⟨(3363615780468217751509662805569 / 10000000000000000000000000000000), (4796618277 / 25000000000000000000000000000000)⟩
def CA1_4_11I1R1H : Ball := ⟨(7850373283081763302683668487331 / 50000000000000000000000000000000), (21584782249 / 50000000000000000000000000000000)⟩
def CA1_4_11I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(223940389815138067251494298067 / 2500000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(10805867789225661561870460519403 / 50000000000000000000000000000000), (948424451 / 10000000000000000000000000000000)⟩ ⟨(-15079163195708386909004244644217 / 6250000000000000000000000000000), (21175823741 / 20000000000000000000000000000000)⟩ ⟨-4, 223940389815138067251494298067, 156250000000000000000000000000⟩,
   .log ⟨(209189197543782672972939077581 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(400253574441421611996235844733 / 10000000000000000000000000000000), (354380291 / 25000000000000000000000000000000)⟩ ⟨(-478339200997281105739975070413043 / 100000000000000000000000000000000), (169406589941 / 100000000000000000000000000000000)⟩ ⟨-7, 209189197543782672972939077581, 195312500000000000000000000000⟩,
   .log ⟨(15224332591794269613006245759661 / 50000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩ ⟨(36207361219350480702515376712927 / 100000000000000000000000000000000), (9671633527 / 50000000000000000000000000000000)⟩ ⟨(-11891280291283773157913279044349 / 10000000000000000000000000000000), (63527471189 / 100000000000000000000000000000000)⟩ ⟨-2, 15224332591794269613006245759661, 12500000000000000000000000000000⟩]
def CA1_4_11I1R2Entropy : Ball := ⟨(87435903865081559189921935685199 / 100000000000000000000000000000000), (20573399201 / 50000000000000000000000000000000)⟩
def CA1_4_11I1R2Mass : Ball := ⟨(5003740994914984598991554798533 / 10000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
def CA1_4_11I1R2MassTermLogWitness : LogWitness := ⟨-1, 5003740994914984598991554798533, 5000000000000000000000000000000⟩
def CA1_4_11I1R2MassTermLog : Ball := ⟨(-34619963066913570366131252995201 / 50000000000000000000000000000000), (42351647571 / 100000000000000000000000000000000)⟩
def CA1_4_11I1R2MassTerm : Ball := ⟨(34645865688071626023959378116581 / 100000000000000000000000000000000), (21191667587 / 100000000000000000000000000000000)⟩
def CA1_4_11I1R2H : Ball := ⟨(26395019088504966582981278784309 / 50000000000000000000000000000000), (62338465989 / 100000000000000000000000000000000)⟩
def CA1_4_11I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(137888861593042178984912356271 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2868189307593617450192719616833 / 100000000000000000000000000000000), (1051167699 / 100000000000000000000000000000000)⟩ ⟨(-520018309393734457926281583611911 / 100000000000000000000000000000000), (19058241369 / 10000000000000000000000000000000)⟩ ⟨-8, 137888861593042178984912356271, 97656250000000000000000000000⟩,
   .log ⟨(4904076801820583064126827285721 / 50000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩ ⟨(22774102539518115754746011166397 / 100000000000000000000000000000000), (2076957341 / 20000000000000000000000000000000)⟩ ⟨(-232195614586046936348432266750089 / 100000000000000000000000000000000), (105879118833 / 100000000000000000000000000000000)⟩ ⟨-4, 4904076801820583064126827285721, 3125000000000000000000000000000⟩,
   .log ⟨(482992777307967784909064602021 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(4481957157449281667465669218783 / 100000000000000000000000000000000), (818221603 / 50000000000000000000000000000000)⟩ ⟨(-463977658468325110475718101747593 / 100000000000000000000000000000000), (169406589877 / 100000000000000000000000000000000)⟩ ⟨-7, 482992777307967784909064602021, 390625000000000000000000000000⟩]
def CA1_4_11I1R3Entropy : Ball := ⟨(30124249004561014872404400002013 / 50000000000000000000000000000000), (1307239761 / 5000000000000000000000000000000)⟩
def CA1_4_11I1R3Mass : Ball := ⟨(1415711825578658801751429150071 / 6250000000000000000000000000000), (3 / 3125000000000000000000000000000)⟩
def CA1_4_11I1R3MassTermLogWitness : LogWitness := ⟨-3, 1415711825578658801751429150071, 781250000000000000000000000000⟩
def CA1_4_11I1R3MassTermLog : Ball := ⟨(-148494900219778646294756194987429 / 100000000000000000000000000000000), (21175823789 / 25000000000000000000000000000000)⟩
def CA1_4_11I1R3MassTerm : Ball := ⟨(3363615780468217751509662805569 / 10000000000000000000000000000000), (9593236601 / 50000000000000000000000000000000)⟩
def CA1_4_11I1R3H : Ball := ⟨(1663271262777490764357010746771 / 6250000000000000000000000000000), (22665634211 / 50000000000000000000000000000000)⟩
def CA1_4_11I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(858584694521010948985622169 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(8633891199949041081299899313 / 20000000000000000000000000000000), (7272501 / 50000000000000000000000000000000)⟩ ⟨(-201119150039489921776711304601741 / 20000000000000000000000000000000), (338813202221 / 100000000000000000000000000000000)⟩ ⟨-15, 858584694521010948985622169, 610351562500000000000000000⟩,
   .log ⟨(11664977189338182042318946841 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(34046911231915542261283174941 / 2000000000000000000000000000000), (123507753 / 20000000000000000000000000000000)⟩ ⟨(-583745869010948486140178427050387 / 100000000000000000000000000000000), (42351647503 / 20000000000000000000000000000000)⟩ ⟨-9, 11664977189338182042318946841, 7812500000000000000000000000⟩,
   .log ⟨(1432041275913219638258759429603 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(6080546489257217219713937617783 / 100000000000000000000000000000000), (1212986169 / 50000000000000000000000000000000)⟩ ⟨(-106151732347582358530726446483411 / 25000000000000000000000000000000), (84703295081 / 50000000000000000000000000000000)⟩ ⟨-7, 1432041275913219638258759429603, 781250000000000000000000000000⟩,
   .log ⟨(72646759446330440509803789261 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(18987449595068623982609898379 / 2000000000000000000000000000000), (338438109 / 100000000000000000000000000000000)⟩ ⟨(-130683390007891982652220310067249 / 20000000000000000000000000000000), (232934061889 / 100000000000000000000000000000000)⟩ ⟨-10, 72646759446330440509803789261, 48828125000000000000000000000⟩,
   .log ⟨(15442796055875565115581455813 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(135522624707020123450557332547 / 100000000000000000000000000000000), (1144549 / 2500000000000000000000000000000)⟩ ⟨(-27424321390834174728384894737699 / 3125000000000000000000000000000), (296461538037 / 100000000000000000000000000000000)⟩ ⟨-13, 15442796055875565115581455813, 12207031250000000000000000000⟩]
def CA1_4_11I1R4Entropy : Ball := ⟨(580292205433107218918340063773 / 5000000000000000000000000000000), (88255961 / 2000000000000000000000000000000)⟩
def CA1_4_11I1R4Mass : Ball := ⟨(11649529080832680885096798031 / 500000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def CA1_4_11I1R4MassTermLogWitness : LogWitness := ⟨-6, 11649529080832680885096798031, 7812500000000000000000000000⟩
def CA1_4_11I1R4MassTermLog : Ball := ⟨(-375934234147360499072534355300923 / 100000000000000000000000000000000), (74115383341 / 50000000000000000000000000000000)⟩
def CA1_4_11I1R4MassTerm : Ball := ⟨(437945679318023839001681305581 / 5000000000000000000000000000000), (1726818667 / 50000000000000000000000000000000)⟩
def CA1_4_11I1R4H : Ball := ⟨(8896657882192711244791172387 / 312500000000000000000000000000), (983304423 / 12500000000000000000000000000000)⟩
def CA1_4_11I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R5Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R5Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R5MassTerm : Ball := .exact 0
def CA1_4_11I1R5H : Ball := ⟨0, 0⟩
def CA1_4_11I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R6Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R6Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R6MassTerm : Ball := .exact 0
def CA1_4_11I1R6H : Ball := ⟨0, 0⟩
def CA1_4_11I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R7Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R7Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R7MassTerm : Ball := .exact 0
def CA1_4_11I1R7H : Ball := ⟨0, 0⟩
def CA1_4_11I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R8Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R8Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R8MassTerm : Ball := .exact 0
def CA1_4_11I1R8H : Ball := ⟨0, 0⟩
def CA1_4_11I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R9Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R9Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R9MassTerm : Ball := .exact 0
def CA1_4_11I1R9H : Ball := ⟨0, 0⟩
def CA1_4_11I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R10Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R10Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R10MassTerm : Ball := .exact 0
def CA1_4_11I1R10H : Ball := ⟨0, 0⟩
def CA1_4_11I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R11Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R11Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R11MassTerm : Ball := .exact 0
def CA1_4_11I1R11H : Ball := ⟨0, 0⟩
def CA1_4_11I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R12Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R12Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R12MassTerm : Ball := .exact 0
def CA1_4_11I1R12H : Ball := ⟨0, 0⟩
def CA1_4_11I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R13Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R13Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R13MassTerm : Ball := .exact 0
def CA1_4_11I1R13H : Ball := ⟨0, 0⟩
def CA1_4_11I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R14Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R14Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R14MassTerm : Ball := .exact 0
def CA1_4_11I1R14H : Ball := ⟨0, 0⟩
def CA1_4_11I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R15Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R15Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R15MassTerm : Ball := .exact 0
def CA1_4_11I1R15H : Ball := ⟨0, 0⟩
def CA1_4_11I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I1R16Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I1R16Mass : Ball := ⟨0, 0⟩
def CA1_4_11I1R16MassTerm : Ball := .exact 0
def CA1_4_11I1R16H : Ball := ⟨0, 0⟩
def CA1_4_11I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_4_11I1R0H
  | 1 => CA1_4_11I1R1H
  | 2 => CA1_4_11I1R2H
  | 3 => CA1_4_11I1R3H
  | 4 => CA1_4_11I1R4H
  | 5 => CA1_4_11I1R5H
  | 6 => CA1_4_11I1R6H
  | 7 => CA1_4_11I1R7H
  | 8 => CA1_4_11I1R8H
  | 9 => CA1_4_11I1R9H
  | 10 => CA1_4_11I1R10H
  | 11 => CA1_4_11I1R11H
  | 12 => CA1_4_11I1R12H
  | 13 => CA1_4_11I1R13H
  | 14 => CA1_4_11I1R14H
  | 15 => CA1_4_11I1R15H
  | 16 => CA1_4_11I1R16H
  | _ => (.exact 0)
def CA1_4_11I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA1_4_11I1Singleton : Ball := ⟨0, 0⟩
def CA1_4_11I1Group : Ball := ⟨(3060939233434843112480476301733 / 3125000000000000000000000000000), (165613008857 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I1H : Ball := ⟨(29858925884867968039673444479119 / 25000000000000000000000000000000), (241431188193 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_4_11I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(61436712352474830488612391 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7372459591722180802103669681 / 100000000000000000000000000000000), (1235931 / 50000000000000000000000000000000)⟩ ⟨(-1200008807343871317001204918543989 / 100000000000000000000000000000000), (201170406373 / 50000000000000000000000000000000)⟩ ⟨-18, 61436712352474830488612391, 38146972656250000000000000⟩,
   .log ⟨(20890993075933606986049075471 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(44255518130701293310819022579 / 25000000000000000000000000000000), (7741721 / 12500000000000000000000000000000)⟩ ⟨(-847360735219113820046267163931973 / 100000000000000000000000000000000), (74115384087 / 25000000000000000000000000000000)⟩ ⟨-13, 20890993075933606986049075471, 12207031250000000000000000000⟩,
   .log ⟨(12647475172166827455070439 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2187112567878730349464064949 / 10000000000000000000000000000000), (3557 / 48828125000000000000000000000)⟩ ⟨(-1080804932459902736691495491288357 / 100000000000000000000000000000000), (359989052027 / 100000000000000000000000000000000)⟩ ⟨-16, 12647475172166827455070439, 9536743164062500000000000⟩,
   .log ⟨(247638212185665772009484323 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(26264822769214557249286875369 / 100000000000000000000000000000000), (2228679 / 25000000000000000000000000000000)⟩ ⟨(-530306339587095105926029728199953 / 50000000000000000000000000000000), (22499315187 / 6250000000000000000000000000000)⟩ ⟨-16, 247638212185665772009484323, 152587890625000000000000000⟩,
   .log ⟨(69447984709920411412613034571 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(51096815302679477193995154419 / 3125000000000000000000000000000), (294123663 / 50000000000000000000000000000000)⟩ ⟨(-588605305292672876755862321341519 / 100000000000000000000000000000000), (211758237549 / 100000000000000000000000000000000)⟩ ⟨-9, 69447984709920411412613034571, 48828125000000000000000000000⟩,
   .log ⟨(530086454874906741118217258983 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(163418910837898166576723149541 / 2000000000000000000000000000000), (628600979 / 20000000000000000000000000000000)⟩ ⟨(-38535909882016987914182026336639 / 10000000000000000000000000000000), (37057691563 / 25000000000000000000000000000000)⟩ ⟨-6, 530086454874906741118217258983, 390625000000000000000000000000⟩,
   .log ⟨(36353911613803057996403498157 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(475024151536006995650968084953 / 50000000000000000000000000000000), (169361289 / 50000000000000000000000000000000)⟩ ⟨(-653332929592708737962053091580513 / 100000000000000000000000000000000), (582335153 / 250000000000000000000000000000)⟩ ⟨-10, 36353911613803057996403498157, 24414062500000000000000000000⟩,
   .log ⟨(246603819537866388940074677 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(74550597575614554248039379723 / 100000000000000000000000000000000), (12532899 / 50000000000000000000000000000000)⟩ ⟨(-472358088087160571858308357214297 / 50000000000000000000000000000000), (79409341979 / 25000000000000000000000000000000)⟩ ⟨-14, 246603819537866388940074677, 190734863281250000000000000⟩,
   .log ⟨(4104145260099889041045443621 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(19305449453087283873116811937 / 25000000000000000000000000000000), (814769 / 3125000000000000000000000000000)⟩ ⟨(-470389039120350646964104214669537 / 50000000000000000000000000000000), (317637367427 / 100000000000000000000000000000000)⟩ ⟨-14, 4104145260099889041045443621, 3051757812500000000000000000⟩,
   .log ⟨(600828099618234061392902613529 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(8960323050853044634501556597273 / 100000000000000000000000000000000), (178122421 / 5000000000000000000000000000000)⟩ ⟨(-372832223415750294598111936759829 / 100000000000000000000000000000000), (148230766197 / 100000000000000000000000000000000)⟩ ⟨-6, 600828099618234061392902613529, 390625000000000000000000000000⟩,
   .log ⟨(93456021197746811342512607853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(26075854183003606395757775073 / 4000000000000000000000000000000), (59370249 / 25000000000000000000000000000000)⟩ ⟨(-348771725042584591538500912392203 / 50000000000000000000000000000000), (127054942633 / 50000000000000000000000000000000)⟩ ⟨-11, 93456021197746811342512607853, 48828125000000000000000000000⟩,
   .log ⟨(284072886806370408119373327 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(3628022640385256911008687731 / 100000000000000000000000000000000), (120311 / 10000000000000000000000000000000)⟩ ⟨(-63857249475170566733952604570697 / 5000000000000000000000000000000), (211758412841 / 50000000000000000000000000000000)⟩ ⟨-19, 284072886806370408119373327, 190734863281250000000000000⟩,
   .log ⟨(94239156817735785123068899863 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(591251052228123992924326317639 / 50000000000000000000000000000000), (87806041 / 20000000000000000000000000000000)⟩ ⟨(-313697125586362789199873511438207 / 50000000000000000000000000000000), (116467030787 / 50000000000000000000000000000000)⟩ ⟨-10, 94239156817735785123068899863, 48828125000000000000000000000⟩,
   .log ⟨(3477934774897537944856216767 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(8323862696055864315472366073 / 12500000000000000000000000000000), (5523613 / 25000000000000000000000000000000)⟩ ⟨(-239333490556938070483060085432873 / 25000000000000000000000000000000), (15881868481 / 5000000000000000000000000000000)⟩ ⟨-14, 3477934774897537944856216767, 3051757812500000000000000000⟩,
   .log ⟨(503911615790262895556819127379 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2665956788363537793012590795623 / 100000000000000000000000000000000), (960366937 / 100000000000000000000000000000000)⟩ ⟨(-132263114444317408776508448138551 / 25000000000000000000000000000000), (95291206871 / 50000000000000000000000000000000)⟩ ⟨-8, 503911615790262895556819127379, 390625000000000000000000000000⟩,
   .log ⟨(15037030684492895073999860934781 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩ ⟨(28489975068915472258197911036001 / 100000000000000000000000000000000), (12736860571 / 100000000000000000000000000000000)⟩ ⟨(-23683178935632614221075250605851 / 12500000000000000000000000000000), (84703295077 / 100000000000000000000000000000000)⟩ ⟨-3, 15037030684492895073999860934781, 12500000000000000000000000000000⟩,
   .log ⟨(527266867202792760023966491371 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(960062586291216178629491724419 / 20000000000000000000000000000000), (1786449657 / 100000000000000000000000000000000)⟩ ⟨(-227603573733082047463521721259441 / 50000000000000000000000000000000), (169406589843 / 100000000000000000000000000000000)⟩ ⟨-7, 527266867202792760023966491371, 390625000000000000000000000000⟩]
def CA1_4_11I2PairEntropy : Ball := ⟨(71515153480864000296843130640223 / 25000000000000000000000000000000), (14585933523 / 12500000000000000000000000000000)⟩
def CA1_4_11I2PairMass : Ball := ⟨(24999999999999999999999999999999 / 25000000000000000000000000000000), (113 / 25000000000000000000000000000000)⟩
def CA1_4_11I2PairMassTermLogWitness : LogWitness := ⟨-1, 24999999999999999999999999999999, 12500000000000000000000000000000⟩
def CA1_4_11I2PairMassTermLog : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175823909 / 50000000000000000000000000000000)⟩
def CA1_4_11I2PairMassTerm : Ball := ⟨(1 / 25000000000000000000000000000000), (42351647819 / 100000000000000000000000000000000)⟩
def CA1_4_11I2PairH : Ball := ⟨(35757576740432000148421565320111 / 12500000000000000000000000000000), (159039116003 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R0Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R0Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R0MassTerm : Ball := .exact 0
def CA1_4_11I2R0H : Ball := ⟨0, 0⟩
def CA1_4_11I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R1Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R1Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R1MassTerm : Ball := .exact 0
def CA1_4_11I2R1H : Ball := ⟨0, 0⟩
def CA1_4_11I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R2Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R2Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R2MassTerm : Ball := .exact 0
def CA1_4_11I2R2H : Ball := ⟨0, 0⟩
def CA1_4_11I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(61436712352474830488612391 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7372459591722180802103669681 / 100000000000000000000000000000000), (1235931 / 50000000000000000000000000000000)⟩ ⟨(-1200008807343871317001204918543989 / 100000000000000000000000000000000), (201170406373 / 50000000000000000000000000000000)⟩ ⟨-18, 61436712352474830488612391, 38146972656250000000000000⟩,
   .log ⟨(20890993075933606986049075471 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(44255518130701293310819022579 / 25000000000000000000000000000000), (7741721 / 12500000000000000000000000000000)⟩ ⟨(-847360735219113820046267163931973 / 100000000000000000000000000000000), (74115384087 / 25000000000000000000000000000000)⟩ ⟨-13, 20890993075933606986049075471, 12207031250000000000000000000⟩,
   .log ⟨(12647475172166827455070439 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2187112567878730349464064949 / 10000000000000000000000000000000), (3557 / 48828125000000000000000000000)⟩ ⟨(-1080804932459902736691495491288357 / 100000000000000000000000000000000), (359989052027 / 100000000000000000000000000000000)⟩ ⟨-16, 12647475172166827455070439, 9536743164062500000000000⟩]
def CA1_4_11I2R3Entropy : Ball := ⟨(206265657793314657540020409487 / 50000000000000000000000000000000), (35845183 / 25000000000000000000000000000000)⟩
def CA1_4_11I2R3Mass : Ball := ⟨(23528956227005047683746469621 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
def CA1_4_11I2R3MassTermLogWitness : LogWitness := ⟨-12, 23528956227005047683746469621, 12207031250000000000000000000⟩
def CA1_4_11I2R3MassTermLog : Ball := ⟨(-383077322094910835836992754825221 / 50000000000000000000000000000000), (275285720629 / 100000000000000000000000000000000)⟩
def CA1_4_11I2R3MassTerm : Ball := ⟨(180268190862589412980979300497 / 50000000000000000000000000000000), (1619297 / 1250000000000000000000000000000)⟩
def CA1_4_11I2R3H : Ball := ⟨(2599746693072524455904110899 / 5000000000000000000000000000000), (68231123 / 25000000000000000000000000000000)⟩
def CA1_4_11I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(675590492357013698713995109 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(502685504275185179583228751 / 6250000000000000000000000000000), (2718189 / 100000000000000000000000000000000)⟩ ⟨(-595254681600276381793198535164501 / 50000000000000000000000000000000), (80468159599 / 20000000000000000000000000000000)⟩ ⟨-18, 675590492357013698713995109, 381469726562500000000000000⟩,
   .log ⟨(133830529574469617999668594627 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1585411053395870048139682753047 / 100000000000000000000000000000000), (283397177 / 50000000000000000000000000000000)⟩ ⟨(-296160199477069350470806166977669 / 50000000000000000000000000000000), (211758237577 / 100000000000000000000000000000000)⟩ ⟨-9, 133830529574469617999668594627, 97656250000000000000000000000⟩,
   .log ⟨(284437587041342969390806612487 / 10000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(405019386275128425873996955433 / 4000000000000000000000000000000), (421624019 / 10000000000000000000000000000000)⟩ ⟨(-355982652018717647827715657652457 / 100000000000000000000000000000000), (148230766203 / 100000000000000000000000000000000)⟩ ⟨-6, 284437587041342969390806612487, 156250000000000000000000000000⟩,
   .log ⟨(147480825491657547530678195629 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(480730511466098859677777116159 / 50000000000000000000000000000000), (343533083 / 100000000000000000000000000000000)⟩ ⟨(-26076909177229525697088505975703 / 4000000000000000000000000000000), (232934061191 / 100000000000000000000000000000000)⟩ ⟨-10, 147480825491657547530678195629, 97656250000000000000000000000⟩,
   .log ⟨(43928590602018655644399493 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(4413478728619861079566301109 / 100000000000000000000000000000000), (1488373 / 100000000000000000000000000000000)⟩ ⟨(-251173476552252963534643964200933 / 20000000000000000000000000000000), (105879189553 / 25000000000000000000000000000000)⟩ ⟨-19, 43928590602018655644399493, 23841857910156250000000000⟩]
def CA1_4_11I2R4Entropy : Ball := ⟨(238120753506246437010416054339 / 1562500000000000000000000000000), (1208763963 / 20000000000000000000000000000000)⟩
def CA1_4_11I2R4Mass : Ball := ⟨(1838181124702076718805340040399 / 50000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
def CA1_4_11I2R4MassTermLogWitness : LogWitness := ⟨-5, 1838181124702076718805340040399, 1562500000000000000000000000000⟩
def CA1_4_11I2R4MassTermLog : Ball := ⟨(-330324644189821671673985641754329 / 100000000000000000000000000000000), (31763735667 / 25000000000000000000000000000000)⟩
def CA1_4_11I2R4MassTerm : Ball := ⟨(3035982629868298560652886595353 / 25000000000000000000000000000000), (2335500009 / 50000000000000000000000000000000)⟩
def CA1_4_11I2R4H : Ball := ⟨(773949426231644431513770274071 / 25000000000000000000000000000000), (10714819833 / 100000000000000000000000000000000)⟩
def CA1_4_11I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18138120034399794853090260729 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(156258265537147701001751566529 / 100000000000000000000000000000000), (53772559 / 100000000000000000000000000000000)⟩ ⟨(-430745483106288237002291658559271 / 50000000000000000000000000000000), (11858461483 / 4000000000000000000000000000000)⟩ ⟨-13, 18138120034399794853090260729, 12207031250000000000000000000⟩,
   .log ⟨(752915443548722822830379625787 / 6250000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩ ⟨(25495328928592416167136082228937 / 100000000000000000000000000000000), (12754883817 / 100000000000000000000000000000000)⟩ ⟨(-211638381399983837207000776148451 / 100000000000000000000000000000000), (52939559303 / 50000000000000000000000000000000)⟩ ⟨-4, 752915443548722822830379625787, 390625000000000000000000000000⟩,
   .log ⟨(111141817618374134334930680753 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(481539625883784876366837532177 / 20000000000000000000000000000000), (423633523 / 50000000000000000000000000000000)⟩ ⟨(-27079120409095235826197750264821 / 5000000000000000000000000000000), (47645603399 / 25000000000000000000000000000000)⟩ ⟨-8, 111141817618374134334930680753, 97656250000000000000000000000⟩]
def CA1_4_11I2R5Entropy : Ball := ⟨(28059285323548488249972021456351 / 50000000000000000000000000000000), (6827961711 / 25000000000000000000000000000000)⟩
def CA1_4_11I2R5Mass : Ball := ⟨(12509352487287461497478886996333 / 50000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
def CA1_4_11I2R5MassTermLogWitness : LogWitness := ⟨-2, 12509352487287461497478886996333, 12500000000000000000000000000000⟩
def CA1_4_11I2R5MassTermLog : Ball := ⟨(-17319330523727708959248212380091 / 12500000000000000000000000000000), (7940933907 / 12500000000000000000000000000000)⟩
def CA1_4_11I2R5MassTerm : Ball := ⟨(34664577658423499082858619295681 / 100000000000000000000000000000000), (3973437671 / 25000000000000000000000000000000)⟩
def CA1_4_11I2R5H : Ball := ⟨(21453992988673477417085423617021 / 100000000000000000000000000000000), (5400699691 / 12500000000000000000000000000000)⟩
def CA1_4_11I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(177571602779606609244244421869 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1124658898503515455075567975467 / 100000000000000000000000000000000), (10340619 / 2500000000000000000000000000000)⟩ ⟨(-158338788536389508578027784169353 / 25000000000000000000000000000000), (232934061639 / 100000000000000000000000000000000)⟩ ⟨-10, 177571602779606609244244421869, 97656250000000000000000000000⟩,
   .log ⟨(1398464475151336582003091 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(179069061735961277107640157 / 100000000000000000000000000000000), (11849 / 20000000000000000000000000000000)⟩ ⟨(-400146609276093460159869386768671 / 25000000000000000000000000000000), (10588090609 / 2000000000000000000000000000000)⟩ ⟨-24, 1398464475151336582003091, 745058059692382812500000⟩,
   .log ⟨(930993068943178587526919271357 / 5000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩ ⟨(31298895088922340799913625208817 / 100000000000000000000000000000000), (985727261 / 6250000000000000000000000000000)⟩ ⟨(-168094135891105168076544183405379 / 100000000000000000000000000000000), (84703294957 / 100000000000000000000000000000000)⟩ ⟨-3, 930993068943178587526919271357, 625000000000000000000000000000⟩]
def CA1_4_11I2R6Entropy : Ball := ⟨(6709714204810568726523795288013 / 20000000000000000000000000000000), (8299502093 / 50000000000000000000000000000000)⟩
def CA1_4_11I2R6Mass : Ball := ⟨(9487513479927193695206093160167 / 50000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
def CA1_4_11I2R6MassTermLogWitness : LogWitness := ⟨-3, 9487513479927193695206093160167, 6250000000000000000000000000000⟩
def CA1_4_11I2R6MassTermLog : Ball := ⟨(-83102322094910835836992839972633 / 50000000000000000000000000000000), (10587911873 / 12500000000000000000000000000000)⟩
def CA1_4_11I2R6MassTerm : Ball := ⟨(15768688021774360428200263096397 / 50000000000000000000000000000000), (803623657 / 5000000000000000000000000000000)⟩
def CA1_4_11I2R6H : Ball := ⟨(2011194980504122776218450247271 / 100000000000000000000000000000000), (16335738663 / 50000000000000000000000000000000)⟩
def CA1_4_11I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R7Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R7Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R7MassTerm : Ball := .exact 0
def CA1_4_11I2R7H : Ball := ⟨0, 0⟩
def CA1_4_11I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R8Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R8Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R8MassTerm : Ball := .exact 0
def CA1_4_11I2R8H : Ball := ⟨0, 0⟩
def CA1_4_11I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R9Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R9Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R9MassTerm : Ball := .exact 0
def CA1_4_11I2R9H : Ball := ⟨0, 0⟩
def CA1_4_11I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R10Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R10Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R10MassTerm : Ball := .exact 0
def CA1_4_11I2R10H : Ball := ⟨0, 0⟩
def CA1_4_11I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R11Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R11Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R11MassTerm : Ball := .exact 0
def CA1_4_11I2R11H : Ball := ⟨0, 0⟩
def CA1_4_11I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R12Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R12Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R12MassTerm : Ball := .exact 0
def CA1_4_11I2R12H : Ball := ⟨0, 0⟩
def CA1_4_11I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R13Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R13Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R13MassTerm : Ball := .exact 0
def CA1_4_11I2R13H : Ball := ⟨0, 0⟩
def CA1_4_11I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R14Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R14Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R14MassTerm : Ball := .exact 0
def CA1_4_11I2R14H : Ball := ⟨0, 0⟩
def CA1_4_11I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R15Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R15Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R15MassTerm : Ball := .exact 0
def CA1_4_11I2R15H : Ball := ⟨0, 0⟩
def CA1_4_11I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_4_11I2R16Entropy : Ball := ⟨0, 0⟩
def CA1_4_11I2R16Mass : Ball := ⟨0, 0⟩
def CA1_4_11I2R16MassTerm : Ball := .exact 0
def CA1_4_11I2R16H : Ball := ⟨0, 0⟩
def CA1_4_11I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_4_11I2R0H
  | 1 => CA1_4_11I2R1H
  | 2 => CA1_4_11I2R2H
  | 3 => CA1_4_11I2R3H
  | 4 => CA1_4_11I2R4H
  | 5 => CA1_4_11I2R5H
  | 6 => CA1_4_11I2R6H
  | 7 => CA1_4_11I2R7H
  | 8 => CA1_4_11I2R8H
  | 9 => CA1_4_11I2R9H
  | 10 => CA1_4_11I2R10H
  | 11 => CA1_4_11I2R11H
  | 12 => CA1_4_11I2R12H
  | 13 => CA1_4_11I2R13H
  | 14 => CA1_4_11I2R14H
  | 15 => CA1_4_11I2R15H
  | 16 => CA1_4_11I2R16H
  | _ => (.exact 0)
def CA1_4_11I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)
def CA1_4_11I2Singleton : Ball := ⟨(56488132491887973451105759346661 / 100000000000000000000000000000000), (24495359647 / 50000000000000000000000000000000)⟩
def CA1_4_11I2Group : Ball := ⟨(83101113099853601859582796525217 / 100000000000000000000000000000000), (135855538473 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I2H : Ball := ⟨(59929193861874398734103464755227 / 50000000000000000000000000000000), (430750192949 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_5_10I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_5_10I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_5_10I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 5 10)) A1_5_10Law ((Equiv.refl (Fin 3)) 0) a
def CA1_5_10I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(49999999999999999999999999999999 / 100000000000000000000000000000000), (21 / 25000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (31763735667 / 100000000000000000000000000000000)⟩ ⟨(-69314718055994530941723193050331 / 100000000000000000000000000000000), (63527471217 / 100000000000000000000000000000000)⟩ ⟨-2, 49999999999999999999999999999999, 25000000000000000000000000000000⟩]
def CA1_5_10I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I0Certificates (CA1_5_10I0CertificateIndex a)).input
def CA1_5_10I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I0Certificates (CA1_5_10I0CertificateIndex a)).output
def CA1_5_10I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (31763735667 / 50000000000000000000000000000000)⟩
def CA1_5_10I0Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (21 / 12500000000000000000000000000000)⟩
def CA1_5_10I0MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA1_5_10I0MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (21175823767 / 50000000000000000000000000000000)⟩
def CA1_5_10I0MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (8470329507 / 20000000000000000000000000000000)⟩
def CA1_5_10I0H : Ball := ⟨(69314718055994530941723193050329 / 100000000000000000000000000000000), (105879118869 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_5_10I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_5_10I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(22268884945206414182146674039 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(47323448329967572271861989909 / 6250000000000000000000000000000), (129679553 / 50000000000000000000000000000000)⟩ ⟨(-170007428558399866366735946547719 / 25000000000000000000000000000000), (232934062309 / 100000000000000000000000000000000)⟩ ⟨-10, 22268884945206414182146674039, 19531250000000000000000000000⟩,
   .log ⟨(5073240300123497419871639527 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(93304991677621678275312218259 / 100000000000000000000000000000000), (1007157 / 3125000000000000000000000000000)⟩ ⟨(-91957985585021828636861036394861 / 10000000000000000000000000000000), (3176373651 / 1000000000000000000000000000000)⟩ ⟨-14, 5073240300123497419871639527, 3051757812500000000000000000⟩,
   .log ⟨(5438635077537771407403874419 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(53404118816045124414143044197 / 100000000000000000000000000000000), (2303353 / 12500000000000000000000000000000)⟩ ⟨(-122742466755608112311191459318267 / 12500000000000000000000000000000), (67762639463 / 20000000000000000000000000000000)⟩ ⟨-15, 5438635077537771407403874419, 3051757812500000000000000000⟩,
   .log ⟨(503707182470066923959310737177 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1332539810352274052911456223889 / 50000000000000000000000000000000), (959977323 / 100000000000000000000000000000000)⟩ ⟨(-21163721411599461767867524868173 / 4000000000000000000000000000000), (95291206871 / 50000000000000000000000000000000)⟩ ⟨-8, 503707182470066923959310737177, 390625000000000000000000000000⟩,
   .log ⟨(255193173092274822371952880777 / 10000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(9361301115128316629100104983021 / 100000000000000000000000000000000), (3782748013 / 100000000000000000000000000000000)⟩ ⟨(-73366391441383749399422062155569 / 20000000000000000000000000000000), (148230766329 / 100000000000000000000000000000000)⟩ ⟨-6, 255193173092274822371952880777, 156250000000000000000000000000⟩,
   .log ⟨(125699728194725478810433817933 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(60193902562488651779210685601 / 4000000000000000000000000000000), (532359071 / 100000000000000000000000000000000)⟩ ⟨(-74823529139369373198258005927601 / 12500000000000000000000000000000), (1694065901 / 800000000000000000000000000000)⟩ ⟨-9, 125699728194725478810433817933, 97656250000000000000000000000⟩,
   .log ⟨(12924529061909621010619436253 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(106765027808725347330636653301 / 50000000000000000000000000000000), (71158773 / 100000000000000000000000000000000)⟩ ⟨(-413032565044774768934775549269317 / 50000000000000000000000000000000), (275285711747 / 100000000000000000000000000000000)⟩ ⟨-12, 12924529061909621010619436253, 12207031250000000000000000000⟩,
   .log ⟨(7241760128070376296042527833 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1380722846529755478347343081 / 2000000000000000000000000000000), (23002547 / 100000000000000000000000000000000)⟩ ⟨(-119163264706343902913200946417513 / 12500000000000000000000000000000), (317637369053 / 100000000000000000000000000000000)⟩ ⟨-14, 7241760128070376296042527833, 6103515625000000000000000000⟩,
   .log ⟨(78309427042427579441955721699 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1011618452372932438045376250439 / 100000000000000000000000000000000), (22801167 / 6250000000000000000000000000000)⟩ ⟨(-161477757305139585549445375081577 / 25000000000000000000000000000000), (23293406179 / 10000000000000000000000000000000)⟩ ⟨-10, 78309427042427579441955721699, 48828125000000000000000000000⟩,
   .log ⟨(3154898529883487505530600990651 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(5452002000629977185954074050957 / 50000000000000000000000000000000), (501056821 / 12500000000000000000000000000000)⟩ ⟨(-345621385219721994331378287963377 / 100000000000000000000000000000000), (127054942573 / 100000000000000000000000000000000)⟩ ⟨-5, 3154898529883487505530600990651, 3125000000000000000000000000000⟩,
   .log ⟨(7698603852803860679159811007 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1780843203845114424029959940873 / 100000000000000000000000000000000), (5216777 / 800000000000000000000000000000)⟩ ⟨(-144575175406359929211606310492157 / 25000000000000000000000000000000), (211758237479 / 100000000000000000000000000000000)⟩ ⟨-9, 7698603852803860679159811007, 4882812500000000000000000000⟩,
   .log ⟨(15955597746132917085758812853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(34875409454573142592713603831 / 25000000000000000000000000000000), (2365111 / 5000000000000000000000000000000)⟩ ⟨(-874311574143957871285697078124269 / 100000000000000000000000000000000), (296461537829 / 100000000000000000000000000000000)⟩ ⟨-13, 15955597746132917085758812853, 12207031250000000000000000000⟩,
   .log ⟨(308702927519657890792613245011 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(356894297667234668311633767527 / 20000000000000000000000000000000), (653703891 / 100000000000000000000000000000000)⟩ ⟨(-289027302506313290239710288398163 / 50000000000000000000000000000000), (105879118739 / 50000000000000000000000000000000)⟩ ⟨-9, 308702927519657890792613245011, 195312500000000000000000000000⟩,
   .log ⟨(30216127494741087159206101773 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(244888105817775592438390103263 / 100000000000000000000000000000000), (8318069 / 10000000000000000000000000000000)⟩ ⟨(-810454966012427346008748038820529 / 100000000000000000000000000000000), (68821427797 / 25000000000000000000000000000000)⟩ ⟨-12, 30216127494741087159206101773, 24414062500000000000000000000⟩,
   .log ⟨(573369051292370077537550288831 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2959384663076721829910329755453 / 100000000000000000000000000000000), (546370297 / 50000000000000000000000000000000)⟩ ⟨(-516139588700556513683282065940681 / 100000000000000000000000000000000), (19058241367 / 10000000000000000000000000000000)⟩ ⟨-8, 573369051292370077537550288831, 390625000000000000000000000000⟩,
   .log ⟨(5578469393746635659764022855967 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩ ⟨(3058547257135294209203379630207 / 12500000000000000000000000000000), (1476608569 / 12500000000000000000000000000000)⟩ ⟨(-219310856885859833802796074616251 / 100000000000000000000000000000000), (21175823751 / 20000000000000000000000000000000)⟩ ⟨-4, 5578469393746635659764022855967, 3125000000000000000000000000000⟩,
   .log ⟨(136451581513342476380793490701 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1232843883026774969871488768507 / 25000000000000000000000000000000), (1849263787 / 100000000000000000000000000000000)⟩ ⟨(-451751408577930377411076121778643 / 100000000000000000000000000000000), (16940658983 / 10000000000000000000000000000000)⟩ ⟨-7, 136451581513342476380793490701, 97656250000000000000000000000⟩]
def CA1_5_10I1PairEntropy : Ball := ⟨(41523217069936040245483418022181 / 12500000000000000000000000000000), (33568586887 / 25000000000000000000000000000000)⟩
def CA1_5_10I1PairMass : Ball := ⟨(25000000000000000000000000000001 / 25000000000000000000000000000000), (61 / 12500000000000000000000000000000)⟩
def CA1_5_10I1PairMassTermLogWitness : LogWitness := ⟨0, 25000000000000000000000000000001, 25000000000000000000000000000000⟩
def CA1_5_10I1PairMassTermLog : Ball := ⟨(1 / 25000000000000000000000000000000), (2117582417 / 10000000000000000000000000000000)⟩
def CA1_5_10I1PairMassTerm : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175824171 / 100000000000000000000000000000000)⟩
def CA1_5_10I1PairH : Ball := ⟨(83046434139872080490966836044363 / 25000000000000000000000000000000), (155450171719 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_5_10I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(50771816161526734863152209467 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(758549484444178149680679190387 / 50000000000000000000000000000000), (107513507 / 20000000000000000000000000000000)⟩ ⟨(-59761461518800880570056690030777 / 10000000000000000000000000000000), (211758238011 / 100000000000000000000000000000000)⟩ ⟨-9, 50771816161526734863152209467, 39062500000000000000000000000⟩]
def CA1_5_10I1R0Entropy : Ball := ⟨(758549484444178149680679190387 / 50000000000000000000000000000000), (107513507 / 20000000000000000000000000000000)⟩
def CA1_5_10I1R0Mass : Ball := ⟨(50771816161526734863152209467 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
def CA1_5_10I1R0MassTermLogWitness : LogWitness := ⟨-9, 50771816161526734863152209467, 39062500000000000000000000000⟩
def CA1_5_10I1R0MassTermLog : Ball := ⟨(-59761461518800880570056690030777 / 10000000000000000000000000000000), (211758238011 / 100000000000000000000000000000000)⟩
def CA1_5_10I1R0MassTerm : Ball := ⟨(758549484444178149680679190387 / 50000000000000000000000000000000), (107513507 / 20000000000000000000000000000000)⟩
def CA1_5_10I1R0H : Ball := ⟨0, (107513507 / 10000000000000000000000000000000)⟩
def CA1_5_10I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1025619396755435995373302370507 / 25000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩ ⟨(13101586701749977828114928045673 / 100000000000000000000000000000000), (5212400591 / 100000000000000000000000000000000)⟩ ⟨(-319357910526971922324675037272351 / 100000000000000000000000000000000), (127054942487 / 100000000000000000000000000000000)⟩ ⟨-5, 1025619396755435995373302370507, 781250000000000000000000000000⟩]
def CA1_5_10I1R1Entropy : Ball := ⟨(13101586701749977828114928045673 / 50000000000000000000000000000000), (5212400591 / 50000000000000000000000000000000)⟩
def CA1_5_10I1R1Mass : Ball := ⟨(1025619396755435995373302370507 / 12500000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
def CA1_5_10I1R1MassTermLogWitness : LogWitness := ⟨-4, 1025619396755435995373302370507, 781250000000000000000000000000⟩
def CA1_5_10I1R1MassTermLog : Ball := ⟨(-250043192470977391382951844222021 / 100000000000000000000000000000000), (26469779701 / 25000000000000000000000000000000)⟩
def CA1_5_10I1R1MassTerm : Ball := ⟨(20515931857990976613637576474281 / 100000000000000000000000000000000), (8687334317 / 100000000000000000000000000000000)⟩
def CA1_5_10I1R1H : Ball := ⟨(1137448309101795808518455923413 / 20000000000000000000000000000000), (19112135499 / 100000000000000000000000000000000)⟩
def CA1_5_10I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3619461538080497091580904874329 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩ ⟨(19007223939689147579515642461891 / 100000000000000000000000000000000), (7664508023 / 100000000000000000000000000000000)⟩ ⟨(-262569773704091029867312389988677 / 100000000000000000000000000000000), (52939559373 / 50000000000000000000000000000000)⟩ ⟨-4, 3619461538080497091580904874329, 3125000000000000000000000000000⟩,
   .log ⟨(354874652760531895037578159637 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1755924625224395990092778958639 / 50000000000000000000000000000000), (338164343 / 25000000000000000000000000000000)⟩ ⟨(-247400682405075496013496227375001 / 50000000000000000000000000000000), (19058241357 / 10000000000000000000000000000000)⟩ ⟨-8, 354874652760531895037578159637, 195312500000000000000000000000⟩,
   .log ⟨(5128768196356952483244777570549 / 20000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩ ⟨(34897850813233620737731844437989 / 100000000000000000000000000000000), (4072720941 / 25000000000000000000000000000000)⟩ ⟨(-136086676087338601525818244277431 / 100000000000000000000000000000000), (63527471227 / 100000000000000000000000000000000)⟩ ⟨-2, 5128768196356952483244777570549, 5000000000000000000000000000000⟩]
def CA1_5_10I1R2Entropy : Ball := ⟨(79935997193509499857134245196327 / 100000000000000000000000000000000), (17162607277 / 50000000000000000000000000000000)⟩
def CA1_5_10I1R2Mass : Ball := ⟨(41541185745148878362697819988609 / 100000000000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
def CA1_5_10I1R2MassTermLogWitness : LogWitness := ⟨-2, 41541185745148878362697819988609, 25000000000000000000000000000000⟩
def CA1_5_10I1R2MassTermLog : Ball := ⟨(-43924241164408934512891830914001 / 50000000000000000000000000000000), (6352747129 / 10000000000000000000000000000000)⟩
def CA1_5_10I1R2MassTerm : Ball := ⟨(18246650609254260008448820334291 / 50000000000000000000000000000000), (3298758117 / 12500000000000000000000000000000)⟩
def CA1_5_10I1R2H : Ball := ⟨(8688539195000195968047320905549 / 20000000000000000000000000000000), (6071527949 / 10000000000000000000000000000000)⟩
def CA1_5_10I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(459258977477173114738445400667 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(134624995532851081425096845973 / 3125000000000000000000000000000), (155602997 / 10000000000000000000000000000000)⟩ ⟨(-469016401237944039661153399430267 / 100000000000000000000000000000000), (169406590007 / 100000000000000000000000000000000)⟩ ⟨-7, 459258977477173114738445400667, 390625000000000000000000000000⟩,
   .log ⟨(9042070851149781056087237091629 / 50000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩ ⟨(3092631970608047946983192993897 / 10000000000000000000000000000000), (3063572797 / 20000000000000000000000000000000)⟩ ⟨(-171013478080344384390576475007727 / 100000000000000000000000000000000), (84703295013 / 100000000000000000000000000000000)⟩ ⟨-3, 9042070851149781056087237091629, 6250000000000000000000000000000⟩,
   .log ⟨(1767933215320530839697545009713 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(142684904117555242456412765777 / 2000000000000000000000000000000), (262062097 / 10000000000000000000000000000000)⟩ ⟨(-403535899662607171230223242518487 / 100000000000000000000000000000000), (148230766063 / 100000000000000000000000000000000)⟩ ⟨-6, 1767933215320530839697545009713, 1562500000000000000000000000000⟩]
def CA1_5_10I1R3Entropy : Ball := ⟨(10592141192252369049563916824739 / 12500000000000000000000000000000), (779780597 / 2000000000000000000000000000000)⟩
def CA1_5_10I1R3Mass : Ball := ⟨(4154118574514887836269781998861 / 10000000000000000000000000000000), (61 / 50000000000000000000000000000000)⟩
def CA1_5_10I1R3MassTermLogWitness : LogWitness := ⟨-2, 4154118574514887836269781998861, 2500000000000000000000000000000⟩
def CA1_5_10I1R3MassTermLog : Ball := ⟨(-87848482328817869025783661827999 / 100000000000000000000000000000000), (31763735671 / 50000000000000000000000000000000)⟩
def CA1_5_10I1R3MassTerm : Ball := ⟨(18246650609254260008448820334291 / 50000000000000000000000000000000), (26390064977 / 100000000000000000000000000000000)⟩
def CA1_5_10I1R3H : Ball := ⟨(4824382831951043237961369392933 / 10000000000000000000000000000000), (65379094827 / 100000000000000000000000000000000)⟩
def CA1_5_10I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2896704051228150518417011133 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(128033073422848728261177381463 / 100000000000000000000000000000000), (10734519 / 25000000000000000000000000000000)⟩ ⟨(-883991399594756692363884378296679 / 100000000000000000000000000000000), (148230769233 / 50000000000000000000000000000000)⟩ ⟨-13, 2896704051228150518417011133, 2441406250000000000000000000⟩,
   .log ⟨(503707182470066923959310737177 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(1157968203673813654462679024211 / 25000000000000000000000000000000), (106664147 / 6250000000000000000000000000000)⟩ ⟨(-91955663446798402650992985730799 / 20000000000000000000000000000000), (169406590059 / 100000000000000000000000000000000)⟩ ⟨-7, 503707182470066923959310737177, 390625000000000000000000000000⟩,
   .log ⟨(255193173092274822371952880777 / 5000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩ ⟨(15184873661715505394591427934243 / 100000000000000000000000000000000), (3242355439 / 50000000000000000000000000000000)⟩ ⟨(-59503447830184843211077423545503 / 20000000000000000000000000000000), (63527471323 / 50000000000000000000000000000000)⟩ ⟨-5, 255193173092274822371952880777, 156250000000000000000000000000⟩,
   .log ⟨(502798912778901915241735271733 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2661181479343130870123496415501 / 100000000000000000000000000000000), (958246327 / 100000000000000000000000000000000)⟩ ⟨(-529273515058960454644340854370279 / 100000000000000000000000000000000), (95291206971 / 50000000000000000000000000000000)⟩ ⟨-8, 502798912778901915241735271733, 390625000000000000000000000000⟩,
   .log ⟨(51698116247638484042477745011 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(97806426929397618687614051929 / 25000000000000000000000000000000), (131370033 / 100000000000000000000000000000000)⟩ ⟨(-756750412033555006927827905490239 / 100000000000000000000000000000000), (25410988613 / 10000000000000000000000000000000)⟩ ⟨-11, 51698116247638484042477745011, 48828125000000000000000000000⟩]
def CA1_5_10I1R4Entropy : Ball := ⟨(1216730964174222572072506557183 / 4000000000000000000000000000000), (12031702421 / 100000000000000000000000000000000)⟩
def CA1_5_10I1R4Mass : Ball := ⟨(1640991034808697592597283792811 / 20000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
def CA1_5_10I1R4MassTermLogWitness : LogWitness := ⟨-4, 1640991034808697592597283792811, 1250000000000000000000000000000⟩
def CA1_5_10I1R4MassTermLog : Ball := ⟨(-250043192470977391382951844222033 / 100000000000000000000000000000000), (26469779759 / 25000000000000000000000000000000)⟩
def CA1_5_10I1R4MassTerm : Ball := ⟨(512898296449774415340939411857 / 2500000000000000000000000000000), (542958399 / 6250000000000000000000000000000)⟩
def CA1_5_10I1R4H : Ball := ⟨(1980468449272917537635017491059 / 20000000000000000000000000000000), (4143807361 / 20000000000000000000000000000000)⟩
def CA1_5_10I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5438635077537771407403874419 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(53404118816045124414143044197 / 100000000000000000000000000000000), (2303353 / 12500000000000000000000000000000)⟩ ⟨(-122742466755608112311191459318267 / 12500000000000000000000000000000), (67762639463 / 20000000000000000000000000000000)⟩ ⟨-15, 5438635077537771407403874419, 3051757812500000000000000000⟩,
   .log ⟨(22268884945206414182146674039 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(47323448329967572271861989909 / 6250000000000000000000000000000), (129679553 / 50000000000000000000000000000000)⟩ ⟨(-170007428558399866366735946547719 / 25000000000000000000000000000000), (232934062309 / 100000000000000000000000000000000)⟩ ⟨-10, 22268884945206414182146674039, 19531250000000000000000000000⟩,
   .log ⟨(5073240300123497419871639527 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(93304991677621678275312218259 / 100000000000000000000000000000000), (1007157 / 3125000000000000000000000000000)⟩ ⟨(-91957985585021828636861036394861 / 10000000000000000000000000000000), (3176373651 / 1000000000000000000000000000000)⟩ ⟨-14, 5073240300123497419871639527, 3051757812500000000000000000⟩]
def CA1_5_10I1R5Entropy : Ball := ⟨(903884283773147959039247101 / 50000000000000000000000000000), (155007477 / 25000000000000000000000000000000)⟩
def CA1_5_10I1R5Mass : Ball := ⟨(31732385100954209289470130917 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def CA1_5_10I1R5MassTermLogWitness : LogWitness := ⟨-9, 31732385100954209289470130917, 24414062500000000000000000000⟩
def CA1_5_10I1R5MassTermLog : Ball := ⟨(-37350913449250550356285431269211 / 6250000000000000000000000000000), (211758239981 / 100000000000000000000000000000000)⟩
def CA1_5_10I1R5MassTerm : Ball := ⟨(758549484444178149680679190389 / 50000000000000000000000000000000), (53756757 / 10000000000000000000000000000000)⟩
def CA1_5_10I1R5H : Ball := ⟨(145334799328969809358567910611 / 50000000000000000000000000000000), (578798739 / 50000000000000000000000000000000)⟩
def CA1_5_10I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R6Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R6Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R6MassTerm : Ball := .exact 0
def CA1_5_10I1R6H : Ball := ⟨0, 0⟩
def CA1_5_10I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R7Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R7Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R7MassTerm : Ball := .exact 0
def CA1_5_10I1R7H : Ball := ⟨0, 0⟩
def CA1_5_10I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R8Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R8Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R8MassTerm : Ball := .exact 0
def CA1_5_10I1R8H : Ball := ⟨0, 0⟩
def CA1_5_10I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R9Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R9Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R9MassTerm : Ball := .exact 0
def CA1_5_10I1R9H : Ball := ⟨0, 0⟩
def CA1_5_10I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R10Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R10Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R10MassTerm : Ball := .exact 0
def CA1_5_10I1R10H : Ball := ⟨0, 0⟩
def CA1_5_10I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R11Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R11Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R11MassTerm : Ball := .exact 0
def CA1_5_10I1R11H : Ball := ⟨0, 0⟩
def CA1_5_10I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R12Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R12Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R12MassTerm : Ball := .exact 0
def CA1_5_10I1R12H : Ball := ⟨0, 0⟩
def CA1_5_10I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R13Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R13Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R13MassTerm : Ball := .exact 0
def CA1_5_10I1R13H : Ball := ⟨0, 0⟩
def CA1_5_10I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R14Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R14Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R14MassTerm : Ball := .exact 0
def CA1_5_10I1R14H : Ball := ⟨0, 0⟩
def CA1_5_10I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R15Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R15Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R15MassTerm : Ball := .exact 0
def CA1_5_10I1R15H : Ball := ⟨0, 0⟩
def CA1_5_10I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I1R16Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I1R16Mass : Ball := ⟨0, 0⟩
def CA1_5_10I1R16MassTerm : Ball := .exact 0
def CA1_5_10I1R16H : Ball := ⟨0, 0⟩
def CA1_5_10I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_5_10I1R0H
  | 1 => CA1_5_10I1R1H
  | 2 => CA1_5_10I1R2H
  | 3 => CA1_5_10I1R3H
  | 4 => CA1_5_10I1R4H
  | 5 => CA1_5_10I1R5H
  | 6 => CA1_5_10I1R6H
  | 7 => CA1_5_10I1R7H
  | 8 => CA1_5_10I1R8H
  | 9 => CA1_5_10I1R9H
  | 10 => CA1_5_10I1R10H
  | 11 => CA1_5_10I1R11H
  | 12 => CA1_5_10I1R12H
  | 13 => CA1_5_10I1R13H
  | 14 => CA1_5_10I1R14H
  | 15 => CA1_5_10I1R15H
  | 16 => CA1_5_10I1R16H
  | _ => (.exact 0)
def CA1_5_10I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
def CA1_5_10I1Singleton : Ball := ⟨0, 0⟩
def CA1_5_10I1Group : Ball := ⟨(107566777685042918569334801350657 / 100000000000000000000000000000000), (168158279169 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_5_10I1H : Ball := ⟨(58526090594701242412598870738069 / 50000000000000000000000000000000), (491766730057 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_5_10I2Pair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_5_10I2PairEntropy : Ball := ⟨(152296903243188808321651602681663 / 50000000000000000000000000000000), (32383312703 / 25000000000000000000000000000000)⟩
def CA1_5_10I2PairMass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (27 / 5000000000000000000000000000000)⟩
def CA1_5_10I2PairMassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA1_5_10I2PairMassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (21175823953 / 50000000000000000000000000000000)⟩
def CA1_5_10I2PairMassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (42351647907 / 100000000000000000000000000000000)⟩
def CA1_5_10I2PairH : Ball := ⟨(12183752259455104665732128214533 / 4000000000000000000000000000000), (171884898719 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_5_10I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_5_10I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R0Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R0Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R0MassTerm : Ball := .exact 0
def CA1_5_10I2R0H : Ball := ⟨0, 0⟩
def CA1_5_10I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R1Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R1Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R1MassTerm : Ball := .exact 0
def CA1_5_10I2R1H : Ball := ⟨0, 0⟩
def CA1_5_10I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(447236789237316840707946291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(688610068444994029318992737 / 12500000000000000000000000000000), (179943 / 10000000000000000000000000000000)⟩ ⟨(-615879627987935948080324132652163 / 50000000000000000000000000000000), (402340873571 / 100000000000000000000000000000000)⟩ ⟨-18, 447236789237316840707946291, 381469726562500000000000000⟩,
   .log ⟨(53769237716673631681010297 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(194052899722326233188264489 / 25000000000000000000000000000000), (25051 / 10000000000000000000000000000000)⟩ ⟨(-180449740374644722766312628984091 / 12500000000000000000000000000000), (18634799233 / 4000000000000000000000000000000)⟩ ⟨-21, 53769237716673631681010297, 47683715820312500000000000⟩,
   .log ⟨(1706374619138283140882338411 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(18733526669721479089924408983 / 100000000000000000000000000000000), (3071387 / 50000000000000000000000000000000)⟩ ⟨(-137231930635356939885690339142263 / 12500000000000000000000000000000), (179994530607 / 50000000000000000000000000000000)⟩ ⟨-16, 1706374619138283140882338411, 1525878906250000000000000000⟩]
def CA1_5_10I2R2Entropy : Ball := ⟨(31303710962619993424534408687 / 100000000000000000000000000000000), (5121327 / 50000000000000000000000000000000)⟩
def CA1_5_10I2R2Mass : Ball := ⟨(2708386673046264085660251587 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
def CA1_5_10I2R2MassTermLogWitness : LogWitness := ⟨-16, 2708386673046264085660251587, 1525878906250000000000000000⟩
def CA1_5_10I2R2MassTermLog : Ball := ⟨(-262914308273830957315809376714093 / 25000000000000000000000000000000), (359989187223 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R2MassTerm : Ball := ⟨(28482944347280835581130251043 / 100000000000000000000000000000000), (9749953 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R2H : Ball := ⟨(705191653834789460851039411 / 25000000000000000000000000000000), (19992607 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(7545199268018009738646353009 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(71619136801824455550077378629 / 100000000000000000000000000000000), (23966383 / 100000000000000000000000000000000)⟩ ⟨(-949201396249373474590457070135581 / 100000000000000000000000000000000), (158818684249 / 50000000000000000000000000000000)⟩ ⟨-14, 7545199268018009738646353009, 6103515625000000000000000000⟩,
   .log ⟨(16035475738875733852218175097 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(191320327118919030770614562963 / 12500000000000000000000000000000), (271651533 / 50000000000000000000000000000000)⟩ ⟨(-149138331031153994408879828874169 / 25000000000000000000000000000000), (211758237609 / 100000000000000000000000000000000)⟩ ⟨-9, 16035475738875733852218175097, 12207031250000000000000000000⟩,
   .log ⟨(24852298700834377326952470709 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(206273463219252053923611048123 / 100000000000000000000000000000000), (17103709 / 25000000000000000000000000000000)⟩ ⟨(-829997521365404894280747642876339 / 100000000000000000000000000000000), (137642855951 / 50000000000000000000000000000000)⟩ ⟨-12, 24852298700834377326952470709, 24414062500000000000000000000⟩]
def CA1_5_10I2R3Entropy : Ball := ⟨(226056902121553594454825616307 / 6250000000000000000000000000000), (127136857 / 10000000000000000000000000000000)⟩
def CA1_5_10I2R3Mass : Ball := ⟨(28896510979086412870108962527 / 5000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
def CA1_5_10I2R3MassTermLogWitness : LogWitness := ⟨-8, 28896510979086412870108962527, 19531250000000000000000000000⟩
def CA1_5_10I2R3MassTermLog : Ball := ⟨(-128836808273830957315809414912993 / 25000000000000000000000000000000), (190582414531 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R3MassTerm : Ball := ⟨(2978347395836165963875989593137 / 100000000000000000000000000000000), (1101433409 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R3H : Ball := ⟨(25542521524347661896048810711 / 4000000000000000000000000000000), (2372801979 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R4Entropy : Ball := ⟨(1945356576932199708792746366517 / 5000000000000000000000000000000), (4203106543 / 25000000000000000000000000000000)⟩
def CA1_5_10I2R4Mass : Ball := ⟨(13775585449883897327311949605707 / 100000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R4MassTermLogWitness : LogWitness := ⟨-3, 13775585449883897327311949605707, 12500000000000000000000000000000⟩
def CA1_5_10I2R4MassTermLog : Ball := ⟨(-39645446619064765852647551025943 / 20000000000000000000000000000000), (84703295043 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R4MassTerm : Ball := ⟨(1365348093999343346937508993141 / 5000000000000000000000000000000), (11668374873 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R4H : Ball := ⟨(9062632545825880653988083959 / 78125000000000000000000000000), (5696160209 / 20000000000000000000000000000000)⟩
def CA1_5_10I2R5Entropy : Ball := ⟨(14846894371321228357712412549011 / 25000000000000000000000000000000), (12324199463 / 50000000000000000000000000000000)⟩
def CA1_5_10I2R5H : Ball := ⟨(23809505514625303294760011177851 / 100000000000000000000000000000000), (42287182743 / 100000000000000000000000000000000)⟩
def CA1_5_10I2R7Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R10Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R10Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R10MassTerm : Ball := .exact 0
def CA1_5_10I2R10H : Ball := ⟨0, 0⟩
def CA1_5_10I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R11Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R11Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R11MassTerm : Ball := .exact 0
def CA1_5_10I2R11H : Ball := ⟨0, 0⟩
def CA1_5_10I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R12Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R12Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R12MassTerm : Ball := .exact 0
def CA1_5_10I2R12H : Ball := ⟨0, 0⟩
def CA1_5_10I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R13Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R13Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R13MassTerm : Ball := .exact 0
def CA1_5_10I2R13H : Ball := ⟨0, 0⟩
def CA1_5_10I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R14Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R14Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R14MassTerm : Ball := .exact 0
def CA1_5_10I2R14H : Ball := ⟨0, 0⟩
def CA1_5_10I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R15Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R15Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R15MassTerm : Ball := .exact 0
def CA1_5_10I2R15H : Ball := ⟨0, 0⟩
def CA1_5_10I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
def CA1_5_10I2R16Entropy : Ball := ⟨0, 0⟩
def CA1_5_10I2R16Mass : Ball := ⟨0, 0⟩
def CA1_5_10I2R16MassTerm : Ball := .exact 0
def CA1_5_10I2R16H : Ball := ⟨0, 0⟩
def CA1_5_10I2Group : Ball := ⟨(9493581015904919494732526364841 / 10000000000000000000000000000000), (69387122503 / 50000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_5_10I2H : Ball := ⟨(22944437233655845349730535613301 / 20000000000000000000000000000000), (449433388731 / 100000000000000000000000000000000)⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_InitialFamily
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldInitialGibbs

open AllFieldParameters AllFieldHistory AllFieldInitialEntropy
open MatrixMultiplication.Foundation
open scoped BigOperators

def coordinateWeight (k : Fin 17) : ℝ :=
  (weight (initialInteger k.val) : ℝ)

def orderedWeight (u : JointPopulation.Shape) : ℝ :=
  ∏ s : Fin 3, coordinateWeight (JointPopulation.shapeSide s u)

def initialNormalizer : ℝ := ((sortedInitial.map initialWeight).sum : ℚ)

def initialPotential (k : Fin 17) : ℝ := Real.log (coordinateWeight k)

def initialLogNormalizer : ℝ := Real.log initialNormalizer

end MatrixMultiplication.AllFieldInitialGibbs

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_StageCCapacity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldStageCCapacity

open AllFieldHistory AllFieldParameters MatrixMultiplication.Foundation
open scoped BigOperators

def stageCMarginal (t u : Shape) (i : Fin 3) (k : Fin 17) : ℝ :=
  ∑ b : Fin 4, if stageCAtom u b i = k.val then (stageCWeight t u b : ℝ) else 0

end MatrixMultiplication.AllFieldStageCCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupAmbientDegree
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldStageCGibbs

open AllFieldParameters AllFieldHistory AllFieldActiveLaws AllFieldActiveGibbs
open MatrixMultiplication.Foundation JointPopulation JointAmbientDegree
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def distinguishedSide {K : ℕ} (h : PartC K) (phi : Placement) : Fin 3 :=
  phi (stageCDistinguished (cShapeParent h))

def coordinateMass {K : ℕ} (h : PartC K) (k : Fin 17) : ℝ :=
  if k.val = 1 then
    (((1 - binaryParameter (cParameterParent h) (cShapeParent h)) / 2 : ℚ) : ℝ)
  else ((binaryParameter (cParameterParent h) (cShapeParent h) / 2 : ℚ) : ℝ)

def physicalPotential {K : ℕ} (h : PartC K) (phi : Placement)
    (side : Fin 3) (k : Fin 17) : ℝ :=
  if side = distinguishedSide h phi then Real.log (coordinateMass h k) else 0

end MatrixMultiplication.AllFieldStageCGibbs

namespace MatrixMultiplication.AllFieldGroupAmbientDegree

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldGroupTargetRate JointPopulation JointAmbientDegree
open JointAmbientEntropy JointGibbsApproximation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

def potential {K : ℕ} (w : PlacedWork K) (s : Fin 3) (k : Fin 17) : ℝ :=
  match w.1 with
  | .stageA h => AllFieldActiveGibbs.physicalPotential positiveInitial tableP
      (initialShape h.val) w.2 s k
  | .stageB h => AllFieldActiveGibbs.physicalPotential positiveSecond tablep
      (aShape h.val) w.2 s k
  | .stageC h => AllFieldStageCGibbs.physicalPotential h w.2 s k

def logNormalizer {K : ℕ} (w : PlacedWork K) : ℝ :=
  match w.1 with
  | .stageA h => AllFieldActiveGibbs.splitLogNormalizer positiveInitial tableP
      (initialShape h.val)
  | .stageB h => AllFieldActiveGibbs.splitLogNormalizer positiveSecond tablep
      (aShape h.val)
  | .stageC _ => 0

variable {K tick : ℕ} {sigma : Placement}

def orderTotal (h : ActiveOrder K tick sigma) : ℕ := 2 * h.val.val.1.halfLength

end MatrixMultiplication.AllFieldGroupAmbientDegree

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupBranchDesignation
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldGroupBranchDesignation

open AllFieldHistory AllFieldHistoryChildLaws AllFieldGroupOrbitData
open AllFieldGroupNativeLaws
attribute [local instance] Classical.propDecidable Classical.decEq

def nativeBranchDesignated {K : ℕ} (w : Work K) (right : Bool)
    (side : Fin 3) (b : w.Branch) : Prop :=
  w.stage ≠ 2 ∧ AllFieldNativeCapacity.designated w.priority side
    (halfShape w.parentShape (w.splitShape b) right)

end MatrixMultiplication.AllFieldGroupBranchDesignation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointMaskedRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointMaskedRates

open Filter JointCoarseHashing JointExtractionRates JointMaskedSelection
open JointOrdinarySelection (hashLevel hashSet)
open scoped Topology

attribute [local instance] Classical.propDecidable

def errorBound (degree : ℕ → ℕ) (B p : ℕ) (H : ℝ) (N : ℕ) : ℝ :=
  (degree N : ℝ) / (hashModulus H N : ℝ) *
    (1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * (N : ℝ))

end MatrixMultiplication.JointMaskedRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointMaskedGoodSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointMaskedSelection.OrbitData

open JointCoarseHashing
attribute [local instance] Classical.propDecidable

variable {P E O V : Type*} [Fintype P] [Fintype E]

omit [Fintype E] in
theorem good_randomLossFraction_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) (s : Sample P k)
    (hg : d.Good k U N e s) (o : O) (ho : o ∈ d.orbits e) :
    JointLossCounts.randomLossFraction (d.full e o) (d.passing e o)
      (d.variableBad k U e o) s ≤ 1 / N := by
  exact le_of_not_gt (fun h => hg.2 (Or.inr ⟨o, ho, h⟩))

theorem passing_actual_failure_subset_bad (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (hc : ∀ v ∈ d.passing e o, compatible (d.coarse e) v)
    (hu : ∀ v ∈ d.passing e o, useful (d.coarse e) v)
    (hk : ∀ v ∈ d.passing e o, keep v)
    (hcover : ∀ v ∈ d.passing e o, ∀ f ∈ d.actualTargets,
      f ≠ d.coarse e → compatible f v → f ∈ d.competitors e o v) :
    (d.passing e o).filter (fun v => d.actualAssignment k U compatible useful keep s v ≠
      some (d.coarse e)) ⊆ (d.passing e o).filter (fun v => d.variableBad k U e o v s) := by
  intro v hv
  obtain ⟨hpass, hfail⟩ := Finset.mem_filter.mp hv
  refine Finset.mem_filter.mpr ⟨hpass, ?_⟩
  by_contra hnotbad
  have hret : v ∈ JointLossCounts.retained (d.passing e o) (d.variableBad k U e o) s :=
    Finset.mem_filter.mpr ⟨hpass, hnotbad⟩
  exact hfail (d.model_retained_assigned k U hAP N e o ho s hg
    compatible useful keep v hret (hc v hpass) (hu v hpass) (hk v hpass) (hcover v hpass))

theorem good_passing_actual_failure_fraction_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (hc : ∀ v ∈ d.passing e o, compatible (d.coarse e) v)
    (hu : ∀ v ∈ d.passing e o, useful (d.coarse e) v)
    (hk : ∀ v ∈ d.passing e o, keep v)
    (hcover : ∀ v ∈ d.passing e o, ∀ f ∈ d.actualTargets,
      f ≠ d.coarse e → compatible f v → f ∈ d.competitors e o v) :
    (((d.passing e o).filter (fun v => d.actualAssignment k U compatible useful keep s v ≠
      some (d.coarse e))).card : ℝ) / ((d.full e o).card : ℝ) ≤ 1 / N := by
  have hcard := Finset.card_le_card
    (d.passing_actual_failure_subset_bad k U hAP N e o ho s hg
      compatible useful keep hc hu hk hcover)
  have hR : (((d.passing e o).filter (fun v =>
      d.actualAssignment k U compatible useful keep s v ≠ some (d.coarse e))).card : ℝ) ≤
      (((d.passing e o).filter (fun v => d.variableBad k U e o v s)).card : ℝ) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hR (Nat.cast_nonneg _)).trans
    (d.good_randomLossFraction_le k U N e s hg o ho)

end MatrixMultiplication.JointMaskedSelection.OrbitData

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_JointScalarOrbitAdmissibility
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointScalarOrbitAdmissibility

open JointPopulation JointCanonicalization PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ) (L R : H → Type*)

def ClassWeights (wl : ∀ h, L h → ℕ) (wr : ∀ h, R h → ℕ)
    (vl vr : H → Shape → ℕ) (e : Target counts) (w : RawPairs counts L R) : Prop :=
  ∀ h j, wl h (w h j).1 = vl h ((e h).val j) ∧
    wr h (w h j).2 = vr h ((e h).val j)

omit [Fintype H] [DecidableEq H] in
theorem classWeights_smul (wl : ∀ h, L h → ℕ) (wr : ∀ h, R h → ℕ)
    (vl vr : H → Shape → ℕ) (e : Target counts) :
    letI : MulAction (HalfClassPermutations (ClassPositions counts)) (RawPairs counts L R) :=
      EquivOrbitTransport.action (pairEquiv counts L R e)
    ∀ (g : HalfClassPermutations (ClassPositions counts)) (w : RawPairs counts L R),
      ClassWeights counts L R wl wr vl vr e w →
      ClassWeights counts L R wl wr vl vr e ((EquivOrbitTransport.action (pairEquiv counts L R e)).smul g w) := by
  let : MulAction (HalfClassPermutations (ClassPositions counts)) (RawPairs counts L R) :=
    EquivOrbitTransport.action (pairEquiv counts L R e)
  intro g w hw h j
  constructor
  · change wl h (w h ((positionEquiv counts e h).symm
      ⟨(e h).val j, (g.1 (h, (e h).val j)).symm (positionEquiv counts e h j).2⟩)).1 = _
    simpa only [positionEquiv_symm_shape] using
      (hw h ((positionEquiv counts e h).symm
        ⟨(e h).val j, (g.1 (h, (e h).val j)).symm (positionEquiv counts e h j).2⟩)).1
  · change wr h (w h ((positionEquiv counts e h).symm
      ⟨(e h).val j, (g.2 (h, (e h).val j)).symm (positionEquiv counts e h j).2⟩)).2 = _
    simpa only [positionEquiv_symm_shape] using
      (hw h ((positionEquiv counts e h).symm
        ⟨(e h).val j, (g.2 (h, (e h).val j)).symm (positionEquiv counts e h j).2⟩)).2

end MatrixMultiplication.JointScalarOrbitAdmissibility

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointCompatibilityRateLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityRateLimit

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityEntropyBound JointCompatibilityScaling Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape Pair Left Right : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]

def pairReferenceEntropy (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ) : ℝ :=
  ∑ c, (baseSize base c : ℝ) * finiteEntropy (q c)

def compatibilityRate (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (HL HR : (Σ c, Option (Shape c)) → ℝ) : ℝ :=
  baseEntropy base - pairReferenceEntropy base q +
    projectedReferenceEntropy base designatedLeft HL +
    projectedReferenceEntropy base designatedRight HR

end MatrixMultiplication.JointCompatibilityRateLimit

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupPairWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.JointTypeCounts MatrixMultiplication.JointCompatibilityIncidence

namespace MatrixMultiplication.JointCompatibilityControls

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

def groupCap (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (ε : ℝ) (g : Σ c, Option (Shape c)) : ℝ :=
  finiteEntropy (groupCenter base d law g) + ε

def control_mono_width
    {Pos Pair : C → Type*}
    [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
    (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
    (part : ∀ c, Pair c → A c) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) {χ χ' : ℝ}
    (H : (Σ c, Option (Shape c)) → ℝ)
    (w : FixedClassWords Pos Shape shapeCounts)
    (control : SideEntropyControl Pos Shape Pair A shapeCounts pairCounts part d law χ H w)
    (hχ : χ' ≤ χ) :
    SideEntropyControl Pos Shape Pair A shapeCounts pairCounts part d law χ' H w where
  residualLaw := control.residualLaw
  totalTarget := control.totalTarget
  totalError := control.totalError
  aggregate_window := control.aggregate_window
  mixture_balance := control.mixture_balance
  nonneg := control.nonneg
  designated_entropy c u hu q hq :=
    control.designated_entropy c u hu q (fun a => (hq a).trans hχ)
  residual_entropy c q hq := by
    apply control.residual_entropy c q
    intro a
    apply (hq a).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply add_le_add (le_refl _)
    exact mul_le_mul_of_nonneg_left hχ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

end MatrixMultiplication.JointCompatibilityControls

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupProjectedEntropy
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointNativeGroupedEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section NativeSupport

variable {A : Type*} [Fintype A]

abbrev SupportIndex (support : List Shape) := Fin support.length

end NativeSupport

end MatrixMultiplication.JointNativeGroupedEntropy

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_CWShapePhysicalPermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.CWShapePhysicalPermutation

open MatrixMultiplication.Foundation CWStrands
open scoped BigOperators

variable {F : Type*} [CommRing F]

theorem tensor_swapXY_inline_MatrixMultiplication_CWShapePhysicalPermutation (q : ℕ) (x y z : Fin (q + 2)) :
    FieldCW.tensor F q x y z = FieldCW.tensor F q y x z := by
  unfold FieldCW.tensor
  simp only [Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
  ring

theorem tensor_swapYZ_inline_MatrixMultiplication_CWShapePhysicalPermutation (q : ℕ) (x y z : Fin (q + 2)) :
    FieldCW.tensor F q x y z = FieldCW.tensor F q x z y := by
  exact (FieldCW.tensor_cyclic F q x y z).trans
    ((tensor_swapXY_inline_MatrixMultiplication_CWShapePhysicalPermutation q y z x).trans (FieldCW.tensor_cyclic F q x z y).symm)

theorem tensor_swapXZ_inline_MatrixMultiplication_CWShapePhysicalPermutation (q : ℕ) (x y z : Fin (q + 2)) :
    FieldCW.tensor F q x y z = FieldCW.tensor F q z y x := by
  exact (FieldCW.tensor_cyclic F q x y z).trans (tensor_swapXY_inline_MatrixMultiplication_CWShapePhysicalPermutation q y z x)

theorem tensor_permute (q : ℕ) (σ : Equiv.Perm (Fin 3))
    (a : Fin 3 → Fin (q + 2)) :
    FieldCW.tensor F q (a (σ 0)) (a (σ 1)) (a (σ 2)) =
      FieldCW.tensor F q (a 0) (a 1) (a 2) := by
  have h01 : σ 0 ≠ σ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h)
  have h02 : σ 0 ≠ σ 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (σ.injective h)
  have h12 : σ 1 ≠ σ 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h)
  generalize hs0 : σ 0 = s0 at *
  generalize hs1 : σ 1 = s1 at *
  generalize hs2 : σ 2 = s2 at *
  fin_cases s0 <;> fin_cases s1 <;> fin_cases s2 <;> try contradiction
  · rfl
  · exact (tensor_swapYZ_inline_MatrixMultiplication_CWShapePhysicalPermutation q (a 0) (a 1) (a 2)).symm
  · exact (tensor_swapXY_inline_MatrixMultiplication_CWShapePhysicalPermutation q (a 0) (a 1) (a 2)).symm
  · exact (FieldCW.tensor_cyclic F q (a 0) (a 1) (a 2)).symm
  · exact FieldCW.tensor_cyclic F q (a 2) (a 0) (a 1)
  · exact (tensor_swapXZ_inline_MatrixMultiplication_CWShapePhysicalPermutation q (a 0) (a 1) (a 2)).symm

theorem strand_permute {P : Type*} [Fintype P]
    (σ : Equiv.Perm (Fin 3)) (a : Fin 3 → P → Fin 7) :
    strand (F := F) P (a (σ 0)) (a (σ 1)) (a (σ 2)) =
      strand P (a 0) (a 1) (a 2) := by
  apply Finset.prod_congr rfl
  intro i _
  exact tensor_permute 5 σ (fun s => a s i)

end MatrixMultiplication.CWShapePhysicalPermutation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryTick

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldHistoryGroupedRecovery
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ) (ε slack : ℝ)

@[instance_reducible] def coarseTripleFintype (P : Type) [Fintype P] :
    Fintype (JointCoarseHashing.Triple P) := inferInstance

end MatrixMultiplication.AllFieldHistoryTick

end
end

end MatrixAllFields

end OAI
end


