-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
-- name    : EdgeSublinearMWIS_Main_NativeDetailedInterfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T14:24:59.91311+00:00
-- url     : https://prove2.me/theorems/4369ee89-97bd-44dd-8fa6-8d8eb6f5e73c
-- title:
--   Detailed state interfaces for native solver, rounding and recursive steps
-- statement:
--   These definitions expose the premises and postconditions of finer native execution steps: bounded signed rational arithmetic, matrix storage, LP frontend and certificate construction, region-growth rounding, point recovery, and recursive oracle collection. They include the finite input records, workspace and numeric bounds, stored context and output predicates required by those steps.
--
--   Writing $\sigma$ and $\tau$ for command environments, the interfaces are used in bounded operational specifications of the form
--   $$\forall\sigma,\ P(\sigma)\Longrightarrow\exists\tau,\ \operatorname{Run}_B(c,\sigma,\tau,T)\land Q(\sigma,\tau).$$
--   Here $B$ is the word bound, $c$ is the fixed command, and $T$ is an instruction bound. The bundle defines the state predicates and data used in such statements. Correctness, termination, resource comparisons and composition of the actual executions remain separate theorem obligations. The matrix-index bound is an immediate structural API for constructing finite row indices.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/CertificateFamilyEntries.lean (definitions and structure interfaces, starting at lines 10, 19)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/LexicographicBounds.lean (definitions and structure interfaces, starting at lines 13)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/LexicographicSupport.lean (definitions and structure interfaces, starting at lines 11)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamCertificateContext.lean (definitions and structure interfaces, starting at lines 11, 13)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamDecodedProgram.lean (definitions and structure interfaces, starting at lines 14, 19)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamFeasibilityQuery.lean (definitions and structure interfaces, starting at lines 27)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamFrontEndTotal.lean (definitions and structure interfaces, starting at lines 13)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamMatrixRows.lean (definitions and structure interfaces, starting at lines 14, 231)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamMatrixStorage.lean (definitions and structure interfaces, starting at lines 17)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamPointInitialization.lean (definitions and structure interfaces, starting at lines 11)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRational.lean (definitions and structure interfaces, starting at lines 45, 98)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamReadArray.lean (definitions and structure interfaces, starting at lines 13, 19)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamReadBody.lean (definitions and structure interfaces, starting at lines 27, 28, 29, 30)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamReadFraction.lean (definitions and structure interfaces, starting at lines 226)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRounding.lean (definitions and structure interfaces, starting at lines 11, 93)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSolverTotalExecution.lean (definitions and structure interfaces, starting at lines 12, 18)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/WordDecoding.lean (definitions and structure interfaces, starting at lines 12, 15)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/concepts/Lax263307/LinearRelaxation.lean (definitions and structure interfaces, starting at lines 39, 47, 48, 51, 53, 55, 58, 60)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/concepts/Lax263307/NearOracle.lean (definitions and structure interfaces, starting at lines 74)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/concepts/Lax263307/PowerBagBounds.lean (definitions and structure interfaces, starting at lines 11)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/concepts/Lax263307/RationalConditioning.lean (definitions and structure interfaces, starting at lines 20)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeArrayBounds.lean (definitions and structure interfaces, starting at lines 10)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeCollectionExecution.lean (definitions and structure interfaces, starting at lines 20)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeCollectionTrace.lean (definitions and structure interfaces, starting at lines 11, 16, 21)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeLargeNode.lean (definitions and structure interfaces, starting at lines 33, 48)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeMomentFamily.lean (definitions and structure interfaces, starting at lines 122)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeNearExecution.lean (definitions and structure interfaces, starting at lines 66)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeNodeAliases.lean (definitions and structure interfaces, starting at lines 18)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeNodePrecision.lean (definitions and structure interfaces, starting at lines 21, 25)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeQptasPositive.lean (definitions and structure interfaces, starting at lines 72, 73, 74, 75, 76, 77, 78, 79, 81, 82)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeRootWorkspace.lean (definitions and structure interfaces, starting at lines 17, 19)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/BallMassData.lean (definitions and structure interfaces, starting at lines 11, 14)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/BoundaryData.lean (definitions and structure interfaces, starting at lines 12, 15, 18)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/CertificatePostprocessing.lean (definitions and structure interfaces, starting at lines 12, 17)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/CutScoreData.lean (definitions and structure interfaces, starting at lines 11, 12, 13, 15, 17, 18, 19)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/CutScoreHeight.lean (definitions and structure interfaces, starting at lines 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/CutSweeps.lean (definitions and structure interfaces, starting at lines 12, 16, 19, 25)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/LargeBallRounding.lean (definitions and structure interfaces, starting at lines 12, 14, 17)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/LargePotentialData.lean (definitions and structure interfaces, starting at lines 10, 12, 55, 57, 58, 59, 60, 61, 62)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/MaskedMassData.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RadiusData.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RadiusSearchData.lean (definitions and structure interfaces, starting at lines 11, 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamArcMask.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamBallMask.lean (definitions and structure interfaces, starting at lines 14)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamBooleanArithmetic.lean (definitions and structure interfaces, starting at lines 11, 13)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamCutScore.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamEdgePortion.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamFind.lean (definitions and structure interfaces, starting at lines 9, 11)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamHistoryCut.lean (definitions and structure interfaces, starting at lines 25)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamHistoryPotential.lean (definitions and structure interfaces, starting at lines 26)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamLargeCut.lean (definitions and structure interfaces, starting at lines 24)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamLargePotential.lean (definitions and structure interfaces, starting at lines 47)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamMaskedSum.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamPotentialAverage.lean (definitions and structure interfaces, starting at lines 14)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamPotentialSweep.lean (definitions and structure interfaces, starting at lines 15)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRadiusSearch.lean (definitions and structure interfaces, starting at lines 13, 18, 19, 20, 21, 22, 23, 24, 48)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionBoundedLoop.lean (definitions and structure interfaces, starting at lines 11, 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionBranch.lean (definitions and structure interfaces, starting at lines 11, 14, 29)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionContext.lean (definitions and structure interfaces, starting at lines 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 56, 57, 58, 59, 60)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionCore.lean (definitions and structure interfaces, starting at lines 14, 27)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionCut.lean (definitions and structure interfaces, starting at lines 22, 24)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionInvariant.lean (definitions and structure interfaces, starting at lines 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 50, 51, 52, 53, 54)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionPrelude.lean (definitions and structure interfaces, starting at lines 13)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionRecord.lean (definitions and structure interfaces, starting at lines 11, 12, 13, 14, 16, 17, 18)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionScan.lean (definitions and structure interfaces, starting at lines 19)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionSetup.lean (definitions and structure interfaces, starting at lines 13, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 75)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionState.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRoundingInit.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamSelectedRegion.lean (definitions and structure interfaces, starting at lines 15)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamSetDistances.lean (definitions and structure interfaces, starting at lines 26)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamSetPotential.lean (definitions and structure interfaces, starting at lines 29)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamSmallRegion.lean (definitions and structure interfaces, starting at lines 21, 23, 24, 25, 26, 27, 34)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamThresholdCandidate.lean (definitions and structure interfaces, starting at lines 46)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamTruncatedSubtract.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionCharging.lean (definitions and structure interfaces, starting at lines 15)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionExecutionData.lean (definitions and structure interfaces, starting at lines 13)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionLoop.lean (definitions and structure interfaces, starting at lines 15, 19, 22, 23, 24, 25, 27, 31, 62, 71, 77)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionQueryData.lean (definitions and structure interfaces, starting at lines 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 25, 28, 31, 34, 35, 36, 38)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionQueryHeight.lean (definitions and structure interfaces, starting at lines 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionRounding.lean (definitions and structure interfaces, starting at lines 13, 16)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionRuntimeCorrespondence.lean (definitions and structure interfaces, starting at lines 151)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionRuntimeState.lean (definitions and structure interfaces, starting at lines 10, 11, 12, 13, 14, 16, 17, 18, 19, 21, 56)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionSearch.lean (definitions and structure interfaces, starting at lines 10, 13, 15, 23, 30, 35, 40, 45)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionSelection.lean (definitions and structure interfaces, starting at lines 13, 17, 38)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RegionVolume.lean (definitions and structure interfaces, starting at lines 9, 11, 13, 19, 22)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/ResidualData.lean (definitions and structure interfaces, starting at lines 12, 14, 17)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/SetDistanceData.lean (definitions and structure interfaces, starting at lines 45)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/UndirectedConversion.lean (definitions and structure interfaces, starting at lines 14)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/VolumeData.lean (definitions and structure interfaces, starting at lines 13, 16, 20)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/VolumeHeight.lean (definitions and structure interfaces, starting at lines 13, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24)

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Logic.Function.Iterate
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces

-- Solutions.RAM_Lax263307_LinearRelaxation
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: The independent-set relaxation and its exact hull
type: definition
---
For an $n$-vertex graph $G$, target $k$, and level $r$, the relaxation
$R_r(G,k)$ has coordinates $y_A$ for vertex sets $|A|\le r+2$ and constraints
$$y_\varnothing=1,\qquad 0\le y_A\le1,$$
$$y_{A\cup\{v\}}\le y_A\quad (|A|\le r+1),$$
$$y_A=0\quad\text{if }A\text{ is not independent},$$
$$\sum_v y_{A\cup\{v\}}=k y_A\quad (|A|\le r+1).$$
The exact hull $P_r(G,k)$ is the convex hull of the vectors
$y_A=\mathbf1[A\subseteq I]$ over independent sets $I$ of size $k$.
For $y_A>0$, conditioning on $A$ gives costs $x_v=y_{A\cup\{v\}}/y_A$.

# Formalization notes

The coordinate type contains exactly the sets of size at most $r+2$;
there are no coordinates for larger sets. The accessor is extended by zero
outside this domain, solely to simplify notation. Every constraint that
uses it supplies a size bound ensuring that it reads an actual coordinate.
The vector space and convex hull are over the reals, as in the paper;
the algorithms will use rational points in this space.
-/

namespace Lax263307.LinearRelaxation





/-- Read a coordinate, returning zero outside the truncated coordinate domain. -/
def value {n r : ℕ} (y : MomentVector n r) (A : Finset (Fin n)) : ℝ :=
  if h : A.card ≤ r + 2 then y ⟨A, h⟩ else 0



/-- The five families of linear constraints defining `R_r(G,k)`. -/
structure IsFeasible {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) : Prop where
  /-- The empty moment is normalized. -/
  normalized : value y ∅ = 1
  /-- Each moment lies in the unit interval. -/
  bounds : ∀ A, 0 ≤ y A ∧ y A ≤ 1
  /-- Adding a vertex cannot increase a moment. -/
  monotone : ∀ A : Finset (Fin n), A.card ≤ r + 1 →
    ∀ v, value y (insert v A) ≤ value y A
  /-- Nonindependent sets have zero moment. -/
  vanishes : ∀ A : Coordinate n r, ¬G.IsIndepSet (A.val : Set (Fin n)) → y A = 0
  /-- The cardinality constraint remains valid after conditioning. -/
  mass : ∀ A : Finset (Fin n), A.card ≤ r + 1 →
    ∑ v : Fin n, value y (insert v A) = (k : ℝ) * value y A







end Lax263307.LinearRelaxation

end

-- Solutions.RAM_Lax228581_Treewidth
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Treewidth
type: definition
---
A tree decomposition of a finite simple graph *G* consists of a finite tree
*T* and a bag of graph vertices at each node such that every graph
vertex occurs in a bag, the endpoints of every graph edge occur together in a
bag, and the nodes whose bags contain any fixed vertex induce a connected
subgraph of *T*.

The treewidth of *G* is the least *w* such that *G* has a tree
decomposition with every bag of size at most *w* + 1.

# Formalization notes

A tree decomposition always exists (a single node whose bag is all of the
vertices), so the infimum in `treewidth` ranges over a nonempty set. The
`Fintype` and `DecidableEq` hypotheses of `treewidth` are the uniform
signature shared by all graph parameters in this archive.
-/

namespace Lax228581.Treewidth

/-- A tree decomposition of a simple graph: a finite tree of nodes with a bag
of graph vertices at each node, such that the bags cover every vertex and
every edge, and the nodes whose bags contain any fixed vertex induce a
connected subgraph of the tree. -/
structure TreeDecomposition {V : Type} (G : SimpleGraph V) where
  /-- The node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree is finite. -/
  [nodeFintype : Fintype Node]
  /-- The graph on the decomposition nodes. -/
  tree : SimpleGraph Node
  /-- The node graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag assigned to each decomposition node. -/
  bag : Node → Finset V
  /-- Every graph vertex appears in at least one bag. -/
  vertex_mem_bag : ∀ v : V, ∃ i : Node, v ∈ bag i
  /-- Every graph edge has both endpoints together in at least one bag. -/
  edge_mem_bag : ∀ ⦃u v : V⦄, G.Adj u v → ∃ i : Node, u ∈ bag i ∧ v ∈ bag i
  /-- For each graph vertex, the nodes whose bags contain it induce a
  connected subgraph of the tree. -/
  bag_indices_connected :
    ∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected





end Lax228581.Treewidth

end

-- Solutions.RAM_Lax263307_PowerBagBounds
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.PowerBagBounds

open GraphClasses Lax228581.Treewidth

def HasPowerBagBound (C : GraphClass) (a A : ℕ) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)), G ∈ C n → ∃ D : TreeDecomposition G,
    ∀ i, (D.bag i).card ^ a ≤ A * (G.edgeSet.ncard + 1) ^ (a - 1)



end Lax263307.PowerBagBounds

end

-- Solutions.RAM_Lax263307_RationalConditioning
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.RationalConditioning

open LinearRelaxation Entropy





def realVector {n r : ℕ} (y : RationalVector n r) : MomentVector n r :=
  fun A => (y A : ℝ)




















end Lax263307.RationalConditioning

end

-- Solutions.RAM_Lax109476_LinearProgram
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Linear programs and their duals
type: definition
---
A linear program in inequality form is
$$\max\{c^T x: Ax\le b,\ x\ge0\}.$$
Its dual is
$$\min\{b^T y: A^T y\ge c,\ y\ge0\}.$$
All vector inequalities are componentwise. A feasible maximization program
is bounded above if one finite real number bounds the objective of every
feasible point. A primal point is optimal if it is feasible and no feasible
point has a larger objective.

# Formalization notes

There are `n` variables and `m` inequalities, indexed by `Fin n` and `Fin m`.
The coefficient data are shared by real and rational instances. Feasibility
and objective formulas are the same in either field. Both dimensions may be
zero. No feasibility, boundedness, optimizer, or optimum value is bundled
into the input data. Theorems state the necessary hypotheses explicitly.
Equality constraints and unrestricted variables can be represented by paired
inequalities and differences of nonnegative variables.
-/

open scoped BigOperators

namespace Lax109476.LinearProgram















/-- The real primal feasible set is nonempty. -/
def IsFeasible {m n : ℕ} (P : Program ℝ m n) : Prop :=
  ∃ x, PrimalFeasible P x





end Lax109476.LinearProgram

end

-- Solutions.RAM_Lax109476_RationalCertificates
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Exact rational solution certificates
type: definition
---
A rational linear program is a linear program with rational coefficients,
still optimized over real variables. Its outcomes have three certificate forms:

* an optimal primal point and matching dual multipliers;
* nonnegative Farkas multipliers certifying infeasibility;
* a feasible primal point and an improving recession direction certifying
  unboundedness.

Every coordinate in these certificates is rational, and all certificate
conditions can be checked by exact rational arithmetic.

# Formalization notes

The three constructors carry precisely the witnesses needed for their
claims. The predicates use the same row, column, and objective formulas
as the real program. The real interpretation casts the coefficient data
and witness coordinates exactly. No outcome or correctness proof is
assumed as part of the input.
-/

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

/-- Interpret rational coefficient data as a real linear program. -/
def toReal {m n : ℕ} (P : Program ℚ m n) : Program ℝ m n where
  A i j := P.A i j
  b i := P.b i
  c j := P.c j









end Lax109476.RationalCertificates

end

-- Solutions.RAM_Lax109476Proofs_LexicographicSupport
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicSupport



def Feasible {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Prop := (∀ j, 0 ≤ x j) ∧ C *ᵥ x = b





end Lax109476Proofs.LexicographicSupport

end

-- Solutions.RAM_Lax109476Proofs_LexicographicBounds
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicBounds

open LexicographicSupport LexicographicMinima
open Lax109476.LinearProgram Lax109476.RationalCertificates

def coordinateCap (m n H : ℕ) : ℕ := n.factorial * (m * H ^ 2 + 1) ^ n





end Lax109476Proofs.LexicographicBounds

end

-- Solutions.RAM_Lax109476Proofs_RamRational
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic









def FractionOutput (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d") = q ∧
    σ.vars "rat.n" = q.num.natAbs ∧ σ.vars "rat.d" = q.den ∧ σ.vars "rat.s" ≤ 1









def fractionInputs (s₁ n₁ d₁ s₂ n₂ d₂ : ℕ) (σ : Env) : Prop :=
  σ.vars "left.s" = s₁ ∧ σ.vars "left.n" = n₁ ∧ σ.vars "left.d" = d₁ ∧
    σ.vars "right.s" = s₂ ∧ σ.vars "right.n" = n₂ ∧ σ.vars "right.d" = d₂















end Lax109476Proofs.RamRational

end

-- Solutions.RAM_Lax109476Proofs_RamRounding
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRounding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamArithmetic RationalRounding

def ceilQuotient (n d : ℕ) : ℕ := n / d + if n % d = 0 then 0 else 1













def upperMagnitude (s n d D : ℕ) : ℕ :=
  if s = 1 then 0 else ceilQuotient (n * D ^ 2) d









end Lax109476Proofs.RamRounding

end

-- Solutions.RAM_Lax109476Proofs_WordDecoding
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.WordDecoding

open Lax109476.LinearProgram Lax109476.RationalEncoding

def signedNumerator (sign magnitude : ℕ) : ℤ :=
  if sign = 1 then -(magnitude : ℤ) else magnitude

def readRational : List ℕ → Option (ℚ × List ℕ)
  | sign :: magnitude :: denominator :: rest =>
    if sign ≤ 1 ∧ 0 < denominator then
      some ((signedNumerator sign magnitude : ℚ) / denominator, rest)
    else none
  | _ => none































end Lax109476Proofs.WordDecoding

end

-- Solutions.RAM_Lax109476Proofs_RamReadFraction
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReadFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput RamRational RamArithmetic































def safeValue (xs : List ℕ) (v : ℕ) : ℚ :=
  if v = 1 then (WordDecoding.readRational xs).map Prod.fst |>.getD 0 else 0



end Lax109476Proofs.RamReadFraction

end

-- Solutions.RAM_Lax109476Proofs_RamReadArray
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReadArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadFraction RamRational RamRationalArrays RamCenterUpdate
open RationalArithmeticBounds RamArithmetic

/-- Pure descriptions of the values and flags produced by the uniform loop.
They are specification parameters, not commands or input-dependent code. -/
def flag (xs : List ℕ) (v : ℕ) : ℕ → ℕ
  | 0 => v
  | k + 1 => if WordDecoding.readRational (xs.drop (3 * k)) = none then 0 else flag xs v k

def values (xs : List ℕ) (v n : ℕ) : Fin n → ℚ :=
  fun i => safeValue (xs.drop (3 * i.val)) (flag xs v i.val)



































end Lax109476Proofs.RamReadArray

end

-- Solutions.RAM_Lax109476Proofs_RamMatrixRows
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax109476Proofs.RamMatrixRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRational RamDotProduct RationalArithmeticBounds

/-- A row occupies a bounded slice of three arrays. The arrays may contain
other rows before or after this slice. -/
def Slice (a : String) (qs : List ℚ) (base : ℕ) (σ : Env) : Prop :=
  base + qs.length ≤ (σ.arrs (a ++ ".s")).length ∧
  base + qs.length ≤ (σ.arrs (a ++ ".n")).length ∧
  base + qs.length ≤ (σ.arrs (a ++ ".d")).length ∧
  (∀ i (hi : i < qs.length), (σ.arrs (a ++ ".s")).getD (base + i) 0 = rationalSign qs[i]) ∧
  (∀ i (hi : i < qs.length), (σ.arrs (a ++ ".n")).getD (base + i) 0 = qs[i].num.natAbs) ∧
  (∀ i (hi : i < qs.length), (σ.arrs (a ++ ".d")).getD (base + i) 0 = qs[i].den)





























/-- Row-major representation; every row has its explicit bounded slice. -/
def MatrixRows {m n : ℕ} (a : String) (A : Matrix (Fin m) (Fin n) ℚ) (σ : Env) : Prop :=
  ∀ i, Slice a (List.ofFn (A i)) (i.val * n) σ





end Lax109476Proofs.RamMatrixRows

end

-- Solutions.RAM_Lax109476Proofs_RamMatrixStorage
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamMatrixStorage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows





theorem row_index_lt {m n : ℕ} (i : Fin m) (j : Fin n) : i.val * n + j.val < m * n := by
  have hmul := Nat.mul_le_mul_right n i.isLt
  calc
    _ < i.val * n + n := Nat.add_lt_add_left j.isLt _
    _ = (i.val + 1) * n := by ring
    _ ≤ _ := hmul







end Lax109476Proofs.RamMatrixStorage

end

-- Solutions.RAM_Lax109476Proofs_RamReadBody
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReadBody

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBlock RamRationalArrays RamEllipsoidStep RamAdvanceState







def afterA (xs : List ℕ) (m n : ℕ) : List ℕ := xs.drop (3 * (m * n))
def flagA (xs : List ℕ) (v m n : ℕ) : ℕ := flag xs v (m * n)
def afterB (xs : List ℕ) (m n : ℕ) : List ℕ := (afterA xs m n).drop (3 * m)
def flagB (xs : List ℕ) (v m n : ℕ) : ℕ := flag (afterA xs m n) (flagA xs v m n) m













end Lax109476Proofs.RamReadBody

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateContext
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateContext

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

def fields : List String := ["source.m", "source.n", "system.m", "system.n"]

def Context {m n : ℕ} (P : Program ℤ m n) (r s : ℕ) (σ : Env) : Prop :=
  RamCertificateSource.Data P σ ∧ σ.vars "system.m" = r ∧ σ.vars "system.n" = s







end Lax109476Proofs.RamCertificateContext

end

-- Solutions.RAM_Lax109476Proofs_RamFeasibilityQuery
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFeasibilityQuery

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamMatrixStorage IntegerEncoding RationalArithmeticBounds RamCopyBlock





def Input {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  RamClearProgram.IntegerRep P σ ∧ Workspace m n σ ∧
    σ.vars "lp.m" = m ∧ σ.vars "lp.n" = n ∧ σ.vars "decode.count" = m * n ∧
    σ.vars "input.bits" = bitSize (encodeProgram P)



end Lax109476Proofs.RamFeasibilityQuery

end

-- Solutions.RAM_Lax109476Proofs_RamPointInitialization
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPointInitialization

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRecoveryThreshold RamEllipsoidStep RationalArithmeticBounds

def Base {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  Represents "point.A" (RamMatrixStorage.flatten P.A) σ ∧ Represents "point.b" (List.ofFn P.b) σ ∧
    σ.vars "point.m" = m ∧ σ.vars "point.n" = n










end Lax109476Proofs.RamPointInitialization

end

-- Solutions.RAM_Lax109476Proofs_CertificateFamilyEntries
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.CertificateFamilyEntries

open Lax109476.LinearProgram
open CertificateFamilyPrograms IntegerCertificates CertificateSearch IndexedPointRecovery

def pairEntry {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + (n + 2))) (j : Fin (n + m)) : ℤ :=
  if hi : i.val < m then
    if hj : j.val < n then P.A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else if hir : i.val < m + n then
    if hj : j.val < n then 0 else -P.A ⟨j.val - n, by omega⟩ ⟨i.val - m, by omega⟩
  else if i.val = m + n then
    if hj : j.val < n then P.c ⟨j.val, hj⟩ else -P.b ⟨j.val - n, by omega⟩
  else if hj : j.val < n then -P.c ⟨j.val, hj⟩ else P.b ⟨j.val - n, by omega⟩

def pairRhs {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + (n + 2))) : ℤ :=
  if hi : i.val < m then P.b ⟨i.val, hi⟩
  else if hir : i.val < m + n then -P.c ⟨i.val - m, by omega⟩ else 0





















end Lax109476Proofs.CertificateFamilyEntries

end

-- Solutions.RAM_Lax109476Proofs_RamDecodedProgram
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamDecodedProgram

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBody RamRationalArrays RationalArithmeticBounds

def bodyProgram (xs : List ℕ) (m n : ℕ) : Program ℚ m n :=
  { A := fun i j => values xs 1 (m * n) ⟨i.val * n + j.val, RamMatrixStorage.row_index_lt i j⟩
    b := values (afterA xs m n) (flagA xs 1 m n) m
    c := values (afterB xs m n) (flagB xs 1 m n) n }

def decodedProgram (xs : List ℕ) : Program ℚ (xs.headD 0) (xs.tail.headD 0) :=
  bodyProgram (xs.drop 2) (xs.headD 0) (xs.tail.headD 0)



















end Lax109476Proofs.RamDecodedProgram

end

-- Solutions.RAM_Lax109476Proofs_RamFrontEndTotal
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFrontEndTotal

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding RamDecodedProgram

def Input (B : ℕ) (xs : List ℕ) (σ : Env) : Prop := RamDecoder.Input B xs σ ∧
  Extents "int.A" (if RamReadHeader.ValidDimensions xs then xs.headD 0 * xs.tail.headD 0 else 0) σ ∧
  Extents "int.b" (if RamReadHeader.ValidDimensions xs then xs.headD 0 else 0) σ ∧
  Extents "int.c" (if RamReadHeader.ValidDimensions xs then xs.tail.headD 0 else 0) σ








end Lax109476Proofs.RamFrontEndTotal

end

-- Solutions.RAM_Lax109476Proofs_RamSolverTotalExecution
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSolverTotalExecution

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamSolverWorkspace RamDecodedProgram RamUniformSolverBounds

def Input (B : ℕ) (xs : List ℕ) (σ : Env) : Prop :=
  RamFrontEndTotal.Input B xs σ ∧
  Extents "source.A" (xs.headD 0 * xs.tail.headD 0) σ ∧
  Extents "source.b" (xs.headD 0) σ ∧ Extents "source.c" (xs.tail.headD 0) σ ∧
  All (xs.headD 0) (xs.tail.headD 0) (stackLength (bitSize xs)) σ

def Result (xs : List ℕ) (σ τ : Env) : Prop :=
  (τ.vars "input.valid" = 0 ∧ τ.out = σ.out) ∨ RamSolverFinish.Result (decodedProgram xs) σ τ






end Lax109476Proofs.RamSolverTotalExecution

end

-- Solutions.RAM_Lax263307_NearOracle
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: The recursive oracle near the moment relaxation
type: definition
---
The oracle searches for a heavy conditioning set, computes separators,
and queries the resulting parts. Its possible outputs are an independent
set, a component cut, or rejection.

The correctness predicate requires an approximation guarantee for a found
set and a valid inequality with a quantitative gap for a returned cut.
It rules out rejection under the oracle's hypotheses.

# Formalization notes

`ChildCorrect` specifies the recursive answers on balanced parts.
`Correct` specifies the corresponding answer or cut at the current level.
The function itself is computable for the supplied flow solver and child
queries.
-/

namespace Lax263307.NearOracle

open AlgorithmParameters (level load sparsity)
open ComponentCutEncoding (coefficient evaluate)
open ComputedRounding (collect)
open ComputedSeparators (cuts pieces step)
open HeavyRationalConditioning (findHeavyConditioning)
open scoped NNRat
open LinearRelaxation RationalConditioning











def Correct {n r : ℕ} (G : SimpleGraph (Fin n)) (k h D : ℕ) (η : ℝ)
    (x : MomentVector n r) : Result n → Prop
  | .found I => G.IsIndepSet (I : Set (Fin n)) ∧
      (1 - 4 * (1 / (D : ℝ))) ^ (h + 1) * (k : ℝ) ≤ I.card
  | .cut A C u => A.card ≤ r ∧ u ≤ n ∧ IsIndependenceBound G C u ∧
      (∀ z ∈ independentSetHull G k r,
        evaluate (coefficient A C u) z ≤ 0) ∧
      η * (1 / (D : ℝ)) ^ 2 / (16 * n) ≤
        evaluate (coefficient A C u) x ∧
      (∑ T : Coordinate n r, |(coefficient A C u T : ℝ)|) ≤ 2 * n
  | .reject => False

end Lax263307.NearOracle

end

-- Solutions.RAM_Lax455465Proofs_RegionVolume
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax455465Proofs.RegionVolume

abbrev Matrix (n : ℕ) := Fin n → Fin n → ℚ

def edgePortion (length base radius : ℚ) : ℚ := min length (max (radius - base) 0)

/-- Seeded exact rational volume of an outward ball. Inward balls use the
transposed capacity/length arrays and distances towards the root. -/
def volume {n : ℕ} (capacity length : Matrix n) (distance : Fin n → ℚ)
    (seed radius : ℚ) : ℚ :=
  seed + ∑ u, ∑ v, capacity u v * edgePortion (length u v) (distance u) radius

def weight {n : ℕ} (capacity length : Matrix n) : ℚ :=
  ∑ u, ∑ v, capacity u v * length u v

/-- The strict ball is the left limit at a candidate threshold. -/
def boundary {n : ℕ} (capacity : Matrix n) (distance : Fin n → ℚ) (radius : ℚ) : ℚ :=
  ∑ u, ∑ v, if distance u < radius ∧ radius ≤ distance v then capacity u v else 0



















end Lax455465Proofs.RegionVolume

end

-- Solutions.RAM_Lax455465Proofs_RegionSearch
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RegionSearch

open RegionVolume

/-- Rational grid; no logarithm or real arithmetic is executed. -/
def grid (k : ℕ) (delta : ℚ) (j : ℕ) : ℚ := delta * j / k

def slope (k : ℕ) (delta : ℚ) : ℚ := k / delta

/-- Runtime candidates need no sorting: grid endpoints followed by both
vertex-distance vectors clipped to the radius budget. -/
def candidates {n : ℕ} (outDistance inDistance : Fin n → ℚ)
    (k : ℕ) (delta : ℚ) : List ℚ :=
  (List.range (k+1)).map (grid k delta) ++
    List.ofFn (fun v => min delta (max (outDistance v) 0)) ++
    List.ofFn (fun v => min delta (max (inDistance v) 0))

/-- The orientation is computed separately, for example by comparing the
two ball masses. The radius search works for any such choice. -/
def selectedVolume {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed : ℚ) (direction : ℚ → Bool) (r : ℚ) : ℚ :=
  if direction r then volume capacity length outDistance seed r
  else volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed r

def selectedBoundary {n : ℕ} (capacity : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (direction : ℚ → Bool) (r : ℚ) : ℚ :=
  if direction r then boundary capacity outDistance r
  else boundary (fun u v => capacity v u) inDistance r

def Good {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed beta : ℚ) (direction : ℚ → Bool) (r : ℚ) : Prop :=
  selectedBoundary capacity outDistance inDistance direction r ≤
    beta * selectedVolume capacity length outDistance inDistance seed direction r

instance {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed beta : ℚ) (direction : ℚ → Bool) (r : ℚ) :
    Decidable (Good capacity length outDistance inDistance seed beta direction r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- First successful threshold in the actual finite candidate list. -/
def search {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed delta : ℚ) (p : ℕ)
    (direction : ℚ → Bool) : Option ℚ :=
  (candidates outDistance inDistance (RegionBudget.steps p) delta).find? fun r =>
    decide (0 < r ∧ Good capacity length outDistance inDistance seed
      (slope (RegionBudget.steps p) delta) direction r)

























end Lax455465Proofs.RegionSearch

end

-- Solutions.RAM_Lax455465Proofs_RegionCharging
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax455465Proofs.RegionCharging

open RegionVolume



/-- Strict rational ball used by the event-threshold search. -/
def ball {n : ℕ} (distance : Fin n → ℚ) (r : ℚ) : Finset (Fin n) :=
  Finset.univ.filter fun v => distance v < r

























end Lax455465Proofs.RegionCharging

end

-- Solutions.RAM_Lax455465Proofs_RegionSelection
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionSelection

open RegionCharging

/-- Rational mass of a strict ball in the current residual weights. -/
def ballMass {n : ℕ} (weights distance : Fin n → ℚ) (r : ℚ) : ℚ :=
  ∑ v ∈ ball distance r, weights v

/-- Ties select the outward ball. -/
def direction {n : ℕ} (weights outDistance inDistance : Fin n → ℚ) (r : ℚ) : Bool :=
  decide (ballMass weights outDistance r ≤ ballMass weights inDistance r)







def chooseRoot {n : ℕ} (weights : Fin n → ℚ) : Option (Fin n) :=
  (List.finRange n).find? fun v => decide (0 < weights v)











end Lax455465Proofs.RegionSelection

end

-- Solutions.RAM_Lax455465Proofs_CutSweeps
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators NNRat NNReal

namespace Lax455465Proofs.CutSweeps

open Lax455465.ProductNetwork Lax455465.RationalEncoding

/-- Rational cut quantities used by the algorithm, without real comparisons. -/
def massQ {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ :=
  ∑ v ∈ S, (I.weight v : ℚ)

def capacityQ {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, (I.capacity u v : ℚ)

def admissibleQ {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : Prop :=
  0 < massQ I S ∧ 0 < massQ I Sᶜ



def ratioQ {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ :=
  capacityQ I S / (massQ I S * massQ I Sᶜ)































end Lax455465Proofs.CutSweeps

end

-- Solutions.RAM_Lax455465Proofs_LargeBallRounding
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax455465Proofs.LargeBallRounding

open Lax455465.RationalEncoding CutSweeps RationalDistances

def total {n : ℕ} (I : RationalInstance n) : ℚ := ∑ v, (I.weight v : ℚ)

def mass {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ :=
  ∑ v ∈ S, (I.weight v : ℚ)

def distanceSeparation {n : ℕ} (I : RationalInstance n) (d : Distance n) : ℚ :=
  ∑ u, ∑ v, (I.weight u : ℚ) * I.weight v * d u v























end Lax455465Proofs.LargeBallRounding

end

-- Solutions.RAM_Lax455465Proofs_RegionLoop
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionLoop

open Lax455465.RationalEncoding RegionVolume RegionCharging RegionSelection RationalDistances

/-- Residual arrays are determined by the active vertex set. -/
def weights {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) : Fin n → ℚ :=
  fun v => if v ∈ active then (I.weight v : ℚ) else 0

def capacity {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) : Matrix n :=
  fun u v => if u ∈ active ∧ v ∈ active then (I.capacity u v : ℚ) else 0

structure Region (n : ℕ) where
  root : Fin n
  radius : ℚ
  outward : Bool

def Region.ball {n : ℕ} (R : Region n) (d : Distance n) : Finset (Fin n) :=
  if R.outward then RegionCharging.ball (d R.root) R.radius
  else RegionCharging.ball (fun v => d v R.root) R.radius

def chooseDirection {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (active : Finset (Fin n)) (root : Fin n) : ℚ → Bool :=
  direction (weights I active) (d root) (fun v => d v root)





/-- A removed small ball has the actual search guarantee at its selected orientation. -/
def StepGood {n : ℕ} (I : RationalInstance n) (d : Distance n) (seed delta : ℚ) (p : ℕ)
    (active : Finset (Fin n)) (R : Region n) : Prop :=
  0 < weights I active R.root ∧ 0 < R.radius ∧ R.radius ≤ delta ∧
  R.outward = chooseDirection I d active R.root R.radius ∧
  RegionSearch.Good (capacity I active) d (d R.root) (fun v => d v R.root)
    seed (RegionSearch.slope (RegionBudget.steps p) delta) (chooseDirection I d active R.root) R.radius ∧
  (∑ v ∈ R.ball d, weights I active v) < (2 / 3 : ℚ) * LargeBallRounding.total I

def ValidHistory {n : ℕ} (I : RationalInstance n) (d : Distance n) (seed delta : ℚ) (p : ℕ) :
    Finset (Fin n) → List (Region n) → Prop
  | active, [] => (support (weights I active)).card = 0
  | active, R :: rest => StepGood I d seed delta p active R ∧
      ValidHistory I d seed delta p (active \ R.ball d) rest

def LargeGood {n : ℕ} (I : RationalInstance n) (d : Distance n) (delta : ℚ) (R : Region n) : Prop :=
  0 < R.radius ∧ R.radius ≤ delta ∧
  (2 / 3 : ℚ) * LargeBallRounding.total I ≤ LargeBallRounding.mass I (RegionCharging.ball (d R.root) R.radius) ∧
  (2 / 3 : ℚ) * LargeBallRounding.total I ≤ LargeBallRounding.mass I (RegionCharging.ball (fun v => d v R.root) R.radius)

















end Lax455465Proofs.RegionLoop

end

-- Solutions.RAM_Lax455465Proofs_RegionRounding
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax455465Proofs.RegionRounding

open Lax455465.RationalEncoding RegionLoop CutSweeps RationalDistances



def metricCost {n : ℕ} (I : RationalInstance n) (d : Distance n) : ℚ :=
  RegionVolume.weight (fun u v => (I.capacity u v : ℚ)) d

def radiusBudget {n : ℕ} (I : RationalInstance n) : ℚ := 1 / (4 * LargeBallRounding.total I ^ 2)













end Lax455465Proofs.RegionRounding

end

-- Solutions.RAM_Lax455465Proofs_RamBooleanArithmetic
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamBooleanArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def bit (b : Bool) : ℚ≥0 := if b then 1 else 0

def flag (mode : Option Bool) (a b : Bool) : Bool := match mode with
  | none => a && b
  | some true => a && !b
  | some false => !a && b





end Lax455465Proofs.RamBooleanArithmetic

end

-- Solutions.RAM_Lax455465Proofs_RamMaskedSum
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamMaskedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def coefficients (qs mask : List ℚ≥0) : List ℚ≥0 :=
  List.ofFn fun i : Fin qs.length => if (mask.getD i.val 0).num = 1 then qs[i.val] else 0















end Lax455465Proofs.RamMaskedSum

end

-- Solutions.RAM_Lax455465Proofs_MaskedMassData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.MaskedMassData

open LpInputSize
open scoped BigOperators NNRat

def flags {n : ℕ} (mask : Fin n → Bool) : List ℚ≥0 := List.ofFn fun v => if mask v then 1 else 0









end Lax455465Proofs.MaskedMassData

end

-- Solutions.RAM_Lax455465Proofs_RamArcMask
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamArcMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix DirectedFlowLP
open scoped NNRat

def matrix {n : ℕ} (mode : Option Bool) (mask : Fin n → Bool) : Matrix n :=
  fun u v => RamBooleanArithmetic.bit (RamBooleanArithmetic.flag mode (mask u) (mask v))













end Lax455465Proofs.RamArcMask

end

-- Solutions.RAM_Lax455465Proofs_RamBallMask
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamBallMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar
open scoped NNRat

def flag (q radius : ℚ≥0) : ℚ≥0 := if (q : ℚ) < (radius : ℚ) then 1 else 0











end Lax455465Proofs.RamBallMask

end

-- Solutions.RAM_Lax455465Proofs_BallMassData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.BallMassData

open scoped BigOperators NNRat

def mask {n : ℕ} (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : List ℚ≥0 :=
  (List.ofFn distance).map (fun q => RamBallMask.flag q radius)

def mass {n : ℕ} (weights distance : Fin n → ℚ≥0) (radius : ℚ≥0) : ℚ≥0 :=
  (RamMaskedSum.coefficients (List.ofFn weights) (mask distance radius)).sum





end Lax455465Proofs.BallMassData

end

-- Solutions.RAM_Lax455465Proofs_BoundaryData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.BoundaryData

open MetricMatrix
open scoped BigOperators NNRat

def vertices {n : ℕ} (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : Fin n → Bool :=
  fun v => decide ((distance v : ℚ) < (radius : ℚ))

def arcs {n : ℕ} (outward : Bool) (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : Matrix n :=
  RamArcMask.matrix (some outward) (vertices distance radius)

def value {n : ℕ} (outward : Bool) (capacity : Matrix n)
    (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : ℚ≥0 :=
  (RamMaskedSum.coefficients (values capacity) (values (arcs outward distance radius))).sum







end Lax455465Proofs.BoundaryData

end

-- Solutions.RAM_Lax455465Proofs_RamTruncatedSubtract
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamTruncatedSubtract

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def value (a b : ℚ≥0) : ℚ≥0 := ⟨max ((a : ℚ)-(b : ℚ)) 0, le_max_right _ _⟩







end Lax455465Proofs.RamTruncatedSubtract

end

-- Solutions.RAM_Lax455465Proofs_RamEdgePortion
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamEdgePortion

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

/-- The unsigned part of an edge lying within a radius. -/
def value (length base radius : ℚ≥0) : ℚ≥0 := min length (RamTruncatedSubtract.value radius base)










end Lax455465Proofs.RamEdgePortion

end

-- Solutions.RAM_Lax455465Proofs_VolumeData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.VolumeData

open MetricMatrix LpInputSize
open scoped BigOperators NNRat

def base {n : ℕ} (outward : Bool) (distance : Fin n → ℚ≥0) (u v : Fin n) : ℚ≥0 :=
  if outward then distance u else distance v

def coefficients {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : List ℚ≥0 :=
  values (fun u v => capacity u v * RamEdgePortion.value (length u v) (base outward distance u v) radius)

def value {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (seed radius : ℚ≥0) : ℚ≥0 :=
  seed + (coefficients outward capacity length distance radius).sum







end Lax455465Proofs.VolumeData

end

-- Solutions.RAM_Lax455465Proofs_RegionQueryData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RegionQueryData

open MetricMatrix
open scoped NNRat

structure Query (n : ℕ) where
  weights : Fin n → ℚ≥0
  capacity : Matrix n
  length : Matrix n
  outDistance : Fin n → ℚ≥0
  inDistance : Fin n → ℚ≥0
  seed : ℚ≥0
  beta : ℚ≥0
  radius : ℚ≥0

def direction {n : ℕ} (q : Query n) (r : ℚ) : Bool :=
  RegionSelection.direction (fun v => (q.weights v : ℚ)) (fun v => (q.outDistance v : ℚ))
    (fun v => (q.inDistance v : ℚ)) r

def distance {n : ℕ} (q : Query n) (outward : Bool) : Fin n → ℚ≥0 :=
  if outward then q.outDistance else q.inDistance

def boundaryAt {n : ℕ} (q : Query n) (outward : Bool) : ℚ≥0 :=
  BoundaryData.value outward q.capacity (distance q outward) q.radius

def volumeAt {n : ℕ} (q : Query n) (outward : Bool) : ℚ≥0 :=
  VolumeData.value outward q.capacity q.length (distance q outward) q.seed q.radius

def boundary {n : ℕ} (q : Query n) : ℚ≥0 := boundaryAt q (direction q q.radius)
def volume {n : ℕ} (q : Query n) : ℚ≥0 := volumeAt q (direction q q.radius)
def bound {n : ℕ} (q : Query n) : ℚ≥0 := q.beta*volume q

def accepted {n : ℕ} (q : Query n) : Bool := decide (0 < (q.radius : ℚ) ∧
  RegionSearch.Good (rational q.capacity) (rational q.length)
    (fun v => (q.outDistance v : ℚ)) (fun v => (q.inDistance v : ℚ)) q.seed q.beta (direction q) q.radius)







end Lax455465Proofs.RegionQueryData

end

-- Solutions.RAM_Lax455465Proofs_VolumeHeight
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.VolumeHeight

open LpInputSize MetricMatrix
open scoped NNRat




structure Bounds {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (seed radius : ℚ≥0) (H : ℕ) : Prop where
  capacityBound : ∀ u v, Height (2^H) (capacity u v : ℚ)
  lengthBound : ∀ u v, Height (2^H) (length u v : ℚ)
  distanceBound : ∀ v, Height (2^H) (distance v : ℚ)
  seedBound : Height (2^H) (seed : ℚ)
  radiusBound : Height (2^H) (radius : ℚ)
  differenceBound : ∀ v, Height (2^H) (RamTruncatedSubtract.value radius (distance v) : ℚ)
  portionBound : ∀ u v, Height (2^H) (RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius : ℚ)
  coefficientBound : ∀ q ∈ VolumeData.coefficients outward capacity length distance radius, Height (2^H) (q : ℚ)
  prefixBound : ∀ i, Height (2^H) ((((VolumeData.coefficients outward capacity length distance radius).take i).sum : ℚ≥0) : ℚ)
  valueBound : Height (2^H) (VolumeData.value outward capacity length distance seed radius : ℚ)



end Lax455465Proofs.VolumeHeight

end

-- Solutions.RAM_Lax455465Proofs_RegionQueryHeight
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RegionQueryHeight

open RegionQueryData LpInputSize
open scoped NNRat



structure Bounds {n : ℕ} (q : Query n) (H : ℕ) : Prop where
  weightsBound : ∀ v, Height (2^H) (q.weights v : ℚ)
  capacityBound : ∀ u v, Height (2^H) (q.capacity u v : ℚ)
  lengthBound : ∀ u v, Height (2^H) (q.length u v : ℚ)
  distanceBound : ∀ b v, Height (2^H) (distance q b v : ℚ)
  seedBound : Height (2^H) (q.seed : ℚ)
  betaBound : Height (2^H) (q.beta : ℚ)
  radiusBound : Height (2^H) (q.radius : ℚ)
  volumeBounds : ∀ b, VolumeHeight.Bounds b q.capacity q.length (distance q b) q.seed q.radius H
  massPrefixBound : ∀ b i, Height (2^H)
    ((((RamMaskedSum.coefficients (List.ofFn q.weights) (BallMassData.mask (distance q b) q.radius)).take i).sum : ℚ≥0) : ℚ)
  boundaryPrefixBound : ∀ b i, Height (2^H)
    ((((RamMaskedSum.coefficients (MetricMatrix.values q.capacity) (MetricMatrix.values (BoundaryData.arcs b (distance q b) q.radius))).take i).sum : ℚ≥0) : ℚ)
  boundBound : Height (2^H) (bound q : ℚ)



end Lax455465Proofs.RegionQueryHeight

end

-- Solutions.RAM_Lax455465Proofs_RamRegionContext
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionContext

open RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

structure Input {n : ℕ} (q : Query n) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  radiusData : Stored "region.radius" q.radius σ
  seedData : Stored "round.seed" q.seed σ
  betaData : Stored "round.slope" q.beta σ
  weightsData : Prefix (RamUnsignedBuffer.encode (List.ofFn q.weights)) "region.weights" σ
  capacityData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values q.capacity)) "region.capacities" σ
  lengthData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values q.length)) "metric.old" σ
  outData : Prefix (RamUnsignedBuffer.encode (List.ofFn q.outDistance)) "region.out" σ
  inData : Prefix (RamUnsignedBuffer.encode (List.ofFn q.inDistance)) "region.in" σ










structure Masks {n : ℕ} (q : Query n) (σ : Env) : Prop where
  input : Input q σ
  outMask : Prefix (RamUnsignedBuffer.encode (BallMassData.mask q.outDistance q.radius)) "region.outMask" σ
  inMask : Prefix (RamUnsignedBuffer.encode (BallMassData.mask q.inDistance q.radius)) "region.inMask" σ
  directionValue : σ.vars "region.outward" = if direction q q.radius then 1 else 0









end Lax455465Proofs.RamRegionContext

end

-- Solutions.RAM_Lax455465Proofs_RadiusData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RadiusData

open LpInputSize
open scoped NNRat

def candidates {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0) : List ℚ≥0 :=
  (List.range (k+1)).map (fun j : ℕ => (delta/(k : ℚ≥0))*(j : ℚ≥0)) ++
    List.ofFn (fun v => min delta (outDistance v)) ++ List.ofFn (fun v => min delta (inDistance v))







end Lax455465Proofs.RadiusData

end

-- Solutions.RAM_Lax455465Proofs_RamFind
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamFind

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def first (predicate : ℕ → Bool) (count : ℕ) : Option ℕ := (List.range count).find? predicate

def Matches (result : Option ℕ) (σ : Env) : Prop :=
  match result with
  | none => σ.vars "find.found" = 0
  | some i => σ.vars "find.found" = 1 ∧ σ.vars "find.result" = i


















end Lax455465Proofs.RamFind

end

-- Solutions.RAM_Lax455465Proofs_RadiusSearchData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RadiusSearchData
open RegionQueryData
open scoped NNRat

def atRadius {n : ℕ} (q : Query n) (r : ℚ≥0) : Query n := {q with radius := r}
def predicate {n : ℕ} (q : Query n) (radii : List ℚ≥0) (i : ℕ) : Bool := accepted (atRadius q (radii.getD i 0))







end Lax455465Proofs.RadiusSearchData

end

-- Solutions.RAM_Lax455465Proofs_RamRadiusSearch
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 4096
namespace Lax455465Proofs.RamRadiusSearch
open RadiusSearchData RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def queryCost (n H : ℕ) : ℕ := (288*H+880)*(n*n)+(144*H+584)*n+144*H+554




structure Context {n : ℕ} (q : Query n) (radii : List ℚ≥0) (σ : Env) : Prop where
  input : ∃ r : ℚ≥0, Input (atRadius q r) σ
  radiusData : Prefix (RamUnsignedBuffer.encode radii) "region.radii" σ
  count : σ.vars "find.count"=radii.length
  outRoom : 2*n < (σ.arrs "region.outMask").length
  inRoom : 2*n < (σ.arrs "region.inMask").length
  crossingRoom : 2*(n*n) < (σ.arrs "region.crossing").length



def Answer {n : ℕ} (q : Query n) (σ : Env) : Prop :=
  Masks q σ ∧ Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) σ ∧
    Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) σ ∧
    Stored "region.boundary" (boundary q) σ ∧ Stored "region.volume" (volume q) σ ∧
    Stored "query.bound" (bound q) σ ∧ σ.vars "find.ok" = if accepted q then 1 else 0













end Lax455465Proofs.RamRadiusSearch

end

-- Solutions.RAM_Lax455465Proofs_RamSelectedRegion
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 4096
namespace Lax455465Proofs.RamSelectedRegion
open RadiusSearchData RamRadiusSearch RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open scoped NNRat





def Selected {n : ℕ} (q : Query n) (radii : List ℚ≥0) (σ : Env) : Prop :=
  match RamFind.first (predicate q radii) radii.length with
  | none => True
  | some i => Answer (atRadius q (radii.getD i 0)) σ



end Lax455465Proofs.RamSelectedRegion

end

-- Solutions.RAM_Lax455465Proofs_RamRegionSetup
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 4096
namespace Lax455465Proofs.RamRegionSetup
open RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def query {n : ℕ} (weights : Fin n → ℚ≥0) (capacity length : MetricMatrix.Matrix n)
    (root : Fin n) (seed beta : ℚ≥0) : Query n :=
  ⟨weights,capacity,length,length root,(fun v => length v root),seed,beta,0⟩

structure Input {n : ℕ} (weights : Fin n → ℚ≥0) (capacity length : MetricMatrix.Matrix n)
    (root : Fin n) (seed beta delta : ℚ≥0) (k : ℕ) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  rootValue : σ.vars "region.root"=root.val
  stepsValue : σ.vars "round.steps"=k
  seedData : Stored "round.seed" seed σ
  betaData : Stored "round.slope" beta σ
  deltaData : Stored "round.delta" delta σ
  unitData : Stored "round.gridStep" (delta/(k : ℚ≥0)) σ
  weightsData : Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "region.weights" σ
  capacityData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values capacity)) "region.capacities" σ
  lengthData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values length)) "metric.old" σ

structure Room (n count : ℕ) (σ : Env) : Prop where
  outRoom : 2*n<(σ.arrs "region.out").length
  inRoom : 2*n<(σ.arrs "region.in").length
  radiusRoom : 2*count<(σ.arrs "region.radii").length
  outMaskRoom : 2*n<(σ.arrs "region.outMask").length
  inMaskRoom : 2*n<(σ.arrs "region.inMask").length
  crossingRoom : 2*(n*n)<(σ.arrs "region.crossing").length











def cost (n k M H : ℕ) : ℕ :=
  (36*(M^2).size+RamRadiusSearch.queryCost n H+160)*(k+1+2*n)+84*n+RamRadiusSearch.queryCost n H+80



end Lax455465Proofs.RamRegionSetup

end

-- Solutions.RAM_Lax455465Proofs_ResidualData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.ResidualData

open Lax455465.RationalEncoding MetricMatrix LpInputSize
open scoped NNRat

def mask {n : ℕ} (active : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∈ active)

def weights {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) : Fin n → ℚ≥0 :=
  fun v => if v ∈ active then I.weight v else 0

def capacity {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) : Matrix n :=
  fun u v => if u ∈ active ∧ v ∈ active then I.capacity u v else 0













end Lax455465Proofs.ResidualData

end

-- Solutions.RAM_Lax455465Proofs_RamRegionRecord
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionRecord
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat

structure Entry (n : ℕ) where
  root : Fin n
  radius : ℚ≥0
  outward : Bool

def Entry.region {n : ℕ} (e : Entry n) : RegionLoop.Region n := ⟨e.root,e.radius,e.outward⟩
def Entry.words {n : ℕ} (e : Entry n) : List ℕ := [e.root.val,e.radius.num,e.radius.den,if e.outward then 1 else 0]
def words {n : ℕ} (history : List (Entry n)) : List ℕ := history.flatMap Entry.words








end Lax455465Proofs.RamRegionRecord

end

-- Solutions.RAM_Lax455465Proofs_RamSmallRegion
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamSmallRegion
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionRecord RamRegionContext
open scoped NNRat





structure Input {n : ℕ} (q : RegionQueryData.Query n) (active : Finset (Fin n))
    (history : List (Entry n)) (root : Fin n) (σ : Env) : Prop where
  masks : Masks q σ
  rootValue : σ.vars "region.root"=root.val
  activeData : Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ
  historyData : Prefix (words history) "region.history" σ
  historyPosition : σ.vars "history.pos"=4*history.length



def selected {n : ℕ} (q : RegionQueryData.Query n) (root : Fin n) : Entry n :=
  ⟨root,q.radius,RegionQueryData.direction q q.radius⟩




end Lax455465Proofs.RamSmallRegion

end

-- Solutions.RAM_Lax455465Proofs_RamRegionBranch
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionBranch
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open RegionQueryData RamRegionRecord
open scoped NNRat

def large {n : ℕ} (q : Query n) (threshold : ℚ≥0) : Prop :=
  (threshold : ℚ)≤ BallMassData.mass q.weights q.outDistance q.radius ∧
    (threshold : ℚ)≤ BallMassData.mass q.weights q.inDistance q.radius
instance {n : ℕ} (q : Query n) (threshold : ℚ≥0) : Decidable (large q threshold) := inferInstanceAs (Decidable (_∧_))







def Output {n : ℕ} (q : Query n) (threshold : ℚ≥0) (active : Finset (Fin n))
    (history : List (Entry n)) (root : Fin n) (σ : Env) : Prop :=
  if large q threshold then
    σ.vars "region.phase"=1 ∧ RamSmallRegion.Input q active history root σ
  else
    σ.vars "region.phase"=0 ∧ σ.vars "metric.n"=n ∧
      Prefix (words (history++[RamSmallRegion.selected q root])) "region.history" σ ∧
      σ.vars "history.pos"=4*(history.length+1) ∧
      Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask
        (active \ (RamSmallRegion.selected q root).region.ball (MetricMatrix.rational q.length))))) "region.active" σ



end Lax455465Proofs.RamRegionBranch

end

-- Solutions.RAM_Lax455465Proofs_RamRegionInvariant
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionInvariant
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding RamRegionRecord
open scoped NNRat

structure Fixed {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  supportValue : σ.vars "round.support"=p
  stepsValue : σ.vars "round.steps"=RegionBudget.steps p
  seedData : Stored "round.seed" seed σ
  betaData : Stored "round.slope" beta σ
  deltaData : Stored "round.delta" delta σ
  unitData : Stored "round.gridStep" (delta/(RegionBudget.steps p : ℚ≥0)) σ
  thresholdData : Stored "round.largeThreshold" threshold σ
  weightsData : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacityData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  lengthData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values length)) "metric.old" σ






structure Dynamic {n : ℕ} (active : Finset (Fin n)) (history : List (Entry n)) (σ : Env) : Prop where
  phase : σ.vars "region.phase"=0
  activeData : Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ
  historyData : Prefix (words history) "region.history" σ
  historyPosition : σ.vars "history.pos"=4*history.length












end Lax455465Proofs.RamRegionInvariant

end

-- Solutions.RAM_Lax455465Proofs_RamRegionPrelude
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionPrelude
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionInvariant RamRegionRecord
open Lax455465.RationalEncoding
open scoped NNRat



def cost (n M : ℕ) : ℕ := (36*(M^2).size+208)*(n*n)+(36*(M^2).size+166)*n+40



end Lax455465Proofs.RamRegionPrelude

end

-- Solutions.RAM_Lax455465Proofs_RegionExecutionData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators NNRat
namespace Lax455465Proofs.RegionExecutionData
open Lax455465.RationalEncoding RegionQueryData

def query {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (active : Finset (Fin n)) (root : Fin n) (seed beta : ℚ≥0) : Query n :=
  RamRegionSetup.query (ResidualData.weights I active) (ResidualData.capacity I active) length root seed beta







end Lax455465Proofs.RegionExecutionData

end

-- Solutions.RAM_Lax455465Proofs_RamRegionCore
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionCore
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open RamRegionInvariant RamRegionRecord Lax455465.RationalEncoding
open scoped NNRat

def Output {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (active : Finset (Fin n)) (history : List (Entry n)) (σ : Env) : Prop :=
  match RegionSelection.chooseRoot (RegionLoop.weights I active) with
  | none => σ.vars "region.phase"=2 ∧
      Prefix (words history) "region.history" σ ∧ σ.vars "history.pos"=4*history.length ∧
      Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ
  | some root => ∃ rn : ℚ≥0,
      RegionSearch.search (RegionLoop.capacity I active) (MetricMatrix.rational length)
        (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
        (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root)=some (rn : ℚ) ∧
      RamRegionBranch.Output (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta) rn)
        threshold active history root σ

def cost (n p M H : ℕ) : ℕ := RamRegionPrelude.cost n M+
  RamRegionSetup.cost n (RegionBudget.steps p) M H+96*n+200



end Lax455465Proofs.RamRegionCore

end

-- Solutions.RAM_Lax455465Proofs_RegionRuntimeState
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option backward.isDefEq.respectTransparency false
namespace Lax455465Proofs.RegionRuntimeState
open Lax455465.RationalEncoding RegionQueryData RamRegionRecord
open scoped NNRat

inductive Status (n : ℕ) where
  | running
  | large : Entry n → Status n
  | exhausted
  | failed

structure State (n : ℕ) where
  active : Finset (Fin n)
  history : List (Entry n)
  status : Status n

def radius {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p : ℕ) (active : Finset (Fin n)) (root : Fin n) : Option ℚ≥0 :=
  (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).find?
    (fun r => accepted (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta) r))





/-- The deterministic runtime state transition, with exactly the native
candidate order and two-thirds branch. Frozen states remain unchanged. -/
def advance {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (s : State n) : State n :=
  match s.status with
  | .running =>
    match RegionSelection.chooseRoot (RegionLoop.weights I s.active) with
    | none => {s with status := .exhausted}
    | some root =>
      match radius I length seed beta delta p s.active root with
      | none => {s with status := .failed}
      | some r =>
        let q := RadiusSearchData.atRadius (RegionExecutionData.query I length s.active root seed beta) r
        let e := RamSmallRegion.selected q root
        if RamRegionBranch.large q threshold then {s with status := .large e}
        else {active := s.active \ e.region.ball (MetricMatrix.rational length),history := s.history++[e],status := .running}
  | _ => s

end Lax455465Proofs.RegionRuntimeState

end

-- Solutions.RAM_Lax455465Proofs_RamRegionState
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option backward.isDefEq.respectTransparency false
namespace Lax455465Proofs.RamRegionState
open Lax808846Proofs.Imp RamVirtualState RamRegionInvariant RamRegionRecord RegionRuntimeState
open Lax455465.RationalEncoding
open scoped NNRat

def View {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n) (seed beta : ℚ≥0)
    (s : State n) (σ : Env) : Prop :=
  match s.status with
  | .running => Dynamic s.active s.history σ
  | .large e => σ.vars "region.phase"=1 ∧
      RamSmallRegion.Input (RadiusSearchData.atRadius (RegionExecutionData.query I length s.active e.root seed beta) e.radius)
        s.active s.history e.root σ
  | .exhausted => σ.vars "region.phase"=2 ∧ Prefix (words s.history) "region.history" σ ∧
      σ.vars "history.pos"=4*s.history.length ∧
      Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask s.active))) "region.active" σ
  | .failed => False



end Lax455465Proofs.RamRegionState

end

-- Solutions.RAM_Lax455465Proofs_RamRegionScan
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionScan
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionInvariant
open RegionRuntimeState RamRegionState Lax455465.RationalEncoding
open scoped NNRat



def command : Com := .seq (.assign "loop.i" (.lit 0))
  (.while (.lt (.var "loop.i") (.var "loop.limit")) RamRegionLoop.step)



end Lax455465Proofs.RamRegionScan

end

-- Solutions.RAM_Lax455465Proofs_RamRegionBoundedLoop
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionBoundedLoop
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionInvariant RegionRuntimeState RamRegionState
open Lax455465.RationalEncoding
open scoped NNRat

def initial (n : ℕ) : State n := ⟨Finset.univ,[],.running⟩
def cost (n p M H : ℕ) : ℕ := (RamRegionCore.cost n p M H+13)*(p+1)+6



end Lax455465Proofs.RamRegionBoundedLoop

end

-- Solutions.RAM_Lax455465Proofs_RamRoundingInit
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRoundingInit
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext RamVirtualState
open scoped NNRat

def total {n : ℕ} (weights : Fin n → ℚ≥0) : ℚ≥0 := (List.ofFn weights).sum








end Lax455465Proofs.RamRoundingInit

end

-- Solutions.RAM_Lax455465Proofs_RegionRuntimeCorrespondence
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNRat
namespace Lax455465Proofs.RegionRuntimeCorrespondence
open Lax455465.RationalEncoding RegionRuntimeState RamRegionRecord RegionLoop













def ValidFinal {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed delta : ℚ≥0) (p : ℕ) (s : State n) : Prop :=
  match s.status with
  | .large e => LargeGood I (MetricMatrix.rational length) delta e.region
  | .exhausted => ValidHistory I (MetricMatrix.rational length) seed delta p Finset.univ
      (s.history.map Entry.region) ∧ s.history.length≤ p
  | _ => False



end Lax455465Proofs.RegionRuntimeCorrespondence

end

-- Solutions.RAM_Lax455465Proofs_CutScoreData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.CutScoreData
open Lax455465.RationalEncoding MetricMatrix
open scoped BigOperators NNRat

def vertexFlags {n : ℕ} (S : Finset (Fin n)) : List ℚ≥0 := MaskedMassData.flags (ResidualData.mask S)
def arcFlags {n : ℕ} (S : Finset (Fin n)) : Matrix n := RamArcMask.matrix (some true) (ResidualData.mask S)
def mass {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ≥0 :=
  (RamMaskedSum.coefficients (List.ofFn I.weight) (vertexFlags S)).sum
def capacity {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ≥0 :=
  (RamMaskedSum.coefficients (values I.capacity) (values (arcFlags S))).sum
def otherMass {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ≥0 := RamRoundingInit.total I.weight-mass I S
def demand {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ≥0 := mass I S*otherMass I S
def ratio {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ≥0 := capacity I S/demand I S

















end Lax455465Proofs.CutScoreData

end

-- Solutions.RAM_Lax455465Proofs_SetDistanceData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.SetDistanceData
open scoped NNRat







def distance {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n) (S : Finset (Fin n))
    (hS : S.Nonempty) (v : Fin n) : ℚ≥0 := S.inf' hS fun u => if toSet then d v u else d u v







end Lax455465Proofs.SetDistanceData

end

-- Solutions.RAM_Lax455465Proofs_LargePotentialData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.LargePotentialData
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat

def vector {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n) (S : Finset (Fin n)) (hS : S.Nonempty) : List ℚ≥0 :=
  List.ofFn (SetDistanceData.distance toSet d S hS)
def products {n : ℕ} (I : RationalInstance n) (toSet : Bool) (d : MetricMatrix.Matrix n)
    (S : Finset (Fin n)) (hS : S.Nonempty) : List ℚ≥0 := RamProductSum.products (List.ofFn I.weight) (vector toSet d S hS)











structure Bounds {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) (M : ℕ) : Prop where
  weights : ∀ v,Height M (I.weight v : ℚ)
  distances : ∀ u v,Height M (d u v : ℚ)
  fromProducts : ∀ q∈products I false d Tout hout,Height M (q : ℚ)
  toProducts : ∀ q∈products I true d Tin hin,Height M (q : ℚ)
  fromPrefix : ∀ i,Height M ((((products I false d Tout hout).take i).sum : ℚ≥0) : ℚ)
  toPrefix : ∀ i,Height M ((((products I true d Tin hin).take i).sum : ℚ≥0) : ℚ)



end Lax455465Proofs.LargePotentialData

end

-- Solutions.RAM_Lax455465Proofs_RamSetDistances
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamSetDistances
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionContext
open scoped NNRat







def cost (n : ℕ) : ℕ := (168*n+46)*n+8





end Lax455465Proofs.RamSetDistances

end

-- Solutions.RAM_Lax455465Proofs_RamSetPotential
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamSetPotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionContext
open scoped NNRat










def cost (n : ℕ) : ℕ := RamSetDistances.cost n+48*n+18





end Lax455465Proofs.RamSetPotential

end

-- Solutions.RAM_Lax455465Proofs_RamPotentialAverage
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamPotentialAverage
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped NNRat



def cost (n M : ℕ) : ℕ := (72*(M^2).size+224)*n+22



end Lax455465Proofs.RamPotentialAverage

end

-- Solutions.RAM_Lax455465Proofs_RamLargePotential
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamLargePotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped NNRat














def cost (n M : ℕ) : ℕ := 2*RamSetPotential.cost n+2*RamPotentialAverage.cost n M+24*n+80



end Lax455465Proofs.RamLargePotential

end

-- Solutions.RAM_Lax455465Proofs_CutScoreHeight
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.CutScoreHeight
open Lax455465.RationalEncoding LpInputSize CutScoreData
open scoped NNRat




structure Bounds {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) (M : ℕ) : Prop where
  weightsBound : ∀ v, Height M (I.weight v : ℚ)
  capacityBound : ∀ u v, Height M (I.capacity u v : ℚ)
  massPrefix : ∀ i, Height M ((((RamMaskedSum.coefficients (List.ofFn I.weight) (vertexFlags S)).take i).sum : ℚ≥0) : ℚ)
  capacityPrefix : ∀ i, Height M ((((RamMaskedSum.coefficients (MetricMatrix.values I.capacity) (MetricMatrix.values (arcFlags S))).take i).sum : ℚ≥0) : ℚ)
  totalBound : Height M (RamRoundingInit.total I.weight : ℚ)
  massBound : Height M (mass I S : ℚ)
  otherBound : Height M (otherMass I S : ℚ)
  demandBound : Height M (demand I S : ℚ)
  inverseBound : Height M (((demand I S)⁻¹ : ℚ≥0) : ℚ)
  cutCapacityBound : Height M (capacity I S : ℚ)
  ratioBound : Height M (ratio I S : ℚ)



end Lax455465Proofs.CutScoreHeight

end

-- Solutions.RAM_Lax455465Proofs_RamCutScore
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamCutScore
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding CutScoreData
open scoped NNRat



def cost (n M : ℕ) : ℕ := (36*(M^2).size+234)*(n*n)+(36*(M^2).size+152)*n+144*(M^2).size+468



end Lax455465Proofs.RamCutScore

end

-- Solutions.RAM_Lax455465Proofs_RamThresholdCandidate
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 4096
namespace Lax455465Proofs.RamThresholdCandidate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding
open scoped NNRat










def cost (n M : ℕ) : ℕ := RamCutScore.cost n M+110*n+30



end Lax455465Proofs.RamThresholdCandidate

end

-- Solutions.RAM_Lax455465Proofs_RamPotentialSweep
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamPotentialSweep
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding RamThresholdCandidate
open scoped NNRat




def cost (n M : ℕ) : ℕ := (RamThresholdCandidate.cost n M+92)*n+RamThresholdCandidate.cost n M+16









end Lax455465Proofs.RamPotentialSweep

end

-- Solutions.RAM_Lax455465Proofs_RamLargeCut
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamLargeCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped BigOperators NNRat




def cost (n M : ℕ) : ℕ := RamLargePotential.cost n M+RamPotentialSweep.cost n M+2





end Lax455465Proofs.RamLargeCut

end

-- Solutions.RAM_Lax455465Proofs_RamHistoryPotential
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryPotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding
open scoped NNRat







def cost (n m : ℕ) : ℕ := (140*m+74)*n+16





end Lax455465Proofs.RamHistoryPotential

end

-- Solutions.RAM_Lax455465Proofs_RamHistoryCut
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext RamRegionRecord
open Lax455465.RationalEncoding
open scoped BigOperators NNRat




def cost (n m M : ℕ) : ℕ := RamHistoryPotential.cost n m+RamPotentialSweep.cost n M





end Lax455465Proofs.RamHistoryCut

end

-- Solutions.RAM_Lax455465Proofs_RamRegionCut
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding RegionRuntimeState
open scoped BigOperators NNRat






def cost (n p M : ℕ) : ℕ := RamLargeCut.cost n M+RamHistoryCut.cost n p M+4

def Output {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (p : ℕ) (σ : Env) : Prop :=
  ∃ S : Finset (Fin n),CutSweeps.admissibleQ I S ∧
    CutSweeps.ratioQ I S ≤ (288/5 : ℚ)*(RegionBudget.steps p : ℚ)*RegionRounding.metricCost I (MetricMatrix.rational d) ∧
    Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ



end Lax455465Proofs.RamRegionCut

end

-- Solutions.RAM_Lax455465Proofs_UndirectedConversion
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option backward.isDefEq.respectTransparency false

open scoped BigOperators NNReal NNRat

namespace Lax455465Proofs.UndirectedConversion

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

/-- Convert a directed flow in a symmetric capacity matrix to shared-capacity
undirected flow. The common demand fraction is retained. -/
def halve {n : ℕ} (F : ArcCertificate n) : ArcCertificate n where
  value := F.value
  arcs s t u v := F.arcs s t u v / 2









end Lax455465Proofs.UndirectedConversion

end

-- Solutions.RAM_Lax455465Proofs_CertificatePostprocessing
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators NNReal NNRat

namespace Lax455465Proofs.CertificatePostprocessing

open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.FlowCutCertificate Lax109476.LinearProgram DirectedFlowLP

/-- Extract the primal coordinates without requiring proof data at runtime. -/
def primalFlow {n : ℕ} (z : Fin (1 + (n * n) * (n * n)) → ℚ) : ArcCertificate n where
  value := (z (variableIndex n (.inl 0))).toNNRat
  arcs s t u v := (z (variableIndex n (.inr ((s, t), (u, v))))).toNNRat

def convertFlow {n : ℕ} (kind : EdgeKind) (F : ArcCertificate n) : ArcCertificate n :=
  match kind with
  | .directed => F
  | .undirected => UndirectedConversion.halve F





end Lax455465Proofs.CertificatePostprocessing

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentFamily
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

/-! Native entry readers for the six fixed moment-matrix row families. -/

namespace Lax263307Proofs.NativeMomentFamily

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 MomentLP






































def Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) (σ : Env) : Prop :=
  NativeMomentAccess.Data G r σ ∧ σ.vars "row.k"=k






open NativeCatalogMetadata NativeMomentProduce

























end Lax263307Proofs.NativeMomentFamily

end

-- Solutions.RAM_Lax263307Proofs_NativeNodeAliases
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodeAliases

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters



def Output (a K b n D k : ℕ) (σ : Env) : Prop :=
  σ.vars "row.k"=k ∧ σ.vars "conditioning.k"=k ∧ σ.vars "conditioning.p"=sparsity a K b n D ∧
    σ.vars "algorithm.load"=load b n D ∧ σ.vars "algorithm.D"=D ∧ σ.vars "class.B"=b



end Lax263307Proofs.NativeNodeAliases

end

-- Solutions.RAM_Lax263307Proofs_NativeNodePrecision
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodePrecision

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters






def Context (n D N b r : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "node.D"=D ∧ σ.vars "catalog.count"=N ∧
    σ.vars "node.floorDen"=b ∧ σ.vars "moment.r"=r

def Output (n D N b r : ℕ) (σ : Env) : Prop := Context n D N b r σ ∧
  σ.vars "node.floorPower"=b^r ∧ σ.vars "node.radius"=radius n D N b r ∧
  σ.vars "node.precision"=prec n D N b r ∧ σ.vars "round.limit"=count n D N b r ∧
  σ.vars "vec.n"=N

























end Lax263307Proofs.NativeNodePrecision

end

-- Solutions.RAM_Lax263307Proofs_NativeArrayBounds
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeArrayBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Bounded (B : ℕ) (σ : Env) : Prop := ∀ a,∀ z ∈ σ.arrs a,z < B







end Lax263307Proofs.NativeArrayBounds

end

-- Solutions.RAM_Lax263307Proofs_NativeLargeNode
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeLargeNode

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 AlgorithmParameters MomentLP RoundedOracleSearch







/-- The large-node setup program computes every parameter and builds
every initial LP/state buffer from the encoded graph and runtime target.
Only class constants occur as source-program parameters. -/
def Input {n : ℕ} (B a K b D k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (σ : Env) : Prop :=
  let r := level a K b n D
  let N := dimension n r
  σ.vars "graph.n"=n ∧ σ.vars "node.D"=D ∧ σ.vars "node.k"=k ∧
      Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧ NativeArrayBounds.Bounded B σ ∧
      (n+1)*(r+3)≤(σ.arrs "choose.table").length ∧ n≤(σ.arrs "subset.bits").length ∧
      N≤(σ.arrs "catalog.mask").length ∧ N≤(σ.arrs "catalog.card").length ∧ N≤(σ.arrs "catalog.independent").length ∧
      NativeMomentInput.length n r≤(σ.arrs "lp.input").length ∧
      NativeMomentInput.length n r≤(σ.arrs "moment.program").length ∧
      3*(N*N)+3*N≤(σ.arrs "lp.input").length ∧ 3*(N*N)≤(σ.arrs "round.shape").length ∧
      3*N≤(σ.arrs "round.center").length

def Output {n : ℕ} (a K b D k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (τ : Env) : Prop :=
  let r := level a K b n D
  let N := dimension n r
  NativeNodeAliases.Output a K b n D k τ ∧ NativeMomentFamily.Data G k r τ ∧
        Prefix (encodeProgram (MomentLP.program G k r)) "moment.program" τ ∧
        τ.vars "node.programLength"=NativeMomentInput.length n r ∧
        NativeNodePrecision.Output n D N (floorDenominator a K b n D) r τ ∧
        Prefix (NativeRoundedQuery.shape ((1,0) : State N)) "round.shape" τ ∧
        Prefix (NativeRoundedQuery.center ((1,0) : State N)) "round.center" τ ∧ τ.vars "round.i"=0



end Lax263307Proofs.NativeLargeNode

end

-- Solutions.RAM_Lax263307Proofs_NativeCollectionTrace
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCollectionTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 ComputedRounding NativeCoreMachine NativeMachineSegment NativeMasks

/-- The collection invariant at the top of phase 9. -/
def At {n : ℕ} (Q : Env → Prop) (i : ℕ) (S : Finset (Fin n)) (σ : Env) : Prop :=
  Q σ ∧ σ.vars "component.i"=i ∧ σ.vars "component.union"=mask S ∧
    σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=9

def ResultOutput {n : ℕ} (Q : Env → Prop) (cut : Finset (Fin n) → ℕ → Env → Prop)
    (result : Result n) (σ : Env) : Prop := Q σ ∧ match result with
  | .found I => NativeRoundTrace.Stopped (some I) σ
  | .cut C u => σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=13 ∧ cut C u σ

/-- One actual part iteration. Light parts return the empty set; a heavy
part includes its complete child call, recursive execution and restored
reply. The caller obtains this premise from the concrete component/child
phase lemmas and the induction hypothesis on recursion fuel. -/
def Iterations {n : ℕ} {ι : Type} (B : ℕ) (cfg : Config) (Q : Env → Prop)
    (cut : Finset (Fin n) → ℕ → Env → Prop) (parts : ι → Finset (Fin n)) (bound : ι → ℕ)
    (reply : ι → Option (Finset (Fin n))) (order : List ι) (S K : ℕ) : Prop :=
  ∀ (pre : List ι) (i : ι) (suffix : List ι),pre++i::suffix=order →
    ∀ U σ,At Q pre.length U σ →
    ∃ τ transitions total,Segment B (phases cfg) transitions total σ τ ∧
      transitions≤ S ∧ total≤ K ∧
      match reply i with
      | none => ResultOutput Q cut (.cut (parts i) (bound i)) τ
      | some I => At Q (pre.length+1) (U∪I) τ





end Lax263307Proofs.NativeCollectionTrace

end

-- Solutions.RAM_Lax263307Proofs_NativeCollectionExecution
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCollectionExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedRounding NativeCoreMachine NativeMachineSegment NativeMasks NativeCollectionContext



/-- Exact normal stored on the first failed component. -/
def Cut {n : ℕ} (r : ℕ) (A C : Finset (Fin n)) (u : ℕ) (σ : Env) : Prop :=
  Prefix (NativeRoundedQuery.normal (RationalCutBuffer.integerNormal
    (RoundedOracleSearch.rationalNormal (NativeComponentNormal.normal (r:=r) A C u)))) "round.normal" σ









end Lax263307Proofs.NativeCollectionExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeNearExecution
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNearExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning ComputedSeparators
open NativeCoreMachine NativeMachineSegment NativeOracleContext





def Output {n : ℕ} (r : ℕ) : NearOracle.Result n → Env → Prop
  | .reject,σ => NativeRoundTrace.Stopped (none : Option (Finset (Fin n))) σ
  | .found I,σ => NativeRoundTrace.Stopped (some I) σ
  | .cut A C u,σ => σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=13 ∧
      NativeCollectionExecution.Cut r A C u σ















end Lax263307Proofs.NativeNearExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeRootWorkspace
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeRootWorkspace

open Lax263307 AlgorithmParameters NativeCoreMachine NativeSelectedRounds



def capacity (cfg : Config) (rootN W : ℕ) : ℕ := RecursionDepth.depth rootN*frameLength cfg W

def extent (cfg : Config) (rootN W originalN : ℕ) (a : String) : ℕ :=
  if a="recursion.frames" then capacity cfg rootN W
  else if a="image.output" then originalN
  else if a="weighted.output" then originalN else stride W













end Lax263307Proofs.NativeRootWorkspace

end

-- Solutions.RAM_Lax263307Proofs_NativeQptasPositive
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeQptasPositive

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses BlowUpClasses WeightedIndependentSet
open NativeQptasImplementation NativeRootWorkspace















structure Bounds {C : GraphClass} (i : Fixed C) (n N M w : ℕ) (ε : ℚ) : Prop where
  allocation : n*n+N*N+3*n+N+3 ≤ workspace i N ε
  frontend : 2*M^4+3<2^w
  input : n*n+3*n+3<2^w
  graph : n*n+N*N+n+N+3<2^w
  copy : N*N+N+5<2^w
  accuracy : 3*M+8*(RecursionDepth.depth N+1)*M+2*N+RecursionDepth.depth N+40<2^w
  budget : NativeRootBudget.guard i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent
    N (denominator N ε)<2^w
  host : hostHeight i.cfg (workspace i N ε) ≤ w
  output : n+N+5<2^w



end Lax263307Proofs.NativeQptasPositive

end


