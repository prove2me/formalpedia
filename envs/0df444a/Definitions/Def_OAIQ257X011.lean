-- Prove2me | Definitions.Def_OAIQ257X011
-- name    : OAIQ257X011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:57:01.4473+00:00
-- url     : https://prove2.me/theorems/5e2d62aa-aad5-4e3c-a898-ceb4e7956625
-- title:
--   Definitions bundle OAIQ257X011 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 762 declarations of OpenAI's Lean: 762 definitions. The definitions and types are `OAI.AtomicTriangular.Bernstein.bernsteinBasis`, `OAI.AtomicTriangular.Bernstein.bernsteinCoefficient`, `OAI.AtomicTriangular.Construction.DeltaStar`, `OAI.AtomicTriangular.Construction.ParameterPolytope`, `OAI.AtomicTriangular.Construction.Pstar`, `OAI.AtomicTriangular.Construction.Ustar`, `OAI.AtomicTriangular.Construction.Wstar`, `OAI.AtomicTriangular.Construction.actualJ0`, `OAI.AtomicTriangular.Construction.bernsteinRows`, `OAI.AtomicTriangular.Construction.cellBarrier`, `OAI.AtomicTriangular.Construction.cellFactor`, `OAI.AtomicTriangular.Construction.cellHi`, `OAI.AtomicTriangular.Construction.cellLo`, `OAI.AtomicTriangular.Construction.cellMagnitude`, `OAI.AtomicTriangular.Construction.cellSeparation`, `OAI.AtomicTriangular.Construction.complexDeleted`, `OAI.AtomicTriangular.Construction.complexError`, `OAI.AtomicTriangular.Construction.complexTaylor`, `OAI.AtomicTriangular.Construction.curvaturePoint`, `OAI.AtomicTriangular.Construction.curvatureWave`, `OAI.AtomicTriangular.Construction.deletedSecond`, `OAI.AtomicTriangular.Construction.exceptionalOffset`, `OAI.AtomicTriangular.Construction.exceptionalRow`, `OAI.AtomicTriangular.Construction.exceptionalValue`, `OAI.AtomicTriangular.Construction.exceptionalWeight`, `OAI.AtomicTriangular.Construction.farK`, `OAI.AtomicTriangular.Construction.finiteCurvatureCap`, `OAI.AtomicTriangular.Construction.finiteCurvatureEnvelope`, `OAI.AtomicTriangular.Construction.finiteErrorBound`, `OAI.AtomicTriangular.Construction.finiteJ`, `OAI.AtomicTriangular.Construction.finiteJJet`, `OAI.AtomicTriangular.Construction.finiteResidualBound`, `OAI.AtomicTriangular.Construction.finiteSpectrum`, `OAI.AtomicTriangular.Construction.finiteTargetEnvelope`, `OAI.AtomicTriangular.Construction.finiteTaylor`, `OAI.AtomicTriangular.Construction.freezeParameter`, `OAI.AtomicTriangular.Construction.frozenTaylor`, `OAI.AtomicTriangular.Construction.frozenTaylorRow`, `OAI.AtomicTriangular.Construction.localBoundary`, `OAI.AtomicTriangular.Construction.localCenter` and 722 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Auxiliary_Bernstein`, `Triangular_Certificate_Inverse`, `Triangular_Certificate_JetMatrix`, `Triangular_Certificate_Param`, `Triangular_Certificate_ParamA`, `Triangular_Certificate_ParamInterval`, `Triangular_Certificate_ParamNorm`, `Triangular_Certificate_ParamRHS`, `Triangular_Certificate_ParamU`, `Triangular_Certificate_Polytope`, `Triangular_Certificate_PolytopeInterval`, `Triangular_Certificate_TargetInterval`, `Triangular_Construction_ConcreteSchur`, `Triangular_Construction_CurvatureBoxes`, `Triangular_Construction_CurvatureEnvelope`, `Triangular_Construction_FarCurvature`, `Triangular_Construction_FiniteRemainder`, `Triangular_Envelope_EnvelopeSums`, `Triangular_Envelope_EnvelopeSumsBase`, `Triangular_Envelope_TargetEnvelope`, `Triangular_Signs_DeletedAccuracy`, `Triangular_Signs_DeletedExponential`, `Triangular_Signs_DeletedJets`, `Triangular_Signs_DeletedQuotient`, `Triangular_Signs_Exceptional`, `Triangular_Signs_FarSigns`, `Triangular_Signs_GaussianDeleted`, `Triangular_Signs_RemainderBoxes`, `Triangular_Signs_SignBase`, `Triangular_Signs_Signs00`, `Triangular_Signs_Signs01`, `Triangular_Signs_Signs02`, `Triangular_Signs_Signs03`, `Triangular_Signs_Signs04`, `Triangular_Signs_Signs05`, `Triangular_Signs_Signs06`, `Triangular_Signs_Signs10`, `Triangular_Signs_Signs11`, `Triangular_Signs_Signs12`, `Triangular_Signs_Signs13`, `Triangular_Signs_Signs14`, `Triangular_Signs_Signs15`, `Triangular_Signs_SineBarrierBase`, `Triangular_Signs_SineGridAnalytic`, `Triangular_Signs_SineGridCover`, `Triangular_Signs_SineGridDefs`, `Triangular_Taylor_FiniteTaylorIdentity`, `Triangular_Taylor_Taylor`, `Triangular_Taylor_TaylorPhase`, `Triangular_Taylor_TaylorRowsBase`, `Triangular_Taylor_TaylorSpectrum`.
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ257X005` and `OAIQ257X010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ257X021`, `OAIQ257X022` and `OAIQ257X024`; the statements `OAI.AtomicTriangular.Construction.actualJ0_deleted_x`, `OAI.AtomicTriangular.Construction.cellFactors00_x`, `OAI.AtomicTriangular.Construction.cellFactors01_x`, `OAI.AtomicTriangular.Construction.cellFactors02_x`, `OAI.AtomicTriangular.Construction.cellFactors03_x`, `OAI.AtomicTriangular.Construction.cellFactors04_x`, `OAI.AtomicTriangular.Construction.cellFactors05_x`, `OAI.AtomicTriangular.Construction.cellFactors06_x`, `OAI.AtomicTriangular.Construction.cellFactors07_x`, `OAI.AtomicTriangular.Construction.cellFactors08_x`, `OAI.AtomicTriangular.Construction.cellFactors09_x`, `OAI.AtomicTriangular.Construction.cellFactors10_x`, `OAI.AtomicTriangular.Construction.cellFactors11_x`, `OAI.AtomicTriangular.Construction.cellFactors12_x`, `OAI.AtomicTriangular.Construction.cellFactors13_x`, `OAI.AtomicTriangular.Construction.cellFactors14_x`, `OAI.AtomicTriangular.Construction.cellFactors15_x`, `OAI.AtomicTriangular.Construction.cellFactors16_x`, `OAI.AtomicTriangular.Construction.cellFactors17_x`, `OAI.AtomicTriangular.Construction.cellFactors18_x`, `OAI.AtomicTriangular.Construction.cellFactors19_x`, `OAI.AtomicTriangular.Construction.cellFactors20_x`, `OAI.AtomicTriangular.Construction.cellFactors21_x`, `OAI.AtomicTriangular.Construction.cellFactors22_x`, `OAI.AtomicTriangular.Construction.cellFactors23_x`, `OAI.AtomicTriangular.Construction.cellFactors24_x`, `OAI.AtomicTriangular.Construction.cellFactors25_x`, `OAI.AtomicTriangular.Construction.cellFactors26_x`, `OAI.AtomicTriangular.Construction.cellFactors27_x`, `OAI.AtomicTriangular.Construction.cellFactors28_x`, `OAI.AtomicTriangular.Construction.cellFactors29_x`, `OAI.AtomicTriangular.Construction.cellGeometry00_x`, `OAI.AtomicTriangular.Construction.cellGeometry01_x`, `OAI.AtomicTriangular.Construction.cellGeometry02_x`, `OAI.AtomicTriangular.Construction.cellGeometry04_x`, `OAI.AtomicTriangular.Construction.cellGeometry05_x`, `OAI.AtomicTriangular.Construction.cellGeometry06_x`, `OAI.AtomicTriangular.Construction.cellGeometry09_x`, `OAI.AtomicTriangular.Construction.cellGeometry10_x`, `OAI.AtomicTriangular.Construction.cellGeometry11_x`, `OAI.AtomicTriangular.Construction.cellGeometry12_x`, `OAI.AtomicTriangular.Construction.cellGeometry13_x`, `OAI.AtomicTriangular.Construction.cellGeometry14_x`, `OAI.AtomicTriangular.Construction.cellGeometry15_x`, `OAI.AtomicTriangular.Construction.cellGeometry16_x`, `OAI.AtomicTriangular.Construction.cellGeometry17_x`, `OAI.AtomicTriangular.Construction.cellGeometry18_x`, `OAI.AtomicTriangular.Construction.cellGeometry19_x`, `OAI.AtomicTriangular.Construction.cellGeometry20_x`, `OAI.AtomicTriangular.Construction.cellGeometry21_x`, `OAI.AtomicTriangular.Construction.cellGeometry22_x`, `OAI.AtomicTriangular.Construction.cellGeometry23_x`, `OAI.AtomicTriangular.Construction.cellGeometry24_x`, `OAI.AtomicTriangular.Construction.cellGeometry25_x`, `OAI.AtomicTriangular.Construction.cellGeometry26_x`, `OAI.AtomicTriangular.Construction.cellGeometry27_x`, `OAI.AtomicTriangular.Construction.cellGeometry28_x`, `OAI.AtomicTriangular.Construction.cellGeometry29_x`, `OAI.AtomicTriangular.Construction.cell_factors_x`, `OAI.AtomicTriangular.Construction.cell_geometry_x`, `OAI.AtomicTriangular.Construction.correctionFinite_small_x`, `OAI.AtomicTriangular.Construction.correctionTail_small_x`, `OAI.AtomicTriangular.Construction.exceptional_rational_comparison_x`, `OAI.AtomicTriangular.Construction.finiteApprox_norm_x`, `OAI.AtomicTriangular.Construction.finiteCurvatureCap_bound_x`, `OAI.AtomicTriangular.Construction.finiteSpectral_curvature_x`, `OAI.AtomicTriangular.Construction.finiteTaylor_error_x`, `OAI.AtomicTriangular.Construction.near_negative_polynomial_x`, `OAI.AtomicTriangular.Construction.near_positive_polynomial_x`, `OAI.AtomicTriangular.Construction.pairJ_curvature_x`, `OAI.AtomicTriangular.Construction.tailCurvatureCap_sum_x`, `OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.UminusCachedBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.UminusTable_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.UplusCachedBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn0_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn0_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn0_2_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_2_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData00_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData01_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData10_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData10_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData10_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData10_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureData11_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable01_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureTable11_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_2_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_2_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_3_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_3_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_5_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_5_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_6_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_6_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_0_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_0_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_1_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_1_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_3_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_4_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_4_1_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_6_0_x`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_6_1_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns0_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns1_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns1_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns2_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns2_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns3_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns3_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns4_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns4_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns5_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns5_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns6_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns6_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst0_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_01_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_11_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_00_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_11_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_00_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData3_10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_00_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData4_11_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData5_01_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable0_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable2_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable3_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable4_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable5_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable6_x`, `OAI.AtomicTriangular.FiniteCertificate.remainder_table_x`, `OAI.AtomicTriangular.FiniteCertificate.spectrum0_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.spectrum1_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.spectrumTable_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.taylorExpTable_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_0_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_2_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_3_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_4_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_5_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_6_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_0_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_2_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_3_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_3_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_4_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_5_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_5_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_5_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_6_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_6_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_5_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_5_mem_x` and `OAI.AtomicTriangular.FiniteCertificate.tw1_1_mem_x`; the proofs of `OAI.AtomicTriangular.Construction.actualJ0_deleted_x`, `OAI.AtomicTriangular.Construction.actualSchwartz_signs_x`, `OAI.AtomicTriangular.Construction.actualTrigonometric_norm_x`, `OAI.AtomicTriangular.Construction.cellFactors00_x`, `OAI.AtomicTriangular.Construction.cellFactors01_x`, `OAI.AtomicTriangular.Construction.cellFactors02_x`, `OAI.AtomicTriangular.Construction.cellFactors03_x`, `OAI.AtomicTriangular.Construction.cellFactors04_x`, `OAI.AtomicTriangular.Construction.cellFactors05_x`, `OAI.AtomicTriangular.Construction.cellFactors06_x`, `OAI.AtomicTriangular.Construction.cellFactors07_x`, `OAI.AtomicTriangular.Construction.cellFactors08_x`, `OAI.AtomicTriangular.Construction.cellFactors09_x`, `OAI.AtomicTriangular.Construction.cellFactors10_x`, `OAI.AtomicTriangular.Construction.cellFactors11_x`, `OAI.AtomicTriangular.Construction.cellFactors12_x`, `OAI.AtomicTriangular.Construction.cellFactors13_x`, `OAI.AtomicTriangular.Construction.cellFactors14_x`, `OAI.AtomicTriangular.Construction.cellFactors15_x`, `OAI.AtomicTriangular.Construction.cellFactors16_x`, `OAI.AtomicTriangular.Construction.cellFactors17_x`, `OAI.AtomicTriangular.Construction.cellFactors18_x`, `OAI.AtomicTriangular.Construction.cellFactors19_x`, `OAI.AtomicTriangular.Construction.cellFactors20_x`, `OAI.AtomicTriangular.Construction.cellFactors21_x`, `OAI.AtomicTriangular.Construction.cellFactors22_x`, `OAI.AtomicTriangular.Construction.cellFactors23_x`, `OAI.AtomicTriangular.Construction.cellFactors24_x`, `OAI.AtomicTriangular.Construction.cellFactors25_x`, `OAI.AtomicTriangular.Construction.cellFactors26_x`, `OAI.AtomicTriangular.Construction.cellFactors27_x`, `OAI.AtomicTriangular.Construction.cellFactors28_x`, `OAI.AtomicTriangular.Construction.cellFactors29_x`, `OAI.AtomicTriangular.Construction.cellGeometry00_x`, `OAI.AtomicTriangular.Construction.cellGeometry01_x`, `OAI.AtomicTriangular.Construction.cellGeometry02_x`, `OAI.AtomicTriangular.Construction.cellGeometry04_x`, `OAI.AtomicTriangular.Construction.cellGeometry05_x`, `OAI.AtomicTriangular.Construction.cellGeometry06_x`, `OAI.AtomicTriangular.Construction.cellGeometry09_x`, `OAI.AtomicTriangular.Construction.cellGeometry10_x`, `OAI.AtomicTriangular.Construction.cellGeometry11_x`, `OAI.AtomicTriangular.Construction.cellGeometry12_x`, `OAI.AtomicTriangular.Construction.cellGeometry13_x`, `OAI.AtomicTriangular.Construction.cellGeometry14_x`, `OAI.AtomicTriangular.Construction.cellGeometry15_x`, `OAI.AtomicTriangular.Construction.cellGeometry16_x`, `OAI.AtomicTriangular.Construction.cellGeometry17_x`, `OAI.AtomicTriangular.Construction.cellGeometry18_x`, `OAI.AtomicTriangular.Construction.cellGeometry19_x`, `OAI.AtomicTriangular.Construction.cellGeometry20_x`, `OAI.AtomicTriangular.Construction.cellGeometry21_x`, `OAI.AtomicTriangular.Construction.cellGeometry22_x`, `OAI.AtomicTriangular.Construction.cellGeometry23_x`, `OAI.AtomicTriangular.Construction.cellGeometry24_x`, `OAI.AtomicTriangular.Construction.cellGeometry25_x`, `OAI.AtomicTriangular.Construction.cellGeometry26_x`, `OAI.AtomicTriangular.Construction.cellGeometry27_x`, `OAI.AtomicTriangular.Construction.cellGeometry28_x`, `OAI.AtomicTriangular.Construction.cellGeometry29_x`, `OAI.AtomicTriangular.Construction.cell_factors_x`, `OAI.AtomicTriangular.Construction.cell_geometry_x`, `OAI.AtomicTriangular.Construction.correctionFinite_small_x`, `OAI.AtomicTriangular.Construction.correctionTail_small_x`, `OAI.AtomicTriangular.Construction.finiteCurvatureCap_bound_x`, `OAI.AtomicTriangular.Construction.finiteSpectral_curvature_x`, `OAI.AtomicTriangular.Construction.near_signs_x`, `OAI.AtomicTriangular.Construction.pairJ_curvature_x`, `OAI.AtomicTriangular.Construction.tailFixedColumn_norm_constant_x`, `OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.UminusTable_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn0_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn0_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn0_2_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_2_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns0_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns1_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns2_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns2_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns3_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns4_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable0_x`, `OAI.AtomicTriangular.FiniteCertificate.taylorExpTable_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_5_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_6_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_6_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_5_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_5_mem_x` and `OAI.AtomicTriangular.FiniteCertificate.tw1_1_mem_x`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X005
import Definitions.Def_OAIQ257X010

section
-- module Solutions.OAIQ250_TR.Triangular_Auxiliary_Bernstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Finset
noncomputable section
namespace AtomicTriangular.Bernstein

def bernsteinBasis (n d : ℕ) (x : ℝ) : ℝ :=
  (n.choose d : ℝ) * x^d * (1-x)^(n-d)

def bernsteinCoefficient (n : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ r ∈ range (n+1), (d.choose r : ℝ)/(n.choose r : ℝ)*c r

end AtomicTriangular.Bernstein
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def R0Box (i : Fin 20) (j : Fin 3) : RI := jetMatrixTable i (if j.val<2 then ⟨j.val,by omega⟩ else 22)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
def minusInverseBox (i j : Fin 20) : RI := (minusApproxBox i j).widen 10000000000000000000000000000000000000
def plusInverseBox (i j : Fin 20) : RI := (plusApproxBox i j).widen 10000000000000000000000000000000000000

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSumsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def tailConstantEnvelope : ℝ :=
  ∑ j : Fin 31, tailEnvelopeSum 0 0 j * ‖fourierCoeff j‖
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def boundV : Fin 1 → RI := ![⟨126171129704549000174024895793069760796707492960977549,126171129704549000174024895793069760796707905563055481⟩]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Param
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Matrix

def Wstar : ℝ := 61/10000
def DeltaStar : ℝ := 18/100000
def Ustar : ℝ := 48/100000
def Pstar : ℝ := 3/10000000

def ParameterPolytope (e : Fin 8 → ℝ) : Prop :=
  ∃ z w delta u a r p : ℝ,
    0 ≤ z ∧ z ≤ Z ∧ 0 ≤ w ∧ w ≤ Wstar ∧ 0 ≤ delta ∧ delta ≤ DeltaStar ∧
    0 ≤ u ∧ u ≤ Ustar ∧ 0 ≤ a ∧ a ≤ Z*u ∧ 0 ≤ r ∧ r ≤ Pstar ∧
    0 ≤ p ∧ p ≤ Pstar ∧ e = ![z,1,Z*w-delta,w,a,u,r,p]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def etaPiBox : RI := piBox.mul ((RI.point 1).divNat 5)
def targetExp1 : CI := ⟨⟨1874456087585338350570292911831758804106207970527136794947232,1874456087585338350570292911831758804106207970527140544080552⟩,⟨-89486,127712⟩⟩
def targetExp3 : CI := ⟨⟨6586061962694724858363079230007804318951962476704132881322785,6586061962694724858363079230007804318951962476704172398460991⟩,⟨-299830,445690⟩⟩
def targetExp4 : CI := ⟨⟨12345283939187368579546362975259193426256726581361584530677933,12345283939187368579546362975259193426256726581361683294398213⟩,⟨-559982,834380⟩⟩
def targetExp7 : CI := ⟨⟨81306804970548025028728213865486592780875124829090734179774898,81306804970548025028728213865486592780875124829091872484574647⟩,⟨-3590186,5502878⟩⟩
def targetExp9 : CI := ⟨⟨285678421101121373296910627054045027465449762627940480024201346,285678421101121373296910627054045027465449762627945622269619008⟩,⟨-12198192,19184204⟩⟩
def targetExp12 : CI := ⟨⟨1881495782776781532852850263821915726713407411393103994834360489,1881495782776781532852850263821915726713407411393149150951454626⟩,⟨-79274714,125984300⟩⟩
def targetExp13 : CI := ⟨⟨3526781223792079544620739081630049069956543439091374085403532668,3526781223792079544620739081630049069956543439091465782125133725⟩,⟨-147616118,236466238⟩⟩
def targetExp16 : CI := ⟨⟨23227599668762967071881451076152236804878668516890355990185412686,23227599668762967071881451076152236804878668516891099276032739152⟩,⟨-963281130,1545340506⟩⟩
def targetExp19 : CI := ⟨⟨152978410663140367916372603043345717766819220723182442689619188462,152978410663140367916372603043345717766819220723188255886496314568⟩,⟨-6149562064,10174537158⟩⟩
def targetExp21 : CI := ⟨⟨537502744532089381174095882504998632861298023555570017400851929660,537502744532089381174095882504998632861298023555592592579196475004⟩,⟨-21799573834,35672662814⟩⟩
def targetExpTable : Fin 10 → CI := ![targetExp1,targetExp3,targetExp4,targetExp7,targetExp9,targetExp12,targetExp13,targetExp16,targetExp19,targetExp21]
def targetCoefficientBox (n : Fin 10) : RI := (QBox1.mul (QTable n).invPos).mul (targetExpTable n).re

def YfBox (i : Fin 20) (j : Fin 8) : RI :=
  if i.val<8 then (targetCoefficientBox ⟨i.val/2,by omega⟩).mul
    (if i.val%2=0 then (if j.val=i.val then RI.point 1 else RI.point 0)
     else (if j.val=i.val then RI.point (-1) else if j.val=i.val-1 then etaPiBox.sub (DTable ⟨i.val/2,by omega⟩) else RI.point 0))
  else RI.point 0

def gammaBox (side : Fin 2) (i : Fin 3) (j : Fin 8) : RI :=
  if j.val=1 then (if i.val=0 then (RI.point 11).divNat 25 else if i.val=1 then RI.point 0 else if side.val=0 then ((RI.point 3).divNat 500).neg else (RI.point 3).divNat 500) else RI.point 0

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def rhsPlusTableRow0 : Fin 8 → RI := ![⟨1874456087585338350570292911831758804106153791481581659431790,1874456087585338350570292911831758804106262149572695679595998⟩,⟨-791886840546457827717261766487251937317323882728293964008424,-791886840546457827717261766487251908072700273946820069026578⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
def rhsPlusTableRow1 : Fin 8 → RI := ![⟨561973897773317740648608818680619254334178781616840649784489,561973897773317740648608818680619254334243741279123192255363⟩,⟨-250271701543505453454448791090305012853544068561128160160704,-250271701543505453454448791090304914713595166685245179068394⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
def rhsPlusTableRow2 : Fin 8 → RI := ![⟨0,4⟩,⟨-18237250733434003640496825739255374539565914380627990004759,-18237250733434003640496825739255360847254951978029207854377⟩,⟨13579638705302215226590059801737535389302367201278493258175143,13579638705302215226590059801737535389303510602438686091632968⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
def rhsPlusTableRow3 : Fin 8 → RI := ![⟨0,4⟩,⟨-169326312877590649891007097087058863936249646326846562533323,-169326312877590649891007097087058818576690066430882065576176⟩,⟨23119557865402894747844636724206319683690342698197126975826623,23119557865402894747844636724206319683693301089643897369978455⟩,⟨-13579638705302215226590059801737535389303510602438686091632964,-13579638705302215226590059801737535389302367201278493258175139⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
def rhsPlusTableRow4 : Fin 8 → RI := ![⟨0,4⟩,⟨5156498132250989535156195502169660220036359023416553880220,5156498132250989535156195502169665526862152116117638474608⟩,⟨0,4⟩,⟨0,4⟩,⟨16694432693867460272613036027758482030952285631480513206525991,16694432693867460272613036027758482030953395543236286930261587⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
def rhsPlusTableRow5 : Fin 8 → RI := ![⟨0,4⟩,⟨22756504449753060760971129249563838900133777152108942376915,22756504449753060760971129249563860119555443019686586040862⟩,⟨0,4⟩,⟨0,4⟩,⟨-22202865676981591280126265323976477328265401786512631278337981,-22202865676981591280126265323976477328262526089602442488170375⟩,⟨-16694432693867460272613036027758482030953395543236286930261583,-16694432693867460272613036027758482030952285631480513206525987⟩,⟨0,4⟩,⟨0,4⟩]
def rhsPlusTableRow6 : Fin 8 → RI := ![⟨0,4⟩,⟨-117595715452103264028043496323669029766028321257604540047,-117595715452103264028043496323668923841770177450798209097⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨16555288516830855347972997338697702932368932792470320650261501,16555288516830855347972997338697702932369504183796023455900141⟩,⟨0,4⟩]
def rhsPlusTableRow7 : Fin 8 → RI := ![⟨0,4⟩,⟨-29404890737555391624532723396911892982956483791454969802,-29404890737555391624532723396911490107036626586330906925⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨12793894392299767606603013637939229848621314311453231203851719,12793894392299767606603013637939229848621794570562709080136670⟩,⟨-16555288516830855347972997338697702932369504183796023455900137,-16555288516830855347972997338697702932368932792470320650261497⟩]
def rhsPlusTableRow8 : Fin 8 → RI := ![⟨0,3⟩,⟨-14161368646876411825263828259605396135656776103879864677,-14161368646876411825263828259605370656949114883927935600⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow9 : Fin 8 → RI := ![⟨0,3⟩,⟨48658109850423137779720163102648641177497040217518896331,48658109850423137779720163102648726102948238732586202357⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow10 : Fin 8 → RI := ![⟨0,3⟩,⟨-866064556935212017717311504278910933528986846619607011,-866064556935212017717311504278902532506275274466502594⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow11 : Fin 8 → RI := ![⟨0,3⟩,⟨-10084402938649966990755679536537123179970132791391599231,-10084402938649966990755679536537094438721227603950472864⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow12 : Fin 8 → RI := ![⟨0,3⟩,⟨678489486441443849645465154620129865407085455173189260,678489486441443849645465154620133388074543266831996269⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow13 : Fin 8 → RI := ![⟨0,3⟩,⟨606398979550235099515397986722593475474322441158528681,606398979550235099515397986722605610437472930042105979⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow14 : Fin 8 → RI := ![⟨0,3⟩,⟨-5541246284173884064720658849882916513100465556579359,-5541246284173884064720658849882865872260329082319212⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow15 : Fin 8 → RI := ![⟨0,3⟩,⟨21780503350109283249490080573320501782310770033812801,21780503350109283249490080573320686807820666393657737⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow16 : Fin 8 → RI := ![⟨0,3⟩,⟨-242196331137455198322408323680282630504323497545100,-242196331137455198322408323680276724090703668020701⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow17 : Fin 8 → RI := ![⟨0,3⟩,⟨-1322670319984407916629287226643997731362671243382595,-1322670319984407916629287226643975757549641322032420⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow18 : Fin 8 → RI := ![⟨0,3⟩,⟨-61388454782416196798460909664239373375784406252275,-61388454782416196798460909664238058894167176055713⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTableRow19 : Fin 8 → RI := ![⟨0,3⟩,⟨81191344668734640112990239726836010545630862295641,81191344668734640112990239726840147684908547515557⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsPlusTable : Fin 20 → Fin 8 → RI := ![rhsPlusTableRow0,rhsPlusTableRow1,rhsPlusTableRow2,rhsPlusTableRow3,rhsPlusTableRow4,rhsPlusTableRow5,rhsPlusTableRow6,rhsPlusTableRow7,rhsPlusTableRow8,rhsPlusTableRow9,rhsPlusTableRow10,rhsPlusTableRow11,rhsPlusTableRow12,rhsPlusTableRow13,rhsPlusTableRow14,rhsPlusTableRow15,rhsPlusTableRow16,rhsPlusTableRow17,rhsPlusTableRow18,rhsPlusTableRow19]
def rhsMinusTableRow0 : Fin 8 → RI := ![⟨1874456087585338350570292911831758804106153791481581659431790,1874456087585338350570292911831758804106262149572695679595998⟩,⟨3800510165282262322258459079662541176708724756910040726396,3800510165282262322258459079662541176730295556369595812238⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
def rhsMinusTableRow1 : Fin 8 → RI := ![⟨561973897773317740648608818680619254334178781616840649784489,561973897773317740648608818680619254334243741279123192255363⟩,⟨-1871079386855962384913401297548939417519015300278098369966479,-1871079386855962384913401297548939417518755299779619568913209⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
def rhsMinusTableRow2 : Fin 8 → RI := ![⟨0,4⟩,⟨32298687622280709990851182301646460640599555784330561537103,32298687622280709990851182301646460640624089521277919177400⟩,⟨13579638705302215226590059801737535389302367201278493258175143,13579638705302215226590059801737535389303510602438686091632968⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
def rhsMinusTableRow3 : Fin 8 → RI := ![⟨0,4⟩,⟨88281906839232413390666577025539590651677053747313876301865,88281906839232413390666577025539590651848902814068400484909⟩,⟨23119557865402894747844636724206319683690342698197126975826623,23119557865402894747844636724206319683693301089643897369978455⟩,⟨-13579638705302215226590059801737535389303510602438686091632964,-13579638705302215226590059801737535389302367201278493258175139⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
def rhsMinusTableRow4 : Fin 8 → RI := ![⟨0,4⟩,⟨-28267994688546660485407508871694824140623172721543163089282,-28267994688546660485407508871694824140613970884994270402676⟩,⟨0,4⟩,⟨0,4⟩,⟨16694432693867460272613036027758482030952285631480513206525991,16694432693867460272613036027758482030953395543236286930261587⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
def rhsMinusTableRow5 : Fin 8 → RI := ![⟨0,4⟩,⟨106868635310709889166732321991480152333396950299700409162860,106868635310709889166732321991480152333467326256028532411470⟩,⟨0,4⟩,⟨0,4⟩,⟨-22202865676981591280126265323976477328265401786512631278337981,-22202865676981591280126265323976477328262526089602442488170375⟩,⟨-16694432693867460272613036027758482030953395543236286930261583,-16694432693867460272613036027758482030952285631480513206525987⟩,⟨0,4⟩,⟨0,4⟩]
def rhsMinusTableRow6 : Fin 8 → RI := ![⟨0,4⟩,⟨-7234947148275458062642027223080526693864268565711158195726,-7234947148275458062642027223080526693864157168542168372771⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨16555288516830855347972997338697702932368932792470320650261501,16555288516830855347972997338697702932369504183796023455900141⟩,⟨0,4⟩]
def rhsMinusTableRow7 : Fin 8 → RI := ![⟨0,4⟩,⟨12841934272106857530937290901480783425456784008202733457126,12841934272106857530937290901480783425457199118225049012963⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨12793894392299767606603013637939229848621314311453231203851719,12793894392299767606603013637939229848621794570562709080136670⟩,⟨-16555288516830855347972997338697702932369504183796023455900137,-16555288516830855347972997338697702932368932792470320650261497⟩]
def rhsMinusTableRow8 : Fin 8 → RI := ![⟨0,3⟩,⟨6297752757445065626459474264305459413090904494770990068929,6297752757445065626459474264305459413090938991820012428757⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow9 : Fin 8 → RI := ![⟨0,3⟩,⟨7519050541546144040317772025475080705789468527006476842416,7519050541546144040317772025475080705789633905782515434443⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow10 : Fin 8 → RI := ![⟨0,3⟩,⟨13330763399432416902771460277347667500538198574829617287533,13330763399432416902771460277347667500538322462674276340395⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow11 : Fin 8 → RI := ![⟨0,3⟩,⟨12190911551380191881788561565169501321963919210555605989272,12190911551380191881788561565169501321964597492385241151826⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow12 : Fin 8 → RI := ![⟨0,3⟩,⟨-2614594628346643569837666170574498402485896795895652666701,-2614594628346643569837666170574498402485836711283028534835⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow13 : Fin 8 → RI := ![⟨0,3⟩,⟨47416265186631222392752187825280969532085989419846286270364,47416265186631222392752187825280969532086462649610979995513⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow14 : Fin 8 → RI := ![⟨0,3⟩,⟨127985850114211739748205125064025577081636368035293151673,127985850114211739748205125064025577081636592591373167215⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow15 : Fin 8 → RI := ![⟨0,3⟩,⟨3050603057555462399132639579408736584554558738439309507917,3050603057555462399132639579408736584554560584703907882762⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow16 : Fin 8 → RI := ![⟨0,3⟩,⟨258391711635444201049532658285191228798640070817137966727,258391711635444201049532658285191228798640192546992384573⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow17 : Fin 8 → RI := ![⟨0,3⟩,⟨1764409646795333172805051773694276725308271097823259265427,1764409646795333172805051773694276725308272097740979488536⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow18 : Fin 8 → RI := ![⟨0,3⟩,⟨61184842643293630433407730629952597930545038076115326901,61184842643293630433407730629952597930545106423504287423⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTableRow19 : Fin 8 → RI := ![⟨0,3⟩,⟨-1230482993355089794580253355339900524326004622452759641840,-1230482993355089794580253355339900524326004213985555240154⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
def rhsMinusTable : Fin 20 → Fin 8 → RI := ![rhsMinusTableRow0,rhsMinusTableRow1,rhsMinusTableRow2,rhsMinusTableRow3,rhsMinusTableRow4,rhsMinusTableRow5,rhsMinusTableRow6,rhsMinusTableRow7,rhsMinusTableRow8,rhsMinusTableRow9,rhsMinusTableRow10,rhsMinusTableRow11,rhsMinusTableRow12,rhsMinusTableRow13,rhsMinusTableRow14,rhsMinusTableRow15,rhsMinusTableRow16,rhsMinusTableRow17,rhsMinusTableRow18,rhsMinusTableRow19]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def UplusCachedBox (i : Fin 20) (j : Fin 8) : RI := matrixMul minusInverseBox rhsPlusTable i j
def UplusTableRow0 : Fin 8 → RI := ![⟨1986693347139307363069307549061542363564615698889849458598851,1986693347139307363069356277661249536686648911145041871983310⟩,⟨-821479769590824363517157442250763278014592768659042968034089,-821479769590824363517132285106908083038520168903884236111878⟩,⟨485544049925449592286071207339654743309394861714122187695211,485544049925449592286805191271068845509155326037156531983846⟩,⟨639212987895441472011344054292593539526884100702724437646556,639212987895441472011615647066699583831469723424341058369526⟩,⟨228836551963986348604367137512630920665847740131476562028361,228836551963986348605145083480047901696961762742823724698717⟩,⟨285606114266839981639764250553122929365986496864264388180399,285606114266839981640098139207000278571457745806196020955012⟩,⟨36928626106145596274092399966893700920531670371278707437803,36928626106145596274679383625076313379626817864916951501503⟩,⟨42252808487510968430848882421627503524064237362317812570210,42252808487510968431179988191964120631025155627878044554386⟩]
def UplusTableRow1 : Fin 8 → RI := ![⟨-4061662620931796005960790460761872120270077723473704578993530,-4061662620931796005960741732162164947147060630547338950058326⟩,⟨1611684366526660929166421067204346355213326245840282326330341,1611684366526660929166446224348202539898148234833348458159546⟩,⟨-10317694815521480120945946362400969791247185809377929839802845,-10317694815521480120945212378469555689046773231705844328666846⟩,⟨740060655766027075607945228248285092505260645451352849185493,740060655766027075608216821022391136809854759513788496720843⟩,⟨5207827054427945726836418225817469435747272244590093218679521,5207827054427945726837196171784886416778711615245265216746467⟩,⟨457424076933228735035869240312197280693615067076227624414698,457424076933228735036203128966074629899097739154249803620010⟩,⟨-547803623939188981483470784552047465489413928720175316110827,-547803623939188981482883800893864853030303328854529426323942⟩,⟨73891959532345772828044947091747224219741420841935107841647,73891959532345772828376052862083841326703431105163712697317⟩]
def UplusTableRow2 : Fin 8 → RI := ![⟨1035723349336988548181576996465900019540520829687922799975308,1035723349336988548181625725065607192662636530968343811386823⟩,⟨-409912969811677806357637623665751205139047390920289497670240,-409912969811677806357612466521895854154827460608562772353625⟩,⟨13653503127514328331002127742495694647229742445354207208227388,13653503127514328331002861726427108749430995898297575642129674⟩,⟨1703011650132763108308114362525180507958179766782420167597928,1703011650132763108308385955299286552262854961005238717231672⟩,⟨1422135166803965730345693870085547757046804540569382086050210,1422135166803965730346471816052964738078109180468270533482603⟩,⟨1321194033931200497409543626010365669830529787561859483020544,1321194033931200497409877514664243019036069886474751491916663⟩,⟨158589061861584559370323979869385965300100545291889072662952,158589061861584559370910963527568577759205264800324166921075⟩,⟨138747635088733305959341534019418296793145539112333319830986,138747635088733305959672639789754913900109787812566380423514⟩]
def UplusTableRow3 : Fin 8 → RI := ![⟨-291428142843590255695145096723148280742660950328010692581326,-291428142843590255695096368123441107620813691357674185659938⟩,⟨-5197305332849089921052145479633500712571897520914729245625,-5197305332849089921026988335778390993370336387696642494949⟩,⟨15091671442507824224467185605618809965795758241343511197915161,15091671442507824224467919589550224067997487184568118664479491⟩,⟨-9720105584092971922877674927164618902348352228821281329353662,-9720105584092971922877403334390512858043001997897973403649455⟩,⟨7241316749981627211930988246901200563458184529994043924663493,7241316749981627211931766192868617544490301503611589755110098⟩,⟨5921609014257910796954949651162361061942890744367193548627744,5921609014257910796955283539816238411148736697019576676618536⟩,⟨-3281521228449508397117698048145501634213637749043289582991816,-3281521228449508397117111064487319021754373913151286499799847⟩,⟨5128681571235149581590793641024196983403052632825333024557826,5128681571235149581591124746794533600510189104737746619239169⟩]
def UplusTableRow4 : Fin 8 → RI := ![⟨-305915701279620595912625374985685257361050444080592383441441,-305915701279620595912576646385978084239139233261152546550936⟩,⟨119339409606492460801466403684868650388340851413552633256778,119339409606492460801491560828723796868478540613831363720591⟩,⟨269724349152001751014186823604587990143750884802415296794684,269724349152001751014920807536002092343446640235200618032651⟩,⟨-636124622906044925171244273041449440105987796505533207658627,-636124622906044925170972680267343395801402433823243744892740⟩,⟨16017898119402609444059827341067711743533180270841206646355775,16017898119402609444060605287035128724565464254285106387254963⟩,⟨-630148574719034063444028645427660118186143700369375246042220,-630148574719034063443694756773782768980649544885230916888496⟩,⟨106013598376091345547213095350637319719183737385536116326970,106013598376091345547800079008819932178287537289116574063578⟩,⟨-286244959833732399024640331377248130703270741594897594156986,-286244959833732399024309225606911513596301402153307898146191⟩]
def UplusTableRow5 : Fin 8 → RI := ![⟨986237111696857445652984441627648795100332173267928154457654,986237111696857445653033170227355968222422807624132168264328⟩,⟨-360313591574799248104711431390845940264935740081918011037590,-360313591574799248104686274246990611503540126334023502414750⟩,⟨1665786412467845017209646805879148840402151082648983992937267,1665786412467845017210380789810562942602066657935591447075613⟩,⟨793515237724677098512024942729781985565668294355699937163795,793515237724677098512296535503888029870266909276542464023518⟩,⟨-22297921228339977718580414077077006320098197258016906872123254,-22297921228339977718579636131109589339064250653592432914969444⟩,⟨-16780521137003340119159550860383545114975315166326122592632536,-16780521137003340119159216971729667765768747270350419691155779⟩,⟨1549887790791655985993712630946544331297391679358246244433303,1549887790791655985994299614604726943756540596831060464268833⟩,⟨-1670645917637407328646289852906296121408520312441457528424185,-1670645917637407328645958747135959504301503191609783360370358⟩]
def UplusTableRow6 : Fin 8 → RI := ![⟨4605523100888349195387394322616313269142641345612329897943,4605523100888349195436122922323486390968352873118942592088⟩,⟨-1786859192101072274600115957152797525160713529569391414374,-1786859192101072274574958813297739360421667109107806943517⟩,⟨-14679038797159138572190020680818337231558301323807498912788,-14679038797159138571456036749404235032065733279329536283312⟩,⟨14147274342295707726568874505390262916581827757589436605406,14147274342295707726840467279496307221114820149520307232829⟩,⟨18758685009942353930215920360636571678714748002487844513527,18758685009942353930993866328053552709773281595982903593312⟩,⟨19160666067857874815424156806241316814648905337725429876718,19160666067857874815758045460118666020102439934961954628311⟩,⟨16536888200629906078120330727365395899121307562649727219108925,16536888200629906078120917711023578511580971158496458279639480⟩,⟨23694833833723544104505526398211069248945861129546261374509,23694833833723544104836632168547686355906138882817685689024⟩]
def UplusTableRow7 : Fin 8 → RI := ![⟨-16119301300562814968643206005621312602362918736693408165368,-16119301300562814968594477405914139480534029502007450686861⟩,⟨6015076832129169581213457412398199502750793295943157775444,6015076832129169581238614556253261008980477202986784658454⟩,⟨12817818933542460369284221555413995214596292298101392613859,12817818933542460370018205486828097414095378809315927359120⟩,⟨-31759794089491983178895319714848988462039605224166062021626,-31759794089491983178623726940742944157505129863803564388297⟩,⟨-33382726779279953165929531641743446571113763441879356113117,-33382726779279953165151585674326465540052688072863760793711⟩,⟨-32641174821595410067149290693955669891356192341244247037108,-32641174821595410066815402040078320685901761506596487575415⟩,⟨12799602387854164385133318487058264718073428906119268506877896,12799602387854164385133905470716447330533001405003564462883210⟩,⟨-16571749206588792621286308361124124087099471661545497092634312,-16571749206588792621285977255353787469991940242146688181834869⟩]
def UplusTableRow8 : Fin 8 → RI := ![⟨334620199457911238472536569170000228793451427222582438277,334620199457911238521265168877173350617928616529990757024⟩,⟨-131963123969135446696739855162220424031565665638080785439,-131963123969135446671582711307163565696727205310206708974⟩,⟨-1786462117016899155715044671887730951431662095749206314433,-1786462117016899154981060740473628751942633140337344139906⟩,⟨1343953461413856873835877880768791646567155011760692170842,1343953461413856874107470654874835951099069368239573529748⟩,⟨1938640259766840776370635147542148102632499594085075608509,1938640259766840777148581114959129133687693316360149398960⟩,⟨2058434785984490256463738626324526836270947238467879382323,2058434785984490256797627280201876041723344811889471792194⟩,⟨-2859954351232909057992854045926769851177795079401274681665,-2859954351232909057405870387744157392086168394102653862412⟩,⟨3319245935115988916133758630822792847317981329855395136966,3319245935115988916464864401159409954277555837504157956375⟩]
def UplusTableRow9 : Fin 8 → RI := ![⟨-4747515471402537682327975613242212667119053764582847870337,-4747515471402537682279247013535039545293323898984703078022⟩,⟨1794172868172317193956873495701036994029089135581157157351,1794172868172317193982030639556095142206265988832777104615⟩,⟨10835668656731998719590974205434722091595078437645507369043,10835668656731998720324958136848824291087369388574146125195⟩,⟨-12484224422810210797462090023177640173590392421012220449976,-12484224422810210797190497249071595869057540057343416607550⟩,⟨-15557093789015091266640715343555553153852742970180611785806,-15557093789015091265862769376138572122794801898234149839274⟩,⟨-16071094168400487300295605347876079755372127034634710435096,-16071094168400487299961716693998730549918797844328411924365⟩,⟨14739414936140896477382439125745966555346885563342413751654,14739414936140896477969422783928579014438959026892604256955⟩,⟨-19052964940202232146239020668417774001166041057615457597724,-19052964940202232145907914898081156894205923514395226971911⟩]
def UplusTableRow10 : Fin 8 → RI := ![⟨307234486754712436770054806415977816364062616042988840202,307234486754712436818783406123150938188527429587969696366⟩,⟨-114599847610672232241461833549191635332802622644100296332,-114599847610672232216304689694134809823589639402035908466⟩,⟨-565664370220755119697050307617696337688237653459077175301,-565664370220755118963066376203594138199323281446725431684⟩,⟨742152805316553120512818759415172457133984627059053501701,742152805316553120784411533521216761665848312118516478386⟩,⟨888546319602983792823367329271923120664949013549718682948,888546319602983793601313296688904151719916522745620008915⟩,⟨922818397115624418898510905453552408684051205545282848528,922818397115624419232399559330901614136373278708605454059⟩,⟨-803124752553930466780293152462328191730861682957744282712,-803124752553930466193309494279715732639310799532260491792⟩,⟨1048511054642646557360345340405375418579770479205690913387,1048511054642646557691451110741992525539266614423048856347⟩]
def UplusTableRow11 : Fin 8 → RI := ![⟨1366040886861774587192153448373658910209601510662235373157,1366040886861774587240882048080832032034367886266114715390⟩,⟨-512028452219385358115759097183590046792219722359751390853,-512028452219385358090601953328532903254407052223866878303⟩,⟨-3282325042271927215102000269418975986873564135938237255462,-3282325042271927214368016338004873787383832299390854406171⟩,⟨3638576692651778459778688774490248400979014159446538339597,3638576692651778460050281548596292705511121722454823050399⟩,⟨4566407714192078740651946363147147556837679037903449076129,4566407714192078741429892330564128587893415619320963246834⟩,⟨4811141712339158747387200397268498956298064738570554318813,4811141712339158747721089051145848161750645322809811896885⟩,⟨-5214469226949034795410158294552748885123440162128288031180,-5214469226949034794823174636370136426031725086592175140984⟩,⟨6368599886301079773968403201482614399493330057035050199225,6368599886301079774299508971819231506453009810472488544337⟩]
def UplusTableRow12 : Fin 8 → RI := ![⟨-173747742130567374257262608166780306725388321267835257788,-173747742130567374208534008459607184900961117454990691060⟩,⟨64834060944343125160527680141088240901586726938177078372,64834060944343125185684823996145024791958796402481926654⟩,⟨355171294754373967734682730121585704018771836123930399560,355171294754373968468666661535687903507592918519392359325⟩,⟨-434813001416230564913911585319990253176102294941164296538,-434813001416230564642318811213945948644264487793181826074⟩,⟨-530065210885915690704352227815306972388338866497441038737,-530065210885915689926406260398325941333443396417187927113⟩,⟨-555034226473402373745578248382968551039888835716264459691,-555034226473402373411689594505619345587591214295751494102⟩,⟨540700855222715208918276336015001626086794132339729723675,540700855222715209505259994197614085178334604085245707296⟩,⟨-680540604281397357169843407630130582110975954074774501340,-680540604281397356838737637293513475151492519036168358318⟩]
def UplusTableRow13 : Fin 8 → RI := ![⟨148589403153957986582174870832568550978015492039711780695,148589403153957986630903470539741672802435053025501269844⟩,⟨-55100077423668854919668692561715631183264720239195499231,-55100077423668854894511548706658846702606721165951395882⟩,⟨-127013265115886649000550079749432834181322841586366528511,-127013265115886648266566148335330634692533057258098995137⟩,⟨294979054127110637222446605242096749273502597133148194646,294979054127110637494039379348141053805328630308270673256⟩,⟨313354828112774679986489642953049819840593719597844655111,313354828112774680764435610370030850895439732563418077870⟩,⟨310036691512262174635745361041297414533618223806750572673,310036691512262174969634014918646619985899556824466308586⟩,⟨-54010458250822915093364289096377901542767583897981108820,-54010458250822914506380630913765442451240065535512980705⟩,⟨164559051788451963262086852013622460383707583534659730806,164559051788451963593192622350239567343173209920579609801⟩]
def UplusTableRow14 : Fin 8 → RI := ![⟨2136322210551163633034402999734471164250670704082559067,2136322210551163681763002706907592988629309539691265814⟩,⟨-793927780163033904232163693480735877879125716517072095,-793927780163033879075019838424003135333703143326318453⟩,⟨-4531269543050164640673747624532730918381163799820335829,-4531269543050163906689816210430531429685664397796133977⟩,⟨5399725059498081271279626903017329980758242597254757895,5399725059498081542872401009061634512559893287098413200⟩,⟨6619416735346762942074166140979392841705503521087812143,6619416735346763720020133557960423896492915278000704777⟩,⟨7000299430829322558803214062989390856721853105718601690,7000299430829322892691867940338596308983039068415092161⟩,⟨-7449575714564736670200724249950546735467863757933956277,-7449575714564736083217066067338087643947365832403828775⟩,⟨9104652060365146844196924704063428555942969178921670410,9104652060365147175302695040680535515403230191990652757⟩]
def UplusTableRow15 : Fin 8 → RI := ![⟨-8342747890298384002172857741412576239101004018043350308,-8342747890298383953444258034239454414720611057040682464⟩,⟨3104019807917668074846651430426891052035021252809106902,3104019807917668100003795285483625649783903772848510750⟩,⟨16870938263017501443342884236213784788435225281833744360,16870938263017502177326815650315984277135231671534272476⟩,⟨-20753787737476925971188310376199070268964923656143941261,-20753787737476925699595536270154765737161980159218988598⟩,⟨-25236704483363587134240733605582093872768712421821070002,-25236704483363586356294766188601062817977445543479616526⟩,⟨-26537503715558473671786153934037472144145516136434322974,-26537503715558473337897500056688266691883031263310134104⟩,⟨26586757809374134349596062510412302014115675187947466377,26586757809374134936579720693024761105636889725394957527⟩,⟨-33113977339471426491199500500356542592953282663505677301,-33113977339471426160093730163739435633492192989541627423⟩]
def UplusTableRow16 : Fin 8 → RI := ![⟨111701632346866956747370544323349933453683098943596695,111701632346867005475970251496471757831749261921089362⟩,⟨-41549256546675982409615778303799958585796877604512947,-41549256546675957252471923247067823364683032651005822⟩,⟨-217670273058422604118775779758336839042167543282137329,-217670273058421870134844365656137350348156267000105971⟩,⟨274317414412391361368543997595234055874165761058532938,274317414412391632961318103639538587675384893246271816⟩,⟨331412288635770791858471354676166145662110765670044732,331412288635771569804438771657197200448206389243734006⟩,⟨347644643231363292530904782445463704991058676568703623,347644643231363626419558659794669157251802344525908241⟩,⟨-336619154263351567983909544943267757201558401493368910,-336619154263350981000251362330808665681326260515806331⟩,⟨423680133516206223237866197225269412990297290405954136,423680133516206554343636533842376372450258687309828380⟩]
def UplusTableRow17 : Fin 8 → RI := ![⟨1236618737874583492092583635151542141733062127302558906,1236618737874583540821183342324663966111445862615606490⟩,⟨-458486086887487228739886236031516431672093378169550278,-458486086887487203582742380974783968856890827177423478⟩,⟨-2469642091654901167423339664165314122656801740004052402,-2469642091654900433439408250063114633961975650985912953⟩,⟨3055077615350094904301826773126843964033728523784658818,3055077615350095175894600879171148495835181795076461549⟩,⟨3704297360327639729339523113437783274977262196834965051,3704297360327640507285490530418814329764063284941141580⟩,⟨3914174423068793943533697263484618170420466999808055690,3914174423068794277422351140833823622681447784737280137⟩,⟨-4044296474459181723049293243402631258023558033399727534,-4044296474459181136065635060790172166503187276683885297⟩,⟨4980241493598126263060813413959358501061721536484858443,4980241493598126594166583750576465460521840199124907356⟩]
def UplusTableRow18 : Fin 8 → RI := ![⟨69613006674815269766916844430627921971374169177350528,69613006674815318495516551603749746349428426058033290⟩,⟨-25808108175996015060539018944838697918081635791382315,-25808108175995989903395163888106578964178970656722353⟩,⟨-136519180022514522931453359539441219002847579724018837,-136519180022513788947521945437241730308866823384286172⟩,⟨170906038039047363932400668117829453382288362242634181,170906038039047635525174774162133985183498787226132330⟩,⟨206567731431551194707856716927637046610521120610837597,206567731431551972653824133908668101396591246003630010⟩,⟨217987930173484765567928447651496651390322550911377024,217987930173485099456582325000702103651057598778718347⟩,⟨-221464212273266432404805105114137316677979130744157527,-221464212273265845421146922501678225157751313787279459⟩,⟨274106031210033747871591685503258210180290987688263156,274106031210034078977362022120365169640247222172616859⟩]
def UplusTableRow19 : Fin 8 → RI := ![⟨40130487877781330421519616159850582242410855970157014,40130487877781379150119323332972406620456765947954968⟩,⟨-14776535145841181962467358871131345516891471032736413,-14776535145841156805323503814399231932131259278482460⟩,⟨-77408611083019641312928290771863422271635524746608423,-77408611083018907328996876669663933577676313257937087⟩,⟨97480010704922974920013636647155805076893615549753355,97480010704923246512787742691460336878097858085642687⟩,⟨117320498743053100764462119807080476461683209125272033,117320498743053878710429536788111531247735042771955822⟩,⟨125055351984635405066443656566793732425553452835815287,125055351984635738955097533915999184686282322178679761⟩,⟨-135504281436479646953080184976152791427083283077958046,-135504281436479059969422002363693699906858690392112699⟩,⟨163946128707283818894618281726826222443046455940316666,163946128707284150000388618343933181902998888351836281⟩]
def UplusTable : Fin 20 → Fin 8 → RI := ![UplusTableRow0,UplusTableRow1,UplusTableRow2,UplusTableRow3,UplusTableRow4,UplusTableRow5,UplusTableRow6,UplusTableRow7,UplusTableRow8,UplusTableRow9,UplusTableRow10,UplusTableRow11,UplusTableRow12,UplusTableRow13,UplusTableRow14,UplusTableRow15,UplusTableRow16,UplusTableRow17,UplusTableRow18,UplusTableRow19]
def UminusCachedBox (i : Fin 20) (j : Fin 8) : RI := matrixMul plusInverseBox rhsMinusTable i j
def UminusTableRow0 : Fin 8 → RI := ![⟨2682929039134676477143124686831163129950503051333963718537196,2682929039134676477143173415430870303072486670331183542979193⟩,⟨-184230622211075862339444893042701467751061426034704660973807,-184230622211075862339399962314720082207832642001306098812611⟩,⟨5239297444691062823918590252179255088674724343937283671476317,5239297444691062823919324236110669190875041714138514173191975⟩,⟨-3515507627871913335841624237435293936467585230702389925839043,-3515507627871913335841352644661187892162757424908029151814923⟩,⟨-5329840387909212346890557978828991633329715621647021754127117,-5329840387909212346889780032861574652298009189139802700790621⟩,⟨-3546261601886235947388315445215225872565108554191752903894121,-3546261601886235947387981556561348523359420524007619115267112⟩,⟨1135381768998026386603870181920783438131824684678220667650356,1135381768998026386604457165578966050590990492641036395618911⟩,⟨-2037907145863097704711996609654907514659132542900251833303438,-2037907145863097704711665503884570897552102746368008522343874⟩]
def UminusTableRow1 : Fin 8 → RI := ![⟨1325267216886631048474242314667174652751228699463736719857411,1325267216886631048474291043266881825873149873546090838981264⟩,⟨-1120678605815361150383254748201321960753154296784082535538023,-1120678605815361150383209817473340575209830466490602013478314⟩,⟨4669338676903737722769868253316970840396703168529396008912392,4669338676903737722770602237248384942596787066610369236301138⟩,⟨-2711913355278730617082549383523711774252857252095939843404690,-2711913355278730617082277790749605729948097108677843071213646⟩,⟨-4424269609475489563511126797971297514286041170455421232475024,-4424269609475489563510348852003880533254457556492827620882362⟩,⟨-2799398168828635938878595748636783980734633296108294045685568,-2799398168828635938878261859982906631528994920352047025535493⟩,⟨890007712712232973912799916044038487003020008649689770009028,890007712712232973913386899702221099462168187170459092275788⟩,⟨-1569203067092239280410248704563568541366297781212213900839143,-1569203067092239280409917598793231924259284161591937960413208⟩]
def UminusTableRow2 : Fin 8 → RI := ![⟨732754332407709656272999721840658269961231813176051890317733,732754332407709656273048450440365443083107202637325708547559⟩,⟨-352501811813189676889670335024463305416046537593658690916152,-352501811813189676889625404296481919872711303417672236932063⟩,⟨26014347589026647206583930972800924187618580129777249202089838,26014347589026647206584664956732338289820821267035394525311402⟩,⟨-7543844852767881147527649734333137275058733547283976787654338,-7543844852767881147527378141559031230753566556806094529477773⟩,⟨-12290425907514332221586306813797392956859597170420909201296891,-12290425907514332221585528867829975975827034918475813808271056⟩,⟨-8234714545976004736072894618005773851795168196789968028479363,-8234714545976004736072560729351896502589168459755145703779786⟩,⟨2244569299531016059324223990805092610639168787526231273906443,2244569299531016059324810974463275223098420897834183438659577⟩,⟨-4275350213467658523461813275126614113241321554050196098832980,-4275350213467658523461482169356277496134214534124395895982352⟩]
def UminusTableRow3 : Fin 8 → RI := ![⟨1885424543104963673294650493050725148495701075080387905236524,1885424543104963673294699221650432321617648410481279369858800⟩,⟨-398836821770029179378767913199642611397224452999039585837715,-398836821770029179378722982471661225853473067281982522517323⟩,⟨57013220204227420092145576715359297268075475662491654007347110,57013220204227420092146310699290711370282197304154975354538719⟩,⟨-32648792770671481456153652075309336573763567272484298563741337,-32648792770671481456153380482535230529456286453560840381522981⟩,⟨-32509792181879595311087366201526015140074525689058106611947424,-32509792181879595311086588255558598159039339831905419160630232⟩,⟨-23495114652116432000071357537375064984376126728358237288243155,-23495114652116432000071023648721187635169112419712255169992179⟩,⟨8492292651003940426705736538440743369784716419418756019910303,8492292651003940426706323522098925982244349087861289729746756⟩,⟨-14982479717796255714329558980652780703000590453366681244652217,-14982479717796255714329227874882444085893113886216395636700119⟩]
def UminusTableRow4 : Fin 8 → RI := ![⟨-274732101079334570200410890794926001166527360332515604320995,-274732101079334570200362162195218828044684028988251713438524⟩,⟨103686392556719962290914977694816794135107870180151007173661,103686392556719962290959908422798179678299426828008302623069⟩,⟨-4883513153383185077780936268458679737994864588271250983842109,-4883513153383185077780202284527265635794741066101273092699239⟩,⟨2895903348939129666971840254036371516418396865233312006755279,2895903348939129666972111846810477560723172500549004922720831⟩,⟨21474285211937632990149132538103399230312537638750395247302898,21474285211937632990149910484070816211345295714909757503746098⟩,⟨3287384377379442318969236100890690326035967375492138358096849,3287384377379442318969569989544567675241638194496949610533710⟩,⟨-992411152222608054394087138478880393038073139312718909028959,-992411152222608054393500154820697780578913108529044685571975⟩,⟨1845534158087119532092974958722835488801178746732236806540445,1845534158087119532093306064493172105908201903678803131207339⟩]
def UminusTableRow5 : Fin 8 → RI := ![⟨295846211867943808464370640855184775396079818835054440844655,295846211867943808464419369454891948517926336054921426669316⟩,⟨-146151153400136280810684201956868231656341659466097710614861,-146151153400136280810639271228886846113071497046455826301682⟩,⟨4590548871509185937795297647894904641039774338312742676846570,4590548871509185937796031631826318743239997175999821592912675⟩,⟨-3102566481107269165231440922667501474083212426948726600790093,-3102566481107269165231169329893395429778419390664552993810010⟩,⟨-26998260185932134390947395204368932142939282552579110520984511,-26998260185932134390946617258401515161904802946141803494422597⟩,⟨-19441605301193292894753273023737921043595325751217848220066756,-19441605301193292894752939135084043694388580935867219647248449⟩,⟨-368952209718646270249187359387133463219493679830411093134028,-368952209718646270248600375728950850760379449439883261708310⟩,⟨-179162626381749408906876666485438090658337742080350040851979,-179162626381749408906545560715101473551372098491986235412727⟩]
def UminusTableRow6 : Fin 8 → RI := ![⟨6153574309290805264600957429081192967102605472877929801942,6153574309290805264649686028788366088927403748268224275748⟩,⟨-9804686649648464559670600905507696326398942184631842197618,-9804686649648464559625670177526310783292770945224694099117⟩,⟨115894436764820074343579538752522844010852446844701930242447,115894436764820074344313522683936946210355870229467021171880⟩,⟨-66724014215490001870604084250743485942411539035449341534367,-66724014215490001870332491476637441637874119699129538486276⟩,⟨-111460081112522754890170849517204409217771424789196435006681,-111460081112522754889392903549787428186702492213870242530122⟩,⟨-80352053046553952689560985783991825837430208452903156007014,-80352053046553952689227097130114476631972605610820868834694⟩,⟨16592880433811981571742580561773896232856068982207870758123669,16592880433811981571743167545432078845315733327960318015567899⟩,⟨-58518387540020836204066403521916982391064483680801261233188,-58518387540020836203735297751580365284103004022984489069321⟩]
def UminusTableRow7 : Fin 8 → RI := ![⟨-13401110646067945702195454949439889588444459684424722843638,-13401110646067945702146726349732716466619151186440484739740⟩,⟨19587281122788895269910257439925475482381447481967193430728,19587281122788895269955188167906861025490066706316459061632⟩,⟨-244739647044415488825496819797555165834665823670644410662011,-244739647044415488824762835866141063635145464511229723575317⟩,⟨144715724321660152184239869509086211309245911488156562955227,144715724321660152184511462283192255613789897701088922646011⟩,⟨239096661256862758679816181783466763161392577875040111086193,239096661256862758680594127750883744192477126171503527784275⟩,⟨165400230316843003848141339721443236480937129296439038004475,165400230316843003848475228375320585686400386476916070203289⟩,⟨12744045786675976949901679181385772407482841616267084251608130,12744045786675976949902266165043955019942411455175149731419093⟩,⟨-16461174786357686304065239961516706236752511222370093484295793,-16461174786357686304064908855746369619644983619350836064733642⟩]
def UminusTableRow8 : Fin 8 → RI := ![⟨588913130998017573154405514128069610619622384248019703385,588913130998017573203134113835242732444040408689520076425⟩,⟨6075958818634736998209277973300455150734936403932927146878,6075958818634736998254208701281840693839431893706187236247⟩,⟨11321129098451627638587217343889944445399974836518366291678,11321129098451627639321201275304046644890101508205704504730⟩,⟨-6436006776968894866169440478182783170823275678649002231579,-6436006776968894865897847704076738866290932572937897479722⟩,⟨-10795451963966507908865240095999535026664735700502908739096,-10795451963966507908087294128582553995608564933337971046133⟩,⟨-7956378874746876243085156998745494860292307014290693213414,-7956378874746876242751268344868145654839517322274893155042⟩,⟨4655889585590297726872034975534413097455174314819036812739,4655889585590297727459018633717025556546902889712706862862⟩,⟨-6627820018486831906546425884706641075143203588047585452077,-6627820018486831906215320114370023968183514887853657306635⟩]
def UminusTableRow9 : Fin 8 → RI := ![⟨-5356460040025310045399336029313304637526667320978419849465,-5356460040025310045350607429606131515701921320056363825458⟩,⟨9881246516628856410736140964923035892315146787830872719849,9881246516628856410781071692904421435421160217996903454963⟩,⟨-100756878443015524381774282774947836842943816092749627014048,-100756878443015524381040298843533734643442291211482083760399⟩,⟨58349574961561026436158576450144052876850965531976215506030,58349574961561026436430169224250097181387679743235867427104⟩,⟨97162730051023304953506512785800124144862510292732910709291,97162730051023304954284458753217105175929588081155174143271⟩,⟨69565958160831511337249998867890764169957107041734998690590,69565958160831511337583887521768113375413992781671194259911⟩,⟨-31743932378398711954122769518016299250983767885074061616347,-31743932378398711953535785859833686791890577706964580519904⟩,⟨49667393447370941290788154234159469178833865386581442274589,49667393447370941291119260004496086285795039560066531220605⟩]
def UminusTableRow10 : Fin 8 → RI := ![⟨315771805436416811379028877324055763665296178030803573528,315771805436416811427757477031228885489695984036737657506⟩,⟨13186771838998917887673694960932994513953017874495728986791,13186771838998917887718625688914380057057525663189513753324⟩,⟨5933240233491325723661558531909002675219279980566478090118,5933240233491325724395542463323104874708730457851961012314⟩,⟨-3449092552227498116359383979246408352810913625672949769276,-3449092552227498116087791205140364048278822017167630934125⟩,⟨-5732295368739800791594726814468735269035024994774337355349,-5732295368739800790816780847051754237979515441941621030372⟩,⟨-4084497486501050089620413732797240502587234116312799856702,-4084497486501050089286525078919891297134701842248755305040⟩,⟨1816837537331601998644532897025081887844321895870440934077,1816837537331601999231516555207694346935938914386534154731⟩,⟨-2864587389555049963969756234295978228498202441175824011465,-2864587389555049963638650463959361121538643625669715550647⟩]
def UminusTableRow11 : Fin 8 → RI := ![⟨1556322378318005569851855883114737577539298860117244240545,1556322378318005569900584482821910699363783847684195237683⟩,⟨11514697505367411325558804175104672919509695846533831144269,11514697505367411325603734903086058462615120561170679705037⟩,⟨29483094027041843926398888078725777451484948146033703744445,29483094027041843927132872010139879650977393768075314629167⟩,⟨-17035744772417115907678104807626045559256603653733773840427,-17035744772417115907406512033520001254723368053532590839511⟩,⟨-28374036774096793792997108045642864855641453768411149439708,-28374036774096793792219162078225883824583069142295161866422⟩,⟨-20423444574799488751286508057406099618426813027697179749955,-20423444574799488750952619403528750412973194475963039290679⟩,⟨10152759310677486754072951675907048529329861893079437233986,10152759310677486754659935334089660988421882409582866532691⟩,⟨-15278057225182720120960619763425620899037262626433937111897,-15278057225182720120629513993089003792077275370856926831976⟩]
def UminusTableRow12 : Fin 8 → RI := ![⟨-185263742796052906159191114359001894910948671962048608855,-185263742796052906110462514651828773086557878145847147944⟩,⟨-2531719814973151977235253861929958837115435431623087852714,-2531719814973151977190323133948573294011029634840755256537⟩,⟨-3494928825715855148686685235333757471003855632967558453434,-3494928825715855147952701303919655271514716441059027396468⟩,⟨2026606578032126248856345643885620409297682070574747477987,2026606578032126249127938417991664713829653906223913817739⟩,⟨3370878633541750999608614513745933772656856133608223997055,3370878633541751000386560481162914803712068519451638465771⟩,⟨2412496691122974392683163525100616281246497166443199794538,2412496691122974393017052178977965486698918279297247983578⟩,⟨-1132965494950754166261917341778553871063849964142162858923,-1132965494950754165674933683595941411972271707573769641650⟩,⟨1744560188624703531886234631769900648989489006100622857081,1744560188624703532217340402106517755949009164845992163949⟩]
def UminusTableRow13 : Fin 8 → RI := ![⟨124140742138557986227674437754100053126948949257162826734,124140742138557986276403037461273174951335606566065406839⟩,⟨47353056433605278108049013437525741407343013110071536212115,47353056433605278108093944165507126950447814226962569691916⟩,⟨2281989923707939141990115729713628317458265038979204486954,2281989923707939142724099661127730516947253294764211579915⟩,⟨-1346787446586965674683612545472921732246276328162570458685,-1346787446586965674412019771366877427714361733063059698449⟩,⟨-2226840259090527858093890734814496779114376845385989747545,-2226840259090527857315944767397515748059313204782983360169⟩,⟨-1545486102052475292188479196180798961995451558970179765305,-1545486102052475291854590542303449756543088088401007967528⟩,⟨463302454207203147446782750161897192496136350116450585795,463302454207203148033766408344509651587689897529562442701⟩,⟨-885716873805907294444178337802142968000348246187491434788,-885716873805907294113072567465525861040857729669119645965⟩]
def UminusTableRow14 : Fin 8 → RI := ![⟨2297568829719906315033434626714748487038811194665517386,2297568829719906363762034333887870311417004048319970937⟩,⟨126968318245913944723611246906811195795128609655779552875,126968318245913944768541974888196738899420966397348509845⟩,⟨43509943628446947108280352944957701753860200689699584120,43509943628446947842264284359059901242559671948403317691⟩,⟨-25196316814097990467237466572397357731491071809763657445,-25196316814097990195644692466353053199687754253336045437⟩,⟨-41918407319059619554696406928319586876245031911355422700,-41918407319059618776750439511338555821453695465315317512⟩,⟨-30089308852163203742760672139453653753233599036580292127,-30089308852163203408872018262104448300970878025436463738⟩,⟨14790219134161784271840634394430477268874802872108580433,14790219134161784858824292577042936360395754163014582418⟩,⟨-22309415306833607060260234488484805629793713892565482567,-22309415306833606729154464151867698670332997128624546493⟩]
def UminusTableRow15 : Fin 8 → RI := ![⟨-8829835673175567671209911633336854517103146479124881425,-8829835673175567622481311926163732692724503487943034155⟩,⟨3054553700083492163390337725292409153734164592847198735950,3054553700083492163435268453273794696838460487030312287207⟩,⟨-166785527577837631042167903082595024458779095353597391339,-166785527577837630308183971668492824970063916402869690333⟩,⟨96708656781209728017545836041866653364326732918396032968,96708656781209728289138610147910957896136071790578870011⟩,⟨160834510410228191450695239423205064283947594934288402840,160834510410228192228641206840186095338753969828727530468⟩,⟨115167294805201838415327810676544727733493370717721707645,115167294805201838749216464553893933185761748049059124701⟩,⟨-54844956354756579170558295326373919245338536797452351594,-54844956354756578583574637143761460153815539828507970739⟩,⟨83875830682101870639339224590036491098152161499065880192,83875830682101870970444994926653598057615003174068576386⟩]
def UminusTableRow16 : Fin 8 → RI := ![⟨116641652523282447763028876298052148149039326473122774,116641652523282496491628583471173972527081976763311567⟩,⟨258339158545101022353171812141628089656037097927355003010,258339158545101022398102540123013632760328711422295456902⟩,⟨2200355634758740096105588831452306272833258631708009522,2200355634758740830089520245554505761527469557565978650⟩,⟨-1276954818782488251541703257672326272189925237559239726,-1276954818782487979948929151628021740388621683628309565⟩,⟨-2123058739936634615470550029604031191781134714206590013,-2123058739936633837524582612623000136994839272093966289⟩,⟨-1517975221623173557512290988200315004048465876117201990,-1517975221623173223623637110851109551787644399965438260⟩,⟨710479665535967495630437899254091515634576500643937670,710479665535968082614096081866550607154832461505047210⟩,⟨-1094606238799054436383046984510790576828913525846622444,-1094606238799054105277276647893683617368928972514132876⟩]
def UminusTableRow17 : Fin 8 → RI := ![⟨1297556321879793980076918315357860204422113353975679302,1297556321879794028805518022530982028800237412627412745⟩,⟨1763829024660808584531969285849287889268597699207185365673,1763829024660808584576900013830673432372890538126305197645⟩,⟨24547062462307270908092036400838394438407136103185853009,24547062462307271642075967814940593927104193839405767016⟩,⟨-14232365050924681814053605110228047802370205917529515499,-14232365050924681542460831004183743270567811522272709589⟩,⟨-23665988836747086756957273742616354582629267793833187522,-23665988836747085979011306325635323527840245829079337122⟩,⟨-16956366000001919616872153929836062422508828333502664385,-16956366000001919282983500052486856970246980452217562658⟩,⟨8202257913978211067937307093077398939611540188249082244,8202257913978211654920965275689858031132169788898873142⟩,⟨-12448609332364444713267679571107665097580923228293341824,-12448609332364444382161909234490558138120546801459338190⟩]
def UminusTableRow18 : Fin 8 → RI := ![⟨72568302938981161702078907172991055455424891212885566,72568302938981210430678614346112879833464505030431451⟩,⟨61152256241375864510834348994475315609108072525637472591,61152256241375864555765076975860858713399619751891471274⟩,⟨1371917155305950431084208368132376072158720020901648976,1371917155305951165068139782234575560852825343214526689⟩,⟨-795779591826148303521142640518043581032621995827167350,-795779591826148031928368534473739049231358956693773233⟩,⟨-1323057535441397530939386861343250549490078720932922063,-1323057535441396752993419444362219494703884313288029073⟩,⟨-947238143998555704379567097072524281226433216607741868,-947238143998555370490913219723318828965649685308823854⟩,⟨454178962426842375542920040720843418483316310465425796,454178962426842962526578223333302510003558693603742268⟩,⟨-691894851407310101614731218629191585862935479316509368,-691894851407309770508960882012084626402964825215874530⟩]
def UminusTableRow19 : Fin 8 → RI := ![⟨41254203243857259145660206597083836883932161987735233,41254203243857307874259913770205661261969619351578570⟩,⟨-1230501497197626462391082312843289076120052576320566216592,-1230501497197626462346151584861903533015760698129675830106⟩,⟨782532832421289906638007471399662731080773591480061741,782532832421290640621938885501862219774803806196061703⟩,⟨-453760911519304786311585585059823090636377251465664592,-453760911519304514718811479015518558835143010193859954⟩,⟨-754245937774099339019091782978054155046533222247959101,-754245937774098561073124365997023100260410704757178010⟩,⟨-540800746564120573296366088273694774600494506210185707,-540800746564120239407712210924489322339737996473106343⟩,⟨268098799759005056952812213691574272396757398556652371,268098799759005643936470396304033363916990061649285146⟩,⟨-401990006755773485944828255364363115201462938016924109,-401990006755773154839057918747256155741502289728833381⟩]
def UminusTable : Fin 20 → Fin 8 → RI := ![UminusTableRow0,UminusTableRow1,UminusTableRow2,UminusTableRow3,UminusTableRow4,UminusTableRow5,UminusTableRow6,UminusTableRow7,UminusTableRow8,UminusTableRow9,UminusTableRow10,UminusTableRow11,UminusTableRow12,UminusTableRow13,UminusTableRow14,UminusTableRow15,UminusTableRow16,UminusTableRow17,UminusTableRow18,UminusTableRow19]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamA
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def A1CachedBox (i : Fin 23) (j : Fin 8) : RI :=
  if hi : i.val<2 then gammaBox 0 ⟨i.val,by omega⟩ j
  else if h22 : i.val=22 then gammaBox 0 2 j
  else ((UplusTable ⟨i.val-2,by omega⟩ j).add (UminusTable ⟨i.val-2,by omega⟩ j)).divNat 2

def A1TableRow0 : Fin 8 → RI := ![⟨0,0⟩,⟨440000000000000000000000000000000000000000000000000000000000,440000000000000000000000000000000000000000000000000000000001⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩]
def A1TableRow1 : Fin 8 → RI := ![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩]
def A1TableRow2 : Fin 8 → RI := ![⟨2334811193136991920106216117946352746757559375111906588568023,2334811193136991920106264846546059919879567790738112707481252⟩,⟨-502855195900950112928301167646732372882827097346873814503948,-502855195900950112928266123710814082623176405452595167462244⟩,⟨2862420747308256208102330729759454915992059602825702929585764,2862420747308256208103064713690869018192098520087835352587911⟩,⟨-1438147319988235931915140091571350198470350564999832744096244,-1438147319988235931914868498797244154165643850741844046722698⟩,⟨-2550501917972612999143095420658180356331933940757772596049378,-2550501917972612999142317474690763375300523713198489488045951⟩,⟨-1630327743809697982874275597331051471599561028663744257856861,-1630327743809697982873941708677174122393981389100711547156049⟩,⟨586155197552085991438981290943838569526178177524749687544079,586155197552085991439568274602021181985308655252976673560208⟩,⟨-997827168687793368140573863616640005567534152768967010366614,-997827168687793368140242757846303388460538795370065238894743⟩]
def A1TableRow3 : Fin 8 → RI := ![⟨-1368197702022582478743274073047348733759424512004983929568060,-1368197702022582478743225344447641560636955378500624055538530⟩,⟨245502880355649889391583159501512197230085974528099895396159,245502880355649889391618203437430982344158884171373222340617⟩,⟨-2824178069308871199088039054541999475425241320424266915445227,-2824178069308871199087305070610585373224993082547737546182853⟩,⟨-985926349756351770737302077637713340873798303322293497109599,-985926349756351770737030484863607296569121174582027287246401⟩,⟨391778722476228081662645713923085960730615537067335993102248,391778722476228081663423659890502941762127029376218797932053⟩,⟨-1170987045947703601921363254162293350020509114516033210635435,-1170987045947703601921029365508416000814948590598898610957741⟩,⟨171102044386521996214664565745995510756803039964757226949100,171102044386521996215251549404178123215932429157964832975924⟩,⟨-747655553779946753791101878735910658573278180185139396498748,-747655553779946753790770772965574041466290365243387123857945⟩]
def A1TableRow4 : Fin 8 → RI := ![⟨884238840872349102227288359153279144750876321431987345146520,884238840872349102227337087752986317872871866802834759967192⟩,⟨-381207390812433741623653979345107255277546964256974094293196,-381207390812433741623618935409188887013769382013117504642843⟩,⟨19833925358270487768793029357648309417424161287565728205158613,19833925358270487768793763341579723519625908582666485083720539⟩,⟨-2920416601317559019609767685903978383550276890250778310028205,-2920416601317559019609496093129872339245355797900427906123050⟩,⟨-5434145370355183245620306471855922599906396314925763557623341,-5434145370355183245619528525888505618874462869003771637394226⟩,⟨-3456760256022402119331675495997704090982319204614054272729410,-3456760256022402119331341607343826741776549286640197105931561⟩,⟨1201579180696300309347273985337239287969634666409060173284697,1201579180696300309347860968995421900428813081317253802790327⟩,⟨-2068301289189462608751235870553597908224088007468931389500997,-2068301289189462608750904764783261291117052373155914757779418⟩]
def A1TableRow5 : Fin 8 → RI := ![⟨796998200130686708799752698163788433876520062376188606327599,796998200130686708799801426763495606998417359561802592099432⟩,⟨-202017063551439134649910029339638056054898175259977157541670,-202017063551439134649874985403719808423421701834839582506135⟩,⟨36052445823367622158306381160489053616935616951917582602631135,36052445823367622158307115144420467719139842244361547009509106⟩,⟨-21184449177382226689515663501236977738055959750652789946547500,-21184449177382226689515391908462871693749644225729406892586217⟩,⟨-12634237715948984049578188977312407288308170579532031343641966,-12634237715948984049577411031344990307274519164146914702760066⟩,⟨-8786752818929260601558203943106351961216617991995521869807706,-8786752818929260601557870054452474612010187861346339246686821⟩,⟨2605385711277216014794019245147620867785539335187733218459243,2605385711277216014794606228805803480244987587355001614973455⟩,⟨-4926899073280553066369382669814291859798768910270674110047196,-4926899073280553066369051564043955242691462390739324508730474⟩]
def A1TableRow6 : Fin 8 → RI := ![⟨-290323901179477583056518132890305629263788902206553993881218,-290323901179477583056469404290598456141911631124702129994729⟩,⟨111512901081606211546190690689842722261724360796851820215219,111512901081606211546225734625760988273388983720919833171831⟩,⟨-2306894402115591663383374722427045873925556851734417843523713,-2306894402115591663382640738495631771725647212933036237333293⟩,⟨1129889363016542370900297990497461038156204534363889399548326,1129889363016542370900569583271567082460885033362880588914046⟩,⟨18746091665670121217104479939585555486922858954795800946829336,18746091665670121217105257885552972467955379984597431945500531⟩,⟨1328617901330204127762603727731515103924911837561381556027314,1328617901330204127762937616385392453130494324805859346822608⟩,⟨-443198776923258354423437021564121536659444700963591396350995,-443198776923258354422850037905938924200312785619964055754198⟩,⟨779644599126693566534167313672793679048954002568669606191729,779644599126693566534498419443130296155950250762747616530575⟩]
def A1TableRow7 : Fin 8 → RI := ![⟨641041661782400627058677541241416785248205996051491297651154,641041661782400627058726269841123958370174571839526797466823⟩,⟨-253232372487467764457697816673857085960638699774007860826226,-253232372487467764457662772737938728808305811690239664358215⟩,⟨3128167641988515477502472226887026740720962710480863334891918,3128167641988515477503206210818440842921031916967706519994145⟩,⟨-1154525621691296033359707989968859744258772066296513331813149,-1154525621691296033359436397194753699954076240694005264893245⟩,⟨-24648090707136056054763904640722969231518739905298008696553883,-24648090707136056054763126694755552250484526799867118204696020⟩,⟨-18111063219098316506956411942060733079285320458771985406349646,-18111063219098316506956078053406855730078664103108819669202113⟩,⟨590467790536504857872262635779705434038948999763917575649637,590467790536504857872849619437888046498080573695588601280262⟩,⟨-924904272009578368776583259695867106033429027260903784638082,-924904272009578368776252153925530488926437645050884797891542⟩]
def A1TableRow8 : Fin 8 → RI := ![⟨5379548705089577229994175875848753118122623409245129849942,5379548705089577230042904475555926239947878310693583433919⟩,⟨-5795772920874768417135358431330246925779827857100616805996,-5795772920874768417100314495412025071857219027166250521316⟩,⟨50607698983830467885694759035852253389647072760447215664829,50607698983830467886428742967266355589145068475068742444285⟩,⟨-26288369936597147072017604872676611512914855638929952464481,-26288369936597147071746012098570567208379649774804615626723⟩,⟨-46350698051290200479977464578283918769528338393354295246577,-46350698051290200479199518610866937738464605308943669468404⟩,⟨-30595693489348038937068414488875254511390651557588863065148,-30595693489348038936734525834997905305935082837929457103191⟩,⟨16564884317220943824931455644569646065988688272428798988616297,16564884317220943824932042628227828678448352243228388147603690⟩,⟨-17411776853148646049780438561852956571059311275627499929340,-17411776853148646049449332791516339464098432570083401690148⟩]
def A1TableRow9 : Fin 8 → RI := ![⟨-14760205973315380335419330477530601095403689210559065504503,-14760205973315380335370601877823427973576590344223967713300⟩,⟨12801178977459032425561857426161837492566120388955175603086,12801178977459032425596901362080061017235271954651621860044⟩,⟨-115960914055436514228106299121070585310034765686271509024076,-115960914055436514227372315189656483110525042850956898108098⟩,⟨56477965116084084502672274897118611423603153131995250466800,56477965116084084502943867671224655728142383918642679128858⟩,⟨102856967238791402756943325070861658295139407216580377486538,102856967238791402757721271038278639326212219049319883495283⟩,⟨66379527747623796890496024513743783294790468477597395483683,66379527747623796890829913167621132500249312485159791313938⟩,⟨12771824087265070667517498834222018562778135261193176379243013,12771824087265070667518085817880201175237706430089357097151152⟩,⟨-16516461996473239462675774161320415161925991441957795288465053,-16516461996473239462675443055550078544818461930748762123284255⟩]
def A1TableRow10 : Fin 8 → RI := ![⟨461766665227964405813471041649034919706536905735301070831,461766665227964405862199641356208041530984512609755416725⟩,⟨2971997847332800775756269059069117363351685369147423180719,2971997847332800775791312994987338564071352344197990263637⟩,⟨4767333490717364241436086336001106746984156370384579988622,4767333490717364242170070267415208946473734183934180182413⟩,⟨-2546026657777518996166781298706995762128060333444155030369,-2546026657777518995895188524600951457595931602349161974986⟩,⟨-4428405852099833566247302474228693462016118053208916565294,-4428405852099833565469356506811712430960435808488910823586⟩,⟨-2948972044381192993310709186210484012010679887911406915546,-2948972044381192992976820532333134806558086255192710681423⟩,⟨897967617178694334439590464803821623138689617708881065537,897967617178694335026574122986434082230367247805026500226⟩,⟨-1654287041685421495206333626941924113912611129096095157556,-1654287041685421494875227856605307006952979525174749675129⟩]
def A1TableRow11 : Fin 8 → RI := ![⟨-5051987755713923863863655821277758652322860542780633859901,-5051987755713923863814927221570585530497622609520533451739⟩,⟨5837709692400586802346507230312036443172117961706014938600,5837709692400586802381551166230258288813713103414840279790⟩,⟨-44960604893141762831091654284756557375674368827552059822503,-44960604893141762830357670353342455176177460911453968817601⟩,⟨22932675269375407819348243213483206351630286555481997528027,22932675269375407819619835987589250656165069842946225409778⟩,⟨40802818131004106843432898721122285495504883661276149461742,40802818131004106844210844688539266526567393091460512151999⟩,⟨26747431996215512018477196760007342207292490003550144127747,26747431996215512018811085413884691412747597468671391167774⟩,⟨-8502258721128907738370165196135166347818441160865823932347,-8502258721128907737783181537952553888725809340035988131474⟩,⟨15307214253584354572274566782870847588833912164482992338432,15307214253584354572605672553207464695794558022835652124348⟩]
def A1TableRow12 : Fin 8 → RI := ![⟨311503146095564624074541841870016790014679397036896206865,311503146095564624123270441577189911839111706812353676937⟩,⟨6536085995694122827716116563691901439310107625925814345229,6536085995694122827751160499610122623616968011893738922430⟩,⟨2683787931635285301982254112145653168765521163553700457408,2683787931635285302716238043559755368254703588202617790316⟩,⟨-1353469873455472497923282609915617947838464499306948133788,-1353469873455472497651689835809573643306486852524557227869⟩,⟨-2421874524568408499385679742598406074185037990612309336201,-2421874524568408498607733775181425043129799459598000510728⟩,⟨-1580839544692712835360951413671844046951591455383758504087,-1580839544692712835027062759794494841499164281770074925490⟩,⟨506856392388835765932119872281376848056730106456348325682,506856392388835766519103530463989307148314057427136831470⟩,⟨-908038167456201703304705446945301404959215980985066549039,-908038167456201702973599676608684297999688505623333347149⟩]
def A1TableRow13 : Fin 8 → RI := ![⟨1461181632589890078522004665744198243874450185389739806851,1461181632589890078570733265451371365699075866975154976537⟩,⟨5501334526574012983721522538960541436358738062087039876708,5501334526574012983756566474878762779680356754473406413368⟩,⟨13100384492384958355648443904653400732305692005047733244491,13100384492384958356382427836067502931796780734342230111499⟩,⟨-6698584039882668723949708016567898579138794747143617750415,-6698584039882668723678115242461854274606123165538883894555⟩,⟨-11903814529952357526172580841247858649401887365253850181790,-11903814529952357525394634873830877618344826761487099309793⟩,⟨-7806151431230165001949653830068800331064374144563312715571,-7806151431230165001615765176191451125611274576576613696896⟩,⟨2469145041864225979331396690677149822103210865475574601403,2469145041864225979918380348859762281195078661495345695854⟩,⟨-4454728669440820173496108280971503249771966284699443456336,-4454728669440820173165002510634886142812132780192219143819⟩]
def A1TableRow14 : Fin 8 → RI := ![⟨-179505742463310140208226861262891100818168496614941933322,-179505742463310140159498261555717978993759497800418919501⟩,⟨-1233442877014404426037363090894435298106924352342455387171,-1233442877014404426002319154976214134609535419219136664941⟩,⟨-1569878765480740590476001252606085883492541898421814026937,-1569878765480740589742017321191983684003561761269817518571⟩,⟨795896788307947841971217029282815078060789887816791590724,795896788307947842242809803388859382592694709215365995833⟩,⟨1420406711327917654452131142965313400134258633555391479159,1420406711327917655230077110382294431189312561517225269330⟩,⟨928731232324786009468792638358823865103304165363467667423,928731232324786009802681292236173070555663532500748244739⟩,⟨-296132319864019478671820502881776122488527915901216567624,-296132319864019478084836844699163663396968551744261967176⟩,⟨532009792171653087358195612069885033439256526012924177870,532009792171653087689301382406502140398758322904911902816⟩]
def A1TableRow15 : Fin 8 → RI := ![⟨136365072646257986404924654293334302052482220648437303714,136365072646257986453653254000507423876885329795783338342⟩,⟨23648978178090804626564672372482012888079874194916170356442,23648978178090804626599716308400234051872603752898309148018⟩,⟨1077488329296026246494782824982097741638471098696418979221,1077488329296026247228766756396199941127360118753056292390⟩,⟨-525904196229927518730582970115412491486386865514711132020,-525904196229927518458990196009368186954516551377394512596⟩,⟨-956742715488876589053700545930723479636891562894072546217,-956742715488876588275754578513742448581936736109782641149⟩,⟨-617724705270106558776366917569750773730916667581714596316,-617724705270106558442478263692401568278594265788270829470⟩,⟨204645997978190116176709230532759645476684383109234738487,204645997978190116763692888715372104568224915997024730999⟩,⟨-360578911008727665591045742894260253808320331326415851991,-360578911008727665259939972557643146848842259874270018081⟩]
def A1TableRow16 : Fin 8 → RI := ![⟨2216945520135534974033918813224609825644740949374038226,2216945520135535022762518520397731650023156794005618376⟩,⟨63087195232875455409689541606665229958624741969631240390,63087195232875455444733477524886367882043631627011095697⟩,⟨19489337042698391233803302660212485417739518444939624145,19489337042698391967787234074314684906437003775303591858⟩,⟨-9898295877299954597978919834690013875366414606254449775,-9898295877299954326386145728645709343563930483118816118⟩,⟨-17649495291856428306311120393670097017269764195133805279,-17649495291856427528365152976689065962480390093657306367⟩,⟨-11544504710666940591978729038232131448255872965430845219,-11544504710666940258090075160882925995993919478510685788⟩,⟨3670321709798523800819955072239965266703469557087312078,3670321709798524387803613254852424358224194165305376822⟩,⟨-6602381623234230108031654892210688536925372356821906079,-6602381623234229776925884555593581577464883468316946867⟩]
def A1TableRow17 : Fin 8 → RI := ![⟨-8586291781736975836691384687374715378102075248584115867,-8586291781736975787962784980201593553722557272491858309⟩,⟨1528828859945704915732592188361418022393099807050003921426,1528828859945704915767636124279639161244122195401580398979⟩,⟨-74957294657410064799412509423190619835171935035881823490,-74957294657410064065428578009088420346464342365667708928⟩,⟨37977434521866401023178762832833791547680904631126045853,37977434521866401294771536938878096079487045815679940707⟩,⟨67798902963432302158227252908811485205589441256233666419,67798902963432302936173220325792516260388262142623956972⟩,⟨44314895544821682371770828371253627794673927290643692335,44314895544821682705659482248602833246939358392874495299⟩,⟨-14129099272691222410481116407980808615611430804752442609,-14129099272691221823497458225368349524089325051556506605⟩,⟨25380926671315222074069862044839974252599439417780101445,25380926671315222405175632381457081212061405092263474482⟩]
def A1TableRow18 : Fin 8 → RI := ![⟨114171642435074702255199710310701040801361212708359734,114171642435074750983799417483822865179415619342200465⟩,⟨129148804644277173185381098181662144848725650524875245031,129148804644277173220425034099883282468482014194822225541⟩,⟨991342680850158745993406525846984716895545544212936096,991342680850159479977337939949184205589656645282936340⟩,⟨-501318702185048445086579630038546108157879738250353394,-501318702185048173493805523994241576356618395191018874⟩,⟨-895823225650431911806039337463932523059511974268272641,-895823225650431133860071920482901468273316441425116141⟩,⟨-585165289195905132490693102877425649528703599774249184,-585165289195904798602039225528220197267921027719765009⟩,⟨186930255636307963823264177155411879216509049575284380,186930255636308550806922359767870970736753100494620440⟩,⟨-335463052641424106572590393642760581919308117720334154,-335463052641423775466820057025653622459335142602152247⟩]
def A1TableRow19 : Fin 8 → RI := ![⟨1267087529877188736084750975254701173077587740639119104,1267087529877188784813350682427822997455841637621509618⟩,⟨881685269286960548651614699806628186418462802914507907697,881685269286960548686658635724849324202016823649563887084⟩,⟨11038710185326184870334348368336540157875167181590900303,11038710185326185604318279782438739646571109094209927032⟩,⟨-5588643717787293454875889168550601919168238696872428341,-5588643717787293183283115062506297387366314863598124019⟩,⟨-9980845738209723513808875314589285653826002798499111236,-9980845738209722735862907897608254599038091272069097770⟩,⟨-6521095788466562836669228333175722126044180666847304348,-6521095788466562502780574455826516673782766333740141260⟩,⟨2078980719759514672444006924837383840793991077424677355,2078980719759515259427665107449842932314491256107493923⟩,⟨-3734183919383159225103433078574153298259600845904241691,-3734183919383158893997662741957046338799353301167215416⟩]
def A1TableRow20 : Fin 8 → RI := ![⟨71090654806898215734497875801809488713399530195118047,71090654806898264463097582974931313091446465544232371⟩,⟨30563224066599934247886904987765238455594995444923045138,30563224066599934282930840905986376067217720390617374461⟩,⟨617698987641717954076377504296467426577936220588815069,617698987641718688060308918398666915271979259915120259⟩,⟨-312436776893550469794370986200107063825166816792266585,-312436776893550198201596880155802532023930084733820451⟩,⟨-558244902004923168115765072207806751439778800161042233,-558244902004922390169797655226775696653646533642199531⟩,⟨-364625106912535469405819324710513814918055332848182422,-364625106912535135517165447361308362657296043265052753⟩,⟨116357375076787971569057467803353050902668589860634134,116357375076788558552715650415812142422903689908231405⟩,⟨-208894410098638176871569766562966687841322245814123106,-208894410098637845765799429945859728381358801521628835⟩]
def A1TableRow21 : Fin 8 → RI := ![⟨40692345560819294783589911378467209563171508978946123,40692345560819343512189618551589033941213192649766770⟩,⟨-615258136866386151786522390101080103732784733895799476503,-615258136866386151751478454182858966123846414694477156282⟩,⟨352562110669135132662539590313899654404569033366726659,352562110669135866646471004416099143098563746469062309⟩,⟨-178140450407190905695785974206333642779741817957955619,-178140450407190634103011868162029110978522576054108633⟩,⟨-318462719515523119127314831585486839292425006561343534,-318462719515522341181347414604455784506337830992611093⟩,⟨-207872697289742584114961215853450521087470526687185210,-207872697289742250226307338504245068826727837147213290⟩,⟨66297259161262704999866014357710740484837057739347162,66297259161263291983524196970169832005065685628586224⟩,⟨-119021939024244833525104986818768446379208241038303722,-119021939024244502419334650201661486919251700688498549⟩]
def A1TableRow22 : Fin 8 → RI := ![⟨0,0⟩,⟨-6000000000000000000000000000000000000000000000000000000001,-6000000000000000000000000000000000000000000000000000000000⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩]
def A1Table : Fin 23 → Fin 8 → RI := ![A1TableRow0,A1TableRow1,A1TableRow2,A1TableRow3,A1TableRow4,A1TableRow5,A1TableRow6,A1TableRow7,A1TableRow8,A1TableRow9,A1TableRow10,A1TableRow11,A1TableRow12,A1TableRow13,A1TableRow14,A1TableRow15,A1TableRow16,A1TableRow17,A1TableRow18,A1TableRow19,A1TableRow20,A1TableRow21,A1TableRow22]
def A2CachedBox (i : Fin 23) (j : Fin 8) : RI :=
  if hi : i.val<2 then gammaBox 1 ⟨i.val,by omega⟩ j
  else if h22 : i.val=22 then gammaBox 1 2 j
  else ((UplusTable ⟨i.val-2,by omega⟩ j).sub (UminusTable ⟨i.val-2,by omega⟩ j)).divNat 2

def A2TableRow0 : Fin 8 → RI := ![⟨0,0⟩,⟨440000000000000000000000000000000000000000000000000000000000,440000000000000000000000000000000000000000000000000000000001⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩]
def A2TableRow1 : Fin 8 → RI := ![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩]
def A2TableRow2 : Fin 8 → RI := ![⟨-348117845997684557036932933184663969753935485720667042190171,-348117845997684557036884204584956796631927070094460923276942⟩,⟨-318624573689874250588878739968021597903380063328868434610739,-318624573689874250588843696032103307643729371434589787569035⟩,⟨-2376876697382806615816626514385507223782823426212195992748382,-2376876697382806615815892530454093121582784508950063569746235⟩,⟨2077360307883677403926348349476890715844820762805376794730739,2077360307883677403926619942250996760149527477063365492104285⟩,⟨2779338469936599347747073585187102786481928464635639631409491,2779338469936599347747851531154519767513338692194922739412918⟩,⟨1915933858076537964513872903557235726362703510435941751723755,1915933858076537964514206792211113075568283149998974462424567⟩,⟨-549226571445940395165182382806036174835229411134878844090554,-549226571445940395164595399147853562376098933406651858074426⟩,⟨1040079977175304336571257193153099200538083491865163167457042,1040079977175304336571588298923435817645078849264064938928913⟩]
def A2TableRow3 : Fin 8 → RI := ![⟨-2693464918909213527217540752014376973071613798509897708987397,-2693464918909213527217492023414669799949144665005537834957868⟩,⟨1366181486171011039774815442338843465211578356165442169904327,1366181486171011039774850486274762250325651265808715496848785⟩,⟨-7493516746212608921858274299824677366921986437994149538051992,-7493516746212608921857540315893263264721738200117620168789618⟩,⟨1725987005522378846345111509498945411226678877064597960199569,1725987005522378846345383102273051455531356005804864170062767⟩,⟨4816048331951717645173383538910674984500864900541460419780941,4816048331951717645174161484878091965532376392850343224610746⟩,⟨1628411122880932336957065550147551956111304993714137324975095,1628411122880932336957399438801429305316865517631271924652790⟩,⟨-718905668325710977698428842127134282475791057945317204193308,-718905668325710977697841858468951670016661668752109598166484⟩,⟨821547513312292526618981272942489574239512791216936534127427,821547513312292526619312378712826191346500606158688806768231⟩]
def A2TableRow4 : Fin 8 → RI := ![⟨151484508464639445954264273012767288228706813525298545713874,151484508464639445954313001612474461350702358896145960534546⟩,⟨-28705578999244064734006109684634642633168043751308630369089,-28705578999244064733971065748716274369390461507452040718736⟩,⟨-6180422230756159437791268607118321821295539410840593658542007,-6180422230756159437790534623186907719093792115739836779980081⟩,⟨4623428251450322127917746252042105869355873161794257348537850,4623428251450322127918017844816211913660794254144607752443006⟩,⟨6856280537159148975965611368957761866436919729522597947160633,6856280537159148975966389314925178847468853175444589867389748⟩,⟨4777954289953602616741052177681131086209849123658502593400165,4777954289953602616741386066335008435415619041632359760198014⟩,⟨-1042990118834715749977243497296944628899160176271147182998313,-1042990118834715749976656513638762016439981761362953553492683⟩,⟨2207048924278195914710411851687847896463680036618364607906669,2207048924278195914710742957458184513570715670931381239628248⟩]
def A2TableRow5 : Fin 8 → RI := ![⟨-1088426342974276964494922159186790301180154680404645031220063,-1088426342974276964494873430587083128058257383219031045448230⟩,⟨196819758218590044728835418496013862570450584880533896635849,196819758218590044728870462431932110201927058305671471671384⟩,⟨-20960774380859797933839562546835950702243219531405732078311779,-20960774380859797933838828562904536600038994238961767671433809⟩,⟨11464343593289254766637852777685305813553967112369779526084659,11464343593289254766638124370459411857860282637293162580045942⟩,⟨19875554465930611261508788251229899361248762180949731542646862,19875554465930611261509566197197316342282413596334848183528762⟩,⟨14708361833187171398512986649941774348556001582039724359309961,14708361833187171398513320538595651697762431712688906982430846⟩,⟨-5886906939726724411912010785122213808228993418452289656369286,-5886906939726724411911423801464031195769545166285021259855074⟩,⟨10055580644515702647960010757953320534648083259520864330628972,10055580644515702647960341863723657151755389779052213931945694⟩]
def A2TableRow6 : Fin 8 → RI := ![⟨-15591800100143012856131606395233214658183207546170335001459,-15591800100143012856082877795526041536305936464318471114970⟩,⟨7826508524886249255253247631035235355020712292772165316854,7826508524886249255288291566953501366685335216840178273466⟩,⟨2576618751267593414397194554065926812969245975451844194746961,2576618751267593414397928537997340915169155614253225800937381⟩,⟨-1766013985922587296071678059925963500414580148527269065189729,-1766013985922587296071406467151857456109899649528277875824009⟩,⟨-2728193546267511773045041571501552233906057722034275428695162,-2728193546267511773044263625534135252873536692232644430023967⟩,⟨-1958766476049238191206799317486113896713890947433162428287965,-1958766476049238191206465428832236547508308460188684637492672⟩,⟨549212375299349699970356625085667550149048422957290400949472,549212375299349699970943608743850162608180338300917741546269⟩,⟨-1065889558960425965558973197935210118305736322636850362682163,-1065889558960425965558642092164873501198740074442772352343317⟩]
def A2TableRow7 : Fin 8 → RI := ![⟨345195449914456818594282536086378423291202918606503363894169,345195449914456818594331264686085596413171494394538863709837⟩,⟨-107081219087331483647036080080979547075932121517731092367954,-107081219087331483647001036145061189923599233433962895899944⟩,⟨-1462381229520670460293192412973584951418923046675418799987704,-1462381229520670460292458429042170849218853840188575614885478⟩,⟨1948040859415973131871597136311588707672043842510126465486902,1948040859415973131871868729085694751976739668112634532406806⟩,⟨2350169478796078336183101590662254420903302844062448311149671,2350169478796078336183879536629671401937515949493338803007534⟩,⟨1330542082094976387796694137350249289706632884770548527307956,1330542082094976387797028026004126638913289240433714264455489⟩,⟨959420000255151128121156503337747591028885564399064753070806,959420000255151128121743486995930203488017138330735778701431⟩,⟨-745741645627828959869872146095597323928574106974735646505729,-745741645627828959869541040325260706821582724764716659759189⟩]
def A2TableRow8 : Fin 8 → RI := ![⟨-774025604201228034631145853086026409892381201327947188903,-774025604201228034582417253378853288067126299879493604926⟩,⟨4008913728773696142512777110186756629066028707827651342371,4008913728773696142547821046104978482988637537762017627051⟩,⟨-65286737780989606458251771682377641720957085776637260042334,-65286737780989606457517787750963539521459090062015733262879⟩,⟨40435644278892854798450682991013852277227973728359487545841,40435644278892854798722275765119896581763179592484824383599⟩,⟨65109383061232554409804411955211999932708620108179043521824,65109383061232554410582357922628980963772353192589669299997⟩,⟨49756359557205913752325626968177896723310755474273149355706,49756359557205913752659515622055245928766324193932555317663⟩,⟨-27996116591037746811418409033341473097212882655295398229487,-27996116591037746810831425375158860637548911855706239242094⟩,⟨41106610686872190154120412074895717266524432576265375221915,41106610686872190154451517845232334373485311281809473461107⟩]
def A2TableRow9 : Fin 8 → RI := ![⟨-1359095327247434633248239827944298067871883775126461712814,-1359095327247434633199511228237124946044784908791363921611⟩,⟨-6786102145329862844370865377754330761369636705186650643094,-6786102145329862844335821441836107236700485139490204386136⟩,⟨128778732988978974597023528710777529424870878404665558094588,128778732988978974597757512642191631624380601239980169010566⟩,⟨-88237759205576067681703390999020622037914751462627492333819,-88237759205576067681431798224914577733375520675980063671761⟩,⟨-136239694018071355923261829696313595381795444806691441948696,-136239694018071355922483883728896614350722632973951935939951⟩,⟨-99020702569219206957812259534638127788878289409080158620199,-99020702569219206957478370880760778583419445401517762789944⟩,⟨27778300589093717615526161007154849065508725472059387729401,27778300589093717616113144665337461525079894368240105637541⟩,⟨-55287210115553158610699752688877233727244021097330513950335,-55287210115553158610368646918540616619714509888297348769537⟩]
def A2TableRow10 : Fin 8 → RI := ![⟨-127146465770053167365298772332621251825294490733468819074,-127146465770053167316570172625448130000846883859014473180⟩,⟨-3103960971301936222475474278222030558935498779672134010843,-3103960971301936222440430342303809358215831804621566927925⟩,⟨-6553795607734263397518122973595888798160881801977455409582,-6553795607734263396784139042181786598671303988427855215791⟩,⟨3889980119191375869866862792422765256429043792349294825282,3889980119191375870138455566528809560961172523444287880664⟩,⟨6367046111866674342228964638062351049120532263711523327321,6367046111866674343006910605479332080176214508431529069029⟩,⟨5007406830365683249607503485596336245555232280371386268682,5007406830365683249941392139473685451007825913090082502805⟩,⟨-3757921968411603392725936339821897703862348984556990772264,-3757921968411603392138952681639285244770671354460845337575⟩,⟨4973532976801410411174539372596408407750748108854526221800,4973532976801410411505645142933025514710379712775871704227⟩]
def A2TableRow11 : Fin 8 → RI := ![⟨304472284311386181511315908181959424291433777736757977560,304472284311386181560044507889132546116671710996858385722⟩,⟨-4043536824228269608412099098601692220696035541207873148806,-4043536824228269608377055162683470375054440399499047807616⟩,⟨55796273549873761550315636524484228367518684824563795564721,55796273549873761551049620455898330567015592740661886569622⟩,⟨-35416899692185618616946129623713868677489036082124043938540,-35416899692185618616674536849607824372954252794659816056789⟩,⟨-56359911920019198110462587048386329164891165525667892964539,-56359911920019198109684641080969348133828656095483530274282⟩,⟨-42818526164615999318939746434822096565393059908152952347504,-42818526164615999318605857780944747359937952443031705307477⟩,⟨23241673657269804215459112492789826673618731635153497135779,23241673657269804216046096150972439132711363455983332936652⟩,⟨-34360179193786586718679140336456930143480540308840994409165,-34360179193786586718348034566120313036519894450488334623249⟩]
def A2TableRow12 : Fin 8 → RI := ![⟨-4268659340852187328851335307625534562816683996874408652,-4268659340852187280122735600452412738384374221416938580⟩,⟨-6650685843304795059980043761231785846195164142916807024828,-6650685843304795059944999825313564661888303756948882447628⟩,⟨-3249452301856040422046296385470400606198484055655519093808,-3249452301856040421312312454056298406709301631006601760900⟩,⟨2095622678772025618300304982277768252706403322113342217913,2095622678772025618571897756383812557238380968895733123832⟩,⟨3310420844171392291820074088161838679322232227745669856660,3310420844171392292598020055578819710377470758759978682133⟩,⟨2503657941808337254092517992186721852909376523897019076784,2503657941808337254426406646064071058361803697510702655381⟩,⟨-1309981144942766233005904853835011269333400298672139218722,-1309981144942766232418921195652398810241816347701350712934⟩,⟨1956549222098848260499497902182368270059207052437703232017,1956549222098848260830603672518985377018734527799436433907⟩]
def A2TableRow13 : Fin 8 → RI := ![⟨-95140745728115491354215517224125894577091168510979932263,-95140745728115491305486917516952772752465486925564762577⟩,⟨-6013362978793398341859747000134824254703670141765215547945,-6013362978793398341824703064216602911382051449378849011285⟩,⟨-16382709534656885571117436139779427818925478952006775942315,-16382709534656885570383452208365325619434390222712279075307⟩,⟨10337160732534447183592600404005124827851191106489564589554,10337160732534447183864193178111169132383862688094298445414⟩,⟨16470222244144436266435554220686515690710374090099305471275,16470222244144436267213500188103496721767434693866056343272⟩,⟨12617293143569323749169909900398624684635629607266796804746,12617293143569323749503798554275973890088729175253495823421⟩,⟨-7683614268813260775035046814321204936772661285855577281936,-7683614268813260774448063156138592477680793489835806187484⟩,⟨10823328555741899947298958597285809095785302713945988515600,10823328555741899947630064367622426202745136218453212828118⟩]
def A2TableRow14 : Fin 8 → RI := ![⟨5758000332742765926599953242524233180584778439005945078,5758000332742765975328552949697355004993777253528958898⟩,⟨1298276937958747551175425407044830767456308180889466167454,1298276937958747551210469342963051930953697114012784889685⟩,⟨1925050060235114557843692017020620487766744138591478898014,1925050060235114558577675948434722687255724275743475406380⟩,⟨-1230709789724178407020925001655827483502878100582539057139,-1230709789724178406749332227549783178970973279183964652030⟩,⟨-1950471922213833345545456354489110888050203692974539752254,-1950471922213833344767510387072129856995149765012705962083⟩,⟨-1483765458798188383381315213680467018869403557506756221635,-1483765458798188383047426559803117813417044190369475644319⟩,⟨836833175086734687296605009805471519029532919956749682662,836833175086734687883588667988083978121092284113704283110⟩,⟨-1212550396453050444693591904868324169029992559460383332645,-1212550396453050444362486134531707062070490762568395607699⟩]
def A2TableRow15 : Fin 8 → RI := ![⟨12224330507700000152885916685647688013339942736823186928,12224330507700000201614516392820809837743051884169221556⟩,⟨-23704078255514473481506806429034421290815539473600882595574,-23704078255514473481471762493116200127022809915618743803998⟩,⟨-1204501594411912895862324870438581675564288068175289054213,-1204501594411912895128340939024479476075399048118651741045⟩,⟨820883250357038155817233188304487088493932165098103946547,820883250357038156088825962410531393025802479235420565971⟩,⟨1270097543601651268651217205175282783949953462190414007640,1270097543601651269429163172592263815004908288974703912708⟩,⟨927761396782368733245167951672373585538353156103879270100,927761396782368733579056605549722790990675557897323036946⟩,⟨-258656456229013031563565348720443776565228740713771775761,-258656456229013030976581690537831317473688207825981783249⟩,⟨525137962797179628687579709739574160712282656601889688385,525137962797179629018685480076191267671760728054035522295⟩]
def A2TableRow16 : Fin 8 → RI := ![⟨-80623309584371365363815667076699573583166672118705935,-80623309584371316635215959903577749204750827487125785⟩,⟨-63881123013038489336387069290838737388650046056932790970,-63881123013038489301343133372617599465231156399552935663⟩,⟨-24020606585748556241469015991796316080470417874111826760,-24020606585748555507485084577694116591772932543747859048⟩,⟨15298020936798035733462159684685191590222998425295401666,15298020936798036005054933790729496122025482548431035323⟩,⟨24268912027203190859412302826158974331579599493201564827,24268912027203191637358270243140005386368973594678063739⟩,⟨18544804141496262983837616162546919578846365565577532714,18544804141496263317726270039896125031108319052497692145⟩,⟨-11119897424363260764512508413496741547931808960474269348,-11119897424363260177528850230884282456411084352256204603⟩,⟨15707033683599376786675694427965563613137983153773108451,15707033683599377117781464764582670572598472042278067663⟩]
def A2TableRow17 : Fin 8 → RI := ![⟨243543891438591810154227092375578226811749734949841923,243543891438591858882826799548700051191267711042099481⟩,⟨-1525724840137787247680210900921683902893212732888751590153,-1525724840137787247645166965003462764042190344537175112599⟩,⟨91828232920427565875763427952353304879249570842351717346,91828232920427566609747359366455504367957163512565831908⟩,⟨-58731222259343327130163460262055014082550497723361405636,-58731222259343326858570686156010709550744356538807510782⟩,⟨-93035607446795889681440970222884094605761341125274300235,-93035607446795888903495002805903063550962520238884009682⟩,⟨-70852399260380156210501309243965702664953632092746723838,-70852399260380155876612655366616497212688200990515920874⟩,⟨40715857082065356466585349827086881083965607508227718558,40715857082065357053569008009699340175487713261423654561⟩,⟨-58494904010786648730822247713505070325284142918787126844,-58494904010786648399716477376887963365822177244303753807⟩]
def A2TableRow18 : Fin 8 → RI := ![⟨-2470010088207769872129019573912019536699438909857436,-2470010088207721143529312400790195158645032276016705⟩,⟨-129190353900823849190256077950658716359457254149949984925,-129190353900823849155212142032437578739700890480003004415⟩,⟨-1209012953908581717104148012656421300284818550424057990,-1209012953908580983120216598554221811590707449354057746⟩,⟨775636116597439670658736574611627898131393722343421251,775636116597439942251510680655932429932655065402755772⟩,⟨1227235514286202314691526983649583141328475018882005510,1227235514286203092637494400630614196114670551725162010⟩,⟨932809932427268258077270946648286628389351538267070941,932809932427268591965924823997492080650134110321555116⟩,⟨-523549409899659825299002813404909182178195431499208060,-523549409899659238315344630792450090657951380579872000⟩,⟨759143186157630164257571422559476515179613131460043506,759143186157630495363341759176583474639586106578225413⟩]
def A2TableRow19 : Fin 8 → RI := ![⟨-30468792002605268356467193689719943533587642662426920,-30468792002605219627867486516598119155333745680036405⟩,⟨-882143755373848035902819950033352474402281315752237373962,-882143755373848035867776014115131336618727295017181394575⟩,⟨-13508352276981086404749653739552954024880497789704909709,-13508352276981085670765722325450754536184555877085882980⟩,⟨8643721333137388223381328888655293617300770023028684203,8643721333137388494974102994699598149102693856302988525⟩,⟨13685143098537362854175414719536553401408754012957151086,13685143098537363632121382136517584456196665539387164552⟩,⟨10435270211535356613258598657985737570333723726012809174,10435270211535356947147252535334943022595138059119972262⟩,⟨-6123277194218696688985129259546244644577863911149300338,-6123277194218696102001471076933785553057363732466483770⟩,⟨8714425412981285322611361324224958319591134168972098316,8714425412981285653717131660842065279051381713709124591⟩]
def A2TableRow20 : Fin 8 → RI := ![⟨-1477648132082970331880884957742478931045167926540462,-1477648132082921603281177784620654552998232577426137⟩,⟨-30589032174775930285412807997402848705658850693841426795,-30589032174775930250368872079181711094036125748147097471⟩,⟨-754218167664232843999796570887008389927836461469272763,-754218167664232110015865156784808901233793422142967573⟩,⟨483342814932597697930384601295784251306823659468203707,483342814932597969523158707340088783108060391526649841⟩,⟨764812633436473973850638080644928270657202716949433335,764812633436474751796605497625959325443334983468276037⟩,⟨582613037086020068029420833687407740177986118110100439,582613037086020401918074711036613192438745407693230108⟩,⟨-337821587350054697465691664223719913340768912173949898,-337821587350054110482033481611260821820533812126352627⟩,⟨483000441308671759190276283757671418291627906452068843,483000441308672090296046620374778377751591350744563114⟩]
def A2TableRow21 : Fin 8 → RI := ![⟨-561857683037988726370148805177539509779381690710778,-561857683037939997770441632055715131737698019890132⟩,⟨615243360331240310582094558751516200835121903329321546846,615243360331240310617138494669737338444060222530643867067⟩,⟨-429970721752155140967433588136862821023219665471335063,-429970721752154406983502174034663332329224952368999413⟩,⟨275620461112113744819412557831337181956018312871806654,275620461112114016412186663875641713757237554775653640⟩,⟨435783218258575830918793242902051788361046956941225021,435783218258576608864760659883082843147134132509957462⟩,⟨332928049274377822237077933745641527382645724654460815,332928049274378156125731811094846979643388414194432735⟩,⟨-201801540597742645444775290640093077672036672363621596,-201801540597742058461117108027633986151808044474382534⟩,⟨282968067731528486866838100237041189092274372834575023,282968067731528817972608436854148148552230913184380196⟩]
def A2TableRow22 : Fin 8 → RI := ![⟨0,0⟩,⟨6000000000000000000000000000000000000000000000000000000000,6000000000000000000000000000000000000000000000000000000001⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩]
def A2Table : Fin 23 → Fin 8 → RI := ![A2TableRow0,A2TableRow1,A2TableRow2,A2TableRow3,A2TableRow4,A2TableRow5,A2TableRow6,A2TableRow7,A2TableRow8,A2TableRow9,A2TableRow10,A2TableRow11,A2TableRow12,A2TableRow13,A2TableRow14,A2TableRow15,A2TableRow16,A2TableRow17,A2TableRow18,A2TableRow19,A2TableRow20,A2TableRow21,A2TableRow22]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Polytope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def rowLower (row : Fin 8 → ℝ) : ℝ :=
  row 1 + Z*min 0 (row 0) + DeltaStar*min 0 (-row 2) +
    Wstar*min 0 (row 3+Z*row 2) + Ustar*min 0 (min (row 5) (row 5+Z*row 4)) +
    Pstar*(min 0 (row 6)+min 0 (row 7))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_PolytopeInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def ZBox : RI := (RI.point 391).divNat 1000
def WstarBox : RI := (RI.point 61).divNat 10000
def DeltaStarBox : RI := (RI.point 18).divNat 100000
def UstarBox : RI := (RI.point 48).divNat 100000
def PstarBox : RI := (RI.point 3).divNat 10000000
end AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction
open Bernstein

def bernsteinRows (n : ℕ) (a : Fin (n+1) → Fin 8 → ℝ)
    (d : Fin (n+1)) (r : Fin 8) : ℝ :=
  ∑ l : Fin (n+1), ((d.val.choose l.val:ℝ)/(n.choose l.val:ℝ))*a l r
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def A1AbsNumerators : Fin 23 → ℤ := ![440000000000000000000000000000000000000000000000000000000001,0,506577505428133277725966475437659806584283989084294867243756,302774817060523226008427819375140853579223338747880481900281,387457243193308200069636705474069589107674040706856315643116,258333268405700108415766990932050848493543155072123131754165,117474530319733233171216765313719887584341491266670302584683,267114984143389787040856194121942352815924686473407109538211,5867927195876975597649742368649551994382111264673349312243,12944987069239917597719635291971760783647267965868133639386,3152548882827220012091733562729852804240191957738578973085,5898957614123196260712065177997627471962474307313637191910,6657883877874406312434089197997863018342852833751586438255,6072657285660172563745517157184353641597379776984290457798,1303629711157254650064623395194376583059664981077272453465,23702296982889290892760129759822299069220097287315935232418,63954022032344962578190938607445857412929993400725542075,1528929237228086938660276170299412803686943689405875186396,129193445812548364138952264914196165139128456923010956072,882180701134836745429375233669978135228974937424221274178,30591020547536644027372479626744269335380118685516276292,615258605672107878598391040390489397249836382026702415079,6000000000000000000000000000000000000000000000000000000001]
def A2AbsNumerators : Fin 23 → ℤ := ![440000000000000000000000000000000000000000000000000000000001,0,454738816242940346172438066397940051888021288814472588570751,1369216078939506848957928799800550912466197839167609454312517,48680193988305558232813101436011536089534122008575612020381,231324924966709612485096049689756405659716613972249598433513,7826673288598839060198282850036124521734117670941668548790,107081442809825171995724041042623375755129300089963184788649,4147722486977679401690787571499073784427933809462713435724,7644904754493197779312564244221933208689987342527361008971,3153676366794617534396323915984987414968500084253615686199,4167684378427698269131479896681917875739511139690945267191,6652355282101411748055494535108523580712606266379674520253,6050565315457372142957477777883501775844793820451394458134,1300528567138802498727229172242983993185843117246599946727,23704078333111410350210715898104025906948672443169504809706,63912650063055205849222550570418250970943528605273893134,1525932097780078207513875441918362091078110909680030049043,129191319831833161398174027987012959980568858284022368633,882155670508504212828356335401623932764076341893877556233,30589610036542050931828982663128825282036863356731377769,615244335165763033627719424276730057858090662671075964848,6000000000000000000000000000000000000000000000000000000001]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_TargetEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate AtomicTriangular.L1Kernel

def finiteTargetEnvelope : ℝ := ∑ i : Fin 6, targetEnvelope H (finiteNode ⟨i.val+4,by omega⟩)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def targetEnvt52 : RI := ⟨67,68⟩
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ConcreteSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.Schur

def finiteResidualBound : ℝ := 82/10^9
def tailResidualBound (e : Fin 2) : ℝ := 1/10^26+6*beta+(if e.val=0 then 0 else (12/1000)*(13/10^8))
def tailErrorBound (e : Fin 2) : ℝ := if e.val=0 then 1801/10^12 else 3361/10^12
def finiteErrorBound (e : Fin 2) : ℝ := if e.val=0 then 11804/10^9 else 6124/10^9
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_Taylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def finiteSpectrum (side q : Fin 2) (j : Fin 31) (r : Fin 8) : ℂ :=
  if q.val=0 then fourierCoeff j*(Acoefficient side 22 r:ℂ)
  else ∑ col : Fin 22, finiteColumn ⟨col.val,by omega⟩ j*(Acoefficient side ⟨col.val,by omega⟩ r:ℂ)

def taylorWave (q branch : Fin 2) (m : ℤ) (l : ℕ) (t : ℝ) : ℂ :=
  taylorAmplitude q branch t * exp (taylorPhase q branch t*m) *
    (taylorPhase q branch t)^(l+2) / ((l+2).factorial:ℂ)

def taylorRow (side : Fin 2) (m : ℤ) (y : ℝ) (l : ℕ) (r : Fin 8) : ℝ :=
  y^l*(∑ q : Fin 2, ∑ j : Fin 31,
    (finiteSpectrum side q j r*taylorWave q 0 m l (frequency j) +
    finiteSpectrum (otherSide side) q j r*taylorWave q 1 m l (frequency j))).re

def finiteTaylor (side : Fin 2) (m : ℤ) (y : ℝ) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  ∑ l ∈ Finset.range 21, (∑ r : Fin 8, taylorRow side m y l r*e r)*τ^l

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def nearNode (n : Fin 7) : ℤ := finiteNode ⟨n.val,by omega⟩

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def curvatureWave (q br : Fin 2) (s t : ℝ) : ℝ :=
  ‖taylorPhase q br t‖^2 * ‖taylorAmplitude q br t‖ * Real.exp ((taylorPhase q br t).re*s)
def curvaturePoint : Fin 5 → ℝ := ![0,1,2,29/2,23]
def rawCurvatureColumn (br : Fin 2) (s : ℝ) (c : Fin 22) : ℝ :=
  ∑ j : Fin 31, curvatureWave 1 br s (frequency j)*‖finiteColumn ⟨c.val,by omega⟩ j‖
def rawConstantCurvature (s : ℝ) : ℝ :=
  (∑ j : Fin 31, curvatureWave 0 1 s (frequency j)*‖fourierCoeff j‖)/2
def rawTailCurvature (i : Fin 5) : ℝ :=
  60*(curvatureWave 0 0 (curvaturePoint i) (frequency 30)+
    curvatureWave 0 1 (curvaturePoint i) (frequency (if i.val=0 then 15 else 30)))
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def amplitudeNormBox (q br : Fin 2) (j : Fin 31) : RI :=
  if br.val=0 then RI.point 1 else if q.val=0 then lambdaNorm0 j else lambdaNorm1 j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_FiniteTaylorIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def finiteJJet (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ r : Fin 8, (e r:ℂ) * (∑ q : Fin 2, ∑ j : Fin 31,
    (finiteSpectrum side q j r * finiteWaveJet q 0 (frequency j) k s +
    finiteSpectrum (otherSide side) q j r * finiteWaveJet q 1 (frequency j) k s))
def finiteJ (side : Fin 2) (e : Fin 8 → ℝ) (s : ℝ) : ℝ := (finiteJJet side e 0 s).re
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

def finiteCurvatureCap (br : Fin 2) : Fin 5 → ℝ :=
  if br.val=0 then ![828/10,44164/1000,23561/1000,9147/1000000,43834/1000000000]
  else ![291294/100,45877/1000,3893/1000,635/10000000000,167/100000000000000]
def finiteCurvatureEnvelope : Fin 5 → ℝ := ![1510,46,14,465/100000,23/1000000]
def tailCurvatureEnvelope : Fin 5 → ℝ := ![26500,1160,800,800,800]
def tailCurvatureCap (br : Fin 2) (i : Fin 5) : ℝ :=
  curvatureWave 0 br (curvaturePoint i) (if br.val=1 ∧ i.val=0 then 0 else 5/6)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineBarrierBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set Filter
namespace AtomicTriangular.Construction

def sinePolynomial (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040+x^9/362880-x^11/39916800

def piLow : ℚ := 314159265358979/100000000000000
def piHigh : ℚ := 15707963267949/5000000000000

def sineLower (d : ℚ) : ℚ :=
  let l:=piLow*d/36
  let u:=piHigh*d/36
  2*(l-u^3/6+l^5/120-u^7/5040+l^9/362880-u^11/39916800)

def vanishingLower (v : ℚ) : ℚ := 2*(piLow/36-(piHigh/36)^3*v^2/6)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def localCenter (u : Fin 30) : ℤ := residue ⟨u.val/2,by omega⟩
def localNeighbor : Fin 30 → ℤ := ![-5,1,0,3,1,4,3,7,4,9,7,12,9,13,12,16,13,19,16,21,19,25,21,27,25,28,27,31,28,36]
def localPivot (u : Fin 30) : Fin 15 := ⟨u.val/2,by omega⟩
def localHalf (u : Fin 30) : ℚ := ((localNeighbor u:ℚ)-localCenter u)/2
def localPhase (u : Fin 30) (j : Fin 15) : ℤ := (localCenter u-residue j)%36
def localShift (u : Fin 30) (j : Fin 15) : ℤ := (localCenter u-residue j)/36
def cellLo (u : Fin 30) (k : Fin 100) : ℚ := min (localHalf u*k.val/100) (localHalf u*(k.val+1)/100)
def cellHi (u : Fin 30) (k : Fin 100) : ℚ := max (localHalf u*k.val/100) (localHalf u*(k.val+1)/100)
def cellMagnitude (u : Fin 30) (k : Fin 100) : ℚ := max |cellLo u k| |cellHi u k|
def cellSeparation (u : Fin 30) (k : Fin 100) (j : Fin 15) : ℚ :=
  min ((localPhase u j:ℚ)+cellLo u k) (36-((localPhase u j:ℚ)+cellHi u k))
def cellFactor (u : Fin 30) (k : Fin 100) (j : Fin 15) : ℚ :=
  if j=localPivot u then vanishingLower (cellMagnitude u k) else sineLower (cellSeparation u k j)
def cellBarrier (u : Fin 30) : ℚ := if 16≤u.val ∧ u.val≤21 then 3 else 27/500
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

def realP (s : ℝ) : ℝ := ∏ a : Fin 15,(2*Real.sin (Real.pi*(s-residue a)/36))^2
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FarCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def transformedP (s : ℝ) : ℝ := (spectralPCLM (waveFunctionJet 0 1 0 s)).re

def sideConstant (side : Fin 2) : ℝ := if side.val=0 then -(3/500) else 3/500
def actualJ0 (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z ≤ Z) : ℝ → ℝ :=
  pairJ (coefficientInput 0 (actualTrigonometric side z hz hzB) (actualTail side z hz hzB))
    (coefficientInput 0 (actualTrigonometric (otherSide side) z hz hzB) (actualTail (otherSide side) z hz hzB))+
      sideConstant (otherSide side) • transformedP
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Envelope
open Complex

def expDeleted (w : ℂ) (m v : ℝ) : ℂ :=
  if v=0 then exp (w*(m:ℂ))*w^2/2
  else (exp (w*((m+v:ℝ):ℂ))-exp (w*(m:ℂ))-(v:ℂ)*w*exp (w*(m:ℂ)))/(v:ℂ)^2
def expDeletedTaylor (w : ℂ) (m v : ℝ) : ℂ :=
  exp (w*(m:ℂ))*w^2*∑ j ∈ Finset.range 21, (w*(v:ℂ))^j/((j+2).factorial:ℂ)
end AtomicTriangular.Envelope
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

def deletedSecond (f : ℝ → ℝ) (m s : ℝ) : ℝ :=
  if s=m then iteratedDeriv 2 f m/2 else (f s-f m-deriv f m*(s-m))/(s-m)^2

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex
namespace AtomicTriangular.Construction

def complexDeleted (F : ℕ → ℝ → ℂ) (m v : ℝ) : ℂ :=
  if v=0 then F 2 m/2 else (F 0 (m+v)-F 0 m-(v:ℂ)*F 1 m)/(v:ℂ)^2
def complexTaylor (F : ℕ → ℝ → ℂ) (m v : ℝ) : ℂ :=
  ∑ j ∈ Finset.range 21,F (j+2) m*(v:ℂ)^j/((j+2).factorial:ℂ)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def ATable (side : Fin 2) (i : Fin 23) (r : Fin 8) : RI := if side.val=0 then A1Table i r else A2Table i r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def nearDisplacementNum : Fin 7 → Fin 2 → ℤ :=
  ![![-2,2],![-2,1],![-1,3],![-3,2],![-2,3],![-3,1],![-1,3]]
def nearDisplacement (n : Fin 7) (y : Fin 2) : ℝ := nearDisplacementNum n y / 2
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def bernsteinRowsBox (n : ℕ) (a : Fin (n+1) → Fin 8 → RI)
    (d : Fin (n+1)) (r : Fin 8) : RI :=
  RI.sum (fun l : Fin (n+1) => ((RI.point (d.val.choose l.val)).divNat (n.choose l.val)).mul (a l r))
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction

def remainderWave (q br : Fin 2) (m Y t : ℝ) : ℝ :=
  curvatureWave q br m t * (Y*‖taylorPhase q br t‖)^21 / (23).factorial /
    (1-Y*‖taylorPhase q br t‖/24)
def nearRadius : Fin 7 → ℝ := ![1,1,3/2,3/2,3/2,3/2,3/2]
def rawRemainderColumn (br : Fin 2) (n : Fin 7) (c : Fin 22) : ℝ :=
  ∑ j : Fin 31, remainderWave 1 br (nearNode n) (nearRadius n) (frequency j)*
    ‖finiteColumn ⟨c.val,by omega⟩ j‖
def rawRemainderConstant (br : Fin 2) (n : Fin 7) : ℝ :=
  ∑ j : Fin 31, remainderWave 0 br (nearNode n) (nearRadius n) (frequency j)*‖fourierCoeff j‖
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def complexError (F : ℕ → ℝ → ℂ) (m v : ℝ) : ℂ := complexDeleted F m v-complexTaylor F m v
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
def nearBase (n : Fin 7) (y : Fin 2) : Fin 5 := if n.val=0 then (if y.val=0 then 0 else 1) else 2
def nearError (n : Fin 7) (y : Fin 2) : ℝ := if n.val=0 then (if y.val=0 then 18/1000 else 3/1000) else 16/100000
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Exceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def freezeParameter (z : ℝ) (e : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun r => if r.val=0 then z else e r

def frozenTaylorRow (z : ℝ) (l : ℕ) (r : Fin 8) : ℝ :=
  (if r.val=0 then 0 else -taylorRow 0 1 1 l r) -
    (if r.val=1 then z*taylorRow 0 1 1 l 0 else 0)

def frozenTaylor (z : ℝ) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  ∑ l : Fin 21, (∑ r : Fin 8, frozenTaylorRow z l.val r*e r)*τ^l.val

def exceptionalWeight (test : Fin 4) (endpt : Fin 2) (j : Fin 3) : ℝ :=
  if test.val=0 then (if endpt.val=0 ∧ j.val=1 then 1 else 0)
  else if test.val=1 then (if endpt.val=0 then
    (if j.val=1 then 4*Z/3 else if j.val=2 then 2/3 else 0)
    else if j.val=2 then 1/3 else 0)
  else if test.val=2 then (if endpt.val=0 then
    (if j.val=0 then 2*Z^2 else if j.val=1 then 4*Z/3 else 1/3)
    else (if j.val=1 then 4*Z/3 else if j.val=2 then 2/3 else 0))
  else (if endpt.val=1 then (if j.val=0 then 6*Z^2 else if j.val=1 then 4*Z else 1) else 0)

def exceptionalOffset (test : Fin 4) (l : ℕ) (r : Fin 8) : ℝ :=
  if r.val=1 then (if l=0 then Q 1*(if test.val=0 then 1 else test.val*Z)
    else if l=1 ∧ test.val≠0 then Q 1 else 0) else 0

def exceptionalRow (test : Fin 4) (l : Fin 23) (r : Fin 8) : ℝ :=
  exceptionalOffset test l.val r +
    ∑ ep : Fin 2, ∑ j : Fin 3, if j.val≤l.val ∧ l.val-j.val<21 then
      exceptionalWeight test ep j * frozenTaylorRow (if ep.val=0 then 0 else Z) (l.val-j.val) r else 0

def exceptionalValue (test : Fin 4) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  let A := frozenTaylor 0 e τ
  let D := frozenTaylor Z e τ
  if test.val=0 then Q 1+τ*A
  else if test.val=1 then Q 1*(τ+Z)+(2*(τ^2+2*Z*τ)*A+τ^2*D)/3
  else if test.val=2 then Q 1*(τ+2*Z)+((τ^2+4*Z*τ+6*Z^2)*A+2*(τ^2+2*Z*τ)*D)/3
  else Q 1*(τ+3*Z)+(τ^2+4*Z*τ+6*Z^2)*D
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_GaussianDeleted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction

def pade0 (x : ℝ) := Real.exp (-x)*(6+4*x+x^2)-6+2*x
def pade1 (x : ℝ) := 2-Real.exp (-x)*(2+2*x+x^2)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def ordinaryOffset (n : Fin 7) (r : Fin 8) : ℝ :=
  if n.val=0 ∧ r.val=1 then Q 1/(2*Z)
  else if n.val=1 ∧ r.val=3 then (4/5:ℝ)*Q 1 else 0
def ordinarySignRow (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) : ℝ :=
  if side.val=0 then (if l.val=0 then ordinaryOffset n r else 0) -
    taylorRow side (nearNode n) (nearDisplacement n y) l.val r
  else taylorRow side (nearNode n) (nearDisplacement n y) l.val r
def ordinarySignValue (side : Fin 2) (n : Fin 7) (y : Fin 2) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  if side.val=0 then (∑ r : Fin 8, ordinaryOffset n r*e r) -
    finiteTaylor side (nearNode n) (nearDisplacement n y) e τ
  else finiteTaylor side (nearNode n) (nearDisplacement n y) e τ
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_0_0_0 : Fin 8 → RI := ![⟨310627079097082178063118274154035356158754197590155965641161,310627079097082178072923986867761465837071218935033349773874⟩,
  ⟨61361665963453900494401710627341928601141818699614960098580,61361665963453900501453642552264341024144355064419692935381⟩,
  ⟨483169025561007177361993851881727100628698146249150156641056,483169025561007177509694290870217463910395993362159738691862⟩,
  ⟨-696790370593526751623657129039898498341987982476803480155054,-696790370593526751569004199663519520613599376826935327342018⟩,
  ⟨-776720069120214335967184999696320074536128050804987504525835,-776720069120214335810638029134608472751440717954793103515573⟩,
  ⟨-400251014916968479706971544397951880890928862379172327314029,-400251014916968479639782742773764022416132335844181590740192⟩,
  ⟨-18843983881606130606751317837848826285292126167312083414147,-18843983881606130488631914581623292223121193130096760516798⟩,
  ⟨-16573469530357650255368719055320262986766741782515978285787,-16573469530357650188739920338582793346555232044366137412869⟩]
def bs0_0_0_1 : Fin 8 → RI := ![⟨307386530583974313127929646448657371554320501170871700572289,307386530583974313138282272410128927905154336036177642930114⟩,
  ⟨63134228528158602019036857775108177427013747618957266637598,63134228528158602026482110930672207168798579957533172146282⟩,
  ⟨466329923776456458249585742683314402894912123049495056064335,466329923776456458405524167949614389532949307183006001166681⟩,
  ⟨-677043807031929914749593103539655572883734125226514472504007,-677043807031929914691891909138915202283099304389792059678735⟩,
  ⟨-755910852276029570762717827096591009400267029332243679917692,-755910852276029570597439455300484322993110823858948602934646⟩,
  ⟨-395966149352147586398914255961399815069518190491191997935824,-395966149352147586327978001522676937812854705597480333732133⟩,
  ⟨-18436520922738292788921861039883947976649941467332157496991,-18436520922738292664214352630885228431957023936641998234066⟩,
  ⟨-18104774859644739235455242016958061698261201333103040351424,-18104774859644739165110224626113990361451165756847236976434⟩]
def bs0_0_0_2 : Fin 8 → RI := ![⟨302885338891488801347860147076612141271682527641966101801812,302885338891488801358818265581511106665997289342643558275912⟩,
  ⟨65746007095227041794404453298390189405602344064447374929022,65746007095227041802285155902851740994335625011419334983005⟩,
  ⟨440719580601325908158082794351069505192550006995442542520139,440719580601325908323141567834624571704082709767014983401038⟩,
  ⟨-650028927851710462164614043616706423910595503766475044929389,-650028927851710462103538087770259392183265125655354090525422⟩,
  ⟨-725317066566218044571931538789081851077699369812384562140297,-725317066566218044396986554668473532773288697153272422780250⟩,
  ⟨-386899299845780433422109263913485790329697867282927880756382,-386899299845780433347024170979096183744238760149119427450177⟩,
  ⟨-18161111232240138794860356969876913628342802745994096289243,-18161111232240138662859098479358548596712514564337269997288⟩,
  ⟨-19011687441163983578079994054668492394959844092995079885839,-19011687441163983503620717764090731243355911105592120313766⟩]
def bs0_0_0_3 : Fin 8 → RI := ![⟨297126477945779123065922329998211798044194393264078114771763,297126477945779123077554038210073961509694817318527093966736⟩,
  ⟨69191525053300754037682411403321471032844996959337287754289,69191525053300754046047536598720930441252400891914179573939⟩,
  ⟨405901681336904015782172097968502660482306354590533822982550,405901681336904015957376946329025010667364391956711837483874⟩,
  ⟨-615556669914529830892247103644178898616811313444156283926922,-615556669914529830827416841327810967403485282805834993840474⟩,
  ⟨-684534010654767096931733268553765519141885216770249648496934,-684534010654767096746034509454992604221217227660469873620434⟩,
  ⟨-372777774875727814051677331743621259224908443134648436009751,-372777774875727813971976798145504089930124325130104789565951⟩,
  ⟨-18042527251358496397073300202593593340307404242469968024904,-18042527251358496256957994671503105167815086541213964387543⟩,
  ⟨-19221696475765024778372610034886784733468263857435483427562,-19221696475765024699336361696135398140831972848076900168387⟩]
def bs0_0_0_4 : Fin 8 → RI := ![⟨290151111824837164472900798961076739962775021777329290145869,290151111824837164485285574420045336283532300269730598470950⟩,
  ⟨73440581648522435800950731456496514863031350052697982506979,73440581648522435809857436761009065886338955555376628664339⟩,
  ⟨361736434787389326572755730131278882125949150632194688869501,361736434787389326759303799146072330145882533685101952429888⟩,
  ⟨-573666119926612240374734312070226598306178621364451300173051,-573666119926612240305706768814346031014219835239842418886872⟩,
  ⟨-633475368194540570207839778923588660711326448260170657757848,-633475368194540570010118395911363247684834844773974400252573⟩,
  ⟨-353502214732989163908823684494196146230988518088456898134851,-353502214732989163823963129656346653436677915941080986521367⟩,
  ⟨-18083526020396711699609800928482846093579262031856193150197,-18083526020396711550423063627298936464014805760826473690477⟩,
  ⟨-18714488073988925144734432816944255132224458740183813146280,-18714488073988925060581170805368162837690129431331926039448⟩]
def bs0_0_0_5 : Fin 8 → RI := ![⟨282047165553255889705387331838244623749325320909598778816918,282047165553255889718618335038236023493143508034166621872701⟩,
  ⟨78432531418754066503978894669426327563479615885161302445901,78432531418754066513494177911805419748225071995937500095714⟩,
  ⟨308463642560764230964786645227421854280365595457804114423043,308463642560764231164081182804039831584839802981407602790685⟩,
  ⟨-524682168921177728179034197449177737611550756173834391957102,-524682168921177728105290135739577589967157556267802346935069⟩,
  ⟨-572459272050659061614015561533212357825450735183483935624563,-572459272050659061402784259035686534652397557128009624894518⟩,
  ⟨-329196491636263868449550961803975481428462331483788643575713,-329196491636263868358892049470063429791008459732591555675525⟩,
  ⟨-18257100894995452374841047535594028260398805063105419249587,-18257100894995452215460669169589886231761170278109925951349⟩,
  ⟨-17539149027129820512026162026341491319881000277780274040419,-17539149027129820422122870468559282481262348308550787159576⟩]
def bs0_0_0_6 : Fin 8 → RI := ![⟨272957845218062957564510271452869334462305194642881952207351,272957845218062957578697219260070229449853796791980058096161⟩,
  ⟨84070480652958649200497640250170196633193860466271934585363,84070480652958649210700406033678006980308110718093148560424⟩,
  ⟨246780615590253934737842185332882525890187627228932213165780,246780615590253934951535822929440335955319946110977609675078⟩,
  ⟨-469271039779274716422860271392851706255506495004506037967836,-469271039779274716343788175441346639434936877670393684909175⟩,
  ⟨-502289855706319719150363633838028223474709681100977623667729,-502289855706319718923870795881776611933906114468968533844517⟩,
  ⟨-300253731005778078256711295353958545193452259935124766479023,-300253731005778078159502244906761276594283406081286545543108⟩,
  ⟨-18499988816195163859309251128091160938171081795123507523032,-18499988816195163688413584700264862686499109353913541020573⟩,
  ⟨-15828733274292113230349092008825327781482191381489149909423,-15828733274292113133950256202689762344342024912887425759280⟩]
def bs0_0_0_7 : Fin 8 → RI := ![⟨263089352876434123019885330046716563353407823356648755542623,263089352876434123035158111061766232224687003793560917451636⟩,
  ⟨90215883961097138609527237147922340573318400064419201608236,90215883961097138620510896894685494781294558836644847646575⟩,
  ⟨177903782308727016026327540221031658669870720741896731057672,177903782308727016256376749936374489751701267335573897219024⟩,
  ⟨-408487252607038863260920051511804402177243407342212442384345,-408487252607038863175795976743997091881868110262551505270500⟩,
  ⟨-424323489186275190593747872433245602471747909668951882317912,-424323489186275190349919843840604164202060095850768809679686⟩,
  ⟨-267371132946993530727337447402220915452760804839627850398249,-267371132946993530622688261380530547518995874951656495377400⟩,
  ⟨-18709254664978409503572333088449136242304477913758853894868,-18709254664978409319596743324870468133658750746531746056163⟩,
  ⟨-13808470867047528643460549990002992691614358847746990519687,-13808470867047528539683590394340343580751441769081829618192⟩]
def bs0_0_0_8 : Fin 8 → RI := ![⟨252716797516580049142589368917961381435888462702674400839539,252716797516580049159102626332641742214157913717502403012523⟩,
  ⟨96684191414251616207309074117305273896810960101021331970756,96684191414251616219184841901503714544857025454187205071719⟩,
  ⟨103599379245850318853626362498523199739148752089124108468268,103599379245850319102360487235019078154829015735120575081193⟩,
  ⟨-343803609950630811005513787909252617944184483514070767008502,-343803609950630810913475818043757972198921285585359752605669⟩,
  ⟨-340505565992688621686109821717440261191453295720397529385422,-340505565992688621422477743375676572203287289426932254775122⟩,
  ⟨-231564014303474719458695488442385451990573978074134982258050,-231564014303474719345546550779816770640831264226875385278072⟩,
  ⟨-18744391847765766041263459092624039113024026063137701895314,-18744391847765765842345117449865638199431843259778512452359⟩,
  ⟨-11792697569153005835053904370315809985252649651181428926276,-11792697569153005722848036570042690850977149731320158009006⟩]
def bs0_0_0_9 : Fin 8 → RI := ![⟨242187096734971079523249445564154290039569769368165805975384,242187096734971079541188427547606147680201895878043017218010⟩,
  ⟨103242335772864670729315566332539480477354645371842877709334,103242335772864670742216666277312663191651502408248797407525⟩,
  ⟨26165742659027543357586957560291333146794024835956824481175,26165742659027543627796333594581772154821900376165236374233⟩,
  ⟨-277114157135804714212325059635058457202265219588975983451650,-277114157135804714112340699084851625550542979300955948099439⟩,
  ⟨-253360957173296764064825383091696738435208819866473753130304,-253360957173296763778431791272667870751448966534472740131464⟩,
  ⟨-194147609815847955849444184303353452058041573879425566019507,-194147609815847955726526173447328827477909844000477998019588⟩,
  ⟨-18437944310217195980420935137546535562904808581262944561114,-18437944310217195764328346176856765557000718336331437480057⟩,
  ⟨-10164524161643403680254494658069297201683303334652246307620,-10164524161643403558360976597921449252601308627633409806950⟩]
def bs0_0_0_10 : Fin 8 → RI := ![⟨231917587069649104894575734483780564163145465259384219349239,231917587069649104914163815161679828589604241823824168940331⟩,
  ⟨109608896961160315280870930977601659904897084239907696067551,109608896961160315294958006085055332044231338178818539050430⟩,
  ⟨-51651235521969515196970083884865090182429439836551671901221,-51651235521969514901920840702446346403279301991736081698725⟩,
  ⟨-210699586059439069752648111554939023094467961731616993793669,-210699586059439069643472366644324250498540030410807827157639⟩,
  ⟨-165920381264281847283625940936451485416516783065633298235051,-165920381264281846970904695809708610226292118918838585934089⟩,
  ⟨-156674535997992642366362241282084187384636482851454540191053,-156674535997992642232144596399959364192941398281248761349353⟩,
  ⟨-17617969134211507152203138863012153540278142567051678422211,-17617969134211506916245542697823906926293279638465963040258⟩,
  ⟨-9331768209328486403852803639955752072372952210179125944260,-9331768209328486270753831352689241665885377327431400843551⟩]
def bs0_0_0_11 : Fin 8 → RI := ![⟨222389275862505107982726776089254750766669249813291585579777,222389275862505108004235194140678118249918094403382732504297⟩,
  ⟨115457636738138527433186577496074777515770420235034981078313,115457636738138527448654693311792872839098684315340649672628⟩,
  ⟨-126824632675355486069125808495449252104695283914169520405455,-126824632675355485745151113247296318765101575259805131114845⟩,
  ⟨-147146566671652014860561768388470807590245855329729518933284,-147146566671652014740682868499294700571630017022143051053397⟩,
  ⟨-81568223533455177674883344123371256387727914302442328026157,-81568223533455177331504154281684984918447154280727909273306⟩,
  ⟨-120817951833982944070286134537847653304543758645427651476018,-120817951833982943922910326593491128799112313256680982666810⟩,
  ⟨-16145360736484134392959771405182486955651699413555886853826,-16145360736484134133869832773897472464293268529841037360843⟩,
  ⟨-9653481836423715521892720626507312988715947034172375469540,-9653481836423715375745255479391007786707554939453945288586⟩]
def bs0_0_0_12 : Fin 8 → RI := ![⟨214134445900978110397022635909593207424888925773571989506883,214134445900978110420783200980764214697930438890038541256457⟩,
  ⟨120424611203361622038841492111342640489221889986162510839202,120424611203361622055929274740905916737217597122855420122589⟩,
  ⟨-196298709969457380030678491478820610383273530624430742141580,-196298709969457379672780397372309810486317316278395279018079⟩,
  ⟨-89219284517976686167732715980500298234866040327725648924540,-89219284517976686035301293332012700805901216977147606392985⟩,
  ⟨-3808566337258873608710886463488074708968945840253226658338,-3808566337258873229376452625038257215578342750517179886228⟩,
  ⟨-88197887385168669613472802910773682922397841341249511522976,-88197887385168669450665270242299079802821828025785096388717⟩,
  ⟨-13967532245991131031768094433097811712795092522052594484790,-13967532245991130745548841513917895315098810417395231461678⟩,
  ⟨-11334786575755900010981114082694341634939983894172784950061,-11334786575755899849530544016764425009045272501417958855278⟩]
def bs0_0_0_13 : Fin 8 → RI := ![⟨207720110375667340460482614770065624559638856793136519024739,207720110375667340486904421679621632971418964429230647429497⟩,
  ⟨124118027413399604247782168351062130440757654535779818126080,124118027413399604266783824742629748176217047950663339323864⟩,
  ⟨-257304593785845165059810159725989327267766494474594807821707,-257304593785845164661826597152963679284916766923100652151449⟩,
  ⟨-39696733284161496639892966003140880681760994659806804823757,-39696733284161496492628897683105145844759251131293511660058⟩,
  ⟨64028466881721001195841144690382919764700703663398555239406,64028466881721001617661969867527818356252092190037700489401⟩,
  ⟨-60165093642031536591262946262291260511616487202352848823371,-60165093642031536410220568748544376958659533228221518708470⟩,
  ⟨-11186177299933226267128528841834408378423926649407088191695,-11186177299933225948852014297612340881806048740538737962860⟩,
  ⟨-14295741347509888230812188479502043329410800955466464752682,-14295741347509888051278756721987178920710227606244494502662⟩]
def bs0_0_0_14 : Fin 8 → RI := ![⟨203732325549760321190309176386636267505748435734344687399924,203732325549760321219900785244938209401971625091672308597318⟩,
  ⟨126128090724018488106761572526837101242418679428618935189705,126128090724018488128042841651447349454863995463778355271444⟩,
  ⟨-307666601813675441310714603325235772725564401584899586353626,-307666601813675440864985287537005280970360538151136891469864⟩,
  ⟨-1218972096134289794441349716753998532138185679677635451375,-1218972096134289629510135000522775153502018650454797037485⟩,
  ⟨119068624748540882640143515579704976868716759648957164050815,119068624748540883112569830313542376738211192629555433137081⟩,
  ⟨-37589725350175742468615548247058815438280430017659421438375,-37589725350175742265853668998701281115728108099911703135479⟩,
  ⟨-8129156945021594807768704079315205297432708706075997831864,-8129156945021594451308823820062871574245492794005839870751⟩,
  ⟨-18035967635734973498159710493016743851425892717961144994994,-18035967635734973297087803951950013897811561883670922794181⟩]
def bs0_0_0_15 : Fin 8 → RI := ![⟨202772748513475740960928034186294885039150123943192682697380,202772748513475740994327186142789226689330172157194566451572⟩,
  ⟨126030730688198496835285001668812625195229001509889692719884,126030730688198496859304525065659222663402205721567524884585⟩,
  ⟨-345934932173368546289187240726136811100735285541606460014139,-345934932173368545786106072657539775150108798043185411681599⟩,
  ⟨23761002524323609266558849782707285331889764632565732908169,23761002524323609452711712542836401183862541726323432512088⟩,
  ⟨159003263195837142400744193882037290525805104372434475706877,159003263195837142933957455436943524574604772261289971562766⟩,
  ⟨-20761750638836218237344965474009265149241699477107156227669,-20761750638836218008493778356544259762022627806830828357580⟩,
  ⟨-5402291577639704016004303431669327833393398609709116975071,-5402291577639703613678841364529157018612755230321594395118⟩,
  ⟨-21546102149517072061095010551792162034479114150737664623739,-21546102149517071834151244401234111662485167522275615020153⟩]
def bs0_0_0_16 : Fin 8 → RI := ![⟨205489927255940409501380187374908117192236894124689975338182,205489927255940409539394034698425902823465016733031269902014⟩,
  ⟨123373100264144955131035365486410240898834241160195302996033,123373100264144955158373619355379997193238371489101964782819⟩,
  ⟨-371022255188590763404748729065506532032379803637527390698441,-371022255188590762832157821991198426549822812329029197720634⟩,
  ⟨32730949992691482921442678113276636526024765380851762909572,32730949992691483133315917079947517784593006356655111438305⟩,
  ⟨181712758334537770756772569892028735442930794580830692942996,181712758334537771363658862752388872054717621401316356774561⟩,
  ⟨-9613016814145129843017857437486525940738496079656640421839,-9613016814145129582546750322708525974122452094605181534196⟩,
  ⟨-3871642154995102989914807933188785287030417218642423871418,-3871642154995102532000825285248264671721993593286198284943⟩,
  ⟨-23368475360928512266448194238342017880497398604266463196003,-23368475360928512008148052704117938858115305928226919617123⟩]
def bs0_0_0_17 : Fin 8 → RI := ![⟨212686684934545655237408866471690928825934178976013352883310,212686684934545655281069073175849288721858982444291894592907⟩,
  ⟨117617252216938108955855256732141826887700715081887387628229,117617252216938108987254178411841856670585235681299970365380⟩,
  ⟨-380754809106207969263607161441081113195167335784108454261245,-380754809106207968605966877178123845655566980675746366293063⟩,
  ⟨22234720686084502572168087037967986009058396692837500927128,22234720686084502815511764661161598869183843944471532436956⟩,
  ⟨183830447579018693380874665560436339531652309380351981850462,183830447579018694077904375987081150689241312733710084944020⟩,
  ⟨-4644701052786397619829561104045312134199576215151580198010,-4644701052786397320669566058348890534238414777289994310734⟩,
  ⟨-4483563037316501393884653675539682946384492152323068208715,-4483563037316500867954748051960264609282804660420915912037⟩,
  ⟨-21996866358803261749541494402069793030164569761790809828158,-21996866358803261452874927739126366209059798623879358214154⟩]
def bs0_0_0_18 : Fin 8 → RI := ![⟨225576901096659368430996045793330415860706468235718503997319,225576901096659368481635253129492467268557982637469375111589⟩,
  ⟨107994693468977112209163045949072955907557222626546198578574,107994693468977112245581025274089200326262937645770022669954⟩,
  ⟨-368301835862865020238020062575452174265627537909063776441654,-368301835862865019475257235247646129072114988033008265117767⟩,
  ⟨-14253394689981444009253147850965956287693869990210348020921,-14253394689981443727011448251894042608258573656996790357148⟩,
  ⟨157241248538862378515975089909943619000121518498730909255959,157241248538862379324423667920836514115464313589347391807118⟩,
  ⟨-9234459608548283203796759475229956887135356161584615934078,-9234459608548282856816610748834946127719797186609689819385⟩,
  ⟨-7756065545159191236761929950095663126667543202954538565427,-7756065545159190626763133659710067666998793969801006796629⟩,
  ⟨-16952847695840129434563642828412476090710091003597876142778,-16952847695840129090475492243702056781981457306651746986779⟩]
def bs0_0_0_19 : Fin 8 → RI := ![⟨246319986986855690968060398201684512486075573234895275274672,246319986986855691027419971675694362154425500639275028687834⟩,
  ⟨93174273061954560340361569888024338945835715209619330151468,93174273061954560383050937144095462331038164544467993031087⟩,
  ⟨-314691184744437140958573959789157043166630954344313443413309,-314691184744437140064458935606218296466674356316544477719706⟩,
  ⟨-90733645563947231135443357291684645473300112151485551024908,-90733645563947230804597994854409313129334129738315166888032⟩,
  ⟨81778712232808028931176110565964840834961677505662659996474,81778712232808029878844237510764037592577360832318723377358⟩,
  ⟨-34488341914584978935757661568375493836417178452801502145326,-34488341914584978529025512398321898667987538242561248049502⟩,
  ⟨-12647985172860227992513106440010679113173698526197994965327,-12647985172860227277468968262077775134714815952694018684940⟩,
  ⟨-11128284892737034760923632004805958905086585149908330686541,-11128284892737034357581499877407236739700174635678576973914⟩]
def bs0_0_0_20 : Fin 8 → RI := ![⟨279061558171982991316153950474900920308910128753814042897484,279061558171982991386538652812934157640942237965238946356203⟩,
  ⟨70508490556503696222738190971374375306413972141574339691172,70508490556503696273356452382068276232693660289554078166252⟩,
  ⟨-174280308232196320089808079086764122699788135598186755296349,-174280308232196319029624924964304316163015814088059009349505⟩,
  ⟨-237169410736907650489661981061374306736231455495457298013968,-237169410736907650097367175151120752628754957226246284530413⟩,
  ⟨-88904094722514730616254271996575478090549444547426318230880,-88904094722514729492571348984577882489965940873562613455061⟩,
  ⟨-108668244788934808832119642075273763915716685157765135637761,-108668244788934808349843244607071139228260650741668743526390⟩,
  ⟨-14282971056554751289227343578727581044707388372855383887811,-14282971056554750441374741561549130227090721382430585065733⟩,
  ⟨-15433852026085439955437983632532469990055533396390293209284,-15433852026085439477181246786844355369157275288869194385198⟩]
def bs0_0_0 : Fin 21 → Fin 8 → RI := ![bs0_0_0_0,bs0_0_0_1,bs0_0_0_2,bs0_0_0_3,bs0_0_0_4,bs0_0_0_5,bs0_0_0_6,bs0_0_0_7,bs0_0_0_8,bs0_0_0_9,bs0_0_0_10,bs0_0_0_11,bs0_0_0_12,bs0_0_0_13,bs0_0_0_14,bs0_0_0_15,bs0_0_0_16,bs0_0_0_17,bs0_0_0_18,bs0_0_0_19,bs0_0_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_1_0_0 : Fin 8 → RI := ![⟨-36667751636365443940845858708717326459367581500199434198912,-36667751636365443939434531135596698870174490489317241911122⟩,
  ⟨18492631635635764028483427952068908172679474522565510083326,18492631635635764029498406287610906925035647960641436095566⟩,
  ⟨745537937317760844698907463863366616376624276963191837497245,745537937317760844720165857638602368292625502816135098100475⟩,
  ⟨-160983113086922546203391027763078878971748810926919291314386,-160983113086922546195524879891932835966029102572974096290028⟩,
  ⟨-706469331166926317236637733770915719054228104314591754885615,-706469331166926317214106066515242328673484006251263510532332⟩,
  ⟨-240501608250212125714906167318212105252783951746337172396312,-240501608250212125705235742420881014091091484266233578734422⟩,
  ⟨-7887414792121986614748266162055072016658786841169803114401,-7887414792121986597747444744014003187463176148367589675676⟩,
  ⟨3479582196311526050779543998556839177502592504038835278954,3479582196311526060369368168808262596827225045408801281733⟩]
def bs0_1_0_1 : Fin 8 → RI := ![⟨-40590569999221706637520108108544921181764095728564937454236,-40590569999221706636066253219489888833601539325241432013768⟩,
  ⟨20451386706487244225676089989611260004557214526524373962632,20451386706487244226721652510681637668011638206780602616694⟩,
  ⟨744103822685633274381434118644226682546716686665929897900401,744103822685633274403333088318056487966234958135897093511047⟩,
  ⟨-148575825427697818234402173862512915758580104823238819846923,-148575825427697818226298996571603610820886825192442480927274⟩,
  ⟨-701336596943239207153052052393128054769612215653445830998451,-701336596943239207129841441885538182663708265153003838451757⟩,
  ⟨-241800677567740298962322484370202249356567639857130267993931,-241800677567740298952360662051899906701560320097499858527959⟩,
  ⟨-8897349742439224080241587699575163804535606738488580207382,-8897349742439224062728483153750324205323851346816812494783⟩,
  ⟨4831558262479267377108127167716311035725135205225504993817,4831558262479267386986920029567427881586281256132106591188⟩]
def bs0_1_0_2 : Fin 8 → RI := ![⟨-44679631241527322932311277837753306784600076850111323525367,-44679631241527322930812589063123323638133265708087946290812⟩,
  ⟨22482593533626365595922095385579546607651155859923112019943,22482593533626365596999900897872085842476388605031417937092⟩,
  ⟨739909313390323979903102063319701960370405778789702557169701,739909313390323979925676352042210111917322806879209033645270⟩,
  ⟨-134304754864733440608905782889099996062490763317452090192593,-134304754864733440600552720326803496271555359862843135584558⟩,
  ⟨-693322372626058777689677572613559129283902528214586343862830,-693322372626058777665751194759744254229706413932069085591409⟩,
  ⟨-241725435806049614158685445114969289126546497715693314707238,-241725435806049614148416420746836523986551046440305522593586⟩,
  ⟨-9931831652944816555420228909464960109181140155308729807026,-9931831652944816537367056347866405395356385535471486392581⟩,
  ⟨6278603346895417093928367008075971744396649611680140803184,6278603346895417104111801462494985884499105685431152890553⟩]
def bs0_1_0_3 : Fin 8 → RI := ![⟨-48910925802279709403611801208662279562270060768253699447527,-48910925802279709402065783213128800391803515896644933758343⟩,
  ⟨24570754464131260374639423460427764498647265157740319971315,24570754464131260375751266523438129145446487161196012035033⟩,
  ⟨733045720455463053007059681687048893789606652923072499891582,733045720455463053030346875927902811471069703795707142714923⟩,
  ⟨-118270315980576436274241568876646817200448108277828627293847,-118270315980576436265624713090576996591022124781420944882751⟩,
  ⟨-682534842218673580566948393859092373923782287383754662612254,-682534842218673580542266410944268425804115400332954807081680⟩,
  ⟨-240325693835620615119002030265628238359648428589348148064063,-240325693835620615108408705795191849845908573343065161353861⟩,
  ⟨-10971631434181618812809963786557576448120896710760779623822,-10971631434181618794186664453801741633334278944101847727584⟩,
  ⟨7788974539608436576240498784888612319671448306088510877455,7788974539608436586745530376073807025926164412010900748493⟩]
def bs0_1_0_4 : Fin 8 → RI := ![⟨-53257222159055267245635717577119196410771694412736789376212,-53257222159055267244039665755132998116173776320266889137135⟩,
  ⟨26698260804840335077318873073132868493400285862695213528955,26698260804840335078466698746314518925419400727560231677955⟩,
  ⟨723639614681357547253268131427952640736354883561223100223923,723639614681357547277308969829881084666945276625729875223291⟩,
  ⟨-100597103519998595719884507402172408577866467454301502946957,-100597103519998595710988784055516955987320320880869745807241⟩,
  ⟨-669118876073128303159196074500320583492025219870475032230775,-669118876073128303133715307836941775208427774412184287799150⟩,
  ⟨-237671319372944121059419574028594990076434682284255878240034,-237671319372944121048483417482588199018510104447340421386181⟩,
  ⟨-11995231040744828009373306942774980573602866502524539463313,-11995231040744827990147301218927672137234646286890719279347⟩,
  ⟨9325862775373226330068810773537286739053911306961731685085,9325862775373226340913817015085383537612029588797762712944⟩]
def bs0_1_0_5 : Fin 8 → RI := ![⟨-57688412993350822515895901006304883354031049131350820364310,-57688412993350822514246877715430658405356655871640318896574⟩,
  ⟨28845594234427694989273774772520870310818194792321519695004,28845594234427694990459695707454837187064034721694605687931⟩,
  ⟨711849350804263156768794914876126842827549641201766614836456,711849350804263156793633646244901510039304011754020468397559⟩,
  ⟨-81431573102458648540579872640539014115874057492359417365440,-81431573102458648531388908546636004064164291668014029057266⟩,
  ⟨-653252533221323352642972561496215264028901923650863007750699,-653252533221323352616646111992149079056506389346424270872199⟩,
  ⟨-233849989479114539062145184729015390727775241279953798668565,-233849989479114539050846067364045494712667978544674534909292⟩,
  ⟨-12979431945687172626895766590957533653176388440522130255171,-12979431945687172607031667698796658349252644983937417836610⟩,
  ⟨10848606929027162047606882680521474958481087193176472548490,10848606929027162058811824547448820908144386112057899544032⟩]
def bs0_1_0_6 : Fin 8 → RI := ![⟨-62171955805745315360949067198092827779371088795005225725541,-62171955805745315359243874243959601031115827142016389994074⟩,
  ⟨30991596219747389199719451229077698954687177618130008922224,30991596219747389200945767457351562727565388218006341226867⟩,
  ⟨697860493133584744975221623127253419871018368495235248389653,697860493133584745000906420882430155858458015504240932160242⟩,
  ⟨-60939029233229923820055621733485484126639805499198774714984,-60939029233229923810551591498478906241633312167391923865523⟩,
  ⟨-635142466458070185947924521058931279079802862113241047294140,-635142466458070185920701329943151372920078349177417799773707⟩,
  ⟨-228964261010756684618602122153268493686855254475511092479875,-228964261010756684606918129922533914880891619511851727904268⟩,
  ⟨-13900117067151033557366745825262040444124125419495580674424,-13900117067151033536826028384585639535285450568104714415432⟩,
  ⟨12314209350066729513069185714665772709116818864449833380724,12314209350066729524655794605310410743303587205295102088846⟩]
def bs0_1_0_7 : Fin 8 → RI := ![⟨-66673397648229593768360348861675795924404168075549548637705,-66673397648229593766595495625236731771038774026157412924489⟩,
  ⟨33113799627813402946374476395592999262080750031447477511623,33113799627813402947643698250581342612881649661922488524724⟩,
  ⟨681880298156031021845138994232009195006269042175703004374095,681880298156031021871722436496224484838916885249384517379431⟩,
  ⟨-39300012674565708320313837866763328727785835423409854777044,-39300012674565708310477286244319107703063714991526457491184⟩,
  ⟨-615018382269412652004171805022232240398968403470955830373684,-615018382269412651975996145000528662577214827237385661242699⟩,
  ⟨-223128062173033737113177718623346442914574438031928765458485,-223128062173033737101084933784431876315402552333058339749620⟩,
  ⟨-14733143684515963934838057689470589031001790904571790379065,-14733143684515963913578673778758068330937625040486030102355⟩,
  ⟨13679102665593232075657194736667344288547977734442352642569,13679102665593232087649189044645849365714878300951794223290⟩]
def bs0_1_0_8 : Fin 8 → RI := ![⟨-71156968158833111276611185790793892974100330732999680770410,-71156968158833111274782852235309321138670147508159761946153⟩,
  ⟨35188812620840024037922622366363953478670577065285303314083,35188812620840024039237497087336079337940367852625916426656⟩,
  ⟨664131483317006433587647398828943454403944568543806708614293,664131483317006433615187025642367485247759358457492828812579⟩,
  ⟨-16706222524282996464218545383144709235898036056015999275078,-16706222524282996454028181090891781277222488684789804422289⟩,
  ⟨-593126779365572262734212476000644743356044645288326295919577,-593126779365572262705023360666759131078317643304033782880709⟩,
  ⟨-216462756074214564884133057218663765583755187229403031271391,-216462756074214564871605304857168457223440346704807204934917⟩,
  ⟨-15455332332048658517658080939988010066661922519230703957058,-15455332332048658495634014479318040022924356174491013825748⟩,
  ⟨14901093130675311511256502753002502951966765238434246644831,14901093130675311523679839230915359647403948117333521041063⟩]
def bs0_1_0_9 : Fin 8 → RI := ![⟨-75586219856936006841001128386078253803405658395848157889940,-75586219856936006839105121990006195054626479343753174205499⟩,
  ⟨37192741071315045521339935082560685077629951265348286188910,37192741071315045522703477787067117576166206249751259636465⟩,
  ⟨644845580096940113363750537322235499176537910605398709998090,644845580096940113392309499349215020229392486412773691078602⟩,
  ⟨6643851311659676410115623496453755627664899557432677857336,6643851311659676420683167814926022410952575099382580698022⟩,
  ⟨-569724256409759186874039331806145529999662110561831196311960,-569724256409759186843769828080783250897505742128236978174097⟩,
  ⟨-209092971746735436737976982966472356759463663261498002319827,-209092971746735436724985535899920551714068208098747586806111⟩,
  ⟨-16045504348456804859489012545538860625365887435451680864159,-16045504348456804836649760511120434527483974938645804161199⟩,
  ⟨15941382302962298366268405331334291020081136735402705618776,15941382302962298379151571727298484203882111593802245701107⟩]
def bs0_1_0_10 : Fin 8 → RI := ![⟨-79924690210024437442038905661674161780693625704017047090384,-79924690210024437440070611083972310856142609324554958523612⟩,
  ⟨39101632580112991339428119901931983442602147419879859756826,39101632580112991340843649784791129194094495578164742375378⟩,
  ⟨624256226143489538746620816245498896008819865479117056026851,624256226143489538776268632950654209615066433675682213874388⟩,
  ⟨30549376494074344691726137519573268285607623470857242587864,30549376494074344702696585839207607696782714622979123328713⟩,
  ⟨-545070734309773981717094723266117598600204249001185227798027,-545070734309773981685671147809822583121093444566046588544235⟩,
  ⟨-201142434619979845485600495814764893758362052528372770430295,-201142434619979845472113729698956492808339997516474891785937⟩,
  ⟨-16485509921113676696010447214095979585929191020589787202933,-16485509921113676672300413307585119987687659756860558078656⟩,
  ⟨16766548837793556076223954111080754137888868102143573876966,16766548837793556089598311187771134432693807630769322468822⟩]
def bs0_1_0_11 : Fin 8 → RI := ![⟨-84136556904799353921070118897863791231021194115564192500349,-84136556904799353919024438879798112125591610359279993843486⟩,
  ⟨40891923162188002519117941875326987968619695493175227323566,40891923162188002520589124710015362925102617548455916377827⟩,
  ⟨602592787269785407382428590566519157808857562586489701359835,602592787269785407413242040392650483119783150377802760600922⟩,
  ⟨54811477714850871992271969591510546618413217893318968549492,54811477714850872003673731894310389903876356731530012217444⟩,
  ⟨-519422973107297361089640051580241391159839198594259821861698,-519422973107297361056981027298200892594147155013038008031678⟩,
  ⟨-192730051467950873573019130510986939892790983495708992748404,-192730051467950873559002118898839498906580113819705491516123⟩,
  ⟨-16761180536119069579347189748179185080929604047494213457975,-16761180536119069554704972501143900345480323478554543550849⟩,
  ⟨17350358579825053459429840577046046692799647632398091940119,17350358579825053473330023677763411344829160364478340793978⟩]
def bs0_1_0_12 : Fin 8 → RI := ![⟨-88187256649225904907557722508913715940509280354429966547053,-88187256649225904905429008131856279720725591573872661408437⟩,
  ⟨42540867133138529263244543522230739679440012974982108865351,42540867133138529264775441817080289825851552641866375714790⟩,
  ⟨580074707177821005881431228274837748094683676170407684508938,580074707177821005913495399148296536769583074869389799283151⟩,
  ⟨79237153384780128626213131533631911371346347018627730555598,79237153384780128638077692522441030037863968456501600861580⟩,
  ⟨-493028769961670198990402998576547537895223383706659658165063,-493028769961670198956418341193103455594657220051801118323186⟩,
  ⟨-183966508919667576952476085579547258580556699796484714872549,-183966508919667576937890122047113163509215048980471009263181⟩,
  ⟨-16863136264537976995997436821946770623478595309495210785695,-16863136264537976970354989482808707815862887047230399856454⟩,
  ⟨17675266819761485325133132271015409662446923952043098600133,17675266819761485339597525210701371373652341281634499045996⟩]
def bs0_1_0_13 : Fin 8 → RI := ![⟨-92044039225995916771347052420154516135948348505560942912611,-92044039225995916769129020345326281562337274944844020166116⟩,
  ⟨44026931863607547282268237081681262294000108499395178173709,44026931863607547283863369598214930092564317503219594170108⟩,
  ⟨556906953529376811354669196927087860633078001903184282037317,556906953529376811388078732850113212042458970746341879548869⟩,
  ⟨103642592600023942952074526298349765358725207041490500906162,103642592600023942964436906667810030548929678750302668646444⟩,
  ⟨-466122195998427920628809355685861866072322627386540438743601,-466122195998427920593398752487409885472345653023231165382008⟩,
  ⟨-174951624946773815544398960846585359823392783742780650194652,-174951624946773815529200991919278561236185075913405742520202⟩,
  ⟨-16787380717887368644545135750067741595670423653405687536731,-16787380717887368617826769355834261197591550770358111459281⟩,
  ⟨17733484267148306515942785608667179017043119516002770216674,17733484267148306531014083021250088141994905831722482856364⟩]
def bs0_1_0_14 : Fin 8 → RI := ![⟨-95676432756669710759807860639398776504100325752913313332368,-95676432756669710757493494316155084909983220922914564030454⟩,
  ⟨45330141816044456681183926030052725987088401072542534798934,45330141816044456682848338830593685745434092553164753128789⟩,
  ⟨533276858872850865784383421660274432468498978319569110794933,533276858872850865819244010780246872038949999894067450324079⟩,
  ⟨127855715935685988593955582620301876066515839610982317288556,127855715935685988606854889680429102769791953721895676714522⟩,
  ⟨-438920161535093114134020804329306127443159491764441331376311,-438920161535093114097072236966994986372503720138606942563296⟩,
  ⟨-165772646318921313370525514252964267765596885383621079861061,-165772646318921313354667462484146640741720456795181816707388⟩,
  ⟨-16535625867852992418704865049979573532400192635133547251794,-16535625867852992390826058383388191975527850922338786111950⟩,
  ⟨17527499838536260185702970493513879428563194702141144397323,17527499838536260201428849111340738491902351956702151172929⟩]
def bs0_1_0_15 : Fin 8 → RI := ![⟨-99056603251820120184741823266075744862609779217316938395321,-99056603251820120182323254258602988285224996843363991088598⟩,
  ⟨46432360380453375624649549145855183380145992881336326942522,46432360380453375626388900939292162710280075641738091860356⟩,
  ⟨509352543861100622990959969474467745560189741508768096801393,509352543861100623027390131623429278881287014842479391071765⟩,
  ⟨151717827583112379133918525532996317103440857574931432483731,151717827583112379147398614644392359833932620115265239495495⟩,
  ⟨-411620491459771531248752515850432927585475515172178845919988,-411620491459771531210140365735797851353294785878657629606301⟩,
  ⟨-156503611768809374538181968636630387684762558098824271611495,-156503611768809374521609919457433574458944691155967573846546⟩,
  ⟨-16115305642332211399738796902855194214003972272070758931529,-16115305642332211370604766956329143265297204518187555316872⟩,
  ⟨17069989226988845755867936596122283591963714458820446106615,17069989226988845772301861622720304181368852443490802513162⟩]
def bs0_1_0_16 : Fin 8 → RI := ![⟨-102159601111282017559832174762644886141754106612262268776519,-102159601111282017557300539237948034705444514972704652928728⟩,
  ⟨47317503123661097594068248897414273211600120055587694360000,47317503123661097595888914248113696925617250178597389782832⟩,
  ⟨485282964346203305064973519787795948462810782047682812161326,485282964346203305103106768159817202180870055724318490153376⟩,
  ⟨175084350045719863065361162662402879646839227991216574228629,175084350045719863079471437112013209734620278362643793466778⟩,
  ⟨-384401551459878596960859407721494016915657224430998031642964,-384401551459878596920442164875221791344966391652273947606534⟩,
  ⟨-147205804548628119683128271212382184055764940594694945821719,-147205804548628119665781489586547143072649496475244436385444⟩,
  ⟨-15539260671038750881899066666139926006666533446653892721767,-15539260671038750851403039899190765616216647170725934073458⟩,
  ⟨16383086807736385718376343429254275711109609704218517150787,16383086807736385735578543688539383410612147480645530589008⟩]
def bs0_1_0_17 : Fin 8 → RI := ![⟨-104963498374215183791824964535213724495451875993468972836689,-104963498374215183789170228473280181452971577276742139806230⟩,
  ⟨47971681810963368280330362277770142986871853469218115099979,47971681810963368282239557308425195624711912690892440250809⟩,
  ⟨461199456929197780722234054346716023192533262322814987149591,461199456929197780762221528303515018733566087729637465492765⟩,
  ⟨197824707985806170834888831841200975336429935837175538217794,197824707985806170849685217047541075085945089889133976163751⟩,
  ⟨-357423304717911305257935019344176713409111354956385296515026,-357423304717911305215552491898348520240207852117154119814026⟩,
  ⟨-137929208056645022709413914405429945770274630668549830403442,-137929208056645022691223647168313268291427887452505484739673⟩,
  ⟨-14825104888974884060948479228254816658649962750635487770253,-14825104888974884028969586052897751853155998955373237546628⟩,
  ⟨15497055647799509187753128353170432550975219050460785516298,15497055647799509205791783968216700401853686836449894012228⟩]
def bs0_1_0_18 : Fin 8 → RI := ![⟨-107449431761062175133950291808143905503501779587532552984351,-107449431761062175131161036484583063159120432837270630111228⟩,
  ⟨48383284503265986968258817106683477918625031552300102496651,48383284503265986970264753771834671145754053941160548136897⟩,
  ⟨437218490251267942536966859300863160875555806458302154009776,437218490251267942578980555580921107850907450181776439952622⟩,
  ⟨219821522647537319057383441401534655977908644710568907024941,219821522647537319072929580544472062931021226969252454036311⟩,
  ⟨-330829517951228938157548273097855007024215722140121698576465,-330829517951228938113018162553258938561287679004421318275493⟩,
  ⟨-128714767879898135760527702197758271243513636992112929046734,-128714767879898135741415708182106486409777597293365485990722⟩,
  ⟨-13994314738248391805989703033455551071085085739500347666576,-13994314738248391772390393742726494236432622061369901899268⟩,
  ⟨14448449597744720520854654426802956953008251778803935586769,14448449597744720539807354443010490887903155560911589143624⟩]
def bs0_1_0_19 : Fin 8 → RI := ![⟨-109601576106445577832995383136851216459112373194999081755776,-109601576106445577830058539657989133381499251109166364069240⟩,
  ⟨48543002444914411267845809035918073507201590793284788727084,48543002444914411269957886035198901106562605974095557546030⟩,
  ⟨413445187440947712525216098161127920302100658427001191448165,413445187440947712569452869496026017891064490816298577854160⟩,
  ⟨240969357616421841023550501468417885175516224376985204500696,240969357616421841039919235079198048222669592286991555602455⟩,
  ⟨-304750700231874603608453717215711165016908850762767286970145,-304750700231874603561567380328006615957715162746129744984339⟩,
  ⟨-119597169709896332704604013070050276703192795688677224363873,-119597169709896332684480744138894631071805240266405547948195⟩,
  ⟨-13071109273547798741647133015822665335514495526967056512560,-13071109273547798706269979999271860903685991432173693240557⟩,
  ⟨13277914211289944892240481639316273064596976496314378215646,13277914211289944912196027830851214151740031423347248127427⟩]
def bs0_1_0_20 : Fin 8 → RI := ![⟨-111407078888418076488360029247527419917930957465128754771871,-111407078888418076485260547026688738786439316433983655535113⟩,
  ⟨48443819850000707621931687647023202340781455172318412029164,48443819850000707624160728845635926053780417075624599821067⟩,
  ⟨389977093815373440587812870513910746352525507509305123912028,389977093815373440634499419268274958916788302754098733455126⟩,
  ⟨261173305977493332943018327931175518571404800716815464471977,261173305977493332960293541666559790384708172111257374328654⟩,
  ⟨-279307272209548746521689255728645149886746609652902740877591,-279307272209548746472206411773887391254699580931526280960155⟩,
  ⟨-110607781563847457868461579867904192394769952442842010027930,-110607781563847457847223909312078822523087179538931984812410⟩,
  ⟨-12081210263738491887325578457363295891331769706741525269045,-12081210263738491849989282673519509817777563793301495760939⟩,
  ⟨12027811043406165333436516005829799059808625516246837213174,12027811043406165354497175544831074742560871475620722759892⟩]
def bs0_1_0 : Fin 21 → Fin 8 → RI := ![bs0_1_0_0,bs0_1_0_1,bs0_1_0_2,bs0_1_0_3,bs0_1_0_4,bs0_1_0_5,bs0_1_0_6,bs0_1_0_7,bs0_1_0_8,bs0_1_0_9,bs0_1_0_10,bs0_1_0_11,bs0_1_0_12,bs0_1_0_13,bs0_1_0_14,bs0_1_0_15,bs0_1_0_16,bs0_1_0_17,bs0_1_0_18,bs0_1_0_19,bs0_1_0_20]
def bs0_1_1_0 : Fin 8 → RI := ![⟨-36667751636365443940845858708717326459367581500199434198910,-36667751636365443939434531135596698870174490489317241911122⟩,
  ⟨18492631635635764028483427952068908172679474522565510083326,18492631635635764029498406287610906925035647960641436095566⟩,
  ⟨745537937317760844698907463863366616376624276963191837497245,745537937317760844720165857638602368292625502816135098100475⟩,
  ⟨-160983113086922546203391027763078878971748810926919291314386,-160983113086922546195524879891932835966029102572974096290028⟩,
  ⟨-706469331166926317236637733770915719054228104314591754885615,-706469331166926317214106066515242328673484006251263510532332⟩,
  ⟨-240501608250212125714906167318212105252783951746337172396310,-240501608250212125705235742420881014091091484266233578734422⟩,
  ⟨-7887414792121986614748266162055072016658786841169803114401,-7887414792121986597747444744014003187463176148367589675676⟩,
  ⟨3479582196311526050779543998556839177502592504038835278954,3479582196311526060369368168808262596827225045408801281733⟩]
def bs0_1_1_1 : Fin 8 → RI := ![⟨-34706342454937312592529997666770731477654057082237339147588,-34706342454937312591097406435682901508976233375134490283460⟩,
  ⟨17513254100210023929871804840533542801191479399495926822762,17513254100210023930902075268839731009096777958662004155912⟩,
  ⟨746254994633824629857323848523639556539819549303310839791958,746254994633824629878902530248172335207579297964766067898897⟩,
  ⟨-167186756916534910188003969423243491544319949617185098995763,-167186756916534910180019306842215817572613455624814332023760⟩,
  ⟨-709035698278769872278770046085767792059115974863721590925902,-709035698278769872255898907204136160815791950581836472475915⟩,
  ⟨-239852073591448039091343707502702658947549533830704032499542,-239852073591448039081527583894885942039199640210837030935613⟩,
  ⟨-7382447316963367882257746957186911507728449241945191704848,-7382447316963367865000783975253957293524766199708201129186⟩,
  ⟨2803594163227655387470768068177256535123064398677182624227,2803594163227655397205076584228526667715953694815466424301⟩]
def bs0_1_1_2 : Fin 8 → RI := ![⟨-32786493993371519643743366707169334216050399387570464800216,-32786493993371519642288935175704165358054145647682319699398⟩,
  ⟨16551989503856194124523517568604661122507534608786312106699,16551989503856194125569494791098484451030097994710484416076⟩,
  ⟨746281953284092983975525555657566299616413992248688491803208,746281953284092983997433211118917178191902691469284523878231⟩,
  ⟨-172924455020212361758490026815196364996160929456924342130424,-172924455020212361750383635561381076828150511689387635262502⟩,
  ⟨-710881692867240097475955158800174549763730395718423036154076,-710881692867240097452735342269007547352043367381740664224554⟩,
  ⟨-238858961162879237955017908610387436558863908352013380381696,-238858961162879237945052135134870301155938268783325329204826⟩,
  ⟨-6883616581851837902188557670411177127990290022595923421960,-6883616581851837884668506902588851442629320998600175352368⟩,
  ⟨2151373384705886821784906305597721105355779219632521493125,2151373384705886831667617392690888918143124398866066814346⟩]
def bs0_1_1_3 : Fin 8 → RI := ![⟨-30911207446793388022186935261584160036052377633850292529785,-30911207446793388020710063191620515880608910319033841779533⟩,
  ⟨15610775053189508083011301752000278424500566649711399687851,15610775053189508084073417439330417686249862239414552411550⟩,
  ⟨745607399390612145585618681875541899190760023955620265504522,745607399390612145607864352276179841752856295881120130465173⟩,
  ⟨-178183655575136523046431867197306936293148323171481410140759,-178183655575136523038200401795202776568019355533160315388448⟩,
  ⟨-711993791931925923863139186188335006863991748410634146178837,-711993791931925923839561109281496059366402850977758414636563⟩,
  ⟨-237516044605695654329053059730078815099246461554213392239951,-237516044605695654318933523551694714716691382075283244101082⟩,
  ⟨-6393326222969539827975260785797932017972621654400718720922,-6393326222969539810184891776664546195086151842652196381411⟩,
  ⟨1526887724490162681846768972257874085655678707066731814565,1526887724490162691881961186038750471089448084724881430569⟩]
def bs0_1_1_4 : Fin 8 → RI := ![⟨-29083282637739427194050523139406706836755955477873904779302,-29083282637739427192550585415579158659436687911922564751004⟩,
  ⟨14691416014810216418412444227596094888741550572029712068698,14691416014810216419491147941271210753387879791307115977149⟩,
  ⟨744222122811470663333260122155738203471592592262065425967640,744222122811470663355853223416422453317343784563621441479636⟩,
  ⟨-182953318018628064154795611674395413156686641353804664127525,-182953318018628064146435587993176850873539433343564241306573⟩,
  ⟨-712360765369213540953636833708430013273076069555029406349544,-712360765369213540929690516537705217654838470841173785679388⟩,
  ⟨-235818351113962862449144722043920476532693663839929698936976,-235818351113962862438867139868477389174282510527867237193081⟩,
  ⟨-5913836816751888212079715075985292582873911638547628187864,-5913836816751888194011497699372642382592295934748734903819⟩,
  ⟨933788411618577741470169642730498108562083815880777786096,933788411618577751662090577134176312747142309195030000376⟩]
def bs0_1_1_5 : Fin 8 → RI := ![⟨-27305307198490413156279137233946658159262807193935057997917,-27305307198490413154755482480170544755481450416251272016961⟩,
  ⟨13795579421176229871004104475383621934102929984771030336923,13795579421176229872099864662720032712922125409105256144082⟩,
  ⟨742119225760822156016710894222100631736385553260968826599008,742119225760822156039661237820738830428951169157811894105366⟩,
  ⟨-187223985525882260296582865857955541393063477469487633702673,-187223985525882260288090653400563789996118462634812713895780⟩,
  ⟨-711973785274439534734496308078711925890055216448766115240415,-711973785274439534710171351506806575607577821902059808860938⟩,
  ⟨-233762231669041037749030997631347524098728980971814306954469,-233762231669041037738590906226049455590016097115101182665135⟩,
  ⟨-5447246865062406851604006424421638558749831624212035427719,-5447246865062406833250094218105807946339426747622141101253⟩,
  ⟨375372099942878093434635811382798759028100757304761116612,375372099942878103787711499202077698236099973576591607503⟩]
def bs0_1_1_6 : Fin 8 → RI := ![⟨-25579647229182909819124742264060116349041195644571471476836,-25579647229182909817576691350517277237419759916576947330641⟩,
  ⟨12924788839042462613963788357310882963142357673025249014429,12924788839042462615077093425157165270987445484188402896700⟩,
  ⟨739294214264500710906781871880819013663384949171312124259675,739294214264500710930099687341282554436556028230033481572098⟩,
  ⟨-190987846664246197196304271578164911432930589401689276227994,-190987846664246197187676085159872689421401098858480421014263⟩,
  ⟨-710826518099543334190029092994533894407696667111899629991666,-710826518099543334165314654799287427978470000596953489060699⟩,
  ⟨-231345420617009126909686250721750882687786082892826063062798,-231345420617009126899078996685055254324787002595584977651776⟩,
  ⟨-4995476178058612448668920027241706031729261320992231320736,-4995476178058612430021132208125512239456226063195722689712⟩,
  ⟨-145452362364530620195593600177586927316980387075546462472,-145452362364530609676748542415440108072277134681845674699⟩]
def bs0_1_1_7 : Fin 8 → RI := ![⟨-23908439512423076657515092191468831110015678079432966056788,-23908439512423076655941936623494967151478922551045267022090⟩,
  ⟨12080420245846821764714098778186586197139738500467927346254,12080420245846821765845458251580470480332080919099278528229⟩,
  ⟨735745071236470910202734637138754630301266918052401546762827,735745071236470910226430596298573526254011639986435542730341⟩,
  ⟨-194238785504808154371579253782777778388987793254513087590781,-194238785504808154362811144551523280635207220232431271135997⟩,
  ⟨-708915198477989979896520584761952135422540090520470196263494,-708915198477989979871405353915127415494926237579102993210531⟩,
  ⟨-228567083783236825637375136191380131946234772370845187449809,-228567083783236825626595864913644418842695138086642405139380⟩,
  ⟨-4560251830238877940233868318456058705344779660676956655443,-4560251830238877921283670375141056226838915775962630039690⟩,
  ⟨-626192061356444321619722516623902362506764161535562788103,-626192061356444310930293941314222853050850159449871757446⟩]
def bs0_1_1_8 : Fin 8 → RI := ![⟨-22293585343711689321817233157552851424067195229156292741803,-22293585343711689320218233336788034393665586955935350628864⟩,
  ⟨11263699043391764377180367711802803646878032547603025462433,11263699043391764378330313484492027367476573458344428463504⟩,
  ⟨731472310249328138625090570976586912997073626176613487721621,731472310249328138649175814178705620906841731446861103284535⟩,
  ⟨-196972419641155666556708494578050327456934774393372294336735,-196972419641155666547796340322819571394622572095135392803963⟩,
  ⟨-706238683808679726863770666843861220103871058326379454418433,-706238683808679726838242835750631046240289708115414745441454⟩,
  ⟨-225427854504769346022322819890646851757708094049719688321786,-225427854504769346011366463639521560305706318964104084826646⟩,
  ⟨-4143096816139500696574872795787477825794119612597876728267,-4143096816139500677313355542430618310578212519340061521835⟩,
  ⟨-1064792747848878768495422367659138077185847778925254094355,-1064792747848878757630384780818307729492247805933733138981⟩]
def bs0_1_1_9 : Fin 8 → RI := ![⟨-20736746015075399806551782954975990744536623175261428591315,-20736746015075399804926166301927257438659261276729523132593⟩,
  ⟨10475698221644220660159022010784132956722632426672233013468,10475698221644220661328109695414964410105913221410008508922⟩,
  ⟨726479009369440521457517836334957762123088974011399809447955,726479009369440521482004000706998212515914082514832606982691⟩,
  ⟨-199186125740000229267404259412943607466429113409472566311539,-199186125740000229258343754099721872853779561256117559103891⟩,
  ⟨-702798488979948218549553822916096036409762657263007959023743,-702798488979948218523601057441991012499227967914533475233496⟩,
  ⟨-221929857153931625331872342803712355830406038969849501404295,-221929857153931625320733607859928782541319873762806770392052⟩,
  ⟨-3745321482662297215708947446370876419342291582400515753110,-3745321482662297196126804407114137261774060022138294080110⟩,
  ⟨-1459655971836135284756074560178273596198016997852265922460,-1459655971836135273710178364451684129851355537625153122313⟩]
def bs0_1_1_10 : Fin 8 → RI := ![⟨-19239339967397739157200450684715456000524137244560773560049,-19239339967397739155547409610516884214788323058069692908957⟩,
  ⟨9717337668888075733586981681829051413603946812802486075978,9717337668888075734775792068586807049260622567756138244612⟩,
  ⟨720770824726825851116606314500920024740263074052738273827351,720770824726825851141505564505936666693066418921029409739668⟩,
  ⟨-200879052424744394448668994073243802244485327234265537970645,-200879052424744394439455636540457092989256923935802465398258⟩,
  ⟨-698598800906537149446502053993360530183763693746818080124442,-698598800906537149420111461083673690723813752511024943735658⟩,
  ⟨-218076717920772615870536741136362289549961902392347509171254,-218076717920772615859210093896220531388435858238495390997263⟩,
  ⟨-3368017766257349063517269315818759476422568776779205207078,-3368017766257349043604772292654901663577838683936270988787⟩,
  ⟨-1809650520244360014241010100173306572538786361328220291700,-1809650520244360003008767813155886103972178887651137923737⟩]
def bs0_1_1_11 : Fin 8 → RI := ![⟨-17802541605532841461737916771957061060791076563104543508540,-17802541605532841460056606485577235848527719557025482780726⟩,
  ⟨8989384608246872163530613363779742974854965085973052532749,8989384608246872164739753997369892007245315988950230479613⟩,
  ⟨714355983784638900262790964080887996377452789248623755594437,714355983784638900288116024546728263616742279499088384286248⟩,
  ⟨-202052120466998568491946341862692468558985572076564391327191,-202052120466998568482575423599501753925563112747623512902171⟩,
  ⟨-693646472839932715749524959281640404437555775006165292272904,-693646472839932715722683051953770116295780249776952671524654⟩,
  ⟨-213873562813191018665893787274428081829174565802247358287031,-213873562813191018654373439224769588933473716769212928905821⟩,
  ⟨-3012056216260995311675371063675871037876653630899805655665,-3012056216260995291422343722117020443952868094347327144627⟩,
  ⟨-2114118152455045180745552941940531521231253817819031793357,-2114118152455045169321224296379391208613812209244861668216⟩]
def bs0_1_1_12 : Fin 8 → RI := ![⟨-16427281749797565015218141190471465532775486147590526812771,-16427281749797565013507677325886015412965768908923795647924⟩,
  ⟨8292455125166110776099643130211327238061700202110624416347,8292455125166110777329750016315536772133300241761862554514⟩,
  ⟨707245258556985803075138455141896816335854699804653196585650,707245258556985803100902647002372450704972437783763958012711⟩,
  ⟨-202708010428909131870204999054279015809525149860898172250012,-202708010428909131860671590975435291955953078513234298676659⟩,
  ⟨-687950998689676070676956497774501672988251752723785360577447,-687950998689676070649649157236059515203303759067654358472784⟩,
  ⟨-209327003017754645421206349519703886726454558577577998261861,-209327003017754645409486240979283606806013500850115151803666⟩,
  ⟨-2678085741561226337458916414010421112809108517387703015090,-2678085741561226316854705700059777486926803983988994089502⟩,
  ⟨-2372873718395458154900381650249371815749090526447330867537,-2372873718395458143277957470927815158525671558891406368012⟩]
def bs0_1_1_13 : Fin 8 → RI := ![⟨-15114249678249197320898699080905606030842018318333398163849,-15114249678249197319158155126794222552972474098228132684179⟩,
  ⟨7627016736182346937077532233362439174849483986070974440534,7627016736182346938329271687112230932552323631647503081158⟩,
  ⟨699451919291235337004731287403969432798120055347753220367933,699451919291235337030948566414540864418933078082657876149649⟩,
  ⟨-202851138057744173280018739944172002481951687442129416048221,-202851138057744173270317678064225660582335837630610145390992⟩,
  ⟨-681524467854835533763200748900106819384895286421274463282199,-681524467854835533735413183514353668925446481393714701145281⟩,
  ⟨-204445107937794944684728544455691680092566079383087912063918,-204445107937794944672802326963446791761886628686315138602754⟩,
  ⟨-2366535977243788455970407150876142534446172551073657444744,-2366535977243788435003852329213887408104414476128659996757⟩,
  ⟨-2586199828040283403300452021456240487051868492189539288466,-2586199828040283391473636760252162109294365521587482580749⟩]
def bs0_1_1_14 : Fin 8 → RI := ![⟨-13863896696578508031334915657370686423965900161653123901975,-13863896696578508029563320169679054747777503808557580089598⟩,
  ⟨6993391936532417722911881346469844532934856158564436853119,6993391936532417724185951997076352633372116513210594114540⟩,
  ⟨690991669377486612819588827855672402111853568154577147405314,690991669377486612846273826579772286395089113886099912648481⟩,
  ⟨-202487617880803279749415783319595718108093009388359229074657,-202487617880803279739541653216886009562458319918860269654798⟩,
  ⟨-674381501306321344090303839830670858320403148336533135723506,-674381501306321344062020540615418581233138939887819512428806⟩,
  ⟨-199237366385343578199395302911850303768484650563752665484305,-199237366385343578187256320127358032567034240787897218628798⟩,
  ⟨-2077622131610425224334871765004445640879140238515097216436,-2077622131610425202994270841569066047168749621343856513440⟩,
  ⟨-2754836317495826033106282981481850622121524593969249253372,-2754836317495826021068475777015773835713568914818381129284⟩]
def bs0_1_1_15 : Fin 8 → RI := ![⟨-12676441156727120000403258119925955223651545034813748630832,-12676441156727119998599591695112177342628499146873673475890⟩,
  ⟨6391762653124341972236122963579058744473749477298649789593,6391762653124341973533257931070283905925886691606862317461⟩,
  ⟨681882562469727200903307491346417002698964878287043083196810,681882562469727200930475564746509743867589103248238838271910⟩,
  ⟨-201625215581207733920850608685857096324859520751201138380410,-201625215581207733910797728632657347230172723048330543333473⟩,
  ⟨-666539169878536633513484255897399961258209610785170519386183,-666539169878536633484688948203271118738672850748003050244579⟩,
  ⟨-193714636547499139359609341975172380896461877258732782444037,-193714636547499139347250608939316539809455751163011874804013⟩,
  ⟨-1811352142435289177807178013708362681984006282174704056317,-1811352142435289156080251275488550846113767083458305597155⟩,
  ⟨-2879964824366503883614407368284914083801758431712874519255,-2879964824366503871358681479444029768605592704190707137241⟩]
def bs0_1_1_16 : Fin 8 → RI := ![⟨-11551874831652533312877277686814327818790116685476588369579,-11551874831652533311040469670727786589263725979220856090381⟩,
  ⟨5822175520279823702745799078480131665642488718417284824983,5822175520279823704066768340562267394973383738515557028638⟩,
  ⟨672144902997756562126481491515982394015788640730592769882063,672144902997756562154148766526711017754921047878203253902516⟩,
  ⟨-200273289851857937781372391425236509590599642620850256621312,-200273289851857937771134794044425456287268363736595688916248⟩,
  ⟨-658016895920309664536364881155489075350274063194694863794853,-658016895920309664507040472123581787034347589327876416241959⟩,
  ⟨-187889085474097344110638674858812187026337450509072436405966,-187889085474097344098052855443001633783287963316408338494672⟩,
  ⟨-1567535944851149232655638993365486071949832109165484552125,-1567535944851149210529489363626140612388511722819095266600⟩,
  ⟨-2963188843075919535772963872293232029535380194689729203188,-2963188843075919523292044315405350428426826210532641623655⟩]
def bs0_1_1_17 : Fin 8 → RI := ![⟨-10489970542127361975513802688218469924478076738446383284336,-10489970542127361973642727592278294911990772020586796097310⟩,
  ⟨5284547888567846372848691695646536601705464281686434318773,5284547888567846374194304665065372415413730196004299837563⟩,
  ⟨661801131414345279490747738812830714627789766281109015337156,661801131414345279518931168323019941691373992271364346974673⟩,
  ⟨-198442724524709874520126752633069168608187626111783748230489,-198442724524709874509698164923413054757323181753322180647717⟩,
  ⟨-648836339618335456505858967112264989736801577559551150526707,-648836339618335456475987488458892742166471201603973563309297⟩,
  ⟨-181774118940926537348817907219065041677787381697025959059166,-181774118940926537335997289568867272104959685896656836624168⟩,
  ⟨-1345796631992080980304582589584427467320751571662583873327,-1345796631992080957765652457229990609148083187533832617114⟩,
  ⟨-3006509678781884006464424894681700336169806543210625917171,-3006509678781883993750664091820419671943365374901237670271⟩]
def bs0_1_1_18 : Fin 8 → RI := ![⟨-9490290922124525442650923437298206198164827970654106722921,-9490290922124525440744397029878680645650736724307983567420⟩,
  ⟨4778674472006848664703832539705158045714557469072553098284,4778674472006848666074940875187499452198397302808990853774⟩,
  ⟨650875695657391856646832175326032074643933725891187049361222,650875695657391856675549597052949486869257225495926495594769⟩,
  ⟨-196145851854909175780711781762460120666007100026977197491895,-196145851854909175770085603313634527278150949323064216206830⟩,
  ⟨-639021271440488197846171371645716350798134576133425392574283,-639021271440488197815733917261867458202423573957371342360032⟩,
  ⟨-175384302630556722740989249569835090910619649265928297622741,-175384302630556722727925719323125866990018641214762956840263⟩,
  ⟨-1145583273479759057079869589305392174463499145311563893319,-1145583273479759034113893725793026529635592589704336240821⟩,
  ⟨-3012298756321212726052907728121340965121463706255785155728,-3012298756321212713098258948476139070849053761576539212190⟩]
def bs0_1_1_19 : Fin 8 → RI := ![⟨-8552198202205488905619231641548644273424661828207982948461,-8552198202205488903676006678156007775714321798623794858520⟩,
  ⟨4304234535880250877907631959259560446447252103301531171374,4304234535880250879305132636223475691582646575845107159416⟩,
  ⟨639394910411843210860970796175353935925662468078951825376381,639394910411843210890240996979745410958448016902746189766319⟩,
  ⟨-193396367904068091104506441539938648257720821872922956517493,-193396367904068091093675720734325082017380224238077382794894⟩,
  ⟨-628597432251121072750583196782748646322132567387967768726859,-628597432251121072719559854566895759836465574808504285843575⟩,
  ⟨-168735275641014973094058960071157825257392412041303896182227,-168735275641014973080743971101267304819446878256928545062936⟩,
  ⟨-966185145916071056526329585556902596403964442522493448968,-966185145916071033118283710698635245039214909799034497593⟩,
  ⟨-2983266768335830547654518449163959787286111729070485347838,-2983266768335830534450506796035362576186387803853043924239⟩]
def bs0_1_1_20 : Fin 8 → RI := ![⟨-7674864885344198984774134849156842596932899900329739864781,-7674864885344198982792896399994438853475452249703118830005⟩,
  ⟨3860799526289987930809808098996927002244720230007589077911,3860799526289987932234646769806473092688981586876581445033⟩,
  ⟨627386805831366422791566646550894327806974611986330621700617,627386805831366422821409432816435178046119047068058799947873⟩,
  ⟨-190209241014315798833412296772080821519030020900067216981287,-190209241014315798822369704742574824841084116720124886705623⟩,
  ⟨-617592382726286392246053601135994459689453993206624841069040,-617592382726286392214423378399259627521705148172184696870904⟩,
  ⟨-161843657381370562082596789668519968093530767268457936062661,-161843657381370562069021332068681387791146534386296423611061⟩,
  ⟨-806747123517569485165891866240446709728125934776403159589,-806747123517569461299936364154028419717129910972312128001⟩,
  ⟨-2922430164678013275687134089914063189775195741307255998780,-2922430164678013262224824752004464256642882634806545675873⟩]
def bs0_1_1 : Fin 21 → Fin 8 → RI := ![bs0_1_1_0,bs0_1_1_1,bs0_1_1_2,bs0_1_1_3,bs0_1_1_4,bs0_1_1_5,bs0_1_1_6,bs0_1_1_7,bs0_1_1_8,bs0_1_1_9,bs0_1_1_10,bs0_1_1_11,bs0_1_1_12,bs0_1_1_13,bs0_1_1_14,bs0_1_1_15,bs0_1_1_16,bs0_1_1_17,bs0_1_1_18,bs0_1_1_19,bs0_1_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_2_0_0 : Fin 8 → RI := ![⟨-20652456903227746481567526807749473840494437677494819037491,-20652456903227746480776601110582301368942362186943916208726⟩,
  ⟨10304471390399633489876378887268279104445348174050735525203,10304471390399633490445185493879071692629751594849082672239⟩,
  ⟨-899013312094494093452844344614760460740572155281698330667359,-899013312094494093440930873754083574582347550094497248306792⟩,
  ⟨370683870197844953611699940412796721656902451512765617742129,370683870197844953616108228472325540681271192323625469013461⟩,
  ⟨934384170158308385259065624808185094495249391889946912747699,934384170158308385271692654118335387005904926485447104732151⟩,
  ⟨558359944564634581228558918328539221943159382525064656217459,558359944564634581233978345893588571783897722357541999359954⟩,
  ⟨2694110906225691968816864063420700384641415736103311911762,2694110906225691978344337903873189775887177880435667884528⟩,
  ⟨-28985677204130445349865796585653469128278643734499054786172,-28985677204130445344491538679730221996582249001122863601257⟩]
def bs0_2_0_1 : Fin 8 → RI := ![⟨-20144039530656855346568352515816230221172306237457534574738,-20144039530656855345767935183163380276167041213503260356437⟩,
  ⟨10050314930889808138028068398982367534947495329634207691744,10050314930889808138603701063958038491236500488559186038601⟩,
  ⟨-894173962653435425549452173043882066866657928578242132778150,-894173962653435425537395732593028604233077844662211656119726⟩,
  ⟨365260315951896807188411529615046796374198236990906228910558,365260315951896807192872720069243807786573145780082593191390⟩,
  ⟨928055851239005881285751685094749952777523115846002421187299,928055851239005881298530247172046274529311129298534077770754⟩,
  ⟨559062129392197791515993261424460229670645592804258229027302,559062129392197791521477725732144513940868530630897535249006⟩,
  ⟨2329020528826302074708600100622736057606019556085919103545,2329020528826302084350409976812912855005530745042706455800⟩,
  ⟨-26842212646327165137027919034992630264245786693426630129857,-26842212646327165131589166452479378693163095907684962283694⟩]
def bs0_2_0_2 : Fin 8 → RI := ![⟨-19609383905910485046613452095037353208520236905194962650131,-19609383905910485045803258945591381303919626607119896000334⟩,
  ⟨9783963686764033676101016817027462163305200007169275894657,9783963686764033676683679913807506681867952095776946743650⟩,
  ⟨-888535654448552050881701523958858356603014092339097829505676,-888535654448552050869497833382074159881244038205118167916051⟩,
  ⟨359417546387063025753988466447016596883426375886815073297340,359417546387063025758504143203281983632795148975601871209050⟩,
  ⟨920937281278562511970714016405733947089972205929382760920876,920937281278562511983648648169019897083114648142317524021499⟩,
  ⟨559266435612933482931736388881493929091756372165115034127552,559266435612933482937287837143817460266909022095694501166797⟩,
  ⟨1980739405512470997409859527873212166623452758191751145284,1980739405512471007169428681682730916741791652629237360391⟩,
  ⟨-24782038030851514737781321617042197701500784655748000330881,-24782038030851514732276143375491976697306050365302614779470⟩]
def bs0_2_0_3 : Fin 8 → RI := ![⟨-19049885343041908429484895166424119133516349647554572919158,-19049885343041908428664632868095466074775354589614449699029⟩,
  ⟨9505976926204522309607959703965827724747133190179059077731,9505976926204522310197864186918062089137479620413759970432⟩,
  ⟨-882107059783997646707401029824239255733918873814329957127767,-882107059783997646695045670750349625020973103061136581470678⟩,
  ⟨353164868552349276459383470439357752607952264136085078447709,353164868552349276463955268407712675870629062932754622379573⟩,
  ⟨913039546706740592061579172776495965202829450593806988429320,913039546706740592074674557235701110510465734575659331689775⟩,
  ⟨558975226690670775253718817004818226686414729378392347205085,558975226690670775259339259134998678187339550785262137608037⟩,
  ⟨1650589747981902196052457746921822396898985258289869330333,1650589747981902205933319650355700140452566296792348163960⟩,
  ⟨-22808069435737283375600325038513871710732206193176557539748,-22808069435737283370026727976866362132232466941872268967089⟩]
def bs0_2_0_4 : Fin 8 → RI := ![⟨-18467078710319634400202699313834879975135319497579636419869,-18467078710319634399372064952372678822021628980169921508523⟩,
  ⟨9216984170848738618155517974506108665044172098894511320622,9216984170848738618752881689159775199399218154653343403212⟩,
  ⟨-874899300942311291327183384468387364384608181479894548271666,-874899300942311291314671794193064760901326350104579721309113⟩,
  ⟨346513016859146527070142067571066386494417293822807807691719,346513016859146527074771675068479655045839525711751560109674⟩,
  ⟨904376162417329732536491450322168094804176084061737616793802,904376162417329732549752423465222552134524435027786194160822⟩,
  ⟨558192407525917054661988438408417657534465086327160100278703,558192407525917054667679949976698855458243071777730875633064⟩,
  ⟨1339716284918084270552148510730114768937890382022301445375,1339716284918084280557952062301155914202072710961674631391⟩,
  ⟨-20922740606001737066395070796837075674798057094457330448722,-20922740606001737060750996644241824422446050659415630541001⟩]
def bs0_2_0_5 : Fin 8 → RI := ![⟨-17862635072607676396977262773804440374201631215747358005575,-17862635072607676396135943391757511229203302746325250587949⟩,
  ⟨8917685312787294825667861614515862796112268180611024425644,8917685312787294826272909629125053412897671880047253112596⟩,
  ⟨-866925932195960039411442456932243855647929501216678254625078,-866925932195960039398769921473518963714858646788711437551057⟩,
  ⟨339474130960271498979752633142187243523126785913639209180796,339474130960271498984441794462213334617173744341265148326874⟩,
  ⟨894963046779899221628337306236150731985694172411581152936216,894963046779899221641768864389414921559651597128685356785333⟩,
  ⟨556923418743150811499308327804775550283899088397375031995837,556923418743150811505073053197469474187734342465524261153656⟩,
  ⟨1049079151774348998334380597452526941506468593254435384945,1049079151774349008468895675847203815984700121776532550177⟩,
  ⟨-19127992571752011078942926207383108259046877778447554288220,-19127992571752011073226248450487407525626169238911633601141⟩]
def bs0_2_0_6 : Fin 8 → RI := ![⟨-17238357316456286438416355893280381797803614000167729562890,-17238357316456286437564027997560590289433616131902700820466⟩,
  ⟨8608850178936812141437795162273109390192603278750403629229,8608850178936812142050760121960291183894130486464726876314⟩,
  ⟨-858202906903757852704137165595294865115448133381619997680878,-858202906903757852691298812276134701542735518722259567780091⟩,
  ⟨332061724690301901288775994376377012614121387013683792559349,332061724690301901293526512533791347102768219789408496125868⟩,
  ⟨884818481902266316485116066041489472749144369353870751854147,884818481902266316498723373731443188249083874751338402398830⟩,
  ⟨555175221462668316529530419857221069616172762046990681014598,555175221462668316535370575650886643614692177553287204153932⟩,
  ⟨779448475066488956847148627310902196137596777846545851411,779448475066488967114272023270483149184344774534734242599⟩,
  ⟨-17425267125854477432436970062759398134663049751959132029370,-17425267125854477426645490599652489375347394945306397245595⟩]
def bs0_2_0_7 : Fin 8 → RI := ![⟨-16596174749153516814111941741634784124097513622964424224111,-16596174749153516813248270777753153624799707706094540051244⟩,
  ⟨8291317507607984497352635469000276120528637136333277003474,8291317507607984497973757973867628240613153435890995967727⟩,
  ⟨-848748529520770146039070613159189486118553830235759058072689,-848748529520770146026061402688077434815212768041118315006605⟩,
  ⟨324290646016683146636346417194185633507593718922626394362811,324290646016683146641160156855371941697944050646898785093542⟩,
  ⟨873963059012415778846585497664136723005616733092100472166088,873963059012415778860373896011133498005564974637051476716646⟩,
  ⟨552956272429807753208189773575625261643282247280094404562189,552956272429807753214107652139605634721121009291292134387017⟩,
  ⟨531400743458019318995889188747306893841404426152860714797,531400743458019329399650938408271775198209498150711591175⟩,
  ⟨-15815504301063263549956252237429301057632140229738476727671,-15815504301063263544087697805131404559548468492061543131780⟩]
def bs0_2_0_8 : Fin 8 → RI := ![⟨-15938136673396607655990109612240631978791509262788316369173,-15938136673396607655114749403074525157126751962174612981585⟩,
  ⟨7965993307645601064960358468346806037734131604872674119930,7965993307645601065589887477095593730239835941581380544780⟩,
  ⟨-838583392499326241292133419410239480812635675467779391640770,-838583392499326241278948137427497718264689517450280030179283⟩,
  ⟨316177028040107410623100415488904968031527138359900147105766,316177028040107410627979306099931596745999480811548903633092⟩,
  ⟨862419608975186179681922417792812767168341879366044232790880,862419608975186179695897433471091260226245263257792548244146⟩,
  ⟨550276489470622171620493498158076225108537773949658124433162,550276489470622171626491471500069374871255202244779903350530⟩,
  ⟨305317037865922980324214204511799585740085129470628691119,305317037865922990868784350004226540584081361654818421655⟩,
  ⟨-14299143943063841114632423954207866982275968943067537315182,-14299143943063841108684442315151514136257711996179197802518⟩]
def bs0_2_0_9 : Fin 8 → RI := ![⟨-15266404950296619527560461137586692135942781990576740653215,-15266404950296619526673053284301606385976315983069148538113⟩,
  ⟨7633848577094299095110873338021898805768236608213842486381,7633848577094299095749066598788949796421954462062873739894⟩,
  ⟨-827730298216276813190099537904172395300280591282965277989180,-827730298216276813176732785958230888244407242176302579287131⟩,
  ⟨307738231176252330525866575290914797913889799868612973313695,307738231176252330530812614416545324609060729352524784221420⟩,
  ⟨850213118113554442276213647060118414234623100643158311317101,850213118113554442290381001862010625230349269994414370412462⟩,
  ⟨547147207344903308065314815257561027222913277947565968397011,547147207344903308071395339128507173982939284880462511946533⟩,
  ⟨101383170638149486044221082498091120709526581055289865907,101383170638149496733916888428745711480339186416020805546⟩,
  ⟨-12876131428814344355951356807848645263726283545094506841953,-12876131428814344349921512679204545711842575748923960450225⟩]
def bs0_2_0_10 : Fin 8 → RI := ![⟨-14583245574990842777892731361549355396963181753278614236270,-14583245574990842776992904604038601054405998954937530905324⟩,
  ⟨7295916365888792290897407129963994980673038528782028998419,7295916365888792291544531640271524671810226021902826247829⟩,
  ⟨-816214166225602639221260435770936491696450964388463711897253,-816214166225602639207706621684832296388588110089987093448604⟩,
  ⟨298992776747894993991555206871666061249115576031193382106026,298992776747894993996570463760000248249943646847095510484448⟩,
  ⟨837370629664789325223443629478196219528471642600487242048012,837370629664789325237809250524627617592964021996139695281322⟩,
  ⟨543581124173539897977549356242641805526000511136831080612504,543581124173539897983714974518994533804197805725688199892975⟩,
  ⟨-80408240167465412056955717911688524207338813890783179570,-80408240167465401217662060329556211295971489128219040257⟩,
  ⟨-11545927529467888542911327402434408494235599180250918282644,-11545927529467888536797098110365538450394539755572657106069⟩]
def bs0_2_0_11 : Fin 8 → RI := ![⟨-13891019301041627242105579700470870241071332477403802039493,-13891019301041627241192949234387349231023637707133259411824⟩,
  ⟨6953288175492460333898947110775777625416643340249384499617,6953288175492460334555279608698685324449388983535355767547⟩,
  ⟨-804061926303528486070464582922236620522496032963970270182609,-804061926303528486056717910506273322576740347215602515416256⟩,
  ⟨289960272315281766269109156427785768801208340703516211194376,289960272315281766274195775816837941206987002927878063598814⟩,
  ⟨823921131365780904706455043771145483161543685054857206262075,823921131365780904721025074415136793640553194997319699870269⟩,
  ⟨539592238725980339633859197499786989912812043543700326918982,539592238725980339640112546863215555416729372421100607490425⟩,
  ⟨-240253760898104365011690745600472962398501905944319884751,-240253760898104354018163891526712288201263426388968627817⟩,
  ⟨-10307522364762820798083899236614637167309155272470901484352,-10307522364762820791882670075578161907887841305610752127622⟩]
def bs0_2_0_12 : Fin 8 → RI := ![⟨-13192171361860736597896334735961478066787717099506844877093,-13192171361860736596970501483094143955457635869141355456627⟩,
  ⟨6607109697588557701173293996367537789426546314489042456588,6607109697588557701839121485253606238575497930224019065297⟩,
  ⟨-791302397922743331254500017377535571827702538005905115413580,-791302397922743331240554475439187991187410206791487848936345⟩,
  ⟨280661329171861808956864321379951540871486598861353204673691,280661329171861808962024527564266139583638397475783337986612⟩,
  ⟨809895429826873243622372537127218471306306832516697980047617,809895429826873243637153348602233758238122989269165551714726⟩,
  ⟨535195778963317274886815517815569550786832019575692839682444,535195778963317274893159332752343707314541258688742817177955⟩,
  ⟨-378533222932443651743492270026275050408690499834093579261,-378533222932443640590924931964460536120578440291533535884⟩,
  ⟨-9159453341919323072957047913562844723604355715034560607695,-9159453341919323066666107188594000485761597902045483424091⟩]
def bs0_2_0_13 : Fin 8 → RI := ![⟨-12489220349408251915065322657650285649483355324763661805589,-12489220349408251914125872486039204481146099509448054564813⟩,
  ⟨6258575903701525593911784513321247328654763213599387819664,6258575903701525594587404822657614907921661571120630313503⟩,
  ⟨-777966156960235725313365205645493042338083791241844831335817,-777966156960235725299214556242239918549739440978889165021980⟩,
  ⟨271117472530363563693106020401745629862013065169662240285706,271117472530363563698342121579148720443021264036813122122519⟩,
  ⟨795326012516671329003814423925713412107568707535811893803263,795326012516671329018812627796425079900884107442235590626803⟩,
  ⟨530408122341307596577243654260233716568073641130430612246252,530408122341307596583680772404999948636385880176540742641713⟩,
  ⟨-495801947191935082251507457178370188745872328666637892018,-495801947191935070934911010498699871014422923904609571379⟩,
  ⟨-8099826917728660801539101835550188387218041425304203435823,-8099826917728660795155635563025180679417812810199948592675⟩]
def bs0_2_0_14 : Fin 8 → RI := ![⟨-11784746322151165992911475514441012955132198332363388002454,-11784746322151165991957978404224078470413953839195802605174⟩,
  ⟨5908925507793893358484478885906496630285436619430989162710,5908925507793893359170201271214060515268567120005179899798⟩,
  ⟨-764085390606476743230735133776883379553864391442012436305059,-764085390606476743216372899651612634309787809624602247822825⟩,
  ⟨261351045018879925905707034601266795321311387467079190440788,261351045018879925911021427522086571127410402542568329271527⟩,
  ⟨780246898338509692557809149925538853334194900423064237032682,780246898338509692573031611404979963190850931835788725840892⟩,
  ⟨525246708483439100969574263790105691363687883348496638560106,525246708483439100976107631641510473097559512293812119647906⟩,
  ⟨-592781193283115241178986316940272994599614225880743094295,-592781193283115229693180751687149747635906929485318175649⟩,
  ⟨-7126343968700681495036867786558820474062481016795169199859,-7126343968700681488557954026209954458081973536990540080082⟩]
def bs0_2_0_15 : Fin 8 → RI := ![⟨-11081378225494512999134023989999600428362375747838138255483,-11081378225494512998166033140534834578810399735908719582314⟩,
  ⟨5559434834217462512505466912706339871698768596238603560777,5559434834217462513201612697666742040218888218362115282235⟩,
  ⟨-749693741598945859987718514127510432468344136343202108400973,-749693741598945859973137965259376609377365448666693941107906⟩,
  ⟨251385104196231527959598224164670632257551878344016326082008,251385104196231527964993399108263171716517818013809466157387⟩,
  ⟨764693477929386351415075645708904155616427686836684313364991,764693477929386351430529497913148639378607926922600923226092⟩,
  ⟨519729944934821673826318008999756733532931800315078620604349,519729944934821673832950688038449825628097653302946296889234⟩,
  ⟨-670346940952234522334501517630621190000463063158118048606,-670346940952234510674104682937205241255124682531895256522⟩,
  ⟨-6236328501944582581936306834929943098385884459103087039650,-6236328501944582575358909622834459764604471918228847656731⟩]
def bs0_2_0_16 : Fin 8 → RI := ![⟨-10381780718377327695084474086534049163242170945863427276445,-10381780718377327694101524959836949898987538298523985931840⟩,
  ⟨5211411133641702120458041906927060371280818399149387278340,5211411133641702121164945171309705092985042425718017956352⟩,
  ⟨-734826143046974293726942958766319544088308057166049254528209,-734826143046974293712137097962334364955412452366400629703316⟩,
  ⟨241243314878482209875119351952564622515055981876589634190265,241243314878482209880597898058792858669453519460608170045254⟩,
  ⟨748702344950971920602960277683390996425279686710033474187122,748702344950971920618652936902956133696172348179577287037955⟩,
  ⟨513877106801053677993614375099302820005888129558264691883134,513877106801053678000349548342310240733424107153759904739317⟩,
  ⟨-729517137449213482394121926848608767637620949633157525396,-729517137449213470553538008203807720369286251195947959162⟩,
  ⟨-5426759390031548647159713476185209489022949428669543114807,-5426759390031548640480676325021487345326592641727582120307⟩]
def bs0_2_0_17 : Fin 8 → RI := ![⟨-9688640509218918079457763194309951188501987175251509683705,-9688640509218918078459372489277207738062115788332711356601⟩,
  ⟨4866185399468284257165596663579090440231462421942042238054,4866185399468284257883604980944229929300659615523718359826⟩,
  ⟨-719518645244305550008073441415014819756222700487918063739380,-719518645244305549993034988859094051848160906727174755101252⟩,
  ⟨230949837142208650613237864268923679348326061637189918988320,230949837142208650618802475255404123620859067012379774727135⟩,
  ⟨732311119766648211173988729571346736003510430649078724957771,732311119766648211189927911647582572119076836617925384798643⟩,
  ⟨507708231160164444890615045911180184134010033475662942617479,507708231160164444897456024940529401049747608676143568176634⟩,
  ⟨-771437568703295420405057831352861109280557047955337670547,-771437568703295408378464994122400464872468011920018609935⟩,
  ⟨-4694304767562151185530614346425908363912919570507849290102,-4694304767562151178746653275430226165865779075423382797965⟩]
def bs0_2_0_18 : Fin 8 → RI := ![⟨-9004652312679434453480670629193235399449831763752738222751,-9004652312679434452466335180442504852152314890444362947083⟩,
  ⟨4525104746495708714414520383252410398901422284378886573582,4525104746495708715143995612867770993830966240069814040702⟩,
  ⟨-703808235977533728888302991341440824929422462019182206309381,-703808235977533728873024368007966032173515085305120697175509⟩,
  ⟨220529210933199896256392220623071496218598922728158231122434,220529210933199896262045700922579414811069154380817238769055⟩,
  ⟨715558267005423439964959859802891655604060483547206720619928,715558267005423439981153597707865522972774843096173913492035⟩,
  ⟨501244007208236928285783298566735731841819173812688747563589,501244007208236928292733531074612048820882144623736571975071⟩,
  ⟨-797366534325768101895966475006889388853042586963121415176,-797366534325768089677303599881088727658647398886789634791⟩,
  ⟨-4035358686638964622189028718376368110615671310181981570913,-4035358686638964615296724771073639403443396227185902289868⟩]
def bs0_2_0_19 : Fin 8 → RI := ![⟨-8332504545551757080708767830179344488733113406534131316319,-8332504545551757079677963424608066033085976461453576136661⟩,
  ⟨4189524421958525477594824842790061039799507893754477080607,4189524421958525478336143980721112518754720835845780072882⟩,
  ⟨-687732655929837643321884786907631095676532010763840156689462,-687732655929837643306358096735638524879210232904783624082981⟩,
  ⟨210006238260068982651036432955627611759421048228959380857085,210006238260068982656781704312101771362862836006660317036147⟩,
  ⟨698482908600291567112451474613315813453861538083225114277312,698482908600291567128908137343302071612428773618333283377430⟩,
  ⟨494505663158522746736227726553697844007664280619016252777082,494505663158522746743290804451390430551309007856493673435628⟩,
  ⟨-808658525822598568536412502262040664527859384139730957307,-808658525822598556119364929548897879751027635240779940319⟩,
  ⟨-3446079593955766665244169392245446820530990061138768760610,-3446079593955766658239960595089367475318671350607524389914⟩]
def bs0_2_0_20 : Fin 8 → RI := ![⟨-7674864885344203149272224832294078984384116203770017447401,-7674864885344203148224404935634703333366260948422572985829⟩,
  ⟨3860799526290386920178162702433972798028158101710856980400,3860799526290386920931718797361685765729508824434228643778⟩,
  ⟨-671330210847724960289637594612410167717014016201777902708522,-671330210847724960273854605324083279393449320345539773923427⟩,
  ⟨199405863989411628140677308880634191208544180617521255155325,199405863989411628146517417446823832219411527298727817436484⟩,
  ⟨681124633952804988171474760794556272489517689644109210690699,681124633952804988188203073700421963616289823210066647138591⟩,
  ⟨487514850958175135781550743972688532342684382094056506237422,487514850958175135788730412116241550132231667642895207428618⟩,
  ⟨-806747123517578064945338171308690651386270479987058494553,-806747123517578052323322361045731080576207906227903721474⟩,
  ⟨-2922430164677996908882148669349175405692882619268774573944,-2922430164677996901762321378797367145025978278865088142845⟩]
def bs0_2_0 : Fin 21 → Fin 8 → RI := ![bs0_2_0_0,bs0_2_0_1,bs0_2_0_2,bs0_2_0_3,bs0_2_0_4,bs0_2_0_5,bs0_2_0_6,bs0_2_0_7,bs0_2_0_8,bs0_2_0_9,bs0_2_0_10,bs0_2_0_11,bs0_2_0_12,bs0_2_0_13,bs0_2_0_14,bs0_2_0_15,bs0_2_0_16,bs0_2_0_17,bs0_2_0_18,bs0_2_0_19,bs0_2_0_20]
def bs0_2_1_0 : Fin 8 → RI := ![⟨-20652456903227746481567526807749473840494437677494819037491,-20652456903227746480776601110582301368942362186943916208726⟩,
  ⟨10304471390399633489876378887268279104445348174050735525203,10304471390399633490445185493879071692629751594849082672239⟩,
  ⟨-899013312094494093452844344614760460740572155281698330667359,-899013312094494093440930873754083574582347550094497248306791⟩,
  ⟨370683870197844953611699940412796721656902451512765617742129,370683870197844953616108228472325540681271192323625469013461⟩,
  ⟨934384170158308385259065624808185094495249391889946912747698,934384170158308385271692654118335387005904926485447104732151⟩,
  ⟨558359944564634581228558918328539221943159382525064656217457,558359944564634581233978345893588571783897722357541999359954⟩,
  ⟨2694110906225691968816864063420700384641415736103311911764,2694110906225691978344337903873189775887177880435667884528⟩,
  ⟨-28985677204130445349865796585653469128278643734499054786174,-28985677204130445344491538679730221996582249001122863601257⟩]
def bs0_2_1_1 : Fin 8 → RI := ![⟨-22177709020940419886593524590006237118820400597816786594359,-22177709020940419885774123986382032226908756507055769596986⟩,
  ⟨11066940768929109545400832177031378708625101492920425426116,11066940768929109545990116958736806401123310128098666172617⟩,
  ⟨-913531360417670097163449768097925371788381271578555107228559,-913531360417670097151107388466718756204090230204865841974419⟩,
  ⟨386954532935689392881406465622041920340996591143394245208341,386954532935689392885973460865575316529383835889203635508175⟩,
  ⟨953369126916215897178552845647052431925030783450685993631888,953369126916215897191634473258640812159083754617280579413353⟩,
  ⟨556253390081944950366060778812871395472246957704998048550299,556253390081944950371675316605825548601439091519961280930424⟩,
  ⟨3789382038423861650798647844601531147286357142282196197945,3789382038423861660669129792267082756993366420487846309181⟩,
  ⟨-35416070877540285988572913267405999038536103014812758738864,-35416070877540285983005171331712738588680820124340137570204⟩]
def bs0_2_1_2 : Fin 8 → RI := ![⟨-23466816869073780807017987212652299857176922488111166994542,-23466816869073780806167554070804062169626308130683246450921⟩,
  ⟨11719657085915043610216615623773534093504872509354479654372,11719657085915043610828217941529053637839193082917165721186⟩,
  ⟨-920858779866423739994828893953782435328623902054218935340370,-920858779866423739982019080730258671802756001091963371492575⟩,
  ⟨399452257803563117050901119498764651152481911533936971639724,399452257803563117055641077092904271045776927106341186560470⟩,
  ⟨965241824303855621022526505705691993626390470157348556161876,965241824303855621036103563888310852585838427025382313003838⟩,
  ⟨549665928137807649658341698547217794243955654619900531496798,549665928137807649664168871476115562940607609405353432759536⟩,
  ⟨5035936457392060684066142136218325834406762987570104133745,5035936457392060694310441368031830581660727347355455733701⟩,
  ⟨-42596074031898794949601551143552185660384257325670616407618,-42596074031898794943822946336066226948838359207057395859200⟩]
def bs0_2_1_3 : Fin 8 → RI := ![⟨-24482106968189462352725281979500298246032625359221043155533,-24482106968189462351841011596543930260685777952944666072342⟩,
  ⟨12247520100437706135479691353248927994523584717745228267773,12247520100437706136115628253074665551603283904180369835585⟩,
  ⟨-920761418228605735986152367195838297019871793584855275080259,-920761418228605735972832874001855325202832727004047357359802⟩,
  ⟨407925754478313113044459097644604507522678165074968175581730,407925754478313113049387649826718409799584775714029078448945⟩,
  ⟨969702928717645058605065701570092671834271659920663618792199,969702928717645058619182967052655538489883655459337780519564⟩,
  ⟨538533745208836445101276044359014197774635914369882611699749,538533745208836445107335070264655139843482039203272011301597⟩,
  ⟨6398074447292295672057354877698567603374279544845671446361,6398074447292295682709256783925703749346972932573841237587⟩,
  ⟨-50446952560293663199146729955436683666846533333868535072814,-50446952560293663193138204611574779768463514813013050404706⟩]
def bs0_2_1_4 : Fin 8 → RI := ![⟨-25197209730283218269873561184975995963577091583849409982269,-25197209730283218268952366845195667031363502255310601051761⟩,
  ⟨12641120101452809873950735015068499701038866785819647329046,12641120101452809874613226356930751892243178986822189632321⟩,
  ⟨-913203571541284283645339803306426224138268872343840790827829,-913203571541284283631464135891171318378489693637210486873120⟩,
  ⟨412239348989995717568372917977105058268260792185451734149668,412239348989995717573507268805787932860836631500049189032534⟩,
  ⟨966649812140212706412186638287872552129341667919580184599960,966649812140212706426893390098695199955727536168281676544658⟩,
  ⟨522917884142584681262245664089033302174272640152379958687670,522917884142584681268557693165813851143911828732167008826638⟩,
  ⟨7825720168135169621709300456629940770860829278597819822756,7825720168135169632805987548005588664826414974114752037482⟩,
  ⟨-58850903381474201890704953492539719816670772285764981897652,-58850903381474201884445533699838897142835322290091396234726⟩]
def bs0_2_1_5 : Fin 8 → RI := ![⟨-25597875360379683284453625692914028166217447005122732172728,-25597875360379683283492096518713180114280510024737696122298⟩,
  ⟨12896709477302959215644846879386847783972502688428998821159,12896709477302959216336345649347001699091266019180230234896⟩,
  ⟨-898352355285899261503341231548456608757641259460169632270568,-898352355285899261488858012910266485176680836628873795341327⟩,
  ⟨412378359115046534866891962491952203239181482122908411213803,412378359115046534872251122768144006776189029922997301865424⟩,
  ⟨956182624284569466715308697669780678748577378315100772384580,956182624284569466730659390040849104910841730711167365802352⟩,
  ⟨503005632345385705454873030311490832978069288775615803421821,503005632345385705461461433912938228188645185529866331319958⟩,
  ⟨9256149438253779019099041111975022375756809474282723826907,9256149438253779030681600746235409018661198782940693158500⟩,
  ⟨-67653577239997974480242836950095963604254354513112130669754,-67653577239997974473709346149806509183076532391744102346211⟩]
def bs0_2_1_6 : Fin 8 → RI := ![⟨-25682048154056534890421130319518118237883599737519954539257,-25682048154056534889415480648162321286225284857557278063465⟩,
  ⟨13015771421579365156671727605830658546298964117555478435083,13015771421579365157394956322553665324581722142146062776458⟩,
  ⟨-876571202458279493404286780356325340275363797005022651937701,-876571202458279493389138988220111567570945066304447893310267⟩,
  ⟨408447953453345751431461062092564514419834005699216991529472,408447953453345751437066131512350614218922324008422452066934⟩,
  ⟨938599612510178912435364642942018642004645209232078236766084,938599612510178912451419713502924717144666707696966570650353⟩,
  ⟨479104973209941556792365117729557353357624055324692946053034,479104973209941556799255835239188108749023319974138154057783⟩,
  ⟨10616952813517548943876358506633390588048420696786797121471,10616952813517548955990392695176239206282949809817415234751⟩,
  ⟨-76669415127786230899717515065818159064217717570305697841316,-76669415127786230892884230073133024320448318428163498860543⟩]
def bs0_2_1_7 : Fin 8 → RI := ![⟨-25459218326356204844435796452120636298802089839056197417687,-25459218326356204843381805051962894803554287465091459604602⟩,
  ⟨13004262713476982366566997609143270635170407932349434096981,13004262713476982367324992037501496672769330397152740345232⟩,
  ⟨-848402863345071604355713841677221726778250141986750701323761,-848402863345071604339837892927140854712297639063529851133201⟩,
  ⟨400665604683634446086938069991100237579436235176825277849143,400665604683634446092812575928974298779869344094507327061281⟩,
  ⟨914381976586752303416353622643725347219280421566852580093145,914381976586752303433180462826987697016150963125637096955880⟩,
  ⟨451632378917408416028877442094248160136106105080376543408805,451632378917408416036099397416353092506013818597118921761315⟩,
  ⟨11830032137993014158349849533235809180803164691916767852587,11830032137993014171046207141155040610949694882573364322298⟩,
  ⟨-85689492374150971963084557796100038223604359381913418571697,-85689492374150971955922795780723555025888082247011172783868⟩]
def bs0_2_1_8 : Fin 8 → RI := ![⟨-24949138798605168887066879604988328717722451230315320347296,-24949138798605168885959816492318253499020076697438994162843⟩,
  ⟨12871643967114327444510199964714548196349336033544436728972,12871643967114327445306361746597229407691865625967375649205⟩,
  ⟨-814543259512636452946623782985065988600024983950005964465756,-814543259512636452929948431329195172007180827970121033368306⟩,
  ⟨389347831579258815198802107974192409852664287968523923815604,389347831579258815204972413375240624388309834898689982790190⟩,
  ⟨884169507094231107183757259429118493736279282074085808396665,884169507094231107201431382829984403375948146981737938756266⟩,
  ⟨421094854230202863423641416816742845976326500934336697950506,421094854230202863431227019827770961781920832354901219572472⟩,
  ⟨12816297151732298957572494804527782016621349529975321550690,12816297151732298970908153113264814199783202546875854418714⟩,
  ⟨-94491279439829822589465349310488493452327476438979589676711,-94491279439829822581942970524733031934250441026427665005363⟩]
def bs0_2_1_9 : Fin 8 → RI := ![⟨-24180049949741794402225443462272225222291151495914379002165,-24180049949741794401059981346870946646084985071410245575536⟩,
  ⟨12629827114212271992565384304259178975913613537189291555834,12629827114212271993403544643888958154105425339177796202415⟩,
  ⟨-775808354848861886268800864394501943925028157690142145508122,-775808354848861886251245866496430094172367676966030562527658⟩,
  ⟨374892418654526826516341078251430706384681295829948810445207,374892418654526826522836875196662352595370670819592365925979⟩,
  ⟨848729061760630757581527090160276420093464115378176599684267,848729061760630757600133546297303981081103181166981866964648⟩,
  ⟨388067662484413756965270392675826810569568735980230000881934,388067662484413756973256145999968684861851369932134261101494⟩,
  ⟨13500638886666567411500875820410086879898102189203088734721,13500638886666567425540007252683166587447960008873371439753⟩,
  ⟨-102849514947431318060358006222816539238713559599250218007526,-102849514947431318052438812283352337526015537005978757489819⟩]
def bs0_2_1_10 : Fin 8 → RI := ![⟨-23186589994549740806580353551146690626898342083705530983815,-23186589994549740805350459954045833605887293311489482965374⟩,
  ⟨12292163065810859583358261003072511281437945424159452363931,12292163065810859584242758252209225839824828454563000539474⟩,
  ⟨-733096728600326544829757684888249602913426238355326559046896,-733096728600326544811232175370014434453659258751780512753373⟩,
  ⟨357757634740515057809109141941670971327936045271781810444092,357757634740515057815964052938376009053621279305486248748800⟩,
  ⟨808918464519126128293343475867641044397246443808344070815301,808918464519126128312978572509113392817624263109088392703305⟩,
  ⟨353169498039818555934074132208146200637610069433873511289453,353169498039818555942501370427089827522584084948268259772835⟩,
  ⟨13816724716700723967182570515240348894965115083715066262552,13816724716700723981997842182185524549221839533020720428775⟩,
  ⟨-110547280321262379626325113551546051560061403690750173078250,-110547280321262379617968114390786540184450370619183227725411⟩]
def bs0_2_1_11 : Fin 8 → RI := ![⟨-22007578527121540555536412688909627693121918357529250916553,-22007578527121540554235217433929321994704501688942149874311⟩,
  ⟨11872565634465089276250963233264154667255297741703243789082,11872565634465089277186738186741241003410641120235570571320⟩,
  ⟨-687350706574649673989733595396724393991427461583939287749548,-687350706574649673970134090904546490397995282301444902762186⟩,
  ⟨338440103074339222771009289612633521658511532244274048843978,338440103074339222778261606140965764487212116438325757753916⟩,
  ⟨765648604248174860958476316476123389538211374633982577781626,765648604248174860979249735120984408517962738910569270504193⟩,
  ⟨317036973247347630408428481676807484099453232548621724105267,317036973247347630417344279278506317127814816431627226148563⟩,
  ⟨13711190539140357466171193796878915187472799664440175092439,13711190539140357481845363692115870151855975695316900246130⟩,
  ⟨-117386380763250893856413747370278293615003491202039105804101,-117386380763250893847572260855153565565501371388150464830783⟩]
def bs0_2_1_12 : Fin 8 → RI := ![⟨-20683847238493442532093607789749602375812817242373448718174,-20683847238493442530713238712688763639561856400597573666729⟩,
  ⟨11384829273867997473569050109808167339571200807745822633343,11384829273867997474561764157842356861485461130511270836602⟩,
  ⟨-639518736734015846220173782788462108117114482672456289416188,-639518736734015846199381707330736407978275301570934614538406⟩,
  ⟨317452907766775746706189941298010133632950386211205190417338,317452907766775746713883539499044767319938629343707678532788⟩,
  ⟨719846370434192930775448065004640069012631508087649907668427,719846370434192930797485483764615600683514297850012372377975⟩,
  ⟨280300169003937433922448258824237689644789622791307160097520,280300169003937433931906555924513918140748475147928548811706⟩,
  ⟨13146890067441595674710103253261908395399255019566297109452,13146890067441595691337999296432812961986234150568433264384⟩,
  ⟨-123196263098310025013127856958525801185812591280284397417045,-123196263098310025003748392551506653933445522475449930061369⟩]
def bs0_2_1_13 : Fin 8 → RI := ![⟨-19256260642451142923124245983825955025897877585278711011928,-19256260642451142921655623089556652654132401159331384024421⟩,
  ⟨10842158103339214324806002740604846692869379325999581339950,10842158103339214325862185903946618866494931912356788520522⟩,
  ⟨-590521257129641389332129331029925589234772344919056279149132,-590521257129641389310007915428753975106072547375909350681580⟩,
  ⟨295305293708001037782886312859773032706278286780721450649882,295305293708001037791071800817516689344116468698788947413310⟩,
  ⟨672420659104215402696388766183709245601474132027865913222538,672420659104215402719835146039415196726081872419773492609429⟩,
  ⟨243560703854782003959468474133646850231978386680838378728211,243560703854782003969531486913002423872290205215980547751210⟩,
  ⟨12104980894616227931819144670610185604505853637105913159639,12104980894616227949510144286566789340568657882558065778026⟩,
  ⟨-127840905573635552915527438171040568916566577096078091872489,-127840905573635552905548298248989654304535377985366617046069⟩]
def bs0_2_1_14 : Fin 8 → RI := ![⟨-17764028739605596071320320610969956706987169661500465390176,-17764028739605596069752895168841393567461222477120343942525⟩,
  ⟨10256889984614273132234409498935471689536215839534623040524,10256889984614273133361648062496780695199121611885337364257⟩,
  ⟨-541221704819390761107282360886492312287050843094320898848309,-541221704819390761083672712851884919437836893204937286989441⟩,
  ⟨272484988856763207181592932614694979400551950468718469659588,272484988856763207190329104528861029510870110098366841690380⟩,
  ⟨624233116237308723231266773518219859755125581335213366009575,624233116237308723256290523628234400032813761807189936593977⟩,
  ⟨207373377649546812433341753882305350736292337083479657835611,207373377649546812444081762305762232054367480206208179222486⟩,
  ⟨10585759088518378487167992876074879400738512296567917674746,10585759088518378506049165845996569293735259957036975569075⟩,
  ⟨-131223356607058250224303176800447494477225976027036581806665,-131223356607058250213652683835007273529258250812900215606872⟩]
def bs0_2_1_15 : Fin 8 → RI := ![⟨-16243370539536545518754384441601569586096801717188475302166,-16243370539536545517075804059950317494711236893088259235567⟩,
  ⟨9640376775046816806201560599414470697324523398954871172332,9640376775046816807408737979181866287140152865352991459025⟩,
  ⟨-492403662701098075368339107451115226476582307090915126805994,-492403662701098075343055166701203251827395376313540307091389⟩,
  ⟨249443811284637674059361278771774055875117795570684140151448,249443811284637674068716981691969703558619735233732212586107⟩,
  ⟨576074661842995054054627706807116722579861976449734284044780,576074661842995054081426031551314358217238419534260598996470⟩,
  ⟨172232013272954127618795985430548906697327701324408813578806,172232013272954127630297628159092401192701571204860555790722⟩,
  ⟨8608278100432692968150154949956061007317655549911582985196,8608278100432692988370297916552278095040425559429513273129⟩,
  ⟨-133287839574089968043377862965545590769468492167632045086355,-133287839574089968031972083739246862246346540081739040612796⟩]
def bs0_2_1_16 : Fin 8 → RI := ![⟨-14726548091910861558648030824170460384725827275905833863950,-14726548091910861556843703441063388397327010766868408319794⟩,
  ⟨9002972330029460367513793119116478172450577673784948164311,9002972330029460368811403425039128363938446697460270408082⟩,
  ⟨-444754525311014355977444417211407361208969594322802927745535,-444754525311014355950266387998914705625190859960354916480977⟩,
  ⟨226586869613480591156896383833506838437030399774870284113477,226586869613480591166952947791937042313075595854658325465558⟩,
  ⟨528648241713278174827856334880422408804326909737046177357234,528648241713278174856662194692943657985903262874662182018112⟩,
  ⟨138559712041480986315258860817060367597408018048443198381455,138559712041480986327622122745655692257192366185083935292585⟩,
  ⟨6208889100634443677875195749313909444103591672677215951627,6208889100634443699610084374900294001535808478757639518376⟩,
  ⟨-134019549357626832752756336229624354154241486095783859599970,-134019549357626832740496119198302343041929984346828911368165⟩]
def bs0_2_1_17 : Fin 8 → RI := ![⟨-13241258768069483317746276246373377656466495438552178693467,-13241258768069483315798793637710048917590092879092259299533⟩,
  ⟨8354080282958430626194604909658160661021634556696045531532,8354080282958430627595167538827704896989860135137069542870⟩,
  ⟨-398855543820089622611822676633379954631579360982818862446986,-398855543820089622582488344225226889785336954104149543050569⟩,
  ⟨204265360032091444705522879191680198815264360872397197105068,204265360032091444716377330327160894054754824427341811911117⟩,
  ⟨482557743969039717130511434305922399417530040811283177796127,482557743969039717161602749295836325479872975624304610696238⟩,
  ⟨106703394111820104352145792518529592688104150581210770516145,106703394111820104365489954902024667134203775101547199932046⟩,
  ⟨3438910730871704151961828782076985089597285596049269801072,3438910730871704175421162157499637293594633789923191829628⟩,
  ⟨-133442425838708053813746776120946274397891402835240837958527,-133442425838708053800513834211215737499152184162989905524551⟩]
def bs0_2_1_18 : Fin 8 → RI := ![⟨-11810350349026772077894767427097421792965317889910400725407,-11810350349026772075783129518196893608204369244393539832725⟩,
  ⟨7702222998601364050987755515168090601840565878295322824168,7702222998601364052506373000293429074209957693584733490573⟩,
  ⟨-355177713013107954112339911808065966173294252832967844253550,-355177713013107954080532958529037503204332699313050167505894⟩,
  ⟨182772724017711391066092703313325334726062450296108244810274,182772724017711391077862087233116504062533129617283478932518⟩,
  ⟨438302622926627859334181560932073585390970544690675857006640,438302622926627859367893594651366264062565139829728377502918⟩,
  ⟨76932233513321153128121898913548615295258255477271639662523,76932233513321153142590854388283190782879264035976675047582⟩,
  ⟨361675384033942314197129778779893962091439534689852787969,361675384033942339633874349256422518631302912628177706345⟩,
  ⟨-131615293910027909917221543081306980416164221526823643346329,-131615293910027909902873182968417821951309604019816199518218⟩]
def bs0_2_1_19 : Fin 8 → RI := ![⟨-10451809775359622814428950960392633548451415035847586173175,-10451809775359622812127500878377521041517807230214208250773⟩,
  ⟨7055113837543852825886654789251375894082396384581721231841,7055113837543852827541778672420838367890942641294132412227⟩,
  ⟨-314082704965405636746920570875164873367525103128766664060637,-314082704965405636712254535129048400114764182215307887871182⟩,
  ⟨162343769045904515634924045298468402428180129399364695211050,162343769045904515647751362649565948338404295842678553962963⟩,
  ⟨396277510432968800949029793452233098467502596481912572324708,396277510432968800985772154650598208436835410460068237107906⟩,
  ⟨49439428561442563724219296774912136098929715161167666795914,49439428561442563739988846386099557962874338614708398899933⟩,
  ⟨-2950792384176561065630153148831172091258289329455884309403,-2950792384176561037906935247773128148536279523567184955635⟩,
  ⟨-128626807797702812923055090098314586494689011247979068473164,-128626807797702812907416975997789734734920335149280975316338⟩]
def bs0_2_1_20 : Fin 8 → RI := ![⟨-9178961087655233675113381885294294211259871784627735100010,-9178961087655233672590308089945797125583350601653736147645⟩,
  ⟨6419384613463018291092849600768829992437028155813490227613,6419384613463018292907357649512404454658430964763690619846⟩,
  ⟨-275827807892484018567379215593739138686862295690972780907992,-275827807892484018529374929920433278444522746729445837427796⟩,
  ⟨143156200841093753118095715903254096705894404232230554656951,143156200841093753132158270866684331944941578749896586312161⟩,
  ⟨356775845330526233941645600168564704155151020964003395563382,356775845330526233981926156085972249167458433129388821754701⟩,
  ⟨24346591276997627552396898180902093474032109842605241701485,24346591276997627569685014790895252731703776418691442307943⟩,
  ⟨-6421204808203235928027159063594863791278597930469169487614,-6421204808203235897634266706807223404558097110977673668811⟩,
  ⟨-124589677748266911491212475065207161837997830402991419704052,-124589677748266911474068450867687343823496095709236658840362⟩]
def bs0_2_1 : Fin 21 → Fin 8 → RI := ![bs0_2_1_0,bs0_2_1_1,bs0_2_1_2,bs0_2_1_3,bs0_2_1_4,bs0_2_1_5,bs0_2_1_6,bs0_2_1_7,bs0_2_1_8,bs0_2_1_9,bs0_2_1_10,bs0_2_1_11,bs0_2_1_12,bs0_2_1_13,bs0_2_1_14,bs0_2_1_15,bs0_2_1_16,bs0_2_1_17,bs0_2_1_18,bs0_2_1_19,bs0_2_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_3_0_0 : Fin 8 → RI := ![⟨-6143646843334063460195708629053276910607080844165297533144,-6143646843334063460085241780186167184745633146690839349821⟩,
  ⟨12688037359324949881537512401317387533083723131296658291746,12688037359324949881616956366373410513137332679436753698281⟩,
  ⟨-207837781210653771207131112260890982010541518102335853347533,-207837781210653771205467184043901386629627055216646934839142⟩,
  ⟨114527054806539052468760546830813454828083425764815598083191,114527054806539052469376242707907747280951614708176189367861⟩,
  ⟨186798171897991910196711678966516572206050601118011232179159,186798171897991910198475268319428038829140916280098272278394⟩,
  ⟨165850365769303261383709390648162461208633756929522686581676,165850365769303261384466310151385760390805241033284969382924⟩,
  ⟨281813115136500132032360960913553711929450896229534060488592,281813115136500132033691642185630669988122339683719788041938⟩,
  ⟨-216452729427083700478140365083133729945819919395371060633609,-216452729427083700477389754326660641132062567320566214855739⟩]
def bs0_3_0_1 : Fin 8 → RI := ![⟨-6702431293062945955036399511729858844513481459548810569434,-6702431293062945954921157136009469469510940512517733413516⟩,
  ⟨13061105025339611979222137151378980069653738214693435657769,13061105025339611979305015511389857422506614531501045369062⟩,
  ⟨-224773148801982098035163048350398444479939453276430746540728,-224773148801982098033427187839114611412556173105116263675621⟩,
  ⟨123633564859312644273679371968263076566785507919130107764754,123633564859312644274321684628809080600530306943770309249900⟩,
  ⟨201489502554838562798527036949724262829976236932221109476710,201489502554838562800366866988419939152294617508078181740860⟩,
  ⟨179622955521683529176663231078768430176700313305510485449658,179622955521683529177452872520306946302446900031450328609301⟩,
  ⟨282686768143272333218558827235906572675870317814476388855732,282686768143272333219947034401157868528064630641737242587604⟩,
  ⟨-205563530986720197206205515494815376333836806377000157404008,-205563530986720197205422455529729199485546153758349063923346⟩]
def bs0_3_0_2 : Fin 8 → RI := ![⟨-7269871440310711596032977495609199984462062687310291342919,-7269871440310711595912635805545569549895681957209098486104⟩,
  ⟨13357621887637725472858853935130654413697664227674549535142,13357621887637725472945399546942550407626219861460755650416⟩,
  ⟨-241677213003566437968624836820415053342630814433250446356634,-241677213003566437966812166903319491939660181928376637076795⟩,
  ⟨132676675583395492690091084754597254754618938224996118403912,132676675583395492690761818854242675120602816393905805440609⟩,
  ⟨216028496383864813331769351285490878208428220891167079135181,216028496383864813333690591236539223389725073493760746946611⟩,
  ⟨193438484206774671218835479431026658764851940467463693271639,193438484206774671219660061404682660257344795756298409924230⟩,
  ⟨282412738103227102083812890135054208300967179532033264631766,282412738103227102085262523530579250644690798854679805362220⟩,
  ⟨-193310578927729589997909735949312684690784659651843501385042,-193310578927729589997092026673272889776556857469149365315511⟩]
def bs0_3_0_3 : Fin 8 → RI := ![⟨-7838546724256477822470608671872503312453526529763489934254,-7838546724256477822344810035735922007687872173060976425127⟩,
  ⟨13571083248929681384074370805798927951262089290964460384982,13571083248929681384164840865873254893630361505687918303439⟩,
  ⟨-258311239930383640653364665339338316537123503214347113939744,-258311239930383640651469799119524653202553501018863506374222⟩,
  ⟨141522573220257991216118677271719747628618338919907663926178,141522573220257991216819826099707806090958095583984794094226⟩,
  ⟨230188378077970818694325545656633896982682000999169127640002,230188378077970818696333905065635912528323373987328853109856⟩,
  ⟨207115332204467358900868890886540251232912780063212530455937,207115332204467358901730863887047656212548510157916202844258⟩,
  ⟨280967365412261037522655890700128854595206375504671524242889,280967365412261037524171258350006825393562421122054517769987⟩,
  ⟨-179759671629934702577852692460984863061103243728199383719734,-179759671629934702576997903803559540762268890884287636016581⟩]
def bs0_3_0_4 : Fin 8 → RI := ![⟨-8399989583578067687723943112882943067515922376706978331208,-8399989583578067687592291906773127466222816505032286536098⟩,
  ⟨13696503946156205083859549631732923138272858670953748559026,13696503946156205083954228659195778997116751584781723922553⟩,
  ⟨-274415000441092900265240220749873698259461820502847328541253,-274415000441092900263257199066038590693461659012943814629179⟩,
  ⟨150026650340974456290882825605995287061064285780705197476224,150026650340974456291616594203991190046375111360310479820438⟩,
  ⟨243724135482631417516707343902442389019913394341636026506845,243724135482631417518809138855225759598842409910167321821146⟩,
  ⟨220454610328250335946408200409750996641843981623462032783194,220454610328250335947310275254422021456772672630710749694916⟩,
  ⟨278345568792707696585159622902749007449877109819365950111357,278345568792707696586745490483923830694226984583942274436353⟩,
  ⟨-165003764142276697519203293355434730164769855954985087312951,-165003764142276697518308737093341765314783845933991823561789⟩]
def bs0_3_0_5 : Fin 8 → RI := ![⟨-8944790823236432643800522846684316435817044460671501502006,-8944790823236432643662580715673986181878313730424621019559⟩,
  ⟨13730670682553886689858784013796426434928873886580027603760,13730670682553886689957987258461434172486063962073554992055⟩,
  ⟨-289711559613737840805465206563696359529296532842955879725774,-289711559613737840803387426610200614680466540077403830088316⟩,
  ⟨158036384031744733638652826476118293975243148033163336584533,158036384031744733639421658050607106285844616930318095306524⟩,
  ⟨256377355835100381934076436447646612020569460361382486921604,256377355835100381936278665225512729259761946669449990322210⟩,
  ⟨233243632827916772841977743107412409458331920915699111807557,233243632827916772842922923406809926402962497635674713752489⟩,
  ⟨274562013659024556124470374824833543918885402942587636862971,274562013659024556126132022751275821537226568978341809251703⟩,
  ⟨-149162793623438705031244182283890149236174195965068629679045,-149162793623438705030306879840960375512248473178380234099990⟩]
def bs0_3_0_6 : Fin 8 → RI := ![⟨-9462766173110147324641379742928298680411789225215530618890,-9462766173110147324496660158193528878295114930799552925033⟩,
  ⟨13672339557396598775303487865891806520693565041159047671736,13672339557396598775407565222585093224250371808562525874262⟩,
  ⟨-303913445750249566628889632054634239702421454496092111788429,-303913445750249566626709765397228954059074655966066976486533⟩,
  ⟨165394960279933574609839107802980693354362089265242968992837,165394960279933574610645714061539609082599972829515925579855⟩,
  ⟨267882335993511095048432176793380682817933559062249206020279,267882335993511095050742606767834286955226640127863974274192⟩,
  ⟨245260419336263257757359113756044080931511254076746576583345,245260419336263257758350733208556771729115297546378630513725⟩,
  ⟨269651709072571188901114779433417364566628775445259219538759,269651709072571188902858068420814377435444433950530539074758⟩,
  ⟨-132382552911516247982406648202247244335655434099508651762788,-132382552911516247981423293665690914424748939575297945323352⟩]
def bs0_3_0_7 : Fin 8 → RI := ![⟨-9943188502648052153960700051917124739433782793126192081094,-9943188502648052153808662032242268528960159620514532637839⟩,
  ⟨13522355689360992914464247920334531000865545920190352338411,13522355689360992914573588444172826332032072145290129380995⟩,
  ⟨-316730147818784489899520613554544293502651589768068542005900,-316730147818784489897230511559327785355482952472533823767054⟩,
  ⟨171945600330161619948854626753810369687109481051847096939686,171945600330161619949702022898806606072650150346970665080390⟩,
  ⟨277973399527553233352532029855746365069240267147635319364594,277973399527553233354959297723880119392972243980362809283331⟩,
  ⟨256279188741032495832411840782028845574912001062121368405687,256279188741032495833453606194156764854156407003053019980529⟩,
  ⟨263669947284766858227554538020333782507275287331089634252591,263669947284766858229385984716705336116958256259722822813511⟩,
  ⟨-114832540771085774493928734829676928631388054461536554778568,-114832540771085774492895652288362243032506774667216825477244⟩]
def bs0_3_0_8 : Fin 8 → RI := ![⟨-10375086509703410275583813072740653898470092437405968951995,-10375086509703410275423853914812249778098659942559514689056⟩,
  ⟨13283674639818547617513466002672106980195016952834707849211,13283674639818547617628503137185772209070343972688137715102⟩,
  ⟨-327876797074773815742494413922695144191446582302665832478291,-327876797074773815740084998254762788637171257206820728390578⟩,
  ⟨177536491694850428708055004644164616688425193225534708146611,177536491694850428708946549891047720149394777801989655099293⟩,
  ⟨286393264182873093295844304345523410613087096338536309648866,286393264182873093298398032189961720114430944003541985107736⟩,
  ⟨266076740248912169149691922262469386891740016227858039745956,266076740248912169150787963360893291593707815907511761214313⟩,
  ⟨256691525682212234185184115055568787335259955849105196290036,256691525682212234187110979611989497255476433558421886064366⟩,
  ⟨-96702765237381187702300964662581932079895180729820738873155,-96702765237381187701214058810137744964608982986734436219878⟩]
def bs0_3_0_9 : Fin 8 → RI := ![⟨-10747605803510330889036034096284279878052221649135998182079,-10747605803510330888867480927490019415297506464166898641225⟩,
  ⟨12961272339579772824086868176331085494169109901173841908652,12961272339579772824208085828401075757978324592057222953937⟩,
  ⟨-337083782482929848671037350899341479209704264679070636152589,-337083782482929848668498486285190905639461058424295875113081⟩,
  ⟨182026167339928672687519106670895315031802956487118178117808,182026167339928672688458551329352332682474348379441298411514⟩,
  ⟨292902202816399198871553940971489615605837528079965592539054,292902202816399198874244871118891122916438129746847362717890⟩,
  ⟨274439540418441607149104912256509366179496626265581869362452,274439540418441607150259839568362367659758157040439882796735⟩,
  ⟨248809225635972126983569178042416762661324155409278079002550,248809225635972126985599565867816901216390737604642346752480⟩,
  ⟨-78199535636344266573378700003426948707272470018611180786543,-78199535636344266572233398740389747041126136172757542047279⟩]
def bs0_3_0_10 : Fin 8 → RI := ![⟨-11050422278628152025545756883298867478633760072902908918769,-11050422278628152025367856811605813296306068189947674298870⟩,
  ⟨12561941403589798752994868610164977000344478380742284683002,12561941403589798753122808233892239777622400072173608271803⟩,
  ⟨-344106936938790041813852376072010285141113732099629663030953,-344106936938790041811172721930182193336058361927870625403984⟩,
  ⟨185289115269814926290395079876755182942726100038409626116962,185289115269814926291386620251157605169781442294854589162342⟩,
  ⟨297287635876816900335266616841923063490589862316843644270340,297287635876816900338106769118936540384509225310139676713090⟩,
  ⟨281171254442480284553639079243131913468819735872471947631822,281171254442480284554858051589092442940984403346618623469407⟩,
  ⟨240131565078543406923121090515319873028979148279681865706081,240131565078543406925264070930839207132293731433236063470880⟩,
  ⟨-59540346574569079109154554698256824693497691684195081782340,-59540346574569079107945742201517031552909973999775648437815⟩]
def bs0_3_0_11 : Fin 8 → RI := ![⟨-11274190894324149874371442775658475297433304732424644560827,-11274190894324149874183351361222864509871424251777801072541⟩,
  ⟨12093985827214232141097017543253052176751598048162234231739,12093985827214232141232286430780948882885698413500917290283⟩,
  ⟨-348737821943805248399795500661141903283402321245844792278015,-348737821943805248396962337453619188898196905361992151707505⟩,
  ⟨187221343040337222216441045815717620758355608075396875770359,187221343040337222217489388459532477816805844877541814286317⟩,
  ⟨299373693410332403375858985859664573157035360283297873020943,299373693410332403378861841642229060406247467155653962828154⟩,
  ⟨286100382494855513125978163382173113461775421444591260925135,286100382494855513127266966869063036770364042727148101137888⟩,
  ⟨230779889091465582422371699197789355323507621570052691977186,230779889091465582424637444307515986751078019417169171094109⟩,
  ⟨-40948028856592358202614151956466380186831874548030495261326,-40948028856592358201336090345055219295648603677309992777719⟩]
def bs0_3_0_12 : Fin 8 → RI := ![⟨-11411006089410540613906817782681837286564242336798075599830,-11411006089410540613707585491949856623260111126775882940336⟩,
  ⟨11566840417239661939287217223562583533912543433392806706141,11566840417239661939430498246822536343551349632486077373141⟩,
  ⟨-350813545408363239442430259959211973014402524706749166481883,-350813545408363239439429285153699986485401759705247812338544⟩,
  ⟨187745575058774418871815851909326847790828978807833653281627,187745575058774418872926289124276839506414163578976444676646⟩,
  ⟨299030201926967506780253667525772491488075035757358680222751,299030201926967506783434385997695437237502545932737008777370⟩,
  ⟨289087596724718130752753845760640036248636007987163100489071,289087596724718130754118986598006620009874684650626492200881⟩,
  ⟨220884911566507005081264095329937854808797592625639067645187,220884911566507005083664043194517154080803872632640310552216⟩,
  ⟨-22644411390487622481871588298235943119643116750623677159540,-22644411390487622480517825590348154638066293769440299206332⟩]
def bs0_3_0_13 : Fin 8 → RI := ![⟨-11454844031563983659400084188681795097785062065311464813497,-11454844031563983659188640409489188952510136348245392968092⟩,
  ⟨10990652256631280516216121557224943933412931620682346919452,10990652256631280516368184663727982720293727961115973233536⟩,
  ⟨-350225486213686359502788700628032726137692909877577053476170,-350225486213686359499603787922314029452985767343723881050321⟩,
  ⟨186815733464720825306207654499732640547047437459345115116031,186815733464720825307386153428925676437524840542757206166694⟩,
  ⟨296180500921223843861080644058054272201314159803920445205242,296180500921223843864456317407936675271787353698748798891686⟩,
  ⟨290032332224773085405164754669275373842847735258820288931753,290032332224773085406613568698023743420545732161516307488976⟩,
  ⟨210582866128109298085981663604306576233139505381557851438499,210582866128109298088528710794705390978690883047762805819212⟩,
  ⟨-4843796635209935980377908889817822855149041165484680951300,-4843796635209935978941170387074957313138951546316475584049⟩]
def bs0_3_0_14 : Fin 8 → RI := ![⟨-11401952897883734408675270480093082438110901948256853923630,-11401952897883734408450404569559626787370485001854572251972⟩,
  ⟨10375865628619200335615643324824954809066030667343526158654,10375865628619200335777359167365322194001563366702971354975⟩,
  ⟨-346926286164608524378756165133307867356175931110958025629290,-346926286164608524375369078985497357363299638503188600502400⟩,
  ⟨184420354501341250967575741733411591173372812238137295625757,184420354501341250968829049992427086731691188969435469361087⟩,
  ⟨290807490283080856498838162915377419142667630272381309409335,290807490283080856502428118904595906947960737108584455103920⟩,
  ⟨288878176905459120824474622627965652086282172593736385884513,288878176905459120826015405180298463965082498208690350188980⟩,
  ⟨200011460338275920976932273012352395280341895647018825055533,200011460338275920979641002906512087625180137749289168106997⟩,
  ⟨12253408680655581022416519204922166026199127718455661412457,12253408680655581023944459695058930378305556239887938407341⟩]
def bs0_3_0_15 : Fin 8 → RI := ![⟨-11251156603681764763502577717087608806651460491975484006678,-11251156603681764763262916414298868395389929468376113308624⟩,
  ⟨9732847719545404584188367260847383062476965197179301283922,9732847719545404584360723441526315884980322200800811613630⟩,
  ⟨-340934518383282075088215384257454236499811329112839367927269,-340934518383282075084605439660161579618964383104766243628297⟩,
  ⟨180584628312875250872486541096716706169223941168421246212032,180584628312875250873822312665842690615995662136106046546625⟩,
  ⟨282957365242948231577207640684538308966947876887731933296235,282957365242948231581033803250941226268748595028966781527224⟩,
  ⟨285616639489381612032314180788282830885767334029731303546009,285616639489381612033956341456139087167779107888951464984671⟩,
  ⟨189305848332589202627013564428782067447762928846583657938047,189305848332589202629900519297965261459529583615420946517079⟩,
  ⟨28466553847887227975022434590262004891482013743642784480106,28466553847887227976650908232971612468227577727242673585057⟩]
def bs0_3_0_16 : Fin 8 → RI := ![⟨-11004040726481867059427842541136818343276646914528335226590,-11004040726481867059171822891221670926570768106147197994451⟩,
  ⟨9071581679479778882785282723307104574835552291624307002411,9071581679479778882969403265606670233271217464986584148942⟩,
  ⟨-332336557388885132239592274465444471947397101412559697955316,-332336557388885132235735929109469539247154674019526360176591⟩,
  ⟨175370823592035421168269019790154725182318255419228674080376,175370823592035421169695965924222098876232999842193982710457⟩,
  ⟨272740614945631140730408915130451098850882673936123582458726,272740614945631140734496236652056877715571808863261224008957⟩,
  ⟨280288955712483364748890816824574569431807236447845224383622,280288955712483364750645064984011317792934264089278931587757⟩,
  ⟨178594839446481263951453695257973902143621090365546407115614,178594839446481263954537702422740673479253645288086054991546⟩,
  ⟨43639762039172966664405671314014774685477236925352239447269,43639762039172966666145298225195261880637523369940856717000⟩]
def bs0_3_0_17 : Fin 8 → RI := ![⟨-10664997029228133203515480133538460187609443237806947698277,-10664997029228133203241316820205624010549037540539503479166⟩,
  ⟨8401439661070315345692886932728647862706679258010916340703,8401439661070315345890055774829888220017221028240567010202⟩,
  ⟨-321285355476090412720551522381271930856840344442811261809526,-321285355476090412716421884595635499409812957485290713065919⟩,
  ⟨168876965767461678394840015534657769129166093524544464325237,168876965767461678396368086837778582188857460139931287737859⟩,
  ⟨260330038803943674212442947055064754913335887906411547970976,260330038803943674216819929882009342018957875984422808992600⟩,
  ⟨272985716767710166027634149445185383522029799315905563170808,272985716767710166029512718094031566621443073609127679466462⟩,
  ⟨167997542639080109819685900279068863423529233301248566152325,167997542639080109822988465620834753801327047667505819691888⟩,
  ⟨57645825362566906811206247283451184201559858350705785147026,57645825362566906813069158501738538546807768355219839265446⟩]
def bs0_3_0_18 : Fin 8 → RI := ![⟨-10241114321539740750433122602664865098076402831592014501912,-10241114321539740750138768243942232124950474220773930564994⟩,
  ⟨7731034491010170536221096391354374604449333979037884412267,7731034491010170536432785940078393731110229588242845976859⟩,
  ⟨-307996055795772712437929869000497745735865763521546152151165,-307996055795772712433496099699357237864759248139385283076312⟩,
  ⟨161233768099611084119608728593516498109528911841700527664591,161233768099611084121249336313978052303908705624117076064157⟩,
  ⟨245955754554626669776814944529453105116824674628792947993759,245955754554626669781514274857519945211665079270254216066890⟩,
  ⟨263844259454511547529626402062609125742903151320849578389011,263844259454511547531643319874295639245440018733025470545227⟩,
  ⟨157620610302730948221826035478767028163110207153258341514606,157620610302730948225371821716467754604288276454306072402320⟩,
  ⟨70388777677015471705784696312677692936767070044655962072127,70388777677015471707784803585770244111348630710665075226197⟩]
def bs0_3_0_19 : Fin 8 → RI := ![⟨-9741917017810165231002677147141091498085943400825124542099,-9741917017810165230685773627866308615567887571666563397467⟩,
  ⟨7068140406629465151612406288168571759316640051295750858896,7068140406629465151840312418978385634703784653779861481755⟩,
  ⟨-292738618791980425133252362870562399610606684721945177428677,-292738618791980425128478942489464507303531786277785541589575⟩,
  ⟨152599953914495359823698159136719461350176365208013711079817,152599953914495359825464446419267128464569800753208612355653⟩,
  ⟨229897408047800471611748985262327958394070632053369708577166,229897408047800471616808310103617463928587726997893118425285⟩,
  ⟨253043926735992770297407515091043261732617955663000539287892,253043926735992770299578939884666749962366826325939654393424⟩,
  ⟨147556194846900923097581868346212742751458513822274789723146,147556194846900923101399281284069364334233157903088100736930⟩,
  ⟨81805045268897506091934622103156532223227360784378262250700,81805045268897506094087948578482974642869606494996434533745⟩]
def bs0_3_0_20 : Fin 8 → RI := ![⟨-9178966412554627008246324323841084253460343636730870411742,-9178966412554627007904142538739895493730602000936197091076⟩,
  ⟨6419642668560889787842469470275724941212636798297554729759,6419642668560889788088554861985486913524395844786196891412⟩,
  ⟨-275827870957299614766733743938099136113017096132461136592387,-275827870957299614761579564802475288884563145605417306273257⟩,
  ⟨143156235811310767967585810413071862712357404677716866654048,143156235811310767969492988145714297508147818199037831145176⟩,
  ⟨212474014308184159689539662751070184425606453886728554263868,212474014308184159695002551928178602027224318126725857978860⟩,
  ⟨240799467456952246581809405019023485147745859719519490759259,240799467456952246584154036640131701886324045974774851066551⟩,
  ⟨137880674414028444739608659079093349040182362381555030745988,137880674414028444743730573460186404991786490670027216557141⟩,
  ⟨91863180153356801259665634651084010724989274601366344059934,91863180153356801261990724315322988294506108328041688459395⟩]
def bs0_3_0 : Fin 21 → Fin 8 → RI := ![bs0_3_0_0,bs0_3_0_1,bs0_3_0_2,bs0_3_0_3,bs0_3_0_4,bs0_3_0_5,bs0_3_0_6,bs0_3_0_7,bs0_3_0_8,bs0_3_0_9,bs0_3_0_10,bs0_3_0_11,bs0_3_0_12,bs0_3_0_13,bs0_3_0_14,bs0_3_0_15,bs0_3_0_16,bs0_3_0_17,bs0_3_0_18,bs0_3_0_19,bs0_3_0_20]
def bs0_3_1_0 : Fin 8 → RI := ![⟨-6143646843334063460195708629053276910607080844165297533142,-6143646843334063460085241780186167184745633146690839349821⟩,
  ⟨12688037359324949881537512401317387533083723131296658291746,12688037359324949881616956366373410513137332679436753698281⟩,
  ⟨-207837781210653771207131112260890982010541518102335853347533,-207837781210653771205467184043901386629627055216646934839142⟩,
  ⟨114527054806539052468760546830813454828083425764815598083191,114527054806539052469376242707907747280951614708176189367861⟩,
  ⟨186798171897991910196711678966516572206050601118011232179159,186798171897991910198475268319428038829140916280098272278394⟩,
  ⟨165850365769303261383709390648162461208633756929522686581676,165850365769303261384466310151385760390805241033284969382924⟩,
  ⟨281813115136500132032360960913553711929450896229534060488592,281813115136500132033691642185630669988122339683719788041938⟩,
  ⟨-216452729427083700478140365083133729945819919395371060633611,-216452729427083700477389754326660641132062567320566214855739⟩]
def bs0_3_1_1 : Fin 8 → RI := ![⟨-5771123876848141796971765058504408720763542600280701490680,-5771123876848141796858114525068445895474699403101830658961⟩,
  ⟨12439325581981841816412139637973089593504201896587130511226,12439325581981841816493873199665682155423989290505568787598⟩,
  ⟨-196547536149768219988491109730748832155255439510022967456548,-196547536149768219986779226650896411650028431767250339377012⟩,
  ⟨108456048104689991265463585550212565948364297607752851495165,108456048104689991266097025949607999455150226605299849580151⟩,
  ⟨177003951460094141795450613187188638657281466966024625870848,177003951460094141797265029663956245079857159070625020746693⟩,
  ⟨156668639267716416188385015735548337267539317597412447097425,156668639267716416189163749864315114412094203449293103470935⟩,
  ⟨281230679798651997908190699436535579569489368924189090791482,281230679798651997909559731304062096157176058627091569130510⟩,
  ⟨-223712195053992702659451897614421357710164195103515827921873,-223712195053992702658679654052206210206717975999480150342141⟩]
def bs0_3_1_2 : Fin 8 → RI := ![⟨-5402447887037279309817104644045655733605417961897424442525,-5402447887037279309700126520489745848701291916785920194275⟩,
  ⟨12156591225209156593932141111824383568357529963915085624638,12156591225209156594016267762085174275821900780639014370503⟩,
  ⟨-185243378471218674594486597147499636252544216910032217842323,-185243378471218674592724591599665505890063093177760874832524⟩,
  ⟨102356863923422821889496796558004813268259101962490771999403,102356863923422821890148783548878145496234979486664121485184⟩,
  ⟨167142025765387305808157083564553560554968487545031838389613,167142025765387305810024624599207733070251959531241838434229⟩,
  ⟨147505996736223292881602155454779662046482687503509056037172,147505996736223292882403690250779814230385937743826891820524⟩,
  ⟨280138163106662782752489858660315124933384481677783919942768,280138163106662782753898974606446492804755945239318953876394⟩,
  ⟨-230365547961511880869047461275849279682922233608644705081530,-230365547961511880868252607084629615698052103466401842417235⟩]
def bs0_3_1_3 : Fin 8 → RI := ![⟨-5039817558589144905610206719916586961936258131298120653112,-5039817558589144905489747072766747642351128612983478302239⟩,
  ⟨11841761606722333911393299817584820442789125752133254369436,11841761606722333911479930260083289130317263262215028088148⟩,
  ⟨-173996044140937920315236781064326023934522096426086433739951,-173996044140937920313422334395868666997580550072903826792496⟩,
  ⟨96269150783783353674749607790338559676719260302984288142795,96269150783783353675420999333302257037677096393011513549472⟩,
  ⟨157279587497456540931753322986952072421514302929052755597908,157279587497456540933676446108051398017725184919927988604579⟩,
  ⟨138416251395597025866133258077697989928560286810749701692313,138416251395597025866958648294008569694621438984195898755155⟩,
  ⟨278542575313600160966878246354933234226895767290464609748613,278542575313600160968329300658966901178131660521152509264419⟩,
  ⟨-236393292333397435484823519461115916973079453449625687080182,-236393292333397435484005008678935536704008723200354019631238⟩]
def bs0_3_1_4 : Fin 8 → RI := ![⟨-4685224761277571563148461036392716358219337251503186985812,-4685224761277571563024355084907716277618528039683098035096⟩,
  ⟨11497064199146509140039873577646490475006976992818539313322,11497064199146509140129126317034301605308815916100862511722⟩,
  ⟨-162872023148302168520862744414520838415038909217281168948815,-162872023148302168518993374583743644818081890223860084148379⟩,
  ⟨90230425123776195548394940320045817175831197271454287824168,90230425123776195549086654833829826213686568626003267761593⟩,
  ⟨147480226999654824230099796472398309515301873010593936944415,147480226999654824232081132383759242703896317540826079978374⟩,
  ⟨129449805194235060129047459240656220442772142177454251933960,129449805194235060129897833955893860200737267164982785449445⟩,
  ⟨276454596465408243131847581970921906762118424728205952088475,276454596465408243133342559578101913905113292207283316495959⟩,
  ⟨-241781296633725238755998855032807317489727452491868791949497,-241781296633725238755155567991656510913134547840637421507381⟩]
def bs0_3_1_5 : Fin 8 → RI := ![⟨-4340440674501233168105414524088639790183222410592765148584,-4340440674501233167977485743098275421996875546354454268782⟩,
  ⟨11124993401102534013487392955842596279891258842732257151323,11124993401102534013579394942961507835300838640129672690887⟩,
  ⟨-151932928793281399338643461840707752881417323003814699072987,-151932928793281399336716509903187522883961580501253294032001⟩,
  ⟨84275692278049153549354928202378527179848864524941568632102,84275692278049153550067949564233383382239666542018504301601⟩,
  ⟨137803295404096649912987770602255859901955043977740028892853,137803295404096649915030137506026842118901294477401947603755⟩,
  ⟨120653191458008520205677314532699832859239593737109212317735,120653191458008520206553883298378200949497551375430034485397⟩,
  ⟨273888422542051679822723906733646169267671476191803207378493,273888422542051679824264934062353856582621888900994708772308⟩,
  ⟨-246520816594133813728211592347206582761340678988266580546501,-246520816594133813727342329576901470066126571482359128701890⟩]
def bs0_3_1_6 : Fin 8 → RI := ![⟨-4007007283946333155835014154737757229234802403827214361610,-4007007283946333155703073289735635092795257350065526058750⟩,
  ⟨10728272497115023088361128694447939484563144158690274235886,10728272497115023088456016034641258911710024055343293435571⟩,
  ⟨-141234988084485811017288085781682416132519115541613057638819,-141234988084485811015300701054914429139530714168505082318140⟩,
  ⟨78437132967636801570083319709342841327205592845556973480641,78437132967636801570818702744499357381401071925253016988183⟩,
  ⟨128303379606129583621538469956241054907355531574986447301378,128303379606129583623644889276822422389284228436617949012940⟩,
  ⟨112068707872643168629719966249387083595694098772024668447574,112068707872643168630624025838506990041484268883587316000094⟩,
  ⟨270861561433641710179036449445476027732917830012801948889829,270861561433641710180625806251401067625393911799114528817725⟩,
  ⟨-250608434634893095005476832016741640541404790890859122600577,-250608434634893095004580307552581997596344699534044052329243⟩]
def bs0_3_1_7 : Fin 8 → RI := ![⟨-3686233989095978164720568705689198718519463086652118584366,-3686233989095978164584412689167690983506332583214763748546⟩,
  ⟨10309812158568594923110931546294209148514381828995252527241,10309812158568594923208850278741487538750726283695253655225⟩,
  ⟨-130828656238343251196947611336253118778344888383094282586294,-130828656238343251194896735076737390412417036980028186805121⟩,
  ⟨72743857888469063825988521477392934009298266985358308815107,72743857888469063826747397998956587451100324569928674986641⟩,
  ⟨119029893013147438837859305950485148805878986058539374937333,119029893013147438840033019635105327040459077767688940473718⟩,
  ⟨103734141965252833064662181508094631869937543674646340275980,103734141965252833065595123340423349050016070388758531448605⟩,
  ⟨267394583784964873049567642413872807908467004136221563270454,267394583784964873051207774843818881380818123064626469554812⟩,
  ⟨-254045919901697019885403162632386999176618364660538043012685,-254045919901697019884477996651764915776356935600955204280888⟩]
def bs0_3_1_8 : Fin 8 → RI := ![⟨-3379198918047485487597337949122485230631327292094856481585,-3379198918047485487456748705840722486968472372977258620224⟩,
  ⟨9872666947594123307668287105810510218342927975337567163842,9872666947594123307769394062737782859741302124299713520545⟩,
  ⟨-120758354634366148907182294232537887821120206206538077199259,-120758354634366148905064641639897877234932844911723354963483⟩,
  ⟨67221730916051510485342925065801293172182344058807721012899,67221730916051510486126510533687275211972207430790258024583⟩,
  ⟨110026782509939080128049044895481075065427445646257037563039,110026782509939080130293534487942871640254601635269372901075⟩,
  ⟨95682588609534264438302061106993195089990961395401807514787,95682588609534264439265379435375267665464932658303252332137⟩,
  ⟨263510834749068737268916549782264147963719061964769514290968,263510834749068737270610084765864851602554910469534485406794⟩,
  ⟨-256840014967943841421188108811695389250580909733712371452762,-256840014967943841420232819516015459112030525114178067070125⟩]
def bs0_3_1_9 : Fin 8 → RI := ![⟨-3086754436409989841032542293082726578759128207121352239152,-3086754436409989840887285420415888002411430157624856387705⟩,
  ⟨9419991286512393098085140312232371553038571232908305621502,9419991286512393098189604067959640519137453122039668735340⟩,
  ⟨-111062328283061678614085178655212331095704344636628712424772,-111062328283061678611897218994701596588627586894673806307145⟩,
  ⟨61893259530542327855332217928138428581139611334406064952917,61893259530542327856141818804251141148836708226864755140935⟩,
  ⟨101332348883673806556482284485812490698742368555317200769496,101332348883673806558801292194550770543721073879515819544767⟩,
  ⟨87942356665291942224214277040521142312553021235510162749414,87942356665291942225209577993132889620190667566006694597537⟩,
  ⟨259236113466951329730593711133072797299695879332767730437817,259236113466951329732343472279275538578347279910271492697782⟩,
  ⟨-259002156826514984089701662511264336807538466965884507372930,-259002156826514984088714657159054247322990716999598515396982⟩]
def bs0_3_1_10 : Fin 8 → RI := ![⟨-2809536262145350641657793652818309017341508537639195447335,-2809536262145350641507616960507198853441371289893874365032⟩,
  ⟨8954996247243990105967107610195428761406197847591279451862,8954996247243990106075109531298632321988008166222205493802⟩,
  ⟨-101772616013279498829031317330710118656250715290851461950772,-101772616013279498826769251937908667745083024024619082346055⟩,
  ⟨56777549379810493277488604820124411533334824473060767982155,56777549379810493278325626707180790532774599821135506358546⟩,
  ⟨92979175151915377996212756541858853851308370751493038683401,92979175151915377998610308552654967347801793474575442062436⟩,
  ⟨80536959760099072155723883233573706553663243020534993547582,80536959760099072156752894819567798563088544369766010935076⟩,
  ⟨254598327614420691245888342286193626410283429474317421469205,254598327614420691247697367473404627400731278978077801428981⟩,
  ⟨-260548141028322902491326386702944948582786457269395482522044,-260548141028322902490305951687605629925416487075217868838050⟩]
def bs0_3_1_11 : Fin 8 → RI := ![⟨-2547975557535806120792364687874607875123880299835994541340,-2547975557535806120636996579327999644328842347672883199679⟩,
  ⟨8480908312337253414725594389629774178115954473321728983270,8480908312337253414837329799052565638582677860416488823877⟩,
  ⟨-92915124257852700903455194256148712685483656170577237256837,-92915124257852700901114932155017355460301762408812570414405⟩,
  ⟨51890318485709147764323325425093942069047361687857683766122,51890318485709147765189282088565188935365550432776798709762⟩,
  ⟨84994154912821202506176669340010743442920665314741025144716,84994154912821202508657101658297097992055026182765301026219⟩,
  ⟨73485184485513498387856687422271586360067692695121120037855,73485184485513498388921270623102996669879516001110453191417⟩,
  ⟨249627130621792972132796614644272186334721080620924095145751,249627130621792972134668175519153418562747227667986627627648⟩,
  ⟨-261497738691496878778629129707914771667728603143914760882494,-261497738691496878777573419558838071463666252296060975441064⟩]
def bs0_3_1_12 : Fin 8 → RI := ![⟨-2302313360113877282614580103436541429521419455862526971816,-2302313360113877282453727778172257221597195447757376896225⟩,
  ⟨8000930989567701880165771206426346422241847618464481131222,8000930989567701880281450676222753779508815368921769396547⟩,
  ⟨-84509793544561659417754365742646131055516663822770768775154,-84509793544561659415331496569448532877603330540985186633846⟩,
  ⟨47243965487058890032948978325270920259558158110198105913786,47243965487058890033845501712221896603316546578497498490544⟩,
  ⟨77398611027473526669245714168061796844951882574720889365947,77398611027473526671813701316724036512889924267326107745801⟩,
  ⟨66801227941880022698804764470556302810581590872555130021799,66801227941880022699906925556866711633795882079852073628077⟩,
  ⟨244353549184183448382282162686826065126484927212503825285518,244353549184183448384219786317651110900889623975495733967573⟩,
  ⟨-261874276600852031199927951150831277402054205761282076554833,-261874276600852031198834976319173931031693950910196774090041⟩]
def bs0_3_1_13 : Fin 8 → RI := ![⟨-2072616731771187701488122020653008396265440038833310307954,-2072616731771187701321469474419009982247315859182325893160⟩,
  ⟨7518209861769056114727106835857692276096541551830973064583,7518209861769056114846957625436367046761636752320497742544⟩,
  ⟨-76570845582866659979760652079771576286757481618254828687081,-76570845582866659977250415959512465985148582928867611660941⟩,
  ⟨42847685508111268846847220243533298821954920159789539481494,42847685508111268847776071629108667369733749707108801058752⟩,
  ⟨70208493656121662263335976179206936884120414743884246723743,70208493656121662265996563126399297924072923332374543256873⟩,
  ⟨60494895628909734556602673211449807004724612537232809166619,60494895628909734557744577446249765413036188402320330414910⟩,
  ⟨238809608458818478815112563955927779036640478747428621943836,238809608458818478817120056923079892041134730956905847133192⟩,
  ⟨-261704190757455422398674302537081612328048659070353050988369,-261704190757455422397541915806795922535508412430274771725184⟩]
def bs0_3_1_14 : Fin 8 → RI := ![⟨-1858796043809911665642751760065035034478908422036471663736,-1858796043809911665469957555561153331286290893492069632857⟩,
  ⟨7035801360921160808968345868566497246773946520584638082747,7035801360921160809092613527911108135346228929433679986055⟩,
  ⟨-69107098145999002298119349862569949073535140665402843012235,-69107098145999002295516603830061196862596900915356706996334⟩,
  ⟨38707626733206342436997185257896224467032172343301916140833,38707626733206342437960267670382404950728721009493718666342⟩,
  ⟨63434645881204686264193687406966256867266373801281911895809,63434645881204686266952325156258892145084333326626259998634⟩,
  ⟨54571850127512742233229064577954263616092729022809049570654,54571850127512742234413051491651146995520876917877471504945⟩,
  ⟨233027961919749816326983136742678575485986398961422877467566,233027961919749816329064611992488487329846325350814520384221⟩,
  ⟨-261016563553677888181114623351930055873963338704917431976973,-261016563553677888179940504692049753602156045252871095526639⟩]
def bs0_3_1_15 : Fin 8 → RI := ![⟨-1660622869588466188626933800988483140322343773755337402247,-1660622869588466188447628577789713375600990025026133133934⟩,
  ⟨6556645303319966690688219614398738830816505285280643619740,6556645303319966690817169774845645249457618450625409917464⟩,
  ⟨-62122334732460280740738727021365015354017426295961394467445,-62122334732460280738037907513964992540040680990166702997212⟩,
  ⟨34827080533850205553092083992563085745985303950436467749230,34827080533850205554091456092031285668021232412571604551163⟩,
  ⟨57083124817817307335135504677466973058111489115558420020881,57083124817817307337998090021607492856742627555432469572361⟩,
  ⟨49033900819424288961382819528608281749287996893136722079665,49033900819424288962611419981026664930742103961086606174271⟩,
  ⟨227041532244831652185582778784500667728200482144854242992833,227041532244831652187742685624656690043013393612508633312531⟩,
  ⟨-259842654282601979676392174179422928218095707248202976274763,-259842654282601979675173813824250779607079345166460716779174⟩]
def bs0_3_1_16 : Fin 8 → RI := ![⟨-1477748020105905072395854903490962155585311276939256218154,-1477748020105905072209638590598241042463459141437550758403⟩,
  ⟨6083541032769955862475580067095128933874278268662223776932,6083541032769955862609500445971159646644006845792300413733⟩,
  ⟨-55615716187029153978811345385779154592898404137873526865535,-55615716187029153976006426256901185244446595330066500104434⟩,
  ⟨31206698001731713260684976987818701491279429374460580022588,31206698001731713261722868602197622453219152593363261438373⟩,
  ⟨51155566180463512628538858364213379759553550896076076481231,51155566180463512631511778386403257075994613139613077852425⟩,
  ⟨43879325001861320400659104941596547038702897372924732613494,43879325001861320401935060221596839975050952853841327591166⟩,
  ⟨220883168883597208227168023461446828360987729823319751721603,220883168883597208229411181138547870974869071955726610997323⟩,
  ⟨-258215431991654165426281612592440179505029106790456156808426,-258215431991654165425016292101120241878576086667761871695290⟩]
def bs0_3_1_17 : Fin 8 → RI := ![⟨-1309719326488215033020802936331749776625697186938350411971,-1309719326488215032827241624545270564627434208147937273795⟩,
  ⟨5619126900298306284476127518016238431674616015204777421689,5619126900298306284615330167920421498830955705131619204969⟩,
  ⟨-49582221998574886844554197879842205199802100590108725101708,-49582221998574886841638643288474382748427533892224332144913⟩,
  ⟨27844725953459582277130478361871830768894632184230077941911,27844725953459582278209307919026853499661642748889783786359⟩,
  ⟨45649580679653307026088883792984732837831144909585953564814,45649580679653307029179065799046124942529412072105393849238⟩,
  ⟨39103211125485166386805379474596722881106806017846244516568,39103211125485166388131662730591798555699047214182720069883⟩,
  ⟨214585327137323679374807886185956099194816657659680404414670,214585327137323679377139521560835034938599610743448455562404⟩,
  ⟨-256169118811573331649283677325765482325038608868648688671142,-256169118811573331647968448330384862913485501977193732796832⟩]
def bs0_3_1_18 : Fin 8 → RI := ![⟨-1155998842858876503248260393585194272790538568836202583859,-1155998842858876503046882817347768000666764803902796472113⟩,
  ⟨5165862759233894071648957590338177997557974494039185843649,5165862759233894071793781429279205251335079202368557556766⟩,
  ⟨-44013109798473954213808182094514796393760896914278436375187,-44013109798473954210774893512307047569014405184341081624884⟩,
  ⟨24737255851238210000328990250310217139179239897017940106895,24737255851238210001451384386772732376057234354227631332232⟩,
  ⟨40559171296810400117016669506845662218485300848188521008489,40559171296810400120231637192149847876594566992462888918223⟩,
  ⟨34697815463772575960169245360217410252181060974691206432496,34697815463772575961549085706602797136880588049387689783130⟩,
  ⟨208179772712240458983852220179364505484055163537805442579742,208179772712240458986278010106726906473150701464681752241344⟩,
  ⟨-253738750885822740872830910191165038920512273662595482244125,-253738750885822740871462570491245209023379269749813277060618⟩]
def bs0_3_1_19 : Fin 8 → RI := ![⟨-1015979210376340328753556666081284079651745436573904379011,-1015979210376340328543850235230068459961017132337392973158⟩,
  ⟨4726015162391930443575900875860195419574926455447135336631,4726015162391930443726714541084335732746660271971607286123⟩,
  ⟨-38896382589828389404790766451075434731385266048063091045373,-38896382589828389401632022889834559392562022699110239953544⟩,
  ⟨21878479589862957022453540261572718825567534513047465397308,21878479589862957023622355939891415977745113449872365879049⟩,
  ⟨35875161366079089774040342774454520983597263224981523589224,35875161366079089777388279576506663777562500037035550319579⟩,
  ⟨30652924259684261975278077024989718070876226939549933277146,30652924259684261976714986732604332829894430550063201239522⟩,
  ⟨201697314818527109134404110696392962039487979848014310705119,201697314818527109136930229826249898267086757111399025731177⟩,
  ⟨-250959762942003507239036914214224889510257420766218554146618,-250959762942003507237611980812887139048286024483367110731433⟩]
def bs0_3_1_20 : Fin 8 → RI := ![⟨-888998986113544502319130177609719681635844996390560688016,-888998986113544502100536488137760039705340023439692694971⟩,
  ⟨4301644998895521866069208448520244230506755604698106997020,4301644998895521866226413525017512545202092160594804620199⟩,
  ⟨-34217254380493250488332351550433785331534852302160170866939,-34217254380493250485039741942103304240241694763248233395760⟩,
  ⟨19260946698301038314585112100137790484901523499832910319833,19260946698301038315803461630010712964096961191467953706766⟩,
  ⟨31585624416696644440354480389178540766791028192646533709585,31585624416696644443844301157745305133929066308046760167340⟩,
  ⟨26956214243826513551879627840357295492749895705162846198881,26956214243826513553377433096772040301214428207960152296970⟩,
  ⟨195167570012045022317661967842580137605048284166973440009749,195167570012045022320295142697517503692144232246266638665563⟩,
  ⟨-247867601430524371660273896611836725253097210187052912098921,-247867601430524371658788575211893441751550741195894576979844⟩]
def bs0_3_1 : Fin 21 → Fin 8 → RI := ![bs0_3_1_0,bs0_3_1_1,bs0_3_1_2,bs0_3_1_3,bs0_3_1_4,bs0_3_1_5,bs0_3_1_6,bs0_3_1_7,bs0_3_1_8,bs0_3_1_9,bs0_3_1_10,bs0_3_1_11,bs0_3_1_12,bs0_3_1_13,bs0_3_1_14,bs0_3_1_15,bs0_3_1_16,bs0_3_1_17,bs0_3_1_18,bs0_3_1_19,bs0_3_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_4_0_0 : Fin 8 → RI := ![⟨-1126100095393391792847814518521087500235653407971284349815,-1126100095393391792814214104313031554745351192502200774594⟩,
  ⟨13414299502971684260605635227727422571904132839814142356410,13414299502971684260629799492025340378867054497022966185078⟩,
  ⟨-47841433185506003411795842615279821646181381762012326612555,-47841433185506003411289729895697873590064785698748452642431⟩,
  ⟨27295673554034197466320122145180993214479687281843705839915,27295673554034197466507396759322460063012889480624124166968⟩,
  ⟨44797544380013551200537691361617037928085277998113863529856,44797544380013551201074117749805088932823490531910205600929⟩,
  ⟨37462228884243262046242331055601618139917924644165491507368,37462228884243262046472561292933166177269503251781498742688⟩,
  ⟨-84839093422376457483826236618592412250812810543075842358393,-84839093422376457483421486755820265896182261972719666631722⟩,
  ⟨70742726550787769488373258936394084582280017776716964894606,70742726550787769488601570258613586708503525939832649718976⟩]
def bs0_4_0_1 : Fin 8 → RI := ![⟨-1151526850853891958585107383671556175890082658529009241017,-1151526850853891958550607161454331597802611251592475268217⟩,
  ⟨13112981420379645463600130184545419694587930183379425887411,13112981420379645463624941559870433549858168617527988450215⟩,
  ⟨-48751447232146195502923407829170147182068114526189906363703,-48751447232146195502403741577901847246742038369124036724319⟩,
  ⟨27800835122221591961178573121348752297178175668699968913401,27800835122221591961370862887883894336115057612936462738346⟩,
  ⟨45625844472724079669891507227794966876676379405933145270243,45625844472724079670442298937717059866791331820495695796974⟩,
  ⟨38184371603573319809226758165583150139216074439324664788783,38184371603573319809463153892729705799506929145833016401692⟩,
  ⟨-88388359535235510860722698327857822756209015270738368240940,-88388359535235510860307109397271584227720720735781838930112⟩,
  ⟨72997236254475888196401269699943415230328130613240340186776,72997236254475888196635695124061557092241361088117487853829⟩]
def bs0_4_0_2 : Fin 8 → RI := ![⟨-1174180001620255912140585950750245066279142888673346405081,-1174180001620255912105143346265760835097613147369681833171⟩,
  ⟨12777232185146350892812434849071728734769412374057037958249,12777232185146350892837923953368553271905122230875243731539⟩,
  ⟨-49528570717823313896223140559761817333168234590349355022871,-49528570717823313895689279493833232351496915465669121082533⟩,
  ⟨28229203169766669884552269692928726634153928300016705125092,28229203169766669884749811902913228431547967808441032246577⟩,
  ⟨46328065385221861036853004614512307870526794736327888354925,46328065385221861037418841338846142384897429257744272455782⟩,
  ⟨38802918148834814960492576056975620782311642350144758078467,38802918148834814960735428993006219693504581826424884710227⟩,
  ⟨-91906176037112851980424407115658630340913435208796722154389,-91906176037112851979997466268666363320683770275367922724624⟩,
  ⟨75139967400683793729200444661943226350325436977808716498995,75139967400683793729441273475618661908228779184378819344371⟩]
def bs0_4_0_3 : Fin 8 → RI := ![⟨-1193766690071034316696755368409249805133077205521866841997,-1193766690071034316660325240684026606585783270676171977496⟩,
  ⟨12409546339977738147507031972014337112154885659458112867161,12409546339977738147533231269121270833068900832362498824363⟩,
  ⟨-50161349716036670950564439390227489030313349254333510501160,-50161349716036670950015703565019096592269101187160373561768⟩,
  ⟨28574340814767703722916093549226881014890594247028287654400,28574340814767703723119139799511326586709807530499550990163⟩,
  ⟨46893639257675669799044956055949813741175010731164868059978,46893639257675669799626558464661566499034838264818530113875⟩,
  ⟨39308826798268096201912606643015252226339172195115328701065,39308826798268096202162226094148007184782552061598668755577⟩,
  ⟨-95374946630667874118736163495647538757697756338812854966340,-95374946630667874118297326965059271797751395661896487518348⟩,
  ⟨77152683854848513015547130300560429375778405230460463101225,77152683854848513015794669232016095979166933114879317048206⟩]
def bs0_4_0_4 : Fin 8 → RI := ![⟨-1210002955449779157942528668798598160307288973475243315886,-1210002955449779157905063100460052727278382518846149725530⟩,
  ⟨12012675995443136919768126557237353201303200028933363188167,12012675995443136919795070507683607670959151178717861355568⟩,
  ⟨-50639078402427097702411825166117451625007094777674130892924,-50639078402427097701847492816962730320472165591294485369379⟩,
  ⟨28830261824199385568928837202823828977069709060586135526122,28830261824199385569137654564742775728539914296908614267585⟩,
  ⟨47312737193440616953997611589746683303835507569933325070996,47312737193440616954595744677665166754619669024264603665518⟩,
  ⟨39693631511833570454344991108538681050195552227068047818198,39693631511833570454601705404894846719808518116656621063533⟩,
  ⟨-98776455478002331760023148576329331835282094711522892450160,-98776455478002331759571839150511556335808565384464421928774⟩,
  ⟨79017076321445976527172000677676619390769598143362753770824,79017076321445976527426575320478791464571432743418565188374⟩]
def bs0_4_0_5 : Fin 8 → RI := ![⟨-1222618081166190197666486329032615267918416433288611817580,-1222618081166190197627934393741969835928879794380399327142⟩,
  ⟨11589591023412123392269656248673388021922497488122129930676,11589591023412123392297381476933354621219263415512319704079⟩,
  ⟨-50951999795585485360759527323217714528562690771897656080772,-50951999795585485360178831362316486354418547759540336625696⟩,
  ⟨28991545377023857261092494496972339787247949520768276519013,28991545377023857261307366812575725061389712649899849149750⟩,
  ⟨47576457779142075127628105416467416240771436671226972549902,47576457779142075128243582216188440221777702404459223272106⟩,
  ⟨39949599636243894271055383153356112983116745919928817632673,39949599636243894271319541242511171197584556076230344930374⟩,
  ⟨-102092012891767856175114924476081403792163044834710307126453,-102092012891767856174650528697458933237417317950125639557276⟩,
  ⟨80714961878993383661509830108304562663290524756290657710781,80714961878993383661771786501632059273611336270997531829268⟩]
def bs0_4_0_6 : Fin 8 → RI := ![⟨-1231359203068069077225824015482343896791369359701288186268,-1231359203068069077186131519960365147470963296629383228044⟩,
  ⟨11143436599261676055982118556307758348309311668275192057820,11143436599261676056010664036327239749415795053965985532720⟩,
  ⟨-51091508562119167239718808352721308872567562776798508086441,-51091508562119167239120932483352675398998366551681852303287⟩,
  ⟨29053451425077837747201165143419889853908049891459574433079,29053451425077837747422394463313348245384827445286136889006⟩,
  ⟨47677016678530958891000306137906796830555519953884826912254,47677016678530958891633991838319813227914945458854655226916⟩,
  ⟨40069891421201713610048411797828168606613206010036448521314,40069891421201713610320385012452996908964918971975009372479⟩,
  ⟨-105302617447859161413338424765346366105791515921012111920818,-105302617447859161412860289822849969057230881191224381084243⟩,
  ⟨82228497234358551528468976802437855193485679741962364204528,82228497234358551528738683183990330453082671216450015989855⟩]
def bs0_4_0_7 : Fin 8 → RI := ![⟨-1235996129523948180619515762848374323149433224958493160505,-1235996129523948180578624960611045734472157374069538951677⟩,
  ⟨10677489290694104200259227032131751488517464930849855739014,10677489290694104200288634293199437734767713264053090975439⟩,
  ⟨-51050351993759532882134686664602790571382668650165352197292,-51050351993759532881518761069213484601748587682313874276405⟩,
  ⟨29012034352137911918403173006218892786823747897574181850718,29012034352137911918631081185081037680893308701913475271027⟩,
  ⟨47607933534510230491718933043832776546752927643924399596718,47607933534510230492371749560294880469981962255472693029189⟩,
  ⟨40048718294909251149290954388690033000027769851302572886419,40048718294909251149571138408035777504713010547667150276723⟩,
  ⟨-108389133005815730560470935638297359185365685126870966392173,-108389133005815730559978365919029862226596576303822680084352⟩,
  ⟨83540402996676608498572646591460654666067936625145647781213,83540402996676608498850495342594950204348001787463981128468⟩]
def bs0_4_0_8 : Fin 8 → RI := ![⟨-1236326312122959681478386258910615420684340087132442780111,-1236326312122959681436235532425605666212726532650501913223⟩,
  ⟨10195112899276704178716287056938135775183625580307002532132,10195112899276704178746600412267759626056984280447791844368⟩,
  ⟨-50822824873326549964060398930096583467199331248878754174853,-50822824873326549963425495482721470343570511507959842374329⟩,
  ⟨28864252418372072962234007416938051928633281916055429037795,28864252418372072962468937885046993193552294281653495879713⟩,
  ⟨47364212059183478995566156144182152687291318683812544036592,47364212059183478996239087192850104577455364331930048185455⟩,
  ⟨39881496537655170582796409487514086078751471935695295931880,39881496537655170583085226515277927384064396347599171137626⟩,
  ⟨-111332478662829896727330988361816107979109743340093847244648,-111332478662829896726823241622316091182549155158751230934716⟩,
  ⟨84634195754865317949477171852915522712826701265657896896814,84634195754865317949763581658359428684402677721438775138902⟩]
def bs0_4_0_9 : Fin 8 → RI := ![⟨-1232179892851956892221145638765843304116137664669234284037,-1232179892851956892177669146279482486731492453560182474559⟩,
  ⟨9699715200015827716768382099746851535200749118024709223832,9699715200015827716799648900467101600191315143862543756427⟩,
  ⟨-50404953630571222069950571238812106593795277225738297761275,-50404953630571222069295698185337395574723261394699359205660⟩,
  ⟨28608070311858821262154180771710275709247990242472063894023,28608070311858821262396500503381906906386177663957509197830⟩,
  ⟨46942508913714274078101150377717920791997894540097040327947,46942508913714274078795247113911069339238184919670393332962⟩,
  ⟨39564992743237314862077442708517266762927023729825306404039,39564992743237314862375343892786076055035508325573412667874⟩,
  ⟨-114113829213486164481644095080035037035081593880601969866776,-114113829213486164481120378191962231280632867862545104976781⟩,
  ⟨85494424258793619828704187205539815604850131918216959889224,85494424258793619828999605453166058850306201137073436041262⟩]
def bs0_4_0_10 : Fin 8 → RI := ![⟨-1223424739952931370177374057635405559135009106895157949956,-1223424739952931370132501340394627393545358894631432662266⟩,
  ⟨9194706596740142167136419830625551750065277276772543360638,9194706596740142167168690748252566341771307676611172195321⟩,
  ⟨-49794664969652236455063308507769536830945788760115821034847,-49794664969652236454387404549637528236329043183874709332208⟩,
  ⟨28242552023439321070841271130110365763027201701756856229160,28242552023439321071091372832878497873222499940414732272871⟩,
  ⟨46341286798571932814128164597670062477419517756318904134857,46341286798571932814844551886522657053250790674668392912575⟩,
  ⟨39097457286288549730365600530504162111369517511228423055440,39097457286288549730673068655072085880612712181828357910033⟩,
  ⟨-116714823256167203947535703673948479167975737396576696106091,-116714823256167203946995167892687780289615173222459515870730⟩,
  ⟨86106905573400870851808567696562096352318370710772556781080,86106905573400870852113473146274418425500605295026406938644⟩]
def bs0_4_0_11 : Fin 8 → RI := ![⟨-1209971370641234245929341647392971107369845274707797784342,-1209971370641234245882997192386423761993220413778314544431⟩,
  ⟨8683461526528438804147434423856299968436029970133746813591,8683461526528438804180763764755247682664436690965099111982⟩,
  ⟨-48991934048116246016290775639257254966239537318895238123213,-48991934048116246015592703347169985990290794895322581576927⟩,
  ⟨27767941227760607076336368774072067623900545116433612020877,27767941227760607076594673325786058118914244580299892275876⟩,
  ⟨45560947109981845560328291783682348861498257963974370702010,45560947109981845561068175180926732232137369181167828236305⟩,
  ⟨38478741935846660326685952697496820962894986242285738768749,38478741935846660327003505177965786350075920552060911504616⟩,
  ⟨-119117775695888045188610323535953477778993030918236476859746,-119117775695888045188052059233403828914583244162390262812286⟩,
  ⟨86458956719125021851492373484626708480686051789686650813235,86458956719125021851807279239488569334130992678237237269889⟩]
def bs0_4_0_12 : Fin 8 → RI := ![⟨-1191777645003915184421818863017295736756231844019349005647,-1191777645003915184373921615671584588927273738944306266695⟩,
  ⟨8169283221930041404816532340026817060653160404944608171734,8169283221930041404850978395864028278870747053150457818021⟩,
  ⟨-47998907322043103975819352963214812183286113940484843971124,-47998907322043103975097891437027224714892049176005130497503⟩,
  ⟨27185726402655040629006682894302518228949236160643302179976,27185726402655040629273642059154002351750362231253815167847⟩,
  ⟨44603937587901002511335313891959351819482345393672121868683,44603937587901002512099987423669180312481039444610077676786⟩,
  ⟨37710397786920926638739463826959848587219087191679423978796,37710397786920926639067656049747802229348606459137447577826⟩,
  ⟨-121305891060194449998663773768502897435769624403549808308761,-121305891060194449998086804563026773357616944196963873239999⟩,
  ⟨86539617052367839308040355561993280345739323045203904045054,86539617052367839308365812379406239037817660334221062888732⟩]
def bs0_4_0_13 : Fin 8 → RI := ![⟨-1168853102440074943627349823636313174664555858961840996004,-1168853102440074943577812644111553249091997964171189564683⟩,
  ⟨7655372198149477123314551829063302093923999087853936728138,7655372198149477123350177267819840538694401676506838795285⟩,
  ⟨-46819995360077468872108197818026590913813358945275262921171,-46819995360077468871362034497093423132793252614076431025114⟩,
  ⟨26498688059732776600288659276378361563265330275418170775625,26498688059732776600564758735281772837914211982236890043179⟩,
  ⟨43474830599450710950719323381532118617615776061149083857575,43474830599450710951510178224295512630531515255683102466912⟩,
  ⟨36795749835091191331856186393930544223051093314852314003425,36795749835091191332195615441737556315756648560126206678984⟩,
  ⟨-123263473787442244966767645132857558890171296745806075335011,-123263473787442244966170921339828955291934644995529619031079⟩,
  ⟨86339856496582018705596048921898674648237543046482693257706,86339856496582018705932648908017598500840106994022188571805⟩]
def bs0_4_0_14 : Fin 8 → RI := ![⟨-1141262800924801954072437765049538550140961675230338176682,-1141262800924801954021166820864273907341346985014521697742⟩,
  ⟨7144798599309963537655004098338229781900166701129345176422,7144798599309963537691876401113197336837355328374202014221⟩,
  ⟨-45461931283008267811102575941264107637886577908498672745930,-45461931283008267810330297455735594762665854670943189168949⟩,
  ⟨25710925697290474828590164931678564287762188490339564638214,25710925697290474828875927667525055517834142791862742020935⟩,
  ⟨42180368080123052273537363419094851238852038718469337534570,42180368080123052274355897596681197897944249281116565181824⟩,
  ⟨35739944803561024711678545491871013310383466686864770929437,35739944803561024712029854305416937731754001288920625383190⟩,
  ⟨-124976131481722154737898856166995811448792180895041741115051,-124976131481722154737281247482373166369757765881688882140660⟩,
  ⟨85852764725463098717369243089109196856552425449556508478599,85852764725463098717717623825892804297083361979957368057863⟩]
def bs0_4_0_15 : Fin 8 → RI := ![⟨-1109130511361698711793143037308559803921638445901140687635,-1109130511361698711740037123964789973349816408129931105722⟩,
  ⟨6640478337495394376472449362911825628272094086407705597506,6640478337495394376510641312505518173998439223500639910522⟩,
  ⟨-43933791012668405446260588697662070244430145936830499685832,-43933791012668405445460670635267370584520790810649989647301⟩,
  ⟨24827862424943132720661369816133989285787782741059511997698,24827862424943132720957359900342554864821095801403451875513⟩,
  ⟨40729469698447466350047101775080143699210612641277765255598,40729469698447466350894931004576138960506625641331461833095⟩,
  ⟨34549969252226879625165851722734916906476897759862062141543,34549969252226879625529733755840745813810702450898732747987⟩,
  ⟨-126430967069957306131551627311262632232105188663598792156851,-126430967069957306130911914627852595076194097829125030254299⟩,
  ⟨85073716538217309976025748396246803548489055559329532856482,85073716538217309976386597557739995947458746139841509812684⟩]
def bs0_4_0_16 : Fin 8 → RI := ![⟨-1072641115670888345012457690065199820622512343025071135480,-1072641115670888344957407470111692936267535870088459933082⟩,
  ⟨6145152808745649165987949205395606002069867223112054585102,6145152808745649166027539433549053167690293758020830999056⟩,
  ⟨-42246972214800867253014952301179996902849937776489998538881,-42246972214800867252185747745471580054276786084094929596321⟩,
  ⟨23856225646142183863802076940045249919131222016152666647095,23856225646142183864108903773704625129743896388427382502217⟩,
  ⟨39133201516662402359429779319974592898331333373094778655090,39133201516662402360308649160042782814629708518449677961393⟩,
  ⟨33234635553263037705662839903397492524524988307582854131178,33234635553263037706040044336928055285071717987055886381339⟩,
  ⟨-127616755854785298776487895275025157793023480996847007124296,-127616755854785298775824761516255725057267746054552803712276⟩,
  ⟨84000508961142160668507045220171303662576975138921677668583,84000508961142160668881105742990861533804858557045582423935⟩]
def bs0_4_0_17 : Fin 8 → RI := ![⟨-1032042059400625045274097112188831349508568723278420852723,-1032042059400625045216984261720388677799511153134345896576⟩,
  ⟨5661371880859622613067007064964708767042909721083372002369,5661371880859622613108080666168099403491724344519532611109⟩,
  ⟨-40415129687741974631433578595144395094741706888705125126004,-40415129687741974630573305269478594568636542499635409100412⟩,
  ⟨22804002713471369158078727532829010505809712931497336684920,22804002713471369158397050603752749662450325838238549326342⟩,
  ⟨37404703280923451358202722660047322781291079116465583176418,37404703280923451359114522136958044035352709038634491243121⟩,
  ⟨31804533999997375665992269464488503433946106983363981760807,31804533999997375666383607054544576884784352913307228144886⟩,
  ⟨-128524103637673935216593538622900576457709871898627972073716,-128524103637673935215905558461569701164309721152498287535285⟩,
  ⟨82633466061423824098222970347210919052492525473443389503878,82633466061423824098611046229994287461541359977019369313650⟩]
def bs0_4_0_18 : Fin 8 → RI := ![⟨-987643718767453149589620452167725955972266208745694635253,-987643718767453149530316702066217525892662880824418894368⟩,
  ⟨5191479818423882553891199164581360653145914963932694312520,5191479818423882553933848385580572657153785620930625950862⟩,
  ⟨-38454065965763174152385505024309710839325059812810824912449,-38454065965763174151492230850354902083861459069097777026225⟩,
  ⟨21680371080517808764841148843126855645796406893738334343388,21680371080517808765171683069573625176306020591865904031951⟩,
  ⟨35559073471585437908617741897480084895450241982805017938995,35559073471585437909564518811577797124048190395867529805788⟩,
  ⟨30271950110879160410175220638785516151478662247841791877026,30271950110879160410581570286125945056581694860759211476953⟩,
  ⟨-129145582390842565952005312926205240127869517074879682866876,-129145582390842565951290941235291093949741327653812147326089⟩,
  ⟨80975508062294686250592628503228752263392925158793319360237,80975508062294686250995591321301551076586140371571398756648⟩]
def bs0_4_0_19 : Fin 8 → RI := ![⟨-939818559003281989880293177492516593627510422895729605097,-939818559003281989818659234717533653854321862270810661380⟩,
  ⟨4737603832017925174446247097296320689895453399973226837775,4737603832017925174490572112863648099648428104551422448947⟩,
  ⟨-36381577046477109610428140376532195790157887812463058150549,-36381577046477109609499767226001192050531690266387509672664⟩,
  ⟨20495603145975331468445647755439181867578629720781644571471,20495603145975331468789169498386173332032995989641308722436⟩,
  ⟨33613212349922635017848338862008299442102569572476834777110,33613212349922635018832317009170705384111065980066143312788⟩,
  ⟨28650747076243685868928293677333021276029941730108559148252,28650747076243685869350609818697577487473433683884384225373⟩,
  ⟨-129475840378627020010427100082699994824287324368545275219737,-129475840378627020009684658941251510521648836268937470305573⟩,
  ⟨79032182089811908273991569457537282078041091831098193578783,79032182089811908274410365692631202241600362631352696973876⟩]
def bs0_4_0_20 : Fin 8 → RI := ![⟨-888998986079233512222251008941924094145513437265647203746,-888998986079233512158135340804641035546723015611831706008⟩,
  ⟨4301644998144315330347618772798920494716376208686122803862,4301644998144315330393728560041572081243057052302548969733⟩,
  ⟨-34217254380119846725013157064970265584732736944782471237644,-34217254380119846724047402447510878989706964227417290705531⟩,
  ⟨19260946698098778413304965830420784179839076183569028912678,19260946698098778413662319669511243002352867771961589960170⟩,
  ⟨31585624416347267469802205355528759194649457951540695056641,31585624416347267470825803936081760757230753703069730621756⟩,
  ⟨26956214243592808545277742443601945743364506598535975332012,26956214243592808545717063381874050855813304534606818059442⟩,
  ⟨-129511684157656767544103294745943353717763924802363624896902,-129511684157656767543330958794469474222100547023239939126890⟩,
  ⟨76811652739117649706795810120066760953557840236633609326668,76811652739117649707231469421052310932643857449851972159349⟩]
def bs0_4_0 : Fin 21 → Fin 8 → RI := ![bs0_4_0_0,bs0_4_0_1,bs0_4_0_2,bs0_4_0_3,bs0_4_0_4,bs0_4_0_5,bs0_4_0_6,bs0_4_0_7,bs0_4_0_8,bs0_4_0_9,bs0_4_0_10,bs0_4_0_11,bs0_4_0_12,bs0_4_0_13,bs0_4_0_14,bs0_4_0_15,bs0_4_0_16,bs0_4_0_17,bs0_4_0_18,bs0_4_0_19,bs0_4_0_20]
def bs0_4_1_0 : Fin 8 → RI := ![⟨-1126100095393391792847814518521087500235653407971284349817,-1126100095393391792814214104313031554745351192502200774594⟩,
  ⟨13414299502971684260605635227727422571904132839814142356410,13414299502971684260629799492025340378867054497022966185078⟩,
  ⟨-47841433185506003411795842615279821646181381762012326612555,-47841433185506003411289729895697873590064785698748452642431⟩,
  ⟨27295673554034197466320122145180993214479687281843705839915,27295673554034197466507396759322460063012889480624124166968⟩,
  ⟨44797544380013551200537691361617037928085277998113863529856,44797544380013551201074117749805088932823490531910205600929⟩,
  ⟨37462228884243262046242331055601618139917924644165491507368,37462228884243262046472561292933166177269503251781498742688⟩,
  ⟨-84839093422376457483826236618592412250812810543075842358393,-84839093422376457483421486755820265896182261972719666631722⟩,
  ⟨70742726550787769488373258936394084582280017776716964894606,70742726550787769488601570258613586708503525939832649718976⟩]
def bs0_4_1_1 : Fin 8 → RI := ![⟨-1087959962202641544243224932809137435649763319335872609383,-1087959962202641544208274806587328541263707316665613437790⟩,
  ⟨13866276626859742456112922125959782815417461659056608958703,13866276626859742456138057056798344694841358481675040888577⟩,
  ⟨-46476412115545715275124825091973861161165502756448950489724,-46476412115545715274598382074862385286234686552482083015709⟩,
  ⟨26537931201753105724024922952338841804826435083375197982847,26537931201753105724219720295070821438965156900339729556738⟩,
  ⟨43555094240947758496485419579749081527133516065235628235788,43555094240947758497043393950538195509936838420181282990348⟩,
  ⟨36379014805248175401756442155906808706561785803088215018862,36379014805248175401995920627960868178322278559042738820565⟩,
  ⟨-79515194253087877418497802656415434753505122398482583910809,-79515194253087877418076794191922150138087954881225877807901⟩,
  ⟨67360961995255591426322071638222129006673265054289707692326,67360961995255591426559554113289590736431356685047586780719⟩]
def bs0_4_1_2 : Fin 8 → RI := ![⟨-1043579218450084818229553176435682854216792934770338482885,-1043579218450084818193157546119416214816982573374623261480⟩,
  ⟨14240783657304975160610280866535844873300581384301814775632,14240783657304975160636455354290658750691301325222139878499⟩,
  ⟨-44812387283418511318341184481245926060379745175844779409938,-44812387283418511317792968279913572740579242365097089010723⟩,
  ⟨25607403428026801695889026349174174717297027434942754686741,25607403428026801696091880325371957415161593962237854554427⟩,
  ⟨42028965946403284812050431219094802228015210458152180966382,42028965946403284812631482881009803151361262642944304920985⟩,
  ⟨35062709334598822880903682514386611221749837722248008548959,35062709334598822881153065589068512290835564136019767859887⟩,
  ⟨-74120533459090444774481174620943100684640918477279938532750,-74120533459090444774042753645396821093198977036910889850353⟩,
  ⟨63727695685392933720006003786563754492952197769963702785152,63727695685392933720253308311711147236920749063209633892761⟩]
def bs0_4_1_3 : Fin 8 → RI := ![⟨-993946258608113126565853035364336483587178185181745630677,-993946258608113126527907446208471811565606476107428120687⟩,
  ⟨14529401512674842976580075935925305648347665968919796873022,14529401512674842976607365100862825004908099441976684898293⟩,
  ⟨-42888015691064212330260831047942162897027674849328559397359,-42888015691064212329689268292643718811541778499623892677508⟩,
  ⟨24525814709273615740059658352221575150672581647700576694151,24525814709273615740271151148818236827094885050902489679521⟩,
  ⟨40254826023310516217755730678445548740591299130439765160882,40254826023310516218361527238359871050654370446398904836077⟩,
  ⟨33543828283234027614863218817240640461851774059504589928082,33543828283234027615123222219083848734480274595310329889974⟩,
  ⟨-68714498543908707245935255128865903442675249166805234151279,-68714498543908707245478163382666403595910888252003118580914⟩,
  ⟨59904474575349830484804827155701178514500424932602429278670,59904474575349830485062663490064930121887372359189294768973⟩]
def bs0_4_1_4 : Fin 8 → RI := ![⟨-940094517528187176199868205766992480419978803972860394011,-940094517528187176160258478838143472640170727457229254162⟩,
  ⟨14725015048645228976404515727200724377293892058837207337843,14725015048645228976433001682889727298073066882242198151251⟩,
  ⟨-40745741607514077405024981510195482353965004214454194903882,-40745741607514077404428352358724733591402167479875534339596⟩,
  ⟨23317170931848752470990093520843535591486015335864159339903,23317170931848752471210861523318374626059786701494190263908⟩,
  ⟨38272081999730667314905927217851052567082436813638355394205,38272081999730667315538291528080918852334233806248889239956⟩,
  ⟨31855801850800407468427396563145609213409157171574628286340,31855801850800407468698802646879178278724486254394399097613⟩,
  ⟨-63353340586994166145355873558312991810552092079590059153872,-63353340586994166144878735644498823880031976895789970338049⟩,
  ⟨55952475241910765022304596912472204525743033512471439097141,55952475241910765022573740890037158570870084306637686910752⟩]
def bs0_4_1_5 : Fin 8 → RI := ![⟨-883069458122755987294217672909243470045729571480938252963,-883069458122755987252818669791339247420612580559080157883⟩,
  ⟨14822115339289325619299636039451754587631846587498338257200,14822115339289325619329408781144692392166683122456452650979⟩,
  ⟨-38430272193375941964940646729706806986441126409104616661518,-38430272193375941964317066260535801396576025323875795406077⟩,
  ⟨22006887909669905636401916698156050943627118800771617247852,22006887909669905636632657375547613244635224344902458114909⟩,
  ⟨36122450830468474791196737864066768881495630340981834158837,36122450830468474791857667743691597381268117372698246534429⟩,
  ⟨30033777053064171494326958930713059348898077230822831876398,30033777053064171494610625145506458522703887723735289807604⟩,
  ⟨-58089067901877579983867284990527243334838194440087589691937,-58089067901877579983368593494445657508151517449205943305580⟩,
  ⟨51930988665570457695041564227135413733400497803786269119542,51930988665570457695322866150432144824784587310442194946612⟩]
def bs0_4_1_6 : Fin 8 → RI := ![⟨-823898531667781898117841797538830665765093529870274518068,-823898531667781898074515982520439617673897436502702983527⟩,
  ⟨14817071759003236279717087884751841906846280043483499392786,14817071759003236279748246323410351155217742233584766379930⟩,
  ⟨-35987076638506319518459339747359647426519285396400895562067,-35987076638506319517806736302307942511805162766107841395493⟩,
  ⟨20620926710886230433975857067264483395453865495001482738657,20620926710886230434217336985935292531979944313171299851170⟩,
  ⟨33848539553611733667831417956204278794246396535054457474093,33848539553611733668523109145565293316887643134629325565671⟩,
  ⟨28113440780086115663257164252923510395905562788600257583334,28113440780086115663554032994287619238152797046459315358165⟩,
  ⟨-52968526746445772924951696179797272218138092813449493610209,-52968526746445772924429794349243829192457119374605113973908⟩,
  ⟨47896061283090761637658109179606945459465334016715376658633,47896061283090761637952503589499449508943836133009069450012⟩]
def bs0_4_1_7 : Fin 8 → RI := ![⟨-763564950672829511675450521973839786905992889509610985092,-763564950672829511630046286834078336991492419460181019030⟩,
  ⟨14708353399040864597425702359731582083689181714524210893814,14708353399040864597458355526782943547271140044870752277661⟩,
  ⟨-33460975315039172117084973080286163560592660736228271686831,-33460975315039172116401063031285470925679923230422307210228⟩,
  ⟨19184975084377278675558596223491671597457902969547097996528,19184975084377278675811660384068862744194961011075272828979⟩,
  ⟨31492502516806143542551855631953861775541983306469732577839,31492502516806143543276728537236447175759089089103449233263⟩,
  ⟨26129915630308284155778111623672784211087009237484829361741,26129915630308284156089221712036793291279133236225572904580⟩,
  ⟨-48032694951354343378281517563590649694472758032699800763114,-48032694951354343377734579129216524046405270347885258111090⟩,
  ⟨43899338438437960925338075573897573487077069046276317324111,43899338438437960925646592632488898193845323652635951590547⟩]
def bs0_4_1_8 : Fin 8 → RI := ![⟨-702985805865315865458323993554634644639439457533731125530,-702985805865315865410673702720747825871158705653163196186⟩,
  ⟨14496679564394120118105165363782336764624619400720427364969,14496679564394120118139433816975027479104454883912588198363⟩,
  ⟨-30894875427866110142812374587478973355817199103588424281798,-30894875427866110142094632891382176388897864968892305757631⟩,
  ⟨17723708812940175667081689415589482754904040250778207141164,17723708812940175667347272148436441098256517838488873785637⟩,
  ⟨29094830425370280352047094238618070255840774114072273168071,29094830425370280352807825140665232727887487834482066471105⟩,
  ⟨24116772739682924988225101270802068872305936760230339686203,24116772739682924988551601346105346460823312793682712535370⟩,
  ⟨-43316202537527482787090607147426657047826492487729534361126,-43316202537527482786516612774749149988473692750954022149624⟩,
  ⟨39987143126562863033687413246095635639121077031131922180344,39987143126562863034011192019678936731211094864977472055553⟩]
def bs0_4_1_9 : Fin 8 → RI := ![⟨-642994785543618584575227525386742381679540432817031414281,-642994785543618584525145230385882605565299234496917978823⟩,
  ⟨14185081963952882026113572987409462674526111870814800194770,14185081963952882026149590454500966435956541617462084654500⟩,
  ⟨-28328696734682543769914974974373095384847898859743887495088,-28328696734682543769160600746443342196437954334835354171714⟩,
  ⟨16260159523608337840733368121767939347858746615394777698977,16260159523608337841012505825671355288057088772304666231508⟩,
  ⟨26693314437239416045422681164344547204742639256153007627606,26693314437239416046222238707146924454050330781126932332236⟩,
  ⟨22105195584126656942380071262210675602708753227878508006086,22105195584126656942723235444492753178951644654325756714516⟩,
  ⟨-38847081350606808362281908000740174976198802287462197397572,-38847081350606808361678617758478294743865084206968495859332⟩,
  ⟨36199808447546209470540122218343230053686332782580253962929,36199808447546209470880426207464377517275614493489223333022⟩]
def bs0_4_1_10 : Fin 8 → RI := ![⟨-584329529066859554136805791351612738985052720723560673821,-584329529066859554084084552741158143769858587754465606108⟩,
  ⟨13778866863621397225441741128991921710907408956251434098316,13778866863621397225479656433724497347993167174636833289611⟩,
  ⟨-25798516339369762877512257038534161136558250847039888104235,-25798516339369762876718133213503752064421026637421736825310⟩,
  ⟨14815207074215843271910297944742387373031030629799728047764,14815207074215843272204144013349279688348242963506052175676⟩,
  ⟨24322214736385916240647504235856868725437404701144935024429,24322214736385916241489192181598508693268651706948573269567⟩,
  ⟨20123317166366385214901091235798224310046686597945602670453,20123317166366385215262337475348161282451822157995527574482⟩,
  ⟨-34646734379336367459558938260661253816740000738593735694739,-34646734379336367458923859360766277874761572601470648946922⟩,
  ⟨32571267667037841117004952179986332005676572417463807277038,32571267667037841117363187516649041476044541567875737460901⟩]
def bs0_4_1_11 : Fin 8 → RI := ![⟨-527623465980127040623604468942068823369820207412498491285,-527623465980127040568013210789747198025441413442397740585⟩,
  ⟨13285473411802910194380048054724089214965378280953298567317,13285473411802910194420027378974669571620667730782576916885⟩,
  ⟨-23335946611317601985844340840806965918395819537169675847424,-23335946611317601985006986792877527656110302931883633304953⟩,
  ⟨13407205873921411649157625516164957251167121669263205972256,13407205873921411649467467869790997050204116395833163994583⟩,
  ⟨22011648696353671185719671687113393960994351402031544478380,22011648696353671186607179134001120891052469854571568365379⟩,
  ⟨18195741139120309084567935878688502361670204453498246700818,18195741139120309084948847509165760976425865556200220792806⟩,
  ⟨-30730105564007209252311781337997925381567519500290087820225,-30730105564007209251642130244789036301856590367043532740444⟩,
  ⟨29128892340633784811009259625588206919002872944832853173774,29128892340633784811386996446734655687879936799592492424920⟩]
def bs0_4_1_12 : Fin 8 → RI := ![⟨-473401850547337053809891163083252364087154817728280910749,-473401850547337053751170968949793033323766942677448362630⟩,
  ⟨12714233409854527409978261985441150065349041091602165557373,12714233409854527410020491533023447786010130674017305595751⟩,
  ⟨-20967746134090500114736194617550778143589851896699573614812,-20967746134090500113851710367917544492071005706963894483639⟩,
  ⟨12051746109847616791540768925361168584131298281017280481711,12051746109847616791868050655629637708118385108840761499542⟩,
  ⟨19787200068028320229273777956620986640649613464795325201140,19787200068028320230211238473055695769582502352322823072346⟩,
  ⟨16343246228579634966258528951978227017280309674334770694693,16343246228579634966660880070361545176075082055739494707558⟩,
  ⟨-27106023154886883054276054564995841489322639978808658538412,-27106023154886883053568712376647300958404883193632069454830⟩,
  ⟨25893557534037004777151388453460800469381931014029970492275,25893557534037004777550386069384516031246022187225053065361⟩]
def bs0_4_1_13 : Fin 8 → RI := ![⟨-422081589990723995157885855916979748985385036391901635754,-422081589990723995095745595342460575324532701811554460174⟩,
  ⟨12076046437864952183516006778342457708122728511263616758474,12076046437864952183560695920287827430710699966179482508907⟩,
  ⟨-18715651223221717558546623283339949940738154518792202272823,-18715651223221717557610623623298820328363060666903766200866⟩,
  ⟨10761543455029127561923240402564068288414775386377233940101,10761543455029127562269584148536385587657328618288690564126⟩,
  ⟨17669738574606586170359395289261277065030149956291499240862,17669738574606586171351456736433570348496573023773152256506⟩,
  ⟨14582663598566172059863409099450624415950724104992564807908,14582663598566172060289194533379549292446904072581395021820⟩,
  ⟨-23777684404258240936817066975228868496031308715732011808231,-23777684404258240936068526740519191470932771274115255301792⟩,
  ⟨22879904397680224277383974307357962491567527678918674652452,22879904397680224277806210919274515552926580223895956562503⟩]
def bs0_4_1_14 : Fin 8 → RI := ![⟨-373974378991850196041775402141112729638825877798896695231,-373974378991850195975886551749264417911917519761979452404⟩,
  ⟨11382991022098528363145479989225382703345969580218258361108,11382991022098528363192864988266796862386115103714699821562⟩,
  ⟨-16596405677818981839387493926142201133652112298374433325051,-16596405677818981838395030408974441794104487277176019525020⟩,
  ⟨9546444869179347928012290511402922290720667658931146674787,9546444869179347928379527324570840193934550166115792471813⟩,
  ⟨15675429585671956150420945035438470770144368556438495469549,15675429585671956151472852247747355397304123460070986920882⟩,
  ⟨12926909091421997397852417636543060495547401204006622305551,12926909091421997398303888430142026824276359623211335838396⟩,
  ⟨-20743246652009328833087093296174863262608653596448806259690,-20743246652009328832293397629621335755118696454808230945817⟩,
  ⟨20096764544622101248319850030265196378611103323552747431997,20096764544622101248767557920370162762571929345896921519770⟩]
def bs0_4_1_15 : Fin 8 → RI := ![⟨-329292592535721855490300238084400986823648856551592010543,-329292592535721855420290730105524379861027521547966886917⟩,
  ⟨10647896607345994323417883270899234475504813043036549718547,10647896607345994323468231705402400600297251104007616063390⟩,
  ⟨-14621959422463979753920690872275763465857408101009494121089,-14621959422463979752866159155437978601631334616900495994590⟩,
  ⟨8413533819829063392942033249791902606864164402859758671517,8413533819829063393332236879830383900700304653589804180705⟩,
  ⟨13815906567293282348307082792758562723478719840283020525743,13815906567293282349424775785369725488506249647438402203121⟩,
  ⟨11385146881044269115655021578865256012550117635346936279131,11385146881044269116134727142701111030019944192423533555397⟩,
  ⟨-17996489532257438088392145305301891270239601261713713292925,-17996489532257438087548812286600749243649740246910691266347⟩,
  ⟨17547707826300318330893535038285165702678820719703315257709,17547707826300318331369242368401522958279843945185391142065⟩]
def bs0_4_1_16 : Fin 8 → RI := ![⟨-288157355169856261683996719883800909513885731032559455170,-288157355169856261609443611105144513808743206296489793255⟩,
  ⟨9883902345787950452519789416242273295871883627617748717852,9883902345787950452573405452444823127307726140515695150147⟩,
  ⟨-12799802610707599657888003502359071949426631712821106576608,-12799802610707599656765032922134282466199139728649090905644⟩,
  ⟨7367315696094155752308461668673844717667672307418984999132,7367315696094155752723989423636478299526163546480590293299⟩,
  ⟨12098574844346421495615836873047875087984189521976147982113,12098574844346421496806067881179265409983607050377836757854⟩,
  ⟨9963057999755450199912537616315275789818851666999659730295,9963057999755450200423375959792861180555187741825034871852⟩,
  ⟨-15527514740627652505484105430541696314941306962305806741901,-15527514740627652504586040294903020006024226868743491276994⟩,
  ⟨15231674930645391832268433314400473365892926327915514137090,15231674930645391832775013939698800306599420295325782570702⟩]
def bs0_4_1_17 : Fin 8 → RI := ![⟨-250608198101830249806603734012893550651230225998678403463,-250608198101830249727024437019652720505915063896329547724⟩,
  ⟨9104027438256878681889355472867437397053699460182294700473,9104027438256878681946586171069339361256288663651035000922⟩,
  ⟨-11133400386222086162433580873512798627455919649940870021531,-11133400386222086161234902363886708631120696250711853136296⟩,
  ⟨6409963244247080247723871783532938632207749771199648383555,6409963244247080248167413403236351656533366715528487581718⟩,
  ⟨10527013676100999109040081052583686951028307917873245610720,10527013676100999110310554523640585835541243117797917186274⟩,
  ⟨8663186264148908814584790925390382467996399250406707287936,8663186264148908815130068740341327319480077512740753336998⟩,
  ⟨-13323453099798230051553473013294760344863958180085959641942,-13323453099798230050594862523161314287735102188297892629092⟩,
  ⟨13143658287333445287828314686254664000500555618341417290403,13143658287333445288369047738059130337309791758545957697869⟩]
def bs0_4_1_18 : Fin 8 → RI := ![⟨-216613735058195677392408511288629472723985229948718029849,-216613735058195677307250263236143772067160224354243799830⟩,
  ⟨8320774679759232212939449597907323831374412390096522007921,8320774679759232213000692486168346073856975289094799107971⟩,
  ⟨-9622694422713630094702466221657403878109374907283013989069,-9622694422713630093419753685668399906283894064052644906625⟩,
  ⟨5541602286309196739546151978683785799528630835218267040193,5541602286309196740020788331353851802624148556954312548670⟩,
  ⟨9101444351925958793376076848934442940951354571225089427749,9101444351925958794735617572237388211125298557897216585405⟩,
  ⟨7485334985633861613030639070153579918339844490007738117749,7485334985633861613614143890871807122539226696745674629764⟩,
  ⟨-11369153043812310400820460052623905574845504896025076832138,-11369153043812310399794645638728939111051563325422282433872⟩,
  ⟨11275398504128906910420403890839357306557854708808836698071,11275398504128906910999045335226030170698769843210101700295⟩]
def bs0_4_1_19 : Fin 8 → RI := ![⟨-186082830435837572079017902385898666893997900675798853820,-186082830435837571987645058357452650486127128295196834367⟩,
  ⟨7545784311820217890272153833789467250013989415729400335676,7545784311820217890337866046109985054381857078636033788722⟩,
  ⟨-8264640076283035938941602100468444797306027304779446498291,-8264640076283035937565281013958658740249595015953616166618⟩,
  ⟨4760619488905127673282851163199309715403404805568959111617,4760619488905127673792125066964679645580707078261098741788⟩,
  ⟨7819234471732636572629298572315735338881947907792391117420,7819234471732636574088054539045812120740303119842778022839⟩,
  ⟨6426990093400524311554390497097266315321946784173227301244,6426990093400524312180477766326885479987844443584370161246⟩,
  ⟨-9647829625811987981464959718499363227360670261977436513811,-9647829625811987980364284415929676289832684987490180895469⟩,
  ⟨9616068406787197165853065178461509075502814385582732485265,9616068406787197166473934156571370879106753111084166517532⟩]
def bs0_4_1_20 : Fin 8 → RI := ![⟨-158875803979057455199075095272749511103431733976967021967,-158875803979057455100753714137286900327260521459783563378⟩,
  ⟨6789549901488072411773680344453902512203110405663146441901,6789549901488072411844389706096809911657153950326264922692⟩,
  ⟨-7053752003213250869052907207568645117465136504242965313664,-7053752003213250867571922440692747384668190327001016874251⟩,
  ⟨4063976237602789204334598558686279064495947199265021485126,4063976237602789204882600693541677619834034032112811783749⟩,
  ⟨6675412317713499401666228293721033178580441746675369390018,6675412317713499403235916781763682538538759480494423133050⟩,
  ⟨5483748519997805702454071275586363447619427244658158641021,5483748519997805703127769962316265481889740180862870495422⟩,
  ⟨-8141658320529410704843428730192219952853817188240140748245,-8141658320529410703659051499963790764178120990535043561300⟩,
  ⟨8152922197029953780437627301884787399811416025814020428828,8152922197029953781105710867418423251160287197846864619965⟩]
def bs0_4_1 : Fin 21 → Fin 8 → RI := ![bs0_4_1_0,bs0_4_1_1,bs0_4_1_2,bs0_4_1_3,bs0_4_1_4,bs0_4_1_5,bs0_4_1_6,bs0_4_1_7,bs0_4_1_8,bs0_4_1_9,bs0_4_1_10,bs0_4_1_11,bs0_4_1_12,bs0_4_1_13,bs0_4_1_14,bs0_4_1_15,bs0_4_1_16,bs0_4_1_17,bs0_4_1_18,bs0_4_1_19,bs0_4_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_5_0_0 : Fin 8 → RI := ![⟨-48493744738479334835193394622433269929361140598964193475,-48493744738479334830472686839441545025926438723957673877⟩,
  ⟨6581533089339978584580372721824974209865908136211308835996,6581533089339978584583767692786784785046734744723583704288⟩,
  ⟨-2073723659479442102323870433797633360824380334278213420559,-2073723659479442102252763862324682354285103463465106426799⟩,
  ⟨1196355380615890843178915466706458063391764806206831570586,1196355380615890843205226711653156839646989114713372349989⟩,
  ⟨1969226453678954602951334536906384654945472404058153327599,1969226453678954603026700043118803102831470225854148884340⟩,
  ⟨1602459147203947836687331432060538868088957823687171072192,1602459147203947836719677749773649258655650640130827967820⟩,
  ⟨-1987458510310430438353627870062111018572548546861301663160,-1987458510310430438296762326217515977455602631829460845530⟩,
  ⟨2149169242876001125025947278860499098962381249632872576007,2149169242876001125058023997589929285085100879674428452467⟩]
def bs0_5_0_1 : Fin 8 → RI := ![⟨-56385069554091126460442482045245839410667034137089113290,-56385069554091126455523979834767934691186720230707094063⟩,
  ⟨7279817481825030786406624170607478550501062021848090533269,7279817481825030786410161388530663672640314273716566651743⟩,
  ⟨-2417308215877670600559788822159821325330489583614324705129,-2417308215877670600485702933973746974632215080297474239494⟩,
  ⟨1394689780616753331910755197418137494476116746048108883118,1394689780616753331938168865533282464115227455913591133445⟩,
  ⟨2295411672931937320179332825203570494625256712803601826360,2295411672931937320257856094582230443423789524951662307225⟩,
  ⟨1868373973280561086984856045906473662485222291090864125439,1868373973280561087018557652209710270052404380507926482184⟩,
  ⟨-2329045614251680948250320850214578051918058033085734097845,-2329045614251680948191072678975104569776066742972811311968⟩,
  ⟨2513004613203585124874500330416235077178690524700009147499,2513004613203585124907921041722204832498737851112649260641⟩]
def bs0_5_0_2 : Fin 8 → RI := ![⟨-64856037452324308221327160533225158270229661573825375951,-64856037452324308216196295084491904780177122092047383076⟩,
  ⟨7950900990850560661142806348472103507543766965214268789212,7950900990850560661146496290745176643916669906827339368893⟩,
  ⟨-2787612586879349854207140427568461969824737033318541141721,-2787612586879349854129855777147119589139430632963478423898⟩,
  ⟨1608460186449259040917415165994779637780575874419919458844,1608460186449259040946012457718318662564377258029837541335⟩,
  ⟨2646916463460364647330630751226787456970469834252050166300,2646916463460364647412544373003927755349168614312105894609⟩,
  ⟨2155087785725198632387769348984003457543432616429142506166,2155087785725198632422926069455192285255156485657141331699⟩,
  ⟨-2701118767875075783176061149660961816303313824664305889098,-2701118767875075783114254855447256178884221539282840404698⟩,
  ⟨2907599841689978513825311145177344577822607144689663628012,2907599841689978513860174842614780658335269413806563206937⟩]
def bs0_5_0_3 : Fin 8 → RI := ![⟨-73825407845839795576828817637388303464082574984138383527,-73825407845839795571469647561882222064380972484149497725⟩,
  ⟨8579396585593665411012985189945734422246969266707811001368,8579396585593665411016839321068000740683734033025284917443⟩,
  ⟨-3181311390422633338940672438093851909721503309470776118805,-3181311390422633338859948905198028168756393232486119520780⟩,
  ⟨1835742310591378041272197569673198554482426589316665744215,1835742310591378041302067335617685310997841504739848660167⟩,
  ⟨3020565902093308841442550116684390477767088591061230119141,3020565902093308841528108593123435916276776037304218896306⟩,
  ⟨2460053029681162271318688520322612908711048551410906595942,2460053029681162271355409585450458912186712842181163745491⟩,
  ⟨-3101372743349443447948302403695513527578658392777604105441,-3101372743349443447883745956886361965023578086378191395784⟩,
  ⟨3330057212597640626179999629912076702830499460861064506230,3330057212597640626216414633559042283357851214330648738896⟩]
def bs0_5_0_4 : Fin 8 → RI := ![⟨-83189721959025924332578217650090188224659519479855106977,-83189721959025924326973242942773696280639785373143589812⟩,
  ⟨9150833757806026592109718919641718222801989213238508220603,9150833757806026592113749825015971970914541714479745880081⟩,
  ⟨-3594061189674980312731564964413509038541153712289718819123,-3594061189674980312647138951842039740164893722273200598942⟩,
  ⟨2074021728587284012600942167361350786904106384541078721161,2074021728587284012632181945214019990599097724454584421886⟩,
  ⟨3412216444729419553639381216483818182387887369485917032828,3412216444729419553728863932964981727916538183952282646567⟩,
  ⟨2779933166840650644937091300528403529537918891893253972050,2779933166840650644975496620451259335547362594496074761297⟩,
  ⟨-3526514760417100347778429155399666533158927608502820851210,-3526514760417100347710911751312975248082553913943538292698⟩,
  ⟨3776412721177565522377792577768428360224677157727111478458,3776412721177565522415877798340240810507589889258873060777⟩]
def bs0_5_0_5 : Fin 8 → RI := ![⟨-92823834203399927720527587291337931105984658050011713127,-92823834203399927714657539573009272324594349109831795958⟩,
  ⟨9652140566368867450788020487655411799534075200285405187653,9652140566368867450792242024438432280007597066345062199298⟩,
  ⟨-4020507622292321532396998634185821519665913579454463023758,-4020507622292321532308579908260620923641735641963758988012⟩,
  ⟨2320198033176701807000091161611724881260582895298982634029,2320198033176701807032808345235612119198619573485973171412⟩,
  ⟨3816763410650305519140279023781767793790954905481627030347,3816763410650305519233993597556466789866326925286506952366⟩,
  ⟨3110606737596798784635754392279485933892626854820205317569,3110606737596798784675975994045974290457207190207402722733⟩,
  ⟨-3972228029356958264080735362029151452769427630026434593259,-3972228029356958264010024894185904428694502090370191397313⟩,
  ⟨4241615256074854238995525230990937579097426160635248270290,4241615256074854239035411595121558046846813606056022905495⟩]
def bs0_5_0_6 : Fin 8 → RI := ![⟨-102582377886670178338385535162485747948042634705706399795,-102582377886670178332229139886093523634737713648405072475⟩,
  ⟨10072075549009436027199447135446454174020935944910781330818,10072075549009436027203874603562060125608404513114917486017⟩,
  ⟨-4454334708089139458233076486656976214039080705959769900251,-4454334708089139458140344595409785331750696404071297409383⟩,
  ⟨2570613542664531534098080570193138834650769189109772711044,2570613542664531534132393734989334753826075108973328072641⟩,
  ⟨4228188794720102121305876762336732076566934029703253125745,4228188794720102121404162838873880698002905503883186661143⟩,
  ⟨3447203918634494501033467056890349708748300664626588610374,3447203918634494501075650713823108147166945480631613324924⟩,
  ⟨-4433168657719009143796789163589824419352511875879824399321,-4433168657719009143722629359256493193143970624360173554634⟩,
  ⟨4719545117106106835091488182100765352949287262521271835256,4719545117106106835133320248126175611660063982850994779070⟩]
def bs0_5_0_7 : Fin 8 → RI := ![⟨-112302233866143534496168770921531992852885978821005597149,-112302233866143534489702476408335142340124192879979841325⟩,
  ⟨10401588809199394516123913888425623459226855541432936139534,10401588809199394516128564225432563751334760153268013051827⟩,
  ⟨-4888360634705944267204862849970421374523460984379242753817,-4888360634705944267107463041697705629682139822721137662554⟩,
  ⟨2821109069523419649549373071127872299660156460119401584668,2821109069523419649585413484274304238934713848298901044426⟩,
  ⟨4639653481884756078698511862383640350611509073884027171766,4639653481884756078801745441273289348902458751572751383120⟩,
  ⟨3784178981472571312209569299423772226610288740556679224331,3784178981472571312253876387765293772602403073891779176171⟩,
  ⟨-4903001533579605398597175267130598778711989466626855928529,-4903001533579605398519282423294588250532093543069955044291⟩,
  ⟨5203077391678549128995244427065437454279182530698246703945,5203077391678549129039182226194769247554722309924389174674⟩]
def bs0_5_0_8 : Fin 8 → RI := ![⟨-121806022367637338412553909918640240932335877150088428211,-121806022367637338405751577103960660081135702989632650152⟩,
  ⟨10634095325676620282721031449355718530976685574259770518140,10634095325676620282725923453571874864782939311320990837743⟩,
  ⟨-5314682278532699027514691633533300368814927600171534122724,-5314682278532699027412230183531808203194565342928975750678⟩,
  ⟨3067108060061904796286932178080014086011175452501994847354,3067108060061904796324845527758477040818764585335018825876⟩,
  ⟨5043635972156634993672546569887310115371324200124673213919,5043635972156634993781144958010700576536934327864026496890⟩,
  ⟨4115420502395294424132055469492040488156728137136761471432,4115420502395294424178665094268619068748132089176201133586⟩,
  ⟨-5374479650232011208508629215826431834384303617849057233739,-5374479650232011208426688461880129202310630058212180524659⟩,
  ⟨5684194135743050479553797029854988615068318095164868987569,5684194135743050479600018174315887211247801826650048772137⟩]
def bs0_5_0_9 : Fin 8 → RI := ![⟨-130906579107182811196713053397461216249037649722403158974,-130906579107182811189545598963649459476987008274326834438⟩,
  ⟨10765648417932589645655435341297354914264905030788868208656,10765648417932589645660589928446260503994901493701550118591⟩,
  ⟨-5724868093876829428317676418115845988804422199213396775591,-5724868093876829428209715253304074054964200169160355578387⟩,
  ⟨3303728879829503336784950862563919299684815148708622032571,3303728879829503336824899246987228319213501179807357589213⟩,
  ⟨5432117201316357973238007245149147526732718386746430421798,5432117201316357973352434754016047703290360111592814173958⟩,
  ⟨4434399165814408708699635738088905379248561340901731284668,4434399165814408708748747178365674171107196443919528205222⟩,
  ⟨-5839569660143916112008241993066608023536434587296066990437,-5839569660143916111921902991994809198046006938345431142957⟩,
  ⟨6154147134097576413780911523637967860982389739488556683785,6154147134097576413829613631550997803783360004838176745883⟩]
def bs0_5_0_10 : Fin 8 → RI := ![⟨-139412310182466548299934367907465845015332195955511361961,-139412310182466548292369352005879409729334719342932427966⟩,
  ⟨10795006915825960743480952165111315335447571303833061960700,10795006915825960743486392664818353298104561395198086893734⟩,
  ⟨-6110195899277538634086859091153557420994424292921899492634,-6110195899277538633972909580054530342363737182227673146816⟩,
  ⟨3525923202320180887413661180663866105293256163662485867655,3525923202320180887455825405940609114204484989556015717717⟩,
  ⟨5796808062300201914948401776944470520195622627554435519718,5796808062300201915069176304659960686790409484140630494660⟩,
  ⟨4734350616625226665411305082738749525718306404635170069896,4734350616625226665463140616551134399152419177638182390199⟩,
  ⟨-6289624258326274560212728117431061782294232118923555958327,-6289624258326274560121600099518842457731423223077727997561⟩,
  ⟨6603670298898759653298928438798803225059637436098662820447,6603670298898759653350331935563754199996366677240184942800⟩]
def bs0_5_0_11 : Fin 8 → RI := ![⟨-147133250752335300150952891739887132988409882849232072845,-147133250752335300142954039681381734471650931552806157085⟩,
  ⟨10723595443318813012392354781512002543421538593215185156580,10723595443318813012398107281288182665445463660985937465790⟩,
  ⟨-6461928689605179565329306070406242082507521850379268371391,-6461928689605179565208821818518283223385404996966592683037⟩,
  ⟨3728636468508903537837434966763017303152479202591312616669,3728636468508903537882017212794118071223426836590206643464⟩,
  ⟨6129412972592917400554272914595874604393636244832089383308,6129412972592917400681973582011520793107981057158343669961⟩,
  ⟨5008488190396630770908340457745234278021553319846561703361,5008488190396630770963148639478548706815070982108409040170⟩,
  ⟨-6715599372375668067753497083878467097645069833091319840788,-6715599372375668067657143085005190254367790345966920783703⟩,
  ⟨7023237623447084348319874139399855834437369016384198699398,7023237623447084348374225507759139481642533055027188710907⟩]
def bs0_5_0_12 : Fin 8 → RI := ![⟨-153887586598407184026531366812335938044222398841208633113,-153887586598407184018058011843882072319299345401809314424⟩,
  ⟨10555362873545448858037501506664258083241206093440515683372,10555362873545448858043595252642142903041902523180921710818⟩,
  ⟨-6771618171183601168104738817934976158957038479845042363001,-6771618171183601167977107274447019912356904875331364317424⟩,
  ⟨3906984377773014237034143800849891555147227048108559157076,3906984377773014237081370727058008071107675620030666956268⟩,
  ⟨6421919550074947927593386495028601834967160081348669763923,6421919550074947927728662541743718653435588825287332444786⟩,
  ⟨5250237684213260799168193023871113769144315562329670079632,5250237684213260799226252502358492372877192688133124746946⟩,
  ⟨-7108311217919882800081492104421706262220013690707290651691,-7108311217919882799979422253760202654427229719937839644802⟩,
  ⟨7403359235784187868094145925291011508120067377554998218046,7403359235784187868151721491604634620451155510668185566856⟩]
def bs0_5_0_13 : Fin 8 → RI := ![⟨-159508342460723380326722493295771366417038634558024526255,-159508342460723380317728924759022021842401105733495262532⟩,
  ⟨10296549082856981518638231051994545861786492583864133684292,10296549082856981518644698917710228930469307934723714674695⟩,
  ⟨-7031422585985298434745424045711361352398942874471843602325,-7031422585985298434609956685015654987318456619802169890093⟩,
  ⟨4056437541833956876146538632809487769787709323085248535539,4056437541833956876196665011229725218658700333400436926383⟩,
  ⟨6666901473329535367905240035906969341835599412962719554570,6666901473329535368048821226835137820433641196660141853337⟩,
  ⟨5453483878999985905228825051402520092419175700620021863147,5453483878999985905290449036346285439819955050448964881223⟩,
  ⟨-7458725267127710025548794393611458009258062730888062630402,-7458725267127710025440458061560237857482653836872994828784⟩,
  ⟨7734904759522823809231813274154551761017483391451741567831,7734904759522823809292923637594896844769203129234881957689⟩]
def bs0_5_0_14 : Fin 8 → RI := ![⟨-163849903626653225232338278945260715461977286569620857960,-163849903626653225222772976574434963930517176382458193907⟩,
  ⟨9955374398591036413336539129351456919330216971868117709465,9955374398591036413343418166411235858564182126631659196961⟩,
  ⟨-7234422924153707818936835840749277248790008940691035210408,-7234422924153707818792756628905567095229379100619869219934⟩,
  ⟨4173004996871413378432159858778993654937378367307717684070,4173004996871413378485472841761309257553830090665826649563⟩,
  ⟨6857819263009187764706837187042303821776060032124567190420,6857819263009187764859546036749397365174794442007569341227⟩,
  ⟨5612816567208988462795721596502112585959897935335495191334,5612816567208988462861263105069226614822886352446796509605⟩,
  ⟨-7758266329181097590519348725305922088587941303075256449294,-7758266329181097590404125299858050020987576194485613750723⟩,
  ⟨8009440205255045321608983180149649511048353462944424442912,8009440205255045321673978415567769272628679982907360681308⟩]
def bs0_5_0_15 : Fin 8 → RI := ![⟨-166794023233763941956921365685140343157972428792413939683,-166794023233763941946726096340369564525371973732251483801⟩,
  ⟨9541669471481891122302342241349064746157106270307612305643,9541669471481891122309674329027806521793039135155742978242⟩,
  ⟨-7374920167512488716507213840849328119284711382961676672890,-7374920167512488716353645629956668612041673424625535285879⟩,
  ⟨4253406428417725637615583900319772534769189610685595062221,4253406428417725637672408054958407166512991430479527769871⟩,
  ⟨6989302360447055481860502535747476357546511770735687425238,6989302360447055482023268728990232077737609623696980348109⟩,
  ⟨5723762648071854771568693105057116024945611725643427969273,5723762648071854771638551151067659574528691818790168884493⟩,
  ⟨-7999136536775539689568002024102610867522162374482087295820,-7999136536775539689445190030115140972076910124139471649824⟩,
  ⟨8219562318498999922933828839991691586840617222700924474006,8219562318498999923003104635520336359868722116449703543686⟩]
def bs0_5_0_16 : Fin 8 → RI := ![⟨-168254979985647685827503118788830320383569581433799819619,-168254979985647685816611866263501074014954036176661977296⟩,
  ⟨9066465588810479398623419821410389208789651449244580807377,9066465588810479398631252436297345875089125382378110450020⟩,
  ⟨-7448696026725339174587335142799582557682071994324743801639,-7448696026725339174423283551013023532519915135121984292700⟩,
  ⟨4295222875584110248875279821719749286843924026076772593581,4295222875584110248935983094658181006444451882881006805600⟩,
  ⟨7057395752512228244626033557656535550564992919000746847222,7057395752512228244799911034873784451141161008600548051707⟩,
  ⟨5782990639042965342096484201646303752421022744223254771414,5782990639042965342171111128539923882736529272946171743623⟩,
  ⟨-8174626343769622694450203254056026665877635002940211130707,-8174626343769622694319007461732413924772082231443973568099⟩,
  ⟨8359213001124750439813569939740729110923754557385060899521,8359213001124750439887574868642216745368031596824745548803⟩]
def bs0_5_0_17 : Fin 8 → RI := ![⟨-168183588937470986885770054508653215920324057319318763677,-168183588937470986874107745827435590524141462929573477694⟩,
  ⟨8541566521261238166531394676487004924983124804554482361271,8541566521261238166539781808488541197732983176801078069872⟩,
  ⟨-7453220863810632776529054875137036918386731567660256893340,-7453220863810632776353389101286008545792231392213388772715⟩,
  ⟨4297016422770464713639624900295727361869585712885497835454,4297016422770464713704625716807177685253584410504994021117⟩,
  ⟨7059755621564806016735349192227694192422942136591172929790,7059755621564806016921536484032214188228075285026153683190⟩,
  ⟨5788474829125357176931618910527709848846242280740494775214,5788474829125357177011529118777100816215436420255014358288⟩,
  ⟨-8279402887028986213274581333591766704319826894775418088664,-8279402887028986213134097415495480346946635697896060890235⟩,
  ⟨8423956321704040231344564960114761300257331821381824768419,8423956321704040231423809135453486403564104911091506655336⟩]
def bs0_5_0_18 : Fin 8 → RI := ![⟨-166569828128712563086389437496197907652381621127179208971,-166569828128712563073870419832269238184160205734259756930⟩,
  ⟨7979122772478005431722604892786613947062827874864819233794,7979122772478005431731608140475047362353790459875629663079⟩,
  ⟨-7387795099116481001885055625994991411345594762099435314915,-7387795099116481001696485507855219335743727782532281644021⟩,
  ⟨4258410938519790241808167548614268210786699536613553117546,4258410938519790241877943301626205283287979670687581198465⟩,
  ⟨6995781051659195263450191048540268891476695016853056444664,6995781051659195263650055591543833889722252196805403476034⟩,
  ⟨5739608254936693073031938592994051176784602765108862676445,5739608254936693073117718976277192360633161283462244465103⟩,
  ⟨-8309760384856132250248702548975978332269845463494146996360,-8309760384856132250097898733008340174885293390277056921133⟩,
  ⟨8411201834058397097448507884959239640404911512518815950546,8411201834058397097533573308790829547464682947077698822383⟩]
def bs0_5_0_19 : Fin 8 → RI := ![⟨-163443920373701543685110323424670134748733526975027970901,-163443920373701543671636533711356652167717548485502249797⟩,
  ⟨7391227515042203198425978083842465148810233274948445993436,7391227515042203198435667970808529973637835567309397882092⟩,
  ⟨-7253614193171840241011453111742834030322246996233077363080,-7253614193171840240808501555458652148260207176940394284668⟩,
  ⟨4180128165538323584810608597259835148114842601920357746678,4180128165538323584885705849170885524998487128356415331744⟩,
  ⟨6866672503753946908456377761092834576467864100061028519260,6866672503753946908671485119826249802214593384176094274895⟩,
  ⟨5637256573089804774732256066440207518946681134594262419462,5637256573089804774824578553472278119039451016227367058931⟩,
  ⟨-8263818661247875398419215924196399624747516244573289641438,-8263818661247875398256910944778032309181928306707587006153⟩,
  ⟨8320360389731256026722708760687138051992498760868475258671,8320360389731256026814261761357097423294436451730966167813⟩]
def bs0_5_0_20 : Fin 8 → RI := ![⟨-158875795754805962293438954082141649387978258697614554245,-158875795754805962278897707577687570603162295135269857472⟩,
  ⟨6789550706790026597171590188453877983458631182622366885931,6789550706790026597182047753695017196924724163750307176288⟩,
  ⟨-7053751937839588676954692932993437546606622381529116548904,-7053751937839588676735662602908087231240296307169776858909⟩,
  ⟨4063976204885718554549589420225140687590461131819234914968,4063976204885718554630636228517430686704270148843853584621⟩,
  ⟨6675412258845251055432256255373712964974830622400783454489,6675412258845251055664405427572269492734598775086198903239⟩,
  ⟨5483748482632527986545208009421462767077461674172275537261,5483748482632527986644844716722194779453905105308275399888⟩,
  ⟨-8141658310560238000560668182851058492537655293829886290519,-8141658310560238000385504642020954650207879811534935326295⟩,
  ⟨8152922178033863431532838955307543027986923525363934355345,8152922178033863431631645213923791212608159388560630217481⟩]
def bs0_5_0 : Fin 21 → Fin 8 → RI := ![bs0_5_0_0,bs0_5_0_1,bs0_5_0_2,bs0_5_0_3,bs0_5_0_4,bs0_5_0_5,bs0_5_0_6,bs0_5_0_7,bs0_5_0_8,bs0_5_0_9,bs0_5_0_10,bs0_5_0_11,bs0_5_0_12,bs0_5_0_13,bs0_5_0_14,bs0_5_0_15,bs0_5_0_16,bs0_5_0_17,bs0_5_0_18,bs0_5_0_19,bs0_5_0_20]
def bs0_5_1_0 : Fin 8 → RI := ![⟨-48493744738479334835193394622433269929361140598964193473,-48493744738479334830472686839441545025926438723957673877⟩,
  ⟨6581533089339978584580372721824974209865908136211308835998,6581533089339978584583767692786784785046734744723583704288⟩,
  ⟨-2073723659479442102323870433797633360824380334278213420559,-2073723659479442102252763862324682354285103463465106426799⟩,
  ⟨1196355380615890843178915466706458063391764806206831570586,1196355380615890843205226711653156839646989114713372349989⟩,
  ⟨1969226453678954602951334536906384654945472404058153327599,1969226453678954603026700043118803102831470225854148884340⟩,
  ⟨1602459147203947836687331432060538868088957823687171072192,1602459147203947836719677749773649258655650640130827967820⟩,
  ⟨-1987458510310430438353627870062111018572548546861301663162,-1987458510310430438296762326217515977455602631829460845530⟩,
  ⟨2149169242876001125025947278860499098962381249632872576009,2149169242876001125058023997589929285085100879674428452467⟩]
def bs0_5_1_1 : Fin 8 → RI := ![⟨-45863303133275404293509630290657806707607713430047720078,-45863303133275404288722991031837355198824474211249367272⟩,
  ⟨6348771625178294517304908156577014580668048293213647853513,6348771625178294517308350543192616671501683449511323138530⟩,
  ⟨-1959195474013365936246224076581278487375343128667424149661,-1959195474013365936174124399537286366116400380353069331943⟩,
  ⟨1130243913948936680267934748746416188569018692473425309434,1130243913948936680294613468082597029285538468099613245811⟩,
  ⟨1860498047261293697207615853085242208081365971025648853304,1860498047261293697284033947019741156271542122938999384752⟩,
  ⟨1513820871845076753254371464581851864290039910228138234071,1513820871845076753287169545158337660523562484329596950070⟩,
  ⟨-1873596142330013601722191085809581487799060509813518174350,-1873596142330013601664531332833360299673766136421316700635⟩,
  ⟨2027890786100139791742648264149740583157835592486798973285,2027890786100139791775172980404683959012997787985382928636⟩]
def bs0_5_1_2 : Fin 8 → RI := ![⟨-43297266315029405989118709410567537861216145583199173665,-43297266315029405984264519919166229863248078626828934982⟩,
  ⟨6112987840632219080352769227893735019959916345519253155325,6112987840632219080356260194317407900588051721423261436071⟩,
  ⟨-1847636156836562076325403632370085022813876834208646562320,-1847636156836562076252286466919257932854375512333658500610⟩,
  ⟨1065847559041053986276378501660259059548506710798967188636,1065847559041053986303433717657027282699744650476523877682⟩,
  ⟨1754582926540904414788708240122547663735640517182366583584,1754582926540904414866204765027153650970842885608619903442⟩,
  ⟨1427493594971541702610899129240008749453560425428503765668,1427493594971541702644160064410739507258807480169712191782⟩,
  ⟨-1763121113203168356760648448145264927141099840027305725156,-1763121113203168356702174986528600512646117494920581291995⟩,
  ⟨1910030091341923946137377889795134680956357418109894027117,1910030091341923946170361602859471997210105206435858864596⟩]
def bs0_5_1_3 : Fin 8 → RI := ![⟨-40798643194383528238354705501671027583835202681523333613,-40798643194383528233431296184723832835640453745697658410⟩,
  ⟨5874751625732230155123064568307073415081959241684814257666,5874751625732230155126605315252755311518693401185399804410⟩,
  ⟨-1739168870247617430869752563632451931178883557901028786657,-1739168870247617430795592761208734216891088836218728992486⟩,
  ⟨1003237585800466091905235249618008162404176898825022501286,1003237585800466091932676267886195227253411943399867117953⟩,
  ⟨1651598681264858153582117486361280989402030540922056916595,1651598681264858153660719097077768181900262261171983337754⟩,
  ⟨1343571670466924099630150478481662723286082114228908732574,1343571670466924099663885708307540552363331562773066271415⟩,
  ⟨-1656118801738456610697983768133887589922980942479751601800,-1656118801738456610638676485996042126896718097283529172628⟩,
  ⟨1795694481406447686939705443452556002700052072925325202413,1795694481406447686973159498036950840345446529423662612618⟩]
def bs0_5_1_4 : Fin 8 → RI := ![⟨-38370168383359310226028844882752615825612418163394875212,-38370168383359310221034493014306643277696136969893352235⟩,
  ⟨5634644185602319010099699011461146191484974226396796277428,5634644185602319010103290777854195977656648782279294506860⟩,
  ⟨-1633904207967702930191273998547978439201931884202222355660,-1633904207967702930116045610259436813405416967491553182418⟩,
  ⟨942477978494238347714166820020192915075966838585851954494,942477978494238347742003242311616610127382585767791306209⟩,
  ⟨1551650942897134674365311954134534296890156930312507825507,1551650942897134674445046153766147972722551204921464339159⟩,
  ⟨1262139711678371986873470954402561020779382401127379350941,1262139711678371986907692283012036247817815028469124481116⟩,
  ⟨-1552662394739174689286562719899276743438950239430617226749,-1552662394739174689226400865320690185784751635491941447840⟩,
  ⟨1684978115036935171226578075572690860040727882779144793804,1684978115036935171260514177420936763435921089494742361476⟩]
def bs0_5_1_5 : Fin 8 → RI := ![⟨-36014300008627594774648963206985825321204623782068605096,-36014300008627594769581890533716834836092728798283172523⟩,
  ⟨5393256056737541916750986915353181041243440666069032369039,5393256056737541916754630980052336637069895417024125051698⟩,
  ⟨-1531940165802058441352340330854774486768726566535187014865,-1531940165802058441276016571417734923236485771980394304433⟩,
  ⟨883625418653095623858471038912778921972820440116774856354,883625418653095623886712776465532543081893246884226279188⟩,
  ⟨1454833353818978554756307367569137402515456232089987712874,1454833353818978554837202545706625312384920576486322040836⟩,
  ⟨1183272574699924974724074900833893694211925287111935804367,1183272574699924974758794512829294738969671113490650234497⟩,
  ⟨-1452813037032311742251478609263578393557712799744804802499,-1452813037032311742190440761443176775213388396198321078408⟩,
  ⟨1577962072583853485821497747039374446508030842072424366908,1577962072583853485855927979197981858089168211221456149528⟩]
def bs0_5_1_6 : Fin 8 → RI := ![⟨-33733218806443310695065248463119992929063075219561994629,-33733218806443310689923618706418336402511525507088940687⟩,
  ⟨5151185054512246012023422038565515116306743476759872472670,5151185054512246012027119722159307517604015472558034409397⟩,
  ⟨-1433362170159380171922119355088037678664451109133176097928,-1433362170159380171844672565201773116787046868084613328251⟩,
  ⟨826729301658325237152715656154631767566437287813308315245,826729301658325237181372943615409268029748065626200759890⟩,
  ⟨1361227591848715431743179882127695406542949046797577070102,1361227591848715431825265354728191678027886418156264774519⟩,
  ⟨1107035386231201015322583230704457179280058164576006490523,1107035386231201015357813708277712515266131618012565498480⟩,
  ⟨-1356620027263998378250893185270135795472583934039272423019,-1356620027263998378188957224435512521382279498949933246441⟩,
  ⟨1474714495632011554079629377546560786977928059709812980647,1474714495632011554114566217337823448197950773145149835913⟩]
def bs0_5_1_7 : Fin 8 → RI := ![⟨-31528828467873029693600636256577675535503440708504197003,-31528828467873029688382552504808079237388960332003900450⟩,
  ⟨4909034161380322685669129531081340268977843437796304002836,4909034161380322685672882197763490780068073370257057557236⟩,
  ⟨-1338243162463135948512962130319103926537222583009231997648,-1338243162463135948434363737386244276597074249016558241044⟩,
  ⟨771831785864906745569736086076693198461540140717703180010,771831785864906745598819496035239278887447176996248551814⟩,
  ⟨1270903448218013157964443926511232095825640496536991995071,1270903448218013158047749977530501955260395411561706110445⟩,
  ⟨1033483614454283327772219655904020726444546129916040131449,1033483614454283327807973996704910333975047650800773136452⟩,
  ⟨-1264121056895030614762844835082169811297561639810970040588,-1264121056895030614699987911076803416154519108623390473505⟩,
  ⟨1375290778060144431102231998637529744465480559522117569869,1375290778060144431137688335378848430424468152469436356466⟩]
def bs0_5_1_8 : Fin 8 → RI := ![⟨-29402757195567915148461660971190245167661882074253969816,-29402757195567915143165162955430511506028434724183062649⟩,
  ⟨4667409365798788596573589189705148767700053422314865187704,4667409365798788596577398249233764194625725767209575730016⟩,
  ⟨-1246643737177550730723322622957293614417370053698853350062,-1246643737177550730643543100049114512620958265071052061443⟩,
  ⟨718967872932848787864399271193875373440040345287579955982,718967872932848787893919729366875197153719342490226902248⟩,
  ⟨1183918956841888814087896844394752919395655825895720953322,1183918956841888814172454769279681816210319192258816782891⟩,
  ⟨962663181134627855305933356989830526449036198119882022043,962663181134627855342224992792640482021743071025858283938⟩,
  ⟨-1175342489655106058415838603483367205117848017724227627075,-1175342489655106058352037102950228696798617972308245382206⟩,
  ⟨1279733805767065062792332112928757255145916803212307278014,1279733805767065062828321266443712140652948164857220127940⟩]
def bs0_5_1_9 : Fin 8 → RI := ![⟨-27356360426502681573793229719458435498547027061636634010,-27356360426502681568416290965594643477145725623019818340⟩,
  ⟨4426917462417694053094857859416911522913518793736340193599,4426917462417694053098724769162599527708356776929319247161⟩,
  ⟨-1158612330889287412069855071015005689654549372801934945817,-1158612330889287411988863893974313166934891184378418324008⟩,
  ⟨668165517873876540406659683599328558942932835633338050215,668165517873876540436628484703434478408995297691938470124⟩,
  ⟨1100320572448362937127070218842104341514528855853319428940,1100320572448362937212912369997140026582986532913879098577⟩,
  ⟨894610612937824840149038741713868551239334843151018716629,894610612937824840185881557931251622403928539449860718744⟩,
  ⟨-1090299678566349637387591891277742408463843634407458061769,-1090299678566349637322821403353495670178716208237497214996⟩,
  ⟨1188074242088211282400193963703950043762502867724141112530,1188074242088211282436729703673517809385244972006299476528⟩]
def bs0_5_1_10 : Fin 8 → RI := ![⟨-25390724668865146496904834210455023224889957443089631151,-25390724668865146491445359060052580483787927269017566398⟩,
  ⟨4188163824525739483094356544369169082305667105172026275172,4188163824525739483098282811457525439455047078208617200394⟩,
  ⟨-1074185459635425862273189226546061999898076854009056679143,-1074185459635425862190954829113488105257865325540004704709⟩,
  ⟨619445767174118409966869788605390166020313488929384717787,619445767174118409997298612961636807399747974265248138735⟩,
  ⟨1020143394892230960318892513514689925872905307809714586435,1020143394892230960406052347863261561982979298742806995145⟩,
  ⟨829353229764366658579479647932151535921146491957441384705,829353229764366658616888004028136420709531786833132227599⟩,
  ⟨-1008997317525850915499266779604196580704007203648083812023,-1008997317525850915433502060032675520823697326135254094001⟩,
  ⟨1100330855747151171956154666235926677263624348110082026048,1100330855747151171993251232441352064550855260270409923758⟩]
def bs0_5_1_11 : Fin 8 → RI := ![⟨-23506672395683914745290291601173102621863116433896373380,-23506672395683914739746112093051277664777734196401276642⟩,
  ⟨3951750160115334818144205073881700512050470715724309864301,3951750160115334818148192257435973639498049712473304733432⟩,
  ⟨-993388001450485615670196179533027303892957661450297247439,-993388001450485615586685906375145031159325312786339753896⟩,
  ⟨572822923226033431253739694125203025141632545902644890112,572822923226033431284640625039802743005331905197985335064⟩,
  ⟨943411436767199147240974570392565670641416314744032809497,943411436767199147329486699162354369610848851404156407399⟩,
  ⟨766909367740118829253985583370399623397659625154534802704,766909367740118829291974334227860771111622879826588117557⟩,
  ⟨-931429824343279305399607614896393980103704313060752313547,-931429824343279305332822548464116818517212440013267277089⟩,
  ⟨1016510888038765124497043909930560107526146833398157770355,1016510888038765124534716033442732848001143816000048036084⟩]
def bs0_5_1_12 : Fin 8 → RI := ![⟨-21704767932856737085655799818659778747937419837298686891,-21704767932856737080024672422569115424848120692060941753⟩,
  ⟨3718272263226977953405279142089997836409995655605942212770,3718272263226977953409328855580115855855435901750694257508⟩,
  ⟨-916233520920753561066095898514662439172795537278459439803,-916233520920753560981275956024371791966353848739998320845⟩,
  ⟨528304733194976703370708979041297532940753424026297433583,528304733194976703402094521010752360292776989219514105561⟩,
  ⟨870137931252414979056128477110985769322874745887479439241,870137931252414979146028717980354020514490866331677319214⟩,
  ⟨707288634361530581118220757549640265589514249551048940148,707288634361530581156805275851159627104514861524626887800⟩,
  ⟨-857581752062876060541619731254322683811509596570279007284,-857581752062876060473787292444440758261452775106157078541⟩,
  ⟨936610455824442663850500812204177727184408882320534766467,936610455824442663888763737577955014108979919698691053436⟩]
def bs0_5_1_13 : Fin 8 → RI := ![⟨-19985324275012052776685950548845333850872464132720148514,-19985324275012052770965552742079355227711780513598593694⟩,
  ⟨3488317772445256093126076092653619450815353590175451804693,3488317772445256093130190006358173514505289832640563029119⟩,
  ⟨-842724632383425171975723014453599626825985568919215769644,-842724632383425171889558419184681123258193159977249248795⟩,
  ⟨485892600357728787476752934343957892386670350528030823262,485892600357728787508636032135589876670410114036776279547⟩,
  ⟨800325676983571633890449360053673130527925096308467650648,800325676983571633981774791805628553280047310865677953651⟩,
  ⟨650492193181979687809417980250935697658303871323530300079,650492193181979687848614179935879658088606700252470306990⟩,
  ⟨-787428225358643715238647619149292982264345007674764256718,-787428225358643715169739830903529403392072658721957366588⟩,
  ⟨860614986834393151066458878209652017693646328185086239679,860614986834393151105328386745426156160039442489813102012⟩]
def bs0_5_1_14 : Fin 8 → RI := ![⟨-18348410759114053687701523802045598083353726051809548317,-18348410759114053681889450479206884841515182058708309817⟩,
  ⟨3262463948542829817225711435000049714072953732909016300080,3262463948542829817229891278588266977073061974053151033303⟩,
  ⟨-772853398290970579624936204880404689688095884558606111317,-772853398290970579537390729468928452930051278066721120426⟩,
  ⟨445581815881971040451884566315832579331789404089034216863,445581815881971040484278624978241647427437132502007944210⟩,
  ⟨733967416625226337935332030160949689071269804806221163753,733967416625226338028121050000778220265909199064720619358⟩,
  ⟨596513075338917755379583819796784450024161795577627619745,596513075338917755419408180661607978501362303828540473560⟩,
  ⟨-720935398776500987840368925810388485033207626362608831042,-720935398776500987770356816281157997417781603333376133351⟩,
  ⟨788499683717404677696320584829982805270392026782953632249,788499683717404677735813018968947545552773992342724674697⟩]
def bs0_5_1_15 : Fin 8 → RI := ![⟨-16793861522910484987544740232811856098928931544895309418,-16793861522910484981638499938294050513045085440757186389⟩,
  ⟨3041275483300774258916266565871817290130661061083420430218,3041275483300774258920514131113030502177513261737082203369⟩,
  ⟨-706601759177211593236444431480081307920280559637262425648,-706601759177211593147480547895440591973966711669229925926⟩,
  ⟨407361808966787201206718243015372698666417887982061309653,407361808966787201239637148877001586693807303209989920747⟩,
  ⟨671046245739292658566532340252627545213989347203947283168,671046245739292658660824723955844587236785910354093725501⟩,
  ⟨545336515160251483481521656593839168537371647847401555205,545336515160251483521991250107141499387292388203252838808⟩,
  ⟨-658060933606442359733005064488767105547595567248673655942,-658060933606442359661858621655735824577013185049854020316⟩,
  ⟨720230013253112155915707485770455166234526805420450510170,720230013253112155955839774694498896053864985405796425333⟩]
def bs0_5_1_16 : Fin 8 → RI := ![⟨-15321284673216323615491753829037300266069677474403429267,-15321284673216323609488764801074591514103163868304289559⟩,
  ⟨2825302351471067168170148655401834742791798173513238794229,2825302351471067168174465799010466038062296174011753289361⟩,
  ⟨-643941991609983128739228463181817401267010402463633922152,-643941991609983128648807283139460960205255828769724729547⟩,
  ⟨371216413234305926225141808640771650590760794252057924948,371216413234305926258599951358714650280425265563197044422⟩,
  ⟨611536048494033816001236384120690471065751561841932649465,611536048494033816097073349189293511034120767255578281854⟩,
  ⟨496940307051962667712774657743932888856646999053718426259,496940307051962667753907174152653940442192720509823159783⟩,
  ⟨-598754490200026052145855736940781504793711076273651358415,-598754490200026052073543860957572611258332130710182929399⟩,
  ⟨655762217144788784117854924921349866029121081366894645473,655762217144788784158644611433328181613357108924607757148⟩]
def bs0_5_1_17 : Fin 8 → RI := ![⟨-13930072087610941124016484206515204575842542070438252696,-13930072087610941117914070220884739515272595235015398804⟩,
  ⟨2615077717688480586949316263379962457268433284699072705247,2615077717688480586953704910004589881578599802114864650293⟩,
  ⟨-584837190494754032716179481973745405550637843998673415244,-584837190494754032624260694330143410445510297051738185894⟩,
  ⟨337124147250863899360434013898154446377471346353716285563,337124147250863899394446309623616704582715137318669746241⟩,
  ⟨555401956737156846255148755102731971488240639625907388114,555401956737156846352573027119969058334711310410726627213⟩,
  ⟨451295180856379031374921924880805728949272457056227243245,451295180856379031416735701689201867828303933454119860088⟩,
  ⟨-542958232602323489835134470496829445364384146125245735409,-542958232602323489761624923624352355667694395482601783526⟩,
  ⟨595043840840342783859698814911336005337909245231681742480,595043840840342783901164083676681829988713925858702576129⟩]
def bs0_5_1_18 : Fin 8 → RI := ![⟨-12619409772379150564325434909190568492779362021335530247,-12619409772379150558120820909825895869704009965364943943⟩,
  ⟨2411115909884574338804642846187285907871573316814050452015,2411115909884574338809104991552956214582391381844708605512⟩,
  ⟨-529241772102701444887356448431773399681362111381138647134,-529241772102701444793898253369689696850521457144169617778⟩,
  ⟨305058507061683905478462230961480620427439026523419491629,305058507061683905513044146692905953101656449892115579204⟩,
  ⟨502600828964356658837880125995206723939997319074494732324,502600828964356658936936008382283507840071189277140922932⟩,
  ⟨408365192880579052280926725798224927813113589676881212482,408365192880579052323440777706931598200437150054189880861⟩,
  ⟨-490607342441162992807058249661747035475120750775178111112,-490607342441162992732317603634661491797926226950549875288⟩,
  ⟨538014276883862329796906437155300472771034172059816427151,538014276883862329839066144391551554908912498003423404225⟩]
def bs0_5_1_19 : Fin 8 → RI := ![⟨-11388288699418643666167506712313612458996002357089108856,-11388288699418643659857814215193093480836639607295164827⟩,
  ⟨2213910470407129525397132874078658733516311207975414361697,2213910470407129525401670588292253039410105582198812628388⟩,
  ⟨-477101994233718031818416433545883469299113460716753984750,-477101994233718031723375473344558289550739762704060078203⟩,
  ⟨274988268644996315530716197517813050654305447434983915988,274988268644996315565883776717681989189105718695467696318⟩,
  ⟨453081745749208565406251433525504042455902521129844378079,453081745749208565506984880917927473136403424708398750174⟩,
  ⟨368108129825775092340436200682992108485518704449078611510,368108129825775092383670251081607739677685827753029730222⟩,
  ⟨-441630539108341556706317016601747552938722926942126547567,-441630539108341556630310597263802864562698432824075270061⟩,
  ⟨484605319377813637618332538741761281918542616103672829186,484605319377813637661206243448660731007233631563466822026⟩]
def bs0_5_1_20 : Fin 8 → RI := ![⟨-10235516045332883959089026271085558640881126236964420544,-10235516045332883952671268526792482522754859066709936362⟩,
  ⟨2023932295606717377846809799625256954542192810321923073602,2023932295606717377851425230654411419881237312871910666297⟩,
  ⟨-428356489987720156127046368169850543613483415570156692971,-428356489987720156030377654340129221164981836796775625442⟩,
  ⟨246877798228631429373566270331950984046928044183572392987,246877798228631429409336159888641507300315825080954195908⟩,
  ⟨406786518259777298074574420832026992914798693132620529980,406786518259777298177033116308724909123232506506213311180⟩,
  ⟨330475922899641093623196573431953673373545230259308708879,330475922899641093667171087545206499036873768876134629560⟩,
  ⟨-395950603375629354845733248237709716558520196247936467321,-395950603375629354768425077270048581704624593069448641913⟩,
  ⟨434741726234835014996926804730671002057827351050237955922,434741726234835015040534801560068505686490429545634660367⟩]
def bs0_5_1 : Fin 21 → Fin 8 → RI := ![bs0_5_1_0,bs0_5_1_1,bs0_5_1_2,bs0_5_1_3,bs0_5_1_4,bs0_5_1_5,bs0_5_1_6,bs0_5_1_7,bs0_5_1_8,bs0_5_1_9,bs0_5_1_10,bs0_5_1_11,bs0_5_1_12,bs0_5_1_13,bs0_5_1_14,bs0_5_1_15,bs0_5_1_16,bs0_5_1_17,bs0_5_1_18,bs0_5_1_19,bs0_5_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_6_0_0 : Fin 8 → RI := ![⟨-29280925492483197661529090510135276643002449089894503508,-29280925492483197658937258199671573469788883995361141617⟩,
  ⟨8415036147828304469747236139636678373430653912212722629295,8415036147828304469749100096449206599937300617821340337732⟩,
  ⟨-1194697631141871243000266083118494003340415018386147030546,-1194697631141871242961226109051013265826686999138067184371⟩,
  ⟨687372558927168941907864001324247237692149698837177433359,687372558927168941922309787404249446929952009046054347176⟩,
  ⟨1134015354857086076204513848146876118737750005557528020455,1134015354857086076245892125106379592623864487108491994198⟩,
  ⟨920374832323633262213516438321183098835416731841491427879,920374832323633262231275688675349226521846918325144650531⟩,
  ⟨-1074683599071395642677643063866124309106244693977616625866,-1074683599071395642646421907914967083685583379162534831880⟩,
  ⟨1194006103070178174427172199685732067670440761042588201207,1194006103070178174444783430848396767893660187988910156309⟩]
def bs0_6_0_1 : Fin 8 → RI := ![⟨-28429816638694856337625427106248260280909681619677273650,-28429816638694856334998530511465258373441898640839539501⟩,
  ⟨8013693228314021947961659303854061933245824389842897257036,8013693228314021947963548477696011561709829434565795534090⟩,
  ⟨-1161608224352969149410882913854298222755991014478675781028,-1161608224352969149371314777241327118218100435185058745420⟩,
  ⟨668406051655446704674712938725722578224963444829829538161,668406051655446704689354158417825648166595914189057850848⟩,
  ⟨1102647031855174348514686433942864309714419345343904760912,1102647031855174348556624507792890427822071185600171850729⟩,
  ⟨894946603781069716579040010296209139327763221526849432018,894946603781069716597039521334451037940925551377111089762⟩,
  ⟨-1046164903260474993861814554433313490402968838486884540730,-1046164903260474993830171014871729035790541923978414575784⟩,
  ⟨1161703993418671278260911871283771420992262669746252772864,1161703993418671278278761360613900856902474017481209558986⟩]
def bs0_6_0_2 : Fin 8 → RI := ![⟨-27553175176960801761834727681594415435692812679707753755,-27553175176960801759171920270209560101204194957558919752⟩,
  ⟨7617611560294714745938077811408673358749720676023849027741,7617611560294714745939992811076997973160420831092397141438⟩,
  ⟨-1127365945857109900040798159985931282792305338881228029915,-1127365945857109900000689109771690457432829412007804474920⟩,
  ⟨648770681133510146618820966792852153272003947328297229723,648770681133510146633662338312898226099903477888614051999⟩,
  ⟨1070180527809122237487829949070530765110068098854120598135,1070180527809122237530341334592538409318220316812707328095⟩,
  ⟨868626834407299792305835901307555936586051459610049923430,868626834407299792324081473474095826295026660433593848747⟩,
  ⟨-1016559435706617664065000651397424703018539126115047285553,-1016559435706617664032924530915850497734255477614131760924⟩,
  ⟨1128220451354455372246639636852618853169357284776461416899,1128220451354455372264733136449086346395885999770651312600⟩]
def bs0_6_0_3 : Fin 8 → RI := ![⟨-26653061580193747781384360453410529662954498062350156080,-26653061580193747778684768284381660804594082347626011984⟩,
  ⟨7227488872103603992134967254001588796877221977089719834655,7227488872103603992136908708004680861046438391589890233105⟩,
  ⟨-1092051222666739204797001277762831335341906043825136741191,-1092051222666739204756338150041813438593524030055825847418⟩,
  ⟨628512625903897079021909726371672918485059012177628846508,628512625903897079036956120700432863191805921927419781316⟩,
  ⟨1036692198082074215197320545926619780020749803387316259293,1036692198082074215240419195479468997273199840455929888194⟩,
  ⟨841477259688765410169694503036557450921056002740962036585,841477259688765410188192124580601065468781594855676137995⟩,
  ⟨-985933674528882860010240066446114610258817346626323620539,-985933674528882859977720837569662922288071399714564663683⟩,
  ⟨1093632092772412952688280127855727035925898257515562629852,1093632092772412952706623576057078607688083590412597664525⟩]
def bs0_6_0_4 : Fin 8 → RI := ![⟨-25731656095754346160482261637917195406690679169049916656,-25731656095754346157744982168686318617154702511349764507⟩,
  ⟨6843995028117202722820383511416509063453266756921129421500,6843995028117202722822352068831989249718152666275653086877⟩,
  ⟨-1055749972655723073227652826596978511512164563678348169686,-1055749972655723073186422026647827445443822288458915024579⟩,
  ⟨607681255143058218089515586382324047055984898891342972622,607681255143058218104772033913420347934952337811256393389⟩,
  ⟨1002263632963470070736931917634722146392347711209195325900,1002263632963470070780632240196877388350690123467475649946⟩,
  ⟨813563862025776223327591723303143723280728303862612044566,813563862025776223346347578451653073732714807385835222334⟩,
  ⟨-954359239077389031495510425714516155420124838122783372555,-954359239077389031462537216435058316445440886813300091713⟩,
  ⟨1058021137468222637608108115517016619135307049487017717323,1058021137468222637626707645006125592126237707174868233627⟩]
def bs0_6_0_5 : Fin 8 → RI := ![⟨-24791253844992619417530808878090957022027578507050359505,-24791253844992619414754909719351447820330724544409669940⟩,
  ⟨6467770054025379540140267599406842855713759994697319528993,6467770054025379540142263930777088718829534143559503683880⟩,
  ⟨-1018553435198733760566114857653743239602614426582477449227,-1018553435198733760524302341182694998569936024310226519219⟩,
  ⟨586329031913429151248637696579946333912441827877118828260,586329031913429151264109394060258350175530565773328154769⟩,
  ⟨966981496637236121435580943999631284849169577334177962448,966981496637236121479897825049146440217249842197268629841⟩,
  ⟨784956742270680575092628340874806699550800809449784574109,784956742270680575111648818364842586009515969679684421664⟩,
  ⟨-921912790507981435420755062231325531233578842631475867869,-921912790507981435387316641007444622089370136722425404766⟩,
  ⟨1021475274119139876888975307108335999278159576415948752794,1021475274119139876907837253373630416957438445803683851517⟩]
def bs0_6_0_6 : Fin 8 → RI := ![⟨-23834259243641684502553196002759936787956667236696165472,-23834259243641684499737713617336024606146624688674685622⟩,
  ⟨6099422312978942211726108983850970468315758586181691300105,6099422312978942211728133782118837648942663714202965428329⟩,
  ⟨-980557971044448735957155177121044865903743205108579833557,-980557971044448735914746430663548810529940392356876592370⟩,
  ⟨564511398503294906487180435901488892787129768454984219485,564511398503294906502872753683052827433246265656598727974⟩,
  ⟨930937336749127502473871911855524177246243286606131469027,930937336749127502518820734142268031844367945695371143671⟩,
  ⟨755729967544463481612385635984728250767408140977770139876,755729967544463481631677337978735765370588461521460771492⟩,
  ⟨-888675906193933357057839016488454393876230629793322390653,-888675906193933357023923776572175661266254036740794179296⟩,
  ⟨984087495578260097812712523965080679749968433347401008962,984087495578260097831843434141521975799675098313964428817⟩]
def bs0_6_0_7 : Fin 8 → RI := ![⟨-22863179748351501366663678030708948727192452659153270637,-22863179748351501363807616372962039806525409682562697220⟩,
  ⟨5739526840589547812052049954377810024241355619901521232452,5739526840589547812054103935865124507978390285387133601775⟩,
  ⟨-941864831341735201145727343276243296343455404900617063876,-941864831341735201102707363702757467626181950531641081898⟩,
  ⟨542286643798371418790573267314969206523337375069744205798,542286643798371418806491756938356527703684241288672681413⟩,
  ⟨894227364494402964440351100046473585810588937446260179230,894227364494402964485947765313836822663399464482887381643⟩,
  ⟨725961395253838675029723576834367080955421942081988954480,725961395253838675049293328242971564101784188752656789719⟩,
  ⟨-854734927567150183799374456452366291925153334043826556367,-854734927567150183764970399499475153624196224158591482350⟩,
  ⟨945955904180255832063815984711043714723039946518983313844,945955904180255832083222626825219330509929807689034951877⟩]
def bs0_6_0_8 : Fin 8 → RI := ![⟨-21880618939336563517630888467479063413326935521228991142,-21880618939336563514733217559465948467815926046062711263⟩,
  ⟨5388623845667517190902782736786385042222356747371817869842,5388623845667517190904866642217921291600208652530928982318⟩,
  ⟨-902579895943653474394592945093776740754794697518234874995,-902579895943653474350946218162876239436175821640390756635⟩,
  ⟨519715752749053520831328471467575182792524103635884564327,519715752749053520847478873597789508566344171743077669481⟩,
  ⟨856952205344201843720948304115315464756866134291039846303,856952205344201843767209255831665872494567754795616633775⟩,
  ⟨695732473388595710702642979351291791914311900234970288960,695732473388595710722497837589471249929713312623041791480⟩,
  ⟨-820180781131989720009337682883305604603813922853261887390,-820180781131989719974432401801780227235506277228166390947⟩,
  ⟨907183486938505583063124695781564768306824478199792329887,907183486938505583082814068426545139380196614292817446641⟩]
def bs0_6_0_9 : Fin 8 → RI := ![⟨-20889268953946717180584454558629070097057767920629269310,-20889268953946717177644108999031212639818886471523150017⟩,
  ⟨5047217382448408360933556381898635767615677653283425314305,5047217382448408360935670977474443584686778482969483900269⟩,
  ⟨-862813381329045835266693729314111909229745615992315173946,-862813381329045835222404207212948710803094621966575071430⟩,
  ⟨496862238122793865691590312272435429022095465095964485746,496862238122793865707978565009515207739068222530876152751⟩,
  ⟨819216620735082443641571442349529696611952563479121774789,819216620735082443688513689512968623257635550711617237589⟩,
  ⟨665128017343906663927645017861334479621439761968086082241,665128017343906663947792283065244957245649533877931085671⟩,
  ⟨-785108772555072801750949295999784899336021638457154075306,-785108772555072801715529956988390668625630694446945849886⟩,
  ⟨867877860705584475164481495959557286399826263326429488046,867877860705584475184460838426566348153534990307316172926⟩]
def bs0_6_0_10 : Fin 8 → RI := ![⟨-19891902290914878132503516157696669485421334388215026459,-19891902290914878129519393559316371049534488021994433814⟩,
  ⟨4715774198890486198416394382399381611235714502728013281172,4715774198890486198418540460918485249767404724851458361381⟩,
  ⟨-822679518704051743587808454980473514837329081359979048188,-822679518704051743542859532789261090040750548497201936665⟩,
  ⟨473791954861126999460739784112092718387919936110111332496,473791954861126999477372031699852172948975615292053012210⟩,
  ⟨781129201259600965784682626958581490598568925042175974265,781129201259600965832323769042121127361216972751777728472⟩,
  ⟨634235963683250705867284065451456199271213492177030991687,634235963683250705887731291184717336169746322468094214066⟩,
  ⟨-749618353903385505298558822347570891389767553538545313909,-749618353903385505262612146073973027276726437270591385563⟩,
  ⟨828150987569999394886568841585914126837787882811065529996,828150987569999394906845644481380466959591927633499632929⟩]
def bs0_6_0_11 : Fin 8 → RI := ![⟨-18891363010045490862871507661194263160312847629111530124,-18891363010045490859842467012571225040528540821020408849⟩,
  ⟨4394722764434429504094274954727194957715895815886112174342,4394722764434429504096453336765862241009099421075416675172⟩,
  ⟨-782296203074272708682141483971905419706260675669127176667,-782296203074272708636515974985452192255073929515051856829⟩,
  ⟨450572897494364291128338999447508096444967445823413973317,450572897494364291145221601405199248863421757273809594249⟩,
  ⟨742802032114795310577349339515041210769342127387124635069,742802032114795310625707592623190206009821555791115079072⟩,
  ⟨603147101433184361327539293287696630916550804156933831910,603147101433184361348294297767604712162982156456137904534⟩,
  ⟨-713812864279457759394177277354072066267750164157505657311,-713812864279457759357689519218904176517703621861069699017⟩,
  ⟨788118860970372431264307680387074504958370288966281193729,788118860970372431284889696765276534641147268502647703647⟩]
def bs0_6_0_12 : Fin 8 → RI := ![⟨-17890557357135653332245479630160464763009614243943500689,-17890557357135653329170339576599657824196499357751083210⟩,
  ⟨4084452479415873128961669897502971477034148880503661592120,4084452479415873128963881432650939536105176347235201765348⟩,
  ⟨-741784614310479295192400988094536128554886125672035899638,-741784614310479295146081097929896217002076701786746932276⟩,
  ⟨427274981202774124200690042018383714086268470928431362852,427274981202774124217829582721525974054789266290090016423⟩,
  ⟨704350331788042357001267081669944780802679274988242781294,704350331788042357050361305981882189331032722448005633237⟩,
  ⟨571954781679830767461058782283851413743688028845809794265,571954781679830767482129660159786616346868751382095554596⟩,
  ⟨-677799244285176589632545903747817373170871908020428950395,-677799244285176589595502833177980367873648271675826129450⟩,
  ⟨747901163222375424747415860937794433765861077117724936622,747901163222375424768311117981097344266258352899192030970⟩]
def bs0_6_0_13 : Fin 8 → RI := ![⟨-16892443848916242676057478766528948707742892518433522138,-16892443848916242672935015805546166998911120880551266955⟩,
  ⟨3785313067122835098512796596807766184756637539323253866359,3785313067122835098515042164966015060003085346640947801588⟩,
  ⟨-701268811464517700639687972457787010808522893295260368761,-701268811464517700592655271872810825948064861087512286390⟩,
  ⟨403969807249842805748371062522869818325285711044695939170,403969807249842805765774361261079502727962822956676690278⟩,
  ⟨665892065183871170784483314048091501227805585051006187092,665892065183871170834333042627151652480217577154525106220⟩,
  ⟨540754606417011482204126403545017698749437125328677643283,540754606417011482225521538263261877342328541066721988718⟩,
  ⟨-641687724933440589540563070088218159494761246960190077769,-641687724933440589502949948799256436661029420637935340418⟩,
  ⟨707620895371798012334076249248191754965199854584985828696,707620895371798012355293060528807417329555842403691189259⟩]
def bs0_6_0_14 : Fin 8 → RI := ![⟨-15900022857709879799650674636326650738067031473830467718,-15900022857709879796479621222209907162975053054313505982⟩,
  ⟨3497614148305669069678753840483484513663711995183818219720,3497614148305669069681034353227371522570509991935255001828⟩,
  ⟨-660875301825096323266798552238868050507406305634082941638,-660875301825096323219033948581792734376686338904009925606⟩,
  ⟨380730413649613524302708530673149519470703712388875388815,380730413649613524320382652214519544768078947874226166321⟩,
  ⟨627547532618687589787678090893638740112239385493510413149,627547532618687589838303559947750262202543209063159042297⟩,
  ⟨509644097775614027318494172104196612562938865770561952297,509644097775614027340222248895489875429647654618202839338⟩,
  ⟨-605591491817832899888785609552842046107673170157423831899,-605591491817832899850587168716531077389461172616632858855⟩,
  ⟨667403980507243507726487657757656575687596328049475650455,667403980507243507748034636116951847258553350356243199906⟩]
def bs0_6_0_15 : Fin 8 → RI := ![⟨-14916325740271064852782648011180620954173193683698197455,-14916325740271064849561690563031714627948452816299967839⟩,
  ⟨3221624996788446833711590906616266392335158146101216584796,3221624996788446833713907308628074243859971548138818871404⟩,
  ⟨-620732586432957674582343651876387992788858360353394802204,-620732586432957674533827359081579327325876790129706025247⟩,
  ⟨357631012064681778300913744728463311893920639487368241878,357631012064681778318866010421903922013823949951292431359⟩,
  ⟨589438936330633875606273491587090824314236715636887176173,589438936330633875657695672270142592932115285341639084769⟩,
  ⟨478722348941199334605625232936857821431649400944280673934,478722348941199334627695252465309543749983641526164808141⟩,
  ⟨-569626325543107025685884998314333474808253253832653244680,-569626325543107025647085414563591628018140069256541521368⟩,
  ⟨627378841886012309119705252160160596774143707575640367670,627378841886012309141591323243807828876747015184900078207⟩]
def bs0_6_0_16 : Fin 8 → RI := ![⟨-13944403559845164509190891507749218786966782472452135025,-13944403559845164505918668315008239107241508979154366558⟩,
  ⟨2957574473708547111789311499719895454929686001661511098267,2957574473708547111791664770295107116054110070563660255710⟩,
  ⟨-580970683999026219668773497794482403745440008787177793604,-580970683999026219619485004833993680617240305166794660168⟩,
  ⟨334746712062693612531391548285642681558664103469982696320,334746712062693612549629547734609283345175507257891470175⟩,
  ⟨551689926366524866174792433735830811366179012954753004461,551689926366524866227033065585709925895219139529795796818⟩,
  ⟨448089658240059553024965873556332277522686276068937337406,448089658240059553047387166270779641495906696820006661996⟩,
  ⟨-533910219611761650916145166713289813052403303387887602381,-533910219611761650876728036912171848798926601453862108826⟩,
  ⟨587675957444565678922597048668569765995314092151132095088,587675957444565678944831465158290101083558348072372538685⟩]
def bs0_6_0_17 : Fin 8 → RI := ![⟨-12987315454800866448543712073775186439574192359426121683,-12987315454800866445218811092839075764196738464355715994⟩,
  ⟨2705651136835858559002235208403300474653449356120871238849,2705651136835858559004626363035195450883703187134982844559⟩,
  ⟨-541720635384877864442353418437313433515917170331081710795,-541720635384877864392271456132027576352818554143838862335⟩,
  ⟨312153233985626264282875070554057688152897234250506462552,312153233985626264301406673897274720985116771244570571168⟩,
  ⟨514425127914477376403315694651867305334317745308555681492,514425127914477376456397320767166728002429570844931469683⟩,
  ⟨417847148040952121690358556333333713089336892951297766767,417847148040952121713140797564924405741503364995475211367⟩,
  ⟨-498562977152460932354803500429239972577374444740657781078,-498562977152460932314751815131051927589242839563856134390⟩,
  ⟨548427392478299299542043535000026029165831757192901404939,548427392478299299564635891585337250115189611997023059919⟩]
def bs0_6_0_18 : Fin 8 → RI := ![⟨-12048116711199803544298658043945475470505764227285708740,-12048116711199803540919614579067465235344661947352442881⟩,
  ⟨2466003520403616577570512948139885077607216848723686418608,2466003520403616577572943040187356916276618536377688602143⟩,
  ⟨-503113991009702902757124905900123046552883845164448433777,-503113991009702902706227411987853069914364260898380736054⟩,
  ⟨289926611806202512850237905822753654904091127109019206880,289926611806202512869071276659908330656021765132637765378⟩,
  ⟨477769652346983121927044253380801865538319287603293670007,477769652346983121980990257444969368262669277406283731686⟩,
  ⟨388096370278564802706664453998711152575986127568874928943,388096370278564802729817679851394206474726082081489413840⟩,
  ⟨-463705788062608340263137900266860325250151767201949499037,-463705788062608340222434015778324301318310443019949833875⟩,
  ⟨509766312481883897984357186241196568247332920262013097579,509766312481883898007317435377460384838936004342558920091⟩]
def bs0_6_0_19 : Fin 8 → RI := ![⟨-11129846600313700967066829858954552273823212498714097986,-11129846600313700963632124120151459822896179032875921079⟩,
  ⟨2238740579927648633802586077945313788767882564302363545264,2238740579927648633805056200389139306187989987076781400127⟩,
  ⟨-465282283739266310390966978942496373270538307522721939459,-465282283739266310339231061293493021336181037426748719061⟩,
  ⟨268142887457992828407834614937061781057955186070203912572,268142887457992828426978223940004416512924138101969130276⟩,
  ⟨441848594422301489220820306433472480842012089158627671211,441848594422301489275654951702513633641366866878892248189⟩,
  ⟨358938900553435312793800221880857923311479374392925078311,358938900553435312817334845964617426667693913557810712657⟩,
  ⟨-429460788318043023413049059316588128563822782156822671740,-429460788318043023371674668280446433179762559137711891087⟩,
  ⟨471826478338823394675210756833813484537595625097787881096,471826478338823394698549225336001622663960417992192620921⟩]
def bs0_6_0_20 : Fin 8 → RI := ![⟨-10235516045332883938271520986353910854541110776317395561,-10235516045332883934779575516549776285993048348010575325⟩,
  ⟨2023932295606717373452650979256639520526532184963170219611,2023932295606717373455162266549788763849417466135779528765⟩,
  ⟨-428356489987720155700392242958118924537108631326310510336,-428356489987720155647794140820925460086135244092326966089⟩,
  ⟨246877798228631429148934192018364493948241190389670227966,246877798228631429168396831271130632089119435030224909141⟩,
  ⟨406786518259777297710108084021868444268284014696781977861,406786518259777297765856554399674996168561183514261109361⟩,
  ⟨330475922899641093346300606592090512548969751161517094325,330475922899641093370227437652172694710653434866225730097⟩,
  ⟨-395950603375629354654928159333272367750838901232050399435,-395950603375629354612864259735715436318380868949935299749⟩,
  ⟨434741726234835014763465700117076309679896354474997028627,434741726234835014787193106642062078634260016453680743984⟩]
def bs0_6_0 : Fin 21 → Fin 8 → RI := ![bs0_6_0_0,bs0_6_0_1,bs0_6_0_2,bs0_6_0_3,bs0_6_0_4,bs0_6_0_5,bs0_6_0_6,bs0_6_0_7,bs0_6_0_8,bs0_6_0_9,bs0_6_0_10,bs0_6_0_11,bs0_6_0_12,bs0_6_0_13,bs0_6_0_14,bs0_6_0_15,bs0_6_0_16,bs0_6_0_17,bs0_6_0_18,bs0_6_0_19,bs0_6_0_20]
def bs0_6_1_0 : Fin 8 → RI := ![⟨-29280925492483197661529090510135276643002449089894503506,-29280925492483197658937258199671573469788883995361141617⟩,
  ⟨8415036147828304469747236139636678373430653912212722629295,8415036147828304469749100096449206599937300617821340337732⟩,
  ⟨-1194697631141871243000266083118494003340415018386147030548,-1194697631141871242961226109051013265826686999138067184371⟩,
  ⟨687372558927168941907864001324247237692149698837177433361,687372558927168941922309787404249446929952009046054347176⟩,
  ⟨1134015354857086076204513848146876118737750005557528020457,1134015354857086076245892125106379592623864487108491994198⟩,
  ⟨920374832323633262213516438321183098835416731841491427881,920374832323633262231275688675349226521846918325144650531⟩,
  ⟨-1074683599071395642677643063866124309106244693977616625868,-1074683599071395642646421907914967083685583379162534831880⟩,
  ⟨1194006103070178174427172199685732067670440761042588201209,1194006103070178174444783430848396767893660187988910156309⟩]
def bs0_6_1_1 : Fin 8 → RI := ![⟨-31834252053848221633345273574754221932043405153459309856,-31834252053848221630648248411332622556067186406012831193⟩,
  ⟨9619064906371152035103890995896263488113067461979357040218,9619064906371152035105830603797055920491789184930816454511⟩,
  ⟨-1293965851508577523770000078547552446166174710245172347401,-1293965851508577523729375616843600607579959010860480932927⟩,
  ⟨744272080742335653606730888283518633982217983408166922342,744272080742335653621762975199823425331510771068098032771⟩,
  ⟨1228120323862821259272316700087343613143129910082488450863,1228120323862821259315374367718415019693856467749361772826⟩,
  ⟨996659517951323899116224940343877664578180832685592110186,996659517951323899134704972750271105044807449269070638116⟩,
  ⟨-1160239686504157589126395742995838452791369059529977394158,-1160239686504157589093907436213399539795410945634731087289⟩,
  ⟨1290912432024698862925238410389219800643999272565689993177,1290912432024698862943564416054278707928194461877916441338⟩]
def bs0_6_1_2 : Fin 8 → RI := ![⟨-34157785143701826338178132452471710872967447989253505866,-34157785143701826335368295645549223059329023857833362074⟩,
  ⟨10870444928368777478318503942190899393994013288702985737831,10870444928368777478320524680352538288148840970079610270198⟩,
  ⟨-1382858226512669402513419812539070454578579356894409149897,-1382858226512669402471096103696633330743070889564682197540⟩,
  ⟨795151833305573477900929591233678140900327076531496692164,795151833305573477916590442928864794003042460099115995668⟩,
  ⟨1312341663471292992306857916012915487319324538122000752156,1312341663471292992351716607348684763445330342877932138976⟩,
  ⟨1064920336098157128270384313693459041214420669110275177955,1064920336098157128289637332150079775982970264253643503485⟩,
  ⟨-1236014828250489406746279879697850878346108713152391632074,-1236014828250489406712432646298067584454033591485464313823⟩,
  ⟨1377185869264838462791197466829980243315012141027688436540,1377185869264838462810290015887293252324112110941203884806⟩]
def bs0_6_1_3 : Fin 8 → RI := ![⟨-36195891993400737900889465314403825374780223740395391946,-36195891993400737897958458036928110978302689956989003236⟩,
  ⟨12150337548824210331012233470382680368624674619287491742265,12150337548824210331014341350186597735666717402245890667209⟩,
  ⟨-1459203226818112711741821113300873840266076246196777625290,-1459203226818112711697672250875281334217225225004680950623⟩,
  ⟨838764995968361510183971682678652331974333990074352314234,838764995968361510200307887748375750346276318322803097321⟩,
  ⟨1384617778877600529326969566621664316922358977510615453117,1384617778877600529373762729285092856284840605417403459021⟩,
  ⟨1123490428630201088729648912239355433859089808366293947435,1123490428630201088749732191478758310945422333732396615928⟩,
  ⟨-1300214115095792514015259172869212360944084944433145877261,-1300214115095792513979952322602241308403182993080827985916⟩,
  ⟨1450757785628769573819079291023628370200418066433802852249,1450757785628769573838995180834218264528724547855363080055⟩]
def bs0_6_1_4 : Fin 8 → RI := ![⟨-37902641564584653721767078249354843306343512885582393794,-37902641564584653718705705024509676855727894464025737944⟩,
  ⟨13437647122247124657382241407026298869651034541901463962196,13437647122247124657384443041543712100829144158727116089217⟩,
  ⟨-1521274082863917554901359165206688731317806619080874519415,-1521274082863917554855246640554834035203644400036412821405⟩,
  ⟨874123189429124144678361709124647401477640483050009256689,874123189429124144695424519299392080251089035492700635205⟩,
  ⟨1443311104306763803003684521486228922444465228374474284153,1443311104306763803052558960108571987345126733743153318223⟩,
  ⟨1171046937436810242423699897077277579238470417450129962252,1171046937436810242444676444561166176798592002051781744496⟩,
  ⟨-1351459077541267018481349391652552354986142458326463066790,-1351459077541267018444472156003595694375001614772306610640⟩,
  ⟨1510013467919150654989275125583685385906228370219390094676,1510013467919150655010076838456760590661003624506031711554⟩]
def bs0_6_1_5 : Fin 8 → RI := ![⟨-39242995360608063033553555066991258188338321627187937966,-39242995360608063030351674403136239253265857591719857608⟩,
  ⟨14709500882028370143603614867637164011091183770173217968157,14709500882028370143605917550280672383864847531369006935951⟩,
  ⟨-1567829939493353417673664273296533874378222423749698778262,-1567829939493353417625435328244559100710263662813231176883⟩,
  ⟨900519985479743264107120299108377760983719463563604586115,900519985479743264124966238808427938531776493089431462531⟩,
  ⟨1487247233743259099477044278564298715693207972301882724812,1487247233743259099528161900784543468136579760619380461540⟩,
  ⟨1206642220655082634847981930575074684986049188890686809636,1206642220655082634869921235864343930619453358471073801500⟩,
  ⟨-1388811846159693658195107964644921491909716428433041474011,-1388811846159693658156538179425077042118308301224566571698⟩,
  ⟨1553824928573413459907425949221660359462148064125591127892,1553824928573413459929182395538832324240267125274740559363⟩]
def bs0_6_1_6 : Fin 8 → RI := ![⟨-40193503139292089973388497635831982593749598157138886145,-40193503139292089970034897422905678294764616814212160524⟩,
  ⟨15941838789526540569423610120463107083296395043229502381786,15941838789526540569426021914597320579314242457484289980344⟩,
  ⟨-1598134582032857450081212268265323693641114314533088072120,-1598134582032857450030698018242909274774305156054536590510⟩,
  ⟨917541358752878046833421653351711140702346088488629413367,917541358752878046852113214175331626291647387538547053739⟩,
  ⟨1515732618441690888084067526807377773848522190176387231770,1515732618441690888137607332553001897831967386490409243162⟩,
  ⟨1229717775867618310343904862397831188798847670312650649087,1229717775867618310366883750937153113520207023632861561607⟩,
  ⟨-1411780239148751873237516291185697367196688496466568429152,-1411780239148751873197118895559726991477723733410533274419⟩,
  ⟨1581562073862745876055164172075474317215495510148828057217,1581562073862745876077951536959247007263160800579843735766⟩]
def bs0_6_1_7 : Fin 8 → RI := ![⟨-40742491962721987814460422905920099419288059139256363077,-40742491962721987810942677705409146225837211130035914403⟩,
  ⟨17110095931964545002497587026444713209194902305537400616042,17110095931964545002500116868018407040875132729423789086918⟩,
  ⟨-1611952910590316570158583663503593925330302792121008563316,-1611952910590316570105596947946592978062625258229434466740⟩,
  ⟨925063203107661292345700540432033179412510809860006232715,925063203107661292365306976561318351744197724876698913682⟩,
  ⟨1528551003594813406584794184168866448740468190299048512571,1528551003594813406640954544003539940826642452036680478047⟩,
  ⟨1240101040712972070639035442826583426258135348482114994155,1240101040712972070663139053794386565490013696867709423314⟩,
  ⟨-1420304668351744026342012626588890587006615096900822193097,-1420304668351744026299637943993275930890099180225899119734⟩,
  ⟨1593082891112258914711930355172886687841787464950822977090,1593082891112258914735833068186483410545186602068563053465⟩]
def bs0_6_1_8 : Fin 8 → RI := ![⟨-40889767765862852993367694933181101154666647496964051099,-40889767765862852989672001812694317710538724474357796900⟩,
  ⟨18189952881803892833492476765714770100371515195298602515268,18189952881803892833495134581323022679186658878601735976707⟩,
  ⟨-1609526688682824173708967735130638192813454600853167362202,-1609526688682824173653300644707685630399139016055834125969⟩,
  ⟨923236822777551637542108034504879371290898140886543506020,923236822777551637562706277694973873083875343298321048142⟩,
  ⟨1525940070287127770333872972264291071018396075306102816895,1525940070287127770392874248268261717023849192184113753770⟩,
  ⟨1237986275978317797538497926098714982967053285221343900233,1237986275978317797563820837269657744911633017192711515136⟩,
  ⟨-1414728743392148603598037183199242632938655443060993485153,-1414728743392148603553518943809017112334406467816708012642⟩,
  ⟨1588704509052708750327392645398602696907399662622154188908,1588704509052708750352504496032971817971053704510876853434⟩]
def bs0_6_1_9 : Fin 8 → RI := ![⟨-40645876437343826938852803561378993678729869985899335334,-40645876437343826934963792522041243246852808326192912424⟩,
  ⟨19158123179300002179111374010788625342515526908218914898591,19158123179300002179114170854006927971083890369243296020083⟩,
  ⟨-1591532259133925412553975462014212907689635939513637293179,-1591532259133925412495396483152781593639874291824133626838⟩,
  ⟨912463987841535894613581442700975565730405258144609399495,912463987841535894635257158878260073030866770464515208218⟩,
  ⟨1508550867409263164893235015235149986331689563416056191053,1508550867409263164955322587508067418722207288195117754174⟩,
  ⟨1223901628180996765402761413347901391267255291093682923771,1223901628180996765429408940045495491928587153686607546020⟩,
  ⟨-1395756252663865861547825850575749640212510618930572051652,-1395756252663865861500978907716986938622458369119426272467⟩,
  ⟨1569157979720593555940845541481231616466274126655506614113,1569157979720593555967270967281201270324602806756209242418⟩]
def bs0_6_1_10 : Fin 8 → RI := ![⟨-40030993934280674549892986805297973802024488044773161320,-40030993934280674545793501097692558079309305980055956939⟩,
  ⟨19993142423528877971368580353503478449350040363446531594942,19993142423528877971371528562876967084173011314658506219531⟩,
  ⟨-1559023808163832950976085799542819221607488928995792848099,-1559023808163832950914336505395730597113719013977478351302⟩,
  ⟨893363658611061414527212733568775932483574861392517564724,893363658611061414550061547257652454158994977644735498270⟩,
  ⟨1477393468783782048611673545349371017626061061469851125991,1477393468783782048677121319238647952688950902360158860893⟩,
  ⟨1198665144709705059501895818249278414339836893140211739318,1198665144709705059529985518622356730586268053296732031604⟩,
  ⟨-1364397753642006744111389296549005664344871018882876865110,-1364397753642006744062006980389415448192919994784681152669⟩,
  ⟨1535530350581091709088446173324444897927543853576983025077,1535530350581091709116301752619060660084940720560535805952⟩]
def bs0_6_1_11 : Fin 8 → RI := ![⟨-39073530566657234162994554746201980910611526151752901216,-39073530566657234158665395432385335488899580137932247268⟩,
  ⟨20676120960975466206026536645425181305118956218212051100647,20676120960975466206029650028170865569241304020022643748600⟩,
  ⟨-1513366307098347622334006791728026593752484974100573927223,-1513366307098347622268797994589529266375986723152116735658⟩,
  ⟨866732798861019125937391999379045952359293611590759037295,866732798861019125961520917406118298877863034332119835357⟩,
  ⟨1433772814964206286608329998098344622298077567051237980574,1433772814964206286677444482234478941505054307029459501925⟩,
  ⟨1163332929097046080856234728064911705966698002691707843707,1163332929097046080885898153350221217923441748860169765537⟩,
  ⟨-1321910285647735249344790534170512994658801086797440574351,-1321910285647735249292641574718997293771290722821038021758⟩,
  ⟨1489198000017628199455513132215757271007298532038669620341,1489198000017628199484929319792842295571350821969342418640⟩]
def bs0_6_1_12 : Fin 8 → RI := ![⟨-37808542570316283121483232026959860029331089439404992485,-37808542570316283116902859975215789917821991514117026034⟩,
  ⟨21191422272233624296645892770266079900592005205663654793365,21191422272233624296649186816587984343605899456460774158801⟩,
  ⟨-1456162452292802909982619122396257987097310838887065292200,-1456162452292802909913626384940535424775257686583928385010⟩,
  ⟨833503803403574841582248961013760129064049645539731395924,833503803403574841607778033464068357592841187513875441757⟩,
  ⟨1379218879865523423799556436778930510013657815799643849018,1379218879865523423872681500691789192440223042612930191909⟩,
  ⟨1119142764010647135779183926413648993629116909077586128300,1119142764010647135810568662869565410355106818230392226836⟩,
  ⟨-1269733728815980888910785741388026120466316299343760671497,-1269733728815980888855610678729937380332751381845360260223⟩,
  ⟨1431755293367863131893134964194425865493284020820206268021,1431755293367863131924258116215251425690714452629932991891⟩]
def bs0_6_1_13 : Fin 8 → RI := ![⟨-36276044658916528944406187222918100361426067542030060674,-36276044658916528939550374256957679608116205242641137871⟩,
  ⟨21527232036402296749602849592632168353609017061262753646781,21527232036402296749606341726602850692644761306027656380106⟩,
  ⟨-1389177781804940356717657736594495945472795684275082881600,-1389177781804940356644516117243205075447332509649593604625⟩,
  ⟨794700975933982569171082203204896042483362750139453266487,794700975933982569198146467769942428277852566491865493167⟩,
  ⟨1315415162878173210329396206685560417162906889456581825146,1315415162878173210406918650163546361589408943340540665911⟩,
  ⟨1067456414183013264166361479471697623521017785812000714726,1067456414183013264199633538705980559278536008543830163383⟩,
  ⟨-1209427104367328630217891552255136050253080961853396928475,-1209427104367328630159398534303087987921202879231800659969⟩,
  ⟨1364942410378113774403889854619443079857287700759587439981,1364942410378113774436884599023655952424249394690112348058⟩]
def bs0_6_1_14 : Fin 8 → RI := ![⟨-34519311390633880764885234374642268519507921519276847888,-34519311390633880759726653458916469668213336458885723064⟩,
  ⟨21675988347650824206361448356851541752705775614366787093581,21675988347650824206365158231136745743759035569668637421699⟩,
  ⟨-1314267729610287672605487924840552122244582677368377294285,-1314267729610287672527785804850051414856289443185649946609⟩,
  ⟨751398242644148197943863269396604146434051107502933933667,751398242644148197972615035509514099186803026372024206687⟩,
  ⟨1244129102992623293829694515264260573739536140021744466270,1244129102992623293912050610994275606564669911966160696178⟩,
  ⟨1009703495336396190293824279669369556413766026947016163631,1009703495336396190329170906691835703811729055232427787047⟩,
  ⟨-1142607694586786409945799500569707514874612580977092766975,-1142607694586786409883659346444719242835807283021847810429⟩,
  ⟨1290575754900919686785298672672563484956093872855145382959,1290575754900919686820350693826390765179058797543728795695⟩]
def bs0_6_1_15 : Fin 8 → RI := ![⟨-32583244381847627164671026599954551396618099165273588523,-32583244381847627159178768620176959649157234585094824883⟩,
  ⟨21634651224932818670773138396469448751708993083738398760803,21634651224932818670777088239842961734647810929891691712962⟩,
  ⟨-1233309762357807697141561939218353070467758379309819678774,-1233309762357807697058833744093124443371462681730053600048⟩,
  ⟨704679921793657648427028670876756775668920018827879659478,704679921793657648457640212974947438968199167064385981724⟩,
  ⟨1167147417634242583507484919831953154553243827461818149212,1167147417634242583595168127937603989560990574638969651688⟩,
  ⟨947329318017636541371904160589380607640682732729620010826,947329318017636541409537144834633838584394128191910959353⟩,
  ⟨-1070895317993259466097473916858152642855809861883217377205,-1070895317993259466031314296038282063233274716223640762912⟩,
  ⟨1210483755318473345171092259918416885349166232446888797608,1210483755318473345208411582040788594549975709851003951879⟩]
def bs0_6_1_16 : Fin 8 → RI := ![⟨-30512868325187226743441054809484455145029426745615437955,-30512868325187226737580056558598573005108729919725404114⟩,
  ⟨21404798728523637910286995036143243211312474558793105965938,21404798728523637910291210064859749287967597456866097085373⟩,
  ⟨-1148143013429882885465252495669308671471192493019029991810,-1148143013429882885376970079090262111439493215211942506784⟩,
  ⟨655605938619975692099447484489326554186789291489427493893,655605938619975692132114230180780387878969348106774431030⟩,
  ⟨1086218666014613007400948457809994024830979963890252756472,1086218666014613007494518557983712635821706313466244782054⟩,
  ⟨881748551424849763533499331352469968639134701451820741975,881748551424849763573658926123453093019602617372340829154⟩,
  ⟨-995863488908587516238942431608015906653769698417324816778,-995863488908587516168340973459700331855021343751082410074⟩,
  ⟨1126450174028798278963729710947271760119329972739970205733,1126450174028798279003554584885718158576412846338131537219⟩]
def bs0_6_1_17 : Fin 8 → RI := ![⟨-28352003064197380600823617671532099117699551514097063056,-28352003064197380594553981881987923334202422222693815457⟩,
  ⟨20992546879267140448610606527155905519460561030943017187152,20992546879267140448615115433960426685546325581841066941603⟩,
  ⟨-1060517062576169387930802522856178424109871517510434147945,-1060517062576169387836364924535668216639892507287564716516⟩,
  ⟨605182424654648688355792550875583181955422350473282008219,605182424654648688390736870793710090075851183003929570273⟩,
  ⟨1003004600147013015779942834670664453955659910175273167172,1003004600147013015880036781772929730694074754010910917845⟩,
  ⟨814305961783808937696138795723021309442753769333595789449,814305961783808937739098377333898701255582905669200368158⟩,
  ⟨-918998577479662551362746509745260990227761157265282574428,-918998577479662551287222612646835644935268248080919368937⟩,
  ⟨1040166334557283893886359843514598317372684974452322194135,1040166334557283893928961367055254995957270828229837648466⟩]
def bs0_6_1_18 : Fin 8 → RI := ![⟨-26142143070551227861795348330273283158812049260669283601,-26142143070551227855071531738091857109662228843394855006⟩,
  ⟨20408300345377822912875276455023358206503137905554756798887,20408300345377822912880111993067702650954492382887863675286⟩,
  ⟨-972050771549543380369980299595918069610503299349845406735,-972050771549543380268701515336111717811592064944346675187⟩,
  ⟨554338208717002587182093750160184684411666880229256016756,554338208717002587219569483354141011570186934128436550077⟩,
  ⟨919041158670297610957216255395452564157487263926853271549,919041158670297611064561141909926928156006929123057524845⟩,
  ⟨746244912365567616004110971644078155471335415592300579037,746244912365567616050182602810092099827766599525749565253⟩,
  ⟨-841667511523597483487551671610470992595842300337526824333,-841667511523597483406556722389461663998169318223744942663⟩,
  ⟨953193001133572075104880634566878239154536105640345181849,953193001133572075150568269454775111732016057288744287862⟩]
def bs0_6_1_19 : Fin 8 → RI := ![⟨-23921560728399387423611353683552800134121034430627839188,-23921560728399387416381192799680325077879882436956305883⟩,
  ⟨19666349779395416054477471789770485253244329508561881448929,19666349779395416054482671473245040938461543093014414390347⟩,
  ⟨-884201425614261088780508489754897241746143853361049098198,-884201425614261088671602796940890722804330379631109375541⟩,
  ⟨503907321877935885814767758404987666553147764878054749913,503907321877935885855065642281486011993891039831456211349⟩,
  ⟨835709325907272765156769968925246706214480114748234185928,835709325907272765272198578396632892944471754568260699223⟩,
  ⟨678683804974549274336053592417118431576096534079517408491,678683804974549274385594697675062857754279410892367064989⟩,
  ⟨-765094057912893051398601124720253619007421411689973004586,-765094057912893051311506763116191943111672418704474402933⟩,
  ⟨866932048719864456398537555330014523137323594763465234463,866932048719864456447665747051463500420624271510973946801⟩]
def bs0_6_1_20 : Fin 8 → RI := ![⟨-21724636347776322586004027928715028423735733772265824767,-21724636347776322578207563905874092086134348451892984537⟩,
  ⟨18784338779241099832222723556660725928787907933484222719554,18784338779241099832228330505909874894681242200214265166230⟩,
  ⟨-798243873916726886915411375654056142472578494968875485223,-798243873916726886797975632584164444869943779221494235224⟩,
  ⟨454617315837438399725977354272557087767259466542657599796,454617315837438399769431574295101522532107205901463400481⟩,
  ⟨754215546424871569087680733067865683385502013695129820748,754215546424871569212150300954896271878466669854375825814⟩,
  ⟨612600216197081954152516368347707620763065125216579305550,612600216197081954205937786075250919637278875954138337618⟩,
  ⟨-690343306302699812610151306122749069497519296765239676598,-690343306302699812516235269158694534610930524100484938122⟩,
  ⟨782607564285551909303409626132584246295696944534312492102,782607564285551909356385788822781874554142459876655283179⟩]
def bs0_6_1 : Fin 21 → Fin 8 → RI := ![bs0_6_1_0,bs0_6_1_1,bs0_6_1_2,bs0_6_1_3,bs0_6_1_4,bs0_6_1_5,bs0_6_1_6,bs0_6_1_7,bs0_6_1_8,bs0_6_1_9,bs0_6_1_10,bs0_6_1_11,bs0_6_1_12,bs0_6_1_13,bs0_6_1_14,bs0_6_1_15,bs0_6_1_16,bs0_6_1_17,bs0_6_1_18,bs0_6_1_19,bs0_6_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_0_0_0 : Fin 8 → RI := ![⟨-376225907036466717497512999227363635142277521605628478070254,-376225907036466717487707286513582077147026032135913192168319⟩,
  ⟨321944781721467240656724111722731508592203035973484717430551,321944781721467240663776043647698306044843837986636396825850⟩,
  ⟨-48616828985707993868775808265770014295961991842083399197330,-48616828985707993721075369274777667599695294424594740596251⟩,
  ⟨788162705153727894034682243291809208871421428516441901290291,788162705153727894089335172669177490547308770178274436147084⟩,
  ⟨405094550931871463200294195904828087641189561151440673005774,405094550931871463356841166472128937729524781512142279693763⟩,
  ⟨111354014587842592164691465872401835894066811988800580811706,111354014587842592231880267500501186993689506705309337902279⟩,
  ⟨20790397299857525087523259796120619741139325646798039995269,20790397299857525205642663052184377691165436114394125222365⟩,
  ⟨33967791675520508834299113028100662359868284115313909529848,33967791675520508900927911744650360187823782851427037287065⟩]
def bs1_0_0_1 : Fin 8 → RI := ![⟨-398084715839313237712908617239324826353246554288835175590607,-398084715839313237702555991277787969779607373741532102038016⟩,
  ⟨348713417363603320924951475005571621266779694541102113245666,348713417363603320932396728161187918901132028505919602364850⟩,
  ⟨5304927677537298955587177061628812983457347805142501034889,5304927677537299111525602330874795009462356200951475349874⟩,
  ⟨782562104401593839213307144142782966451031272281491155466596,782562104401593839271008338544688149991293610431295525820150⟩,
  ⟨369423790956618154424771516479354188575706840823772349619910,369423790956618154590049888282042738928091392300559622361124⟩,
  ⟨110991846768146709735503648513981519831353357024057305143798,110991846768146709806439902957310556737791037702116023605413⟩,
  ⟨23228264923868416083220932138028104322026903167240424277513,23228264923868416207928440546836229079256427389523996669410⟩,
  ⟨38364326014013823732482480421189505486054673840779613405930,38364326014013823802827497811812375892327270283887537475118⟩]
def bs1_0_0_2 : Fin 8 → RI := ![⟨-419042367889254901037880676727453861676333457228879833826503,-419042367889254901026922558222478499206071122618157876371052⟩,
  ⟨376733609060816035449864182452349346115389015645099500415235,376733609060816035457744885056872043842269358161784657816787⟩,
  ⟨59894202952899080070326508197970445008808986883633971930128,59894202952899080235385281684971510047411129859284970174151⟩,
  ⟨770543149328816800079274968946617604484350687678305964675419,770543149328816800140350924794427077771687464881042940148047⟩,
  ⟨332470808802408102398204446608927390626652926504172963280688,332470808802408102573149430737235520728310477172846472818447⟩,
  ⟨113074073303292418906968692569619702175979206353290621020650,113074073303292418982053785509397849625808132500407275259657⟩,
  ⟨25933254944136723109738694437867042495278206533981538278345,25933254944136723241739952928162336500530394046939133820085⟩,
  ⟨41489240231629720593898955757159651643178935718286968063928,41489240231629720668358232047478544559269554642583418457850⟩]
def bs1_0_0_3 : Fin 8 → RI := ![⟨-438563254407092513359983453749475512633035835397317447127893,-438563254407092513348351745537524444123834747810028598902514⟩,
  ⟨405899725947403602324772152302498380758635514462037666150193,405899725947403602333137277497968992838728969155435883286157⟩,
  ⟨113958719480059142205890192223423256997868387796349627784087,113958719480059142381095040587955081952873180163858872507674⟩,
  ⟨751589305042662859349980231382704804754884935018423328522767,751589305042662859414810493700657882433035903146030327059608⟩,
  ⟨295168184183700332507823620321460444213216555457962150234373,295168184183700332693522379429193187839367495145301741395322⟩,
  ⟨117549002001494527548504423737925263349299718778968514388970,117549002001494527628204957342312782127790783275259765571172⟩,
  ⟨28720141632081435090568741460445176950128507351930135362156,28720141632081435230684046991275973517350357452652279526051⟩,
  ⟨42989220140619685162952956555280929178292441287000230838638,42989220140619685241989204893730977697492653533672153950983⟩]
def bs1_0_0_4 : Fin 8 → RI := ![⟨-456003852986527602045196261486634557946741096381233159395886,-456003852986527602032811486027562946559559194985489616698994⟩,
  ⟨436063769173147644966396818257334044658201063663221475776586,436063769173147644975303523561929035932724956821855899480093⟩,
  ⟨166334243921701987305380977381448623571596817130753725986715,166334243921701987491929046400887099369784213846830100489137⟩,
  ⟨725165780459374291127368886172949772286600702110602066953489,725165780459374291196396429430666667826916627869480732495899⟩,
  ⟨258344705352490612758288814861695523108198346878944064685175,258344705352490612956010197884302088470016439390424405426131⟩,
  ⟨124040288612217709460791192664437075540451502757251824879208,124040288612217709545651747509551617130663170740900349179353⟩,
  ⟨31328462968856341226457250241824556391152497432782064992523,31328462968856341375643987542707451049637094049101102586512⟩,
  ⟨42592522870527601970596736080507021873000040048383020583811,42592522870527602054749998091733856050717985253150375928178⟩]
def bs1_0_0_5 : Fin 8 → RI := ![⟨-470597680080659908156754248331720572186797921812171750142895,-470597680080659908143523245131610224807069443437303825848844⟩,
  ⟨467027917543206679544838501338263604157615352154137704037941,467027917543206679554353784580737881660186663395680794764310⟩,
  ⟨215956857159344357784456052139849178486791716868424694349340,215956857159344357983750589721829755252081256759172084740725⟩,
  ⟨690727805760480860826534777799679635362667177476093360440550,690727805760480860900278839511399700159000558411263644446028⟩,
  ⟨222617802122111097406802822718741401278067043276308030182692,222617802122111097618034125228253228137032267829461892358283⟩,
  ⟨131783663198232111192053323683346565147405907536460585466817,131783663198232111282712236025646806607178730090587231588900⟩,
  ⟨33431459230386831107025633868872308417539983178401317111974,33431459230386831266406012234528765401778047726625944475552⟩,
  ⟨40167440776064870133651454972510727781379732369156206522918,40167440776064870223554746529889561201631400080490492137251⟩]
def bs1_0_0_6 : Fin 8 → RI := ![⟨-481439701172893522122778755106295502614862732896603045726234,-481439701172893522108591807298957648976967731582277989340776⟩,
  ⟨498536808527018143880120004637359457589947599440651057834342,498536808527018143890322770420976860625103243549793211887048⟩,
  ⟨261928435099993942894209814375831459348458981502594974092998,261928435099993943107903451978563004547344995562873917026559⟩,
  ⟨647746885186140460002743254728960989228755755747236214950482,647746885186140460081815350682906534059226196201711918102429⟩,
  ⟨188282869433254385692835183551618846140403543587813254671124,188282869433254385919328021521670635866530770604442025238067⟩,
  ⟨139590721442621440473120330130142332402782841205487444789521,139590721442621440570329380586997425966877030566672036576871⟩,
  ⟨34660992109675842756554514839817691862138505848287550532932,34660992109675842927450181267243541961214610981423421595233⟩,
  ⟨35784315530686467161224658169159082219846302459012511267884,35784315530686467257623493974830091557208589185569311640229⟩]
def bs1_0_0_7 : Fin 8 → RI := ![⟨-487470775733148862570130921576291938161865873678841976733508,-487470775733148862554858140561084922706380105908237207949871⟩,
  ⟨530269967182005254424682101357277318175438218817353619947789,530269967182005254435665761104166373682594356662910987466343⟩,
  ⟨303560272869828805900795863275265249629106692997948462232970,303560272869828806130845072997699988806347977757022784555726⟩,
  ⟨595765959476825127475420092210537135867068554850418653599194,595765959476825127560544166981147784858890401887139553724010⟩,
  ⟨155215970061379683017669225152201093646270059171274321797353,155215970061379683261497253760696301333370837158765393257050⟩,
  ⟨145860240394217834494418240662920670754212780758889058476540,145860240394217834599067426695706053159623516329866916856804⟩,
  ⟨34652617562631626824441496385657125959224080302432246916209,34652617562631627008417086148775620283478193012832256990916⟩,
  ⟨29771917470043389671438630227571650020800639424774479800000,29771917470043389775215589822700489653057471382816948896680⟩]
def bs1_0_0_8 : Fin 8 → RI := ![⟨-487462892421722827690583937565139061327278656496690920343550,-487462892421722827674070680150278239283463753896660980908418⟩,
  ⟨561834936271307765269560076990705741007594574621962322398486,561834936271307765281435844775048572897636616624726042473279⟩,
  ⟨340375515396990111889373294003025381522746493041618208868060,340375515396990112138107418747654176788812722875015826072155⟩,
  ⟨534497252729526341450776413000537441611381411336635145528404,534497252729526341542814382869246834666737267554750295859345⟩,
  ⟨122814143582296421444600020143832947187616003844368058125290,122814143582296421708232098503778691175678741156786155832662⟩,
  ⟨148662307163189196702829412206767227939947462359400979222360,148662307163189196815978349882060355667554066234078189495159⟩,
  ⟨33112946991627071845826212269964731810187670454494190182116,33112946991627072044744553912195252710699254125999215213917⟩,
  ⟨22754091510413961166663463757903663118382882929362757646837,22754091510413961278869331557564464634863393230383992153802⟩]
def bs1_0_0_9 : Fin 8 → RI := ![⟨-480006086166923974709327097484159439159426034707709392404419,-480006086166923974691388115500500866898390558069718469080547⟩,
  ⟨592761771830231531218572315024817877173251725159131717342652,592761771830231531231473414969756452256420026453804800628091⟩,
  ⟨372048327700241342529729210583676245319009943596565493760817,372048327700241342799938586627282055598136842497596565502457⟩,
  ⟨463978768694999233491895076813181409593485280177777655171781,463978768694999233591879437367070305787193555434371826578343⟩,
  ⟨90006236985199347803604423787343110043417341779048625475277,90006236985199348089998015627198558655707952227608656386417⟩,
  ⟨145923870457251272972938334856684213622469710759419288402105,145923870457251273095856345727284033539837649385013753750006⟩,
  ⟨29906949246618100418280654131870762829037363538351794396535,29906949246618100634373243091955768206654605481447019130770⟩,
  ⟨15647193007890669100879735261994947185018582851474188253817,15647193007890669222773253321441323627283808372573408562749⟩]
def bs1_0_0_10 : Fin 8 → RI := ![⟨-463497944388521850461370999132172992733884471589463734533257,-463497944388521850441782918454037134478963841360844709739760⟩,
  ⟨622499592519801095170199840566944667677167620299046888795127,622499592519801095184286915674587634650074091049202760083578⟩,
  ⟨398258971029970269293676104037036554514487192258144356015244,398258971029970269588725347230116586120252920767238885047340⟩,
  ⟨384805726236189451784506905834244063561742905597580545985781,384805726236189451893682650749072835354240871417694621907856⟩,
  ⟨55375717063707113785535747607071481528345745748336573891350,55375717063707114098256992757650845961875510051787332326561⟩,
  ⟨135743852012113559406567742913280181118639966305845746958569,135743852012113559540785387812086656042156482819967256608887⟩,
  ⟨25154900742383577962841882427281058261862857390495486599850,25154900742383578198799478591777061618128306742574457690845⟩,
  ⟨9594137281863928400771630460662048235307336790514386763840,9594137281863928533870602747125643276906048011887778223225⟩]
def bs1_0_0_11 : Fin 8 → RI := ![⟨-436136370357179660582233078111800744659094262428563093273959,-436136370357179660560724660060106699734491431163864885142448⟩,
  ⟨650415719435620384786729373191253880566772281364496450135670,650415719435620384802197489007188537894806852187485520144641⟩,
  ⟨418453275611855615533770871905328928960084440290970207612370,418453275611855615857745567165678681191855382514605525931217⟩,
  ⟨298449591430600218381206837756276181255623350795972875635006,298449591430600218501085737650273185042821104938422829041766⟩,
  ⟨17443140893079117412840939433918206645132326762675215118060,17443140893079117756220129302874622840282026487401984451671⟩,
  ⟨116857847088109077512401143745655862409420091852764565215550,116857847088109077659776951709097046961050851576965406538687⟩,
  ⟨19316439467318182448669001714665498056559605829177617242682,19316439467318182707758940345158516481369084906415256744609⟩,
  ⟨5809143186185800299064645620559862555848191294679171573506,5809143186185800445212110766757566844201169860351688104956⟩]
def bs1_0_0_12 : Fin 8 → RI := ![⟨-395915555502078970539906529844883704453889060235513342987501,-395915555502078970516145964773403042028170089636762608927482⟩,
  ⟨675797487240956376487489588495555683680578003001153150233367,675797487240956376504577371125366706234126660171472667791448⟩,
  ⟨431519208833055667703074846388288241779087377510358355607418,431519208833055668060972940508752189100231848375635039607139⟩,
  ⟨207666311097657291117386307555841086224113570932381093172451,207666311097657291249817730209843777119392794557051001255016⟩,
  ⟨-24844119548134643622243543040632667462674625205543321879745,-24844119548134643242909109170985719700468813701753881202158⟩,
  ⟨89250459400333839340599680220132354745650440998731303565214,89250459400333839503407212910439873104063755066115400330542⟩,
  ⟨13222704243756836071286158558905334987416699202460233189183,13222704243756836357505411477179226370833137078068183609167⟩,
  ⟨5312568141932741360856323310655331228136034712623842595892,5312568141932741522306893375534393929863908464446476316137⟩]
def bs1_0_0_13 : Fin 8 → RI := ![⟨-340623562076925305472091218580885210541691118334837257539920,-340623562076925305445669411670974850042843760381450054356044⟩,
  ⟨697855868909004649977757898009067821617115098252949299199621,697855868909004649996759554400918948028717795082940228641185⟩,
  ⟨435443240128684184121029605944483806580297154605369137074446,435443240128684184519013168533477040977178576894455296331039⟩,
  ⟨116971284282858504115230857908496042108655443618761718961942,116971284282858504262494926234843128239370397754422402414709⟩,
  ⟨-71380510471195541908269096405103329433714525512425585814740,-71380510471195541486448271192257732233243557491374913596087⟩,
  ⟨54867537138767244407070386118675514496203239582747155141337,54867537138767244588112763657407076524650246779439104423990⟩,
  ⟨7999504996084336863655631741896289533065700527825048542828,7999504996084337181932146285081632873266345131693402298980⟩,
  ⟨8554521709932732528772379453011567947149516875132925414147,8554521709932732708305811209323976420927107833199526366301⟩]
def bs1_0_0_14 : Fin 8 → RI := ![⟨-267836967164229842537000517002308526625632494443305667632451,-267836967164229842507408908143600826020688793348627743141251⟩,
  ⟨715728374803837064734975756400964723305507610673628252470103,715728374803837064756257025525899614058626207785007605492776⟩,
  ⟨427102275247260293371190854704596780436516562580489159682714,427102275247260293816920170511112205354641743168417706668442⟩,
  ⟨33112621732433365414815253918075818471203448403628624837776,33112621732433365579746468641534435868123186386062461392371⟩,
  ⟨-119932636406633887543666767645457218824094668918515612161163,-119932636406633887071240452870739027241128130393260750647627⟩,
  ⟨18295455130621387004985349770743430219214411234577046483519,18295455130621387207747229047710854643154028120973628073840⟩,
  ⟨4813536223034907767719769192507133334425237835120439614207,4813536223034908124179649450572500917041100383649022338835⟩,
  ⟨14970227320977352938845095080169384704115672550890769381924,14970227320977353139917001619859369847142866493870326761509⟩]
def bs1_0_0_15 : Fin 8 → RI := ![⟨-174902780574212986545551810025210459070877316229373316653682,-174902780574212986512152658068251049663787047156710181413340⟩,
  ⟨728475807963873173872251188639632168660520461296514295468569,728475807963873173896270712036850869538791803102895407975683⟩,
  ⟨402510250337815346640284890036207631809794697980108138714245,402510250337815347143366058125763810196170890012572461030224⟩,
  ⟨-34607738263178990225102532846842234945815543088125177210734,-34607738263178990038949670078428549684034702611940783026048⟩,
  ⟨-165015659796599663814805703491862380399441928555870635377406,-165015659796599663281592441890098376134166805273726675785829⟩,
  ⟨-12874095607651821902353807744248600502632176774791266273381,-12874095607651821673502620593990815619063908958631486089033⟩,
  ⟨4391360695372999717787378422575487965329288352496714017507,4391360695373000120112840488355449861587926893210587252354⟩,
  ⟨22595999432864759556684960394265726464424192775286626480817,22595999432864759783628726543246038007854655025519608603516⟩]
def bs1_0_0_16 : Fin 8 → RI := ![⟨-58888930430138740134059886789144873043193798139967200082909,-58888930430138740096046039465093367387732610552682946935451⟩,
  ⟨735062373367666128178225775567863766979597658226417619529296,735062373367666128205564029437260568851785571224659955389131⟩,
  ⟨358114929133384706810583775543256294413471061229294589449210,358114929133384707383174682641619801085634983281255444141051⟩,
  ⟨-74455809371878033787234942448505969454939552439119613925996,-74455809371878033575361703472326417669584203179388707501353⟩,
  ⟨-196855122665605361007556435668168649336219533738616836993350,-196855122665605360400670142754031476069679381783277751642146⟩,
  ⟨-28525415243689120208105926181599244959530935515088858629136,-28525415243689119947634819029186144599390727778593881589782⟩,
  ⟨6355352168165899945591226719423234846515044314052103755147,6355352168165900403505209365803127608890843841855462056297⟩,
  ⟨28025546618524505607522192808629254939879119324821863891425,28025546618524505865822334341043043630719770938458676741198⟩]
def bs1_0_0_17 : Fin 8 → RI := ![⟨83530193150380752726900290894260083898170378133342531661806,83530193150380752770560497599031905134690137847969845085202⟩,
  ⟨734298832191077063000257053581402773378729567761100128451807,734298832191077063031655975261593670967556196153170831575722⟩,
  ⟨294198811581030120349428929609799233206400461434651700783696,294198811581030121007069213900409213321023303997742455465100⟩,
  ⟨-73355736213609257121827868425518867948344267616407000175885,-73355736213609256878484190791394296342892251133053423584092⟩,
  ⟨-200953773497578730122826726151029397689779052044166233762627,-200953773497578729425797015662569794823245771921548999088335⟩,
  ⟨-18289172517972530909940647973838251761352375604016133116075,-18289172517972530610780652884881671115127581116580502627603⟩,
  ⟨8693903110760428894784026772613170206289070542181516664000,8693903110760429420713932394399308597204061024611460654836⟩,
  ⟨27230953112389175079773274509625878418995589020005056695270,27230953112389175376439841170489028447313754815885805895815⟩]
def bs1_0_0_18 : Fin 8 → RI := ![⟨256310914213929867102780246882285364299580749887905718051672,256310914213929867153419454219153829574107693353234951393039⟩,
  ⟨724707839765671483965838383772749351250293971729689117746968,724707839765671484002256363098330866165088729445957136532420⟩,
  ⟨222192686669384923660929349444005717869996496005608980091553,222192686669384924423692176803658893840088437307801968256268⟩,
  ⟨-19863672629026916844672446400607270679345858666574866740194,-19863672629026916562430746788945912337203489522475217857463⟩,
  ⟨-159277013168242934838579546091741152701606688541881970358503,-159277013168242934030130968009663019845576449092873236360068⟩,
  ⟨22784327421398388937156621704813195311567335409671476438137,22784327421398389284136770481026061238849126382215994181694⟩,
  ⟨8346258408364636075100206349475052010247996986075456642122,8346258408364636685099002637796338458990264571335393807644⟩,
  ⟨18136237302415256732643823543502815153297183384451171914262,18136237302415257076731974125818394876924116872015694287960⟩]
def bs1_0_0_19 : Fin 8 → RI := ![⟨464497816686631127446623456242503342076582339197675620456948,464497816686631127505983029717328357559547238457683768345525⟩,
  ⟨704226525167582398379777915009917301500809719097313790146775,704226525167582398422467282266640752538238128460840292600774⟩,
  ⟨178965192181774100340476670523138885387153996269674129861115,178965192181774101234591694742833466755566123736543911983300⟩,
  ⟨89404892636448226758928670419326672195588415790771235758746,89404892636448227089774032871132505964966015986262538016281⟩,
  ⟨-54943598585047366003849291216255909347808405569710345743854,-54943598585047365056181164189307065842645121044458651725437⟩,
  ⟨82432929198874173183653212903046124955691850418132075244081,82432929198874173590385362130590747645840191156898106543870⟩,
  ⟨5375125592922214368563345443601906215823072930959714089737,5375125592922215083607483619153606735746384661932399554225⟩,
  ⟨6299407108621070608917061219130206429441198886985421209123,6299407108621071012259193343766244511428875134870754046758⟩]
def bs1_0_0_20 : Fin 8 → RI := ![⟨715066645209841276144674092525427890183969021074263555447768,715066645209841276215058794864404012637744173026924856272299⟩,
  ⟨669537301741269626663725427154335772781364832472742696204563,669537301741269626714343688565784251785925866112321711982387⟩,
  ⟨253326568573157568620357896661415829933935241089984302448735,253326568573157569680541050826397929257277345282832990583716⟩,
  ⟨237175605302323242850761826050529127215031490109265663332881,237175605302323243243056631977593591969488152735641924738921⟩,
  ⟨116082256879744641770854583663917042657738177578277663529107,116082256879744642894537506770942490986469152695537328641992⟩,
  ⟨108676126769142183240141947217978799576092349061810535518495,108676126769142183722418344752684920271909374578498746293853⟩,
  ⟨16480098171824913405889018394517455306622483812734543728371,16480098171824914253741620408942783788435776888878166892071⟩,
  ⟨15442628821662364425060635643359695182185820139643677253346,15442628821662364903317372485853350447652564150837341163748⟩]
def bs1_0_0 : Fin 21 → Fin 8 → RI := ![bs1_0_0_0,bs1_0_0_1,bs1_0_0_2,bs1_0_0_3,bs1_0_0_4,bs1_0_0_5,bs1_0_0_6,bs1_0_0_7,bs1_0_0_8,bs1_0_0_9,bs1_0_0_10,bs1_0_0_11,bs1_0_0_12,bs1_0_0_13,bs1_0_0_14,bs1_0_0_15,bs1_0_0_16,bs1_0_0_17,bs1_0_0_18,bs1_0_0_19,bs1_0_0_20]
def bs1_0_1_0 : Fin 8 → RI := ![⟨-376225907036466717497512999227363635142277521605628478070260,-376225907036466717487707286513582077147026032135913192168319⟩,
  ⟨321944781721467240656724111722731508592203035973484717430557,321944781721467240663776043647698306044843837986636396825850⟩,
  ⟨-48616828985707993868775808265770014295961991842083399197336,-48616828985707993721075369274777667599695294424594740596251⟩,
  ⟨788162705153727894034682243291809208871421428516441901290297,788162705153727894089335172669177490547308770178274436147084⟩,
  ⟨405094550931871463200294195904828087641189561151440673005777,405094550931871463356841166472128937729524781512142279693762⟩,
  ⟨111354014587842592164691465872401835894066811988800580811713,111354014587842592231880267500501186993689506705309337902278⟩,
  ⟨20790397299857525087523259796120619741139325646798039995263,20790397299857525205642663052184377691165436114394125222365⟩,
  ⟨33967791675520508834299113028100662359868284115313909529850,33967791675520508900927911744650360187823782851427037287065⟩]
def bs1_0_1_1 : Fin 8 → RI := ![⟨-354367098233620197282664294463157742509696180000009568200564,-354367098233620197272311668501620885936056999452706494647966⟩,
  ⟨295176146079331160388103427209241895735914845454201511891557,295176146079331160395548680364858193370267179419019001010734⟩,
  ⟨-102538585648953286701376779871422476905119642467629615143461,-102538585648953286545438354602176494879114634071820640828471⟩,
  ⟨793763305905861948853009077416298549427436588263420811617230,793763305905861948910710271818203732967698926413225181970779⟩,
  ⟨440765310907124771967085474094914286442622950363023330338416,440765310907124772132363845897602836795007501839810603079626⟩,
  ⟨111716182407538474590131830415592466149965280991993895108578,111716182407538474661068084858921503056402961670052613570186⟩,
  ⟨18352529675846634085237482301468768353048334371668168548218,18352529675846634209944990710276893110277858593951740940120⟩,
  ⟨29571257337027193932399526960938646655364796682853409341797,29571257337027194002744544351561517061637393125961333410982⟩]
def bs1_0_1_2 : Fin 8 → RI := ![⟨-331607132677868820177392031175119693989232708651228619046411,-331607132677868820166433912670144331518970374040506661590953⟩,
  ⟨269659066492271714376168086859689895053659317471298297707011,269659066492271714384048789464212592780539659987983455108556⟩,
  ⟨-155792823700082091243601405668132134768344993661910260426566,-155792823700082091078542632181131069729742850686259262182538⟩,
  ⟨792945552337353019358678835493648770437161319642165276976682,792945552337353019419754791341458243724498096844902252449305⟩,
  ⟨475153848703421337482832361840047586360485145582674924717697,475153848703421337657777345968355716462142696251348434255453⟩,
  ⟨114522744582075948616225056372841594813203054289163800950205,114522744582075948691310149312619742263031980436280455189205⟩,
  ⟨16181784448093159113771794764748370557321068942837026819760,16181784448093159245773053255043664562573256455794622361505⟩,
  ⟨23903102877656460993733048836657933981799181402434559935660,23903102877656461068192325126976826897889800326731010329579⟩]
def bs1_0_1_3 : Fin 8 → RI := ![⟨-308481619148411780294151451173378710883469638515047546872714,-308481619148411780282519742961427642374268550927758698647329⟩,
  ⟨245499173825990684527601327510857194574963309823570754772424,245499173825990684535966452706327806655056764516968971908382⟩,
  ⟨-207187265778776200226041057456341592324360199038378463677747,-207187265778776200050836209091809767369355406670869218954154⟩,
  ⟨786225979340935022834243955241596263356050053034161649439819,786225979340935022899074217559549341034201021161768647976657⟩,
  ⟨507327584606302134360152273548742082685590687794096545814029,507327584606302134545851032656474826311741627481436136974974⟩,
  ⟨119825393303240206373488101558599505413730139705233625630432,119825393303240206453188635162987024192221204201524876812628⟩,
  ⟨14463387345178111249519350390846152791594507994291871958227,14463387345178111389634655921676949358816358095014016122128⟩,
  ⟨17316642485156824273830588213176412830329420667899887595716,17316642485156824352866836551626461349529632914571810708059⟩]
def bs1_0_1_4 : Fin 8 → RI := ![⟨-285418252797348993223822833391584021696879303162758417495543,-285418252797348993211438057932512410309697401767014874798645⟩,
  ⟨222759730961673258072497901461407104170431037804558641098417,222759730961673258081404606766002095444954930963193064801919⟩,
  ⟨-255501590501714697166632365873200454608701608025981710433846,-255501590501714696980084296853761978810514211309905335931418⟩,
  ⟨774102865618318067946808315420390942880018646318118101416658,774102865618318068015835858678107838420334572076996766959065⟩,
  ⟨536250147438844879829091766846341294062365999909473801255765,536250147438844880026813149868947859424184092420954141996717⟩,
  ⟨127351168704066305923700448734246473249277794718819550126845,127351168704066306008561003579361014839489462702468074426983⟩,
  ⟨13307327805417301846127284655903147508845050366807057211142,13307327805417301995314021956786042167329646983126094805137⟩,
  ⟨10246761664569196814770890394095827126666974835391280125198,10246761664569196898924152405322661304384920040158635469564⟩]
def bs1_0_1_5 : Fin 8 → RI := ![⟨-262751862663183603816881135867292149197903281780873160591869,-262751862663183603803650132667181801818174803406005236297814⟩,
  ⟨201469087156094540134396388131581075129769780436670625754786,201469087156094540143911671374055352632341091678213716481150⟩,
  ⟨-299559702658403487630563548068946947358507531869274566113356,-299559702658403487431269010486966370593217991978527175721966⟩,
  ⟨757047956223877154819428334358158579898383301178027581620250,757047956223877154893172396069878644694716682113197865625723⟩,
  ⟨560888941537864390102005644910613948680396956176928433520963,560888941537864390313236947420125775539362180730082295696551⟩,
  ⟨136565732486783564443619641515003122716403460522349440168697,136565732486783564534278553857303364176176283076476086290775⟩,
  ⟨12739420391824542422870160473190045150479602736466285197868,12739420391824542582250538838846502134717667284690912561452⟩,
  ⟨3151453330351774645856474580545644626991750929713369330081,3151453330351774735759766137924478047243418641047654944411⟩]
def bs1_0_1_6 : Fin 8 → RI := ![⟨-240738916868733137413365196851556985683306836272349209182749,-240738916868733137399178249044219132045411834958024152797286⟩,
  ⟨181627867770734607766887728615258079806736842332067313251284,181627867770734607777090494398875482841892486441209467303985⟩,
  ⟨-338308792796175655387197665259275152137584103720600083331134,-338308792796175655173504027656543606938698089660321140397568⟩,
  ⟨735516160445370210000941233981672278131358111594555695807065,735516160445370210080013329935617822961828552049031398959008⟩,
  ⟨580319604272337351833045918705357986883364243314254000490931,580319604272337352059538756675409776609491470330882771057870⟩,
  ⟨146763706485712433027476586847762841826296022992128759960874,146763706485712433124685637304617935390390212353313351748219⟩,
  ⟨12708346744343992487186132939988825579193593127271345193444,12708346744343992658081799367414675678269698260407216255750⟩,
  ⟨-3543095915794131008614022682533210534188968574546372329170,-3543095915794130912215186876862201196826681847989571956828⟩]
def bs1_0_1_7 : Fin 8 → RI := ![⟨-219570908402552094804222845207988912896367687511318943470871,-219570908402552094788950064192781897440881919740714174687227⟩,
  ⟨163215486824105818837424283723850289874651916224024826259811,163215486824105818848407943470739345381808054069582193778359⟩,
  ⟨-370890118970554189177769570213750585828800515466136753513998,-370890118970554188947720360491315846651559230707062431191235⟩,
  ⟨709962290710369404935682101501973907268308114389932540705157,709962290710369405020806176272584556260129961426653440829969⟩,
  ⟨593810865504893821317046536118280361650151550639858756982607,593810865504893821560874564726775569337252328627349828442299⟩,
  ⟨157165616661639554885100003284580600834760352899329423781820,157165616661639554989749189317365983240171088470307282162077⟩,
  ⟨13104504883098987080864269478147323256825492154980960487134,13104504883098987264839859241265817581079604865380970561845⟩,
  ⟨-9484684385572742417691845903121488082014237131069091437280,-9484684385572742313914886307992648449757405173026622340602⟩]
def bs1_0_1_8 : Fin 8 → RI := ![⟨-199386222744413920855279975391538309913794896632639736058786,-199386222744413920838766717976677487869979994032609796623646⟩,
  ⟨146195710554918876457307206574712700311624443261000692677815,146195710554918876469182974359055532201666485263764412752601⟩,
  ⟨-396690713211267591713784377273633402640278286412991491005819,-396690713211267591465050252529004607374212056579593873801717⟩,
  ⟨680856748661947539837683927179228174807070198458717228157812,680856748661947539929721897047937567862426054676832378488746⟩,
  ⟨600881058914855433588203942568316894995485906489842761627214,600881058914855433851836020928262638983548643802260859334581⟩,
  ⟨167005812032448099167307425453213921286712700766892084050173,167005812032448099280456363128507049014319304641569294322965⟩,
  ⟨13784454104361752554353863318689218552663849492951930147943,13784454104361752753272204960919739453175433164456955179748⟩,
  ⟨-14420267586465312586477846407329960606375987366275548755057,-14420267586465312474271978607669159089895477065254314248092⟩]
def bs1_0_1_9 : Fin 8 → RI := ![⟨-180280309154506009818507294953342417428708867026787453436267,-180280309154506009800568312969683845167673390388796530112390⟩,
  ⟨130521170675083896186935068892786752710680199589743648581007,130521170675083896199836168837725327793848500884416731866441⟩,
  ⟨-415371025117067420868154357062744711310452866061902509526060,-415371025117067420597944981019138901031325967160871437784416⟩,
  ⟨648695555196531175333065074703848442635981481127117738194025,648695555196531175433049435257737338829689756383711909600583⟩,
  ⟨601324323864096991197188199632681008687694522974691898613929,601324323864096991483581791472536457299985133423251929525066⟩,
  ⟨175602064682536661383197067217159366193080735516838558370484,175602064682536661506115078087759186110448674142433023718380⟩,
  ⟨14595148701244807583226792736749532564101920232100802432668,14595148701244807799319381696834537941719162175196027166908⟩,
  ⟨-18204302507892888306883697554848449290933784507363108833439,-18204302507892888184990179495402072848668558986263888524508⟩]
def bs1_0_1_10 : Fin 8 → RI := ![⟨-162314161882546091569830412821162629606051544879201113077359,-162314161882546091550242332143026771351130914650582088283857⟩,
  ⟨116136869107019878287751244366462080593155685305080956550847,116136869107019878301838319474105047566062156055236827839294⟩,
  ⟨-426868442517812017612116236355035590057855545019736682531306,-426868442517812017317066993161955558452089816510642153499204⟩,
  ⟨614003046728504539457622530562649891193045684045145648732757,614003046728504539566798275477478662985543649865259724654827⟩,
  ⟨595209282208922200957032984208224253404542004077129221261342,595209282208922201269754229358803617838071768380579979696549⟩,
  ⟨182403114674716075886197179596327467724813601432761614704142,182403114674716076020414824495133942648330117946883124354453⟩,
  ⟨15393982809207025441514477250781947811235054532948459909777,15393982809207025677472073415277951167500503885027431000777⟩,
  ⟨-20793284994462464703993285961377256376645372817272129421776,-20793284994462464570894313674913661335046661595898737962393⟩]
def bs1_0_1_11 : Fin 8 → RI := ![⟨-145521243636518605867616676133861809868722071775027517282892,-145521243636518605846108258082167764944119240510329309151376⟩,
  ⟨102982806333733392992127433069991408465116326042824283208004,102982806333733393007595548885926065793150896865813353216971⟩,
  ⟨-431379958736506828860509514648076900174283972317680077979218,-431379958736506828536534819387727147942513030094044759660367⟩,
  ⟨577327580859992352617747820357231785832871460687563206521217,577327580859992352737626720251228789620069214830013159927974⟩,
  ⟨582855675602547307722586063326433456026868929320722865350135,582855675602547308065965253195389872222018629045449634683742⟩,
  ⟨187014470069805608323513157340689177721045692527170611125042,187014470069805608470888965304130362272676452251371452448175⟩,
  ⟨16062726148251352444915614449214360712258456225830936407942,16062726148251352704005553079707379137067935303068575909873⟩,
  ⟨-22230730203515454159958514354344707645007036458692887525343,-22230730203515454013811049208147003356654057893020370993894⟩]
def bs1_0_1_12 : Fin 8 → RI := ![⟨-129913053771640315746844467092779369604679553221440864244510,-129913053771640315723083902021298707178960582622690130184489⟩,
  ⟨90995901580351876271276277579209840897328431337974478079809,90995901580351876288364060209020863450877088508293995637887⟩,
  ⟨-429329023266590494658763619001715167892298384189013063141296,-429329023266590494300865524881251220571153913323736379141569⟩,
  ⟨539231751425277995783971986466245622378452082730491901013638,539231751425277995916403409120248313273731306355161809096200⟩,
  ⟨564795504515443158820283156626214770937723041628468323529848,564795504515443159199617590495861718699928853132257764207433⟩,
  ⟨189205283435213565994949634337506922549136501485375793657816,189205283435213566157757167027814440907549815552759890423137⟩,
  ⟨16515095000469390123384622397329976557462667019495505904422,16515095000469390409603875315603867940879104895103456324409⟩,
  ⟨-22626898932781288593137264689490756157412980895621020306418,-22626898932781288431686694624611693455685107143798386586174⟩]
def bs1_0_1_13 : Fin 8 → RI := ![⟨-115483569693840161889397798445082134786318575330329806923502,-115483569693840161862975991535171774287471217376942603739622⟩,
  ⟨80111372570624410670363798658915736819687450498059682458930,80111372570624410689365455050766863231290147328050611900490⟩,
  ⟨-421322149922305634505579649386092755745929703440925533368267,-421322149922305634107596086797099521349048281151839374111671⟩,
  ⟨500279092824748956567856902020556521635176708990315890283894,500279092824748956715120970346903607765891663125976573736657⟩,
  ⟨541725118582472738912665555997848001288220127487548795296520,541725118582472739334486381210693598488691095508599467515171⟩,
  ⟨188900373170025705500612836764801785866114737259725932818680,188900373170025705681655214303533347894561744456417882101332⟩,
  ⟨16698777080024076397339615282242175451967765193998097572874,16698777080024076715616129825427518792168409797866451329030⟩,
  ⟨-22136932639579069426522889560905440610956573673715240818735,-22136932639579069246989457804593032137178982715648639866583⟩]
def bs1_0_1_14 : Fin 8 → RI := ![⟨-102212785492346075715675664542041999881260964391835626577118,-102212785492346075686084055683334299276317263297157702085914⟩,
  ⟨70263723058299175736103009349949878963407603500839711024065,70263723058299175757384278474884769716526200612219064046735⟩,
  ⟨-408100552180784451381201455602194365421507700357395712095255,-408100552180784450935472139795678940503382519769467165109522⟩,
  ⟨461019267530544551890317543151951775225515039894454597056078,461019267530544552055248757875410392622434777876888433610671⟩,
  ⟨514453916737419731941393712795799737391310797432027130801835,514453916737419732413820027570517928974277335957281992315368⟩,
  ⟨186161784649735119483046604463550280112949880001050898291807,186161784649735119685808483740517704536889496887447479882124⟩,
  ⟨16593259098326102000955469331571495689475163916345763337420,16593259098326102357415349589636863272091026464874346062054⟩,
  ⟨-20940122393281312176379719356487148577519846464822050777840,-20940122393281311975307812816797163434492652521842493398258⟩]
def bs1_0_1_15 : Fin 8 → RI := ![⟨-90069548945852906087699973586168880122342837736106239398867,-90069548945852906054300821629209470715252568663443104158523⟩,
  ⟨61387457078042022782817878873020673875863759579440402381889,61387457078042022806837402270239374754135101385821514889000⟩,
  ⟨-390491279972238905197666278651272623836479905942160327837346,-390491279972238904694585110561716445450103713909696005521360⟩,
  ⟨421973466429996195714892900439351646949457564315657159309942,421973466429996195901045763207765332211238404791841553494627⟩,
  ⟨483854180171200467693793978813802830468515624212302791341077,483854180171200468227007240415566834733790747494446750932654⟩,
  ⟨181164016691170550680378183349528801884525672728491349091122,181164016691170550909229370499786586768093940544651129275469⟩,
  ⟨16204925675565378593055885320285734882379641421767169407052,16204925675565378995381347386065696778638279962481042641901⟩,
  ⟨-19222064260777562673563912557641282767219220326500682416142,-19222064260777562446620146408660971223788758076267700293442⟩]
def bs1_0_1_16 : Fin 8 → RI := ![⟨-79013866055542366666146890580569388271103931342080024689328,-79013866055542366628133043256517882615642743754795771541868⟩,
  ⟨53417612624132932028794687711745361609252320778338728195331,53417612624132932056132941581142163481440233776581064055162⟩,
  ⟨-369361310976052626185549464610674128011368196557561498776790,-369361310976052625612958557512310621339204274505600644084948⟩,
  ⟨383621350273154628164938496393917743962739808185493539222578,383621350273154628376811735370097295748095157445224445647222⟩,
  ⟨450815327519082982959481672534438046260462095109003384084733,450815327519082983566367965448575219527002247064342469435938⟩,
  ⟨174166430313659903823163056044691814656295949319033961852675,174166430313659904083634163197104915016436157055528938892028⟩,
  ⟨15560765067865607582041408067296344139936839771986227882828,15560765067865608039955390713676236902312639299789586183983⟩,
  ⟨-17160603913376136247094764469939380590134341848949921292944,-17160603913376135988794622937525591899293690235313108443172⟩]
def bs1_0_1_17 : Fin 8 → RI := ![⟨-68998808044713612692250682480390607830851556407686414214852,-68998808044713612648590475775618786594331796693059100791457⟩,
  ⟨46290179166116290941429292656439041283833100372188522824550,46290179166116290972828214336629938872659728764259225948465⟩,
  ⟨-345577004458748895544616949837148509115453924451619376681176,-345577004458748894886976665546538529000831081888528621999767⟩,
  ⟨346390429662295046874901641465235722531686721391274490555553,346390429662295047118245319099360294137138737874628067147348⟩,
  ⟨416204723188223220398597202465513358278922293923970081002721,416204723188223221095626912953972961145455574046587315677015⟩,
  ⟨165485611244031799356582044346430506231754101965757489232413,165485611244031799655742039435387086877978896453193119720887⟩,
  ⟨14701740619149863956948903447343984763141912524277775154807,14701740619149864482878809069130123154056903006707719145643⟩,
  ⟨-14915798942062726959928343190958451239469776918153198579894,-14915798942062726663261776530095301211151611122272449379347⟩]
def bs1_0_1_18 : Fin 8 → RI := ![⟨-59972122342265913075048218959526467294624996835213169501685,-59972122342265913024409011622658002020098053369883936160318⟩,
  ⟨39942409288753168440595684083972617073853583559762250747259,39942409288753168477013663409554131988648341276030269532709⟩,
  ⟨-319970323224934668128780843884592816019922986026086637627199,-319970323224934667366018016524939640049831044723893649462480⟩,
  ⟨310648353816863038272887019623307475152390018147054380743607,310648353816863038555128719234968833494532387291154029626337⟩,
  ⟨380836127776357995866393607858885746281584448710400296144928,380836127776357996674842185940963879137614688159409030143369⟩,
  ⟨155469664042806083024455364114839656349437056971762154940957,155469664042806083371435512891052522276718847944306672684516⟩,
  ⟨13676625010885233550143039765212040763862077915231524827587,13676625010885234160141836053533327212604345500491461993112⟩,
  ⟨-12623704003710897007387071868604087126016085157720925843613,-12623704003710896663298921286288507402389151670156403469915⟩]
def bs1_0_1_19 : Fin 8 → RI := ![⟨-51877627357502359789706167937667225085118215311951864366147,-51877627357502359730346594462842209602153316051943716477572⟩,
  ⟨34313786065572932478756588541309847791667578410370533209565,34313786065572932521445955798033298829095987773897035663559⟩,
  ⟨-293312701566713864663131219386637332746106452360470357369721,-293312701566713863769016195166942751377694324893600575247528⟩,
  ⟨276698400926610248828449795584366283471570257398567128054467,276698400926610249159295158036172117240947857594058430312005⟩,
  ⟨345446342185312234830037946991141091349926600749124226060475,345446342185312235777706074018089934855089885274375920078901⟩,
  ⟨144475939209121254794316366070406578544599908393518221931537,144475939209121255201048515297951201234748249132284253231333⟩,
  ⟨12536457721489664074039109225370614000451138686465274920930,12536457721489664789083247400922314520374450417437960385426⟩,
  ⟨-10393163102716666526549526038129025904939358726150208736300,-10393163102716666123207393913492987822951682478264875898659⟩]
def bs1_0_1_20 : Fin 8 → RI := ![⟨-44656327314205709639816135314933040113907639384513493922472,-44656327314205709569431432975956917660132487431852193097942⟩,
  ⟨29323862212335576929704784437470486066097008878180301574896,29323862212335576980323045848918965070658042517759317352704⟩,
  ⟨-266291729220086153189159403590453956146257794858382528003626,-266291729220086152128976249425471856822915690665533839868628⟩,
  ⟨244775287158022057098909854595838676427114419357044673121468,244775287158022057491204660522903141181571081983420934527505⟩,
  ⟨310675200040814902937885327559920618502875291519765148323971,310675200040814904061568250666946066831606266637024813436864⟩,
  ⟨132849172863955408998685768252042583460247820032259712768267,132849172863955409480962165786748704156064845548947923543626⟩,
  ⟨11335435646395838524400174881772197280333591921946869152923,11335435646395839372252776896197525762146884998090492316633⟩,
  ⟨-8310443393130602033194874832715048025748915141936882244568,-8310443393130601554938137990221392760282171130743218334163⟩]
def bs1_0_1 : Fin 21 → Fin 8 → RI := ![bs1_0_1_0,bs1_0_1_1,bs1_0_1_2,bs1_0_1_3,bs1_0_1_4,bs1_0_1_5,bs1_0_1_6,bs1_0_1_7,bs1_0_1_8,bs1_0_1_9,bs1_0_1_10,bs1_0_1_11,bs1_0_1_12,bs1_0_1_13,bs1_0_1_14,bs1_0_1_15,bs1_0_1_16,bs1_0_1_17,bs1_0_1_18,bs1_0_1_19,bs1_0_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_1_0_0 : Fin 8 → RI := ![⟨-26648003543229076746733690503528086388752483009574850576591,-26648003543229076745322362930448771049231802689910862853119⟩,
  ⟨15361991517777810404594272527701125590719206693703705676215,15361991517777810405609250863210114645660157480515109945842⟩,
  ⟨-314271869427859622949421580600453425733341907840465361781108,-314271869427859622928163186827072320396361281065109507991859⟩,
  ⟨213585000772797176853948913483664133784798278411487820901180,213585000772797176861815061354077846679831303344281033146584⟩,
  ⟨328226630718745444905117275756307693380372408571991496452962,328226630718745444927648943007825017700948076341925150801397⟩,
  ⟨187286378943957914874672514022443934712903458305327786618506,187286378943957914884342938916866323764022538849514016607036⟩,
  ⟨229602882781737100756080264355605460012664823598479175529,229602882781737117756901682518511004878652338619312250781⟩,
  ⟨30620974801986520234121834860368692264889175228362269882225,30620974801986520243711659030761166128625322911701549580677⟩]
def bs1_1_0_1 : Fin 8 → RI := ![⟨-29067339379064313764262745874957941641030650262210831804939,-29067339379064313762808890985945890145199557262811397381793⟩,
  ⟨16851498071881027405991694305357372623343687172447068851666,16851498071881027407037256826393408068066482334985228926134⟩,
  ⟨-337384262959469404229442254084185243458466823037407870026432,-337384262959469404207543284412284867882258313188132896141457⟩,
  ⟨230884534993942350487847326289623890734565081798525233850380,230884534993942350495950503579771349561603191425149113101542⟩,
  ⟨353349185158311645850744884031907699598602552534697941129640,353349185158311645873955494535173759022795920253075181638921⟩,
  ⟨200095552087938223678151180446756391911639777621159708977514,200095552087938223688113002762032629691233594408142619572682⟩,
  ⟨1327754472553537760441302425948357409876187727077474292507,1327754472553537777954406971899974022683784353303497939948⟩,
  ⟨30719539354673341314225132625295889528288175217201952376785,30719539354673341324103925487293771701614769028387052240035⟩]
def bs1_1_0_2 : Fin 8 → RI := ![⟨-31498547423383541148389456927985511568246663109122937364385,-31498547423383541146890768153400273601722881564822896658367⟩,
  ⟨18366713806100258153446677449959338532176285558971392163471,18366713806100258154524482962216126709205550835002021277015⟩,
  ⟨-359346988734364990972362085789452889111182167273519620837069,-359346988734364990949787797068953220231746993631841378142159⟩,
  ⟨247752977908790204480917477035553998162429779029340830748171,247752977908790204489270539597057452893181958356870712469052⟩,
  ⟨377472129361484634926375641688658445651821524549543494519772,377472129361484634950302019537972156476424098467618821605554⟩,
  ⟨212025600135372072579333089567998362374402897832266754131336,212025600135372072589602113932980897182177669459267958954744⟩,
  ⟨2566670178748002003241976357507227680907713790891438389535,2566670178748002021295148919237786080504225043478380496734⟩,
  ⟨30359904056265112080094227776928470175309692032274759504180,30359904056265112090277662231500295036708616982464196805566⟩]
def bs1_1_0_3 : Fin 8 → RI := ![⟨-33912473777923332958410293439077741686756163452795576932843,-33912473777923332956864275443590868698852509547584180607328⟩,
  ⟨19891146614689030697683812969141812304029539037797477919386,19891146614689030698795656032114939971947503573866114795765⟩,
  ⟨-379727217605419430072744123889193857352866623198644089105324,-379727217605419430049456929650431788220835948460668138062127⟩,
  ⟨263912160454265585749321634647164360243480187547602795948787,263912160454265585757938490432408236628589244124473143105813⟩,
  ⟨400147418488365492971213186726537189792006784832021683978242,400147418488365492995895169636672920867962953388961043476967⟩,
  ⟨222817254222706892234647818977283194870465887562262330310730,222817254222706892245241143444438437493164079305284457832281⟩,
  ⟨3923636162133322649359824070162775537378657036405730066813,3923636162133322667983123403056129763016760310291332638486⟩,
  ⟨29525639655511470444143809046141548972701471538188740030186,29525639655511470454648840637485933437118797046318761455747⟩]
def bs1_1_0_4 : Fin 8 → RI := ![⟨-36278029375325092302848333916485707164219838145954800462155,-36278029375325092301252282094548072637187286599166389548283⟩,
  ⟨21406716350836018564611724828551273690493537589645589169857,21406716350836018565759550501694124205628319581419076958356⟩,
  ⟨-398095202567948143935470591242267658054574138871456443984109,-398095202567948143911429752842518738918847040782751012108106⟩,
  ⟨279077568181445483159287362064087302161991912945124448370652,279077568181445483168183085409882212058826588098481789689086⟩,
  ⟨420924405296905500056232504606016349216705976856528393302271,420924405296905500081713271264510194375352779302978591669302⟩,
  ⟨232219697324041905432077728026129963439542055703995774717422,232219697324041905443013884568717908570327446364618062858053⟩,
  ⟨5368532016390880982311089922224390491763238415073157749997,5368532016390881001537095646215022630782216600873032390319⟩,
  ⟨28216101464365879002361704850436071379811851443016559297065,28216101464365879013206711092150070107498062522656986988753⟩]
def bs1_1_0_5 : Fin 8 → RI := ![⟨-38562710650306004587479640312334262539225010562046273475554,-38562710650306004585830617021510654129986237573890389441212⟩,
  ⟨22894020478760250822146901771271196544566519974594184394444,22894020478760250823332822706164724650662095185202638030024⟩,
  ⟨-414037224565281417054857016227970780666248528396522015740019,-414037224565281417030018284861467564411459795223670238968226⟩,
  ⟨292965512932136637780422149616347628792173756047505957837282,292965512932136637789613113709353822011183782007636269437597⟩,
  ⟨439362577867242200365241703057391050650615950614306518310723,439362577867242200391568152556365971555764366495141435044443⟩,
  ⟨239999135688244568516371171529440594114833518374248412178290,239999135688244568527670288890847256595288686850078220783457⟩,
  ⟨6864506361526338869342526346217281057263244692471806890768,6864506361526338889206625238527568486296057782106087551422⟩,
  ⟨26447826976611779331966373138341282918526566195181039096541,26447826976611779343171315005441571047880818273466763928112⟩]
def bs1_1_0_6 : Fin 8 → RI := ![⟨-40733205865373318588815234772249895706504936450647459722475,-40733205865373318587110041818169430445836433127579021142498⟩,
  ⟨24332664831450786055905154540813186215579005914981710221928,24332664831450786057131470769044898836643703819134646631124⟩,
  ⟨-427169420495327319127286582977733346510657702912543325031299,-427169420495327319101601785224924105473980056022791471122459⟩,
  ⟨305301044253046258135054135547767459885744642160740720969090,305301044253046258144558165781839322960752479284950943081516⟩,
  ⟨455045388259672597720962600037784084263636466984356394542149,455045388259672597748185791148257170654984109398666419972635⟩,
  ⟨245947678259455007936970209962624742473572991653732655122043,245947678259455007948654202189645222653602690655901382136590⟩,
  ⟨8369150380834060507273102911715642723894477570421393140455,8369150380834060527813820352547818985451969917663354634300⟩,
  ⟨24255184600128813295552620618367346862551859211406705054342,24255184600128813307139229509192284723529890506880636770355⟩]
def bs1_1_0_7 : Fin 8 → RI := ![⟨-42756074768230087437440684176669287739540364230651266725895,-42756074768230087435675830940285217197810417479127629470757⟩,
  ⟨25701653272606178452333985887789661851242421849881033496656,25701653272606178453603207742734072110830759820353141881884⟩,
  ⟨-437151981126452137989952576468671532274859105125742356132756,-437151981126452137963369134206923678809990100380100663282601⟩,
  ⟨315826355096793356320640957759694191957185751662413784905768,315826355096793356330477509381164262957152071601517620722794⟩,
  ⟨467594701579127361212048263767057093865428162538115129844171,467594701579127361240223923783229540830545783649316931848323⟩,
  ⟨249892134354662049703404411038282117081895754181964152571400,249892134354662049715497195873325592048362415341727402192998⟩,
  ⟨9836168671725486328047196916605581180980770635874596025375,9836168671725486349306580827480499926277408951001479004325⟩,
  ⟨21690118087332035177459491747053387833594393705389816945238,21690118087332035189451486055219850171850410243711713211580⟩]
def bs1_1_0_8 : Fin 8 → RI := ![⟨-44598484578646598836079950409827092457243082330130988015536,-44598484578646598834251616854399826092061455852094357659005⟩,
  ⟨26979826339619654392955793028784991294422046495039326512506,26979826339619654394270667749711338479407965065893882193535⟩,
  ⟨-443703095246529219667310979773153471444513502475820312730641,-443703095246529219639771352962300386968800393336485322060961⟩,
  ⟨324309369806131791539495542528916431051327169728537356574539,324309369806131791549685906820154365827996841429561061862039⟩,
  ⟨476685277485899245815819187821728686788984736751574712721115,476685277485899245845008303149850845629853228756754151270360⟩,
  ⟨251702273914543796733501147962642666612671797669999099644924,251702273914543796746028900320104283141363758937118010351140⟩,
  ⟨11217503280883510185586332163913488759625358149582873108294,11217503280883510207610398624752716298951466012193466268706⟩,
  ⟨18820871303423601483678624630543883711651538577649342989057,18820871303423601496101961108652628794081490604831825319424⟩]
def bs1_1_0_9 : Fin 8 → RI := ![⟨-46228980952818684385509583572396989263938573211077483906347,-46228980952818684383613577176384617150569801684564813847093⟩,
  ⟨28146335504930658317047051326974993935655113639350400912249,28146335504930658318410594031433746825752383614472355694548⟩,
  ⟨-446611924223068153204308863808081253320248672832713364123454,-446611924223068153175749901783779295603595988909746242504350⟩,
  ⟨330552143391860961712182155067510034015533859819101703014190,330552143391860961722749699384925238102426944519518786772319⟩,
  ⟨482058593566944307123891948754381228306424238858888215602569,482058593566944307154161452473740763077535473247767183869412⟩,
  ⟨251298047395879911318661326935617252511514803359212295036928,251298047395879911331652773997967888539733161890027196354013⟩,
  ⟨12465816494646078915040156583633277701023556969189344405539,12465816494646078937879408618228025796222161834390469164512⟩,
  ⟨15729638681443626833597453656346890725725711715326199486210,15729638681443626846480620052515140647789519891433146869364⟩]
def bs1_1_0_10 : Fin 8 → RI := ![⟨-47618268962560036913158942220284429331861728739284193005697,-47618268962560036911190647642644701435779734752972506703602⟩,
  ⟨29181136931558048234848806445882889090230843286974857148441,29181136931558048236264336328692410148676371846484132748553⟩,
  ⟨-445749831229778575516743857744866398731466280517336788059164,-445749831229778575487096041042497748366605693616425689648422⟩,
  ⟨334398656498278004731435169346634376747654911434625714712556,334398656498278004742405617665168603152653719725271389275248⟩,
  ⟨483535244690263408362580888997927867012096639123243435720815,483535244690263408394004464447975288053856221101880931625644⟩,
  ⟨248655243313002640145382504255840483884370964495659970058085,248655243313002640158869270367276347975573448313298089031486⟩,
  ⟨13537185114559787311995495861014689393736038729109089459605,13537185114559787335705529767709097853317545693465683156070⟩,
  ⟨12509167378796913199983012464817610538628361057286815094725,12509167378796913213357369541720404021567376433426302413812⟩]
def bs1_1_0_11 : Fin 8 → RI := ![⟨-48739976699303309497140110105148100402906723146133675360204,-48739976699303309495094430087147017404705304851676212484946⟩,
  ⟨30065486894271825577321096183425817484971371335951531425014,30065486894271825578792279018062593270469834213427621796542⟩,
  ⟨-441079075509361607727542204020246785341447673192862080003378,-441079075509361607696728754197012883357161517657279889611762⟩,
  ⟨335741567607159482004205111030591531173815994161591955760823,335741567607159482015606873332247554204855625781344953758913⟩,
  ⟨481025118259025748138980449665662825150790074808952495019235,481025118259025748171639473941207176597537178608486024479030⟩,
  ⟨243809080152328891869789529564021465113168628263514200271341,243809080152328891883806541171622410318649658739946649782836⟩,
  ⟨14393809954542028904932221509061177809963985471461957494610,14393809954542028929574438756287344536397107593307555087262⟩,
  ⟨9258433992555378227994381704983798351931088342227965411574,9258433992555378241894564805922056152466436763895247844642⟩]
def bs1_1_0_12 : Fin 8 → RI := ![⟨-49571373301278818101790737503073873179005612668891598903117,-49571373301278818099662023126083518823393141357227067368248⟩,
  ⟨30782420673771105586472347641358157262634072980938669595185,30782420673771105588003245936154123479651881172968093638022⟩,
  ⟨-432658227366147599875498993745493226908628570484970632220349,-432658227366147599843434822875043215572843162798779960471776⟩,
  ⟨334527490237012192205682602093330868356422631216638208453653,334527490237012192217547163080952222390483102175438246718660⟩,
  ⟨474534565873859981502326855490944262863163054243385511998633,474534565873859981536311512867642347551577618610319972886142⟩,
  ⟨236855294318049187807591034749788978412169498858521452716125,236855294318049187822176998277501710926256753987371005191642⟩,
  ⟨15006507478462213439329172323729651957246863326293239726014,15006507478462213464971619663065963661542896162019435585483⟩,
  ⟨6077624078490742890365456374717286237773780064349213345838,6077624078490742904829849314632661070160206083433202721319⟩]
def bs1_1_0_13 : Fin 8 → RI := ![⟨-50094014360155935830306601133521769996710423225181805250401,-50094014360155935828088569058763085007082242118833499181380⟩,
  ⟨31317197814934189745523003360649306775299574662828839304198,31317197814934189747118135877127420065595428500039886987576⟩,
  ⟨-420643674565760050250036649005068532126417305647043614924517,-420643674565760050216627113085162540699421326796005715627145⟩,
  ⟨330760404236635347249349181825256255747157991220931239957624,330760404236635347261711562193485112467157147031856883819807⟩,
  ⟨464169879103164518843482592972979204439978392290780775872970,464169879103164518878893196164437116793974513523022428777080⟩,
  ⟨227948402494361011471993633243507281479798929081623794426962,227948402494361011487191602165919097087954989653902135919521⟩,
  ⟨15356735324582018191551033004991449960543911429102170136231,15356735324582018218269399399430487355020996983215711475449⟩,
  ⟨3062744804718273640036555943882259820124414326685093896470,3062744804718273655107853356703035368232892550146346457989⟩]
def bs1_1_0_14 : Fin 8 → RI := ![⟨-50294290980159618543451182283824289168787373454283728291902,-50294290980159618541136815960652557867668069877617622028204⟩,
  ⟨31657699059248437381985198412038580953783048145733618245517,31657699059248437383649611212522060849032551609088016097318⟩,
  ⟨-405286780560145104590205283293913915964598555768366880843984,-405286780560145104555344694177168913969658541883109734243659⟩,
  ⟨324502890295840229054839630076597975875569703003985605504511,324502890295840229067738937135451133694861496169338634487972⟩,
  ⟨450136538291055774375533146045384321988692576682225658969536,450136538291055774412481713400459010355026523345775818119164⟩,
  ⟨217296985959878150661179276458708102661646536273430784772656,217296985959878150677037328222461106832951412524683825190868⟩,
  ⟨15437918915643067138991155309481967359775355748111384240793,15437918915643067166869961976286037918290241308777074415501⟩,
  ⟨300284240864693465162824997853556848727573091981562750973,300284240864693480888703615926533766651795759620921869913⟩]
def bs1_1_0_15 : Fin 8 → RI := ![⟨-50163864166330845270753068895915549122865209632636970394616,-50163864166330845268334499888517057358328085030275041717402⟩,
  ⟨31794763716817696831511009637037594006094558241060739712175,31794763716817696833250361430415252524696787190586334180962⟩,
  ⟨-386926516271419905177303648754327256969068909113867026721855,-386926516271419905140873486608696544640838728867126382021451⟩,
  ⟨315874994973871194003964916744841612479662412150475512638500,315874994973871194017445005854922771777407004252593697268831⟩,
  ⟨432733938813366129470247857927959668487303766275276683861716,432733938813366129508860008035126524202717339169327322779754⟩,
  ⟨205156059443591637749209819204938120313998387110929044981999,205156059443591637765781868378908102375823942245034112136383⟩,
  ⟨15255898363614059505795912851562854706125272447128958767147,15255898363614059534929942798308402783227920028625713050866⟩,
  ⟨-2137622620090100150976460960751650065551484147796415003153,-2137622620090100134542535933899632468028692217049324094072⟩]
def bs1_1_0_16 : Fin 8 → RI := ![⟨-49699973285880998504785256261657960915450131876809263363253,-49699973285880998502253620737037510782865734329542468160990⟩,
  ⟨31722460371943932911359575365701209646492751377104469900055,31722460371943932913180240716339605287872524529467038394269⟩,
  ⟨-365977705896837129743989883119517028848346564840052526203406,-365977705896837129705856634750922530886742469404810730648307⟩,
  ⟨305050683846209627709503485164291549019658531278470302840690,305050683846209627723613759612549112347983883256500343279198⟩,
  ⟨412345599060202684950111248560540042241137224927742702920901,412345599060202684990528491399129097546255524587440745766801⟩,
  ⟨191816832561526614790670095778755170298200933283752599187210,191816832561526614808016877399212943931198629427963549507881⟩,
  ⟨14828403127331078162519872947611666868261801678649713382149,14828403127331078193015899714786623051383094023556154503565⟩,
  ⟨-4197067323993308319939874226271536234521655183504769623201,-4197067323993308302737673966725138708827486156637651218022⟩]
def bs1_1_0_17 : Fin 8 → RI := ![⟨-48905615248920538159488804967573497036109454574051859668391,-48905615248920538156834068905718246140587630757491343009119⟩,
  ⟨31438288312265331759558625952777332500621336961963000429565,31438288312265331761467820983369845359756251352932000427989⟩,
  ⟨-342915376631064959925502162731691666462187504206926014011582,-342915376631064959885514688778404453473493104499563339826906⟩,
  ⟨292252010382865933903694715501707507517889130546712472708450,292252010382865933918491100706661251704588206837784285579301⟩,
  ⟨389425196648356890138253053578358959448314240933278416182679,389425196648356890180635581016313636211374110002821571925392⟩,
  ⟨177594422526222818937865933047031591321888871316389092169054,177594422526222818956056200278637786694876739767975781001753⟩,
  ⟨14183576948301708151158281437729689719228741705260800470396,14183576948301708183137174613318106869132256229981593290175⟩,
  ⟨-5844896453680486330499287755946899290035828828859503442924,-5844896453680486312460632140632903548853526212364073648237⟩]
def bs1_1_0_18 : Fin 8 → RI := ![⟨-47789598583860602910047002347205461992175356047984827517210,-47789598583860602907257747023724459616366617744301895998496⟩,
  ⟨30943311586336850817921410673637079703734752611462860128172,30943311586336850819927347338724494629528689863413897702237⟩,
  ⟨-318256043877761887751419867055837929432577000364964795249086,-318256043877761887709406170779361541748574731229017134786588⟩,
  ⟨277741299433994493660983315964890047841191143166130708240437,277741299433994493676529455106413516398806089158273524900927⟩,
  ⟨364479129531776284344225757632192139233892544896186188370479,364479129531776284388755868168758717927399974535707080044067⟩,
  ⟨162814299291866476146946288424025659835839864662196789999899,162814299291866476166058282434057806889720662954782215855055⟩,
  ⟨13357698488128799378610455872598954109139682549703652443907,13357698488128799412209765163563886194978634641458356725239⟩,
  ⟨-7069641705080847116741486029209842055984358738116371488579,-7069641705080847097788786012729333359324889539648234815440⟩]
def bs1_1_0_19 : Fin 8 → RI := ![⟨-46366482303813947737229983361484068177907504627023711845011,-46366482303813947734293139882702907640468657517259222308544⟩,
  ⟨30242231544455215999330682849282527348578258643050786632816,30242231544455216001442759848498708766687453673783577073866⟩,
  ⟨-292537051789167122236299705354097913842757602498948264144531,-292537051789167122192062934022830449159007774197219074669120⟩,
  ⟨261811794473821328605682582868910161115813264135742592943333,261811794473821328622051316478256958534117700350981129974894⟩,
  ⟨338046613046739239737099034663638764384248914591465070610696,338046613046739239783985371543204488189732718681881410600041⟩,
  ⟨147798401802279590083589893553468037556225343579971684822915,147798401802279590103713162478927533375481036986389021255543⟩,
  ⟨12392349539736071931429846085140580996156558813348019746062,12392349539736071966806999101930384377773214203378512298970⟩,
  ⟨-7880775060755438316731878121221170688369219635945577697402,-7880775060755438296776331929409621131567675181079076701115⟩]
def bs1_1_0_20 : Fin 8 → RI := ![⟨-44656412016799179536721912759941406345105901150102014461771,-44656412016799179533622430539184111416831064379568480806902⟩,
  ⟨29343407782343560420150073992933085609349684691873790728766,29343407782343560422379115191480788443110920496635653988073⟩,
  ⟨-266295280189764331808944451609512978349225722122686239857841,-266295280189764331762257902858800910805586121879158124393950⟩,
  ⟨244777325780441647624080635211510135721107776420054220738758,244777325780441647641355848945452474208501144182623954923890⟩,
  ⟨310678557156086083052687713554869310289421186537818073438341,310678557156086083102170557501440967802605733506220633082145⟩,
  ⟨132851924910096499178119336923042978227325142716076107448039,132851924910096499199357007473139123784685253272104703240808⟩,
  ⟨11331349366048696661716954698757692694542396060567074956115,11331349366048696699053250482841743084837643774726785311612⟩,
  ⟨-8306407392849225551118711658518951194603558480851132164090,-8306407392849225530058052119239576579031033995495555405360⟩]
def bs1_1_0 : Fin 21 → Fin 8 → RI := ![bs1_1_0_0,bs1_1_0_1,bs1_1_0_2,bs1_1_0_3,bs1_1_0_4,bs1_1_0_5,bs1_1_0_6,bs1_1_0_7,bs1_1_0_8,bs1_1_0_9,bs1_1_0_10,bs1_1_0_11,bs1_1_0_12,bs1_1_0_13,bs1_1_0_14,bs1_1_0_15,bs1_1_0_16,bs1_1_0_17,bs1_1_0_18,bs1_1_0_19,bs1_1_0_20]
def bs1_1_1_0 : Fin 8 → RI := ![⟨-26648003543229076746733690503528086388752483009574850576591,-26648003543229076745322362930448771049231802689910862853119⟩,
  ⟨15361991517777810404594272527701125590719206693703705676215,15361991517777810405609250863210114645660157480515109945842⟩,
  ⟨-314271869427859622949421580600453425733341907840465361781108,-314271869427859622928163186827072320396361281065109507991859⟩,
  ⟨213585000772797176853948913483664133784798278411487820901180,213585000772797176861815061354077846679831303344281033146584⟩,
  ⟨328226630718745444905117275756307693380372408571991496452962,328226630718745444927648943007825017700948076341925150801397⟩,
  ⟨187286378943957914874672514022443934712903458305327786618506,187286378943957914884342938916866323764022538849514016607036⟩,
  ⟨229602882781737100756080264355605460012664823598479175529,229602882781737117756901682518511004878652338619312250781⟩,
  ⟨30620974801986520234121834860368692264889175228362269882223,30620974801986520243711659030761166128625322911701549580677⟩]
def bs1_1_1_1 : Fin 8 → RI := ![⟨-25438335625311458237990426475779526840768605723124583312255,-25438335625311458236557835244733843423092719063592872238945⟩,
  ⟨14617238240726201903880269546109478879516044266468646186069,14617238240726201904910539974381991129347917241143428358116⟩,
  ⟨-302715672662054732309731531807847151990393391778953667706310,-302715672662054732288152850085206411533798823466638253869197⟩,
  ⟨204935233662224590036881192370817382343912334371053780923701,204935233662224590044865854951097968204947901650762326671983⟩,
  ⟨315665353498962344431963999992633322719448486616416481034200,315665353498962344454835138870025014591833004360571928463057⟩,
  ⟨180881792371967760472787482099860781749297930526013485135683,180881792371967760482603605704710095164654379191598055427531⟩,
  ⟨-319472912104163229342672380335126048889901183743613669054,-319472912104163212085709398277864970053109113120185307709⟩,
  ⟨30571692525643109693925701632102389478394452170019518552544,30571692525643109703660010148297567496925822917281708333396⟩]
def bs1_1_1_2 : Fin 8 → RI := ![⟨-24231635759514837320896576368430395961519189835243347130692,-24231635759514837319442144837008231887092527869552622811747⟩,
  ⟨13878912258703596839680656906254261887364911316178826730011,13878912258703596840726634128713723917718862913158415113037⟩,
  ⟨-290872058957071293035766272570624835229342482977234284272840,-290872058957071293013858617111204453887134277948338273209312⟩,
  ⟨196177693725077673309606405742963218522550863791564286933370,196177693725077673317712796996016239842516219669957000050521⟩,
  ⟨302854173720080940991311511574246637017271771673876242793802,302854173720080941014531328101087425515663015955067108406995⟩,
  ⟨174257424525840991095328260851510007101699102970517964351564,174257424525840991105294034323999356956219474406806278352130⟩,
  ⟨-833357677884397663662562082534327977500466401001964268626,-833357677884397646142511314585153684981043395987008649294⟩,
  ⟨30407860286525936575171017750512432537805358318235048381074,30407860286525936585053728837752448305752423382209777562659⟩]
def bs1_1_1_3 : Fin 8 → RI := ![⟨-23031548183122142238040105055133325340997893601976289541343,-23031548183122142236563232985213568251686773869979563361784⟩,
  ⟨13149075084928304205654843762955890938907040268671668833382,13149075084928304206716959450250964387421427348494969922136⟩,
  ⟨-278795131956300174265705777282117174103188103177253063472177,-278795131956300174243460106883449260623695309178979131650665⟩,
  ⟨187347152094240820807604138471792632326461161674890924948098,187347152094240820815835603873118923570650280221406530237916⟩,
  ⟨289849096987088599478258979048591047423075970943945160134809,289849096987088599501837055951015093190940928598473999713850⟩,
  ⟨167445684013521677910240991400550696863068311226041921381263,167445684013521677920360527575844940542558690917187009351988⟩,
  ⟨-1309212184654990304729088327057523148903629065819994212855,-1309212184654990286938719317794675047939077262651827599001⟩,
  ⟨30131531741041296138805786793835671780220402388960637095501,30131531741041296148840979007766419209261656073409751172742⟩]
def bs1_1_1_4 : Fin 8 → RI := ![⟨-21841596185347853047585640455277454672404940588758660570769,-21841596185347853046085702731494699947365258791840162704012⟩,
  ⟨12429688980052079587661241330910513031582260599547060317940,12429688980052079588739945044549839349258158301371801226862⟩,
  ⟨-266539187937034893607124968753524993215533878209007838187091,-266539187937034893584531867494851379679141659142561935590379⟩,
  ⟨178477983315982935538233056304866765074464759782164351896062,178477983315982935546593079985291433326025349836246023741177⟩,
  ⟨276705966254838322239891280179390912520192928079879008737907,276705966254838322263837597345609699796907681756510397191791⟩,
  ⟨160479507682807129093693863730167294955769405896613298900587,160479507682807129103971445902456761495626976839540542621617⟩,
  ⟨-1744660112954890976110592952021557495671311982710659477317,-1744660112954890958042375575276759280968384931661355400116⟩,
  ⟨29745747080795722688501333570723071961025630088364600959547,29745747080795722698693254505279727480450104197200651981654⟩]
def bs1_1_1_5 : Fin 8 → RI := ![⟨-20665165836363909334273649426177277952393617544484018848732,-20665165836363909332749994672446888470913866590300472950038⟩,
  ⟨11722608650532149849169018067020032024859865119756129579657,11722608650532149850264778254319910318916012303817715739632⟩,
  ⟨-254158311254047476931396403160856381597992999725744117493427,-254158311254047476908446059564270501120927190868411255095084⟩,
  ⟨169603941235064379060314823004422237517229040603376915624416,169603941235064379068807035461003645670104644785777912982938⟩,
  ⟨263480063774163247047745819856374462669570731184954916161266,263480063774163247072070776423680281017867992410737810889662⟩,
  ⟨153392092763938001035539203056846792458266846769388785879619,153392092763938001045979294458925784345398094268084890745938⟩,
  ⟨-2137809166060071851181260930801389161926843675361719938071,-2137809166060071832827348724350652818633786802564530814215⟩,
  ⟨29254489357013922248850506869919234225958973221301757675911,29254489357013922259203582557894679843343877246268858600105⟩]
def bs1_1_1_6 : Fin 8 → RI := ![⟨-19505491054677857417692357437098024122966736405024534684252,-19505491054677857416144306523601863385591323060671112217738⟩,
  ⟨11029573964278932565245911499652850986630312764311005148288,11029573964278932566359216567461838747907435743502856929493⟩,
  ⟨-241705983567554793738929208419944795061416831163388103249780,-241705983567554793715611392961576324745359185811620254014371⟩,
  ⟨160757946438243813429280925097847333838958093860750347713509,160757946438243813437909111515312341422744244240879158154084⟩,
  ⟨250225730083829225236607766960429183780424237701201406629720,250225730083829225261322205150980187748484206894735573739149⟩,
  ⟨146216633824428846968567970211376975538503378633850678336982,146216633824428846979175224244786386824812893638507337979116⟩,
  ⟨-2487264401909603306486844226865062305040888128971031917905,-2487264401909603287839056407611133419893070235050111245032⟩,
  ⟨28662629103607331290542260794075514150664384851831295656586,28662629103607331301061105851997099723561616178795148203316⟩]
def bs1_1_1_7 : Fin 8 → RI := ![⟨-18365640109135517275913021356124700926148577901821488289418,-18365640109135517274339865788198493581691322922680625719680⟩,
  ⟨10352203732028236703570742896486794519594573172860471590251,10352203732028236704702102369842603223715741289407473848395⟩,
  ⟨-229234710857854062835145933226961132978641342130249163786306,-229234710857854062811449974069281121632686054468271318847490⟩,
  ⟨151971887173768939190093013265147438308385573273881045943111,151971887173768939198861122495557431777310244318619865583686⟩,
  ⟨236996003724318730951384349708441330932925968496177803136794,236996003724318730976499580550472270202694367954816052851181⟩,
  ⟨138986067580875949913863304185936175919563775309459714410549,138986067580875949924642575460316860327061466547858282950037⟩,
  ⟨-2792133779744260738262216218947422271426871364820344441796,-2792133779744260719312018275491784305997715810757367937205⟩,
  ⟨27975858473076638035124068261988211584757938856237463036818,27975858473076638045813496837460683936098290716692295231470⟩]
def bs1_1_1_8 : Fin 8 → RI := ![⟨-17248503633541645094924729728467305790741096604508094817636,-17248503633541645093325729907751147105198795372495754678430⟩,
  ⟨9691990588348803668907939682462242065639359244868867318351,9691990588348803670057885455112590439175452481997574959479⟩,
  ⟨-216795671793810612994556050649604220460634930362295367523806,-216795671793810612970470807449669260222528459515538336773010⟩,
  ⟨143276435404462959648027083301532482650115653652985688450357,143276435404462959656939237555901030991748913327264642857043⟩,
  ⟨223842284890716263871304409721008241693753449948200014678685,223842284890716263896832240809343958601447477399314892249657⟩,
  ⟨131732828354832839011124574108827744063824080132611303133356,131732828354832839022080930356527544736239648732225760581916⟩,
  ⟨-3052026086459497562730718457833667407033537829826146107874,-3052026086459497543469201204333201903696671169409081006667⟩,
  ⟨27200616255896862883704184157224744150004881135534591315351,27200616255896862894569221744231802382249509564437965504300⟩]
def bs1_1_1_9 : Fin 8 → RI := ![⟨-16156784212969472298002433317906655912826838863656495080609,-16156784212969472296376816664907605761753818855118915113937⟩,
  ⟨9050296991106979527211125729839548087165471249052629903159,9050296991106979528380213414430686016619024010215331321573⟩,
  ⟨-204438390549710105226944194065394880934600724187904760097628,-204438390549710105202458029695584072103951560009731568219475⟩,
  ⟨134700879377267167775985092573502318415491703484614232432699,134700879377267167785045597885843735393943683028307717734672⟩,
  ⟨210814025754321076925424177688110370831835304699539821520289,210814025754321076951376943157217944455270633393968868821316⟩,
  ⟨124488616665655243516432817877021425904067261790895713434816,124488616665655243527571552817307424615340805337134842055985⟩,
  ⟨-3267041564315219000126999208800878020869589045142246198761,-3267041564315218980544856169397493538986040119171800570574⟩,
  ⟨26344005270158540778437527530055699511069046583090598138660,26344005270158540789483423725952031400903997933466750007967⟩]
def bs1_1_1_10 : Fin 8 → RI := ![⟨-15092987581663477544782860793294543066124907997120579949305,-15092987581663477543129819719146701784527477259753712647839⟩,
  ⟨8428352342956658338168062781465204432099750494056676956228,8428352342956658339356873168182430386583151310302305836370⟩,
  ⟨-192210436667421788993155691316204641897088520458303517829539,-192210436667421788968256441313464542450162890946962620918255⟩,
  ⟨126272973809212220995847932957922215571869241472241915707213,126272973809212221005061290489810100139994071916517002360459⟩,
  ⟨197958449678279857977053168668278339127926246939547413149580,197958449678279858003443761572862471824006977623409310694805⟩,
  ⟨117284183131741710313978182135391366795614687542096755217161,117284183131741710325304829371961882588980996068663823454643⟩,
  ⟨-3437755700846203934352730559647949786912480995803730262945,-3437755700846203914440233536334340137414898895427108604144⟩,
  ⟨25413703683341639981709766799287020618546458808997385771230,25413703683341639992942009086477775642287124936917682528174⟩]
def bs1_1_1_11 : Fin 8 → RI := ![⟨-14059415453412181049728745811577638854718684256342141218436,-14059415453412181048047435525249613353014234143150646971956⟩,
  ⟨7827251223399119892337083787087690248492219310993249992362,7827251223399119893546224420636456004060123067156988816249⟩,
  ⟨-180157154050634812695840400830496817692944808003979779927121,-180157154050634812670515340366980970853301368122811706785806⟩,
  ⟨118018808505115265029753554615563176333027132604033033899336,118018808505115265039124472877836173917950491767367813238627⟩,
  ⟨185320301043143465511666272997408343274530294337712020555733,185320301043143465538508180320068473194821589442326688821854⟩,
  ⟨110149129512033870960800606572030956808708198136550983402966,110149129512033870972320954618043003269661099844845494178309⟩,
  ⟨-3565196760461056693415479108329922107860154643411692133686,-3565196760461056673162451766618148077890779628628418166588⟩,
  ⟨24417871863003192484990365471798129265385387957468544793316,24417871863003192496414694117536271458499594180634057258968⟩]
def bs1_1_1_12 : Fin 8 → RI := ![⟨-13058159986733694211040302991352272959960804421565934837536,-13058159986733694209329839126819712773313739164293695234989⟩,
  ⟨7247952705547518690535574705821624576718475000298127741302,7247952705547518691765681591883580468169766192295338578621⟩,
  ⟨-168321420666638418447886530282951472142613854690014848190177,-168321420666638418422122338424849075866306594471324478290764⟩,
  ⟨109962695941713211338868759976451576140759812236566581791171,109962695941713211348402168054358319882006692559450674894171⟩,
  ⟨172941626894533334392524886591053700584433744718959351503202,172941626894533334419832227124176137764026274130504051403686⟩,
  ⟨103111728370828012218880289997894397689475695634251139143162,103111728370828012230600398534591549670352420384263312269393⟩,
  ⟨-3650817733272979289368136546312996919756581396470885345752,-3650817733272979268763925832206195738814505792557175520598⟩,
  ⟨23365056350004721650079910422754766450299345578019718127972,23365056350004721661702334602257064556752752255708923034114⟩]
def bs1_1_1_13 : Fin 8 → RI := ![⟨-12091099869493568157369071991451672306720471335698555555522,-12091099869493568155628528037394288983484617268282958410506⟩,
  ⟨6691280718287557272113052752725896391739351826466531480838,6691280718287557273364792206432548179621236065171599770558⟩,
  ⟨-156743440029183420522844273812454348971070157838087900173242,-156743440029183420496626994804305867942705591012086798030238⟩,
  ⟨102127078081708647340902323389786200889895821750715202662562,102127078081708647350603385268775946605430574807398885973721⟩,
  ⟨160861591136636039892691656157805919667066060192023051519001,160861591136636039920479221538127777942891939515460407982820⟩,
  ⟨96198762499106843527712845824772358273415193676689045834753,96198762499106843539639063313216030932660123552100032925904⟩,
  ⟨-3696463449200599403784895737047442358034329381267145158820,-3696463449200599382818340915225736137041897551305313646276⟩,
  ⟨22264092509909263301623104053232010803978175179714265654851,22264092509909263313449919314620638880282381873317390526222⟩]
def bs1_1_1_14 : Fin 8 → RI := ![⟨-11159897990936049468232139844990954296346582200921635729280,-11159897990936049466460544357354451781628760157898178272714⟩,
  ⟨6157925402354649198394633156349934629936280855033212773460,6157925402354649199668703806912401436952361111206583061290⟩,
  ⟨-145460565052597188443539035189211745084591814447006768417119,-145460565052597188416854036467585364982214187680301330584591⟩,
  ⟨94532452423879345480306252040160256676595392357096893488245,94532452423879345490180382141893421089344063848606629378783⟩,
  ⟨149116321530304595671593189899072892266954348884087751696778,149116321530304595699876489108780417791529388626903034604146⟩,
  ⟨89435384882136523029454541502891070360790755422052421407528,89435384882136523041593524283502716905174092450342741678285⟩,
  ⟨-3704333654311157826398015027127130736383115987163528253184,-3704333654311157805057414103528950777591892080408591527507⟩,
  ⟨21124007349372729044366692017874105303136313307220085577310,21124007349372729056404499222528604474351072988401354624666⟩]
def bs1_1_1_15 : Fin 8 → RI := ![⟨-10266000653782817270555487753721931900557998799720713564537,-10266000653782817268751821328964429541530616194204352026528⟩,
  ⟨5648445398193408924223290512955015056296160148723774486914,5648445398193408925520425480401283743126920210512618722524⟩,
  ⟨-134507154410354231479505587150255404421767151277261081703646,-134507154410354231452337513752687498686844262021770449497805⟩,
  ⟨87197317055773639479316582716452438362736622044775441397203,87197317055773639489369462768655388453079408583900157982832⟩,
  ⟨137738789320012050375004229815573335620936436769675901837577,137738789320012050403799537504042222660608988079770396665339⟩,
  ⟨82844999672454872222818272052834632031637343269111714081073,82844999672454872235177005084729218502542049039918948646715⟩,
  ⟨-3676942872591862340520326443166943572696254904154298607988,-3676942872591862318793399704780930716566734527367012741068⟩,
  ⟨19953923889321615725732172631094981057539117602900495490190,19953923889321615737987898520128219880471604499388504009943⟩]
def bs1_1_1_16 : Fin 8 → RI := ![⟨-9410638265215549471442946974947856266413716299205291725213,-9410638265215549469606138958918752598738537102551440917285⟩,
  ⟨5163270994504165310242740432039556021636493455222049288945,5163270994504165311563709694075807569687537226222275369457⟩,
  ⟨-123914461107112523277869788074863663093354553312063512348868,-123914461107112523250202513066711909479817940826508513306485⟩,
  ⟨80138134256582552113342166232946550114322664019989946482413,80138134256582552123579763612740271828660360977759715086873⟩,
  ⟨126758720915232930954516948315109642767257949055516347699739,126758720915232930983841357341240194739746880929592908563391⟩,
  ⟨76449164315047380410423688589823388004998039234006515135281,76449164315047380423009508001590953008663837954080253545847⟩,
  ⟨-3617077881353885861192148638118465504780190040056075659730,-3617077881353885839065999008209472060593992434565858723004⟩,
  ⟨18762968370326790930084761115606797839894164311711977461250,18762968370326790942565680672691019666987154574545681743215⟩]
def bs1_1_1_17 : Fin 8 → RI := ![⟨-8594827433339861498641869531336130688918243586587715723653,-8594827433339861496770794435454569013073433157912469904370⟩,
  ⟨4702708059219584044085901720340905090986232371646907236044,4702708059219584045431514689712918038605165007225280533603⟩,
  ⟨-113710552586751792359680426584052225261704880398300680038000,-113710552586751792331496997076492520206061826969925863564816⟩,
  ⟨73369312001767983606974810421419580589133331169539656076319,73369312001767983617403398130037586499656339114970140053120⟩,
  ⟨116202540693079864561877195012527304501288937619544195582809,116202540693079864591748673660004652585578296611551753613394⟩,
  ⟨70267512681865101862364009706799909833080248996442830971214,70267512681865101875184627352871990139329144705518331215697⟩,
  ⟨-3527753614344381156741442616530976533550088849106367209248,-3527753614344381134202512484003404303812402772838903812797⟩,
  ⟨17560181432802783969438222383863324692350477352219047012066,17560181432802783982151983186924978119468934634289464417440⟩]
def bs1_1_1_18 : Fin 8 → RI := ![⟨-7819374385211639543103645171993923458803634329091395282929,-7819374385211639541197118764634198507626683499835459786044⟩,
  ⟨4266942669330795625888344700417109335355376049354643704853,4266942669330795627259453035851679999675495659468636579291⟩,
  ⟨-103920261353740906342387207731032514813985924231692776740318,-103920261353740906313669786006797794030154865248971614899692⟩,
  ⟨66903202549414375377827107184223235506430349938249490059903,66903202549414375388453285631989740058708462802441383129460⟩,
  ⟨106093343672927291427542847243262403478731656311325332217667,106093343672927291457980301621097075982409547927840915317547⟩,
  ⟨64317698809246133739312471202780654832665390159530555763895,64317698809246133752376001445280678417631845456519711673961⟩,
  ⟨-3412168275772902110637552663093719457933338969611531395178,-3412168275772902087671576799404697420896342006034679667224⟩,
  ⟨16354434270319606276439305003975448258419699077063608800483,16354434270319606289393953783825094453821960233848692889174⟩]
def bs1_1_1_19 : Fin 8 → RI := ![⟨-7084879613732920558983195401626202763692612606071827581545,-7084879613732920557039970438294563041953095154611178382680⟩,
  ⟨3856046352473532616689857916534510044370532858452102380979,3856046352473532618087358593449699533829978476465218103740⟩,
  ⟨-94565164783459539138891692821737965792344316729501781468447,-94565164783459539109621492020082754623100015947759114799745⟩,
  ⟨60750117141851085156500648274827812803506191553402597146079,60750117141851085167331369079361149872816059738809767224313⟩,
  ⟨96450896541816831364154854671697543221575146976136896209794,96450896541816831395178196881415989953536507396747662338530⟩,
  ⟨58615360596637045315993347658074276394410496422219132698680,58615360596637045329308336623671456259892712960485360674421⟩,
  ⟨-3273658403470450121760012240914812625595167529354493994596,-3273658403470450098351966365876342020969766680859737759275⟩,
  ⟨15154350602978887684837144681907258957917873092985248980839,15154350602978887698041156335244402033679619777071509027094⟩]
def bs1_1_1_20 : Fin 8 → RI := ![⟨-6391743653694761627941105490988427232785157213276525819591,-6391743653694761625959867041888222396468847302400212921276⟩,
  ⟨3469981851413961152116530685063737166815441982642016288630,3469981851413961153541369355823597702126322287492971046825⟩,
  ⟨-85663592539958899724645398355576358806940484214357386662388,-85663592539958899694802612092825616634310492067145881705033⟩,
  ⟨54918355735036863301027119433511099354074174541572253476333,54918355735036863312069711461915618748816183238304250079721⟩,
  ⟨87291665282063778141756947125453769635664882043563879619854,87291665282063778173387169855933339199163878398028276137332⟩,
  ⟨53174102619735557084858807065300405381918452363679487787318,53174102619735557098434264660761082799899758843590189152281⟩,
  ⟨-3115654562995367015275443440649119634789026295670753674167,-3115654562995366991409487938378934302448672432104911926969⟩,
  ⟨13968235163667397765155323858160756857499084307057143102511,13968235163667397778617633196283022976886622626976687862428⟩]
def bs1_1_1 : Fin 21 → Fin 8 → RI := ![bs1_1_1_0,bs1_1_1_1,bs1_1_1_2,bs1_1_1_3,bs1_1_1_4,bs1_1_1_5,bs1_1_1_6,bs1_1_1_7,bs1_1_1_8,bs1_1_1_9,bs1_1_1_10,bs1_1_1_11,bs1_1_1_12,bs1_1_1_13,bs1_1_1_14,bs1_1_1_15,bs1_1_1_16,bs1_1_1_17,bs1_1_1_18,bs1_1_1_19,bs1_1_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_2_0_0 : Fin 8 → RI := ![⟨-19161310605243970596138914178477271333449753394552133298562,-19161310605243970595347988481334459320489691444497830672045⟩,
  ⟨9938250019542961465016365256426227767440728224088244901397,9938250019542961465585171863017529452010501813708298315791⟩,
  ⟨-273735616716711908419479425147467262930460388010366657359482,-273735616716711908407565954287888134718455970697704029887172⟩,
  ⟨169072214849163758267170545538179038528093795652206100925157,169072214849163758271578833597273949734576245866150658480926⟩,
  ⟨274153343269704808297912775034566776608120432857364165913921,274153343269704808310539804342262791494795787088259531081143⟩,
  ⟨174220562142018446893851815261078551177969286543447843387994,174220562142018446899271242824410309901292650819235975302072⟩,
  ⟨-20495853512325440608433804533167029583977161789518125640042,-20495853512325440598906330692643259106621463100516657286882⟩,
  ⟨60320423906192361440541038454229555574770341473311591586808,60320423906192361445915296360235482668468035603890458420437⟩]
def bs1_2_0_1 : Fin 8 → RI := ![⟨-18592086968679229680408088752510811033665869811137566136369,-18592086968679229679607671419882871438364015301392824570991⟩,
  ⟨9658052427494265089081490433954766197050815487292667651768,9658052427494265089657123098910506888949976549375307926745⟩,
  ⟨-265043944291717674779374469796570343736942943229334802770041,-265043944291717674767318029346839319573085629315652466382534⟩,
  ⟨163961796881845010288043332010849049608857442315990975364536,163961796881845010292504522464602408280687606261400459599769⟩,
  ⟨265651328041175908851069428183534611834454202614718581355127,265651328041175908863847990258321344026335440824291380491745⟩,
  ⟨168521193872236343720132027632563905172598899403456712209006,168521193872236343725616491938491887231913364577473801589894⟩,
  ⟨-19330449869239408678824279800492133252667294020944458153565,-19330449869239408669182469924229052105710867857678117617573⟩,
  ⟨57688488022801402905333930077275313025328114699276956091594,57688488022801402910772682659873123688363720604386881036635⟩]
def bs1_2_0_2 : Fin 8 → RI := ![⟨-18003734400577307974719166142197155841566205918959923269335,-18003734400577307973908972992776661162114821227987415266077⟩,
  ⟨9368090936554446406088310657779835221764424884978244712477,9368090936554446406670973754539496556377393826399841884780⟩,
  ⟨-256086838296288124550943047369322934330165234642551198163564,-256086838296288124538739356793686617024599775796913994966251⟩,
  ⟨158675463529673225154212630705502549116575835161553565438632,158675463529673225158728307461314238155183083338040728848390⟩,
  ⟨256873098218571706167849410744169256690889413745679770562247,256873098218571706180784042504888598447078790608070923412343⟩,
  ⟨162659641751955628541322715286746535954455524179321602701506,162659641751955628546874163547273859295159081552595279263436⟩,
  ⟨-18177368525730664078302601006431746887562462712811414750199,-18177368525730664068543031852547650122133562319820939231034⟩,
  ⟨55038543760759884443254032782759292037903540253405502746633,55038543760759884448759211024396009540719106589719122547858⟩]
def bs1_2_0_3 : Fin 8 → RI := ![⟨-17397913925907474143026014235406661740594308610730098272430,-17397913925907474142205751937104070332166514788416445981580⟩,
  ⟨9069026073085017695274520054039539886900411677430943759474,9069026073085017695864424536970924137857148838888264008095⟩,
  ⟨-246892103829456574522396098290083685333570687795227674972564,-246892103829456574510040739217368160685736241419818980655752⟩,
  ⟨153229179840306829999782574706740150519900403784771270194206,153229179840306830004354372674631021082924412369994215650738⟩,
  ⟨247845596672582957246494869271333089177786477494995354696553,247845596672582957259590253727912844045039613718777198073282⟩,
  ⟨156654529819490292359423155778840327463142001206978869955942,156654529819490292365043597907183431231965066860033930658465⟩,
  ⟨-17040719306375373262090071100208811035801518854296420331576,-17040719306375373252209209196698629526376529282958861933046⟩,
  ⟨52379854950140668655889517789659105384935006700023268873649,52379854950140668661463114851395109089521140378689611211286⟩]
def bs1_2_0_4 : Fin 8 → RI := ![⟨-16776386652804471836428120852723707021153337051510033785057,-16776386652804471835597486491288170076747717714729945788878⟩,
  ⟨8761574609775053724533744359541403560985853760544574423148,8761574609775053725131108074173738576878471074417646017337⟩,
  ⟨-237489010300003946616882377889666465387620578547151279295135,-237489010300003946604370787615545006413399894235312411607262⟩,
  ⟨147639881147073919347063472243060767969123592461356089327290,147639881147073919351693079739999308521188951452661848994817⟩,
  ⟨238597296858982698873009165695042959012248025012339771511287,238597296858982698886270138835411421564048438193846564545092⟩,
  ⟨150525376295366836227114383987287630058183003286123592796435,150525376295366836232805895553689065058099205492038539910328⟩,
  ⟨-15924476144770255760183197878396999096918263927926984240026,-15924476144770255750177394326747874614324253041422246120314⟩,
  ⟨49721717167785953340297156764040330669476141695472818988559,49721717167785953345941230916726135902277570425090397323521⟩]
def bs1_2_0_5 : Fin 8 → RI := ![⟨-16141007366734313183608917813877043827382683364195217358639,-16141007366734313182767598431857400184518754670892305550161⟩,
  ⟨8446508605076850095308301791625117786571435281012962877327,8446508605076850095913349806212480524090726686715852622232⟩,
  ⟨-227908156541022199163104488566576799951074610777980673822766,-227908156541022199150431953109080929678965484702296106740855⟩,
  ⟨141925402236767063189365389215528636886096175163266454912520,141925402236767063194054550535068993754300203688588380206489⟩,
  ⟨229158077343541871149398912776421512098657936257261136961998,229158077343541871162830470926937219973761579859339250632810⟩,
  ⟨144292497366587879495683253845991279069369509362730568153401,144292497366587879501447979236761707256373591405375593038010⟩,
  ⟨-14832444135211621335825819927167892498981496708711914649564,-14832444135211621325691304848693297104667210568071531628031⟩,
  ⟨47073392551235982871239606043237462409928477034518422763754,47073392551235982876956283800225841273720963267104314059775⟩]
def bs1_2_0_6 : Fin 8 → RI := ![⟨-15493717284436878834511426841167075807471146338947975733994,-15493717284436878833659098945475210449846656493340997622570⟩,
  ⟨8124653960274809622305743359958143532417226773808913385545,8124653960274809622918708319622985635383476744327182798337⟩,
  ⟨-218181320814900707758451234651930852512820754862323883143177,-218181320814900707745612881334028454197052931154042649162981⟩,
  ⟨136104397194995881549174786840314102057925099185419430578000,136104397194995881553925304997231354226500269041929020753285⟩,
  ⟨219559080993220109508585083301199880989076768872289855402451,219559080993220109522192390988340682994702038410864205751725⟩,
  ⟨137976901238502269659483129210777996696038473691217731802946,137976901238502269665323285002474980984754145414142313544808⟩,
  ⟨-13768227531928475660385615661798434957583335769537142977990,-13768227531928475650118492265757042846748415281627569115483⟩,
  ⟨44444043182459930673123996698857990885360583983604225077413,44444043182459930678915476162059768351971884812241592887733⟩]
def bs1_2_0_7 : Fin 8 → RI := ![⟨-14836535988592974650835134201623900917026893051517652835215,-14836535988592974649971463237770857210723961351537763248957⟩,
  ⟨7796888470031859710506101283743596248378036049693167972194,7796888470031859711127223788588080906082919079195854359220⟩,
  ⟨-208341296378671462963366009874307577634303497616392341499381,-208341296378671462950356799404482930185032107244634711135902⟩,
  ⟨130196250205906437015313078181647034304886922304579238432389,130196250205906437020126817842324558948142025865474268465671⟩,
  ⟨209832559381816134761175837412947221195921723808391103661094,209832559381816134774964235757064641897550092388335047315034⟩,
  ⟨131600173010669183299167078377630438914002236711034830205400,131600173010669183305084956939595722202237331809896443113488⟩,
  ⟨-12735199147764660233633267837031791064428479939790892728992,-12735199147764660223229506087287063033404892279843766041789⟩,
  ⟨41842663753075919776006415010751125855889058261159442919668,41842663753075919781874969443146150259227133778523751411860⟩]
def bs1_2_0_8 : Fin 8 → RI := ![⟨-14171552573510823449254963687985981671313850829610938479386,-14171552573510823448379603478849142935088269121056055718335⟩,
  ⟨7464139347353644530994959237274114481361189929733649905283,7464139347353644531624488245999490455695565403488514089127⟩,
  ⟨-198421713490308549960869281838652161399992398019569604380193,-198421713490308549947683999857228365673650260765336481743149⟩,
  ⟨124220977703101684917111186618732076692783991044347795882787,124220977703101684921990077229237855914629256781880174741574⟩,
  ⟨200011703163733077492769068462226655997959386996102776088397,200011703163733077506744084137557278990924575027391659027148⟩,
  ⟨125184351078807918911557079688534384987905643597759722689442,125184351078807918917555053028464492633327126639014806992473⟩,
  ⟨-11736471607882418032438481116043041863046571885640465481528,-11736471607882418021893910970464838460767256156908736091230⟩,
  ⟨39278014273728448715416379886375275914372806999941849009106,39278014273728448721364361525531086740573819597525041919500⟩]
def bs1_2_0_9 : Fin 8 → RI := ![⟨-13500916041710185939254940010720210073202789639332259479598,-13500916041710185938367532157465095025602795215532032170053⟩,
  ⟨7127380209870124517052392370751127724682954065482305954402,7127380209870124517690585631494205719087656365806914116376⟩,
  ⟨-188456848950571186951822081275515674051802990188028160745229,-188456848950571186938455329330923651320456451622271483315627⟩,
  ⟨118199122391946762731045154855881471066725153988956400840790,118199122391946762735991193980978705705347813255556357370437⟩,
  ⟨190130459379926787353636995197268035034122068319149806783184,190130459379926787367804349996141717498159823444998421105215⟩,
  ⟨118751795911336824991284690140156053839416603730521521542849,118751795911336824997365214008989706497312279825523533911630⟩,
  ⟨-10774870909008641455168941641220792173874889612525807168265,-10774870909008641444479245835202284527690101907424546643701⟩,
  ⟨36758553631404794204931161858554509923136967828569659016839,36758553631404794210961005987300470723640773469197420347708⟩]
def bs1_2_0_10 : Fin 8 → RI := ![⟨-12826825000969932398154941265522030011178200656192297192866,-12826825000969932397255114508041971003835878382326360194860⟩,
  ⟨6787627521108539165188327452407169871793974799098539789608,6787627521108539165835451962690147714476135410408834879512⟩,
  ⟨-178481424488772561051237104033845344828671076638634608177441,-178481424488772561037683289949123136818521622072469312010989⟩,
  ⟨112151639788245666629239703892593113875778087862761931051791,112151639788245666634254960780381177433862379257682903968303⟩,
  ⟨180223336872183348678256571939553053891030450051450851290093,180223336872183348692622192982893052794204847944372559319128⟩,
  ⟨112325052193467156438111523966221440299177063119663155768950,112325052193467156444277142240410674216586693429877590022616⟩,
  ⟨-9852912720233398695445520009643548951842814254233597085243,-9852912720233398684606226351971421610408823919224863672745⟩,
  ⟨34292374827866721485617223616088061465674424304168239408366,34292374827866721491731452908261271595202084782151942969487⟩]
def bs1_2_0_11 : Fin 8 → RI := ![⟨-12151516721050564304431338835107711652866262759336084118726,-12151516721050564303518708369055633334560769169827525442538⟩,
  ⟨6445936487941045329375120891181373185302260073767619750655,6445936487941045330031453389079132044660713358195777518029⟩,
  ⟨-168530395510521132691968989049498029352735974300204196451393,-168530395510521132678222316634950238816031748773603805208201⟩,
  ⟨106099778042425169469787025775133009379695438961121801462087,106099778042425169474873645163625825640894918088385152500647⟩,
  ⟨170325201191935854796537448172030362148399850356460504581596,170325201191935854811107478812855119568776735041013282193175⟩,
  ⟨105926705471414252860417599144006240625220445040264549667507,105926705471414252866670948505218713469972724894796713704927⟩,
  ⟨-8972781836864966141433704140514605914355886019774994575442,-8972781836864966130440177286348640770384762852395063895655⟩,
  ⟨31887142748306909751964818226573537052077871694436590013401,31887142748306909758166047387716909233694254962166082724627⟩]
def bs1_2_0_12 : Fin 8 → RI := ![⟨-11477255618747613086229824896506610245842972654823896834000,-11477255618747613085303991643671489629414988658920056797761⟩,
  ⟨6103396423521657861992428983467730574983927143463462252629,6103396423521657862658256472328034477193568911716886064631⟩,
  ⟨-158638731926754277107956189729644993698568193131998635549494,-158638731926754277094010647792747490067772375995433356372659⟩,
  ⟨100064951939543179878311437096894099836136400397840747596250,100064951939543179883471643280635695623054591441284821208329⟩,
  ⟨160471060593844840472287802810773447224511682596575460739419,160471060593844840487068614282544671298436944877849067276163⟩,
  ⟨99579234560892552067056563279460859960991711454357935586550,99579234560892552073400378213964676655143143935259525737437⟩,
  ⟨-8136315164063277682649013879345582614769083710308995630624,-8136315164063277671496446541189284573599703419558754951960⟩,
  ⟨29550035310252287783126955054654093129665676186552537111197,29550035310252287789417895779732471608251374545762133699031⟩]
def bs1_2_0_13 : Fin 8 → RI := ![⟨-10806321249005451906791817305827040148219340618253315271615,-10806321249005451905852367134248967461257284699063191458882⟩,
  ⟨5761125593633805896604652837279385156504392683804966466049,5761125593633805897280273146589353177510686142031366857487⟩,
  ⟨-148841192971747540410760820097162594913954022855055138493452,-148841192971747540396610170695395200193411968975789190202704⟩,
  ⟨94068612081169416322167960489673513555197744425314403911689,94068612081169416327404061666489527344208965997556646569302⟩,
  ⟨150695844898009736883254927736811128070252796408023889239119,150695844898009736898253131604198793287909888349987012401839⟩,
  ⟨93304861104400687660389557866149313130902521286429066054311,93304861104400687666826676008589257511549716856403364887244⟩,
  ⟨-7344988561929800772298620619886601028141549694628087836937,-7344988561929800760982024173110096322581238458931911583238⟩,
  ⟨27287688827337795354515780381954361219083148648146959100979,27287688827337795360899246654591623497490895771588443187353⟩]
def bs1_2_0_14 : Fin 8 → RI := ![⟨-10140995888347417688426715307321857427262653366146277639348,-10140995888347417687473218197138751342242284884136811272450⟩,
  ⟨5420265573273322647157753012050307823427706493532888229225,5420265573273322647843475397330817237274316054431390482856⟩,
  ⟨-139172098088563389848469579237761661074575366989701357809669,-139172098088563389834107345114013412917847803199340678715817⟩,
  ⟨88132110362867306743773375648031754449580053749064709754836,88132110362867306749087768568249939292162416752136869581881⟩,
  ⟨141034179183431632901498926038381117324983248021297239913549,141034179183431632916721387514415779758325844298525517430795⟩,
  ⟨87125397767542735539045907796772224790430789364540692037171,87125397767542735545579275645793017662948637361139789371401⟩,
  ⟨-6599907828782734477501751173939364662022014500575058676560,-6599907828782734466015945608586982139830275558831868758767⟩,
  ⟨25106148389925272848899426073077742777493505456718472025039,25106148389925272855378339833541669274717278833693414528584⟩]
def bs1_2_0_15 : Fin 8 → RI := ![⟨-9483551804678098337992713183445328653405130812235392649076,-9483551804678098337024722334015236811775433183600266038009⟩,
  ⟨5081975149285312743230480083876655501777268131122507795279,5081975149285312743926625868809327779607588052037889209340⟩,
  ⟨-129665096108896619644280944993891296363939326757040026732860,-129665096108896619629700396127317888275096322124808752114868⟩,
  ⟨82276562957986308622443389470250515397931474208509308242122,82276562957986308627838564413226496028059537538643973599176⟩,
  ⟨131520154434606248800785287933433551051607080068328010164705,131520154434606248816239140134186561241192493031175142263625⟩,
  ⟨81062096652469453099473334478733283702389323824317899887306,81062096652469453106106013514982879131000906691715680331865⟩,
  ⟨-5901804035221236427737132804664091676700608048689584878181,-5901804035221236416076735969868915288692722308811811039152⟩,
  ⟨23010824014139549540798817491959603761164840967286931110143,23010824014139549547376214704173041669098525719934963955907⟩]
def bs1_2_0_16 : Fin 8 → RI := ![⟨-8836238314410091327611144749073300939371355942415415203343,-8836238314410091326628195622411747745849399479666895020198⟩,
  ⟨4747423813728588623867874046920274310055584008208221614862,4747423813728588624574777311274492604388713009756965832093⟩,
  ⟨-120352935075885861040021153295104189374310009688815860607018,-120352935075885861025215292492718527290007934053322219019481⟩,
  ⟨76522712102125332544559521194934658209888821055716501951762,76522712102125332550038067300530900467365112472047610540842⟩,
  ⟨122187097398331232740696480906533693528403652849970055122019,122187097398331232756389140122519672932639277629756269065812⟩,
  ⟨75135499573300860768592649166479050361172822543254763474722,75135499573300860775327822406981606203694095696519903469854⟩,
  ⟨-5251033349399436202571148941366549951042811972639468585842,-5251033349399436190730565022617408754778432632455706240302⟩,
  ⟨21006453242742542628514593378967279612605383691132262568816,21006453242742542635193630530251941229169005211034725455065⟩]
def bs1_2_0_17 : Fin 8 → RI := ![⟨-8201268733690734072722234466262645987740250160502565066668,-8201268733690734071723843761266347893232736093890817158078⟩,
  ⟨4417784901116724422429656609417135807612210625320359860229,4417784901116724423147664926753130602520251424681350177303⟩,
  ⟨-111267235148866707189048892320278037673551765587812943346316,-111267235148866707174010439765997107374897493750533255171341⟩,
  ⟨70890788040429944253614570686217727574468156305781963625769,70890788040429944259179181672050262111866055309690054484027⟩,
  ⟨113067342014596575505764597632933067681747469844474484238886,113067342014596575521703779705499326329267828445110933633205⟩,
  ⟨69365291881214690596570334896382032155522424891584679479241,69365291881214690603411313923163101549356917301054212705792⟩,
  ⟨-4647581415194271794871724689610231295622933561424027877608,-4647581415194271782845131852272769969430705839972683003479⟩,
  ⟨19097070795938888847243117060240882946261615938843313256015,19097070795938888854027078131360582955058830303756118565320⟩]
def bs1_2_0_18 : Fin 8 → RI := ![⟨-7580807335097471046942454723230914092055151435840137636366,-7580807335097471045928119274517556174960896137917941960967⟩,
  ⟨4094228430536465062271600234289740487384675911016959345891,4094228430536465063001075463875215779120489886284269760793⟩,
  ⟨-102438267084351802796231635448950993734372539256827353347331,-102438267084351802780953012117157612003456090424757528406367⟩,
  ⟨65400372549515343551007122784614868596291916821135058547078,65400372549515343556660603083458467293754950041596605932146⟩,
  ⟨104192004859773857653478063917357627079310895523572669340418,104192004859773857669671801818568685014240060947205758892609⟩,
  ⟨63770161543249207940161549225307431638571693268237672742242,63770161543249207947111781730550350109244059918473885671067⟩,
  ⟨-4091072261523370562720394033974094832419388088530354646884,-4091072261523370550501731158738549860727881782881719087147⟩,
  ⟨17285985768879455632592334186015776660816078746436085423105,17285985768879455639484638133445697584254820685942518562500⟩]
def bs1_2_0_19 : Fin 8 → RI := ![⟨-6976956424395558536397519597269819351389056976737333268697,-6976956424395558535366715191736869549768373191083318303082⟩,
  ⟨3777913720637982932809867051403176707310783775749028597188,3777913720637982933551186189303579324555973559504080829683⟩,
  ⟨-93894738804450179540655779971114994212223513100847850296726,-93894738804450179525129089800846694782533099718739085094893⟩,
  ⟨60070265475230092756625105309691584384122454438361084785241,60070265475230092762370376665484506164291361285517771053081⟩,
  ⟨95590767078723608390023119513130305783505518278639233899961,95590767078723608406479782239257633735719779245156353622881⟩,
  ⟨58367665166781290600613512808926494534832929876850172395721,58367665166781290607676590703918409733113346888969301889611⟩,
  ⟨-3580781635119470045100357678636068807076756636249516545299,-3580781635119470032683310105810352734082886982059859901419⟩,
  ⟨15575766757089297721622013662260397118102317210464634286306,15575766757089297728626222459546941758664362843206758563884⟩]
def bs1_2_0_20 : Fin 8 → RI := ![⟨-6391743653694763448928639802074407119514883084523831587779,-6391743653694763447880819905454345644132269705908517234977⟩,
  ⟨3469981851414359198288677987063895465107782812716418229207,3469981851414359199042234081960172465566550932808202375882⟩,
  ⟨-85663592539958970957328438704403644885972493047302325223293,-85663592539958970941545449417845208735007450504495973359360⟩,
  ⟨54918355735036903428542639514317017724410046335205669928587,54918355735036903434382748079807981979306753557537491593435⟩,
  ⟨87291665282063843285664914156548397822143277822682177618564,87291665282063843302393227058456073941216726003992780922009⟩,
  ⟨53174102619735613626296277915602024606532088629948505204812,53174102619735613633475946056385023716807373453338925714440⟩,
  ⟨-3115654562995419003233773173605827383980028054817857709078,-3115654562995418990611757363227377983145507756851605648823⟩,
  ⟨13968235163667368605583011558209313130334864936976032572912,13968235163667368612702838848894961001410834360366566611551⟩]
def bs1_2_0 : Fin 21 → Fin 8 → RI := ![bs1_2_0_0,bs1_2_0_1,bs1_2_0_2,bs1_2_0_3,bs1_2_0_4,bs1_2_0_5,bs1_2_0_6,bs1_2_0_7,bs1_2_0_8,bs1_2_0_9,bs1_2_0_10,bs1_2_0_11,bs1_2_0_12,bs1_2_0_13,bs1_2_0_14,bs1_2_0_15,bs1_2_0_16,bs1_2_0_17,bs1_2_0_18,bs1_2_0_19,bs1_2_0_20]
def bs1_2_1_0 : Fin 8 → RI := ![⟨-19161310605243970596138914178477271333449753394552133298560,-19161310605243970595347988481334459320489691444497830672045⟩,
  ⟨9938250019542961465016365256426227767440728224088244901399,9938250019542961465585171863017529452010501813708298315791⟩,
  ⟨-273735616716711908419479425147467262930460388010366657359480,-273735616716711908407565954287888134718455970697704029887172⟩,
  ⟨169072214849163758267170545538179038528093795652206100925155,169072214849163758271578833597273949734576245866150658480926⟩,
  ⟨274153343269704808297912775034566776608120432857364165913919,274153343269704808310539804342262791494795787088259531081143⟩,
  ⟨174220562142018446893851815261078551177969286543447843387992,174220562142018446899271242824410309901292650819235975302072⟩,
  ⟨-20495853512325440608433804533167029583977161789518125640044,-20495853512325440598906330692643259106621463100516657286882⟩,
  ⟨60320423906192361440541038454229555574770341473311591586808,60320423906192361445915296360235482668468035603890458420437⟩]
def bs1_2_1_1 : Fin 8 → RI := ![⟨-20868981514938193343359865362832034979826781823867151601724,-20868981514938193342540464759233840219841342194741532158626⟩,
  ⟨10778842795689050592800511548747295456622304017087216068536,10778842795689050593389796330431914163180240024095030064678⟩,
  ⟨-299810633991694609340223199970613708366571412156521347873394,-299810633991694609327880820340578892299008305040799593655498⟩,
  ⟨184403468751120002204393478936193662889759714466456697568624,184403468751120002208960474179263916492285305874796035162789⟩,
  ⟨299659388955291506637988217286391119013501471649268617682112,299659388955291506651069844895359285815794477816196284757525⟩,
  ⟨191318666951364756414816067918833819186107145268734364524525,191318666951364756420430605709954247917403812239209368839036⟩,
  ⟨-23992064441583536397605386838409650586708947518033744647971,-23992064441583536387734904890667948100551066406237659746316⟩,
  ⟨68216231556365237045968879555316632515083286471822323738211,68216231556365237051536621491098210316794715925994364906080⟩]
def bs1_2_1_2 : Fin 8 → RI := ![⟨-22404492040797788980957941888062044595361787474314488561313,-22404492040797788980107508746241619572081331572281604810469⟩,
  ⟨11531560481815038957059913257737138501735579020416576028713,11531560481815038957671515575470408948741461106699480937295⟩,
  ⟨-323496749132759460966028771106605741883340062050910288233990,-323496749132759460953218957884334663251521030153712986219017⟩,
  ⟨198151484189398911749285022332059683094018348916706734924546,198151484189398911754024979925704225205451416015955625012648⟩,
  ⟨322679503294200475850673624243216748089795482803634033343523,322679503294200475864250682423034097139626432973862280023875⟩,
  ⟨206957117106223557889974598120864578279288111236725080704444,206957117106223557895801771047801738527140002611135624847485⟩,
  ⟨-27599176067037218148567582591182861285286061390514980403911,-27599176067037218138323283359287882250480277056790913750674⟩,
  ⟨75949963798683073309541620398347703513555102423801695241892,75949963798683073315320225205928141457258705111620641446946⟩]
def bs1_2_1_3 : Fin 8 → RI := ![⟨-23722994508652503582178957852784770488595820114253377121834,-23722994508652503581294687469858185824233893473923922103277⟩,
  ⟨12178568866160095018376651292602263446541882993204501690543,12178568866160095019012588192404177585085073033800523682983⟩,
  ⟨-344043224466006910015204468654113755936844893178613622970711,-344043224466006910001884975461471880743021656315724758899876⟩,
  ⟨209885204877222954281032205370794392569602846607041978546257,209885204877222954285960757552378312220485977200939653767983⟩,
  ⟨342486228777781276983427094464439853060630479782626380678847,342486228777781276997544359944003019456560548953071745525819⟩,
  ⟨220633063572117094265345218943636289652260026330714888862047,220633063572117094271404244847177915361224532864733155885255⟩,
  ⟨-31206223125129991570348188375798099676559967914590858151746,-31206223125129991559696286469483666783660118344385946955937⟩,
  ⟨83271497221178579988376959248366609242538225221584143154007,83271497221178579994385484592329731234023511923966280356456⟩]
def bs1_2_1_4 : Fin 8 → RI := ![⟨-24787747980735557179063941905453489831798523572478024446199,-24787747980735557178142747565705099735464771397604411127834⟩,
  ⟨12706589689495948818463267026772061014668579178814368272224,12706589689495948819125758368608767902513561548804371149181⟩,
  ⟨-360817931407093419136021630134680802361610336505303884524994,-360817931407093419122145962720863679718067672387899937262986⟩,
  ⟨219252167667057655623522244353177439958168544208150846578435,219252167667057655628656595181292162209465838880790891854493⟩,
  ⟨358476085289048133892365171896968832205754288347483771418384,358476085289048133907071923704575014678022533564481978964017⟩,
  ⟨231916086073780922592168086645120194513439161998455308358769,231916086073780922598480115719649718911822923951756580276114⟩,
  ⟨-34691233182970161428766593411976164801373121559247242832042,-34691233182970161417669906320506848884539234924878554882803⟩,
  ⟨89933279900200617672549230584542341654219457210842807260158,89933279900200617678808650377351755776437577560387659141358⟩]
def bs1_2_1_5 : Fin 8 → RI := ![⟨-25571674873395825585936396309116219112488852086417857593609,-25571674873395825584974867134949668510362391870142561623414⟩,
  ⟨13107134062261914171221865737983173431430587743584073248530,13107134062261914171913364507915898037102771674546151154708⟩,
  ⟨-373340127622317668147018893874131831387015209089089540364214,-373340127622317668132535675237485268187566163426062352657097⟩,
  ⟨225995714776473235926501947599006410119076076340573215721672,225995714776473235931861107874588304820225750058209544161509⟩,
  ⟨370200060548183415879448115014865577748838548179445808922089,370200060548183415894798807382480366295610882135505975783068⟩,
  ⟨240471573519107109781358650347715009177494070940461540556698,240471573519107109787947053946745388798835801993395089561143⟩,
  ⟨-37929233080324802037707262408177378874295609962956339123069,-37929233080324802026124702773816349892732520628885703907101⟩,
  ⟨95706171615737331901429289651109839220543969986107446153271,95706171615737331907962780451515955608996669375942295666848⟩]
def bs1_2_1_6 : Fin 8 → RI := ![⟨-26058305052101999532897175176933776063102941110469824503161,-26058305052101999531891525505614857992258549286902336363811⟩,
  ⟨13376384236323148240338433217412533344670973962633052144364,13376384236323148241061661934106048948390722815061943948272⟩,
  ⟨-381302219308037008221705743368556347944112325862957860489344,-381302219308037008206557951234001885944002065145057080122711⟩,
  ⟨229965409953618006100984298824328915390179841366917095011312,229965409953618006106589368243459415004817538855403516686079⟩,
  ⟨377382922272638947111419920633932567350598291290597654745578,377382922272638947127474991191125444458338101465231576319928⟩,
  ⟨246077009508227092233163240575847081531686943457648349764942,246077009508227092240053958082879161025854792353294947562406⟩,
  ⟨-40800946138529676209188496317675200809754787008706896871145,-40800946138529676197074462129024073910330082281100514473875⟩,
  ⟨100394241452522011672276353510370190640676146302113584758390,100394241452522011679109638503180822754037439712276988260367⟩]
def bs1_2_1_7 : Fin 8 → RI := ![⟨-26242061591227966441322588205986578936941615796658123714583,-26242061591227966440268596805868541615834908808141960822470⟩,
  ⟨13514776559861569588239378216696723155570768912825086775406,13514776559861569588997372645023201495989421376428458634577⟩,
  ⟨-384579043438672517937659765852567705136664292826150111341787,-384579043438672517921783817104272809055582470408725472110973⟩,
  ⟨231120053200907886438187136904403892789473215876061229016382,231120053200907886444061642841572355984849036495138869430364⟩,
  ⟨379930153172487727484189788147234534677811359987049045927658,379930153172487727501016628326499623337762034630039111275510⟩,
  ⟨248629946108294657952159723920282475688316548593445638772783,248629946108294657959381679239589922617068797166168431358926⟩,
  ⟨-43201191842025053343004795001720647948663787994486853916122,-43201191842025053330308437393684778170474205415933172259029⟩,
  ⟨103846966327524855665735336474228762067901690704237242725913,103846966327524855672897098489740415169507489087508299175868⟩]
def bs1_2_1_8 : Fin 8 → RI := ![⟨-26127903713929717284953600150768309903332983644355952680205,-26127903713929717283846537038141030044042757973213803400654⟩,
  ⟨13526371878376700907599488481123433134001178497420925958807,13526371878376700908395650262971897881883933967808667462212⟩,
  ⟨-383224586971182800506416080016118933403991331609064533481752,-383224586971182800489740728362172659312541570812948144617071⟩,
  ⟨229523476160795890290762461248984885378296189740586631604950,229523476160795890296932766649272808455286463188943533779034⟩,
  ⟨377922657996297990368152255499550601914094489742097333765137,377922657996297990385826378896108470897507717298414403230164⟩,
  ⟨248147405039859754760645228128081447830703657895921759031850,248147405039859754768230831136094570049756654410295937154146⟩,
  ⟨-45046023825817749435206475896799804848363486810678989338397,-45046023825817749421870817587936984751815372211446417665844⟩,
  ⟨105967608472744870733546812392450085600690226125863367217587,105967608472744870741069191178351302274668878921605736319234⟩]
def bs1_2_1_9 : Fin 8 → RI := ![⟨-25730399112272977901459633028033673485416049828757480192379,-25730399112272977900294170912678569721442584046435740451374⟩,
  ⟨13418116083996909460048857690140839286674533395952597710471,13418116083996909460887018029733703125988458140583358727263⟩,
  ⟨-377457376504179378533319851575079498310220142695060549196294,-377457376504179378515764853679083661093053471692359849096526⟩,
  ⟨225334022319489386632934105369688765391601233109099892815944,225334022319489386639429902314100335527233058789828950441337⟩,
  ⟨371600642667824830820068233390141517679554004870679850238384,371600642667824830838674689522521293118672675090800348967290⟩,
  ⟨244757387459715659791368062290027916888821236265121347155907,244757387459715659799353815610917016833297836815712171221655⟩,
  ⟨-46277837934019746454983974212411499339587581606333304763630,-46277837934019746440944842780002626328919029977611363073534⟩,
  ⟨106717078622294330190338120480528128761150266616361953507684,106717078622294330198257314420149660304358227931650515917538⟩]
def bs1_2_1_10 : Fin 8 → RI := ![⟨-25072342126135408800442813015058659589696074058405552637866,-25072342126135408799212919418007666744217236366366982457510⟩,
  ⟨13199090094627832802004661674962361820300775918999722877027,13199090094627832802889158924059214769470283269152740835812⟩,
  ⟨-367636814030862458779806763000581326081647537976313730856921,-367636814030862458761281253484587514046128151619056428328811⟩,
  ⟨218789162314911095960785786360272664569502450019515401913208,218789162314911095967640697356092367425002744066608291845526⟩,
  ⟨361339025644004865659306398528140081803953098967721112492151,361339025644004865678941495164593758302330605219926672689160⟩,
  ⟨238683944749040731268168830783616486316338585409138238269129,238683944749040731276596068999047762464247704281295542061855⟩,
  ⟨-46868006628931126743717667636076095078044871961792614099479,-46868006628931126728902395968984200880488829279284842151285⟩,
  ⟨106113205331569434236265991021413057978275086440793981573108,106113205331569434244622990182342537358699930423324027522003⟩]
def bs1_2_1_11 : Fin 8 → RI := ![⟨-24183061004719839399012192243321697163109751356800713221692,-24183061004719839397710996988395274101019143348263369362011⟩,
  ⟨12879827959685320994922471172944925918033727226048566414663,12879827959685320995858246126378941646011697207521650959598⟩,
  ⟨-354233363005592799829131645893502815345254048942269618664354,-354233363005592799809532141403746347700572881892604256985344⟩,
  ⟨210186996083574491621025403576881663148620497019769345455961,210186996083574491628277720104257497803322927034098671166521⟩,
  ⟨347617288984084376188334433253164939110692137096689718633301,347617288984084376209107851892603327733620793300692020257227⟩,
  ⟨230227752193459790833976478457933626436462271796954371210631,230227752193459790842892276055837385566090416937245678464061⟩,
  ⟨-46816970691446054454072547265731909651058583077991039571071,-46816970691446054438398377370336334519332434247794606939819⟩,
  ⟨104225901193366336653351558184229212260060643315410686738873,104225901193366336662193044699537675453410312672083183491957⟩]
def bs1_2_1_12 : Fin 8 → RI := ![⟨-23096565231864682838996452640072275488582490771819611601859,-23096565231864682837616083563069681020584361937500552345031⟩,
  ⟨12471751348732341677481924781783198314703610467414176452681,12471751348732341678474638829770834235813168287300760957741⟩,
  ⟨-337795664930683641516961901819719469148976196874086509081775,-337795664930683641496169826364610655172834819079528593366846⟩,
  ⟨199866438055881493810042824936808681710570729198285313644331,199866438055881493817736423136809768309554565294663133244086⟩,
  ⟨330986786283008181470275276135044797090164706139991578139231,330986786283008181492312694889159249173333677051511963162269⟩,
  ⟨219744296270752767684161236560654302148070045230209010634524,219744296270752767693619533656828593941694654978308627289593⟩,
  ⟨-46152057501364876306084929286618679378260040782778541246661,-46152057501364876289457033243276235599760589242977876555858⟩,
  ⟨101169137369150432155264878561190778384647487559554842841356,101169137369150432164644342968408604512587269402533968749846⟩]
def bs1_2_1_13 : Fin 8 → RI := ![⟨-21849674765712040234529066571662389172828618606809901393114,-21849674765712040233060443677456040826861843919929821290540⟩,
  ⟨11986737055556983408685297740941606041142052067710764170411,11986737055556983409741480904233063622026929680424418015332⟩,
  ⟨-318917447382035431477533422136237578630394850798413588037017,-318917447382035431455412006537893901715099170685211755099645⟩,
  ⟨188187709105010434240149860575206701651999049282538938925442,188187709105010434248335348531833514986904708512570777818239⟩,
  ⟨312038261542196559717008296588395604208642720092743814461741,312038261542196559740454676437767030312704422826616648307756⟩,
  ⟨207621667896449079122807619018322187286464846442906626716428,207621667896449079132870631793244468199332589097486236768049⟩,
  ⟨-44923533907569661483693666522980502830644804568888638257727,-44923533907569661466002666906838409935250232843405418622690⟩,
  ⟨97090856222343936000965464534592798856324227565899841157987,97090856222343936010944604456858528560586936354659426167010⟩]
def bs1_2_1_14 : Fin 8 → RI := ![⟨-20480251502533261456569856828125983170161357484892353418961,-20480251502533261455002431386065421821866346640503793235127⟩,
  ⟨11436807944877494831451570996060667373571654391796059193179,11436807944877494832578809559567630791432982802807228490336⟩,
  ⟨-298206588274511485736475675930442973275155162888925745153139,-298206588274511485712866027898889729880133560874887634984136⟩,
  ⟨175514440914870629207097846060108852023413847401807938420386,175514440914870629215834017973068777380463907799941063492889⟩,
  ⟨291371816624988846475499478403115812302756434460467182820996,291371816624988846500523228506288390584545500552838487735872⟩,
  ⟨194259629720156482209123388627890189065866709963746691435869,194259629720156482219863397046558631799344045842123737897123⟩,
  ⟨-43199517801968477702967371624846309834182648259132898040778,-43199517801968477684086198654724181909566180711159571151735⟩,
  ⟨92161974509018836114924239860382110097430229063185923062487,92161974509018836125574732826054438352415295334926831272366⟩]
def bs1_2_1_15 : Fin 8 → RI := ![⟨-19025624603041856033918591801707824301354795279830846174585,-19025624603041856032240011420129925804663063287624558082158⟩,
  ⟨10833920716659360317919287386557124799689770576856548015160,10833920716659360319126464766265900796807664194176865549869⟩,
  ⟨-276258062063355637386753909235580570552655577384517228113121,-276258062063355637361469968488962618529029880660950013624548⟩,
  ⟨162198312057262451198538622066466759549175039677032799138630,162198312057262451207894324985361605584095830038240051124302⟩,
  ⟨269570925418307653030885280621911854319172049590760237668448,269570925418307653057683605358729494397934525051106312851337⟩,
  ⟨180051190683172284200248210851851622463417176953489521563015,180051190683172284211749853575230119148338385802102612853459⟩,
  ⟨-41060377456057724680934370150728244759168338171237885891899,-41060377456057724660714227183915745668305202276776879600932⟩,
  ⟨86565501850806549030461578980665627724416252699754782071006,86565501850806549041867358207214792474877474601102209328913⟩]
def bs1_2_1_16 : Fin 8 → RI := ![⟨-17521270391483760632188900893410204362685118207234614748523,-17521270391483760630384573510382071069124301831416531717795⟩,
  ⟨10189817600427236884095171251223593374705930811515182410523,10189817600427236885392781557083163244726374690451475037646⟩,
  ⟨-253631828495006082092650666830502208014475598778823996688902,-253631828495006082065472637621553972933091813816342936729469⟩,
  ⟨148566745832867006035961224079529336344061624924977465274892,148566745832867006046017788036559900439624471677809853910704⟩,
  ⟨247181441508854258735694604390271837574559498807448392370936,247181441508854258764500464194851541836935718846335657261076⟩,
  ⟨165367460313667248292618892253727035966974763295551779735874,165367460313667248304982154176764346548584792933181920244568⟩,
  ⟨-38593170688957926769693780929284844709087406948290756594579,-38593170688957926747958892303465653549522543802064155169001⟩,
  ⟨80486579859734482463287788331872254387709420847440162662806,80486579859734482475548005363463820508690884426208463156347⟩]
def bs1_2_1_17 : Fin 8 → RI := ![⟨-15999778165039979950233374502128679658417729076820910381905,-15999778165039979948285891893549981433422849494681729871934⟩,
  ⟨9515910593053886585049998072876841577910970541033358043146,9515910593053886586450560701978758808369807922005506774104⟩,
  ⟨-230836118803923024594777199658371347953638739231882582998069,-230836118803923024565442867254018004908228827729084070275065⟩,
  ⟨134913854084687719349814985346582524167150146658686028801998,134913854084687719360669436480562793469199864758348664513220⟩,
  ⟨224695962431809973427022046904960474431026651602846990934200,224695962431809973458113361886360468502677012325825956084212⟩,
  ⟨150546131347340447242876712079554053591761256146832745818005,150546131347340447256220874457090514729312569359439435031478⟩,
  ⟨-35886553226054099394218341885664525774320234661377109365210,-35886553226054099370759008509992244045829669964189570995380⟩,
  ⟨74103993258826567128206552432556066314124403312098968629502,74103993258826567141439494342575626502233772509868459603376⟩]
def bs1_2_1_18 : Fin 8 → RI := ![⟨-14490107886946501330559717672217991761221357913632412305226,-14490107886946501328448079763407681919064587522888571645988⟩,
  ⟨8823175436781398357495852902653977777973731490208171086991,8823175436781398359014470387707224417732707279001383425381⟩,
  ⟨-208316075649528559301027656044839849121535730665166661442047,-208316075649528559269220702769861944883329645376040444314266⟩,
  ⟨121494533180797001492090034443731327164429704839754093924692,121494533180797001503859418361923025723003327569286876019237⟩,
  ⟨202543440248759887550722282764387225929570559835656625481321,202543440248759887584434316474603862280712619939709072407481⟩,
  ⟨135883587718712241436714573181090863152196648255318168731907,135883587718712241451183528649473422107306423702633737080907⟩,
  ⟨-33026443181688291107876924016419374268277625690312959561803,-33026443181688291082440179445676729931065069414535673106967⟩,
  ⟨67583453680086215903590166782785563882973612569085262564208,67583453680086215917938526895982831640865501080168940881877⟩]
def bs1_2_1_19 : Fin 8 → RI := ![⟨-13017126059298882435148759728642989274502864936126509020026,-13017126059298882432847309646723241605211371654090205099838⟩,
  ⟨8122051007092580781558497919026878837599484661690211061175,8122051007092580783213621802120135238527584885579660347141⟩,
  ⟨-186447346390600747357041042198745749090170002624982120887251,-186447346390600747322375006456911198352774312465079168324736⟩,
  ⟨108521425245906590136682320982810293746452650659526260900862,108521425245906590149509638332216977505870644772430260206276⟩,
  ⟨181083595061684770646927277524497434409131999350887655532791,181083595061684770683669638713268482081833437114727438290909⟩,
  ⟨121630383097103271892339345049899094163484188832948087957702,121630383097103271908108894654371959762311785955474137946025⟩,
  ⟨-30092610555729807704885321027369541744303738211293084284303,-30092610555729807677162103126030247385016552376857840198841⟩,
  ⟨61072762243997149467538766416761222970827185964451666239033,61072762243997149483176880517611717686150452222626051421469⟩]
def bs1_2_1_20 : Fin 8 → RI := ![⟨-11601387832805280217106574800746185058142946354952351468361,-11601387832805280214583501005497229190281385492130466729592⟩,
  ⟨7422008502159368470680465534081517095494268146036569305333,7422008502159368472494973582745543149811377316277729684106⟩,
  ⟨-165533837694977978504763871763247699035666864166750416173821,-165533837694977978466759586094412111622221777729371102339621⟩,
  ⟨96164248312266835596624502545406333385394939709809732094688,96164248312266835610687057507071242921304528091373693804677⟩,
  ⟨160605332753350057078086547818734961939863850785947469350427,160605332753350057118367103726127530328175845418033220445996⟩,
  ⟨107989542635261417043111569522222707734520115958654233997446,107989542635261417060399686125206741729747254167288263666299⟩,
  ⟨-27156107151505751184834639004535645449211487972599565591193,-27156107151505751154441746647454560505668396194617164920532⟩,
  ⟨54698567734414696745215718941519252285538181438194817279614,54698567734414696762359743139378862367794082222118510827616⟩]
def bs1_2_1 : Fin 21 → Fin 8 → RI := ![bs1_2_1_0,bs1_2_1_1,bs1_2_1_2,bs1_2_1_3,bs1_2_1_4,bs1_2_1_5,bs1_2_1_6,bs1_2_1_7,bs1_2_1_8,bs1_2_1_9,bs1_2_1_10,bs1_2_1_11,bs1_2_1_12,bs1_2_1_13,bs1_2_1_14,bs1_2_1_15,bs1_2_1_16,bs1_2_1_17,bs1_2_1_18,bs1_2_1_19,bs1_2_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_3_0_0 : Fin 8 → RI := ![⟨-11059279082733179871736344042652584899983799582811302550029,-11059279082733179871625877193789854995975247140571299380440⟩,
  ⟨14645945883342238012277545534511090050227016598512045841949,14645945883342238012356989499563611806386811634382731673103⟩,
  ⟨-140158703513230320023153974522042976349751372884128290582635,-140158703513230320021490046305250249130589294832643903642134⟩,
  ⟨78575171898651585589792777071146745382508764051600267949787,78575171898651585590408472948163275251018236431427613365358⟩,
  ⟨133435711463314910123075859956898532027036433856296461694122,133435711463314910124839449309369182905147038128775202771895⟩,
  ⟨90293374102516596230115029893447074059130171756555456756960,90293374102516596230871949396361865306213342576153164253865⟩,
  ⟨-27254235177819368704240546533312916089377140660648410235176,-27254235177819368702909865261223071333658870054130018625056⟩,
  ⟨50438045375783019843166297611874032702356933125888931677966,50438045375783019843916908368362050152683600901006125002110⟩]
def bs1_3_0_1 : Fin 8 → RI := ![⟨-11867751994342143446852244199033479631435284370828400242844,-11867751994342143446737001823317782697249452646123330701767⟩,
  ⟨15119587659300662197708049235111957778127100032221733291992,15119587659300662197790927595119084234876407071948796861506⟩,
  ⟨-151315437287889022925980862212463319851710857772976664339835,-151315437287889022924245001701390367983071502348495023295941⟩,
  ⟨84945278802518438835780281493005586532835260230435973582352,84945278802518438836422594153468296940796510581481714421486⟩,
  ⟨144158498301402584551679833316202656714918435293335839881828,144158498301402584553519663354426088327642902168976129767935⟩,
  ⟨97575523973107287035933228574085671461331233670912950181065,97575523973107287036722870015293683184028762008601270379185⟩,
  ⟨-29384730083072215195321465140758159993083919997547516653777,-29384730083072215193933257975493051926414196480170745905494⟩,
  ⟨54442707942320676758971142689122626378430666950496168119999,54442707942320676759754202654224802604352610998629430459294⟩]
def bs1_3_0_2 : Fin 8 → RI := ![⟨-12656523017888089165244654663754004181324548243282454201978,-12656523017888089165124312973695414481196940627655247637767⟩,
  ⟨15505617648676215808329993668487310440494737048390102818577,15505617648676215808416539280295177406460004074405205749815⟩,
  ⟨-162374706244115173311702207543453455775877664163481175508120,-162374706244115173309889537626584382518978649764932031410274⟩,
  ⟨91282697234857447184994922049476986717121942992520251014073,91282697234857447185665656149032953839298952965782764075972⟩,
  ⟨154808005022003684595328631772127059897085792233628002473135,154808005022003684597249871722668149524550082820635079138337⟩,
  ⟨104809075136683791336886125507250178720440795751679162827823,104809075136683791337710707480551172364875951530029136471118⟩,
  ⟨-31475942289818744560143142371636622092099725216482648743427,-31475942289818744558693508976096735652542901464350642315394⟩,
  ⟨58396140180263977521055400735731400169909075616167225928216,58396140180263977521873110011788388064581186656555261452109⟩]
def bs1_3_0_3 : Fin 8 → RI := ![⟨-13412346928199297551983635798577942402467834236091709436668,-13412346928199297551857837162446790543438948767270099440751⟩,
  ⟨15795220113588383613570546692989669466904806632720428960808,15795220113588383613661016753059657008887822948968623115463⟩,
  ⟨-173164237056324133928163858816554543459501223911143713853552,-173164237056324133926268992596984780578200402156886194346786⟩,
  ⟨97491254812642378102759742780540515121020113256590845116484,97491254812642378103460891608432248806881102765679069691252⟩,
  ⟨165220664228157879578242321918222496790612228080903193698482,165220664228157879580250681326678188254173964941697548473865⟩,
  ⟨111882003634195307528236287887601054544955908532609931246048,111882003634195307529098260887726108227785417663447099138562⟩,
  ⟨-33489894608905741361881769758611861837312367903178366083055,-33489894608905741360366402108717894490196151207016516733053⟩,
  ⟨62231427266526400753729857617312276971703666117182648047438,62231427266526400754584646274756125109803922678867722286209⟩]
def bs1_3_0_4 : Fin 8 → RI := ![⟨-14121329310620468036999426775113095314107743431717864615385,-14121329310620468036867775569009143730743845562739263597458⟩,
  ⟨15981250541288522335539136130196202264383426010915170838896,15981250541288522335633815157654371770967460693096488698846⟩,
  ⟨-183497424637439641128966746893255105685057268091056587041762,-183497424637439641126983725209683358874260284736309952767317⟩,
  ⟨103466064980991736454148921724173440357794480925126967464145,103466064980991736454882690322065339493532529427584046812784⟩,
  ⟨175218670980065172703524662343425352429053024051401487121255,175218670980065172705626457295618726694279926445632289839228⟩,
  ⟨118672369106086423116588576601341027672467590547268355717489,118672369106086423117490651445599135565710952626551595504592⟩,
  ⟨-35385801996227942549725676926051243386875624747539802499638,-35385801996227942548139809344859134259908796425595452541652⟩,
  ⟨65876221078377241918141226905067540425056018108270065969483,65876221078377241919035783167180522047453119330603439524862⟩]
def bs1_3_0_5 : Fin 8 → RI := ![⟨-14769271531189731207357387992976464627927373521311134843805,-14769271531189731207219445861972485077669147361869104943108⟩,
  ⟨16058582043984904739765454438556915141538416050975243386930,16058582043984904739864657683216848011609751812021561071949⟩,
  ⟨-193177153268601781336555620678735308803301412514146434582244,-193177153268601781334477840725524711688033044358472203431361⟩,
  ⟨109095556286205834949227061097176081895979792173833337863419,109095556286205834949995892671552293914894395916938436336416⟩,
  ⟨184613515757047838639183872691621089617178986953017225288500,184613515757047838641386101468848307421943557795026506172419⟩,
  ⟨125050747990381629610907690601563086127936998235829853920835,125050747990381629611852870900513459366487452457637423211642⟩,
  ⟨-37121101476249326553621460170643079558501623319202840500000,-37121101476249326551959812244182071103207269398139689145665⟩,
  ⟨69254388906887543468810574952505445117690652647787200301904,69254388906887543469747877395456906242563535128929991777470⟩]
def bs1_3_0_6 : Fin 8 → RI := ![⟨-15342076770256947663834853899953314791623148174004436257139,-15342076770256947663690134315225441682606089063795918090298⟩,
  ⟨16024397081298638049381588039970854222678797598508652934563,16024397081298638049485665396658630249285614973972144375087⟩,
  ⟨-202000687786359823352647084172523777802872344679289119112035,-202000687786359823350467217515428073973893230202695236710385⟩,
  ⟨114264121928226274628539921466164652235793177177978746023136,114264121928226274629346527724601327585189056571638278020777⟩,
  ⟨193210552581246612010333371842666833660729776140882919450706,193210552581246612012643801816426683169039878300685555982976⟩,
  ⟨130883397098861507283253810781211815089208934169087276437347,130883397098861507284245430233238969460409600550936076234971⟩,
  ⟨-38652755256309523323330420212356512135945051747669793972443,-38652755256309523321587131224939146300970615463390392630900⟩,
  ⟨72288128575482613171004997418405289918674423248874947560366,72288128575482613171988351954985182421798385370050724652668⟩]
def bs1_3_0_7 : Fin 8 → RI := ![⟨-15826206859981442116865266078283539993701148516473336225855,-15826206859981442116713228058616194047003839268204445304508⟩,
  ⟨15878395656816981823890537099610061248532656977856089153876,15878395656816981823999877623442356201623363494581262992026⟩,
  ⟨-209765589849663714579295466710323881690728473813205185077743,-209765589849663714577005364715444405391795185486957631859422⟩,
  ⟨118855375290081200872523131259188814984254000545606602054570,118855375290081200873370527404051981903357768908854217822472⟩,
  ⟨200814569363063445781353520698935243635531429119199965049099,200814569363063445783780788566313605834560694426543185301343⟩,
  ⟨136036126949785919998188863948701297332505571302528204765234,136036126949785919999230629360300540430114186497801760086122⟩,
  ⟨-39938805248286178955883534458790165975104096975783594698931,-39938805248286178954052087762396435275327782240553128356793⟩,
  ⟨74900525041426378923244556806845882517139200448214896496635,74900525041426378924277639348186239095529094771076000203909⟩]
def bs1_3_0_8 : Fin 8 → RI := ![⟨-16209174433300427829680283034808163607180650890636480430940,-16209174433300427829520323876887960443685225128990420182885⟩,
  ⟨15622893323249308575533973086435627178978924495703147044657,15622893323249308575649010220942740832704912025207737880813⟩,
  ⟨-216276534068301623272561982401778226747446553272691142138436,-216276534068301623270152566734213794146160214889809652267886⟩,
  ⟨122755952386856703994357722468387517717281084959873126234048,122755952386856703995249267715125366098858329716386261453007⟩,
  ⟨207236251595831684956720594068919082239115977978077535209868,207236251595831684959274321912532622890661842481402081030334⟩,
  ⟨140378809785468384237317633142126853582230080669811103148448,140378809785468384238413674239973525531286727443491650453176⟩,
  ⟨-40940130775316960852861651591451027197208782318225630352919,-40940130775316960850934787035006085454303493209978868196332⟩,
  ⟨77018483010459720439000454648775378546816901244665208511550,77018483010459720440087360501247611233818875873779702863937⟩]
def bs1_3_0_9 : Fin 8 → RI := ![⟨-16480049638187459360405552971833648224274694461981691305035,-16480049638187459360236999803048367545708686033402175659758⟩,
  ⟨15262789179786244059894287685436756071617105639334823032587,15262789179786244060015505337499573291099631378215615725773⟩,
  ⟨-221352805789514237127684533806742043219126412867544768099771,-221352805789514237125145669192994215386210327372241351747079⟩,
  ⟨125859749205965020195887235268523501384499133974739301617483,125859749205965020196826679926821528488451103718153502803033⟩,
  ⟨212299341541084275501934505184930635418312353390551815781410,212299341541084275504625435331429153531154945484458876560153⟩,
  ⟨143790382973594160908265079692825666643896028641412635647926,143790382973594160909420007004046688987019603940766858702626⟩,
  ⟨-41622331383905927644064599907523529188894005725710299639592,-41622331383905927642034212082096840440695466228232033889111⟩,
  ⟨78575923233001059844842193381265702513799584694726846988670,78575923233001059845987494644333628649823197010485838826326⟩]
def bs1_3_0_10 : Fin 8 → RI := ![⟨-16629955901690234817729361760904994345533313716069601085629,-16629955901690234817551461689221799635260979632793109581778⟩,
  ⟨14805395705243386831186155566005617321850352662612062091378,14805395705243386831314095189725005171079472100495086449533⟩,
  ⟨-224836162409280737807595079343411974221904283823568134214475,-224836162409280737804915425202025949586940396752347668398204⟩,
  ⟨128072423710675117658407822284696358212968613574410351360991,128072423710675117659399362658924281155187458501609325281223⟩,
  ⟨215848198251707044583758738575988603813647829705073178557223,215848198251707044586598890852010751215052351188050435780289⟩,
  ⟨146164138303357436550688255633348815721007927711739680920869,146164138303357436551907227978615536522333317882274054060310⟩,
  ⟨-41957626185793042401347641048732631464543153387438837040935,-41957626185793042399204660633184126983926033175463089087105⟩,
  ⟨79517080626662230226579075956222835420928550385785311098708,79517080626662230227787888452996380272509401888727286015370⟩]
def bs1_3_0_11 : Fin 8 → RI := ![⟨-16652525562918159407037315440736170900003620894538383312890,-16652525562918159406849224026311414861727764835056451981345⟩,
  ⟨14260137585455675057177487329127725076068788393720787312826,14260137585455675057312756216646952817664850356463541735692⟩,
  ⟨-226598642566786280455387305279581848031294648727031612846618,-226598642566786280452554142072545677058982203612888427430434⟩,
  ⟨129315933939572322714980216013632647549677667397536508394715,129315933939572322716028558657255464753195787119219695121295⟩,
  ⟨217755367892357072799722745531688757515081104965754630254790,217755367892357072802725601313161977895720370715828852913919⟩,
  ⟨147413017986871809497762492593435144192289363986861501325195,147413017986871809499051296079561312256790909001998698049981⟩,
  ⟨-41926634226519053760915482171170290989239308715435700112337,-41926634226519053758649737061411523000968424915726265329472⟩,
  ⟨79799695988840204025776717957060067999806195361137814021055,79799695988840204027054779568508407154640401870709463040852⟩]
def bs1_3_0_12 : Fin 8 → RI := ![⟨-16544284318865607535334670371659961751907977870853781814472,-16544284318865607535135438080939963776140990495794460518084⟩,
  ⟨13638142997235854966019219185361642576535984932703933604329,13638142997235854966162500208612026627044072780309470544120⟩,
  ⟨-226549825556441391972505234281048149992113931353497025774654,-226549825556441391969504259476073098457355662262846395720203⟩,
  ⟨129532832499214313660586150089063900429775972568386858617291,129532832499214313661696587303801980201875919914974141779703⟩,
  ⟨217928691213363268800334704748884287952371191580264653459497,217928691213363268803515423219602720285716537342831024260581⟩,
  ⟨147474578188515554853074080566883940197977535508987016795714,147474578188515554854439221403407506759778490725826636080873⟩,
  ⟨-41519882483468981125264640144170959832154066925104472887290,-41519882483468981122864692279556160602012482509585707876904⟩,
  ⟨79397857707404486692628255279686245284239412596152915506856,79397857707404486693982017987615096970463400192608240760627⟩]
def bs1_3_0_13 : Fin 8 → RI := ![⟨-16304934007788105506386348284532669327485231009996345950791,-16304934007788105506174904505353326286302612083647007559932⟩,
  ⟨12951764327691376250603775744794863921042886526229790615774,12951764327691376250755838851287312602545827329454344392991⟩,
  ⟨-224642992748908584720519335322318768997025925459658321295982,-224642992748908584717334422617194197081630928566314137316012⟩,
  ⟨128690003068922381027122788857223471093804040237003182077064,128690003068922381028301287786182043543211182541605789293697⟩,
  ⟨216317421123069711126488534531141883188516269524948110671280,216317421123069711129864207879691229669855873445155331585541⟩,
  ⟨146315242144309769482284962935878682936221152615585101684655,146315242144309769483733776963694066899348418035164203192423⟩,
  ⟨-40738885276996582715247663119728226811735255938713982386301,-40738885276996582712700615929290092046324279005799113812495⟩,
  ⟨78304234764151341689610985653175249427214423365619985896363,78304234764151341691047724155963590080108449602409347411224⟩]
def bs1_3_0_14 : Fin 8 → RI := ![⟨-15937506809870929450651381334119650199087397245504441564381,-15937506809870929450426515423600913586826023524478767487604⟩,
  ⟨12214072374947747918857629774760969731665113418317994543301,12214072374947747919019345617289585751566965401170765465715⟩,
  ⟨-220879640565972106630272109693778810219405533509042296974312,-220879640565972106626885023546627439402501275068694421959529⟩,
  ⟨126781516345711082547092871491460760160877579053451274000106,126781516345711082548346179750216156898384440541768003575333⟩,
  ⟨212916814577808849025726178717300911597321880826357727877563,212916814577808849029316134705040192377630297174315383486298⟩,
  ⟨143933459696347656448766244099009511314518222268536879548859,143933459696347656450307026650307045421397952234967072596548⟩,
  ⟨-39596656395439000689355177008016123863813245423913805688902,-39596656395439000686646447113812765660714383671830435841424⟩,
  ⟨76531456310266950451399289985452224779041358973133254879526,76531456310266950452927230475639482837089720556652943672987⟩]
def bs1_3_0_15 : Fin 8 → RI := ![⟨-15448370684586773850915576061349791493060860453113948403803,-15448370684586773850675914758577428397378452977984051634584⟩,
  ⟨11438366897650018706550609344085467674846547809509388340218,11438366897650018706722965524751326580319739536876334580080⟩,
  ⟨-215311854458799118269031856399441282084498463356811693974105,-215311854458799118265421911802881798556346237714001642278939⟩,
  ⟨123830309833848204254522441932426784919819233718007505673533,123830309833848204255858213501263480327047591747522677042145⟩,
  ⟨207770713478036834749644539012091011292086287311464971155240,207770713478036834753470701576848273548773161770909220541933⟩,
  ⟨140361428667145311191031565537416778203107275060897520138032,140361428667145311192673726204121257780312646794635617883156⟩,
  ⟨-38117555579381296718410506410892787223728955289291066924655,-38117555579381296715523551541660975279116204595802500482563⟩,
  ⟨74112441956270067280768838032761785012682307351840904987228,74112441956270067282397311675527604394350398146902015752979⟩]
def bs1_3_0_16 : Fin 8 → RI := ![⟨-14847075534178452652002178432433285504250837772339149728352,-14847075534178452651746158782536407295807696798642546202629⟩,
  ⟨10637738109432334017913542911352943586647731041518403053245,10637738109432334018097663453637926559246345230801030516737⟩,
  ⟨-208042181208497290201703116913324781928369233448730559039287,-208042181208497290197846771558167469929330654697011055609765⟩,
  ⟨119888462394961530523038975672026733414301436244769830319202,119888462394961530524465921805771523916600800848390464266394⟩,
  ⟨200971745541787277455125220389729383940503578770203925885215,200971745541787277459212541909499625658201055725306119072436⟩,
  ⟨135665120495522415974861909591541007336962851496853162477087,135665120495522415976616157749693077961945988570893482795448⟩,
  ⟨-36336431808946197557536493842213126322837517586776390721500,-36336431808946197554452486677392084954921915993157314453251⟩,
  ⟨71099570167971207048995357161688180049864474249830604801307,71099570167971207050734984072931404847380904639369625691503⟩]
def bs1_3_0_17 : Fin 8 → RI := ![⟨-14146041376688819581622347974041956091034679268085407118565,-14146041376688819581348184660729551124873540539167565436793⟩,
  ⟨9824701368646180985764300625342240745050946892483685238808,9824701368646180985961469467427174344083679547476166026951⟩,
  ⟨-199220825786080937253387207418860163484155918269281903010424,-199220825786080937249257569634137839440423420100780505175655⟩,
  ⟨115035937719048886279130688606335420765911724427058143769546,115035937719048886280658759909095611709125796079724559697895⟩,
  ⟨192658952783915884445074488976982073736521694442023951021989,192658952783915884449451471801874147213782709680092241101260⟩,
  ⟨129942483253546117949624043140901485364970010383801462984900,129942483253546117951502611788311125655539764156488681569795⟩,
  ⟨-34297098914455249774283384944895539176621986579991896562484,-34297098914455249770980819603068917211793533911122308959704⟩,
  ⟨67562680893547737843485257587982943072827858276847274990536,67562680893547737845348168806340494760078277816458822863031⟩]
def bs1_3_0_18 : Fin 8 → RI := ![⟨-13360102438903416378317465528952761330648685625812848852634,-13360102438903416378023111170253034286506379423137390369440⟩,
  ⟨9010913855065870081760903858967410501670158708585910969618,9010913855065870081972593407673149535316180395985186097604⟩,
  ⟨-189040228258976397187740122169300063568009745650496744222408,-189040228258976397183306352869184087828288162976828186637122⟩,
  ⟨109377799997862866971557738925410190308097775480065593871869,109377799997862866973198346645467590447375849158404011417930⟩,
  ⟨183012873434850585058621606838511056522607501519174270754931,183012873434850585063320937164277038742542777643590556743522⟩,
  ⟨123319854815529937761190131716503167283450453315262363496658,123319854815529937763207049526579317806630225940344988505212⟩,
  ⟨-32050252175466146751506278490606690022560367020617603229754,-32050252175466146747960492252837833253972870524422700835597⟩,
  ⟨63586026667212328457250763811784234613961502097879987421761,63586026667212328459250871084955524174433269287811977809218⟩]
def bs1_3_0_19 : Fin 8 → RI := ![⟨-12505932995791738271681363624705816147634315530100513701774,-12505932995791738271364460105456776339860676411377344641748⟩,
  ⟨8206973148840299395328728857925180690647342140291456934183,8206973148840299395556634988714452251338898315521053176997⟩,
  ⟨-177727315493052171862058585644263160521406315511049984475966,-177727315493052171857285165264316378726638518464079319352103⟩,
  ⟨103040043319380628247857363327842700600728026419728571943916,103040043319380628249623650609936315532276739906024557397646⟩,
  ⟨172248334399878013262013272479322401529480010644267174656925,172248334399878013267072597318026350759226359217540372281629⟩,
  ⟨115946785886228248729144081894203643637756159032680697344757,115946785886228248731315506686017503497839287108552939802273⟩,
  ⟨-29650995096245375344734378552865805233945366692097638295927,-29650995096245375340916965614932568396029343586975382168875⟩,
  ⟨59264395004655776331775195271865791609239404879215559470615,59264395004655776333928521747280766675006411620985077139291⟩]
def bs1_3_0_20 : Fin 8 → RI := ![⟨-11601390358647615147310501217091922935605066992473154114395,-11601390358647615146968319432019734699372042593542970898269⟩,
  ⟨7422265431848286487346266758080908977711401751859026813203,7422265431848286487592352149767531393191651264387985163781⟩,
  ⟨-165533932141056644673512304373083882991536662534094421372677,-165533932141056644668358125238756458112431013044657799186820⟩,
  ⟨96164300997392539960224492809898362534543461454142448247063,96164300997392539962131670542029464095553029957278798416192⟩,
  ⟨160605417748433077073827945876585264649772140024377107671903,160605417748433077079290835050781267800120768881136161137816⟩,
  ⟨107989618281196752921343721105679774346967622461065030430993,107989618281196752923688352724749588670967488944942179702074⟩,
  ⟨-27156179960462899753962193866206026726663094002412878102935,-27156179960462899749840279485026610985314324601148396538539⟩,
  ⟨54698701877770971806359694355650441732065587475976467788003,54698701877770971808684784019989199521894374879155022372990⟩]
def bs1_3_0 : Fin 21 → Fin 8 → RI := ![bs1_3_0_0,bs1_3_0_1,bs1_3_0_2,bs1_3_0_3,bs1_3_0_4,bs1_3_0_5,bs1_3_0_6,bs1_3_0_7,bs1_3_0_8,bs1_3_0_9,bs1_3_0_10,bs1_3_0_11,bs1_3_0_12,bs1_3_0_13,bs1_3_0_14,bs1_3_0_15,bs1_3_0_16,bs1_3_0_17,bs1_3_0_18,bs1_3_0_19,bs1_3_0_20]
def bs1_3_1_0 : Fin 8 → RI := ![⟨-11059279082733179871736344042652584899983799582811302550031,-11059279082733179871625877193789854995975247140571299380440⟩,
  ⟨14645945883342238012277545534511090050227016598512045841949,14645945883342238012356989499563611806386811634382731673103⟩,
  ⟨-140158703513230320023153974522042976349751372884128290582635,-140158703513230320021490046305250249130589294832643903642134⟩,
  ⟨78575171898651585589792777071146745382508764051600267949787,78575171898651585590408472948163275251018236431427613365358⟩,
  ⟨133435711463314910123075859956898532027036433856296461694122,133435711463314910124839449309369182905147038128775202771895⟩,
  ⟨90293374102516596230115029893447074059130171756555456756960,90293374102516596230871949396361865306213342576153164253865⟩,
  ⟨-27254235177819368704240546533312916089377140660648410235178,-27254235177819368702909865261223071333658870054130018625056⟩,
  ⟨50438045375783019843166297611874032702356933125888931677966,50438045375783019843916908368362050152683600901006125002110⟩]
def bs1_3_1_1 : Fin 8 → RI := ![⟨-10520297141660537488328927622967299765800995912443281669147,-10520297141660537488215277089535925175007590615226567585230⟩,
  ⟨14330184699369955221988253470807441764567286306801335716347,14330184699369955222069987032496366654453422678576273373074⟩,
  ⟨-132720880996791184754650670924616230448096567873560877480098,-132720880996791184752938787844970020129282971573411654470668⟩,
  ⟨74328433962740350092450029600943397589323247951564200579035,74328433962740350093083470000257381150800572312203809610314⟩,
  ⟨126287186904589793837289050593527261745372524496162510363429,126287186904589793839103467069833099779892370504082283980090⟩,
  ⟨85438607522122802359547749480825862140586558801590052673413,85438607522122802360326483609269467038079301299914835304461⟩,
  ⟨-25833905240984137710224951390466262360873589709954592048220,-25833905240984137708855919522926242064521017162863947679322⟩,
  ⟨47768270331424581899274768087965531067910926394140061373177,47768270331424581900047011650196321035301111684601300707420⟩]
def bs1_3_1_2 : Fin 8 → RI := ![⟨-9972558805893220501933293562544072328701649612936130239960,-9972558805893220501816315438992974946339170745872896063209⟩,
  ⟨13975484943583063287339601732781342338670913162850039846986,13975484943583063287423728383038286277228478862721078939669⟩,
  ⟨-125239740783270915034100459611887170067422794641507303226932,-125239740783270915032338454064269300320609954936662022392769⟩,
  ⟨70067167817261183529874898190567853811231148110749720674575,70067167817261183530526885181355769365571427408200871898986⟩,
  ⟨119106093404759533380411052384209448572279884248585352101002,119106093404759533382278593418379308109931621373370708465778⟩,
  ⟨80562241516389370042373668291549499047335612587250746022157,80562241516389370043175203087210700460181602285445288562441⟩,
  ⟨-24396116327034987993427471191367705608062939151276785270616,-24396116327034987992018355245222169743549110297437507457793⟩,
  ⟨45075726252135318998174088772661553929200330702864000564469,45075726252135318998968942963897628810611762717219821095233⟩]
def bs1_3_1_3 : Fin 8 → RI := ![⟨-9419988586593219868084248819153557345538727297000055891414,-9419988586593219867963789172008772057283693299645619626453⟩,
  ⟨13584458686464677832205014854368268605797091149705072373882,13584458686464677832291645296862697658541645672534696657599⟩,
  ⟨-117766326820990884862141758801292095107022004276876822234499,-117766326820990884860327312133061820271311154002246299329603⟩,
  ⟨65819868983110747393823462047849742830349341808757329758647,65819868983110747394494853590723752729211897743496505454622⟩,
  ⟨111940895377738300804524648465957589764556917600099654287355,111940895377738300806447771586548324867983687505905589049572⟩,
  ⟨75697468369479499754070475482479680963368294143756696326479,75697468369479499754895865698434318547780378707927979865193⟩,
  ⟨-22952120936461761164758984796555387467048547147475194679166,-22952120936461761163307930492506836755665279358376754381527⟩,
  ⟨42380239752163089325253588307827784670985266110109903531646,42380239752163089326072099090025403731975107482037821589306⟩]
def bs1_3_1_4 : Fin 8 → RI := ![⟨-8866382759962806819819845547572635186286451487773602777738,-8866382759962806819695739596092949470196272599861471256806⟩,
  ⟨13160048117042481779753178596807331172528715631153927107401,13160048117042481779842431336190894802678366705387173569687⟩,
  ⟨-110348852093039554383759669685071722936848132899608894919015,-110348852093039554381890299854533272794771203309180453607315⟩,
  ⟨61613311663288367353780419441951572328076367359013004257797,61613311663288367354472133955641291935283875443909671437857⟩,
  ⟨104837244883299099545195820394625788468677398481686470344081,104837244883299099547177156305451965875055859360931940670390⟩,
  ⟨70875521570394987350134091063128429016694126081535905328523,70875521570394987350984465777991813913453943632854730583771⟩,
  ⟨-21512616931739079553354990936533633219813468672112360704607,-21512616931739079551860013329337970442311888224890268230569⟩,
  ⟨39700564201381591428734383524088496455078706532780670440345,39700564201381591429577670565257434518132962269333170405019⟩]
def bs1_3_1_5 : Fin 8 → RI := ![⟨-8315363939073074464089619212869733903289088499071663546959,-8315363939073074463961690431884964733533298052814294003423⟩,
  ⟨12705479926450859463955792363637607646881570404559634714267,12705479926450859464047794350752047485111654234607324285726⟩,
  ⟨-103032195423236851588619971283563239269126338005523191744680,-103032195423236851586693019346294329560328278754740581618679⟩,
  ⟨57472281513524896408203295970114835146686819071209385011691,57472281513524896408916317331870438970425060781183758432642⟩,
  ⟨97837516381054085397800229989371802118505667701715436092778,97837516381054085399842596892579805329038524919227675987018⟩,
  ⟨66125355391829292063969359107263199958392014895631832955679,66125355391829292064845927872547560139342257353401193807058⟩,
  ⟨-20087611909537534473934143657061488225021061660097454869777,-20087611909537534472393116328337312210614677368788470737298⟩,
  ⟨37054162610762505104405059560399407617666018473720561526247,37054162610762505105274322330723615158127546918123921149386⟩]
def bs1_3_1_6 : Fin 8 → RI := ![⟨-7770341006543291919555587013330217452942872408442193361715,-7770341006543291919423646148333993714670549556166651552694⟩,
  ⟨12224214891285041655636369596198443646055898813658133234639,12224214891285041655731256936387049300718520505766892388806⟩,
  ⟨-95857492224045098283323163721376302715256026981122604879597,-95857492224045098281335778994873211450726023270189725693092⟩,
  ⟨53419362868169512524897095095147843133806902855665607782062,53419362868169512525632478130199750122013343509852618686727⟩,
  ⟨90980432362831310069975240304380249617101321445131308287410,90980432362831310072081659624368169854069277898130247798761⟩,
  ⟨61473388590005332723795773019172153646686024782182446699687,61473388590005332724699832607876727824704160689672373820485⟩,
  ⟨-18686311556762374823972781985157214742050540661613802291255,-18686311556762374822383425179214786304746455995449869975644⟩,
  ⟨34457031464249308058537498258737088013978707468569732429269,34457031464249308059434022722916866276651669079187408288719⟩]
def bs1_3_1_7 : Fin 8 → RI := ![⟨-7234475008539254340418669008889269227632982077779043716828,-7234475008539254340282512992373987508019069860817113233527⟩,
  ⟨11719894345184520205361773381391300684788121526296370206849,11719894345184520205459692113833603773648404454563376374141⟩,
  ⟨-88861821818865361253684544374468987722233546760454292310759,-88861821818865361251633668115232820565911361746641121033836⟩,
  ⟨49474781258422648858352351161211621975749251163111730903884,49474781258422648859111227682664879891059022572892699105814⟩,
  ⟨84300781791348400876761731521255753995072370909465928801608,84300781791348400878935445205249565941340349210514605624317⟩,
  ⟨56943313432428838185154459350386267368671894212174280879209,56943313432428838186087401182276612573977634264794133289277⟩,
  ⟨-17317033265352907393208808724210556396550861731525022174077,-17317033265352907391568676294246121603453672107993177309225⟩,
  ⟨31923566955669425053111498070678636269169669430006757749485,31923566955669425054036664051321979668494844676719612395763⟩]
def bs1_3_1_8 : Fin 8 → RI := ![⟨-6710651406381277535486020688821341065457720850126165724465,-6710651406381277535345431445546158630132013627949912023310⟩,
  ⟨11196285312261761290763781708299001129060858130876025763834,11196285312261761290864888665221015666722915053542203699049⟩,
  ⟨-82077990840292295628580035925594157725502103000401008470220,-82077990840292295626462383333249564503594779478098934198378⟩,
  ⟨45656300313731971735281580424219356261229895616176612810915,45656300313731971736065165891988686883426279012082808986421⟩,
  ⟨77829230310314591344497124754993986255367802774236308632922,77829230310314591346741614346793820193992862128301143753695⟩,
  ⟨52555969135927995507296442828103680862225013086288983180780,52555969135927995508259761156022467874099864228886855733925⟩,
  ⟨-15987145249172407707116248654856553711312816130703101470334,-15987145249172407705422713671236436274995168934217423222701⟩,
  ⟨29466473507217053534306125282945301889066511513504665826608,29466473507217053535261414578647708727922802526572026996321⟩]
def bs1_3_1_9 : Fin 8 → RI := ![⟨-6201458878419259141151150573342045957283508850702407423549,-6201458878419259141005893700682171144903074257566921319724⟩,
  ⟨10657226039796177000836559077063751131998995994660263903280,10657226039796177000941022832785455936354542747273132013408⟩,
  ⟨-75534409406541928891054094160462661852577578686371383542614,-75534409406541928888866134500264502357617250938768694047231⟩,
  ⟨41979170604607464909878197030644720814920041009589974520145,41979170604607464910687797906634012971988336853917666463190⟩,
  ⟨71592218567876958343022469067299534831333342013165802344348,71592218567876958345341476775337328948186602369810838660973⟩,
  ⟨48329276927171063131968580035587244029673401662454459118351,48329276927171063132963880987708743713471138116833117103189⟩,
  ⟨-14703030463638265000339379600081256569593480511364511600949,-14703030463638264998589618453857961858708489375198735534312⟩,
  ⟨27096713028181808974014484623377754428707135618290394170513,27096713028181808975001489975611637937517011589556711377063⟩]
def bs1_3_1_10 : Fin 8 → RI := ![⟨-5709174670507145073135505410342727510401512065472837808083,-5709174670507145072985328718038996469398827181364654386065⟩,
  ⟨10106573512553962517127041560068751170752440803622878044991,10106573512553962517235043481166059071661848275786689248802⟩,
  ⟨-69255054410977748376296798236093783833331970885816667390881,-69255054410977748374034732843623489189064817351193979758972⟩,
  ⟨38456126718055392491771409419601466182477223885644668142117,38456126718055392492608431306527094555001803417101581148822⟩,
  ⟨65611942802631524734726063181612409895830045657511898987806,65611942802631524737123615191666312957376511807566911021994⟩,
  ⟨44278232388315015336512673724367003818109368943380557386758,44278232388315015337541685309841645282196347748201949266111⟩,
  ⟨-13470073823193843459352482605271667641981002967319208272274,-13470073823193843457543457418038878207843911330359240070333⟩,
  ⟨24823492182325916584911391838671135283961831141171979128462,24823492182325916585931826854035675393406401560671843617885⟩]
def bs1_3_1_11 : Fin 8 → RI := ![⟨-5235756315835741027117955393913069395253068833942212594316,-5235756315835741026962587285374290571593316493252481442286⟩,
  ⟨9548154274722025885668411551260805051644741349774700303435,9548154274722025885780146960677341506077579103570425708854⟩,
  ⟨-63259512383746136978488517256927929777658227514595061551754,-63259512383746136976148255156147868326568018304975274875442⟩,
  ⟨35097427882762480641896995804341153782706187159025649574174,35097427882762480642762952467673705523623834681547598439080⟩,
  ⟨59906410130111962753110286454905529772150553605592522796320,59906410130111962755590718772404444476542741274021635217193⟩,
  ⟨40414949557454878386660104242044117515194710739995435629456,40414949557454878387724687442324421356923343969803736608415⟩,
  ⟨-12292670575016649965939257060551446363831581082682942399389,-12292670575016649964067696185647086240448792189267900265574⟩,
  ⟨22654284008081841644378985157581831189819901743495537186962,22654284008081841645434695306685300833111473981157862533877⟩]
def bs1_3_1_12 : Fin 8 → RI := ![⟨-4782839389816328379584507710381055369967535034227930450119,-4782839389816328379423655385125089113215563004309823184837⟩,
  ⟨8985719558735803330203212361219423045716061758414670184426,8985719558735803330318891831009185544635257643597836452630⟩,
  ⟨-57563093019007179540432547907246722877373222770510488311210,-57563093019007179538009678734422266795341513870246772910571⟩,
  ⟨31910936784417479164591775743511224108618713145306615122266,31910936784417479165488299130314888003899853471486832017467⟩,
  ⟨54489559750024641922228721059934987919953166287635012733810,54489559750024641924796708207760719207465510862936072750587⟩,
  ⟨36748750423882006788375536070762546245032659180119037901600,36748750423882006789477697156487505603923497513500917227960⟩,
  ⟨-11174253233396845837833573088644988445715901557765328074896,-11174253233396845835895949457795360882532167117801719896935⟩,
  ⟨20594879590558190812250455903167459665486461828842222571303,20594879590558190813343430734853255558937827765871856289908⟩]
def bs1_3_1_13 : Fin 8 → RI := ![⟨-4351740837045480232076030412911888978146319526117846529992,-4351740837045480231909377866686739000924877169482004277438⟩,
  ⟨8422905362900234610029896196951860344224419218598207570486,8422905362900234610149746986523466963997827936536596197169⟩,
  ⟨-52177003590341639916039068331584935957307079123698377893110,-52177003590341639913528832211722684918357754586147279783190⟩,
  ⟨28902230817034749334198173055355645115911146923278246966318,28902230817034749335127024440774346430289650684580752694277⟩,
  ⟨49371440549988222761139848934472747484142241691917958139659,49371440549988222763800435880775323232513349975210178813797⟩,
  ⟨33286292973957939461878468845280779087871516616889427356316,33286292973957939463020373079457999513591361112203065875169⟩,
  ⟨-10117334205428893759410354157208004831607014721765508780873,-10117334205428893757402861190029730659216908489219027049618⟩,
  ⟨18649465108627244013422663717746660566688931658472459764771,18649465108627244014555050448062624802536939780056700808705⟩]
def bs1_3_1_14 : Fin 8 → RI := ![⟨-3943467307182396525911772613907703332728239510027642072165,-3943467307182396525738978409413246561645249689194748131355⟩,
  ⟨7863197772875912282273485033738563639115842815127844913864,7863197772875912282397752693075646401887446011739799251251⟩,
  ⟨-47108574058491641549515576596392759602511202664562281485231,-47108574058491641546912830564306635903638124425698439444870⟩,
  ⟨26074739874548673877697403411094710369242328792686254150064,26074739874548673878660485823414059955276528806193495567689⟩,
  ⟨44558435265251884287458008979095777244612474360665727393068,44558435265251884290216646727440733954326032949457338242868⟩,
  ⟨30031730768754156202564932246872774947851320322863339562802,30031730768754156203748919159906400740319940075954432817511⟩,
  ⟨-9123561129364188233200415157970820863928461904198059772839,-9123561129364188231118939908133030784103994622278925687176⟩,
  ⟨16820719447302281988617024001361015640220533721129799580100,16820719447302281989791142661273576188742394687317363238964⟩]
def bs1_3_1_15 : Fin 8 → RI := ![⟨-3558727865220351473772783449324769012587374046254945448372,-3558727865220351473593478226136051183137627493731938200059⟩,
  ⟨7309903521023863480696538093550907343297337723089746550548,7309903521023863480825488253989785393998565545241508819851⟩,
  ⟨-42361522650435547106479617981179979897303227064855357119263,-42361522650435547103778798474230607322533866281774713195310⟩,
  ⟨23429904860371986017286601618141635076653688972744481112768,23429904860371986018285973717431952591066808133485551384531⟩,
  ⟨40053521405628151373532792298981893174075023713887171458622,40053521405628151376395377642111773644056083672766921483871⟩,
  ⟨26986897122610150754801450250273298129990314755252020874111,26986897122610150756030050701984357282828593535274944739954⟩,
  ⟨-8193781977815073895129699358272505559210538903061459942960,-8193781977815073892969792518086736757778711498599167817454⟩,
  ⟨15109927637473303732036293410857235472196799104942824071659,15109927637473303733254653766063800671775482996513278086848⟩]
def bs1_3_1_16 : Fin 8 → RI := ![⟨-3197950398108544325897176760625233247435444264562077197019,-3197950398108544325710960447743246557874290328908686151312⟩,
  ⟨6766125545907320722261685665802974260174821333987774687024,6766125545907320722395606044670432128931430269873758023506⟩,
  ⟨-37936251989070558186030074994178830918078815931002598430537,-37936251989070558183225155865782007753606113354828965051829⟩,
  ⟨20967351339474153635747172239061385590545107894417452694684,20967351339474153636785063853250397411867962111001779247144⟩,
  ⟨35856559513382174675887425428090113513924656515131900841704,35856559513382174678860345449200824088198921294308353890141⟩,
  ⟨24151507250860695294074278534271166639086065650449595183939,24151507250860695295350233813516172884876817612308602578528⟩,
  ⟨-7328117120279548926433452798608553955695349396269152423396,-7328117120279548924190295121475730491018023396465527245649⟩,
  ⟨13517105619173967903094148342991910298452207638713721739628,13517105619173967904359468834348614526972351035508791615598⟩]
def bs1_3_1_17 : Fin 8 → RI := ![⟨-2861301021850133238351090613948619082830441451280322214037,-2861301021850133238157529302173617779200830351349714068421⟩,
  ⟨6234743162131299866070199799187328878494993847133225483279,6234743162131299866209402449082345999243994041019506821724⟩,
  ⟨-33830166408784110067819584425761751213823393671794377530292,-33830166408784110064904029834908290645914781251873891890237⟩,
  ⟨18685073136409055865554135092630503103547645972818721445810,18685073136409055866632964649582517982729390308817288764699⟩,
  ⟨31964599901055188512859983520289993979009784724145481288726,31964599901055188515950165525197572538277385021616442662187⟩,
  ⟨21523372213831152029969824226445858849225815430209176115319,21523372213831152031296107481633402074391131781404412396021⟩,
  ⟨-6526035763719895385722535327222422566909146324787590176419,-6526035763719895383390899952309488961726184762221812189020⟩,
  ⟨12041132178018773117173853398809133701900108470953978262981,12041132178018773118489082394229080501894609307501381881264⟩]
def bs1_3_1_18 : Fin 8 → RI := ![⟨-2548705798147377591564987378335587052986976743482569615062,-2548705798147377591363609802110449277655330075098797565221⟩,
  ⟨5718396375926573091477822570827136721912375173011054096179,5718396375926573091622646409758351433392194976404616815980⟩,
  ⟨-30038001837251185364801876174211301128152394786249211468674,-30038001837251185361768587592554121722228710986945891870534⟩,
  ⟨16579621154975623532621745997925455096269667409381337316494,16579621154975623533744140134170684577337012187524541334312⟩,
  ⟨28372199771959086979298717176516367184146499475554266836227,28372199771959086982513684860585360619686201450318738094260⟩,
  ⟨19098619055043213282540066847814787726471585297971718990543,19098619055043213283919907193335684610485651836833382185280⟩,
  ⟨-5786434468589970303948018294281313125127515066589298192095,-5786434468589970301522228366882496298370641610986263619803⟩,
  ⟨10679884337550793304158376455259940924931831381915617444500,10679884337550793305526716155221890901732548931900368007377⟩]
def bs1_3_1_19 : Fin 8 → RI := ![⟨-2259874093970953813077840594992899688361681865618991166348,-2259874093970953812868134164154857029145937013926107839247⟩,
  ⟨5219473873100766689622337000744083287371913455790614139089,5219473873100766689773150665957705572009799855259128671656⟩,
  ⟨-26552160497238148773734748217644240106281088707288807515109,-26552160497238148770576004656993435253425231876816618413972⟩,
  ⟨14646293226533412913263034010420349237576637840189002669818,14646293226533412914431849688506184650414910899286433907669⟩,
  ⟨25071743490669517626432521164062480274501592706597947076353,25071743490669517629780457964790641155995001180522563017793⟩,
  ⟨16871912172185502723768151340560762942342011469005109179753,16871912172185502725205061047248743008124678164658631915938⟩,
  ⟨-5107715746552166811922964160832153336051985920623584636352,-5107715746552166809396845030936162017313284012390190829432⟩,
  ⟨9430372968296099558772102131873848879713908373301340867233,9430372968296099560197035533256767447954827060161220913719⟩]
def bs1_3_1_20 : Fin 8 → RI := ![⟨-1994322957472917573374758042206110320082835531080280977819,-1994322957472917573156164352748289490450153401152283237179⟩,
  ⟨4740104247958393948129611253109257664445133462626451725523,4740104247958393948286816329595237586348089185400937819503⟩,
  ⟨-23363043632098357931538756579325903637551210591142433305933,-23363043632098357928246146971628622363081759612487266893381⟩,
  ⟨12879321355785310804075062139004287084031444697597371020996,12879321355785310805293411668627341855585957432272656757542⟩,
  ⟨22053759697475780092065561895787770644595696776963445173348,22053759697475780095555382662933598907710569706056899605731⟩,
  ⟨14836671634808452671224549263641319043498050816289431305893,14836671634808452672722354519061569936511361361563035799261⟩,
  ⟨-4487865066014105942536628569583384971567522905732887385715,-4487865066014105939903453714604080729333698488381825842927⟩,
  ⟨8288875869664955227303579094193740217972202982838656481126,8288875869664955228788900494185521181638882220982187372639⟩]
def bs1_3_1 : Fin 21 → Fin 8 → RI := ![bs1_3_1_0,bs1_3_1_1,bs1_3_1_2,bs1_3_1_3,bs1_3_1_4,bs1_3_1_5,bs1_3_1_6,bs1_3_1_7,bs1_3_1_8,bs1_3_1_9,bs1_3_1_10,bs1_3_1_11,bs1_3_1_12,bs1_3_1_13,bs1_3_1_14,bs1_3_1_15,bs1_3_1_16,bs1_3_1_17,bs1_3_1_18,bs1_3_1_19,bs1_3_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_4_0_0 : Fin 8 → RI := ![⟨-2946607129678650591428544195018807550492732897531297656977,-2946607129678650591394943780812306399562399785622954156934⟩,
  ⟨14136712778783721381660678601791686921142657916809929314748,14136712778783721381684842866088363267549300286314056766009⟩,
  ⟨-32790934767767703636327448509989075033396547411061893105837,-32790934767767703635821335790476779557956632794483725859391⟩,
  ⟨17885384950528793585582837468982183683651575361231608276346,17885384950528793585770112083096162664985216264388555407178⟩,
  ⟨30791532522048055462727496202852602995176844702642867309368,30791532522048055463263922590884376748946223591266574065478⟩,
  ⟨20599046934206389869961359134786673184058170937662031435298,20599046934206389870191589372008845168513611864392263137883⟩,
  ⟨-6091195798446442546949508036752844538167733646419604785513,-6091195798446442546544758173976090179809811592209589040744⟩,
  ⟨11367889231890578388315753409197607384483138267928459522102,11367889231890578388544064731422438937449918104523189245689⟩]
def bs1_4_0_1 : Fin 8 → RI := ![⟨-2996792119209006372496461762553425270436778494494742949683,-2996792119209006372461961540337826595291244357605449557961⟩,
  ⟨13845148982440590051550375149575810207912660737719559615091,13845148982440590051575186524899525857012893957938075242159⟩,
  ⟨-33407576737690203817972268574280961544422063480770208042157,-33407576737690203817452602323085494364092906529015419392892⟩,
  ⟨18228415760201261083543407217572746779054441293113335560382,18228415760201261083735696984079146485867065149273740008017⟩,
  ⟨31376214415166384400269599866200332889642974431150025362931,31376214415166384400820391575959006187953967252475424789926⟩,
  ⟨20994450955433894325041294512980943644886606086943711424222,20994450955433894325277690240013124272185667798421001813645⟩,
  ⟨-6214301940696358753705654066280709661886888045556083801655,-6214301940696358753290065135689651591290025514817750316596⟩,
  ⟨11592079910913563287381331410960494498157533041040427636604,11592079910913563287615756835084210247540463444345931855136⟩]
def bs1_4_0_2 : Fin 8 → RI := ![⟨-3038352682020883541822922267296499298399967389566481086369,-3038352682020883541787479662813716924081753136515290946688⟩,
  ⟨13516835903867184956728974275814175395391664800746897475584,13516835903867184956754463380109641116064147048451199387735⟩,
  ⟨-33933088815337609939371551386668524653555045354946868811731,-33933088815337609938837690320816168955322409229519382134848⟩,
  ⟨18522291828576327371074492503935072350198145526417473717674,18522291828576327371272034713889492043882008114434111132818⟩,
  ⟨31875786508310957840086396199930550340852448045070934207490,31875786508310957840652232924093336333828219046770918551369⟩,
  ⟨21333281629481479835863520184259997838255578470223674984984,21333281629481479836106373120170882307525480155880358256191⟩,
  ⟨-6321162420472820012436258791903456567597412539805560310132,-6321162420472820012009317944906144000466687265513255729846⟩,
  ⟨11785540308265998844236214588094276218177914105544424570848,11785540308265998844477043401775546829300674629510729971068⟩]
def bs1_4_0_3 : Fin 8 → RI := ![⟨-3070622276747669362755892112752743675423925850075818109987,-3070622276747669362719461985029303527312225476195306984799⟩,
  ⟨13154120848507711280824264708552554719931024116119410076196,13154120848507711280850464005658064835243468929313071141741⟩,
  ⟨-34359692287493228939570094736968946094939142115211627078710,-34359692287493228939021358911840413392544004161373014009117⟩,
  ⟨18762730308602372896219737273035576024706314072549644604610,18762730308602372896422783523288507489921305871303039414438⟩,
  ⟨32282911025985340105097422149081080496486433725378719797683,32282911025985340105679024557613629978936970516669008527306⟩,
  ⟨21610601203516839270388598010015164855257964910820223267497,21610601203516839270638217461022497862063097666446272815349⟩,
  ⟨-6410259745089891704989138968681573322129064590716607393461,-6410259745089891704550302438088019163467403351130451379167⟩,
  ⟨11945492471597279635794285884327779539482423475892210747930,11945492471597279636041824815789560429164816513027547644442⟩]
def bs1_4_0_4 : Fin 8 → RI := ![⟨-3092991191405296219753855583787781423246391568889216402183,-3092991191405296219716390015451105903381661003330310497561⟩,
  ⟨12759627652633820807927092678130207713661953167247603181921,12759627652633820807954036628574969267362352398775614700253⟩,
  ⟨-34680120198593778594919170615262610283191937136715785387058,-34680120198593778594354838266191632236308215271801969387666⟩,
  ⟨18945714180623152877591061210939953973738708052503856649142,18945714180623152877799878572825854838626611631361442449535⟩,
  ⟨32590719637651547675900638531313779928648654207127776508713,32590719637651547676498771619044336340664983998721186510693⟩,
  ⟨21821776327903326598610063374844906498412135324069816012572,21821776327903326598866777671069544449704718108818773779111⟩,
  ⟨-6480151171634962186239053830075593591213277766681915917597,-6480151171634962185787744404252272307340930184860167557662⟩,
  ⟨12069311250534195946143388505402703742595787117744330103270,12069311250534195946397963148211288887923071274578651523153⟩]
def bs1_4_0_5 : Fin 8 → RI := ![⟨-3104919134803355864581868739229298876261995326693421432291,-3104919134803355864543316803940616358215866864132371299414⟩,
  ⟨12336220119659589524781935530921234086434095279877753584972,12336220119659589524809660759179633564445501634780211333981⟩,
  ⟨-34887753199165571535462622240756227628700389772959345474020,-34887753199165571534881926279942900204522062613673838070529⟩,
  ⟨19067565849250683411214591900907321260968552754564997611206,19067565849250683411429464216476020854356154468866525646063⟩,
  ⟨32792940594216633528744109929612565339341410088769535226292,32792940594216633529359586729136322473920057833200854478981⟩,
  ⟨21962562825316874802263494468611936567892456522667014034878,21962562825316874802527652557628930119455744975350038681032⟩,
  ⟨-6529493866633769085999369760342577890666902279513794318667,-6529493866633769085534973981714284626920287350402384963623⟩,
  ⟨12154571033536654171952254596764594492114732880542810547616,12154571033536654172214210990098824132519917490973557083881⟩]
def bs1_4_0_6 : Fin 8 → RI := ![⟨-3105947693916576323432459052771632735152767770382277608016,-3105947693916576323392766557251716551487255387070624781638⟩,
  ⟨11886962648783630601640957239662675048269741039070239192086,11886962648783630601669502719680509818969880746528505126663⟩,
  ⟨-34976756914543553165944676316732201341517117180130167129263,-34976756914543553165346800447455922940544831825698571892914⟩,
  ⟨19125021881825207634986768621449785488824933901621019432025,19125021881825207635207997941306801381949330275151542469985⟩,
  ⟨32884027548260378735172951625083464584307628905024538214146,32884027548260378735806637325289206837009935829302065901594⟩,
  ⟨22029191856652656521004003277506398574487083218207922786495,22029191856652656521275976491986158082903697303312571786697⟩,
  ⟨-6557071030374376959902134228251069772058935833042933255792,-6557071030374376959423999285748553213949278185814489056429⟩,
  ⟨12199093789271470079413236036942121791605465931446984534721,12199093789271470079682942418501672986577425879587996934113⟩]
def bs1_4_0_7 : Fin 8 → RI := ![⟨-3095712376433604106515450261564084271544764040844180960056,-3095712376433604106474559459328925113330584279212186517578⟩,
  ⟨11415079162951956553660125948357439865302803121860016122467,11415079162951956553689533209423394220142950228580847771793⟩,
  ⟨-34942218269756063928672844657684792435736441990666079767560,-34942218269756063928056919062392617747163145296421971440288⟩,
  ⟨19115307549396923889089867207622492420747035328370916554385,19115307549396923889317775386446311101064432143488626046531⟩,
  ⟨32859287699706127572768576686423534677842334460628939224634,32859287699706127573421393202667633278848799052000293338251⟩,
  ⟨22018455953152088208045936504940845163326229526771238871421,22018455953152088208326120524134010088654758350693347984403⟩,
  ⟨-6561818601226315914497456962120056242404478504879680266374,-6561818601226315914004887242846121412715064773303315445892⟩,
  ⟨12200997640103992778386204933738900631966541442802453117674,12200997640103992778664053684880639901594365838188756632889⟩]
def bs1_4_0_8 : Fin 8 → RI := ![⟨-3073953937724365647673683045805198525863254006220484525582,-3073953937724365647631532319322472897309139312033263760780⟩,
  ⟨10923911448329294793450077429393838342350961605467034084306,10923911448329294793480390784721638796696142101750553373770⟩,
  ⟨-34780277938660357966899445640457048711788082086693563336655,-34780277938660357966264542193184192486477408413821825619301⟩,
  ⟨19036209681386986819070788309239425679377771192251496731870,19036209681386986819305718777308019270661113384220488171560⟩,
  ⟨32715006654433886145888973351557738299072683167459389478345,32715006654433886146561904399996167866800183047958885341315⟩,
  ⟨21927793208372122546197064726525479852568559741981609054237,21927793208372122546485881754128680782978268347524631329328⟩,
  ⟨-6542852083757195358643312120924447288580136516949396461060,-6542852083757195358135565381417650847882891474468417014200⟩,
  ⟨12158745080476473203784458143870053119148259795966852598287,12158745080476473204070867949321797644330781752975932133399⟩]
def bs1_4_0_9 : Fin 8 → RI := ![⟨-3040528678632716147672087690020494752830537791996068267964,-3040528678632716147628611197536541267434372062120699795619⟩,
  ⟨10416877956741267691013234087430725636696594165493297669359,10416877956741267691044500888149054013947497927046660421723⟩,
  ⟨-34488255860356059702584706088486680289896333424876243712633,-34488255860356059701929833035119731499087063381846143865951⟩,
  ⟨18886146215109244136210202190202063849575778008507340067555,18886146215109244136452521921831176226186452333047882791810⟩,
  ⟨32448567166440369625450355601561895756010845873951272827376,32448567166440369626144452337513150954440062823251003283684⟩,
  ⟨21755367769109390948036800401321641644689547916600662117022,21755367769109390948334701585421152018793925798201786383807⟩,
  ⟨-6499492971482747103455134762359617970055180810754768438066,-6499492971482747102931417874279665348139288000318053763859⟩,
  ⟨12071189842141693010505111705474065924912479330502922413738,12071189842141693010800529953108571924120582299663612675904⟩]
def bs1_4_0_10 : Fin 8 → RI := ![⟨-2995417396319706703507880308949427267240468048772408420475,-2995417396319706703463007591711188900835792310658105906108⟩,
  ⟨9897433998744241674182811728651303000346235920376686448437,9897433998744241674215082646276290228811676573832568601734⟩,
  ⟨-34064766596704269758470420122309939426010084277666289379967,-34064766596704269757794516164291611548742414785460121382078⟩,
  ⟨18664230717906557185869796445339712377964087712480772367095,18664230717906557186119898148062991652865608032676593500670⟩,
  ⟨32058558766531164695226674514839811605100157693347982089244,32058558766531164695943061803437212501778550450415953754179⟩,
  ⟨21500144638923154637070665674676591646848795271229477143876,21500144638923154637378133799065907518498283253422932354073⟩,
  ⟨-6431294163069877874860633228203556645354037468731940809530,-6431294163069877874320097446935315976209726745115815001996⟩,
  ⟨11937621305666682755603699316037443189202085413348474807538,11937621305666682755908604765758484189860610970373397380033⟩]
def bs1_4_0_11 : Fin 8 → RI := ![⟨-2938732676198025821266566971919558441360096063699472679175,-2938732676198025821220222516915693453909898651655630990931⟩,
  ⟨9369034078220790531508820855544509958580818443362724372340,9369034078220790531542150196441316587896696571446361349823⟩,
  ⟨-33509821204878642531969271566543992243703921422014850357922,-33509821204878642531271199274576772639781142364360809352692⟩,
  ⟨18370330089878773150929613284552973382733166069218248868335,18370330089878773151187917836219599576123066245580026012822⟩,
  ⟨31544875174588385853900335855750781985722216074883101694403,31544875174588385854640219252725658750977422218145601120301⟩,
  ⟨21161956719774311402176053956241986163997424244456233365504,21161956719774311402493606436522325939257909020458960680731⟩,
  ⟨-6338063703070268692836583901272201163457771972532477395861,-6338063703070268692278319598714585395357823919724573682666⟩,
  ⟨11757805268579630840939318518053271909915965726191745718258,11757805268579630841254224272924342710368160260448007827017⟩]
def bs1_4_0_12 : Fin 8 → RI := ![⟨-2870724229874320833725082112150871139338926608222131909321,-2870724229874320833677184864807995920879936470371151363438⟩,
  ⟨8835096906949670895672799577381132001985286411452685404776,8835096906949670895707245633216079633252522146733881566588⟩,
  ⟨-32824912281675001723669340901723481545375661848719972593884,-32824912281675001722947879375662803317887939809117128048705⟩,
  ⟨18005113626394250673449293684804778983698764557096439257713,18005113626394250673716252849606193710488522125130691999929⟩,
  ⟨30908796360759326613073967352617219538716326880957456022438,30908796360759326613838640884042123512494797744968917342969⟩,
  ⟨20741561975282129918595006444545676180416528237091076608965,20741561975282129918923198667134213094097602561083930439428⟩,
  ⟨-6219886119208314374668760443316825490012115861699995331063,-6219886119208314374091791237832276443828999575608493753926⟩,
  ⟨11532019811451805825685562387345722740431742626306181861364,11532019811451805826011019204768420431111616891267373769772⟩]
def bs1_4_0_13 : Fin 8 → RI := ![⟨-2791782012624671608693702398098973990015015295376375704371,-2791782012624671608644165218577215602369344082742412042478⟩,
  ⟨8298973412291362320240673833521095836204915707516873577169,8298973412291362320276299272275238595139746199183888711601⟩,
  ⟨-32013078914715999110383701158546873935187618093786325990673,-32013078914715999109637537837748012126241460936670472790678⟩,
  ⟨17570091639188053705438025576997277210330740173576642392776,17570091639188053705714125035847702377648681670605333773527⟩,
  ⟨30153052175818604195771270732359224855809595528073173644601,30153052175818604196562125574821068701565910834993313191203⟩,
  ⟨20240688612263882739345533970065120264361836815876404217528,20240688612263882739684963017661079194802207264776542764937⟩,
  ⟨-6077140583436950026485193507976959711057139885867107237168,-6077140583436950025888469714939437057337776643111304888856⟩,
  ⟨11261084961744627892369705201384216721032885181782484756313,11261084961744627892706305187513450199534486531327750166690⟩]
def bs1_4_0_14 : Fin 8 → RI := ![⟨-2702436894440723704001031476273048336403136218841666321448,-2702436894440723703949760532090964019344499057609032551780⟩,
  ⟨7763917838259831170270045713393314452540749557962803797009,7763917838259831170306918016165743715605653066808089526687⟩,
  ⟨-31078948461495435253696517341765206335734787650340753658836,-31078948461495435252924238856378983918151334642707139489751⟩,
  ⟨17067641910046756859878747653971427144348914182975303811634,17067641910046756860164510389761783883643401061123480923865⟩,
  ⟨29281864624091016665420421115772670248012601787612925380275,29281864624091016666238955293039518805021861308927544917718⟩,
  ⟨19662066254616999696491032885777653672901872730352507690058,19662066254616999696842341699099963002163793279933148927365⟩,
  ⟨-5910515099981492050170087042659715717438093581191628880773,-5910515099981492049552478358027618047342708963237696564749⟩,
  ⟨10946384850105611866910225787776426924590914366635253183075,10946384850105611867258606524570960145208672288448430797730⟩]
def bs1_4_0_15 : Fin 8 → RI := ![⟨-2603358710681490424635435564441608859399083596105055848426,-2603358710681490424582329651101212598273321935951627065744⟩,
  ⟨7233061863316165991798972499922381171712896220361414123193,7233061863316165991837164449513381294900905673407293402935⟩,
  ⟨-30028752380209772956761967037943660932829396081829351372735,-30028752380209772955962048975699880852547714355993564581421⟩,
  ⟨16501022388388724884019153551637322332360932273434569494713,16501022388388724884315143635786350949673655769046246313414⟩,
  ⟨28300966113780870678221239357239846034428094336200095250733,28300966113780870679069068586396944932463018322175883340701⟩,
  ⟨19009441233717900482994705220067588602168430953863721992747,19009441233717900483358587252936225373238816248031973684846⟩,
  ⟨-5721015927622603874808343212105132704525031095972774976887,-5721015927622603874168630528685066145131696135452579009197⟩,
  ⟨10589881094212989283736284065508129751413234953899330235226,10589881094212989284097133227012914028358422430764893263987⟩]
def bs1_4_0_16 : Fin 8 → RI := ![⟨-2495351580781800644483199268352394238877414794777415992794,-2495351580781800644428149048402470054094415406238522844274⟩,
  ⟨6709391534532202464241322028439218452215331080300616263707,6709391534532202464280912256589806399889995255236630932180⟩,
  ⟨-28870313763130167513388270353106382628584963972488860197415,-28870313763130167512559065797558222853658413753876776044311⟩,
  ⟨15874368748658427887312010658765163198971119453761020795805,15874368748658427887618837492361319773651252844388989152731⟩,
  ⟨27217591396774471561230616222174874252419504492505465971713,27217591396774471562109486061883175746963533012411498970479⟩,
  ⟨18287574349412699619582668734279666254829347767166676582886,18287574349412699619959873167558344301155667597084288970167⟩,
  ⟨-5509971482657886687027770361674744135714213982130997496056,-5509971482657886686364636602894657616444503827925650398848⟩,
  ⟨10194116240160279912313770433289803621392961129647261353434,10194116240160279912687830956121674361892984123511830765684⟩]
def bs1_4_0_17 : Fin 8 → RI := ![⟨-2379346454571494935825418274161671325896925752865793759491,-2379346454571494935768305423697037977216612747832702980607⟩,
  ⟨6195726755441113677780069098924942416301450780372925477443,6195726755441113677821142700125293093997664266023957346328⟩,
  ⟨-27613004775771499288535756391110450030573213795646217691599,-27613004775771499287675483065615024033816410505613581514012⟩,
  ⟨15192675698295600016301366097433696503462068157527615827224,15192675698295600016619689168290227936397765230086399010463⟩,
  ⟨26040441406257612690027029586454864958024739431597525864848,26040441406257612690938829062982950777832719356012699109878⟩,
  ⟨17502219769811839449073532046376637589001055298535206889077,17502219769811839449464869636164905415612642878920809151917⟩,
  ⟨-5279030049361982433961377470053702798953228188472231161708,-5279030049361982433273397308711496953954474982977717635334⟩,
  ⟨9762206248024890676969900936709781488896060901824434078257,9762206248024890677357976819506244212488862586518104187950⟩]
def bs1_4_0_18 : Fin 8 → RI := ![⟨-2256390923189952331862383585554311190506530185067033269408,-2256390923189952331803079835456858009595640868679836252799⟩,
  ⟨5694703062201664856947364946985971085534219184031547056700,5694703062201664856990014167981947002618077278925044321124⟩,
  ⟨-26267672878811999295511045804827499710947102161693211357497,-26267672878811999294617771631054043505444512200407815546649⟩,
  ⟨14461761271717775686448513511118170772765329988219953334911,14461761271717775686779047737493404316678713358570846980365⟩,
  ⟨24779617813271609090757434716023408491722477239224864381686,24779617813271609091704211629713801864890712193584483334539⟩,
  ⟨16660084136899459068829486251655022327605912622243150937725,16660084136899459069235835898710369360935616482200381590437⟩,
  ⟨-5030150750081273454123757434273445734151168220180492701166,-5030150750081273453409385743347234419758569696861175757279⟩,
  ⟨9297821230802252257285615995866219052572367748058509772459,9297821230802252257688578813952960341376632187051008862692⟩]
def bs1_4_0_19 : Fin 8 → RI := ![⟨-2127636412443176109799229623590581854705415965431231490971,-2127636412443176109737595680819921434940288702313871473329⟩,
  ⟨5208755469264845301907821645303469293856010315044354299014,5208755469264845301952146660867347473803429788233498712785⟩,
  ⟨-24846535492255786599336551811032116333821290222308890995621,-24846535492255786598408178660694394690861667551605302201885⟩,
  ⟨13688213755550654517285442095908984141133320577050174127772,13688213755550654517628963838779736338610673794139030242952⟩,
  ⟨23446527842716272968710462035496239498909780044691660480662,23446527842716272969694440182224501973895076976179640019558⟩,
  ⟨15768765423521545421239140752711937876795131266143459331638,15768765423521545421661456893772637298458016047807675909583⟩,
  ⟨-4765587397726040419220072054118580336495640980878206733406,-4765587397726040418477630912657232368779506541553274995298⟩,
  ⟨8805153943841297346880603663812213358649721743752511179347,8805153943841297347299399898920997942598715132191216943371⟩]
def bs1_4_0_20 : Fin 8 → RI := ![⟨-1994322957460916469935434756311969585960391259697199416292,-1994322957460916469871319088179299972644923212477861693654⟩,
  ⟨4740104247216011481456021512876210476240983050547399772193,4740104247216011481502131300115180834721084159824390952340⟩,
  ⟨-23363043631558774657622495630679340164634965839284159019941,-23363043631558774656656741013426219617463922409560090317619⟩,
  ⟨12879321355474918051457117888472328784295040577166343667646,12879321355474918051814471727481429504618737108286141645852⟩,
  ⟨22053759696964865022549017956741960408359195763127167244794,22053759696964865023572616536831621079577923174958025414890⟩,
  ⟨14836671634388721179653749264603998040532247685843864760554,14836671634388721180093070202551810655123633359887903003947⟩,
  ⟨-4487865065556224006333562921758284945668343287647987724904,-4487865065556224005561226970270672379829088568524193537207⟩,
  ⟨8288875869124359902812998974827675648960152335176706581730,8288875869124359903248658275829093772582763682156890036943⟩]
def bs1_4_0 : Fin 21 → Fin 8 → RI := ![bs1_4_0_0,bs1_4_0_1,bs1_4_0_2,bs1_4_0_3,bs1_4_0_4,bs1_4_0_5,bs1_4_0_6,bs1_4_0_7,bs1_4_0_8,bs1_4_0_9,bs1_4_0_10,bs1_4_0_11,bs1_4_0_12,bs1_4_0_13,bs1_4_0_14,bs1_4_0_15,bs1_4_0_16,bs1_4_0_17,bs1_4_0_18,bs1_4_0_19,bs1_4_0_20]
def bs1_4_1_0 : Fin 8 → RI := ![⟨-2946607129678650591428544195018807550492732897531297656979,-2946607129678650591394943780812306399562399785622954156934⟩,
  ⟨14136712778783721381660678601791686921142657916809929314748,14136712778783721381684842866088363267549300286314056766009⟩,
  ⟨-32790934767767703636327448509989075033396547411061893105837,-32790934767767703635821335790476779557956632794483725859391⟩,
  ⟨17885384950528793585582837468982183683651575361231608276346,17885384950528793585770112083096162664985216264388555407178⟩,
  ⟨30791532522048055462727496202852602995176844702642867309368,30791532522048055463263922590884376748946223591266574065478⟩,
  ⟨20599046934206389869961359134786673184058170937662031435298,20599046934206389870191589372008845168513611864392263137883⟩,
  ⟨-6091195798446442546949508036752844538167733646419604785515,-6091195798446442546544758173976090179809811592209589040744⟩,
  ⟨11367889231890578388315753409197607384483138267928459522102,11367889231890578388544064731422438937449918104523189245689⟩]
def bs1_4_1_1 : Fin 8 → RI := ![⟨-2871329645383116919828017555730527256899466039557554555439,-2871329645383116919793067429510379819646331390177786217874⟩,
  ⟨14574058473298418376825163113574943036947267409373901600522,14574058473298418376850298044412178337394296054949611315495⟩,
  ⟨-31865971812883953363880548711076002824192136809264352805587,-31865971812883953363354105694038949791418358689921253454911⟩,
  ⟨17370838736020092338634460117507707952328802033903831375087,17370838736020092338829257460210318021880917366565964481123⟩,
  ⟨29914509682370562056392792725240658836665229210829591222695,29914509682370562056950767095862781907247028998505836985132⟩,
  ⟨20005940902365133187332207832780254528550087036618923421655,20005940902365133187571686304717439477270959140469743154496⟩,
  ⟨-5906536585071568236831547594182502420947412762507362871738,-5906536585071568236410539129684292494231079993504870516530⟩,
  ⟨11031603213356101039708215253704950419347320258194345607932,11031603213356101039945697728778108266938325944855237073935⟩]
def bs1_4_1_2 : Fin 8 → RI := ![⟨-2776647200971006371809212525161273656349271602327470352851,-2776647200971006371772816894846786039119007460319146751138⟩,
  ⟨14928718282794999401389678426880243429347129696702715896633,14928718282794999401415852914633636913811525516085653621189⟩,
  ⟨-30735966600381241455881190095378202960729524267520590630155,-30735966600381241455332973894125529541339849758796386769456⟩,
  ⟨16745694353592238368219742726019697791422914884776478938651,16745694353592238368422596702186037287326080149362543233980⟩,
  ⟨28845989792752118780176147755989311680826137461197254415763,28845989792752118780757199417725513655997477705190046738025⟩,
  ⟨19285544839369058880123209690214599271258211912071953444643,19285544839369058880372592764771361382280758369266113146371⟩,
  ⟨-5685324631131420293656119217825644313207674592599365315712,-5685324631131420293217698242274089553469356007996676301462⟩,
  ⟨10626174061062887671126613742796806318489971404092296538180,10626174061062887671373918267950299457683481937206909791773⟩]
def bs1_4_1_3 : Fin 8 → RI := ![⟨-2664809373554636933572751154147071021690389266621498316029,-2664809373554636933534805564993115169464939343810627861758⟩,
  ⟨15192770051399271960610431354662262305268363150120080658942,15192770051399271960637720519598257699115168885204481950687⟩,
  ⟨-29427172287365906993053310605316491487475046265181881836527,-29427172287365906992481747850103530454986290350642463936509⟩,
  ⟨16024406412044447662191338698198738191675909012761925081137,16024406412044447662402831494761667718090966824284317900433⟩,
  ⟨27610737845493196044223985807247424603417597997754514914513,27610737845493196044829782366969912121773627100534903227253⟩,
  ⟨18454523661027203518967409068265929679268631101364822823585,18454523661027203519227412469974875201104550272082106732538⟩,
  ⟨-5432681474441028053686945709621495538017847176129694034415,-5432681474441028053229853963416334131974208202958572242041⟩,
  ⟨10160977364194231585486535079483922937695447826713683640868,10160977364194231585744371413854221401769156782803515971256⟩]
def bs1_4_1_4 : Fin 8 → RI := ![⟨-2538353438995461266941252267913545340545122805001945676423,-2538353438995461266901642540986748692085933519678366482906⟩,
  ⟨15359691560550991974587857315236453306522629786438837179969,15359691560550991974616343270923817735866766225924323498012⟩,
  ⟨-27968432804064681419984873822144148018794331642602978010740,-27968432804064681419388244670765298834109397016849611233132⟩,
  ⟨15222775271365020984403797377040521895481463509063750935170,15222775271365020984624565379479098006182201634328021219379⟩,
  ⟨26235895397996428306929752246323019766336821794546452124011,26235895397996428307562116556346636207798936718561020596689⟩,
  ⟨17531083324326638003539778789346577371258988920183160744187,17531083324326638003811184872935794566083130130902902718968⟩,
  ⟨-5154107073542868404136646168409512262886993843430777223489,-5154107073542868403659508254589255325733526546593825419083⟩,
  ⟨9646162271943991853271739293217214078530186900144344775166,9646162271943991853540883270789208843955952649148896081427⟩]
def bs1_4_1_5 : Fin 8 → RI := ![⟨-2400008755875917902308047392906536613029088177296683110812,-2400008755875917902266648389790843749973905850248550625739⟩,
  ⟨15424638184487002611631951827960781504277851125648038318023,15424638184487002611661724569651953959654213896745772400628⟩,
  ⟨-26390151254762416170695947270471172463256207601708842126385,-26390151254762416170072366801399172959422658216584523074597⟩,
  ⟨14357388166477865000852265765991398606579236546455368841139,14357388166477865001083006443343895191296178322052788034437⟩,
  ⟨24750015130071614258461466336281396128900750819598682726149,24750015130071614259122396215684008111735716232977313298013⟩,
  ⟨16534327111950872185703974085806360663757776915535183705463,16534327111950872185987640300444232844523659516597936868469⟩,
  ⟨-4855288751500572303025034477155827539209646866074080319358,-4855288751500572302526342981067679051096992708415202642260⟩,
  ⟨9092296585518466483975294412918568800623766185197336383254,9092296585518466484256596336222887821307660744551478347413⟩]
def bs1_4_1_6 : Fin 8 → RI := ![⟨-2252599622676038366182967785391499494739674276701437896049,-2252599622676038366139641970375496232747450728442215794224⟩,
  ⟨15384688564575649544216325487225886848777500374613475402536,15384688564575649544247483925882489994565372192065054963998⟩,
  ⟨-24723275635711693051538505719927158985280550420804284975120,-24723275635711693050885902274982344250623307258968328918405⟩,
  ⟨13445073334379347187027051609346460632659066653019045486137,13445073334379347187268531527975094717929329070390493738303⟩,
  ⟨23182114580104266906809112905205345129264618811870033465713,23182114580104266907500804094326427684214068175009968709924⟩,
  ⟨15483627827106422850244702577781096184344128037987859462394,15483627827106422850541571318977278913198230493380787022838⟩,
  ⟨-4541921127760999008380704532385450892306852630100798326778,-4541921127760999007858802701824919451724924360532327660580⟩,
  ⟨8510026709414439172065706614023746848393554839609975484465,8510026709414439172360101023924446178606122870858961002319⟩]
def bs1_4_1_7 : Fin 8 → RI := ![⟨-2098951405596579328828157429951760856507580536515599263540,-2098951405596579328782753194814583303470673653761513671471⟩,
  ⟨15239039388478774309486179583935533449360513174848561153512,15239039388478774309518832750984832361485693345405110668506⟩,
  ⟨-22998345680359335770260856001991015884184299625080645394739,-22998345680359335769576945953105975739467196238419105507151⟩,
  ⟨12502390023851817335469919014067495448528685390067061285964,12502390023851817335722983174599056008870292603493925227146⟩,
  ⟨21560789353819328586078033281072571429523855906609873324585,21560789353819328586802906186095534150648139705155716590304⟩,
  ⟨14398042049870639658362156808882448817727106552405806383472,14398042049870639658673266897064750144947134141457406650467⟩,
  ⟨-4219543610426158872850637584478416630744800381948645475497,-4219543610426158872303699150096617947230937635069025891999⟩,
  ⟨7909765659155661709586179789716264364348852443143952892156,7909765659155661709894696848316459654588549782559112019518⟩]
def bs1_4_1_8 : Fin 8 → RI := ![⟨-1941804222515908105643190808137151002273018281026731350195,-1941804222515908105595540517306066481957631969765806227798⟩,
  ⟨14989130493236443595755925465018383782788694180872469116205,14989130493236443595790193918208837723936597090148767326014⟩,
  ⟨-21244637778869147243051046741991111637602801616736535985410,-21244637778869147242333305046019723847274823040343439403948⟩,
  ⟨11545173428315054747418316304767355231432493987269811227356,11545173428315054747683899037564835475764672992901954658993⟩,
  ⟨19913419584428956845875664180824455640911975309611170140738,19913419584428956846636395082590068019645767461815904038783⟩,
  ⟨13295788100490320531192586483018825368876712746522959691672,13295788100490320531519086558125048055289728943119862738770⟩,
  ⟨-3893400187940964780358487752993397654219134070603247531850,-3893400187940964779784493380307566257813692660252591987944⟩,
  ⟨7301419379681096734946064709600413218628811486177705032676,7301419379681096735269843483193337163256312346604640232188⟩]
def bs1_4_1_9 : Fin 8 → RI := ![⟨-1783737682085341665985860171762594876034401993027351071193,-1783737682085341665935777876764781114996410966523350719478⟩,
  ⟨14638684178650978204609760186404448193784109251887377714236,14638684178650978204645777653493520776554984162261292266787⟩,
  ⟨-19489436412485791577635137783642033611976103834974209507973,-19489436412485791576880763555848575432019417072759921978953⟩,
  ⟨10588148982530148182734428749918648538707101828418357173929,10588148982530148183013566453768293779476363237830602240199⟩,
  ⟨18265495473747221437190900307893366540045301357534751345731,18265495473747221437990457850389726245452156852888584063256⟩,
  ⟨12193804030461474810013605087500461240823236192720264263114,12193804030461474810356769269568358944954907591945796259599⟩,
  ⟨-3568324480936037419860084291373276511521933725434104968656,-3568324480936037419256794049102344892425159406288336131464⟩,
  ⟨6694158530645416668633671919357610352433770299379498192343,6694158530645416668973975908489220364420544230590767887837⟩]
def bs1_4_1_10 : Fin 8 → RI := ![⟨-1627109203151593264364150156610957137326215105492978714576,-1627109203151593264311428918003821116011937459774613311219⟩,
  ⟨14193647982505884435531447177025058138790865491340518464018,14193647982505884435569362481754985197199224526874525792804⟩,
  ⟨-17757451150254245198826247533019585077487733137943559326951,-17757451150254245198032123708137643163514466382284938208579⟩,
  ⟨9644625491885832467486025103717956685285210890911320162360,9644625491885832467779871172266278674767475895708425221338⟩,
  ⟨16640079050430072339995601269377314473251207286059489756672,16640079050430072340837289214785575642259535216554965889287⟩,
  ⟨11107396265220084412213024509220474776615777905185415993510,11107396265220084412574270748537081474163771588018522245360⟩,
  ⟨-3248651429150866081084868086382001058575818815597130184399,-3248651429150866080449789186477160356116230885097956860390⟩,
  ⟨6096239885146600744923356128806131312191859126982305743150,6096239885146600745281591465480242654545022869929252928629⟩]
def bs1_4_1_11 : Fin 8 → RI := ![⟨-1474007380329555859777053558271678775128820648147103523235,-1474007380329555859721462300122981259909946820439661230810⟩,
  ⟨13662037765513644567972542265120907777686445608923607241960,13662037765513644568012521589368595865153274896599222841399⟩,
  ⟨-16070388704662935113380286468532706583336798057345228109157,-16070388704662935112542932420765378203588390014403445177694⟩,
  ⟨8726271577244649439780140882849710738645356015149693459180,8726271577244649440089983236411800948960270970968570910228⟩,
  ⟨15057410496155250079767723793236123976939914958093730055469,15057410496155250080655231239759802304440101217604669855581⟩,
  ⟨10049983850881608219694399400194738323103793606029558252953,10049983850881608220075311030417200536338069066101933851196⟩,
  ⟨-2938155650913954598377213611539830797442639749170937444076,-2938155650913954597707562518320164858907613094791968712028⟩,
  ⟨5514878719233493723119108083738315409636479260960928204328,5514878719233493723496844904897219307457316166540827750098⟩]
def bs1_4_1_12 : Fin 8 → RI := ![⟨-1326220818680950737781802184872578995446169837508960283972,-1326220818680950737723081990743087161599387472138036544820⟩,
  ⟨13053686664652592100524667144724368100304710540297531983701,13053686664652592100566896692303499686891141408365228517307⟩,
  ⟨-14446680488425858605656279877300301990657164875511882104780,-14446680488425858604771795627844508645100853252466690439892⟩,
  ⟨7842975231317920174925857369906838064001546244349563879275,7842975231317920175253139100105313138800111586997907435602⟩,
  ⟨13534659092424857780235238335767073497076549462950576517560,13534659092424857781172698851803266924564746336665873411025⟩,
  ⟨9032937949420076471698518244713817681179154128453960381284,9032937949420076472100869362818215500466119248474616007298⟩,
  ⟨-2640015417180763952548726479981154041210646479507205558303,-2640015417180763951841384291620811212686817605358194966573⟩,
  ⟨4956171120049046927013701266207596209312862531118652690883,4956171120049046927412698882144950951058027063537752715627⟩]
def bs1_4_1_13 : Fin 8 → RI := ![⟨-1185221922712966473679389103745617065220202844855425982966,-1185221922712966473617248843175452397693411529485917075787⟩,
  ⟨12379913787624672251379346401651261617372778544686705390448,12379913787624672251424035543593156566618704332751680542834⟩,
  ⟨-12901358110648263935555016497261374302624281221994223617412,-12901358110648263934619016837414960263269527666400386849409⟩,
  ⟨7002782157013560826344542561016960251833688721970767186673,7002782157013560826690886306912472514441471824895253673800⟩,
  ⟨12085811518892414294866512056588322393654230266100916561643,12085811518892414295858573503323256721433804910208381808610⟩,
  ⟨8065511562744751862867196167618249155443101417811458719551,8065511562744751863292981601241066782092086916774850611642⟩,
  ⟨-2356800297802610839604428977939826965689472927625835496923,-2356800297802610838855888743217191549458306279784741436881⟩,
  ⟨4425063054611143654430597709365924192234947303650804322245,4425063054611143654852834321297451251177015837180021640534⟩]
def bs1_4_1_14 : Fin 8 → RI := ![⟨-1052164357283011777119396333459328171367369562006851260461,-1052164357283011777053507483072271867000648478380467549406⟩,
  ⟨11653133029394617859605862965539308744478879387524478474731,11653133029394617859653247964576899241849295107461957301830⟩,
  ⟨-11446062725027094637222814104292470246774221847812089756488,-11446062725027094636230350587338952610986880434176258799222⟩,
  ⟨6211905200588084091578607381982322688467650237566217657260,6211905200588084091945844195065737454691729585135702288638⟩,
  ⟨10721684269538184163344342823573717254144516606831534919590,10721684269538184164396250035401334591877015110417224455753⟩,
  ⟨7154850668930358688592751872554621510653701463524093552697,7154850668930358689044222665816748508336834160657822136665⟩,
  ⟨-2090479842895783750469888950638052555651340131699289776002,-2090479842895783749676193284070259297209795645151416800016⟩,
  ⟨3925361359261674228573445196368185672253624480089409450237,3925361359261674229021153086489635413486227307780135895302⟩]
def bs1_4_1_15 : Fin 8 → RI := ![⟨-927892336979187904206512672590775086314354567156884710179,-927892336979187904136503164617186693921766994515275438037⟩,
  ⟨10886426271372363201103670199951963871918686353434392341815,10886426271372363201154018634450910651814943475222925173902⟩,
  ⟨-10089169364781045860747699829674280138598485778560100915721,-10089169364781045859693168113072879840735381207248734882084⟩,
  ⟨5474794736488505355431164780776303270454399796982460256782,5474794736488505355821368410721552049529295045046279699819⟩,
  ⟨9450042588286134517994984373477408258586137354304014243623,9450042588286134519112677365557506609435720035886645569907⟩,
  ⟨6306075170947524111272599280314077395247839987323626621483,6306075170947524111752304843778239288680384592282812704172⟩,
  ⟨-1842450154192751555215798877429439403667319303053587554464,-1842450154192751554372465858712548348825565551260238343535⟩,
  ⟨3459780571515542095189311521996591084952036808560975612842,3459780571515542095665018852131144032935540731676816895012⟩]
def bs1_4_1_16 : Fin 8 → RI := ![⟨-812959554988159032481355693469264520557311015536852208276,-812959554988159032406802584696461116915214546409189776426⟩,
  ⟨10093106348504820993175100405705775611409807550943210245075,10093106348504820993228716441903655759151329306332846975469⟩,
  ⟨-8836004456293021089090828577818028417320700197405904539789,-8836004456293021087967857997854822417399594332592065419202⟩,
  ⟨4794258352439164167660769123942666766525175322832092719520,4794258352439164168076296878802134076260931255040431404693⟩,
  ⟨8275805641605183291239710308703741628850479246891675899276,8275805641605183292429941316247392461252134878253200571306⟩,
  ⟨5522416342794693032981105273525305472706235891655564465766,5522416342794693033491943616591529890464229389097144324048⟩,
  ⟨-1613574884993150245575378812355157645929223713276112174406,-1613574884993150244677313676699043502015695132930154470561⟩,
  ⟨3030018753487265014654337861938122735077944802166172118480,3030018753487265015160918487256594832058489146596014770417⟩]
def bs1_4_1_17 : Fin 8 → RI := ![⟨-707655418611813928152963430776516569206337693949546807072,-707655418611813928073384133789773973177980642238487996053⟩,
  ⟨9286293838272004434228771303531892537365366841549848509070,9286293838272004434286002001728610345619607288944263183017⟩,
  ⟨-7689133515642276451755511957211743305634495741125712789507,-7689133515642276450556833447876021422641984503459537597234⟩,
  ⟨4171617584603187011042425680804788788888117338884351389338,4171617584603187011485967300393688715278597930915212814651⟩,
  ⟨7201316571338648507014368530620586505185633081514725273107,7201316571338648508284842001025000219545748102637180107342⟩,
  ⟨4805396770726552105997665529273899623165621304808009815088,4805396770726552106542943343768166818852833584743000824854⟩,
  ⟨-1404237085344782484561144974455538503809309027238055098859,-1404237085344782483602534484302724559231980011313981002099⟩,
  ⟨2636855143912132300759800537630482535366596375340270324917,2636855143912132301300533589457321812342278767188500913333⟩]
def bs1_4_1_18 : Fin 8 → RI := ![⟨-612036286917441922479944524376140569280479523577994613855,-612036286917441922394786276330893204967208735702762591841⟩,
  ⟨8478528643239249006095695488579164061287114421306660437912,8478528643239249006156938376834412071622529338656500181294⟩,
  ⟨-6648696378935098919157509883746421072584793774020802682594,-6648696378935098917874797348080796508709417972551796187619⟩,
  ⟨3606889652776580129258376090258226115184765167312001295122,3606889652776580129733012442800766597111022258782975340152⟩,
  ⟨6226656406902912492756411089031510157763346587412003799065,6226656406902912494115951811607710589206949313261893678895⟩,
  ⟨4155039006624503361390948636548813852900370535256366519633,4155039006624503361974453456758387611946235015697567684871⟩,
  ⟨-1214398371041083410933438917310973866562517625711888560885,-1214398371041083409907624503394424976402924414658744982090⟩,
  ⟨2280262583227409237517264303443200735877493066480506312982,2280262583227409238095905747854802509844613907875354439806⟩]
def bs1_4_1_19 : Fin 8 → RI := ![⟨-525959568775623790636249158178140497900674484242867095454,-525959568775623790544876314157785262507039243514383969753⟩,
  ⟨7681432834994481117970190271173058642742621348826617397820,7681432834994481118035902483487122605586272679291464322260⟩,
  ⟨-5712768896663518727678033584729800566489164449867644088633,-5712768896663518726301712498581410140988460111326777421930⟩,
  ⟨3098982990603505046489077219601276896676306960588931900226,3098982990603505046998351123224136668580788770418219507195⟩,
  ⟨5349982287139944683832818492270659640688448161076994321962,5349982287139944685291574458188465164573503800428574321626⟩,
  ⟨3570090104798649875070568589806866160554992201258215790736,3570090104798649875696655858467970163965543152849026647670⟩,
  ⟨-1043662113611396071275398751951772705411946113008654092725,-1043662113611396070174723449357951786822899069942069643019⟩,
  ⟨1959528113306162065683280284110783529273135787145699430912,1959528113306162066304149262248518971293312721849604056436⟩]
def bs1_4_1_20 : Fin 8 → RI := ![⟨-449118795258812180841790757135661595520494416327170620889,-449118795258812180743469376009275848331060448589336868034⟩,
  ⟨6905435916024075032388204138851492559563526119171438480947,6905435916024075032458913500487160008389704483505795229148⟩,
  ⟨-4877732604229114784289122032090115023653551415485280111529,-4877732604229114782808137265619581946494849137345888421614⟩,
  ⟨2645896747037150062820577771584389253373389503557524180142,2645896747037150063368579906279947377708222772888734029524⟩,
  ⟨4567872842970593414161456114931708304175386658188929716512,4567872842970593415731144602063158296535704145236147949028⟩,
  ⟨3048250798646115760999958129929970748388729087604299805112,3048250798646115761673656816022115656505762870906874547776⟩,
  ⟨-891337841560001923167876190691815615535763463302328698056,-891337841560001921983498960436299867394576427795606515397⟩,
  ⟨1673376032538433444152281244442663254544437802985564681956,1673376032538433444820364810007580036036715789995198669330⟩]
def bs1_4_1 : Fin 21 → Fin 8 → RI := ![bs1_4_1_0,bs1_4_1_1,bs1_4_1_2,bs1_4_1_3,bs1_4_1_4,bs1_4_1_5,bs1_4_1_6,bs1_4_1_7,bs1_4_1_8,bs1_4_1_9,bs1_4_1_10,bs1_4_1_11,bs1_4_1_12,bs1_4_1_13,bs1_4_1_14,bs1_4_1_15,bs1_4_1_16,bs1_4_1_17,bs1_4_1_18,bs1_4_1_19,bs1_4_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs1_5_0_0 : Fin 8 → RI := ![⟨-131587480702055847553296911351804815793742116057753537024,-131587480702055847548576203569038974503107360166538805748⟩,
  ⟨6615160235433789647905209889417838062729156954275809251421,6615160235433789647908604860379468395971753557550991973604⟩,
  ⟨-1442242746807410599991692534443923015669485057637475817126,-1442242746807410599920585962981072136752913559299239963500⟩,
  ⟨783628801166012795002434298586263221711567096693474353569,783628801166012795028745543528978110007760857016391688450⟩,
  ⟨1351668816280008548469632871183185432563757030553685951901,1351668816280008548544998377372916379623901539984287150705⟩,
  ⟨903645452556859809247263742520682606302449429738982010704,903645452556859809279610060217913992662868240531012566948⟩,
  ⟨-267094008327254985208940152689482777853773311648174972724,-267094008327254985152074608844215626789797151517423552226⟩,
  ⟨499158347052195404862733432982234631908443640045929107982,499158347052195404894810151712441432233901586821083482184⟩]
def bs1_5_0_1 : Fin 8 → RI := ![⟨-153498876476980012100355258302225596102678980818630014339,-153498876476980012095436756091989378282531038313177737359⟩,
  ⟨7319087782836330694959901655610892588796641650538753969283,7319087782836330694963438873533884865268082754539119772792⟩,
  ⟨-1681165879311828357830442486510581526378182379914750936413,-1681165879311828357756356598335312858301519632748995496148⟩,
  ⟨913299588517936386462911223530580079583483012303875348601,913299588517936386490324891641462974943198394307948493845⟩,
  ⟨1575463358520737173485539763429699840629878715354714138971,1575463358520737173564063032784086008933679357136879608484⟩,
  ⟨1053147334492528472258002822186755764097130782081816213382,1053147334492528472291704428473003110439369833202335018656⟩,
  ⟨-311148189990037206479031718790634046856753414668485164637,-311148189990037206419783547550441271195888763770485256930⟩,
  ⟨581595700076906892400736287584111609375312288073194635567,581595700076906892434156998890912460589096480696697024177⟩]
def bs1_5_0_10 : Fin 8 → RI := ![⟨-389770589766637150809864371456819025547946932208782550540,-389770589766637150802299355555724103770574078820358999760⟩,
  ⟨10895551493448562739633625438119288276695730018605150637451,10895551493448562739639065937825934171728997489556277140269⟩,
  ⟨-4242947512815845640472322460560489862789110181077082233607,-4242947512815845640358372949483418061172400816364958233264⟩,
  ⟨2302152125937528591757429066481331516446742176636634754105,2302152125937528591799593291749416823334017646163330278763⟩,
  ⟨3973802218568179843909430021850345507266806028950474741205,3973802218568179844030204549516489079945218005667400514601⟩,
  ⟨2653658638375712629837151039162754509629681163836912550919,2653658638375712629888986572940601277610520713986565891038⟩,
  ⟨-779952395862694162323682358644883079495779815218040649447,-779952395862694162232554340731197907472757438086481000823⟩,
  ⟨1461147639449029131490293779336813722882912032571825694210,1461147639449029131541697276103457674501229332333860725761⟩]
def bs1_5_0_11 : Fin 8 → RI := ![⟨-412286139709617560014240228041200851055703157713138102385,-412286139709617560006241375983233732255664442904661563039⟩,
  ⟨10830007623838382697710765294548593376659297249245321147958,10830007623838382697716517794324344139956696218020241957927⟩,
  ⟨-4485708440055636655350941946589519420779077792745716603611,-4485708440055636655230457694725602599218609663549821972746⟩,
  ⟨2433644293895472488662339178298897191174185803136607958548,2433644293895472488706921424320517610134843482967535754168⟩,
  ⟨4200982793708523498785444565532138847499657249327066828623,4200982793708523498913145232893745312487949831441335116638⟩,
  ⟨2805074940149135755954545221266751581417662379400685701812,2805074940149135756009353402962243105821418601795933400867⟩,
  ⟨-823919419564975367138630442139426010031649820264324992315,-823919419564975367042276443264543506751554976529054236064⟩,
  ⟨1543947826914661049957376938467723218251306774473646682596,1543947826914661050011728306828861239643181375822506522859⟩]
def bs1_5_0_12 : Fin 8 → RI := ![⟨-432092489621879104465529407187166877731376018100905485622,-432092489621879104457056052219304043889953702909255432306⟩,
  ⟨10666938050998948096082417075878424604032480897904748606454,10666938050998948096088510821855838001376521085406313159305⟩,
  ⟨-4698999355027574991960839004856502257379148353094987061097,-4698999355027574991833207461394941814410369881654174266465⟩,
  ⟨2549158204646675301778594279927094827036913754830577229752,2549158204646675301825821206124803097107417636928221288673⟩,
  ⟨4400574455937745694377631617641470053664225099847003381463,4400574455937745694512907664297253399677737843318954296059⟩,
  ⟨2938055164788294576025526227265437237231337627124070604090,2938055164788294576083585705711287753087645091270377068376⟩,
  ⟨-862424741548526830986584259649148812967919631489245144136,-862424741548526830884514408985881821914035172257606911101⟩,
  ⟨1616549051862078915685494066153259847611793995391938992871,1616549051862078915743069632468919404245480904658667455565⟩]
def bs1_5_0_13 : Fin 8 → RI := ![⟨-448682265542424605313789491923633580047499973969056829947,-448682265542424605304795923387534935625234818322645768748⟩,
  ⟨10412448160030378833293322131627134535641100030408141561034,10412448160030378833299789997342298604066375284611402482819⟩,
  ⟨-4877407346099866295024441089820487926330180685340848745094,-4877407346099866294888973729153839598987788956716234799144⟩,
  ⟨2645768519677293469823105853583813320612222252324590689821,2645768519677293469873232231992593036050613953147486463680⟩,
  ⟨4567517179551123104574044450319645561002259872964434333276,4567517179551123104717625641182492894931240005134036139846⟩,
  ⟨3049232018516796435688159574693639866694234699943059180445,3049232018516796435749783559591686252062804390170178460210⟩,
  ⟨-894499674485315612361906320039866302983946188536348121086,-894499674485315612253569987986704346984478390466736365041⟩,
  ⟨1677118831181533219107471052250698693463087350679648814242,1677118831181533219168581415693286180021073507546383232204⟩]
def bs1_5_0_14 : Fin 8 → RI := ![⟨-461608606242779349450606383185855861369168697386568731425,-461608606242779349441041080815748501845288957622832427938⟩,
  ⟨10074639712101231688733492725868008797280532183000308671508,10074639712101231688740371762927214761658809331208233570916⟩,
  ⟨-5016177313839856654337694432591149808299809379011406140275,-5016177313839856654193615220779517749369715861699646843967⟩,
  ⟨2720906105547114802631805460202519127236200160278503820477,2720906105547114802685118443172186467974617090929487016416⟩,
  ⟨4697366296307425564267960084084251090148337742590035596268,4697366296307425564420668933719230810737985172603245577559⟩,
  ⟨3135649918750056796283372279541375272681767489589479391955,3135649918750056796348913788058016025162332974294491835280⟩,
  ⟨-919299444436749040831401393247563980216954417891169988612,-919299444436749040716177967797547669523919374715724017768⟩,
  ⟨1724054526156944146252142985933605137379206607576407381937,1724054526156944146317138221354200979204756245484944159498⟩]
def bs1_5_0_15 : Fin 8 → RI := ![⟨-470504701793031136469133940296953210627045144391980875986,-470504701793031136458938670952977864695381847166533052224⟩,
  ⟨9663246036062871142990149122824452530746992336303945999773,9663246036062871142997481210502559903934514798071930028205⟩,
  ⟨-5111416725875990083061073947738887063280259766196139190332,-5111416725875990082907505736881742573324322324327454403679⟩,
  ⟨2772468289558799763561660316609209720894516868546373666261,2772468289558799763618484471233841255021240576202872806970⟩,
  ⟨4786483573481217567698623810074764793747342973634548501080,4786483573481217567861390003237676096869946369170587028355⟩,
  ⟨3194891784151943961981934468769432919481890192808520214860,3194891784151943962051792514724092410483215217932992834181⟩,
  ⟨-936138912367481987611424497107724781407832523863656173529,-936138912367481987488612503117880210686737722271428756514⟩,
  ⟨1756051609783784328187656801530978758397121712995947361303,1756051609783784328256932597062365593904462942293365449955⟩]
def bs1_5_0_16 : Fin 8 → RI := ![⟨-475100870588158545960299102309523650890196856116713129265,-475100870588158545949407849785077820425351557699263056781⟩,
  ⟨9189227003856406139199452215474197316747596028745661149779,9189227003856406139207284830360449430016620151874902325880⟩,
  ⟨-5160273590566037931413052143464855849180600407129278777010,-5160273590566037931249000551717736610804493113506145066312⟩,
  ⟨2798914639526781929325622969028349506564599748075074490588,2798914639526781929386326241951231017019622188662369328410⟩,
  ⟨4832203267186392784662714227646014730471269834859362905442,4832203267186392784836591704774590891781434541343635670353⟩,
  ⟨3225189046018767625216787146183451407941427241152031203068,3225189046018767625291414073015008372367762356441653981544⟩,
  ⟨-944523108465817704362491309407786154654940420390507860320,-944523108465817704231295517081535529249867703140641444613⟩,
  ⟨1772162421156279173524583108081804754416239756791639485362,1772162421156279173598588036986338255681035332051758973407⟩]
def bs1_5_0_17 : Fin 8 → RI := ![⟨-475238076232834816428223704516416609350784451752498115499,-475238076232834816416561395836183251318683806242331660743⟩,
  ⟨8664344569617200637948572051985083947554343908700108150582,8664344569617200637956959183985835259232054449678364032815⟩,
  ⟨-5161076523277278118122099179258434190612382526137624986052,-5161076523277278117946433405451343967438709556807054089601⟩,
  ⟨2799342315840506923671700511489814584769962031752550042913,2799342315840506923736701327983941527999264958743339074674⟩,
  ⟨4832962799245896621153121262209120544826633831944907188588,4832962799245896621339308553914848661544698193212547063029⟩,
  ⟨3225508054836563001477637977812685553399376497700391980205,3225508054836563001557548185992930772519032576167541542050⟩,
  ⟨-944170757719312724361490403106681259228147725769616194640,-944170757719312724221006485007455247817507480873528842276⟩,
  ⟨1771841830033682265563421782183146514759061046884158760475,1771841830033682265642665957525265781520159960853733606687⟩]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
def localBoundary (n : ℕ) : ℚ :=
  if hn : n<31 then ![-5/2,0,1/2,1,2,3,7/2,4,11/2,7,8,9,21/2,12,25/2,13,29/2,16,35/2,19,20,21,23,25,26,27,55/2,28,59/2,31,67/2] ⟨n,hn⟩ else 0
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_FarSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
def farK (i : Fin 5) : ℝ :=
  (301/100)*finiteCurvatureEnvelope i+(3/1000000000)*tailCurvatureEnvelope i+(3/500)*(2/1000)
end AtomicTriangular.Construction
end

end OAI
end


