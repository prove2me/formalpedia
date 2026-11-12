-- Prove2me | Definitions.Def_OAIQ229C015
-- name    : OAIQ229C015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:42:48.826197+00:00
-- url     : https://prove2.me/theorems/e3f22b7c-fba0-485c-967c-349081a30bfc
-- title:
--   Definitions bundle OAIQ229C015 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 771 declarations of OpenAI's Lean: 714 definitions, 5 instances and 52 theorems. The definitions and types are `OAI.CoarseAssembly.explicitBoundaryMetric4`, `OAI.CoarseAssembly.explicitBoundaryMetric5`, `OAI.CoarseAssembly.explicitPersistenceComponent`, `OAI.CoarseAssembly.filledDiscCenter`, `OAI.CoarseAssembly.filledDiscContraction`, `OAI.CoarseAssembly.graphRipsCocycle`, `OAI.CoarseAssembly.ripsCharge`, `OAI.CoarseAssembly.secondDiagonal`, `OAI.NuclearUltrapower.IntegralGroup`, `OAI.NuclearUltrapower.SL3Certificate.gram`, `OAI.NuclearUltrapower.SOS.addHead`, `OAI.NuclearUltrapower.SOS.basis`, `OAI.NuclearUltrapower.SOS.compress`, `OAI.NuclearUltrapower.SOS.delta`, `OAI.NuclearUltrapower.SOS.gramData`, `OAI.NuclearUltrapower.SOS.intL1`, `OAI.NuclearUltrapower.SOS.label102`, `OAI.NuclearUltrapower.SOS.label103`, `OAI.NuclearUltrapower.SOS.label1030`, `OAI.NuclearUltrapower.SOS.label104`, `OAI.NuclearUltrapower.SOS.label105`, `OAI.NuclearUltrapower.SOS.label106`, `OAI.NuclearUltrapower.SOS.label109`, `OAI.NuclearUltrapower.SOS.label1096`, `OAI.NuclearUltrapower.SOS.label1098`, `OAI.NuclearUltrapower.SOS.label1100`, `OAI.NuclearUltrapower.SOS.label1102`, `OAI.NuclearUltrapower.SOS.label1103`, `OAI.NuclearUltrapower.SOS.label1105`, `OAI.NuclearUltrapower.SOS.label1107`, `OAI.NuclearUltrapower.SOS.label1109`, `OAI.NuclearUltrapower.SOS.label1113`, `OAI.NuclearUltrapower.SOS.label112`, `OAI.NuclearUltrapower.SOS.label113`, `OAI.NuclearUltrapower.SOS.label114`, `OAI.NuclearUltrapower.SOS.label1141`, `OAI.NuclearUltrapower.SOS.label1142`, `OAI.NuclearUltrapower.SOS.label1144`, `OAI.NuclearUltrapower.SOS.label1146`, `OAI.NuclearUltrapower.SOS.label1148` and 674 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_BoundaryWalks`, `CoarseAssembly_CongruenceElementary`, `CoarseAssembly_ExplicitBoundaryConclusion`, `CoarseAssembly_ExplicitPersistence`, `CoarseAssembly_FilledDisc`, `CoarseAssembly_FiniteWindingIndex`, `CoarseAssembly_GraphMetric`, `CoarseAssembly_LatticeHat`, `CoarseAssembly_RipsWindingTest`, `CoarseAssembly_ShortLoops`, `NuclearUltrapower_DyadicGroup`, `NuclearUltrapower_IntegralCertificate`, `NuclearUltrapower_Model`, `NuclearUltrapower_SOSCertificate`, `NuclearUltrapower_SOSResidual`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C000`, `OAIQ229C001`, `OAIQ229C002`, `OAIQ229C003`, `OAIQ229C004`, `OAIQ229C005`, `OAIQ229C006`, `OAIQ229C007` and `OAIQ229C008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C022` and `OAIQ229C023`; the statements `OAI_NuclearUltrapower_SOS_eval_buckets`, `OAI.NuclearUltrapower.SOS.eval_buckets_ca`, `OAI_NuclearUltrapower_SOS_gramData_roots`, `OAI.NuclearUltrapower.SOS.gramData_roots_ca`, `OAI_NuclearUltrapower_SOS_intL1_flatten`, `OAI.NuclearUltrapower.SOS.intL1_flatten_ca`, `OAI_NuclearUltrapower_SOS_row_partition_0`, `OAI.NuclearUltrapower.SOS.row_partition_0_ca`, `OAI_NuclearUltrapower_SOS_row_partition_1`, `OAI_NuclearUltrapower_SOS_row_partition_10`, `OAI.NuclearUltrapower.SOS.row_partition_100_ca`, `OAI.NuclearUltrapower.SOS.row_partition_101_ca`, `OAI.NuclearUltrapower.SOS.row_partition_102_ca`, `OAI.NuclearUltrapower.SOS.row_partition_103_ca`, `OAI.NuclearUltrapower.SOS.row_partition_104_ca`, `OAI_NuclearUltrapower_SOS_row_partition_105`, `OAI.NuclearUltrapower.SOS.row_partition_105_ca`, `OAI_NuclearUltrapower_SOS_row_partition_106`, `OAI.NuclearUltrapower.SOS.row_partition_106_ca`, `OAI_NuclearUltrapower_SOS_row_partition_107`, `OAI.NuclearUltrapower.SOS.row_partition_107_ca`, `OAI_NuclearUltrapower_SOS_row_partition_108`, `OAI.NuclearUltrapower.SOS.row_partition_108_ca`, `OAI_NuclearUltrapower_SOS_row_partition_109`, `OAI.NuclearUltrapower.SOS.row_partition_109_ca`, `OAI.NuclearUltrapower.SOS.row_partition_10_ca`, `OAI_NuclearUltrapower_SOS_row_partition_11`, `OAI_NuclearUltrapower_SOS_row_partition_110`, `OAI.NuclearUltrapower.SOS.row_partition_110_ca`, `OAI_NuclearUltrapower_SOS_row_partition_111`, `OAI.NuclearUltrapower.SOS.row_partition_111_ca`, `OAI_NuclearUltrapower_SOS_row_partition_112`, `OAI.NuclearUltrapower.SOS.row_partition_112_ca`, `OAI_NuclearUltrapower_SOS_row_partition_113`, `OAI.NuclearUltrapower.SOS.row_partition_113_ca`, `OAI_NuclearUltrapower_SOS_row_partition_114`, `OAI.NuclearUltrapower.SOS.row_partition_114_ca`, `OAI_NuclearUltrapower_SOS_row_partition_115`, `OAI.NuclearUltrapower.SOS.row_partition_115_ca`, `OAI_NuclearUltrapower_SOS_row_partition_116`, `OAI.NuclearUltrapower.SOS.row_partition_116_ca`, `OAI_NuclearUltrapower_SOS_row_partition_117`, `OAI.NuclearUltrapower.SOS.row_partition_117_ca`, `OAI_NuclearUltrapower_SOS_row_partition_118`, `OAI.NuclearUltrapower.SOS.row_partition_118_ca`, `OAI_NuclearUltrapower_SOS_row_partition_119`, `OAI.NuclearUltrapower.SOS.row_partition_119_ca`, `OAI.NuclearUltrapower.SOS.row_partition_11_ca`, `OAI_NuclearUltrapower_SOS_row_partition_12`, `OAI_NuclearUltrapower_SOS_row_partition_120`, `OAI.NuclearUltrapower.SOS.row_partition_120_ca`, `OAI_NuclearUltrapower_SOS_row_partition_121`, `OAI.NuclearUltrapower.SOS.row_partition_121_ca`, `OAI_NuclearUltrapower_SOS_row_partition_122`, `OAI.NuclearUltrapower.SOS.row_partition_122_ca`, `OAI.NuclearUltrapower.SOS.row_partition_12_ca`, `OAI_NuclearUltrapower_SOS_row_partition_13`, `OAI.NuclearUltrapower.SOS.row_partition_13_ca`, `OAI_NuclearUltrapower_SOS_row_partition_14`, `OAI.NuclearUltrapower.SOS.row_partition_14_ca`, `OAI_NuclearUltrapower_SOS_row_partition_15`, `OAI.NuclearUltrapower.SOS.row_partition_15_ca`, `OAI_NuclearUltrapower_SOS_row_partition_16`, `OAI.NuclearUltrapower.SOS.row_partition_16_ca`, `OAI_NuclearUltrapower_SOS_row_partition_17`, `OAI.NuclearUltrapower.SOS.row_partition_17_ca`, `OAI_NuclearUltrapower_SOS_row_partition_18`, `OAI.NuclearUltrapower.SOS.row_partition_18_ca`, `OAI_NuclearUltrapower_SOS_row_partition_19`, `OAI.NuclearUltrapower.SOS.row_partition_19_ca`, `OAI.NuclearUltrapower.SOS.row_partition_1_ca`, `OAI_NuclearUltrapower_SOS_row_partition_2`, `OAI_NuclearUltrapower_SOS_row_partition_20`, `OAI.NuclearUltrapower.SOS.row_partition_20_ca`, `OAI_NuclearUltrapower_SOS_row_partition_21`, `OAI.NuclearUltrapower.SOS.row_partition_21_ca`, `OAI_NuclearUltrapower_SOS_row_partition_22`, `OAI.NuclearUltrapower.SOS.row_partition_22_ca`, `OAI_NuclearUltrapower_SOS_row_partition_23`, `OAI.NuclearUltrapower.SOS.row_partition_23_ca`, `OAI_NuclearUltrapower_SOS_row_partition_24`, `OAI.NuclearUltrapower.SOS.row_partition_24_ca`, `OAI_NuclearUltrapower_SOS_row_partition_25`, `OAI.NuclearUltrapower.SOS.row_partition_25_ca`, `OAI_NuclearUltrapower_SOS_row_partition_26`, `OAI.NuclearUltrapower.SOS.row_partition_26_ca`, `OAI_NuclearUltrapower_SOS_row_partition_27`, `OAI.NuclearUltrapower.SOS.row_partition_27_ca`, `OAI_NuclearUltrapower_SOS_row_partition_28`, `OAI.NuclearUltrapower.SOS.row_partition_28_ca`, `OAI_NuclearUltrapower_SOS_row_partition_29`, `OAI.NuclearUltrapower.SOS.row_partition_29_ca`, `OAI.NuclearUltrapower.SOS.row_partition_2_ca`, `OAI_NuclearUltrapower_SOS_row_partition_3`, `OAI_NuclearUltrapower_SOS_row_partition_30`, `OAI.NuclearUltrapower.SOS.row_partition_30_ca`, `OAI_NuclearUltrapower_SOS_row_partition_31`, `OAI.NuclearUltrapower.SOS.row_partition_31_ca`, `OAI_NuclearUltrapower_SOS_row_partition_32`, `OAI.NuclearUltrapower.SOS.row_partition_32_ca`, `OAI_NuclearUltrapower_SOS_row_partition_33`, `OAI.NuclearUltrapower.SOS.row_partition_33_ca`, `OAI_NuclearUltrapower_SOS_row_partition_34`, `OAI.NuclearUltrapower.SOS.row_partition_34_ca`, `OAI_NuclearUltrapower_SOS_row_partition_35`, `OAI.NuclearUltrapower.SOS.row_partition_35_ca`, `OAI_NuclearUltrapower_SOS_row_partition_36`, `OAI.NuclearUltrapower.SOS.row_partition_36_ca`, `OAI_NuclearUltrapower_SOS_row_partition_37`, `OAI.NuclearUltrapower.SOS.row_partition_37_ca`, `OAI_NuclearUltrapower_SOS_row_partition_38`, `OAI.NuclearUltrapower.SOS.row_partition_38_ca`, `OAI_NuclearUltrapower_SOS_row_partition_39`, `OAI.NuclearUltrapower.SOS.row_partition_39_ca`, `OAI.NuclearUltrapower.SOS.row_partition_3_ca`, `OAI_NuclearUltrapower_SOS_row_partition_4`, `OAI_NuclearUltrapower_SOS_row_partition_40`, `OAI.NuclearUltrapower.SOS.row_partition_40_ca`, `OAI_NuclearUltrapower_SOS_row_partition_41`, `OAI.NuclearUltrapower.SOS.row_partition_41_ca`, `OAI_NuclearUltrapower_SOS_row_partition_42`, `OAI.NuclearUltrapower.SOS.row_partition_42_ca`, `OAI_NuclearUltrapower_SOS_row_partition_43`, `OAI.NuclearUltrapower.SOS.row_partition_43_ca`, `OAI_NuclearUltrapower_SOS_row_partition_44`, `OAI.NuclearUltrapower.SOS.row_partition_44_ca`, `OAI_NuclearUltrapower_SOS_row_partition_45`, `OAI.NuclearUltrapower.SOS.row_partition_45_ca`, `OAI_NuclearUltrapower_SOS_row_partition_46`, `OAI.NuclearUltrapower.SOS.row_partition_46_ca`, `OAI_NuclearUltrapower_SOS_row_partition_47`, `OAI.NuclearUltrapower.SOS.row_partition_47_ca`, `OAI_NuclearUltrapower_SOS_row_partition_48`, `OAI.NuclearUltrapower.SOS.row_partition_48_ca`, `OAI_NuclearUltrapower_SOS_row_partition_49`, `OAI.NuclearUltrapower.SOS.row_partition_49_ca`, `OAI.NuclearUltrapower.SOS.row_partition_4_ca`, `OAI_NuclearUltrapower_SOS_row_partition_5`, `OAI_NuclearUltrapower_SOS_row_partition_50`, `OAI.NuclearUltrapower.SOS.row_partition_50_ca`, `OAI_NuclearUltrapower_SOS_row_partition_51`, `OAI.NuclearUltrapower.SOS.row_partition_51_ca`, `OAI_NuclearUltrapower_SOS_row_partition_52`, `OAI.NuclearUltrapower.SOS.row_partition_52_ca`, `OAI_NuclearUltrapower_SOS_row_partition_53`, `OAI.NuclearUltrapower.SOS.row_partition_53_ca`, `OAI_NuclearUltrapower_SOS_row_partition_54`, `OAI.NuclearUltrapower.SOS.row_partition_54_ca`, `OAI_NuclearUltrapower_SOS_row_partition_55`, `OAI.NuclearUltrapower.SOS.row_partition_55_ca`, `OAI_NuclearUltrapower_SOS_row_partition_56`, `OAI.NuclearUltrapower.SOS.row_partition_56_ca`, `OAI_NuclearUltrapower_SOS_row_partition_57`, `OAI.NuclearUltrapower.SOS.row_partition_57_ca`, `OAI_NuclearUltrapower_SOS_row_partition_58`, `OAI.NuclearUltrapower.SOS.row_partition_58_ca`, `OAI_NuclearUltrapower_SOS_row_partition_59`, `OAI.NuclearUltrapower.SOS.row_partition_59_ca`, `OAI.NuclearUltrapower.SOS.row_partition_5_ca`, `OAI_NuclearUltrapower_SOS_row_partition_6`, `OAI_NuclearUltrapower_SOS_row_partition_60`, `OAI_NuclearUltrapower_SOS_row_partition_61`, `OAI_NuclearUltrapower_SOS_row_partition_62`, `OAI.NuclearUltrapower.SOS.row_partition_62_ca`, `OAI_NuclearUltrapower_SOS_row_partition_63`, `OAI_NuclearUltrapower_SOS_row_partition_64`, `OAI_NuclearUltrapower_SOS_row_partition_65`, `OAI_NuclearUltrapower_SOS_row_partition_66`, `OAI_NuclearUltrapower_SOS_row_partition_67`, `OAI_NuclearUltrapower_SOS_row_partition_68`, `OAI_NuclearUltrapower_SOS_row_partition_69`, `OAI_NuclearUltrapower_SOS_support_compress_iff` and `OAI.NuclearUltrapower.SOS.support_compress_iff_ca`; the proofs of `OAI_NuclearUltrapower_SOS_eval_buckets`, `OAI.NuclearUltrapower.SOS.eval_buckets_ca`, `OAI_NuclearUltrapower_SOS_gramData_roots`, `OAI.NuclearUltrapower.SOS.gramData_roots_ca`, `OAI_NuclearUltrapower_SOS_intL1_flatten`, `OAI.NuclearUltrapower.SOS.intL1_flatten_ca`, `OAI_NuclearUltrapower_SOS_row_partition_0`, `OAI.NuclearUltrapower.SOS.row_partition_0_ca`, `OAI_NuclearUltrapower_SOS_row_partition_1`, `OAI_NuclearUltrapower_SOS_row_partition_10`, `OAI.NuclearUltrapower.SOS.row_partition_100_ca`, `OAI.NuclearUltrapower.SOS.row_partition_101_ca`, `OAI.NuclearUltrapower.SOS.row_partition_102_ca`, `OAI.NuclearUltrapower.SOS.row_partition_103_ca`, `OAI.NuclearUltrapower.SOS.row_partition_104_ca`, `OAI_NuclearUltrapower_SOS_row_partition_105`, `OAI.NuclearUltrapower.SOS.row_partition_105_ca`, `OAI_NuclearUltrapower_SOS_row_partition_106`, `OAI.NuclearUltrapower.SOS.row_partition_106_ca`, `OAI_NuclearUltrapower_SOS_row_partition_107`, `OAI.NuclearUltrapower.SOS.row_partition_107_ca`, `OAI_NuclearUltrapower_SOS_row_partition_108`, `OAI.NuclearUltrapower.SOS.row_partition_108_ca`, `OAI_NuclearUltrapower_SOS_row_partition_109`, `OAI.NuclearUltrapower.SOS.row_partition_109_ca`, `OAI.NuclearUltrapower.SOS.row_partition_10_ca`, `OAI_NuclearUltrapower_SOS_row_partition_11`, `OAI_NuclearUltrapower_SOS_row_partition_110`, `OAI.NuclearUltrapower.SOS.row_partition_110_ca`, `OAI_NuclearUltrapower_SOS_row_partition_111`, `OAI.NuclearUltrapower.SOS.row_partition_111_ca`, `OAI_NuclearUltrapower_SOS_row_partition_112`, `OAI.NuclearUltrapower.SOS.row_partition_112_ca`, `OAI_NuclearUltrapower_SOS_row_partition_113`, `OAI.NuclearUltrapower.SOS.row_partition_113_ca`, `OAI_NuclearUltrapower_SOS_row_partition_114`, `OAI.NuclearUltrapower.SOS.row_partition_114_ca`, `OAI_NuclearUltrapower_SOS_row_partition_115`, `OAI.NuclearUltrapower.SOS.row_partition_115_ca`, `OAI_NuclearUltrapower_SOS_row_partition_116`, `OAI.NuclearUltrapower.SOS.row_partition_116_ca`, `OAI_NuclearUltrapower_SOS_row_partition_117`, `OAI.NuclearUltrapower.SOS.row_partition_117_ca`, `OAI_NuclearUltrapower_SOS_row_partition_118`, `OAI.NuclearUltrapower.SOS.row_partition_118_ca`, `OAI_NuclearUltrapower_SOS_row_partition_119`, `OAI.NuclearUltrapower.SOS.row_partition_119_ca`, `OAI.NuclearUltrapower.SOS.row_partition_11_ca`, `OAI_NuclearUltrapower_SOS_row_partition_12`, `OAI_NuclearUltrapower_SOS_row_partition_120`, `OAI.NuclearUltrapower.SOS.row_partition_120_ca`, `OAI_NuclearUltrapower_SOS_row_partition_121`, `OAI.NuclearUltrapower.SOS.row_partition_121_ca`, `OAI_NuclearUltrapower_SOS_row_partition_122`, `OAI.NuclearUltrapower.SOS.row_partition_122_ca`, `OAI.NuclearUltrapower.SOS.row_partition_12_ca`, `OAI_NuclearUltrapower_SOS_row_partition_13`, `OAI.NuclearUltrapower.SOS.row_partition_13_ca`, `OAI_NuclearUltrapower_SOS_row_partition_14`, `OAI.NuclearUltrapower.SOS.row_partition_14_ca`, `OAI_NuclearUltrapower_SOS_row_partition_15`, `OAI.NuclearUltrapower.SOS.row_partition_15_ca`, `OAI_NuclearUltrapower_SOS_row_partition_16`, `OAI.NuclearUltrapower.SOS.row_partition_16_ca`, `OAI_NuclearUltrapower_SOS_row_partition_17`, `OAI.NuclearUltrapower.SOS.row_partition_17_ca`, `OAI_NuclearUltrapower_SOS_row_partition_18`, `OAI.NuclearUltrapower.SOS.row_partition_18_ca`, `OAI_NuclearUltrapower_SOS_row_partition_19`, `OAI.NuclearUltrapower.SOS.row_partition_19_ca`, `OAI.NuclearUltrapower.SOS.row_partition_1_ca`, `OAI_NuclearUltrapower_SOS_row_partition_2`, `OAI_NuclearUltrapower_SOS_row_partition_20`, `OAI.NuclearUltrapower.SOS.row_partition_20_ca`, `OAI_NuclearUltrapower_SOS_row_partition_21`, `OAI.NuclearUltrapower.SOS.row_partition_21_ca`, `OAI_NuclearUltrapower_SOS_row_partition_22`, `OAI.NuclearUltrapower.SOS.row_partition_22_ca`, `OAI_NuclearUltrapower_SOS_row_partition_23`, `OAI.NuclearUltrapower.SOS.row_partition_23_ca`, `OAI_NuclearUltrapower_SOS_row_partition_24`, `OAI.NuclearUltrapower.SOS.row_partition_24_ca`, `OAI_NuclearUltrapower_SOS_row_partition_25`, `OAI.NuclearUltrapower.SOS.row_partition_25_ca`, `OAI_NuclearUltrapower_SOS_row_partition_26`, `OAI.NuclearUltrapower.SOS.row_partition_26_ca`, `OAI_NuclearUltrapower_SOS_row_partition_27`, `OAI.NuclearUltrapower.SOS.row_partition_27_ca`, `OAI_NuclearUltrapower_SOS_row_partition_28`, `OAI.NuclearUltrapower.SOS.row_partition_28_ca`, `OAI_NuclearUltrapower_SOS_row_partition_29`, `OAI.NuclearUltrapower.SOS.row_partition_29_ca`, `OAI.NuclearUltrapower.SOS.row_partition_2_ca`, `OAI_NuclearUltrapower_SOS_row_partition_3`, `OAI_NuclearUltrapower_SOS_row_partition_30`, `OAI.NuclearUltrapower.SOS.row_partition_30_ca`, `OAI_NuclearUltrapower_SOS_row_partition_31`, `OAI.NuclearUltrapower.SOS.row_partition_31_ca`, `OAI_NuclearUltrapower_SOS_row_partition_32`, `OAI.NuclearUltrapower.SOS.row_partition_32_ca`, `OAI_NuclearUltrapower_SOS_row_partition_33`, `OAI.NuclearUltrapower.SOS.row_partition_33_ca`, `OAI_NuclearUltrapower_SOS_row_partition_34`, `OAI.NuclearUltrapower.SOS.row_partition_34_ca`, `OAI_NuclearUltrapower_SOS_row_partition_35`, `OAI.NuclearUltrapower.SOS.row_partition_35_ca`, `OAI_NuclearUltrapower_SOS_row_partition_36`, `OAI.NuclearUltrapower.SOS.row_partition_36_ca`, `OAI_NuclearUltrapower_SOS_row_partition_37`, `OAI.NuclearUltrapower.SOS.row_partition_37_ca`, `OAI_NuclearUltrapower_SOS_row_partition_38`, `OAI.NuclearUltrapower.SOS.row_partition_38_ca`, `OAI_NuclearUltrapower_SOS_row_partition_39`, `OAI.NuclearUltrapower.SOS.row_partition_39_ca`, `OAI.NuclearUltrapower.SOS.row_partition_3_ca`, `OAI_NuclearUltrapower_SOS_row_partition_4`, `OAI_NuclearUltrapower_SOS_row_partition_40`, `OAI.NuclearUltrapower.SOS.row_partition_40_ca`, `OAI_NuclearUltrapower_SOS_row_partition_41`, `OAI.NuclearUltrapower.SOS.row_partition_41_ca`, `OAI_NuclearUltrapower_SOS_row_partition_42`, `OAI.NuclearUltrapower.SOS.row_partition_42_ca`, `OAI_NuclearUltrapower_SOS_row_partition_43`, `OAI.NuclearUltrapower.SOS.row_partition_43_ca`, `OAI_NuclearUltrapower_SOS_row_partition_44`, `OAI.NuclearUltrapower.SOS.row_partition_44_ca`, `OAI_NuclearUltrapower_SOS_row_partition_45`, `OAI.NuclearUltrapower.SOS.row_partition_45_ca`, `OAI_NuclearUltrapower_SOS_row_partition_46`, `OAI.NuclearUltrapower.SOS.row_partition_46_ca`, `OAI_NuclearUltrapower_SOS_row_partition_47`, `OAI.NuclearUltrapower.SOS.row_partition_47_ca`, `OAI_NuclearUltrapower_SOS_row_partition_48`, `OAI.NuclearUltrapower.SOS.row_partition_48_ca`, `OAI_NuclearUltrapower_SOS_row_partition_49`, `OAI.NuclearUltrapower.SOS.row_partition_49_ca`, `OAI.NuclearUltrapower.SOS.row_partition_4_ca`, `OAI_NuclearUltrapower_SOS_row_partition_5`, `OAI_NuclearUltrapower_SOS_row_partition_50`, `OAI.NuclearUltrapower.SOS.row_partition_50_ca`, `OAI_NuclearUltrapower_SOS_row_partition_51`, `OAI.NuclearUltrapower.SOS.row_partition_51_ca`, `OAI_NuclearUltrapower_SOS_row_partition_52`, `OAI.NuclearUltrapower.SOS.row_partition_52_ca`, `OAI_NuclearUltrapower_SOS_row_partition_53`, `OAI.NuclearUltrapower.SOS.row_partition_53_ca`, `OAI_NuclearUltrapower_SOS_row_partition_54`, `OAI.NuclearUltrapower.SOS.row_partition_54_ca`, `OAI_NuclearUltrapower_SOS_row_partition_55`, `OAI.NuclearUltrapower.SOS.row_partition_55_ca`, `OAI_NuclearUltrapower_SOS_row_partition_56`, `OAI.NuclearUltrapower.SOS.row_partition_56_ca`, `OAI_NuclearUltrapower_SOS_row_partition_57`, `OAI.NuclearUltrapower.SOS.row_partition_57_ca`, `OAI_NuclearUltrapower_SOS_row_partition_58`, `OAI.NuclearUltrapower.SOS.row_partition_58_ca`, `OAI_NuclearUltrapower_SOS_row_partition_59`, `OAI.NuclearUltrapower.SOS.row_partition_59_ca`, `OAI.NuclearUltrapower.SOS.row_partition_5_ca`, `OAI_NuclearUltrapower_SOS_row_partition_6`, `OAI_NuclearUltrapower_SOS_row_partition_60`, `OAI_NuclearUltrapower_SOS_row_partition_61`, `OAI_NuclearUltrapower_SOS_row_partition_62`, `OAI.NuclearUltrapower.SOS.row_partition_62_ca`, `OAI_NuclearUltrapower_SOS_row_partition_63`, `OAI_NuclearUltrapower_SOS_row_partition_64`, `OAI_NuclearUltrapower_SOS_row_partition_65`, `OAI_NuclearUltrapower_SOS_row_partition_66`, `OAI_NuclearUltrapower_SOS_row_partition_67`, `OAI_NuclearUltrapower_SOS_row_partition_68`, `OAI_NuclearUltrapower_SOS_row_partition_69`, `OAI_NuclearUltrapower_SOS_support_compress_iff` and `OAI.NuclearUltrapower.SOS.support_compress_iff_ca`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.TransferInstance
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C000
import Definitions.Def_OAIQ229C001
import Definitions.Def_OAIQ229C002
import Definitions.Def_OAIQ229C003
import Definitions.Def_OAIQ229C004
import Definitions.Def_OAIQ229C005
import Definitions.Def_OAIQ229C006
import Definitions.Def_OAIQ229C007
import Definitions.Def_OAIQ229C008

section
-- module Solutions.Q229_CA.Compat
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section Y
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ShortLoops
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Short loops and the Rips edge cocycle

The combinatorial step in §4 of the coarse Novikov manuscript. The only
hypothesis on the charge is vanishing on short closed graph walks, exactly
the output required from the manuscript's small-loop lemma. This is a
conditional combinatorial result, not an assumption about analytic K-homology.
-/

namespace CoarseAssembly

variable {V : Type*} {G : SimpleGraph V}

/-- Vanishing short loops makes the charge independent of the chosen short
path. The two paths are compared by concatenating one with the reverse of
the other, exactly as in Proposition 4.1. -/
theorem walkCharge_eq_of_short_loops (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 2 * r → walkCharge a p = 0)
    {u v : V} (p q : G.Walk u v) (hp : p.length ≤ r) (hq : q.length ≤ r) :
    walkCharge a p = walkCharge a q := by
  have hlen : (p.append q.reverse).length ≤ 2 * r := by
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    omega
  have hz := hloop u (p.append q.reverse) hlen
  rw [walkCharge_append, walkCharge_reverse a ha] at hz
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hz)

@[simp] theorem shortestWalk_length (hG : G.Connected) (u v : V) :
    (shortestWalk hG u v).length = G.dist u v :=
  (hG.exists_walk_length_eq_dist u v).choose_spec

/-- The charge assigned to an oriented Rips edge, extended to all vertex
pairs by choosing shortest graph walks. -/
noncomputable def ripsCharge (hG : G.Connected) (a : V → V → ℤ) (u v : V) : ℤ :=
  walkCharge a (shortestWalk hG u v)

theorem ripsCharge_eq_walkCharge (hG : G.Connected) (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 2 * r → walkCharge a p = 0)
    {u v : V} (p : G.Walk u v) (hp : p.length ≤ r) :
    ripsCharge hG a u v = walkCharge a p := by
  apply walkCharge_eq_of_short_loops a ha r hloop
  · simpa only [shortestWalk_length] using (G.dist_le p).trans hp
  · exact hp

/-- The Rips charge is antisymmetric whenever loops of length at most `2r`
have zero charge. -/
theorem ripsCharge_antisymm (hG : G.Connected) (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 2 * r → walkCharge a p = 0)
    {u v : V} (huv : G.dist u v ≤ r) :
    ripsCharge hG a v u = -ripsCharge hG a u v := by
  rw [ripsCharge_eq_walkCharge hG a ha r hloop (shortestWalk hG u v).reverse
    (by simpa using huv), walkCharge_reverse a ha]
  rfl

/-- Every triangle in the Rips complex has zero total charge, assuming
vanishing of graph loops of length at most `3r`. This is the cocycle identity
needed for the circle-valued winding test. -/
theorem ripsCharge_triangle (hG : G.Connected) (a : V → V → ℤ) (r : ℕ)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 3 * r → walkCharge a p = 0)
    {u v w : V} (huv : G.dist u v ≤ r) (hvw : G.dist v w ≤ r)
    (hwu : G.dist w u ≤ r) :
    ripsCharge hG a u v + ripsCharge hG a v w + ripsCharge hG a w u = 0 := by
  have hlen : (((shortestWalk hG u v).append (shortestWalk hG v w)).append
      (shortestWalk hG w u)).length ≤ 3 * r := by
    simp only [SimpleGraph.Walk.length_append, shortestWalk_length]
    omega
  have hz := hloop u (((shortestWalk hG u v).append (shortestWalk hG v w)).append
    (shortestWalk hG w u)) hlen
  simpa only [walkCharge_append, ripsCharge] using hz

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_GraphMetric
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The metric of a connected graph

The metric on a connected graph is exactly the real-valued shortest-path
length. A proof-independent extension uses the discrete metric otherwise.
-/

noncomputable section

namespace CoarseAssembly

variable {V : Type*} (G : SimpleGraph V)

theorem graphMetric_eq (hG : G.Connected) :
    graphMetric G hG = connectedGraphMetric G hG :=
  graphMetricOrDiscrete_eq G hG

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LatticeHat
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Piecewise linear hat functions of the triangular lattice

The nodal function at a lattice vertex is `max (0, 1 - ρ(p-v))`, where
`ρ(x,y) = max(|x|, |y|, |x+y|)`. These are the barycentric coordinate
functions for the filled triangular lattice. Their partition of unity
maps the filled hexagons into Rips space.
-/

noncomputable section

namespace CoarseAssembly

theorem realLatticeRadius_continuous : Continuous realLatticeRadius := by
  unfold realLatticeRadius
  fun_prop

theorem latticeHat_continuous (v : LatticeVertex) : Continuous (fun p => latticeHat p v) := by
  unfold latticeHat hatKernel realLatticeRadius
  fun_prop

theorem latticeHat_adjacent {p : ℝ × ℝ} {v w : LatticeVertex}
    (hv : 0 < latticeHat p v) (hw : 0 < latticeHat p w) :
    v = w ∨ triangularGraph.Adj v w := by
  by_cases h : v = w
  · exact Or.inl h
  right
  have hv' := (latticeHat_pos_iff p v).mp hv
  have hw' := (latticeHat_pos_iff p w).mp hw
  have bound (a b x : ℝ) (ha : |x - a| < 1) (hb : |x - b| < 1) : |a - b| < 2 := by
    rw [abs_lt] at ha hb ⊢
    constructor <;> linarith
  have hab : |v.1 - w.1| < 2 := by exact_mod_cast bound (v.1 : ℝ) w.1 p.1 hv'.1 hw'.1
  have hbc : |v.2 - w.2| < 2 := by exact_mod_cast bound (v.2 : ℝ) w.2 p.2 hv'.2.1 hw'.2.1
  have hs : |(v.1 + v.2) - (w.1 + w.2)| < 2 := by
    have hvsum : |(p.1 + p.2) - ((v.1 : ℝ) + v.2)| < 1 := by
      convert hv'.2.2 using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    have hwsum : |(p.1 + p.2) - ((w.1 : ℝ) + w.2)| < 1 := by
      convert hw'.2.2 using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    exact_mod_cast bound ((v.1 : ℝ) + v.2) ((w.1 : ℝ) + w.2) (p.1 + p.2) hvsum hwsum
  exact ⟨by omega, by omega, by omega, h⟩

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FilledDisc
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual filled hexagonal discs

The compact polygon is contracted by radial scaling. The triangular-lattice
hat functions give a continuous map of this polygon into the scale-one Rips
realization of its lattice vertices. Thus the filling is constructed, not
assumed as an analytic vanishing premise.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips Analytic

theorem realLatticeRadius_nonneg (p : ℝ × ℝ) : 0 ≤ realLatticeRadius p :=
  (abs_nonneg _).trans (le_max_right _ _)

theorem realLatticeRadius_smul (c : ℝ) (hc : 0 ≤ c) (p : ℝ × ℝ) :
    realLatticeRadius (c • p) = c * realLatticeRadius p := by
  simp only [realLatticeRadius, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    ← mul_add, abs_mul, abs_of_nonneg hc, mul_max_of_nonneg _ _ hc]

instance instTopologicalSpaceFilledDisc (j : ℕ) : TopologicalSpace (FilledDisc j) := inferInstanceAs
  (TopologicalSpace {p : ℝ × ℝ // realLatticeRadius p ≤ j})

instance instT2SpaceFilledDisc (j : ℕ) : T2Space (FilledDisc j) := inferInstanceAs
  (T2Space {p : ℝ × ℝ // realLatticeRadius p ≤ j})

def filledDiscCenter (j : ℕ) : FilledDisc j :=
  ⟨(0, 0), by simp [realLatticeRadius]⟩

def filledDiscContraction (j : ℕ) : CompactContraction (FilledDisc j) where
  center := filledDiscCenter j
  homotopy :=
    { toFun := fun z => ⟨(1 - (z.1 : ℝ)) • z.2.val, by
        rw [realLatticeRadius_smul _ (sub_nonneg.mpr z.1.2.2)]
        exact (mul_le_of_le_one_left (realLatticeRadius_nonneg z.2.val)
          (by linarith [z.1.2.1] : 1 - (z.1 : ℝ) ≤ 1)).trans z.2.property⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        fun_prop
      map_zero_left := by intro x; apply Subtype.ext; simp
      map_one_left := by
        intro x
        apply Subtype.ext
        change (1 - (1 : ℝ)) • x.val = (0, 0)
        simp
        rfl }

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryWalks
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary walks and their canonical lifts

Depth-zero fibers are singletons, so every edge of the actual boundary
subgraph has its unique lift. The walk construction and charge comparison
here leave only the explicit hexagonal boundary walk to be supplied.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem walkCharge_map {X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    (f : G →g H) (a : Y → Y → ℤ) {u v : X} (p : G.Walk u v) :
    walkCharge a (p.map f) = walkCharge (fun x y => a (f x) (f y)) p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [SimpleGraph.Walk.map_cons, walkCharge_cons, ih]

theorem walkCharge_copy {X : Type*} {G : SimpleGraph X} (a : X → X → ℤ)
    {u v u' v' : X} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    walkCharge a (p.copy hu hv) = walkCharge a p := by
  subst u' v'
  rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_Model
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u v w
open Filter
open scoped TensorProduct Topology
namespace NuclearUltrapower

/- The dyadic coefficient ring is exactly Z[1/2]. -/
instance instCoeSortComplexHilbertType : CoeSort ComplexHilbert (Type u) := ⟨ComplexHilbert.carrier⟩

instance instCoeSortUnitalCStarType : CoeSort UnitalCStar (Type u) := ⟨UnitalCStar.carrier⟩

end NuclearUltrapower
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_DyadicGroup
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter

namespace NuclearUltrapower

/-! The exact integral subgroup and dilation in the tensor-norm formulation. -/

def integralAction : SL3Z →* MulAut (Multiplicative IntegralVector3) where
  toFun M := AddEquiv.toMultiplicative (Matrix.SpecialLinearGroup.toLin' M).toAddEquiv
  map_one' := by ext v i; simp
  map_mul' M N := by ext v i; simp [map_mul]

abbrev IntegralGroup := SemidirectProduct (Multiplicative IntegralVector3) SL3Z integralAction

def integralTranslation (v : IntegralVector3) : IntegralGroup :=
  SemidirectProduct.inl (Multiplicative.ofAdd v)

def integralTheta : Monoid.End IntegralGroup where
  toFun g := ⟨Multiplicative.ofAdd ((2 : ℤ) • g.left.toAdd), g.right⟩
  map_one' := by ext <;> simp
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd ((2 : ℤ) • (g.left.toAdd +
        Matrix.SpecialLinearGroup.toLin' g.right h.left.toAdd)) =
        Multiplicative.ofAdd ((2 : ℤ) • g.left.toAdd +
        Matrix.SpecialLinearGroup.toLin' g.right ((2 : ℤ) • h.left.toAdd))
      simp only [smul_add, map_smul]
    · rfl

@[simp] theorem integralTheta_left (g : IntegralGroup) :
    (integralTheta g).left.toAdd = (2 : ℤ) • g.left.toAdd := rfl

@[simp] theorem integralTheta_right (g : IntegralGroup) :
    (integralTheta g).right = g.right := rfl

@[simp] theorem integralTheta_translation (v : IntegralVector3) :
    integralTheta (integralTranslation v) = integralTranslation ((2 : ℤ) • v) := rfl

@[simp] theorem integralTheta_pow_translation (n : ℕ) (v : IntegralVector3) :
    (integralTheta ^ n) (integralTranslation v) = integralTranslation ((2 : ℤ) ^ n • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Monoid.End.coe_mul, Function.comp_apply, ih, integralTheta_translation]
      congr 1
      simp only [pow_succ', mul_smul]

end NuclearUltrapower

end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

def addHead (p : α × ℤ) : Poly α → Poly α
  | [] => [p]
  | q::qs => if p.1 = q.1 then (p.1, p.2 + q.2)::qs else p::q::qs

def compress : Poly α → Poly α
  | [] => []
  | p::ps => addHead p (compress ps)

def normalize (le : α → α → Bool) (ps : Poly α) : Poly α :=
  compress (ps.insertionSort (fun p q => le p.1 q.1 = true))

def matMul (a b : Mat3) : Mat3 :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j =>
    entry a i 0 * entry b 0 j + entry a i 1 * entry b 1 j + entry a i 2 * entry b 2 j

def matInv (a : Mat3) : Mat3 :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j =>
    entry a ((j+1)%3) ((i+1)%3) * entry a ((j+2)%3) ((i+2)%3) -
      entry a ((j+1)%3) ((i+2)%3) * entry a ((j+2)%3) ((i+1)%3)

def matOne : Mat3 := [1,0,0,0,1,0,0,0,1]

def matLe : Mat3 → Mat3 → Bool
  | [], _ => true
  | _::_, [] => false
  | a::as, b::bs => if a = b then matLe as bs else decide (a ≤ b)

def intL1 (p : Poly α) : ℤ := (p.map (fun p => |p.2|)).sum

end NuclearUltrapower.SOS

namespace NuclearUltrapower.SOS
def label7 : Mat3 := [-2, 0, -1, 0, 1, 0, 3, 0, 1]
def label19 : Mat3 := [-1, -2, -1, 1, 1, 0, 2, 2, 1]
def label47 : Mat3 := [-1, -1, -2, 1, 1, 1, 2, 1, 2]
def label50 : Mat3 := [-1, -1, -1, 0, 1, 0, 2, 1, 1]
def label51 : Mat3 := [-1, -1, -1, 0, 1, 0, 2, 2, 1]
def label53 : Mat3 := [-1, -1, -1, 1, 1, 0, 2, 1, 1]
def label55 : Mat3 := [-1, -1, -1, 2, 1, 0, 2, 1, 1]
def label90 : Mat3 := [-1, 0, -2, -1, 1, -2, 1, 0, 1]
def label102 : Mat3 := [-1, 0, -2, 1, 1, 2, 1, 0, 1]
def label103 : Mat3 := [-1, 0, -1, -2, 1, -1, 2, 0, 1]
def label104 : Mat3 := [-1, 0, -1, -1, 1, -1, 2, 0, 1]
def label105 : Mat3 := [-1, 0, -1, -1, 1, 0, 2, 0, 1]
def label106 : Mat3 := [-1, 0, -1, 0, 1, -1, 2, 0, 1]
def label109 : Mat3 := [-1, 0, -1, 0, 1, 0, 2, 0, 1]
def label112 : Mat3 := [-1, 0, -1, 0, 1, 1, 2, 0, 1]
def label113 : Mat3 := [-1, 0, -1, 1, 1, 0, 2, 0, 1]
def label114 : Mat3 := [-1, 0, -1, 1, 1, 1, 2, 0, 1]
def label115 : Mat3 := [-1, 0, -1, 2, 1, 1, 2, 0, 1]
def label118 : Mat3 := [-1, 0, 0, 0, 1, 0, 2, 0, -1]
def label149 : Mat3 := [-1, 1, -2, -1, 1, -1, 2, -1, 2]
def label157 : Mat3 := [-1, 1, -1, -2, 1, 0, 2, -1, 1]
def label159 : Mat3 := [-1, 1, -1, -1, 1, 0, 2, -1, 1]
def label160 : Mat3 := [-1, 1, -1, 0, 1, 0, 2, -2, 1]
def label161 : Mat3 := [-1, 1, -1, 0, 1, 0, 2, -1, 1]
def label200 : Mat3 := [-1, 2, -1, -1, 1, 0, 2, -2, 1]
def label202 : Mat3 := [-1, 2, 0, -1, 1, -1, 0, 0, 1]
def label226 : Mat3 := [0, -2, -1, 0, 1, 0, 1, 2, 1]
def label228 : Mat3 := [0, -2, -1, 1, 1, 0, 1, 2, 1]
def label241 : Mat3 := [0, -1, -2, 0, 1, 1, 1, 1, 2]
def label243 : Mat3 := [0, -1, -2, 1, 1, 0, 1, 1, 1]
def label245 : Mat3 := [0, -1, -2, 1, 1, 1, 1, 1, 2]
def label248 : Mat3 := [0, -1, -1, -1, 0, -1, 1, 1, 1]
def label250 : Mat3 := [0, -1, -1, -1, 1, 0, 1, 1, 1]
def label251 : Mat3 := [0, -1, -1, -1, 2, 0, 1, 0, 1]
def label253 : Mat3 := [0, -1, -1, 0, 0, -1, 1, 1, 1]
def label259 : Mat3 := [0, -1, -1, 0, 1, 0, 1, 1, 0]
def label265 : Mat3 := [0, -1, -1, 0, 2, 1, 1, 1, 1]
def label267 : Mat3 := [0, -1, -1, 1, 0, -1, 1, 1, 1]
def label273 : Mat3 := [0, -1, -1, 1, 1, -1, 1, 1, 0]
def label296 : Mat3 := [0, -1, -1, 1, 2, 0, 1, 2, 1]
def label301 : Mat3 := [0, -1, -1, 2, 1, 0, 1, 1, 1]
def label303 : Mat3 := [0, -1, -1, 2, 2, 1, 1, 1, 1]
def label307 : Mat3 := [0, -1, 0, 0, 1, -1, 1, 1, 0]
def label413 : Mat3 := [0, -1, 1, 1, 1, 0, -2, -2, 1]
def label442 : Mat3 := [0, 0, -1, -2, 1, -1, 1, 0, 1]
def label443 : Mat3 := [0, 0, -1, -2, 1, 0, 1, 0, 1]
def label446 : Mat3 := [0, 0, -1, -1, 0, 0, 1, 1, 1]
def label456 : Mat3 := [0, 0, -1, -1, 1, 0, 1, 0, 1]
def label459 : Mat3 := [0, 0, -1, -1, 1, 1, 1, 0, 0]
def label460 : Mat3 := [0, 0, -1, -1, 1, 1, 1, 0, 1]
def label462 : Mat3 := [0, 0, -1, -1, 2, 0, 1, -1, 1]
def label485 : Mat3 := [0, 0, -1, 0, 1, 1, 1, -1, 1]
def label487 : Mat3 := [0, 0, -1, 0, 1, 1, 1, 0, 1]
def label491 : Mat3 := [0, 0, -1, 0, 1, 2, 1, 0, 1]
def label492 : Mat3 := [0, 0, -1, 1, 0, 0, 1, -1, 1]
def label495 : Mat3 := [0, 0, -1, 1, 1, -1, 1, 0, 0]
def label496 : Mat3 := [0, 0, -1, 1, 1, -1, 1, 0, 1]
def label509 : Mat3 := [0, 0, -1, 1, 2, 0, 1, 1, 1]
def label511 : Mat3 := [0, 0, -1, 2, 1, 0, 1, 0, 1]
def label512 : Mat3 := [0, 0, -1, 2, 1, 1, 1, 0, 1]
def label590 : Mat3 := [0, 1, -2, -1, 1, -1, 1, -1, 2]
def label592 : Mat3 := [0, 1, -2, -1, 1, 0, 1, -1, 1]
def label593 : Mat3 := [0, 1, -2, 0, 1, -1, 1, -1, 2]
def label595 : Mat3 := [0, 1, -1, -2, 1, -2, 1, 0, 1]
def label596 : Mat3 := [0, 1, -1, -2, 1, 0, 1, -1, 1]
def label597 : Mat3 := [0, 1, -1, -2, 2, -1, 1, -1, 1]
def label603 : Mat3 := [0, 1, -1, -1, 0, 1, 1, -1, 1]
def label626 : Mat3 := [0, 1, -1, -1, 1, 1, 1, -1, 0]
def label632 : Mat3 := [0, 1, -1, -1, 2, 0, 1, -2, 1]
def label633 : Mat3 := [0, 1, -1, 0, 0, 1, 1, -1, 1]
def label637 : Mat3 := [0, 1, -1, 0, 1, 0, 1, -1, 0]
def label645 : Mat3 := [0, 1, -1, 0, 2, -1, 1, -1, 1]
def label647 : Mat3 := [0, 1, -1, 1, 0, 1, 1, -1, 1]
def label648 : Mat3 := [0, 1, -1, 1, 1, 0, 1, -1, 1]
def label650 : Mat3 := [0, 1, -1, 1, 2, 0, 1, 0, 1]
def label722 : Mat3 := [0, 1, 0, 0, 1, 1, 1, -1, 0]
def label790 : Mat3 := [0, 2, -1, -1, 1, 0, 1, -2, 1]
def label793 : Mat3 := [0, 2, -1, 0, 1, 0, 1, -2, 1]
def label812 : Mat3 := [1, -3, -2, 0, 1, 0, 0, 2, 1]
def label815 : Mat3 := [1, -3, -2, 0, 2, 1, 0, 3, 2]
def label820 : Mat3 := [1, -3, -1, 0, 1, 0, 0, 3, 1]
def label859 : Mat3 := [1, -2, -3, 0, 1, 1, 0, 2, 3]
def label863 : Mat3 := [1, -2, -2, -1, 2, 1, 0, 1, 1]
def label864 : Mat3 := [1, -2, -2, -1, 3, 2, 0, 1, 1]
def label883 : Mat3 := [1, -2, -2, 1, -1, -2, 0, 1, 1]
def label885 : Mat3 := [1, -2, -2, 1, 0, -1, 0, 1, 1]
def label887 : Mat3 := [1, -2, -1, -1, 1, 0, 0, 2, 1]
def label888 : Mat3 := [1, -2, -1, -1, 2, 0, 0, 1, 1]
def label889 : Mat3 := [1, -2, -1, -1, 3, 0, 0, 0, 1]
def label892 : Mat3 := [1, -2, -1, -1, 3, 1, 0, 2, 1]
def label895 : Mat3 := [1, -2, -1, 0, -1, -1, 0, 2, 1]
def label927 : Mat3 := [1, -2, -1, 0, 3, 1, 0, 2, 1]
def label931 : Mat3 := [1, -2, -1, 1, -1, -1, 0, 2, 1]
def label934 : Mat3 := [1, -2, -1, 1, 1, 0, 0, 2, 1]
def label935 : Mat3 := [1, -2, 0, -2, 5, 0, 0, 0, 1]
def label940 : Mat3 := [1, -2, 0, -1, 3, -1, 0, 0, 1]
def label944 : Mat3 := [1, -2, 0, -1, 3, 0, -1, 2, 1]
def label945 : Mat3 := [1, -2, 0, -1, 3, 0, -1, 3, 1]
def label949 : Mat3 := [1, -2, 0, -1, 3, 0, 1, -3, 1]
def label950 : Mat3 := [1, -2, 0, -1, 3, 0, 1, -2, 1]
def label958 : Mat3 := [1, -2, 0, 0, 1, -1, -1, 2, 1]
def label1030 : Mat3 := [1, -2, 1, 0, 1, -1, 0, 2, -1]
def label1096 : Mat3 := [1, -1, -3, 0, 1, 0, 0, 1, 1]
def label1098 : Mat3 := [1, -1, -3, 0, 1, 1, 0, 1, 2]
def label1100 : Mat3 := [1, -1, -3, 0, 1, 2, 0, 1, 3]
def label1102 : Mat3 := [1, -1, -2, -1, 1, 1, 0, 1, 1]
def label1103 : Mat3 := [1, -1, -2, -1, 1, 1, 0, 1, 2]
def label1105 : Mat3 := [1, -1, -2, -1, 2, 1, 0, 0, 1]
def label1107 : Mat3 := [1, -1, -2, -1, 2, 2, 0, 1, 1]
def label1109 : Mat3 := [1, -1, -2, -1, 2, 3, 0, 1, 2]
def label1113 : Mat3 := [1, -1, -2, 0, 0, -1, 0, 1, 2]
def label1141 : Mat3 := [1, -1, -2, 0, 2, 1, 0, 1, 1]
def label1142 : Mat3 := [1, -1, -2, 0, 2, 3, 0, 1, 2]
def label1144 : Mat3 := [1, -1, -2, 1, 0, -2, 0, 1, 1]
def label1146 : Mat3 := [1, -1, -2, 1, 0, -1, 0, 1, 2]
def label1148 : Mat3 := [1, -1, -2, 1, 1, -1, 0, 1, 1]
def label1149 : Mat3 := [1, -1, -2, 1, 1, 1, 0, 1, 2]
def label1150 : Mat3 := [1, -1, -1, -2, 1, 0, 0, 1, 1]
def label1151 : Mat3 := [1, -1, -1, -2, 2, 1, 0, 1, 1]
def label1152 : Mat3 := [1, -1, -1, -2, 3, 0, 0, 0, 1]
def label1153 : Mat3 := [1, -1, -1, -2, 3, 1, 0, 0, 1]
def label1154 : Mat3 := [1, -1, -1, -2, 3, 2, 0, 0, 1]
def label1155 : Mat3 := [1, -1, -1, -2, 3, 2, 0, 1, 1]
def label1156 : Mat3 := [1, -1, -1, -2, 3, 3, 0, 0, 1]
def label1157 : Mat3 := [1, -1, -1, -1, 0, -1, 0, 1, 1]
def label1160 : Mat3 := [1, -1, -1, -1, 1, 0, 0, 1, 1]
def label1165 : Mat3 := [1, -1, -1, -1, 2, -1, 0, 0, 1]
def label1168 : Mat3 := [1, -1, -1, -1, 2, 0, 0, 0, 1]
def label1172 : Mat3 := [1, -1, -1, -1, 2, 1, -1, 1, 2]
def label1173 : Mat3 := [1, -1, -1, -1, 2, 1, -1, 2, 2]
def label1174 : Mat3 := [1, -1, -1, -1, 2, 1, -1, 3, 2]
def label1179 : Mat3 := [1, -1, -1, -1, 2, 1, 1, -2, 0]
def label1184 : Mat3 := [1, -1, -1, -1, 2, 2, -1, 2, 3]
def label1188 : Mat3 := [1, -1, -1, -1, 2, 2, 1, -2, -1]
def label1189 : Mat3 := [1, -1, -1, -1, 2, 2, 1, -1, 0]
def label1296 : Mat3 := [1, -1, -1, 1, 2, 1, 0, 1, 1]
def label1300 : Mat3 := [1, -1, -1, 2, -1, 0, 0, 0, 1]
def label1301 : Mat3 := [1, -1, -1, 2, 0, -1, 0, 1, 1]
def label1302 : Mat3 := [1, -1, -1, 2, 1, 0, 0, 1, 1]
def label1303 : Mat3 := [1, -1, 0, -3, 4, 0, 0, 0, 1]
def label1308 : Mat3 := [1, -1, 0, -2, 2, -1, 1, 0, 1]
def label1313 : Mat3 := [1, -1, 0, -2, 3, -1, 0, 0, 1]
def label1316 : Mat3 := [1, -1, 0, -2, 3, 0, -2, 3, 1]
def label1317 : Mat3 := [1, -1, 0, -2, 3, 0, -1, 0, 1]
def label1318 : Mat3 := [1, -1, 0, -2, 3, 0, -1, 1, 1]
def label1320 : Mat3 := [1, -1, 0, -2, 3, 0, 0, -1, 1]
def label1321 : Mat3 := [1, -1, 0, -2, 3, 0, 0, 0, 1]
def label1322 : Mat3 := [1, -1, 0, -2, 3, 0, 0, 1, 1]
def label1323 : Mat3 := [1, -1, 0, -2, 3, 0, 1, -2, 1]
def label1324 : Mat3 := [1, -1, 0, -2, 3, 0, 1, -1, 1]
def label1325 : Mat3 := [1, -1, 0, -2, 3, 0, 1, 0, 1]
def label1326 : Mat3 := [1, -1, 0, -2, 3, 0, 2, -3, 1]
def label1336 : Mat3 := [1, -1, 0, -1, 1, -1, 0, 1, 1]
def label1347 : Mat3 := [1, -1, 0, -1, 2, -1, -1, 1, 1]
def label1349 : Mat3 := [1, -1, 0, -1, 2, -1, 0, -1, 2]
def label1357 : Mat3 := [1, -1, 0, -1, 2, 0, -2, 1, 1]
def label1365 : Mat3 := [1, -1, 0, -1, 2, 0, -1, 3, 1]
def label1371 : Mat3 := [1, -1, 0, -1, 2, 0, 1, -3, 1]
def label1379 : Mat3 := [1, -1, 0, -1, 2, 0, 2, -1, 1]
def label1392 : Mat3 := [1, -1, 0, -1, 3, -1, 0, -1, 1]
def label1411 : Mat3 := [1, -1, 0, 0, 1, -2, -1, 1, 1]
def label1486 : Mat3 := [1, -1, 0, 0, 2, -1, -1, 0, 1]
def label1508 : Mat3 := [1, -1, 0, 1, 0, -1, -2, 2, 1]
def label1547 : Mat3 := [1, -1, 0, 1, 1, -1, -2, 1, 1]
def label1586 : Mat3 := [1, -1, 1, -2, 3, -3, 0, 0, 1]
def label1587 : Mat3 := [1, -1, 1, -2, 3, -2, 0, -1, 1]
def label1588 : Mat3 := [1, -1, 1, -2, 3, -2, 0, 0, 1]
def label1599 : Mat3 := [1, -1, 1, -1, 2, -3, 0, 0, 1]
def label1602 : Mat3 := [1, -1, 1, -1, 2, -2, -1, 1, 0]
def label1603 : Mat3 := [1, -1, 1, -1, 2, -2, -1, 2, -1]
def label1607 : Mat3 := [1, -1, 1, -1, 2, -2, 1, -2, 3]
def label1612 : Mat3 := [1, -1, 1, -1, 2, -1, -1, 2, 0]
def label1613 : Mat3 := [1, -1, 1, -1, 2, -1, 0, -2, 1]
def label1617 : Mat3 := [1, -1, 1, -1, 2, -1, 1, -3, 2]
def label1618 : Mat3 := [1, -1, 1, -1, 2, -1, 1, -2, 2]
def label1619 : Mat3 := [1, -1, 1, -1, 2, -1, 1, -1, 2]
def label1639 : Mat3 := [1, -1, 1, 0, 1, -2, -1, 1, 0]
def label1724 : Mat3 := [1, -1, 1, 1, 1, 0, -1, -2, 1]
def label1759 : Mat3 := [1, -1, 2, 0, 1, -1, 0, -2, 3]
def label1768 : Mat3 := [1, -1, 2, 0, 1, 0, 0, -2, 1]
def label1795 : Mat3 := [1, 0, -3, -1, 1, 2, 0, 0, 1]
def label1796 : Mat3 := [1, 0, -3, -1, 1, 3, 0, 0, 1]
def label1804 : Mat3 := [1, 0, -3, 1, 1, -3, 0, 0, 1]
def label1805 : Mat3 := [1, 0, -3, 1, 1, -2, 0, 0, 1]
def label1809 : Mat3 := [1, 0, -2, -2, 1, 1, 0, 0, 1]
def label1810 : Mat3 := [1, 0, -2, -2, 1, 2, 0, 0, 1]
def label1811 : Mat3 := [1, 0, -2, -2, 1, 3, 0, 0, 1]
def label1812 : Mat3 := [1, 0, -2, -2, 1, 4, 0, 0, 1]
def label1824 : Mat3 := [1, 0, -2, -1, 1, 2, -1, 0, 3]
def label1825 : Mat3 := [1, 0, -2, -1, 1, 2, -1, 1, 3]
def label1826 : Mat3 := [1, 0, -2, -1, 1, 2, 0, -1, 1]
def label1827 : Mat3 := [1, 0, -2, -1, 1, 2, 0, 0, 1]
def label1829 : Mat3 := [1, 0, -2, -1, 1, 2, 1, -1, -1]
def label1830 : Mat3 := [1, 0, -2, -1, 1, 2, 1, 0, -1]
def label1883 : Mat3 := [1, 0, -2, 2, 1, -3, 0, 0, 1]
def label1884 : Mat3 := [1, 0, -2, 2, 1, -2, 0, 0, 1]
def label1885 : Mat3 := [1, 0, -2, 2, 1, -1, 0, 0, 1]
def label1887 : Mat3 := [1, 0, -1, -3, 1, 0, 0, 0, 1]
def label1888 : Mat3 := [1, 0, -1, -3, 1, 1, 0, 0, 1]
def label1889 : Mat3 := [1, 0, -1, -3, 1, 2, 0, 0, 1]
def label1890 : Mat3 := [1, 0, -1, -3, 1, 3, 0, 0, 1]
def label1891 : Mat3 := [1, 0, -1, -2, 1, -1, 0, 0, 1]
def label1894 : Mat3 := [1, 0, -1, -2, 1, 0, 0, 0, 1]
def label1897 : Mat3 := [1, 0, -1, -2, 1, 1, -2, 1, 2]
def label1898 : Mat3 := [1, 0, -1, -2, 1, 1, -1, 0, 2]
def label1900 : Mat3 := [1, 0, -1, -2, 1, 1, 0, 0, 1]
def label1901 : Mat3 := [1, 0, -1, -2, 1, 1, 1, -1, 1]
def label1903 : Mat3 := [1, 0, -1, -2, 1, 1, 2, -1, 0]
def label1905 : Mat3 := [1, 0, -1, -2, 1, 2, -2, 1, 3]
def label1908 : Mat3 := [1, 0, -1, -2, 1, 2, 0, -1, 1]
def label1910 : Mat3 := [1, 0, -1, -2, 1, 2, 0, 1, 1]
def label1911 : Mat3 := [1, 0, -1, -2, 1, 2, 1, -1, 0]
def label1912 : Mat3 := [1, 0, -1, -2, 1, 2, 1, 0, 0]
def label1913 : Mat3 := [1, 0, -1, -2, 1, 2, 2, -1, -1]
def label1948 : Mat3 := [1, 0, -1, -1, 1, 1, -1, -1, 2]
def label1951 : Mat3 := [1, 0, -1, -1, 1, 1, -1, 2, 2]
def label1952 : Mat3 := [1, 0, -1, -1, 1, 1, 0, -2, 1]
def label1957 : Mat3 := [1, 0, -1, -1, 1, 1, 1, -2, 0]
def label1975 : Mat3 := [1, 0, -1, -1, 2, 0, 0, -1, 1]
def label2061 : Mat3 := [1, 0, -1, 0, 2, -1, -1, -1, 2]
def label2083 : Mat3 := [1, 0, -1, 1, 1, -2, -2, 0, 3]
def label2159 : Mat3 := [1, 0, -1, 2, 1, 1, 0, 0, 1]
def label2166 : Mat3 := [1, 0, -1, 3, 1, -1, 0, 0, 1]
def label2167 : Mat3 := [1, 0, -1, 3, 1, 0, 0, 0, 1]
def label2169 : Mat3 := [1, 0, 0, -4, 1, 0, 0, 0, 1]
def label2176 : Mat3 := [1, 0, 0, -3, 1, -1, 0, 0, 1]
def label2180 : Mat3 := [1, 0, 0, -3, 1, 0, -3, 1, 1]
def label2182 : Mat3 := [1, 0, 0, -3, 1, 0, -1, 0, 1]
def label2183 : Mat3 := [1, 0, 0, -3, 1, 0, -1, 1, 1]
def label2184 : Mat3 := [1, 0, 0, -3, 1, 0, 0, -1, 1]
def label2185 : Mat3 := [1, 0, 0, -3, 1, 0, 0, 0, 1]
def label2186 : Mat3 := [1, 0, 0, -3, 1, 0, 0, 1, 1]
def label2187 : Mat3 := [1, 0, 0, -3, 1, 0, 1, -1, 1]
def label2188 : Mat3 := [1, 0, 0, -3, 1, 0, 1, 0, 1]
def label2189 : Mat3 := [1, 0, 0, -3, 1, 0, 2, -1, 1]
def label2190 : Mat3 := [1, 0, 0, -3, 1, 0, 3, -1, 1]
def label2199 : Mat3 := [1, 0, 0, -3, 2, -1, 1, -1, 1]
def label2210 : Mat3 := [1, 0, 0, -2, 0, -1, 0, 1, 1]
def label2223 : Mat3 := [1, 0, 0, -2, 1, -1, -1, 0, 1]
def label2225 : Mat3 := [1, 0, 0, -2, 1, -1, 0, -1, 2]
def label2228 : Mat3 := [1, 0, 0, -2, 1, -1, 1, -1, 2]
def label2237 : Mat3 := [1, 0, 0, -2, 1, 0, -3, 2, 1]
def label2241 : Mat3 := [1, 0, 0, -2, 1, 0, -1, -1, 1]
def label2245 : Mat3 := [1, 0, 0, -2, 1, 0, 0, -2, 1]
def label2246 : Mat3 := [1, 0, 0, -2, 1, 0, 0, -1, 1]
def label2249 : Mat3 := [1, 0, 0, -2, 1, 0, 0, 2, 1]
def label2250 : Mat3 := [1, 0, 0, -2, 1, 0, 1, -2, 1]
def label2253 : Mat3 := [1, 0, 0, -2, 1, 0, 1, 1, 1]
def label2254 : Mat3 := [1, 0, 0, -2, 1, 0, 2, -2, 1]
def label2257 : Mat3 := [1, 0, 0, -2, 1, 0, 3, -2, 1]
def label2269 : Mat3 := [1, 0, 0, -2, 1, 1, 0, 1, 2]
def label2281 : Mat3 := [1, 0, 0, -2, 2, -1, 0, -1, 1]
def label2297 : Mat3 := [1, 0, 0, -1, -1, -1, 0, 2, 1]
def label2306 : Mat3 := [1, 0, 0, -1, 0, -1, -1, 1, 1]
def label2309 : Mat3 := [1, 0, 0, -1, 0, -1, 0, 1, 2]
def label2327 : Mat3 := [1, 0, 0, -1, 1, -2, -1, 0, 1]
def label2329 : Mat3 := [1, 0, 0, -1, 1, -2, 0, -1, 3]
def label2339 : Mat3 := [1, 0, 0, -1, 1, -1, -1, -1, 2]
def label2343 : Mat3 := [1, 0, 0, -1, 1, -1, 0, -2, 3]
def label2348 : Mat3 := [1, 0, 0, -1, 1, -1, 1, -2, 3]
def label2367 : Mat3 := [1, 0, 0, -1, 1, 0, -1, -2, 1]
def label2372 : Mat3 := [1, 0, 0, -1, 1, 0, -1, 3, 1]
def label2373 : Mat3 := [1, 0, 0, -1, 1, 0, 0, -3, 1]
def label2380 : Mat3 := [1, 0, 0, -1, 1, 0, 1, -3, 1]
def label2404 : Mat3 := [1, 0, 0, -1, 1, 1, -1, 2, 3]
def label2405 : Mat3 := [1, 0, 0, -1, 1, 1, 0, -2, -1]
def label2428 : Mat3 := [1, 0, 0, -1, 2, -3, 0, -1, 2]
def label2430 : Mat3 := [1, 0, 0, -1, 2, -1, -1, -1, 1]
def label2432 : Mat3 := [1, 0, 0, -1, 2, -1, 0, -3, 2]
def label2452 : Mat3 := [1, 0, 0, -1, 3, -1, 0, -2, 1]
def label2465 : Mat3 := [1, 0, 0, 0, -1, -2, -1, 1, 1]
def label2515 : Mat3 := [1, 0, 0, 0, 1, -3, -1, 0, 1]
def label2644 : Mat3 := [1, 0, 0, 0, 2, -3, -1, -1, 2]
def label2683 : Mat3 := [1, 0, 0, 0, 3, -2, -1, -1, 1]
def label2688 : Mat3 := [1, 0, 0, 0, 3, -1, -1, -2, 1]
def label2746 : Mat3 := [1, 0, 0, 1, 1, -2, -2, 0, 1]
def label2849 : Mat3 := [1, 0, 0, 1, 2, -1, -2, -1, 1]
def label2892 : Mat3 := [1, 0, 0, 2, 1, -1, -3, 0, 1]
def label3003 : Mat3 := [1, 0, 1, -3, 1, -3, 0, 0, 1]
def label3004 : Mat3 := [1, 0, 1, -3, 1, -2, 0, 0, 1]
def label3008 : Mat3 := [1, 0, 1, -2, 1, -3, 0, 0, 1]
def label3011 : Mat3 := [1, 0, 1, -2, 1, -2, -2, 1, -1]
def label3012 : Mat3 := [1, 0, 1, -2, 1, -2, -1, 0, 0]
def label3014 : Mat3 := [1, 0, 1, -2, 1, -2, 0, -1, 1]
def label3016 : Mat3 := [1, 0, 1, -2, 1, -2, 0, 1, 1]
def label3017 : Mat3 := [1, 0, 1, -2, 1, -2, 1, -1, 2]
def label3019 : Mat3 := [1, 0, 1, -2, 1, -2, 2, -1, 3]
def label3021 : Mat3 := [1, 0, 1, -2, 1, -1, -2, 1, 0]
def label3025 : Mat3 := [1, 0, 1, -2, 1, -1, 1, -1, 1]
def label3026 : Mat3 := [1, 0, 1, -2, 1, -1, 1, 0, 2]
def label3027 : Mat3 := [1, 0, 1, -2, 1, -1, 2, -1, 2]
def label3032 : Mat3 := [1, 0, 1, -2, 1, 0, 2, -1, 1]
def label3044 : Mat3 := [1, 0, 1, -1, 1, -2, -1, 0, 0]
def label3046 : Mat3 := [1, 0, 1, -1, 1, -2, 0, -1, 2]
def label3056 : Mat3 := [1, 0, 1, -1, 1, -1, -1, -1, 0]
def label3059 : Mat3 := [1, 0, 1, -1, 1, -1, -1, 2, 0]
def label3060 : Mat3 := [1, 0, 1, -1, 1, -1, 0, -2, 1]
def label3065 : Mat3 := [1, 0, 1, -1, 1, -1, 1, -2, 2]
def label3091 : Mat3 := [1, 0, 1, -1, 2, -2, 0, -1, 1]
def label3177 : Mat3 := [1, 0, 1, 0, 2, -1, -1, -1, 0]
def label3250 : Mat3 := [1, 0, 1, 2, 1, 0, -2, -1, 1]
def label3284 : Mat3 := [1, 0, 2, -2, 1, -4, 0, 0, 1]
def label3291 : Mat3 := [1, 0, 2, -1, 1, -2, -1, 0, -1]
def label3292 : Mat3 := [1, 0, 2, -1, 1, -2, -1, 1, -1]
def label3293 : Mat3 := [1, 0, 2, -1, 1, -2, 0, -1, 1]
def label3296 : Mat3 := [1, 0, 2, -1, 1, -2, 1, -1, 3]
def label3297 : Mat3 := [1, 0, 2, -1, 1, -2, 1, 0, 3]
def label3301 : Mat3 := [1, 0, 2, -1, 1, -1, 1, -1, 2]
def label3306 : Mat3 := [1, 0, 2, -1, 1, 0, 1, -1, 1]
def label3339 : Mat3 := [1, 0, 2, 1, 1, 0, -1, -1, 1]
def label3344 : Mat3 := [1, 0, 2, 1, 1, 1, -1, -1, 0]
def label3369 : Mat3 := [1, 0, 3, 0, 1, 0, 0, -1, 1]
def label3380 : Mat3 := [1, 1, -3, 0, 1, -2, 0, -1, 3]
def label3382 : Mat3 := [1, 1, -3, 0, 1, -1, 0, -1, 2]
def label3384 : Mat3 := [1, 1, -3, 0, 1, 0, 0, -1, 1]
def label3387 : Mat3 := [1, 1, -2, -1, 0, 1, 0, -1, 2]
def label3389 : Mat3 := [1, 1, -2, -1, 0, 2, 0, -1, 1]
def label3391 : Mat3 := [1, 1, -2, -1, 1, -1, 0, -1, 2]
def label3392 : Mat3 := [1, 1, -2, -1, 1, 1, 0, -1, 1]
def label3395 : Mat3 := [1, 1, -2, 0, 0, 1, 0, -1, 2]
def label3396 : Mat3 := [1, 1, -2, 0, 1, -3, 0, 0, 1]
def label3423 : Mat3 := [1, 1, -2, 0, 2, -3, 0, -1, 2]
def label3424 : Mat3 := [1, 1, -2, 0, 2, -1, 0, -1, 1]
def label3425 : Mat3 := [1, 1, -2, 1, 1, -1, 0, -1, 1]
def label3426 : Mat3 := [1, 1, -2, 1, 1, -1, 0, -1, 2]
def label3428 : Mat3 := [1, 1, -2, 1, 2, -3, 0, -1, 2]
def label3430 : Mat3 := [1, 1, -2, 1, 2, -2, 0, -1, 1]
def label3432 : Mat3 := [1, 1, -2, 1, 2, -1, 0, 0, 1]
def label3434 : Mat3 := [1, 1, -1, -2, -1, 0, 0, 0, 1]
def label3435 : Mat3 := [1, 1, -1, -2, -1, 1, 0, 0, 1]
def label3436 : Mat3 := [1, 1, -1, -2, -1, 2, 0, -1, 1]
def label3437 : Mat3 := [1, 1, -1, -2, -1, 2, 0, 0, 1]
def label3438 : Mat3 := [1, 1, -1, -2, 0, 1, 0, -1, 1]
def label3439 : Mat3 := [1, 1, -1, -2, 1, 0, 0, -1, 1]
def label3442 : Mat3 := [1, 1, -1, -1, 0, -1, 0, 0, 1]
def label3451 : Mat3 := [1, 1, -1, -1, 0, 1, -1, -2, 2]
def label3454 : Mat3 := [1, 1, -1, -1, 0, 1, 0, -2, 1]
def label3458 : Mat3 := [1, 1, -1, -1, 0, 1, 1, -1, 0]
def label3460 : Mat3 := [1, 1, -1, -1, 0, 1, 1, 1, 0]
def label3463 : Mat3 := [1, 1, -1, -1, 1, -2, 1, 0, 1]
def label3466 : Mat3 := [1, 1, -1, -1, 1, 0, 0, -1, 1]
def label3470 : Mat3 := [1, 1, -1, -1, 2, -1, 0, -1, 1]
def label3481 : Mat3 := [1, 1, -1, 0, 1, -2, -1, -1, 2]
def label3542 : Mat3 := [1, 1, -1, 1, 0, 1, 0, -1, 1]
def label3543 : Mat3 := [1, 1, -1, 1, 1, -2, -1, 0, 1]
def label3544 : Mat3 := [1, 1, -1, 1, 1, -2, -1, 0, 2]
def label3577 : Mat3 := [1, 1, -1, 1, 2, 1, 0, 0, 1]
def label3580 : Mat3 := [1, 1, -1, 2, 1, 0, 0, -1, 1]
def label3581 : Mat3 := [1, 1, -1, 2, 2, -1, 0, -1, 1]
def label3585 : Mat3 := [1, 1, -1, 2, 3, -1, 0, 0, 1]
def label3586 : Mat3 := [1, 1, -1, 2, 3, 0, 0, 0, 1]
def label3587 : Mat3 := [1, 1, 0, -3, -2, 0, 0, 0, 1]
def label3589 : Mat3 := [1, 1, 0, -2, -1, -1, 0, 0, 1]
def label3592 : Mat3 := [1, 1, 0, -2, -1, 0, -2, -1, 1]
def label3593 : Mat3 := [1, 1, 0, -2, -1, 0, -1, -1, 1]
def label3595 : Mat3 := [1, 1, 0, -2, -1, 0, 0, -1, 1]
def label3596 : Mat3 := [1, 1, 0, -2, -1, 0, 0, 0, 1]
def label3597 : Mat3 := [1, 1, 0, -2, -1, 0, 0, 1, 1]
def label3598 : Mat3 := [1, 1, 0, -2, -1, 0, 1, 0, 1]
def label3599 : Mat3 := [1, 1, 0, -2, -1, 0, 1, 1, 1]
def label3600 : Mat3 := [1, 1, 0, -2, -1, 0, 2, 1, 1]
def label3610 : Mat3 := [1, 1, 0, -2, 1, -1, 2, 0, 1]
def label3613 : Mat3 := [1, 1, 0, -1, -1, -1, 0, 1, 1]
def label3619 : Mat3 := [1, 1, 0, -1, 0, -1, -1, -1, 1]
def label3621 : Mat3 := [1, 1, 0, -1, 0, -1, 0, -1, 2]
def label3631 : Mat3 := [1, 1, 0, -1, 0, 0, -1, -2, 1]
def label3658 : Mat3 := [1, 1, 0, -1, 1, -1, 0, -1, 1]
def label3685 : Mat3 := [1, 1, 0, 0, 1, -2, -1, -1, 1]
def label3760 : Mat3 := [1, 1, 0, 0, 2, -1, -1, -2, 1]
def label3777 : Mat3 := [1, 1, 0, 1, 1, -1, -2, -1, 1]
def label3790 : Mat3 := [1, 1, 0, 1, 2, -1, -2, -2, 1]
def label3839 : Mat3 := [1, 1, 0, 2, 1, -1, -2, 0, 1]
def label3868 : Mat3 := [1, 1, 1, -2, -1, -2, 0, 0, 1]
def label3869 : Mat3 := [1, 1, 1, -2, -1, -2, 0, 1, 1]
def label3878 : Mat3 := [1, 1, 1, -1, 0, -1, -1, -1, 0]
def label3880 : Mat3 := [1, 1, 1, -1, 0, -1, -1, 1, 0]
def label3887 : Mat3 := [1, 1, 1, -1, 0, -1, 1, 2, 2]
def label3897 : Mat3 := [1, 1, 1, -1, 1, -2, 1, 0, 2]
def label3985 : Mat3 := [1, 1, 1, 1, 2, 0, -1, -2, 1]
def label4079 : Mat3 := [1, 2, -3, 0, 1, -1, 0, -2, 3]
def label4085 : Mat3 := [1, 2, -2, -1, -1, 2, 0, -1, 1]
def label4086 : Mat3 := [1, 2, -2, -1, 0, 1, 0, -1, 1]
def label4106 : Mat3 := [1, 2, -2, 1, 2, -1, 0, -1, 1]
def label4108 : Mat3 := [1, 2, -2, 1, 3, -2, 0, -1, 1]
def label4110 : Mat3 := [1, 2, -1, -1, -1, 1, 0, -2, 1]
def label4114 : Mat3 := [1, 2, -1, -1, 1, 0, 0, -2, 1]
def label4115 : Mat3 := [1, 2, -1, 0, -1, 1, 0, -2, 1]
def label4117 : Mat3 := [1, 2, -1, 0, 1, -2, 0, 0, 1]
def label4147 : Mat3 := [1, 2, -1, 0, 3, -2, 0, -1, 1]
def label4148 : Mat3 := [1, 2, -1, 0, 3, -1, 0, -2, 1]
def label4149 : Mat3 := [1, 2, -1, 1, 1, 0, 0, -2, 1]
def label4150 : Mat3 := [1, 2, -1, 1, 2, 0, 0, -1, 1]
def label4152 : Mat3 := [1, 2, -1, 1, 3, -1, 0, -2, 1]
def label4155 : Mat3 := [1, 2, -1, 1, 3, 0, 0, 0, 1]
def label4157 : Mat3 := [1, 2, 0, -2, -3, 0, 0, 0, 1]
def label4158 : Mat3 := [1, 2, 0, -1, -1, -1, 0, 0, 1]
def label4160 : Mat3 := [1, 2, 0, -1, -1, 0, -1, -2, 1]
def label4168 : Mat3 := [1, 2, 0, -1, -1, 0, 1, 2, 1]
def label4171 : Mat3 := [1, 2, 0, -1, 0, -1, 1, 1, 1]
def label4173 : Mat3 := [1, 2, 0, -1, 1, -1, 1, 0, 1]
def label4178 : Mat3 := [1, 2, 0, 0, 1, -1, -1, -2, 1]
def label4216 : Mat3 := [1, 2, 0, 1, 1, -1, -1, 0, 1]
def label4218 : Mat3 := [1, 2, 0, 1, 2, -1, -1, -1, 1]
def label4260 : Mat3 := [1, 2, 1, 0, 1, 1, 0, -2, -1]
def label4320 : Mat3 := [1, 3, -2, 0, 1, 0, 0, -2, 1]
def label4322 : Mat3 := [1, 3, -2, 0, 2, -1, 0, -3, 2]
def label4326 : Mat3 := [1, 3, -1, 0, 1, 0, 0, -3, 1]
def label4333 : Mat3 := [1, 3, 0, 0, 1, -1, 0, 0, 1]
def label4368 : Mat3 := [2, -4, -1, 0, 1, 0, -1, 2, 1]
def label4371 : Mat3 := [2, -3, -3, 0, 1, 0, -1, 2, 2]
def label4374 : Mat3 := [2, -3, -1, -1, 2, 0, -1, 2, 1]
def label4379 : Mat3 := [2, -3, -1, 0, 1, 0, -1, 2, 1]
def label4405 : Mat3 := [2, -2, -3, 0, 1, 0, -1, 1, 2]
def label4406 : Mat3 := [2, -2, -3, 0, 1, 1, -1, 1, 2]
def label4407 : Mat3 := [2, -2, -1, -2, 3, 1, -1, 1, 1]
def label4408 : Mat3 := [2, -2, -1, -1, 1, 0, -1, 2, 1]
def label4411 : Mat3 := [2, -2, -1, -1, 2, 0, -1, 1, 1]
def label4414 : Mat3 := [2, -2, -1, 0, 1, -1, -1, 1, 1]
def label4420 : Mat3 := [2, -2, -1, 0, 1, 1, -1, 1, 1]
def label4422 : Mat3 := [2, -2, -1, 1, 0, -1, -1, 1, 1]
def label4423 : Mat3 := [2, -2, -1, 1, 0, 0, -1, 1, 1]
def label4424 : Mat3 := [2, -2, -1, 2, -1, -1, -1, 1, 1]
def label4432 : Mat3 := [2, -2, 1, 0, 1, -1, -1, 1, 0]
def label4446 : Mat3 := [2, -1, -3, -1, 1, 1, -1, 1, 2]
def label4451 : Mat3 := [2, -1, -3, 0, 1, 0, -1, 1, 2]
def label4453 : Mat3 := [2, -1, -2, -1, 1, 0, -1, 1, 1]
def label4467 : Mat3 := [2, -1, -2, 0, 1, 1, -1, 1, 2]
def label4470 : Mat3 := [2, -1, -1, -3, 2, 0, 0, 0, 1]
def label4471 : Mat3 := [2, -1, -1, -3, 2, 1, -1, 1, 1]
def label4475 : Mat3 := [2, -1, -1, -2, 1, 0, -1, 1, 1]
def label4478 : Mat3 := [2, -1, -1, -2, 2, 1, -1, 1, 1]
def label4501 : Mat3 := [2, -1, -1, -1, 2, 0, -1, 0, 1]
def label4502 : Mat3 := [2, -1, -1, -1, 2, 1, -1, 1, 1]
def label4503 : Mat3 := [2, -1, -1, 0, 0, -1, -1, 1, 1]
def label4513 : Mat3 := [2, -1, -1, 0, 2, 1, -1, 1, 1]
def label4519 : Mat3 := [2, -1, -1, 1, 1, 0, -1, 1, 1]
def label4521 : Mat3 := [2, -1, -1, 2, 0, -1, -1, 1, 1]
def label4522 : Mat3 := [2, -1, 0, -5, 3, 0, 0, 0, 1]
def label4523 : Mat3 := [2, -1, 0, -3, 2, -1, 0, 0, 1]
def label4525 : Mat3 := [2, -1, 0, -3, 2, 0, -3, 2, 1]
def label4526 : Mat3 := [2, -1, 0, -3, 2, 0, -2, 1, 1]
def label4534 : Mat3 := [2, -1, 0, -3, 2, 0, 2, -1, 1]
def label4535 : Mat3 := [2, -1, 0, -3, 2, 0, 3, -2, 1]
def label4545 : Mat3 := [2, -1, 0, -1, 1, -1, -2, 1, 1]
def label4586 : Mat3 := [2, -1, 0, 0, 1, -1, -1, 1, 0]
def label4630 : Mat3 := [2, -1, 1, -1, 1, 0, 2, -2, 1]
def label4639 : Mat3 := [2, -1, 1, 0, 1, 0, 1, -2, 1]
def label4680 : Mat3 := [2, 0, -5, 0, 1, 0, -1, 0, 3]
def label4681 : Mat3 := [2, 0, -3, -2, 1, 3, -1, 0, 2]
def label4682 : Mat3 := [2, 0, -3, -1, 1, 0, -1, 0, 2]
def label4683 : Mat3 := [2, 0, -3, -1, 1, 1, -1, 0, 2]
def label4684 : Mat3 := [2, 0, -3, -1, 1, 2, -1, 0, 2]
def label4685 : Mat3 := [2, 0, -3, 0, 1, -1, -1, 0, 2]
def label4688 : Mat3 := [2, 0, -3, 0, 1, 0, -1, 0, 2]
def label4691 : Mat3 := [2, 0, -3, 0, 1, 1, -1, 0, 2]
def label4692 : Mat3 := [2, 0, -3, 1, 1, -2, -1, 0, 2]
def label4693 : Mat3 := [2, 0, -3, 1, 1, -1, -1, 0, 2]
def label4694 : Mat3 := [2, 0, -3, 1, 1, 0, -1, 0, 2]
def label4695 : Mat3 := [2, 0, -3, 2, 1, -3, -1, 0, 2]
def label4696 : Mat3 := [2, 0, -1, -4, 1, 2, -1, 0, 1]
def label4697 : Mat3 := [2, 0, -1, -3, 1, 1, -1, 0, 1]
def label4700 : Mat3 := [2, 0, -1, -2, 1, 0, -1, 0, 1]
def label4701 : Mat3 := [2, 0, -1, -2, 1, 1, -3, 0, 2]
def label4702 : Mat3 := [2, 0, -1, -2, 1, 1, -3, 1, 2]
def label4703 : Mat3 := [2, 0, -1, -2, 1, 1, -1, -1, 1]
def label4704 : Mat3 := [2, 0, -1, -2, 1, 1, -1, 0, 1]
def label4706 : Mat3 := [2, 0, -1, -2, 1, 1, 1, -1, 0]
def label4711 : Mat3 := [2, 0, -1, -1, 1, -1, -1, 0, 1]
def label4714 : Mat3 := [2, 0, -1, -1, 1, 0, -1, 0, 1]
def label4722 : Mat3 := [2, 0, -1, -1, 1, 2, -1, 0, 1]
def label4724 : Mat3 := [2, 0, -1, 0, 1, -2, -1, 0, 1]
def label4727 : Mat3 := [2, 0, -1, 0, 1, -1, -1, 0, 1]
def label4745 : Mat3 := [2, 0, -1, 0, 1, 1, -1, 0, 1]
def label4748 : Mat3 := [2, 0, -1, 0, 1, 2, -1, 0, 1]
def label4751 : Mat3 := [2, 0, -1, 1, 1, -2, -1, 0, 1]
def label4762 : Mat3 := [2, 0, -1, 1, 1, 1, -1, 0, 1]
def label4772 : Mat3 := [2, 0, -1, 2, 1, 0, -1, 0, 1]
def label4775 : Mat3 := [2, 0, -1, 3, 1, -1, -1, 0, 1]
def label4777 : Mat3 := [2, 0, 1, -4, 1, -2, 1, 0, 1]
def label4782 : Mat3 := [2, 0, 1, -2, 1, -1, -1, 0, 0]
def label4783 : Mat3 := [2, 0, 1, -2, 1, -1, -1, 1, 0]
def label4784 : Mat3 := [2, 0, 1, -2, 1, -1, 1, -1, 1]
def label4787 : Mat3 := [2, 0, 1, -2, 1, -1, 3, -1, 2]
def label4788 : Mat3 := [2, 0, 1, -2, 1, -1, 3, 0, 2]
def label4801 : Mat3 := [2, 0, 1, -1, 1, 0, 2, -1, 1]
def label4807 : Mat3 := [2, 0, 1, 0, 1, -1, 1, -1, 2]
def label4825 : Mat3 := [2, 0, 1, 0, 1, 1, 1, -1, 0]
def label4864 : Mat3 := [2, 0, 3, 0, 1, 0, 1, -1, 2]
def label4875 : Mat3 := [2, 1, -3, 0, 1, 0, -1, -1, 2]
def label4879 : Mat3 := [2, 1, -3, 1, 1, -1, -1, -1, 2]
def label4883 : Mat3 := [2, 1, -2, 0, 1, -1, -1, -1, 2]
def label4896 : Mat3 := [2, 1, -2, 1, 1, 0, -1, -1, 1]
def label4899 : Mat3 := [2, 1, -1, -2, 0, 1, -1, -1, 1]
def label4905 : Mat3 := [2, 1, -1, -1, 1, 0, -1, -1, 1]
def label4907 : Mat3 := [2, 1, -1, 0, 0, 1, -1, -1, 1]
def label4917 : Mat3 := [2, 1, -1, 0, 2, -1, -1, -1, 1]
def label4918 : Mat3 := [2, 1, -1, 1, 1, -2, 0, 0, 1]
def label4940 : Mat3 := [2, 1, -1, 1, 2, -1, -1, -1, 1]
def label4941 : Mat3 := [2, 1, -1, 1, 2, 0, -1, 0, 1]
def label4942 : Mat3 := [2, 1, -1, 2, 1, -2, -1, 0, 1]
def label4943 : Mat3 := [2, 1, -1, 2, 1, 0, -1, -1, 1]
def label4944 : Mat3 := [2, 1, -1, 2, 2, -1, -1, -1, 1]
def label4948 : Mat3 := [2, 1, -1, 3, 2, -1, -1, -1, 1]
def label4950 : Mat3 := [2, 1, -1, 3, 2, 0, 0, 0, 1]
def label4969 : Mat3 := [2, 1, 0, 0, 1, 1, -1, -1, 0]
def label4971 : Mat3 := [2, 1, 0, 1, 0, -1, 0, 1, 1]
def label4974 : Mat3 := [2, 1, 0, 1, 1, -1, -2, -1, 1]
def label5010 : Mat3 := [2, 1, 0, 1, 2, -1, 0, -1, 1]
def label5012 : Mat3 := [2, 1, 0, 2, 1, -1, -1, 0, 1]
def label5109 : Mat3 := [2, 2, -3, 0, 1, -1, -1, -1, 2]
def label5110 : Mat3 := [2, 2, -3, 0, 1, 0, -1, -1, 2]
def label5111 : Mat3 := [2, 2, -1, -2, -1, 1, -1, -1, 1]
def label5112 : Mat3 := [2, 2, -1, -1, 0, 0, -1, -1, 1]
def label5113 : Mat3 := [2, 2, -1, -1, 0, 1, -1, -1, 1]
def label5114 : Mat3 := [2, 2, -1, 0, 1, -1, -1, -1, 1]
def label5121 : Mat3 := [2, 2, -1, 0, 1, 1, -1, -1, 1]
def label5123 : Mat3 := [2, 2, -1, 1, 1, 0, -1, -2, 1]
def label5127 : Mat3 := [2, 2, -1, 1, 2, 0, -1, -1, 1]
def label5128 : Mat3 := [2, 2, -1, 2, 3, -1, -1, -1, 1]
def label5138 : Mat3 := [2, 2, 1, 0, 1, 1, -1, -1, 0]
def label5149 : Mat3 := [2, 3, -3, 0, 1, 0, -1, -2, 2]
def label5153 : Mat3 := [2, 3, -1, 0, 1, 0, -1, -2, 1]
def label5157 : Mat3 := [2, 3, -1, 1, 2, 0, -1, -2, 1]
def label5160 : Mat3 := [2, 3, 0, 1, 2, -1, 0, 0, 1]
def label5184 : Mat3 := [2, 4, -1, 0, 1, 0, -1, -2, 1]
def label5190 : Mat3 := [3, -3, -1, 0, 1, 0, -2, 2, 1]
def label5199 : Mat3 := [3, -2, -1, -1, 1, 0, -2, 2, 1]
def label5203 : Mat3 := [3, -2, -1, 0, 1, 0, -2, 1, 1]
def label5233 : Mat3 := [3, -1, -2, -1, 1, 1, -2, 1, 2]
def label5236 : Mat3 := [3, -1, -2, 0, 1, 0, -1, 1, 1]
def label5237 : Mat3 := [3, -1, -1, -2, 1, 0, -2, 1, 1]
def label5242 : Mat3 := [3, -1, -1, -1, 1, 0, -2, 1, 1]
def label5245 : Mat3 := [3, -1, -1, 0, 1, 0, -2, 1, 1]
def label5278 : Mat3 := [3, 0, -4, 0, 1, 0, -2, 0, 3]
def label5279 : Mat3 := [3, 0, -2, -3, 1, 2, -1, 0, 1]
def label5280 : Mat3 := [3, 0, -2, -2, 1, 1, -1, 0, 1]
def label5292 : Mat3 := [3, 0, -2, 2, 1, -1, -1, 0, 1]
def label5293 : Mat3 := [3, 0, -2, 3, 1, -2, -1, 0, 1]
def label5294 : Mat3 := [3, 0, -1, -3, 1, 1, -2, 0, 1]
def label5295 : Mat3 := [3, 0, -1, -2, 1, 1, -2, 0, 1]
def label5296 : Mat3 := [3, 0, -1, -1, 1, 0, -2, 0, 1]
def label5297 : Mat3 := [3, 0, -1, -1, 1, 1, -2, 0, 1]
def label5298 : Mat3 := [3, 0, -1, 0, 1, -1, -2, 0, 1]
def label5301 : Mat3 := [3, 0, -1, 0, 1, 0, -2, 0, 1]
def label5304 : Mat3 := [3, 0, -1, 0, 1, 1, -2, 0, 1]
def label5305 : Mat3 := [3, 0, -1, 1, 1, -1, -2, 0, 1]
def label5306 : Mat3 := [3, 0, -1, 1, 1, 0, -2, 0, 1]
def label5307 : Mat3 := [3, 0, -1, 2, 1, -1, -2, 0, 1]
def label5308 : Mat3 := [3, 0, -1, 3, 1, -1, -2, 0, 1]
def label5315 : Mat3 := [3, 0, 1, 0, 1, 0, 2, -1, 1]
def label5330 : Mat3 := [3, 0, 2, 0, 1, 0, 1, -1, 1]
def label5342 : Mat3 := [3, 1, -2, 0, 1, 0, -1, -1, 1]
def label5344 : Mat3 := [3, 1, -2, 1, 1, -1, -2, -1, 2]
def label5348 : Mat3 := [3, 1, -1, 0, 1, 0, -2, -1, 1]
def label5350 : Mat3 := [3, 1, -1, 1, 1, 0, -2, -1, 1]
def label5355 : Mat3 := [3, 1, -1, 2, 1, 0, -2, -1, 1]
def label5358 : Mat3 := [3, 1, 0, 2, 1, -1, 0, 0, 1]
def label5393 : Mat3 := [3, 2, -1, 0, 1, 0, -2, -1, 1]
def label5395 : Mat3 := [3, 2, -1, 1, 1, 0, -2, -2, 1]
def label5400 : Mat3 := [3, 2, 0, 1, 1, -1, 0, 0, 1]
def label5426 : Mat3 := [3, 3, -1, 0, 1, 0, -2, -2, 1]
def label5432 : Mat3 := [4, -2, -1, -1, 1, 0, -2, 1, 1]
def label5438 : Mat3 := [4, 0, -1, 0, 1, 0, -3, 0, 1]
def label5444 : Mat3 := [4, 2, -1, 1, 1, 0, -2, -1, 1]
def label5449 : Mat3 := [5, 0, -3, 0, 1, 0, -3, 0, 2]
def basis : List Mat3 := [[0, -1, 0, 1, 1, 0, 0, 0, 1], [0, 0, -1, 0, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1, 0, -1, 0, 1], [0, 1, 0, -1, 1, 0, 0, 0, 1], [1, -2, 0, 0, 1, 0, 0, 0, 1], [1, -1, -1, 0, 1, 0, 0, 0, 1], [1, -1, -1, 0, 1, 0, 0, 1, 1], [1, -1, -1, 0, 1, 1, 0, 0, 1], [1, -1, 0, -1, 2, 0, 0, 0, 1], [1, -1, 0, 0, 1, -1, 0, 0, 1], [1, -1, 0, 0, 1, 0, -1, 0, 1], [1, -1, 0, 0, 1, 0, -1, 1, 1], [1, -1, 0, 0, 1, 0, 0, -1, 1], [1, -1, 0, 0, 1, 0, 0, 0, 1], [1, -1, 0, 0, 1, 0, 0, 1, 1], [1, -1, 0, 0, 1, 0, 1, -1, 1], [1, -1, 0, 0, 1, 0, 1, 0, 1], [1, -1, 0, 0, 1, 1, 0, 0, 1], [1, -1, 0, 1, 0, 0, 0, 0, 1], [1, -1, 1, 0, 1, -1, 0, 0, 1], [1, -1, 1, 0, 1, 0, 0, -1, 1], [1, -1, 1, 0, 1, 0, 0, 0, 1], [1, 0, -2, 0, 1, 0, 0, 0, 1], [1, 0, -1, -1, 1, 0, 0, 0, 1], [1, 0, -1, -1, 1, 1, 0, 0, 1], [1, 0, -1, 0, 1, -1, 0, 0, 1], [1, 0, -1, 0, 1, 0, -1, 0, 2], [1, 0, -1, 0, 1, 0, 0, -1, 1], [1, 0, -1, 0, 1, 0, 0, 0, 1], [1, 0, -1, 0, 1, 0, 0, 1, 1], [1, 0, -1, 0, 1, 0, 1, 0, 0], [1, 0, -1, 0, 1, 1, 0, 0, 1], [1, 0, -1, 1, 1, -1, 0, 0, 1], [1, 0, -1, 1, 1, 0, 0, 0, 1], [1, 0, 0, -2, 1, 0, 0, 0, 1], [1, 0, 0, -1, 1, -1, 0, 0, 1], [1, 0, 0, -1, 1, -1, 1, 0, 1], [1, 0, 0, -1, 1, 0, -1, 0, 1], [1, 0, 0, -1, 1, 0, -1, 1, 1], [1, 0, 0, -1, 1, 0, 0, -1, 1], [1, 0, 0, -1, 1, 0, 0, 0, 1], [1, 0, 0, -1, 1, 0, 0, 1, 1], [1, 0, 0, -1, 1, 0, 1, -1, 1], [1, 0, 0, -1, 1, 0, 1, 0, 1], [1, 0, 0, -1, 1, 1, -1, 0, 1], [1, 0, 0, -1, 1, 1, 0, 0, 1], [1, 0, 0, 0, 0, -1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 0, -1, 1], [1, 0, 0, 0, 1, -2, 0, 0, 1], [1, 0, 0, 0, 1, -1, -1, 0, 1], [1, 0, 0, 0, 1, -1, 0, -1, 2], [1, 0, 0, 0, 1, -1, 0, 0, 1], [1, 0, 0, 0, 1, -1, 0, 1, 0], [1, 0, 0, 0, 1, -1, 1, 0, 1], [1, 0, 0, 0, 1, 0, -2, 0, 1], [1, 0, 0, 0, 1, 0, -1, -1, 1], [1, 0, 0, 0, 1, 0, -1, 0, 1], [1, 0, 0, 0, 1, 0, -1, 1, 1], [1, 0, 0, 0, 1, 0, 0, -2, 1], [1, 0, 0, 0, 1, 0, 0, -1, 1], [1, 0, 0, 0, 1, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0, 0, 1, 1], [1, 0, 0, 0, 1, 0, 0, 2, 1], [1, 0, 0, 0, 1, 0, 1, -1, 1], [1, 0, 0, 0, 1, 0, 1, 0, 1], [1, 0, 0, 0, 1, 0, 1, 1, 1], [1, 0, 0, 0, 1, 0, 2, 0, 1], [1, 0, 0, 0, 1, 1, -1, 0, 1], [1, 0, 0, 0, 1, 1, 0, -1, 0], [1, 0, 0, 0, 1, 1, 0, 0, 1], [1, 0, 0, 0, 1, 1, 0, 1, 2], [1, 0, 0, 0, 1, 1, 1, 0, 1], [1, 0, 0, 0, 1, 2, 0, 0, 1], [1, 0, 0, 0, 2, -1, 0, -1, 1], [1, 0, 0, 0, 2, 1, 0, 1, 1], [1, 0, 0, 1, 1, -1, -1, 0, 1], [1, 0, 0, 1, 1, -1, 0, 0, 1], [1, 0, 0, 1, 1, 0, -1, -1, 1], [1, 0, 0, 1, 1, 0, -1, 0, 1], [1, 0, 0, 1, 1, 0, 0, -1, 1], [1, 0, 0, 1, 1, 0, 0, 0, 1], [1, 0, 0, 1, 1, 0, 0, 1, 1], [1, 0, 0, 1, 1, 0, 1, 0, 1], [1, 0, 0, 1, 1, 0, 1, 1, 1], [1, 0, 0, 1, 1, 1, 0, 0, 1], [1, 0, 0, 1, 1, 1, 1, 0, 1], [1, 0, 0, 2, 1, 0, 0, 0, 1], [1, 0, 1, -1, 1, -1, 0, 0, 1], [1, 0, 1, -1, 1, 0, 0, 0, 1], [1, 0, 1, 0, 1, -1, 0, 0, 1], [1, 0, 1, 0, 1, 0, -1, 0, 0], [1, 0, 1, 0, 1, 0, 0, -1, 1], [1, 0, 1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 1, 0, 0, 1, 1], [1, 0, 1, 0, 1, 0, 1, 0, 2], [1, 0, 1, 0, 1, 1, 0, 0, 1], [1, 0, 1, 1, 1, 0, 0, 0, 1], [1, 0, 1, 1, 1, 1, 0, 0, 1], [1, 0, 2, 0, 1, 0, 0, 0, 1], [1, 1, -1, 0, 1, -1, 0, 0, 1], [1, 1, -1, 0, 1, 0, 0, -1, 1], [1, 1, -1, 0, 1, 0, 0, 0, 1], [1, 1, 0, -1, 0, 0, 0, 0, 1], [1, 1, 0, 0, 1, -1, 0, 0, 1], [1, 1, 0, 0, 1, 0, -1, -1, 1], [1, 1, 0, 0, 1, 0, -1, 0, 1], [1, 1, 0, 0, 1, 0, 0, -1, 1], [1, 1, 0, 0, 1, 0, 0, 0, 1], [1, 1, 0, 0, 1, 0, 0, 1, 1], [1, 1, 0, 0, 1, 0, 1, 0, 1], [1, 1, 0, 0, 1, 0, 1, 1, 1], [1, 1, 0, 0, 1, 1, 0, 0, 1], [1, 1, 0, 1, 2, 0, 0, 0, 1], [1, 1, 1, 0, 1, 0, 0, 0, 1], [1, 1, 1, 0, 1, 0, 0, 1, 1], [1, 1, 1, 0, 1, 1, 0, 0, 1], [1, 2, 0, 0, 1, 0, 0, 0, 1], [2, -1, 0, -1, 1, 0, 0, 0, 1], [2, 0, -1, 0, 1, 0, -1, 0, 1], [2, 0, 1, 0, 1, 0, 1, 0, 1], [2, 1, 0, 1, 1, 0, 0, 0, 1]]
def delta : Poly Mat3 := (matOne, 12) :: generators.map (fun g => (g, -1))
def polyMul (x y : Poly Mat3) : Poly Mat3 := x.flatMap (fun p => y.map (fun q => (matMul p.1 q.1, p.2*q.2)))
def residualRow0 : Poly Mat3 := (polyMul delta delta).map (fun p => (p.1, 10000000000000*p.2))
def residualRow1 : Poly Mat3 := delta.map (fun p => (p.1, -1000000000000*p.2))
def residualRow2 : Poly Mat3 := (basis.zip gramRow0).map (fun q => (matMul (matInv [0, -1, 0, 1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow3 : Poly Mat3 := (basis.zip gramRow1).map (fun q => (matMul (matInv [0, 0, -1, 0, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow4 : Poly Mat3 := (basis.zip gramRow2).map (fun q => (matMul (matInv [0, 0, 1, 0, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow5 : Poly Mat3 := (basis.zip gramRow3).map (fun q => (matMul (matInv [0, 1, 0, -1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow6 : Poly Mat3 := (basis.zip gramRow4).map (fun q => (matMul (matInv [1, -2, 0, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow7 : Poly Mat3 := (basis.zip gramRow5).map (fun q => (matMul (matInv [1, -1, -1, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow8 : Poly Mat3 := (basis.zip gramRow6).map (fun q => (matMul (matInv [1, -1, -1, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow9 : Poly Mat3 := (basis.zip gramRow7).map (fun q => (matMul (matInv [1, -1, -1, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow10 : Poly Mat3 := (basis.zip gramRow8).map (fun q => (matMul (matInv [1, -1, 0, -1, 2, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow11 : Poly Mat3 := (basis.zip gramRow9).map (fun q => (matMul (matInv [1, -1, 0, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow12 : Poly Mat3 := (basis.zip gramRow10).map (fun q => (matMul (matInv [1, -1, 0, 0, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow13 : Poly Mat3 := (basis.zip gramRow11).map (fun q => (matMul (matInv [1, -1, 0, 0, 1, 0, -1, 1, 1]) q.1, -10*q.2))
def residualRow14 : Poly Mat3 := (basis.zip gramRow12).map (fun q => (matMul (matInv [1, -1, 0, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow15 : Poly Mat3 := (basis.zip gramRow13).map (fun q => (matMul (matInv [1, -1, 0, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow16 : Poly Mat3 := (basis.zip gramRow14).map (fun q => (matMul (matInv [1, -1, 0, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow17 : Poly Mat3 := (basis.zip gramRow15).map (fun q => (matMul (matInv [1, -1, 0, 0, 1, 0, 1, -1, 1]) q.1, -10*q.2))
def residualRow18 : Poly Mat3 := (basis.zip gramRow16).map (fun q => (matMul (matInv [1, -1, 0, 0, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow19 : Poly Mat3 := (basis.zip gramRow17).map (fun q => (matMul (matInv [1, -1, 0, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow20 : Poly Mat3 := (basis.zip gramRow18).map (fun q => (matMul (matInv [1, -1, 0, 1, 0, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow21 : Poly Mat3 := (basis.zip gramRow19).map (fun q => (matMul (matInv [1, -1, 1, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow22 : Poly Mat3 := (basis.zip gramRow20).map (fun q => (matMul (matInv [1, -1, 1, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow23 : Poly Mat3 := (basis.zip gramRow21).map (fun q => (matMul (matInv [1, -1, 1, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow24 : Poly Mat3 := (basis.zip gramRow22).map (fun q => (matMul (matInv [1, 0, -2, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow25 : Poly Mat3 := (basis.zip gramRow23).map (fun q => (matMul (matInv [1, 0, -1, -1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow26 : Poly Mat3 := (basis.zip gramRow24).map (fun q => (matMul (matInv [1, 0, -1, -1, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow27 : Poly Mat3 := (basis.zip gramRow25).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow28 : Poly Mat3 := (basis.zip gramRow26).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 0, -1, 0, 2]) q.1, -10*q.2))
def residualRow29 : Poly Mat3 := (basis.zip gramRow27).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow30 : Poly Mat3 := (basis.zip gramRow28).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow31 : Poly Mat3 := (basis.zip gramRow29).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow32 : Poly Mat3 := (basis.zip gramRow30).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 0, 1, 0, 0]) q.1, -10*q.2))
def residualRow33 : Poly Mat3 := (basis.zip gramRow31).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow34 : Poly Mat3 := (basis.zip gramRow32).map (fun q => (matMul (matInv [1, 0, -1, 1, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow35 : Poly Mat3 := (basis.zip gramRow33).map (fun q => (matMul (matInv [1, 0, -1, 1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow36 : Poly Mat3 := (basis.zip gramRow34).map (fun q => (matMul (matInv [1, 0, 0, -2, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow37 : Poly Mat3 := (basis.zip gramRow35).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow38 : Poly Mat3 := (basis.zip gramRow36).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, -1, 1, 0, 1]) q.1, -10*q.2))
def residualRow39 : Poly Mat3 := (basis.zip gramRow37).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow40 : Poly Mat3 := (basis.zip gramRow38).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, -1, 1, 1]) q.1, -10*q.2))
def residualRow41 : Poly Mat3 := (basis.zip gramRow39).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow42 : Poly Mat3 := (basis.zip gramRow40).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow43 : Poly Mat3 := (basis.zip gramRow41).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow44 : Poly Mat3 := (basis.zip gramRow42).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, 1, -1, 1]) q.1, -10*q.2))
def residualRow45 : Poly Mat3 := (basis.zip gramRow43).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow46 : Poly Mat3 := (basis.zip gramRow44).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 1, -1, 0, 1]) q.1, -10*q.2))
def residualRow47 : Poly Mat3 := (basis.zip gramRow45).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow48 : Poly Mat3 := (basis.zip gramRow46).map (fun q => (matMul (matInv [1, 0, 0, 0, 0, -1, 0, 1, 1]) q.1, -10*q.2))
def residualRow49 : Poly Mat3 := (basis.zip gramRow47).map (fun q => (matMul (matInv [1, 0, 0, 0, 0, 1, 0, -1, 1]) q.1, -10*q.2))
def residualRow50 : Poly Mat3 := (basis.zip gramRow48).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -2, 0, 0, 1]) q.1, -10*q.2))
def residualRow51 : Poly Mat3 := (basis.zip gramRow49).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -1, -1, 0, 1]) q.1, -10*q.2))
def residualRow52 : Poly Mat3 := (basis.zip gramRow50).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -1, 0, -1, 2]) q.1, -10*q.2))
def residualRow53 : Poly Mat3 := (basis.zip gramRow51).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow54 : Poly Mat3 := (basis.zip gramRow52).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -1, 0, 1, 0]) q.1, -10*q.2))
def residualRow55 : Poly Mat3 := (basis.zip gramRow53).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -1, 1, 0, 1]) q.1, -10*q.2))
def residualRow56 : Poly Mat3 := (basis.zip gramRow54).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, -2, 0, 1]) q.1, -10*q.2))
def residualRow57 : Poly Mat3 := (basis.zip gramRow55).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, -1, -1, 1]) q.1, -10*q.2))
def residualRow58 : Poly Mat3 := (basis.zip gramRow56).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow59 : Poly Mat3 := (basis.zip gramRow57).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, -1, 1, 1]) q.1, -10*q.2))
def residualRow60 : Poly Mat3 := (basis.zip gramRow58).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 0, -2, 1]) q.1, -10*q.2))
def residualRow61 : Poly Mat3 := (basis.zip gramRow59).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow62 : Poly Mat3 := (basis.zip gramRow60).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow63 : Poly Mat3 := (basis.zip gramRow61).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow64 : Poly Mat3 := (basis.zip gramRow62).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 0, 2, 1]) q.1, -10*q.2))
def residualRow65 : Poly Mat3 := (basis.zip gramRow63).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 1, -1, 1]) q.1, -10*q.2))
def residualRow66 : Poly Mat3 := (basis.zip gramRow64).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow67 : Poly Mat3 := (basis.zip gramRow65).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 1, 1, 1]) q.1, -10*q.2))
def residualRow68 : Poly Mat3 := (basis.zip gramRow66).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 2, 0, 1]) q.1, -10*q.2))
def residualRow69 : Poly Mat3 := (basis.zip gramRow67).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 1, -1, 0, 1]) q.1, -10*q.2))
def residualRow70 : Poly Mat3 := (basis.zip gramRow68).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 1, 0, -1, 0]) q.1, -10*q.2))
def residualRow71 : Poly Mat3 := (basis.zip gramRow69).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow72 : Poly Mat3 := (basis.zip gramRow70).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 1, 0, 1, 2]) q.1, -10*q.2))
def residualRow73 : Poly Mat3 := (basis.zip gramRow71).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 1, 1, 0, 1]) q.1, -10*q.2))
def residualRow74 : Poly Mat3 := (basis.zip gramRow72).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 2, 0, 0, 1]) q.1, -10*q.2))
def residualRow75 : Poly Mat3 := (basis.zip gramRow73).map (fun q => (matMul (matInv [1, 0, 0, 0, 2, -1, 0, -1, 1]) q.1, -10*q.2))
def residualRow76 : Poly Mat3 := (basis.zip gramRow74).map (fun q => (matMul (matInv [1, 0, 0, 0, 2, 1, 0, 1, 1]) q.1, -10*q.2))
def residualRow77 : Poly Mat3 := (basis.zip gramRow75).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, -1, -1, 0, 1]) q.1, -10*q.2))
def residualRow78 : Poly Mat3 := (basis.zip gramRow76).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow79 : Poly Mat3 := (basis.zip gramRow77).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, -1, -1, 1]) q.1, -10*q.2))
def residualRow80 : Poly Mat3 := (basis.zip gramRow78).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow81 : Poly Mat3 := (basis.zip gramRow79).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow82 : Poly Mat3 := (basis.zip gramRow80).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow83 : Poly Mat3 := (basis.zip gramRow81).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow84 : Poly Mat3 := (basis.zip gramRow82).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow85 : Poly Mat3 := (basis.zip gramRow83).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, 1, 1, 1]) q.1, -10*q.2))
def residualRow86 : Poly Mat3 := (basis.zip gramRow84).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow87 : Poly Mat3 := (basis.zip gramRow85).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 1, 1, 0, 1]) q.1, -10*q.2))
def residualRow88 : Poly Mat3 := (basis.zip gramRow86).map (fun q => (matMul (matInv [1, 0, 0, 2, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow89 : Poly Mat3 := (basis.zip gramRow87).map (fun q => (matMul (matInv [1, 0, 1, -1, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow90 : Poly Mat3 := (basis.zip gramRow88).map (fun q => (matMul (matInv [1, 0, 1, -1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow91 : Poly Mat3 := (basis.zip gramRow89).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow92 : Poly Mat3 := (basis.zip gramRow90).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 0, -1, 0, 0]) q.1, -10*q.2))
def residualRow93 : Poly Mat3 := (basis.zip gramRow91).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow94 : Poly Mat3 := (basis.zip gramRow92).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow95 : Poly Mat3 := (basis.zip gramRow93).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow96 : Poly Mat3 := (basis.zip gramRow94).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 0, 1, 0, 2]) q.1, -10*q.2))
def residualRow97 : Poly Mat3 := (basis.zip gramRow95).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow98 : Poly Mat3 := (basis.zip gramRow96).map (fun q => (matMul (matInv [1, 0, 1, 1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow99 : Poly Mat3 := (basis.zip gramRow97).map (fun q => (matMul (matInv [1, 0, 1, 1, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow100 : Poly Mat3 := (basis.zip gramRow98).map (fun q => (matMul (matInv [1, 0, 2, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow101 : Poly Mat3 := (basis.zip gramRow99).map (fun q => (matMul (matInv [1, 1, -1, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow102 : Poly Mat3 := (basis.zip gramRow100).map (fun q => (matMul (matInv [1, 1, -1, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow103 : Poly Mat3 := (basis.zip gramRow101).map (fun q => (matMul (matInv [1, 1, -1, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow104 : Poly Mat3 := (basis.zip gramRow102).map (fun q => (matMul (matInv [1, 1, 0, -1, 0, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow105 : Poly Mat3 := (basis.zip gramRow103).map (fun q => (matMul (matInv [1, 1, 0, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow106 : Poly Mat3 := (basis.zip gramRow104).map (fun q => (matMul (matInv [1, 1, 0, 0, 1, 0, -1, -1, 1]) q.1, -10*q.2))
def residualRow107 : Poly Mat3 := (basis.zip gramRow105).map (fun q => (matMul (matInv [1, 1, 0, 0, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow108 : Poly Mat3 := (basis.zip gramRow106).map (fun q => (matMul (matInv [1, 1, 0, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow109 : Poly Mat3 := (basis.zip gramRow107).map (fun q => (matMul (matInv [1, 1, 0, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow110 : Poly Mat3 := (basis.zip gramRow108).map (fun q => (matMul (matInv [1, 1, 0, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow111 : Poly Mat3 := (basis.zip gramRow109).map (fun q => (matMul (matInv [1, 1, 0, 0, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow112 : Poly Mat3 := (basis.zip gramRow110).map (fun q => (matMul (matInv [1, 1, 0, 0, 1, 0, 1, 1, 1]) q.1, -10*q.2))
def residualRow113 : Poly Mat3 := (basis.zip gramRow111).map (fun q => (matMul (matInv [1, 1, 0, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow114 : Poly Mat3 := (basis.zip gramRow112).map (fun q => (matMul (matInv [1, 1, 0, 1, 2, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow115 : Poly Mat3 := (basis.zip gramRow113).map (fun q => (matMul (matInv [1, 1, 1, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow116 : Poly Mat3 := (basis.zip gramRow114).map (fun q => (matMul (matInv [1, 1, 1, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow117 : Poly Mat3 := (basis.zip gramRow115).map (fun q => (matMul (matInv [1, 1, 1, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow118 : Poly Mat3 := (basis.zip gramRow116).map (fun q => (matMul (matInv [1, 2, 0, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow119 : Poly Mat3 := (basis.zip gramRow117).map (fun q => (matMul (matInv [2, -1, 0, -1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow120 : Poly Mat3 := (basis.zip gramRow118).map (fun q => (matMul (matInv [2, 0, -1, 0, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow121 : Poly Mat3 := (basis.zip gramRow119).map (fun q => (matMul (matInv [2, 0, 1, 0, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow122 : Poly Mat3 := (basis.zip gramRow120).map (fun q => (matMul (matInv [2, 1, 0, 1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRows : List (Poly Mat3) := [residualRow0, residualRow1, residualRow2, residualRow3, residualRow4, residualRow5, residualRow6, residualRow7, residualRow8, residualRow9, residualRow10, residualRow11, residualRow12, residualRow13, residualRow14, residualRow15, residualRow16, residualRow17, residualRow18, residualRow19, residualRow20, residualRow21, residualRow22, residualRow23, residualRow24, residualRow25, residualRow26, residualRow27, residualRow28, residualRow29, residualRow30, residualRow31, residualRow32, residualRow33, residualRow34, residualRow35, residualRow36, residualRow37, residualRow38, residualRow39, residualRow40, residualRow41, residualRow42, residualRow43, residualRow44, residualRow45, residualRow46, residualRow47, residualRow48, residualRow49, residualRow50, residualRow51, residualRow52, residualRow53, residualRow54, residualRow55, residualRow56, residualRow57, residualRow58, residualRow59, residualRow60, residualRow61, residualRow62, residualRow63, residualRow64, residualRow65, residualRow66, residualRow67, residualRow68, residualRow69, residualRow70, residualRow71, residualRow72, residualRow73, residualRow74, residualRow75, residualRow76, residualRow77, residualRow78, residualRow79, residualRow80, residualRow81, residualRow82, residualRow83, residualRow84, residualRow85, residualRow86, residualRow87, residualRow88, residualRow89, residualRow90, residualRow91, residualRow92, residualRow93, residualRow94, residualRow95, residualRow96, residualRow97, residualRow98, residualRow99, residualRow100, residualRow101, residualRow102, residualRow103, residualRow104, residualRow105, residualRow106, residualRow107, residualRow108, residualRow109, residualRow110, residualRow111, residualRow112, residualRow113, residualRow114, residualRow115, residualRow116, residualRow117, residualRow118, residualRow119, residualRow120, residualRow121, residualRow122]
end NuclearUltrapower.SOS
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/- Exact rational SOS data. All asserted computed identities reduce in the
   stock Lean kernel; the numerical program and these literals are untrusted. -/
namespace NuclearUltrapower.SL3Certificate
def gram : List (List ℤ) := [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, g81, g82, g83, g84, g85, g86, g87, g88, g89, g90, g91, g92, g93, g94, g95, g96, g97, g98, g99, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119, g120]
end NuclearUltrapower.SL3Certificate
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate
def gramData : List (List ℤ) := [gramRow0, gramRow1, gramRow2, gramRow3, gramRow4, gramRow5, gramRow6, gramRow7, gramRow8, gramRow9, gramRow10, gramRow11, gramRow12, gramRow13, gramRow14, gramRow15, gramRow16, gramRow17, gramRow18, gramRow19, gramRow20, gramRow21, gramRow22, gramRow23, gramRow24, gramRow25, gramRow26, gramRow27, gramRow28, gramRow29, gramRow30, gramRow31, gramRow32, gramRow33, gramRow34, gramRow35, gramRow36, gramRow37, gramRow38, gramRow39, gramRow40, gramRow41, gramRow42, gramRow43, gramRow44, gramRow45, gramRow46, gramRow47, gramRow48, gramRow49, gramRow50, gramRow51, gramRow52, gramRow53, gramRow54, gramRow55, gramRow56, gramRow57, gramRow58, gramRow59, gramRow60, gramRow61, gramRow62, gramRow63, gramRow64, gramRow65, gramRow66, gramRow67, gramRow68, gramRow69, gramRow70, gramRow71, gramRow72, gramRow73, gramRow74, gramRow75, gramRow76, gramRow77, gramRow78, gramRow79, gramRow80, gramRow81, gramRow82, gramRow83, gramRow84, gramRow85, gramRow86, gramRow87, gramRow88, gramRow89, gramRow90, gramRow91, gramRow92, gramRow93, gramRow94, gramRow95, gramRow96, gramRow97, gramRow98, gramRow99, gramRow100, gramRow101, gramRow102, gramRow103, gramRow104, gramRow105, gramRow106, gramRow107, gramRow108, gramRow109, gramRow110, gramRow111, gramRow112, gramRow113, gramRow114, gramRow115, gramRow116, gramRow117, gramRow118, gramRow119, gramRow120]
end NuclearUltrapower.SOS
end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceElementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary generators in the finite congruence quotients -/

noncomputable section

namespace CoarseAssembly

open Congruence
open NuclearUltrapower

def secondDiagonal (k : ℕ) (u : (ZMod (2 ^ k))ˣ) : Congruence.Quotient k :=
  ⟨Matrix.diagonal ![1, (u : ZMod (2 ^ k)), ((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))], by
    simp [Matrix.det_diagonal, Fin.prod_univ_succ]⟩

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsWindingTest
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Winding tests from the short-loop theorem

This connects the proved graph-theoretic small-loop argument to the actual
continuous circle map and its real path lift. It assumes no analytic pairing
or nonvanishing conclusion.
-/

noncomputable section

namespace CoarseAssembly

open Rips

variable {X : Type*} {G : SimpleGraph X}

def graphRipsCocycle (hG : G.Connected) (a : X → X → ℤ)
    (ha : ∀ x y, G.Adj x y → a y x = -a x y) (r : ℕ)
    (hloop : ∀ x (p : G.Walk x x), p.length ≤ 3 * r → walkCharge a p = 0) :
    letI := graphMetric G hG
    IntegralCocycle X (r : ℝ) := by
  let := graphMetric G hG
  have hloop₂ : ∀ x (p : G.Walk x x), p.length ≤ 2 * r → walkCharge a p = 0 := by
    intro x p hp
    exact hloop x p (by omega)
  have toBound : ∀ x y : X, dist x y ≤ (r : ℝ) → G.dist x y ≤ r := by
    intro x y h
    change @dist X (graphMetric G hG).toDist x y ≤ (r : ℝ) at h
    rw [graphMetric_eq G hG] at h
    change (G.dist x y : ℝ) ≤ r at h
    exact_mod_cast h
  exact
    { charge := ripsCharge hG a
      antisymm := fun x y hxy => ripsCharge_antisymm hG a ha r hloop₂
        (toBound x y hxy)
      triangle := fun x y z hxy hyz hzx => ripsCharge_triangle hG a r hloop
        (toBound x y hxy) (toBound y z hyz) (toBound z x hzx) }

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteWindingIndex
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic winding test on a finite Rips component

This derives the finite-component index evaluation from the explicit
published scalar-circle pairing. The cocycle, continuous map, parametrized
loop and its degree are explicit.
-/

noncomputable section

namespace CoarseAssembly

open Rips Analytic

variable {X : Type} [Fintype X] {G : SimpleGraph X}

omit [Fintype X] in
theorem graphEdgeBound (hG : G.Connected) (r : ℕ) (hr : 1 ≤ r) :
    letI := graphMetric G hG
    ∀ x y, G.Adj x y → dist x y ≤ (r : ℝ) := by
  let := graphMetric G hG
  intro x y h
  rw [graphMetric_eq G hG]
  change (G.dist x y : ℝ) ≤ r
  exact_mod_cast (G.dist_le h.toWalk).trans (by simpa using hr)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitPersistence
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Persistence of the explicit circle cycle in the actual graph union -/

noncomputable section

namespace CoarseAssembly

open Topology Congruence Rips Analytic

local instance explicitPersistenceComponent (j : ℕ) : MetricSpace (FiberVertex j) :=
  componentMetric elementaryMoves chosenHolonomyUnit j

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitBoundaryConclusion
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counterexample with circle, filling and additivity inputs discharged -/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

local instance explicitBoundaryMetric3_rb9141f_1 : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
local instance explicitBoundaryMetric4 : PseudoMetricSpace BoundaryVertex :=
  (boundaryMetric elementaryMoves chosenHolonomyUnit).toPseudoMetricSpace
local instance explicitBoundaryMetric5 (j : ℕ) : MetricSpace (FiberVertex j) :=
  componentMetric elementaryMoves chosenHolonomyUnit j

end CoarseAssembly

end

end OAI
end


