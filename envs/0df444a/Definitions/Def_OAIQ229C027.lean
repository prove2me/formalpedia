-- Prove2me | Definitions.Def_OAIQ229C027
-- name    : OAIQ229C027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T10:57:43.029811+00:00
-- url     : https://prove2.me/theorems/4fc0654a-5c34-45cb-ac34-ea735dd44bed
-- title:
--   Definitions bundle OAIQ229C027 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 9 definitions and 12 theorems. The definitions and types are `OAI.CoarseAssembly.fiberedBoundaryLoops`, `OAI.CoarseAssembly.filledBoundaryLoops`, `OAI.CoarseAssembly.filledSegment`, `OAI.CoarseAssembly.filledWalk`, `OAI.CoarseAssembly.hexagonalBoundaryWalks`, `OAI.CoarseAssembly.leftTranslationHom`, `OAI.CoarseAssembly.translationEnergy`, `OAI.NuclearUltrapower.SOS.allRowBuckets`, `OAI.NuclearUltrapower.SOS.residualBucket`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_Averaging`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/Averaging.lean), [`CoarseAssembly_AveragingEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/AveragingEnergy.lean), [`CoarseAssembly_AveragingPropagation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/AveragingPropagation.lean), [`CoarseAssembly_FamilyFilling`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/FamilyFilling.lean), [`CoarseAssembly_FiberedPersistence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/FiberedPersistence.lean), [`CoarseAssembly_FilledEdges`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/FilledEdges.lean), [`CoarseAssembly_FilledWalks`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/FilledWalks.lean), [`CoarseAssembly_HexagonSides`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/HexagonSides.lean), [`CoarseAssembly_RegularConstants`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RegularConstants.lean), `NuclearUltrapower_SOSResidual`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C019`, `OAIQ229C020`, `OAIQ229C021`, `OAIQ229C022` and `OAIQ229C023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C028`, `OAIQ229C029`, `OAIQ229C030` and `OAIQ229C031`; the statements `OAI.NuclearUltrapower.SOS.bucket_aug_0_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_100_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_101_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_102_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_103_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_104_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_105_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_106_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_107_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_108_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_109_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_10_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_110_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_111_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_112_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_113_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_114_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_115_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_116_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_117_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_118_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_119_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_11_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_120_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_121_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_122_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_123_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_124_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_125_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_126_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_127_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_12_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_13_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_14_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_15_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_16_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_17_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_18_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_19_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_1_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_20_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_21_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_22_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_23_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_24_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_25_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_26_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_27_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_28_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_29_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_2_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_30_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_31_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_32_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_33_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_34_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_35_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_36_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_37_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_38_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_39_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_3_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_40_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_41_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_42_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_43_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_44_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_45_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_46_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_47_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_48_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_49_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_4_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_50_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_51_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_52_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_53_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_54_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_55_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_56_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_57_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_58_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_59_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_5_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_60_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_61_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_62_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_63_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_64_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_65_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_66_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_67_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_68_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_69_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_6_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_70_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_71_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_72_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_73_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_74_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_75_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_76_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_77_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_78_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_79_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_7_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_80_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_81_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_82_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_83_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_84_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_85_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_86_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_87_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_88_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_89_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_8_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_90_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_91_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_92_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_93_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_94_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_95_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_96_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_97_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_98_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_99_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_9_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_0_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_100_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_101_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_102_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_103_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_104_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_105_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_106_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_107_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_108_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_109_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_10_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_110_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_111_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_112_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_113_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_114_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_115_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_116_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_117_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_118_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_119_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_11_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_120_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_121_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_122_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_123_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_124_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_125_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_126_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_127_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_12_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_13_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_14_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_15_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_16_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_17_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_18_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_19_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_1_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_20_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_21_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_22_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_23_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_24_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_25_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_26_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_27_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_28_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_29_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_2_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_30_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_31_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_32_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_33_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_34_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_35_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_36_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_37_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_38_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_39_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_3_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_40_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_41_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_42_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_43_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_44_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_45_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_46_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_47_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_48_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_49_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_4_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_50_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_51_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_52_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_53_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_54_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_55_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_56_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_57_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_58_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_59_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_5_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_60_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_61_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_62_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_63_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_64_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_65_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_66_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_67_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_68_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_69_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_6_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_70_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_71_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_72_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_73_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_74_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_75_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_76_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_77_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_78_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_79_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_7_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_80_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_81_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_82_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_83_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_84_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_85_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_86_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_87_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_88_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_89_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_8_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_90_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_91_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_92_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_93_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_94_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_95_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_96_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_97_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_98_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_99_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_9_ca`, `OAI.NuclearUltrapower.SOS.row_length_bound_ca`, `OAI.NuclearUltrapower.SOS.row_lengths_ca` and `OAI.NuclearUltrapower.SOS.row_normalizations_ca`; the proofs of `OAI.NuclearUltrapower.SOS.bucket_aug_0_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_100_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_101_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_102_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_103_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_104_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_105_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_106_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_107_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_108_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_109_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_10_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_110_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_111_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_112_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_113_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_114_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_115_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_116_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_117_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_118_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_119_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_11_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_120_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_121_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_122_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_123_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_124_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_125_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_126_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_127_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_12_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_13_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_14_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_15_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_16_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_17_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_18_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_19_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_1_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_20_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_21_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_22_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_23_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_24_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_25_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_26_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_27_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_28_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_29_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_2_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_30_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_31_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_32_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_33_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_34_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_35_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_36_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_37_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_38_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_39_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_3_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_40_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_41_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_42_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_43_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_44_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_45_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_46_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_47_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_48_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_49_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_4_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_50_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_51_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_52_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_53_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_54_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_55_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_56_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_57_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_58_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_59_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_5_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_60_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_61_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_62_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_63_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_64_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_65_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_66_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_67_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_68_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_69_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_6_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_70_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_71_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_72_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_73_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_74_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_75_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_76_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_77_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_78_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_79_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_7_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_80_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_81_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_82_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_83_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_84_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_85_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_86_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_87_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_88_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_89_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_8_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_90_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_91_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_92_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_93_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_94_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_95_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_96_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_97_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_98_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_99_ca`, `OAI.NuclearUltrapower.SOS.bucket_aug_9_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_0_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_100_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_101_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_102_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_103_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_104_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_105_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_106_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_107_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_108_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_109_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_10_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_110_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_111_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_112_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_113_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_114_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_115_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_116_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_117_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_118_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_119_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_11_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_120_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_121_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_122_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_123_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_124_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_125_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_126_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_127_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_12_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_13_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_14_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_15_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_16_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_17_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_18_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_19_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_1_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_20_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_21_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_22_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_23_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_24_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_25_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_26_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_27_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_28_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_29_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_2_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_30_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_31_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_32_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_33_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_34_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_35_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_36_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_37_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_38_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_39_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_3_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_40_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_41_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_42_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_43_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_44_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_45_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_46_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_47_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_48_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_49_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_4_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_50_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_51_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_52_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_53_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_54_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_55_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_56_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_57_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_58_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_59_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_5_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_60_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_61_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_62_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_63_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_64_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_65_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_66_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_67_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_68_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_69_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_6_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_70_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_71_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_72_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_73_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_74_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_75_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_76_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_77_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_78_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_79_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_7_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_80_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_81_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_82_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_83_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_84_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_85_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_86_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_87_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_88_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_89_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_8_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_90_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_91_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_92_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_93_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_94_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_95_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_96_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_97_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_98_ca`, `OAI.NuclearUltrapower.SOS.bucket_l1_99_ca` and `OAI.NuclearUltrapower.SOS.bucket_l1_9_ca`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
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
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
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
import Definitions.Def_OAIQ229C019
import Definitions.Def_OAIQ229C020
import Definitions.Def_OAIQ229C021
import Definitions.Def_OAIQ229C022
import Definitions.Def_OAIQ229C023

section
-- module Solutions.Q229_CA.CoarseAssembly_Averaging
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Congruence.holonomyCharge_reduceSteps _root_.OAI.CoarseAssembly.Congruence.holonomyWord_reduceSteps _root_.OAI.CoarseAssembly.mem_fiberedNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite-quotient averaging operators

Normalized left translations and their lazy average act on the spatial
fiber Hilbert spaces. They are contractions fixing the constant subspace.
The strict norm bound off constants is kept as the precise published
Kazhdan-gap input, rather than assuming any Roe transfer conclusion.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (Q : Type*) [Fintype Q] [Nonempty Q]

theorem constantProjection_idempotent :
    constantProjection (H := H) Q * constantProjection Q = constantProjection Q := by
  ext x
  simp [constantProjection]

variable [Group Q]

omit [CompleteSpace H] [Nonempty Q] in
theorem leftTranslation_constant (g : Q) (h : H) :
    leftTranslation Q g (fiberConstant Q h) = fiberConstant Q h :=
  reindexFiber_constant _ _

theorem leftTranslation_projection (g : Q) :
    (leftTranslation (H := H) Q g).toLinearIsometry.toContinuousLinearMap *
      constantProjection Q = constantProjection Q := by
  apply ContinuousLinearMap.ext
  intro x
  change leftTranslation (H := H) Q g (fiberConstant (H := H) Q _) =
    fiberConstant (H := H) Q _
  exact leftTranslation_constant (H := H) Q g _

theorem projection_leftTranslation (g : Q) :
    constantProjection (H := H) Q *
      (leftTranslation Q g).toLinearIsometry.toContinuousLinearMap = constantProjection Q := by
  have he : (leftTranslation (H := H) Q g).toLinearIsometry.toContinuousLinearMap.adjoint =
      (leftTranslation Q g⁻¹).toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    have hi := (leftTranslation (H := H) Q g).inner_map_map
      ((leftTranslation Q g⁻¹) x) y
    have hx : leftTranslation Q g (leftTranslation Q g⁻¹ x) = x := by
      apply lp.ext
      funext q
      simp [leftTranslation, reindexFiber_apply]
    rw [hx] at hi
    exact hi
  have hs := congrArg star (leftTranslation_projection (H := H) Q g⁻¹)
  simpa only [star_mul, ContinuousLinearMap.star_eq_adjoint, constantProjection,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, ← he] using hs

variable (S : Finset ArithmeticGroup)

theorem lazyAverage_projection (hS : S.Nonempty) (k : ℕ) :
    lazyAverage (H := H) S k * constantProjection (H := H) (Quotient k) =
      constantProjection (H := H) (Quotient k) := by
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hm : meanTranslation (H := H) S k * constantProjection (H := H) (Quotient k) =
      constantProjection (H := H) (Quotient k) := by
    simp only [meanTranslation, smul_mul_assoc, Finset.sum_mul, leftTranslation_projection,
      Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [← mul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [lazyAverage, smul_mul_assoc, add_mul, one_mul, hm]
  rw [← two_smul ℂ, smul_smul]
  norm_num

theorem projection_lazyAverage (hS : S.Nonempty) (k : ℕ) :
    constantProjection (H := H) (Quotient k) * lazyAverage S k =
      constantProjection (Quotient k) := by
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hm : constantProjection (H := H) (Quotient k) * meanTranslation S k =
      constantProjection (Quotient k) := by
    simp only [meanTranslation, mul_smul_comm, Finset.mul_sum, projection_leftTranslation,
      Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [← mul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [lazyAverage, mul_smul_comm, mul_add, mul_one, hm]
  rw [← two_smul ℂ, smul_smul]
  norm_num

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_AveragingEnergy
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Energy estimate for the actual lazy averages -/

noncomputable section

namespace CoarseAssembly

open Congruence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def translationEnergy (S : Finset ArithmeticGroup) (k : ℕ)
    (x : lp (fun _ : Quotient k => H) 2) : ℝ :=
  ∑ s ∈ S, ‖leftTranslation (Quotient k) (reduce k s) x - x‖ ^ 2

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_AveragingPropagation
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite propagation of the averaging powers

The left regular generators move at most one graph edge. The global lazy
average therefore has propagation one, and its powers have the expected
linear propagation bound on the actual separated union.
-/

noncomputable section

namespace CoarseAssembly

open Congruence DiscreteRoe

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem translation_single_zero {Q : Type*} [Fintype Q] [Group Q]
    [DecidableEq Q] (g q r : Q) (hqr : q ≠ g * r) (v : H) :
    leftTranslation Q g (lp.single 2 r v) q = 0 := by
  change lp.single (E := fun _ : Q => H) 2 r v (g⁻¹ * q) = 0
  apply lp.single_apply_ne
  intro he
  apply hqr
  calc
    q = g * (g⁻¹ * q) := by group
    _ = g * r := by rw [he]

omit [CompleteSpace H] in
theorem lazyAverage_single_zero (S : Finset ArithmeticGroup) (k : ℕ)
    (q r : Quotient k) (hqr : q ≠ r)
    (hm : ∀ s ∈ S, q ≠ reduce k s * r) (v : H) :
    lazyAverage S k (lp.single 2 r v) q = 0 := by
  classical
  simp only [lazyAverage, meanTranslation, smul_apply,
    add_apply, one_apply_eq_self,
    sum_apply, lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sum,
    Pi.smul_apply, Pi.add_apply, Finset.sum_apply]
  change (1 / 2 : ℂ) •
    ((lp.single (E := fun _ : Quotient k => H) 2 r v) q + (S.card : ℂ)⁻¹ •
      ∑ s ∈ S, leftTranslation (H := H) (Quotient k) (reduce k s)
        (lp.single 2 r v) q) = 0
  rw [lp.single_apply_ne (E := fun _ : Quotient k => H) 2 r v hqr]
  have hz : ∑ s ∈ S, leftTranslation (H := H) (Quotient k) (reduce k s)
      (lp.single 2 r v) q = 0 := Finset.sum_eq_zero (fun s hs =>
        translation_single_zero (reduce k s) q r (hm s hs) v)
  rw [hz]
  simp

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FilledEdges
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear edges in the filled polygon

The polygon's straight paths map to the actual barycentric Rips edges.
These identities supply the filling factorization of the boundary walk.
-/

noncomputable section

namespace CoarseAssembly

open Rips

def filledSegment {j : ℕ} (p q : FilledDisc j) : Path p q where
  toFun t := ⟨(1 - (t : ℝ)) • p.val + (t : ℝ) • q.val, by
    calc
      realLatticeRadius ((1 - (t : ℝ)) • p.val + (t : ℝ) • q.val) ≤
          realLatticeRadius ((1 - (t : ℝ)) • p.val) + realLatticeRadius ((t : ℝ) • q.val) :=
        realLatticeRadius_add_le _ _
      _ = (1 - (t : ℝ)) * realLatticeRadius p.val + (t : ℝ) * realLatticeRadius q.val := by
        rw [realLatticeRadius_smul _ (sub_nonneg.mpr t.2.2), realLatticeRadius_smul _ t.2.1]
      _ ≤ (1 - (t : ℝ)) * j + (t : ℝ) * j :=
        add_le_add (mul_le_mul_of_nonneg_left p.property (sub_nonneg.mpr t.2.2))
          (mul_le_mul_of_nonneg_left q.property t.2.1)
      _ = j := by ring⟩
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

@[simp] theorem filledSegment_val {j : ℕ} (p q : FilledDisc j) (t : unitInterval) :
    (filledSegment p q t).val = (1 - (t : ℝ)) • p.val + (t : ℝ) • q.val := rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FilledWalks
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Filling the actual parametrized lattice walks

Straight segments in the compact polygon follow the same concatenation as
the barycentric graph path. Thus every closed base walk, with its original
parametrization, factors through the filled polygon.
-/

noncomputable section

namespace CoarseAssembly

open Rips

def filledWalk {j : ℕ} : {u v : Disc j} → (discGraph j).Walk u v →
    Path (filledVertex u) (filledVertex v)
  | _, _, .nil => Path.refl _
  | _, _, .cons _ p => (filledSegment (filledVertex _) (filledVertex _)).trans (filledWalk p)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FamilyFilling
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire family of base loops vanishes through its actual filling

Both arrows through the disjoint union of compact polygons are constructed
proper maps. The vanishing follows only from the specified published compact
homotopy and countable-additivity inputs.
-/

noncomputable section

namespace CoarseAssembly

open Rips Analytic

variable (o : ∀ j, Disc j) (p : ∀ j, (discGraph j).Walk (o j) (o j))

def filledBoundaryLoops (j : ℕ) : C(WindingCircle, FilledDisc j) :=
  loopCircle (filledWalk (p j))

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberedPersistence
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Persistence in the actual congruence-fiber graph family

The arithmetic small-loop theorem, finite-component circle index and exact
family restriction are combined here. Boundary walks remain explicit
geometric arguments; they are not labeled as published inputs. The only
published inputs in the resulting detector are the stated circle pairing
and countable first-variable additivity.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

variable (S : Finset ArithmeticGroup)
  (boundary : ∀ j, (fiberedGraph S chosenHolonomyUnit j).Walk
    (fiberBoundaryBase j) (fiberBoundaryBase j))

def fiberedBoundaryLoops (r : ℕ) (hr : 1 ≤ r) :
    letI := componentMetric S chosenHolonomyUnit
    ∀ j, C(WindingCircle, Point (FiberVertex j) (r : ℝ)) := by
  let := componentMetric S chosenHolonomyUnit
  intro j
  exact loopCircle (walkPath (by positivity)
    (graphEdgeBound (fiberedGraph_connected S chosenHolonomyUnit j) r hr) (boundary j))

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HexagonSides
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The six oriented sides of the lattice hexagon

These explicit vertex sequences support the boundary-walk construction.
They run counterclockwise from `(j,0)`; only the final side crosses the
half-open positive ray used by the integral charge.
-/

namespace CoarseAssembly

theorem hexagonSideWalk_charge (s : Fin 6) (j k : ℕ) (hk : k ≤ j) :
    walkCharge boundaryCharge (hexagonSideWalk s j k hk) =
      if s = 5 ∧ k = j ∧ 0 < j then 1 else 0 := by
  induction k with
  | zero =>
    simp only [hexagonSideWalk, walkCharge_nil]
    split_ifs <;> omega
  | succ k ih =>
    have hklt : k < j := by omega
    rw [hexagonSideWalk, walkCharge_append, ih (by omega), walkCharge_cons,
      walkCharge_nil, add_zero]
    change (if s = 5 ∧ k = j ∧ 0 < j then (1 : ℤ) else 0) +
      latticeCharge (hexagonPoint s j k) (hexagonPoint s j (k + 1)) = _
    rw [hexagonPoint_charge s j k hklt]
    simp only [show k ≠ j by omega, and_false, false_and, ite_false, if_false, zero_add]
    split_ifs <;> omega

theorem hexagonSide_charge (s : Fin 6) (j : ℕ) :
    walkCharge boundaryCharge (hexagonSide s j) = if s = 5 ∧ 0 < j then 1 else 0 := by
  have h := walkCharge_copy boundaryCharge (hexagonSideWalk s j j le_rfl)
    (show hexagonVertex s j 0 (Nat.zero_le j) = hexagonCorner s j from rfl)
    (hexagonSide_end s j)
  exact h.trans (by simpa only [and_true, true_and] using hexagonSideWalk_charge s j j le_rfl)

theorem hexagonalWalk_charge (j : ℕ) (hj : 0 < j) :
    walkCharge boundaryCharge (hexagonalWalk j) = 1 := by
  simp only [hexagonalWalk, walkCharge_copy, walkCharge_append, hexagonSide_charge]
  simp [hj]

def hexagonalBoundaryWalks : HexagonalBoundaryWalks where
  walk := hexagonalWalk
  charge_one j hj := by
    rw [walkCharge_map]
    exact hexagonalWalk_charge j (by omega)

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RegularConstants
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariants of the actual amplified finite regular representation -/

noncomputable section

namespace CoarseAssembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Q : Type*) [Fintype Q] [Group Q]

/-- Left translations form a unitary representation, with the ample
coefficient space unchanged. -/
def leftTranslationHom : Q →* (lp (fun _ : Q => H) 2 ≃ₗᵢ[ℂ] lp (fun _ : Q => H) 2) where
  toFun := leftTranslation Q
  map_one' := by
    ext x q
    change x ((1 : Q)⁻¹ * q) = x q
    simp
  map_mul' a b := by
    ext x q
    change x ((a * b)⁻¹ * q) = x (b⁻¹ * (a⁻¹ * q))
    simp only [mul_inv_rev, mul_assoc]

end CoarseAssembly

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
def allRowBuckets : List (List (Poly Mat3)) := [rowBuckets0, rowBuckets1, rowBuckets2, rowBuckets3, rowBuckets4, rowBuckets5, rowBuckets6, rowBuckets7, rowBuckets8, rowBuckets9, rowBuckets10, rowBuckets11, rowBuckets12, rowBuckets13, rowBuckets14, rowBuckets15, rowBuckets16, rowBuckets17, rowBuckets18, rowBuckets19, rowBuckets20, rowBuckets21, rowBuckets22, rowBuckets23, rowBuckets24, rowBuckets25, rowBuckets26, rowBuckets27, rowBuckets28, rowBuckets29, rowBuckets30, rowBuckets31, rowBuckets32, rowBuckets33, rowBuckets34, rowBuckets35, rowBuckets36, rowBuckets37, rowBuckets38, rowBuckets39, rowBuckets40, rowBuckets41, rowBuckets42, rowBuckets43, rowBuckets44, rowBuckets45, rowBuckets46, rowBuckets47, rowBuckets48, rowBuckets49, rowBuckets50, rowBuckets51, rowBuckets52, rowBuckets53, rowBuckets54, rowBuckets55, rowBuckets56, rowBuckets57, rowBuckets58, rowBuckets59, rowBuckets60, rowBuckets61, rowBuckets62, rowBuckets63, rowBuckets64, rowBuckets65, rowBuckets66, rowBuckets67, rowBuckets68, rowBuckets69, rowBuckets70, rowBuckets71, rowBuckets72, rowBuckets73, rowBuckets74, rowBuckets75, rowBuckets76, rowBuckets77, rowBuckets78, rowBuckets79, rowBuckets80, rowBuckets81, rowBuckets82, rowBuckets83, rowBuckets84, rowBuckets85, rowBuckets86, rowBuckets87, rowBuckets88, rowBuckets89, rowBuckets90, rowBuckets91, rowBuckets92, rowBuckets93, rowBuckets94, rowBuckets95, rowBuckets96, rowBuckets97, rowBuckets98, rowBuckets99, rowBuckets100, rowBuckets101, rowBuckets102, rowBuckets103, rowBuckets104, rowBuckets105, rowBuckets106, rowBuckets107, rowBuckets108, rowBuckets109, rowBuckets110, rowBuckets111, rowBuckets112, rowBuckets113, rowBuckets114, rowBuckets115, rowBuckets116, rowBuckets117, rowBuckets118, rowBuckets119, rowBuckets120, rowBuckets121, rowBuckets122]
def residualBucket (b : Nat) : Poly Mat3 := normalize matLe (allRowBuckets.flatMap (fun row => row.getD b []))
end NuclearUltrapower.SOS
end

end OAI
end


