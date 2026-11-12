-- Prove2me | Definitions.Def_OAIQ229C025
-- name    : OAIQ229C025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T12:02:39.398257+00:00
-- url     : https://prove2.me/theorems/2b7bf69b-7eef-4657-841b-a6b79dd535cf
-- title:
--   Definitions bundle OAIQ229C025 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 6 definitions and 34 theorems. The definitions and types are `OAI.CoarseAssembly.boundaryLoops`, `OAI.CoarseAssembly.boundaryReindexRoeHom`, `OAI.CoarseAssembly.circleInputOfIndexOne`, `OAI.CoarseAssembly.spatialAveragingPower`, `OAI.CoarseAssembly.spatialLazyAverage`, `OAI.CoarseAssembly.windingCircleCycle`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_Averaging`, `CoarseAssembly_AveragingPropagation`, `CoarseAssembly_BlockOperators`, `CoarseAssembly_BoundaryComponents`, `CoarseAssembly_BoundaryLoopMaps`, `CoarseAssembly_BoundaryRoePerturbation`, `CoarseAssembly_CircleCoefficient`, `CoarseAssembly_ConcreteSpaces`, `CoarseAssembly_ConcreteTransfer`, `CoarseAssembly_ConcreteTransferMaps`, `CoarseAssembly_ControlledRipsCoarsening`, `CoarseAssembly_ExplicitBoundaryRepresentative`, `CoarseAssembly_ExplicitCircleFamily`, `CoarseAssembly_FiberDegree`, `CoarseAssembly_MultiplierBoundaryHomotopy`, `CoarseAssembly_ProjectionBlocks`, `CoarseAssembly_RipsBoundaryDegeneracy`, `CoarseAssembly_RipsInclusionNaturality`, `CoarseAssembly_RipsScaleCompatibility`, `CoarseAssembly_RipsUnitaryLocalization`, `CoarseAssembly_SeparatedFamilyNearby`, `CoarseAssembly_SpatialAveraging`, `CoarseAssembly_TensorFibers`, `CoarseAssembly_TransferCriterion`, `CoarseAssembly_WindingIndexEvaluation`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C016`, `OAIQ229C017`, `OAIQ229C018`, `OAIQ229C019` and `OAIQ229C020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C028`, `OAIQ229C029` and `OAIQ229C030`; the statements `OAI_NuclearUltrapower_SOS_bucket_aug_0`, `OAI_NuclearUltrapower_SOS_bucket_aug_1`, `OAI_NuclearUltrapower_SOS_bucket_aug_10`, `OAI_NuclearUltrapower_SOS_bucket_aug_100`, `OAI_NuclearUltrapower_SOS_bucket_aug_101`, `OAI_NuclearUltrapower_SOS_bucket_aug_102`, `OAI_NuclearUltrapower_SOS_bucket_aug_103`, `OAI_NuclearUltrapower_SOS_bucket_aug_104`, `OAI_NuclearUltrapower_SOS_bucket_aug_105`, `OAI_NuclearUltrapower_SOS_bucket_aug_106`, `OAI_NuclearUltrapower_SOS_bucket_aug_107`, `OAI_NuclearUltrapower_SOS_bucket_aug_108`, `OAI_NuclearUltrapower_SOS_bucket_aug_109`, `OAI_NuclearUltrapower_SOS_bucket_aug_11`, `OAI_NuclearUltrapower_SOS_bucket_aug_110`, `OAI_NuclearUltrapower_SOS_bucket_aug_111`, `OAI_NuclearUltrapower_SOS_bucket_aug_112`, `OAI_NuclearUltrapower_SOS_bucket_aug_113`, `OAI_NuclearUltrapower_SOS_bucket_aug_114`, `OAI_NuclearUltrapower_SOS_bucket_aug_115`, `OAI_NuclearUltrapower_SOS_bucket_aug_116`, `OAI_NuclearUltrapower_SOS_bucket_aug_117`, `OAI_NuclearUltrapower_SOS_bucket_aug_118`, `OAI_NuclearUltrapower_SOS_bucket_aug_119`, `OAI_NuclearUltrapower_SOS_bucket_aug_12`, `OAI_NuclearUltrapower_SOS_bucket_aug_120`, `OAI_NuclearUltrapower_SOS_bucket_aug_121`, `OAI_NuclearUltrapower_SOS_bucket_aug_122`, `OAI_NuclearUltrapower_SOS_bucket_aug_123`, `OAI_NuclearUltrapower_SOS_bucket_aug_124`, `OAI_NuclearUltrapower_SOS_bucket_aug_125`, `OAI_NuclearUltrapower_SOS_bucket_aug_126`, `OAI_NuclearUltrapower_SOS_bucket_aug_127`, `OAI_NuclearUltrapower_SOS_bucket_aug_13`, `OAI_NuclearUltrapower_SOS_bucket_aug_14`, `OAI_NuclearUltrapower_SOS_bucket_aug_15`, `OAI_NuclearUltrapower_SOS_bucket_aug_16`, `OAI_NuclearUltrapower_SOS_bucket_aug_17`, `OAI_NuclearUltrapower_SOS_bucket_aug_18`, `OAI_NuclearUltrapower_SOS_bucket_aug_19`, `OAI_NuclearUltrapower_SOS_bucket_aug_2`, `OAI_NuclearUltrapower_SOS_bucket_aug_20`, `OAI_NuclearUltrapower_SOS_bucket_aug_21`, `OAI_NuclearUltrapower_SOS_bucket_aug_22`, `OAI_NuclearUltrapower_SOS_bucket_aug_23`, `OAI_NuclearUltrapower_SOS_bucket_aug_24`, `OAI_NuclearUltrapower_SOS_bucket_aug_25`, `OAI_NuclearUltrapower_SOS_bucket_aug_26`, `OAI_NuclearUltrapower_SOS_bucket_aug_27`, `OAI_NuclearUltrapower_SOS_bucket_aug_28`, `OAI_NuclearUltrapower_SOS_bucket_aug_29`, `OAI_NuclearUltrapower_SOS_bucket_aug_3`, `OAI_NuclearUltrapower_SOS_bucket_aug_30`, `OAI_NuclearUltrapower_SOS_bucket_aug_31`, `OAI_NuclearUltrapower_SOS_bucket_aug_32`, `OAI_NuclearUltrapower_SOS_bucket_aug_33`, `OAI_NuclearUltrapower_SOS_bucket_aug_34`, `OAI_NuclearUltrapower_SOS_bucket_aug_35`, `OAI_NuclearUltrapower_SOS_bucket_aug_36`, `OAI_NuclearUltrapower_SOS_bucket_aug_37`, `OAI_NuclearUltrapower_SOS_bucket_aug_38`, `OAI_NuclearUltrapower_SOS_bucket_aug_39`, `OAI_NuclearUltrapower_SOS_bucket_aug_4`, `OAI_NuclearUltrapower_SOS_bucket_aug_40`, `OAI_NuclearUltrapower_SOS_bucket_aug_41`, `OAI_NuclearUltrapower_SOS_bucket_aug_42`, `OAI_NuclearUltrapower_SOS_bucket_aug_43`, `OAI_NuclearUltrapower_SOS_bucket_aug_44`, `OAI_NuclearUltrapower_SOS_bucket_aug_45`, `OAI_NuclearUltrapower_SOS_bucket_aug_46`, `OAI_NuclearUltrapower_SOS_bucket_aug_47`, `OAI_NuclearUltrapower_SOS_bucket_aug_48`, `OAI_NuclearUltrapower_SOS_bucket_aug_49`, `OAI_NuclearUltrapower_SOS_bucket_aug_5`, `OAI_NuclearUltrapower_SOS_bucket_aug_50`, `OAI_NuclearUltrapower_SOS_bucket_aug_51`, `OAI_NuclearUltrapower_SOS_bucket_aug_52`, `OAI_NuclearUltrapower_SOS_bucket_aug_53`, `OAI_NuclearUltrapower_SOS_bucket_aug_54`, `OAI_NuclearUltrapower_SOS_bucket_aug_55`, `OAI_NuclearUltrapower_SOS_bucket_aug_56`, `OAI_NuclearUltrapower_SOS_bucket_aug_57`, `OAI_NuclearUltrapower_SOS_bucket_aug_58`, `OAI_NuclearUltrapower_SOS_bucket_aug_59`, `OAI_NuclearUltrapower_SOS_bucket_aug_6`, `OAI_NuclearUltrapower_SOS_bucket_aug_60`, `OAI_NuclearUltrapower_SOS_bucket_aug_61`, `OAI_NuclearUltrapower_SOS_bucket_aug_62`, `OAI_NuclearUltrapower_SOS_bucket_aug_63`, `OAI_NuclearUltrapower_SOS_bucket_aug_64`, `OAI_NuclearUltrapower_SOS_bucket_aug_65`, `OAI_NuclearUltrapower_SOS_bucket_aug_66`, `OAI_NuclearUltrapower_SOS_bucket_aug_67`, `OAI_NuclearUltrapower_SOS_bucket_aug_68`, `OAI_NuclearUltrapower_SOS_bucket_aug_69`, `OAI_NuclearUltrapower_SOS_bucket_aug_7`, `OAI_NuclearUltrapower_SOS_bucket_aug_70`, `OAI_NuclearUltrapower_SOS_bucket_aug_71`, `OAI_NuclearUltrapower_SOS_bucket_aug_72`, `OAI_NuclearUltrapower_SOS_bucket_aug_73`, `OAI_NuclearUltrapower_SOS_bucket_aug_74`, `OAI_NuclearUltrapower_SOS_bucket_aug_75`, `OAI_NuclearUltrapower_SOS_bucket_aug_76`, `OAI_NuclearUltrapower_SOS_bucket_aug_77`, `OAI_NuclearUltrapower_SOS_bucket_aug_78`, `OAI_NuclearUltrapower_SOS_bucket_aug_79`, `OAI_NuclearUltrapower_SOS_bucket_aug_8`, `OAI_NuclearUltrapower_SOS_bucket_aug_80`, `OAI_NuclearUltrapower_SOS_bucket_aug_81`, `OAI_NuclearUltrapower_SOS_bucket_aug_82`, `OAI_NuclearUltrapower_SOS_bucket_aug_83`, `OAI_NuclearUltrapower_SOS_bucket_aug_84`, `OAI_NuclearUltrapower_SOS_bucket_aug_85`, `OAI_NuclearUltrapower_SOS_bucket_aug_86`, `OAI_NuclearUltrapower_SOS_bucket_aug_87`, `OAI_NuclearUltrapower_SOS_bucket_aug_88`, `OAI_NuclearUltrapower_SOS_bucket_aug_89`, `OAI_NuclearUltrapower_SOS_bucket_aug_9`, `OAI_NuclearUltrapower_SOS_bucket_aug_90`, `OAI_NuclearUltrapower_SOS_bucket_aug_91`, `OAI_NuclearUltrapower_SOS_bucket_aug_92`, `OAI_NuclearUltrapower_SOS_bucket_aug_93`, `OAI_NuclearUltrapower_SOS_bucket_aug_94`, `OAI_NuclearUltrapower_SOS_bucket_aug_95`, `OAI_NuclearUltrapower_SOS_bucket_aug_96`, `OAI_NuclearUltrapower_SOS_bucket_aug_97`, `OAI_NuclearUltrapower_SOS_bucket_aug_98`, `OAI_NuclearUltrapower_SOS_bucket_aug_99`, `OAI_NuclearUltrapower_SOS_bucket_l1_0`, `OAI_NuclearUltrapower_SOS_bucket_l1_1`, `OAI_NuclearUltrapower_SOS_bucket_l1_10`, `OAI_NuclearUltrapower_SOS_bucket_l1_100`, `OAI_NuclearUltrapower_SOS_bucket_l1_101`, `OAI_NuclearUltrapower_SOS_bucket_l1_102`, `OAI_NuclearUltrapower_SOS_bucket_l1_103`, `OAI_NuclearUltrapower_SOS_bucket_l1_104`, `OAI_NuclearUltrapower_SOS_bucket_l1_105`, `OAI_NuclearUltrapower_SOS_bucket_l1_106`, `OAI_NuclearUltrapower_SOS_bucket_l1_107`, `OAI_NuclearUltrapower_SOS_bucket_l1_108`, `OAI_NuclearUltrapower_SOS_bucket_l1_109`, `OAI_NuclearUltrapower_SOS_bucket_l1_11`, `OAI_NuclearUltrapower_SOS_bucket_l1_110`, `OAI_NuclearUltrapower_SOS_bucket_l1_111`, `OAI_NuclearUltrapower_SOS_bucket_l1_112`, `OAI_NuclearUltrapower_SOS_bucket_l1_113`, `OAI_NuclearUltrapower_SOS_bucket_l1_114`, `OAI_NuclearUltrapower_SOS_bucket_l1_115`, `OAI_NuclearUltrapower_SOS_bucket_l1_116`, `OAI_NuclearUltrapower_SOS_bucket_l1_117`, `OAI_NuclearUltrapower_SOS_bucket_l1_118`, `OAI_NuclearUltrapower_SOS_bucket_l1_119`, `OAI_NuclearUltrapower_SOS_bucket_l1_12`, `OAI_NuclearUltrapower_SOS_bucket_l1_120`, `OAI_NuclearUltrapower_SOS_bucket_l1_121`, `OAI_NuclearUltrapower_SOS_bucket_l1_122`, `OAI_NuclearUltrapower_SOS_bucket_l1_123`, `OAI_NuclearUltrapower_SOS_bucket_l1_124`, `OAI_NuclearUltrapower_SOS_bucket_l1_125`, `OAI_NuclearUltrapower_SOS_bucket_l1_126`, `OAI_NuclearUltrapower_SOS_bucket_l1_127`, `OAI_NuclearUltrapower_SOS_bucket_l1_13`, `OAI_NuclearUltrapower_SOS_bucket_l1_14`, `OAI_NuclearUltrapower_SOS_bucket_l1_15`, `OAI_NuclearUltrapower_SOS_bucket_l1_16`, `OAI_NuclearUltrapower_SOS_bucket_l1_17`, `OAI_NuclearUltrapower_SOS_bucket_l1_18`, `OAI_NuclearUltrapower_SOS_bucket_l1_19`, `OAI_NuclearUltrapower_SOS_bucket_l1_2`, `OAI_NuclearUltrapower_SOS_bucket_l1_20`, `OAI_NuclearUltrapower_SOS_bucket_l1_21`, `OAI_NuclearUltrapower_SOS_bucket_l1_22`, `OAI_NuclearUltrapower_SOS_bucket_l1_23`, `OAI_NuclearUltrapower_SOS_bucket_l1_24`, `OAI_NuclearUltrapower_SOS_bucket_l1_25`, `OAI_NuclearUltrapower_SOS_bucket_l1_26`, `OAI_NuclearUltrapower_SOS_bucket_l1_27`, `OAI_NuclearUltrapower_SOS_bucket_l1_28`, `OAI_NuclearUltrapower_SOS_bucket_l1_29`, `OAI_NuclearUltrapower_SOS_bucket_l1_3`, `OAI_NuclearUltrapower_SOS_bucket_l1_30`, `OAI_NuclearUltrapower_SOS_bucket_l1_31`, `OAI_NuclearUltrapower_SOS_bucket_l1_32`, `OAI_NuclearUltrapower_SOS_bucket_l1_33`, `OAI_NuclearUltrapower_SOS_bucket_l1_34`, `OAI_NuclearUltrapower_SOS_bucket_l1_35`, `OAI_NuclearUltrapower_SOS_bucket_l1_36`, `OAI_NuclearUltrapower_SOS_bucket_l1_37`, `OAI_NuclearUltrapower_SOS_bucket_l1_38`, `OAI_NuclearUltrapower_SOS_bucket_l1_39`, `OAI_NuclearUltrapower_SOS_bucket_l1_4`, `OAI_NuclearUltrapower_SOS_bucket_l1_40`, `OAI_NuclearUltrapower_SOS_bucket_l1_41`, `OAI_NuclearUltrapower_SOS_bucket_l1_42`, `OAI_NuclearUltrapower_SOS_bucket_l1_43`, `OAI_NuclearUltrapower_SOS_bucket_l1_44`, `OAI_NuclearUltrapower_SOS_bucket_l1_45`, `OAI_NuclearUltrapower_SOS_bucket_l1_46`, `OAI_NuclearUltrapower_SOS_bucket_l1_47`, `OAI_NuclearUltrapower_SOS_bucket_l1_48`, `OAI_NuclearUltrapower_SOS_bucket_l1_49`, `OAI_NuclearUltrapower_SOS_bucket_l1_5`, `OAI_NuclearUltrapower_SOS_bucket_l1_50`, `OAI_NuclearUltrapower_SOS_bucket_l1_51`, `OAI_NuclearUltrapower_SOS_bucket_l1_52`, `OAI_NuclearUltrapower_SOS_bucket_l1_53`, `OAI_NuclearUltrapower_SOS_bucket_l1_54`, `OAI_NuclearUltrapower_SOS_bucket_l1_55`, `OAI_NuclearUltrapower_SOS_bucket_l1_56`, `OAI_NuclearUltrapower_SOS_bucket_l1_57`, `OAI_NuclearUltrapower_SOS_bucket_l1_58`, `OAI_NuclearUltrapower_SOS_bucket_l1_59`, `OAI_NuclearUltrapower_SOS_bucket_l1_6`, `OAI_NuclearUltrapower_SOS_bucket_l1_60`, `OAI_NuclearUltrapower_SOS_bucket_l1_61`, `OAI_NuclearUltrapower_SOS_bucket_l1_62`, `OAI_NuclearUltrapower_SOS_bucket_l1_63`, `OAI_NuclearUltrapower_SOS_bucket_l1_64`, `OAI_NuclearUltrapower_SOS_bucket_l1_65`, `OAI_NuclearUltrapower_SOS_bucket_l1_66`, `OAI_NuclearUltrapower_SOS_bucket_l1_67`, `OAI_NuclearUltrapower_SOS_bucket_l1_68`, `OAI_NuclearUltrapower_SOS_bucket_l1_69`, `OAI_NuclearUltrapower_SOS_bucket_l1_7`, `OAI_NuclearUltrapower_SOS_bucket_l1_70`, `OAI_NuclearUltrapower_SOS_bucket_l1_71`, `OAI_NuclearUltrapower_SOS_bucket_l1_72`, `OAI_NuclearUltrapower_SOS_bucket_l1_73`, `OAI_NuclearUltrapower_SOS_bucket_l1_74`, `OAI_NuclearUltrapower_SOS_bucket_l1_75`, `OAI_NuclearUltrapower_SOS_bucket_l1_76`, `OAI_NuclearUltrapower_SOS_bucket_l1_77`, `OAI_NuclearUltrapower_SOS_bucket_l1_78`, `OAI_NuclearUltrapower_SOS_bucket_l1_79`, `OAI_NuclearUltrapower_SOS_bucket_l1_8`, `OAI_NuclearUltrapower_SOS_bucket_l1_80`, `OAI_NuclearUltrapower_SOS_bucket_l1_81`, `OAI_NuclearUltrapower_SOS_bucket_l1_82`, `OAI_NuclearUltrapower_SOS_bucket_l1_83`, `OAI_NuclearUltrapower_SOS_bucket_l1_84`, `OAI_NuclearUltrapower_SOS_bucket_l1_85`, `OAI_NuclearUltrapower_SOS_bucket_l1_86`, `OAI_NuclearUltrapower_SOS_bucket_l1_87`, `OAI_NuclearUltrapower_SOS_bucket_l1_88`, `OAI_NuclearUltrapower_SOS_bucket_l1_89`, `OAI_NuclearUltrapower_SOS_bucket_l1_9`, `OAI_NuclearUltrapower_SOS_bucket_l1_90`, `OAI_NuclearUltrapower_SOS_bucket_l1_91`, `OAI_NuclearUltrapower_SOS_bucket_l1_92`, `OAI_NuclearUltrapower_SOS_bucket_l1_93`, `OAI_NuclearUltrapower_SOS_bucket_l1_94`, `OAI_NuclearUltrapower_SOS_bucket_l1_95`, `OAI_NuclearUltrapower_SOS_bucket_l1_96`, `OAI_NuclearUltrapower_SOS_bucket_l1_97`, `OAI_NuclearUltrapower_SOS_bucket_l1_98`, `OAI_NuclearUltrapower_SOS_bucket_l1_99`, `OAI_NuclearUltrapower_SOS_row_lengths` and `OAI_NuclearUltrapower_SOS_row_normalizations`; the proofs of `OAI_NuclearUltrapower_SOS_bucket_aug_0`, `OAI_NuclearUltrapower_SOS_bucket_aug_1`, `OAI_NuclearUltrapower_SOS_bucket_aug_10`, `OAI_NuclearUltrapower_SOS_bucket_aug_100`, `OAI_NuclearUltrapower_SOS_bucket_aug_101`, `OAI_NuclearUltrapower_SOS_bucket_aug_102`, `OAI_NuclearUltrapower_SOS_bucket_aug_103`, `OAI_NuclearUltrapower_SOS_bucket_aug_104`, `OAI_NuclearUltrapower_SOS_bucket_aug_105`, `OAI_NuclearUltrapower_SOS_bucket_aug_106`, `OAI_NuclearUltrapower_SOS_bucket_aug_107`, `OAI_NuclearUltrapower_SOS_bucket_aug_108`, `OAI_NuclearUltrapower_SOS_bucket_aug_109`, `OAI_NuclearUltrapower_SOS_bucket_aug_11`, `OAI_NuclearUltrapower_SOS_bucket_aug_110`, `OAI_NuclearUltrapower_SOS_bucket_aug_111`, `OAI_NuclearUltrapower_SOS_bucket_aug_112`, `OAI_NuclearUltrapower_SOS_bucket_aug_113`, `OAI_NuclearUltrapower_SOS_bucket_aug_114`, `OAI_NuclearUltrapower_SOS_bucket_aug_115`, `OAI_NuclearUltrapower_SOS_bucket_aug_116`, `OAI_NuclearUltrapower_SOS_bucket_aug_117`, `OAI_NuclearUltrapower_SOS_bucket_aug_118`, `OAI_NuclearUltrapower_SOS_bucket_aug_119`, `OAI_NuclearUltrapower_SOS_bucket_aug_12`, `OAI_NuclearUltrapower_SOS_bucket_aug_120`, `OAI_NuclearUltrapower_SOS_bucket_aug_121`, `OAI_NuclearUltrapower_SOS_bucket_aug_122`, `OAI_NuclearUltrapower_SOS_bucket_aug_123`, `OAI_NuclearUltrapower_SOS_bucket_aug_124`, `OAI_NuclearUltrapower_SOS_bucket_aug_125`, `OAI_NuclearUltrapower_SOS_bucket_aug_126`, `OAI_NuclearUltrapower_SOS_bucket_aug_127`, `OAI_NuclearUltrapower_SOS_bucket_aug_13`, `OAI_NuclearUltrapower_SOS_bucket_aug_14`, `OAI_NuclearUltrapower_SOS_bucket_aug_15`, `OAI_NuclearUltrapower_SOS_bucket_aug_16`, `OAI_NuclearUltrapower_SOS_bucket_aug_17`, `OAI_NuclearUltrapower_SOS_bucket_aug_18`, `OAI_NuclearUltrapower_SOS_bucket_aug_19`, `OAI_NuclearUltrapower_SOS_bucket_aug_2`, `OAI_NuclearUltrapower_SOS_bucket_aug_20`, `OAI_NuclearUltrapower_SOS_bucket_aug_21`, `OAI_NuclearUltrapower_SOS_bucket_aug_22`, `OAI_NuclearUltrapower_SOS_bucket_aug_23`, `OAI_NuclearUltrapower_SOS_bucket_aug_24`, `OAI_NuclearUltrapower_SOS_bucket_aug_25`, `OAI_NuclearUltrapower_SOS_bucket_aug_26`, `OAI_NuclearUltrapower_SOS_bucket_aug_27`, `OAI_NuclearUltrapower_SOS_bucket_aug_28`, `OAI_NuclearUltrapower_SOS_bucket_aug_29`, `OAI_NuclearUltrapower_SOS_bucket_aug_3`, `OAI_NuclearUltrapower_SOS_bucket_aug_30`, `OAI_NuclearUltrapower_SOS_bucket_aug_31`, `OAI_NuclearUltrapower_SOS_bucket_aug_32`, `OAI_NuclearUltrapower_SOS_bucket_aug_33`, `OAI_NuclearUltrapower_SOS_bucket_aug_34`, `OAI_NuclearUltrapower_SOS_bucket_aug_35`, `OAI_NuclearUltrapower_SOS_bucket_aug_36`, `OAI_NuclearUltrapower_SOS_bucket_aug_37`, `OAI_NuclearUltrapower_SOS_bucket_aug_38`, `OAI_NuclearUltrapower_SOS_bucket_aug_39`, `OAI_NuclearUltrapower_SOS_bucket_aug_4`, `OAI_NuclearUltrapower_SOS_bucket_aug_40`, `OAI_NuclearUltrapower_SOS_bucket_aug_41`, `OAI_NuclearUltrapower_SOS_bucket_aug_42`, `OAI_NuclearUltrapower_SOS_bucket_aug_43`, `OAI_NuclearUltrapower_SOS_bucket_aug_44`, `OAI_NuclearUltrapower_SOS_bucket_aug_45`, `OAI_NuclearUltrapower_SOS_bucket_aug_46`, `OAI_NuclearUltrapower_SOS_bucket_aug_47`, `OAI_NuclearUltrapower_SOS_bucket_aug_48`, `OAI_NuclearUltrapower_SOS_bucket_aug_49`, `OAI_NuclearUltrapower_SOS_bucket_aug_5`, `OAI_NuclearUltrapower_SOS_bucket_aug_50`, `OAI_NuclearUltrapower_SOS_bucket_aug_51`, `OAI_NuclearUltrapower_SOS_bucket_aug_52`, `OAI_NuclearUltrapower_SOS_bucket_aug_53`, `OAI_NuclearUltrapower_SOS_bucket_aug_54`, `OAI_NuclearUltrapower_SOS_bucket_aug_55`, `OAI_NuclearUltrapower_SOS_bucket_aug_56`, `OAI_NuclearUltrapower_SOS_bucket_aug_57`, `OAI_NuclearUltrapower_SOS_bucket_aug_58`, `OAI_NuclearUltrapower_SOS_bucket_aug_59`, `OAI_NuclearUltrapower_SOS_bucket_aug_6`, `OAI_NuclearUltrapower_SOS_bucket_aug_60`, `OAI_NuclearUltrapower_SOS_bucket_aug_61`, `OAI_NuclearUltrapower_SOS_bucket_aug_62`, `OAI_NuclearUltrapower_SOS_bucket_aug_63`, `OAI_NuclearUltrapower_SOS_bucket_aug_64`, `OAI_NuclearUltrapower_SOS_bucket_aug_65`, `OAI_NuclearUltrapower_SOS_bucket_aug_66`, `OAI_NuclearUltrapower_SOS_bucket_aug_67`, `OAI_NuclearUltrapower_SOS_bucket_aug_68`, `OAI_NuclearUltrapower_SOS_bucket_aug_69`, `OAI_NuclearUltrapower_SOS_bucket_aug_7`, `OAI_NuclearUltrapower_SOS_bucket_aug_70`, `OAI_NuclearUltrapower_SOS_bucket_aug_71`, `OAI_NuclearUltrapower_SOS_bucket_aug_72`, `OAI_NuclearUltrapower_SOS_bucket_aug_73`, `OAI_NuclearUltrapower_SOS_bucket_aug_74`, `OAI_NuclearUltrapower_SOS_bucket_aug_75`, `OAI_NuclearUltrapower_SOS_bucket_aug_76`, `OAI_NuclearUltrapower_SOS_bucket_aug_77`, `OAI_NuclearUltrapower_SOS_bucket_aug_78`, `OAI_NuclearUltrapower_SOS_bucket_aug_79`, `OAI_NuclearUltrapower_SOS_bucket_aug_8`, `OAI_NuclearUltrapower_SOS_bucket_aug_80`, `OAI_NuclearUltrapower_SOS_bucket_aug_81`, `OAI_NuclearUltrapower_SOS_bucket_aug_82`, `OAI_NuclearUltrapower_SOS_bucket_aug_83`, `OAI_NuclearUltrapower_SOS_bucket_aug_84`, `OAI_NuclearUltrapower_SOS_bucket_aug_85`, `OAI_NuclearUltrapower_SOS_bucket_aug_86`, `OAI_NuclearUltrapower_SOS_bucket_aug_87`, `OAI_NuclearUltrapower_SOS_bucket_aug_88`, `OAI_NuclearUltrapower_SOS_bucket_aug_89`, `OAI_NuclearUltrapower_SOS_bucket_aug_9`, `OAI_NuclearUltrapower_SOS_bucket_aug_90`, `OAI_NuclearUltrapower_SOS_bucket_aug_91`, `OAI_NuclearUltrapower_SOS_bucket_aug_92`, `OAI_NuclearUltrapower_SOS_bucket_aug_93`, `OAI_NuclearUltrapower_SOS_bucket_aug_94`, `OAI_NuclearUltrapower_SOS_bucket_aug_95`, `OAI_NuclearUltrapower_SOS_bucket_aug_96`, `OAI_NuclearUltrapower_SOS_bucket_aug_97`, `OAI_NuclearUltrapower_SOS_bucket_aug_98`, `OAI_NuclearUltrapower_SOS_bucket_aug_99`, `OAI_NuclearUltrapower_SOS_bucket_l1_0`, `OAI_NuclearUltrapower_SOS_bucket_l1_1`, `OAI_NuclearUltrapower_SOS_bucket_l1_10`, `OAI_NuclearUltrapower_SOS_bucket_l1_100`, `OAI_NuclearUltrapower_SOS_bucket_l1_101`, `OAI_NuclearUltrapower_SOS_bucket_l1_102`, `OAI_NuclearUltrapower_SOS_bucket_l1_103`, `OAI_NuclearUltrapower_SOS_bucket_l1_104`, `OAI_NuclearUltrapower_SOS_bucket_l1_105`, `OAI_NuclearUltrapower_SOS_bucket_l1_106`, `OAI_NuclearUltrapower_SOS_bucket_l1_107`, `OAI_NuclearUltrapower_SOS_bucket_l1_108`, `OAI_NuclearUltrapower_SOS_bucket_l1_109`, `OAI_NuclearUltrapower_SOS_bucket_l1_11`, `OAI_NuclearUltrapower_SOS_bucket_l1_110`, `OAI_NuclearUltrapower_SOS_bucket_l1_111`, `OAI_NuclearUltrapower_SOS_bucket_l1_112`, `OAI_NuclearUltrapower_SOS_bucket_l1_113`, `OAI_NuclearUltrapower_SOS_bucket_l1_114`, `OAI_NuclearUltrapower_SOS_bucket_l1_115`, `OAI_NuclearUltrapower_SOS_bucket_l1_116`, `OAI_NuclearUltrapower_SOS_bucket_l1_117`, `OAI_NuclearUltrapower_SOS_bucket_l1_118`, `OAI_NuclearUltrapower_SOS_bucket_l1_119`, `OAI_NuclearUltrapower_SOS_bucket_l1_12`, `OAI_NuclearUltrapower_SOS_bucket_l1_120`, `OAI_NuclearUltrapower_SOS_bucket_l1_121`, `OAI_NuclearUltrapower_SOS_bucket_l1_122`, `OAI_NuclearUltrapower_SOS_bucket_l1_123`, `OAI_NuclearUltrapower_SOS_bucket_l1_124`, `OAI_NuclearUltrapower_SOS_bucket_l1_125`, `OAI_NuclearUltrapower_SOS_bucket_l1_126`, `OAI_NuclearUltrapower_SOS_bucket_l1_127`, `OAI_NuclearUltrapower_SOS_bucket_l1_13`, `OAI_NuclearUltrapower_SOS_bucket_l1_14`, `OAI_NuclearUltrapower_SOS_bucket_l1_15`, `OAI_NuclearUltrapower_SOS_bucket_l1_16`, `OAI_NuclearUltrapower_SOS_bucket_l1_17`, `OAI_NuclearUltrapower_SOS_bucket_l1_18`, `OAI_NuclearUltrapower_SOS_bucket_l1_19`, `OAI_NuclearUltrapower_SOS_bucket_l1_2`, `OAI_NuclearUltrapower_SOS_bucket_l1_20`, `OAI_NuclearUltrapower_SOS_bucket_l1_21`, `OAI_NuclearUltrapower_SOS_bucket_l1_22`, `OAI_NuclearUltrapower_SOS_bucket_l1_23`, `OAI_NuclearUltrapower_SOS_bucket_l1_24`, `OAI_NuclearUltrapower_SOS_bucket_l1_25`, `OAI_NuclearUltrapower_SOS_bucket_l1_26`, `OAI_NuclearUltrapower_SOS_bucket_l1_27`, `OAI_NuclearUltrapower_SOS_bucket_l1_28`, `OAI_NuclearUltrapower_SOS_bucket_l1_29`, `OAI_NuclearUltrapower_SOS_bucket_l1_3`, `OAI_NuclearUltrapower_SOS_bucket_l1_30`, `OAI_NuclearUltrapower_SOS_bucket_l1_31`, `OAI_NuclearUltrapower_SOS_bucket_l1_32`, `OAI_NuclearUltrapower_SOS_bucket_l1_33`, `OAI_NuclearUltrapower_SOS_bucket_l1_34`, `OAI_NuclearUltrapower_SOS_bucket_l1_35`, `OAI_NuclearUltrapower_SOS_bucket_l1_36`, `OAI_NuclearUltrapower_SOS_bucket_l1_37`, `OAI_NuclearUltrapower_SOS_bucket_l1_38`, `OAI_NuclearUltrapower_SOS_bucket_l1_39`, `OAI_NuclearUltrapower_SOS_bucket_l1_4`, `OAI_NuclearUltrapower_SOS_bucket_l1_40`, `OAI_NuclearUltrapower_SOS_bucket_l1_41`, `OAI_NuclearUltrapower_SOS_bucket_l1_42`, `OAI_NuclearUltrapower_SOS_bucket_l1_43`, `OAI_NuclearUltrapower_SOS_bucket_l1_44`, `OAI_NuclearUltrapower_SOS_bucket_l1_45`, `OAI_NuclearUltrapower_SOS_bucket_l1_46`, `OAI_NuclearUltrapower_SOS_bucket_l1_47`, `OAI_NuclearUltrapower_SOS_bucket_l1_48`, `OAI_NuclearUltrapower_SOS_bucket_l1_49`, `OAI_NuclearUltrapower_SOS_bucket_l1_5`, `OAI_NuclearUltrapower_SOS_bucket_l1_50`, `OAI_NuclearUltrapower_SOS_bucket_l1_51`, `OAI_NuclearUltrapower_SOS_bucket_l1_52`, `OAI_NuclearUltrapower_SOS_bucket_l1_53`, `OAI_NuclearUltrapower_SOS_bucket_l1_54`, `OAI_NuclearUltrapower_SOS_bucket_l1_55`, `OAI_NuclearUltrapower_SOS_bucket_l1_56`, `OAI_NuclearUltrapower_SOS_bucket_l1_57`, `OAI_NuclearUltrapower_SOS_bucket_l1_58`, `OAI_NuclearUltrapower_SOS_bucket_l1_59`, `OAI_NuclearUltrapower_SOS_bucket_l1_6`, `OAI_NuclearUltrapower_SOS_bucket_l1_60`, `OAI_NuclearUltrapower_SOS_bucket_l1_61`, `OAI_NuclearUltrapower_SOS_bucket_l1_62`, `OAI_NuclearUltrapower_SOS_bucket_l1_63`, `OAI_NuclearUltrapower_SOS_bucket_l1_64`, `OAI_NuclearUltrapower_SOS_bucket_l1_65`, `OAI_NuclearUltrapower_SOS_bucket_l1_66`, `OAI_NuclearUltrapower_SOS_bucket_l1_67`, `OAI_NuclearUltrapower_SOS_bucket_l1_68`, `OAI_NuclearUltrapower_SOS_bucket_l1_69`, `OAI_NuclearUltrapower_SOS_bucket_l1_7`, `OAI_NuclearUltrapower_SOS_bucket_l1_70`, `OAI_NuclearUltrapower_SOS_bucket_l1_71`, `OAI_NuclearUltrapower_SOS_bucket_l1_72`, `OAI_NuclearUltrapower_SOS_bucket_l1_73`, `OAI_NuclearUltrapower_SOS_bucket_l1_74`, `OAI_NuclearUltrapower_SOS_bucket_l1_75`, `OAI_NuclearUltrapower_SOS_bucket_l1_76`, `OAI_NuclearUltrapower_SOS_bucket_l1_77`, `OAI_NuclearUltrapower_SOS_bucket_l1_78`, `OAI_NuclearUltrapower_SOS_bucket_l1_79`, `OAI_NuclearUltrapower_SOS_bucket_l1_8`, `OAI_NuclearUltrapower_SOS_bucket_l1_80`, `OAI_NuclearUltrapower_SOS_bucket_l1_81`, `OAI_NuclearUltrapower_SOS_bucket_l1_82`, `OAI_NuclearUltrapower_SOS_bucket_l1_83`, `OAI_NuclearUltrapower_SOS_bucket_l1_84`, `OAI_NuclearUltrapower_SOS_bucket_l1_85`, `OAI_NuclearUltrapower_SOS_bucket_l1_86`, `OAI_NuclearUltrapower_SOS_bucket_l1_87`, `OAI_NuclearUltrapower_SOS_bucket_l1_88`, `OAI_NuclearUltrapower_SOS_bucket_l1_89`, `OAI_NuclearUltrapower_SOS_bucket_l1_9`, `OAI_NuclearUltrapower_SOS_bucket_l1_90`, `OAI_NuclearUltrapower_SOS_bucket_l1_91`, `OAI_NuclearUltrapower_SOS_bucket_l1_92`, `OAI_NuclearUltrapower_SOS_bucket_l1_93`, `OAI_NuclearUltrapower_SOS_bucket_l1_94`, `OAI_NuclearUltrapower_SOS_bucket_l1_95`, `OAI_NuclearUltrapower_SOS_bucket_l1_96`, `OAI_NuclearUltrapower_SOS_bucket_l1_97`, `OAI_NuclearUltrapower_SOS_bucket_l1_98` and `OAI_NuclearUltrapower_SOS_bucket_l1_99`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Basic
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
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TwoSidedIdeal.Basic
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
import Mathlib.Topology.Bases
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
import Definitions.Def_OAIQ229C016
import Definitions.Def_OAIQ229C017
import Definitions.Def_OAIQ229C018
import Definitions.Def_OAIQ229C019
import Definitions.Def_OAIQ229C020

section
-- module Solutions.Q229_CA.CoarseAssembly_BlockOperators
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform block operators on Hilbert sums

The averaging operators used in the transfer act separately on finite
fibers. A uniform norm bound, rather than finiteness of the set of fibers,
makes their direct sum a bounded operator. The resulting operator admits the uniform approximation needed for the
fiber projection.
-/

noncomputable section

namespace CoarseAssembly

open Filter
open scoped Topology

variable {ι : Type*} {E F : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]

/-- Removing a fixed projection converts averaging powers into powers on
its complementary subspace. This identity needs no spectral theorem. -/
theorem projection_error_power {R : Type*} [Ring R] (M P : R)
    (hPP : P * P = P) (hMP : M * P = P) (hPM : P * M = P) (n : ℕ) :
    (M - P) ^ (n + 1) = M ^ (n + 1) - P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (M - P), ih, mul_sub, sub_mul, sub_mul,
      power_mul_fixed M P hMP, hPM, hPP, sub_self, sub_zero, ← pow_succ]

/-- The uniform spectral-gap consequence needed by the transfer. The
published input is the strict contraction bound on `M i - P i`; norm
convergence of the direct sum is proved here. -/
theorem averaging_blocks_tendsto (M P : ∀ i, E i →L[ℂ] E i)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hM : ∀ i, ‖M i‖ ≤ 1) (hP : ∀ i, ‖P i‖ ≤ 1)
    (hPP : ∀ i, P i * P i = P i) (hMP : ∀ i, M i * P i = P i)
    (hPM : ∀ i, P i * M i = P i) (hgap : ∀ i, ‖M i - P i‖ ≤ c) :
    Tendsto
      (fun n : ℕ => blockOperator (fun i => M i ^ (n + 1)) 1 (by norm_num)
        (averaging_power_norm_le M hM n))
      atTop (nhds (blockOperator P 1 (by norm_num) hP)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (show Tendsto (fun n : ℕ => c ^ (n + 1)) atTop (nhds 0) by
      simpa only [pow_succ, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1).mul_const c)
  apply blockOperator_dist_le _ _ _ _ _ _ _ (pow_nonneg hc _) _ hP
  intro i
  rw [← projection_error_power _ _ (hPP i) (hMP i) (hPM i)]
  exact (norm_pow_le' _ (Nat.succ_pos n)).trans (by gcongr; exact hgap i)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Averaging
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

theorem constantProjection_norm_le : ‖constantProjection (H := H) Q‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [LinearIsometryEquiv.norm_map]
  have h := (fiberConstantIsometry (H := H) Q).norm_toContinuousLinearMap_le
  nlinarith [norm_nonneg (fiberConstantIsometry (H := H) Q).toContinuousLinearMap]

variable [Group Q]

variable (S : Finset ArithmeticGroup)

theorem meanTranslation_norm_le (k : ℕ) : ‖meanTranslation (H := H) S k‖ ≤ 1 := by
  have hsum : ‖∑ s ∈ S,
      (leftTranslation (H := H) (Quotient k) (reduce k s)).toLinearIsometry.toContinuousLinearMap‖ ≤
      (S.card : ℝ) := by
    apply (norm_sum_le S (fun s =>
      (leftTranslation (H := H) (Quotient k) (reduce k s)).toLinearIsometry.toContinuousLinearMap)).trans
    calc
      _ ≤ ∑ _s ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun s _ =>
        (leftTranslation (H := H) (Quotient k) (reduce k s)).toLinearIsometry.norm_toContinuousLinearMap_le)
      _ = _ := by simp
  by_cases hS : S.card = 0
  · change ‖(((S.card : ℂ)⁻¹) • _)‖ ≤ (1 : ℝ)
    simp only [hS, Nat.cast_zero, inv_zero, zero_smul, norm_zero]
    exact (zero_le_one : (0 : ℝ) ≤ 1)
  · have hpos : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hS
    change ‖((S.card : ℂ)⁻¹) • (∑ s ∈ S,
      (leftTranslation (H := H) (Quotient k) (reduce k s)).toLinearIsometry.toContinuousLinearMap)‖ ≤ 1
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpos.le)).trans_eq
      (inv_mul_cancel₀ (ne_of_gt hpos))

theorem lazyAverage_norm_le (k : ℕ) : ‖lazyAverage (H := H) S k‖ ≤ 1 := by
  have h := norm_add_le (1 : lp (fun _ : Quotient k => H) 2 →L[ℂ] _) (meanTranslation (H := H) S k)
  have hi : ‖(1 : lp (fun _ : Quotient k => H) 2 →L[ℂ] _)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hm := meanTranslation_norm_le (H := H) S k
  change ‖(1 / 2 : ℂ) • (1 + meanTranslation (H := H) S k)‖ ≤ 1
  rw [norm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  linarith

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberDegree
attribute [-instance] _root_.OAI.CoarseAssembly.discGraphMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform degree bound for the finite fibered graphs

A neighbor is encoded by its base vertex, one integral left move, and nine
binary digits. The digits distinguish children in a successive congruence
fiber; at equal or smaller depth the reduced equation already determines
the target. The resulting bound is independent of the disc radius.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem target_eq_of_same_code {t : ℤ_[2]ˣ}
    {j : ℕ} (x : FiberVertex j) (v : Disc j) (q r : Quotient (discDepth j v))
    (s : ArithmeticGroup)
    (hp : x.1 = v ∨ (discGraph j).Adj x.1 v ∧ s = 1)
    (hq : ∀ m (hx : m ≤ discDepth j x.1) (hv : m ≤ discDepth j v),
      quotientMap hv q = reduce m s * quotientMap hx x.2 *
        holonomy t m ^ latticeCharge x.1.val v.val)
    (hr : ∀ m (hx : m ≤ discDepth j x.1) (hv : m ≤ discDepth j v),
      quotientMap hv r = reduce m s * quotientMap hx x.2 *
        holonomy t m ^ latticeCharge x.1.val v.val)
    (hbits : fiberBits (discDepth j v) q = fiberBits (discDepth j v) r) : q = r := by
  by_cases hvx : discDepth j v ≤ discDepth j x.1
  · have he := (hq _ hvx le_rfl).trans (hr _ hvx le_rfl).symm
    simpa only [quotientMap_self] using he
  · have hdepth : discDepth j v = discDepth j x.1 + 1 := by
      rcases hp with hp | ⟨hp, hs⟩
      · subst v; omega
      · have := discDepth_adj hp
        rw [abs_le] at this
        omega
    have he := (hq _ le_rfl (by omega)).trans (hr _ le_rfl (by omega)).symm
    exact fiberBits_injective hdepth q r he hbits

theorem neighborCode_injective {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    (x : FiberVertex j) : Function.Injective (neighborCode (S := S) (t := t) x) := by
  intro y z he
  have hb : y.val.1 = z.val.1 := congrArg (fun c => c.1.val) he
  have hs : neighborMove x y = neighborMove x z := congrArg (fun c => c.2.1.val) he
  have hc : fiberBits _ y.val.2 = fiberBits _ z.val.2 := congrArg (fun c => c.2.2) he
  apply Subtype.ext
  rcases y with ⟨⟨v, q⟩, hy⟩
  rcases z with ⟨⟨w, r⟩, hz⟩
  dsimp only at hb
  subst w
  apply congrArg (Sigma.mk v)
  apply target_eq_of_same_code x v q r (neighborMove x ⟨⟨v, q⟩, hy⟩)
    (neighborMove_spec x ⟨⟨v, q⟩, hy⟩).2.1
  · exact (neighborMove_spec x ⟨⟨v, q⟩, hy⟩).2.2
  · simpa only [hs, fiberCoordinate, fiberCharge] using (neighborMove_spec x ⟨⟨v, r⟩, hz⟩).2.2
  · exact hc

/-- A bound uniform in the component and in the chosen vertex. -/
theorem card_fibered_neighbors_le (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (x : FiberVertex j) :
    Nat.card {y // (fiberedGraph S t j).Adj x y} ≤
      7 * (symmetricMoves S).card * 2 ^ 9 := by
  classical
  rw [Nat.card_eq_fintype_card]
  have h := Fintype.card_le_of_injective _ (neighborCode_injective (S := S) (t := t) x)
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun,
    Fintype.card_fin, FiberBits] at h
  calc
    _ ≤ (baseNeighbors x.1).card * ((symmetricMoves S).card * (2 ^ 3) ^ 3) := h
    _ ≤ 7 * ((symmetricMoves S).card * (2 ^ 3) ^ 3) :=
      Nat.mul_le_mul_right _ (card_baseNeighbors_le x.1)
    _ = _ := by ring

theorem card_fiberedNeighbors_le (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (x : FiberVertex j) :
    (fiberedNeighbors S t x).card ≤ 7 * (symmetricMoves S).card * 2 ^ 9 := by
  classical
  have h := card_fibered_neighbors_le S t x
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
    fiberedNeighbors] using h

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TensorFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Amplifying finite-fiber operators

The algebraic Hilbert tensor product of a finite scalar fiber with the
coefficient Hilbert space is isometrically the fiber's vector-valued ℓ²
space. This gives the norm-controlled amplification used in each transfer
block, using Mathlib's Hilbert tensor-product operator norm theorem.
-/

noncomputable section

namespace CoarseAssembly

open scoped TensorProduct

variable {Q R H : Type*} [Fintype Q] [Fintype R]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [DecidableEq Q]

variable [DecidableEq R]

theorem amplifyFiber_constant (O : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (T : H →L[ℂ] H)
    (hO : O (fiberConstant Q (1 : ℂ)) = fiberConstant R (1 : ℂ)) (h : H) :
    amplifyFiber O T (fiberConstant Q h) = fiberConstant R (T h) := by
  rw [← fiberTensor_constant, amplifyFiber_tensor, hO, fiberTensor_constant]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TransferCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-fiber Roe transfer criterion

This proves the operator statement of Proposition 5.1. The required
finite-propagation scalar contractions between fibers are amplified here;
the bounded lift, compactness and compression are constructed, not assumed.
The concrete graph family still has to supply these fiber contractions and
the averaging approximants.
-/

noncomputable section

namespace CoarseAssembly

open DiscreteRoe
open scoped Topology

variable {D : Type*} [DecidableEq D] [PseudoMetricSpace D]

variable {Q : D → Type*} [∀ u, Fintype (Q u)] [∀ u, Nonempty (Q u)]
variable [∀ u, DecidableEq (Q u)] [PseudoMetricSpace (Sigma Q)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem lift_generator_from_fiber_maps (hD : UniformFiniteBalls D)
    (hO : ControlledFiberMaps Q) (T : Operator D H) (hT : Generator T) :
    ∃ A : Operator (Sigma Q) H, Generator A ∧
      fiberProjection Q * A * fiberProjection Q = operatorConjugation (fiberEmbedding Q) T := by
  obtain ⟨R, hR, hpropT⟩ := hT.1
  obtain ⟨N, hballs⟩ := hD R hR
  let rows : D → Finset D := fun u => (hballs u).choose
  have hmem (u v : D) : v ∈ rows u ↔ dist u v ≤ R := (hballs u).choose_spec.1 v
  have hcard (u : D) : (rows u).card ≤ N := (hballs u).choose_spec.2
  have hdual (u v : D) : v ∈ rows u ↔ u ∈ rows v := by
    rw [hmem, hmem, dist_comm]
  obtain ⟨s, hs, O, hO⟩ := hO R hR
  let B := fun u v => amplifyFiber (O u v) (entry T u v)
  have hB (u v : D) (huv : v ∈ rows u) : ‖B u v‖ ≤ ‖T‖ := by
    calc
      _ ≤ ‖O u v‖ * ‖entry T u v‖ := amplifyFiber_norm_le _ _
      _ ≤ 1 * ‖T‖ := mul_le_mul (hO u v ((hmem u v).mp huv)).1
        (entry_norm_le T u v) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  let A := spatialBlocks rows rows hdual B N ‖T‖ (norm_nonneg T) hcard hcard hB
  refine ⟨A, ?_, ?_⟩
  · apply spatialBlocks_generator rows rows hdual B N ‖T‖ (norm_nonneg T) hcard hcard hB T hT s hs
    · intro u v huv q r hdist
      apply ContinuousLinearMap.ext
      intro h
      change amplifyFiber (O u v) (entry T u v) (lp.single 2 r h) q = 0
      rw [amplifyFiber_single, (hO u v ((hmem u v).mp huv)).2.2 q r hdist, zero_smul]
    · intro u v huv q r
      refine ⟨O u v (lp.single 2 r 1) q, ?_⟩
      apply ContinuousLinearMap.ext
      intro h
      exact amplifyFiber_single (O u v) (entry T u v) r q h
  · apply spatialBlocks_compression rows rows hdual B N ‖T‖ (norm_nonneg T) hcard hcard hB T
    · intro u v huv
      exact hpropT u v (lt_of_not_ge (fun h => huv ((hmem u v).mpr h)))
    · intro u v huv h
      exact amplifyFiber_constant (O u v) (entry T u v)
        (hO u v ((hmem u v).mp huv)).2.1 h

/-- The finite-fiber transfer lands in the ordinary locally compact reduced
Roe algebra. The approximation is an operator-norm approximation of the
amplified projection; the projection itself need not be locally compact. -/
theorem finite_fiber_transfer (hD : UniformFiniteBalls D)
    (hX : ∀ x : Sigma Q, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    (hO : ControlledFiberMaps Q)
    (Pn : ℕ → Operator (Sigma Q) H)
    (hlim : Filter.Tendsto Pn Filter.atTop (nhds (fiberProjection Q)))
    (hprop : ∀ n, ∃ r : ℝ, 0 ≤ r ∧ PropagationLE r (Pn n)) :
    MapsToRoe (fiberEmbedding (H := H) Q) := by
  intro T hT
  apply conjugation_mem_of_sandwich_lifts hX (fiberEmbedding Q) (fiberProjection Q) Pn hlim hprop
    (fun T hT => lift_generator_from_fiber_maps hD hO T hT) hT

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual base and fibered coarse unions

Both metrics restrict to shortest-path metrics on the components. The
fibered union is indexed by base vertices so its Hilbert module has exactly
the form used by the finite-fiber transfer theorem.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem componentUnion_uniform_balls (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    @UniformFiniteBalls ((j : ℕ) × FiberVertex j)
      (componentUnionMetric S t).toPseudoMetricSpace := by
  classical
  let := componentMetric S t
  apply separated_uniform_finite_balls fiberBoundaryBase
  intro R hR
  refine ⟨(7 * (symmetricMoves S).card * 2 ^ 9 + 1) ^ ⌈R⌉₊, ?_⟩
  intro j x
  change ∃ b : Finset (FiberVertex j),
    (∀ y, y ∈ b ↔ @dist _ (componentMetric S t j).toDist x y ≤ R) ∧ _
  rw [componentMetric_eq]
  exact graphMetric_ball_bound (fiberedGraph S t j) (fiberedGraph_connected S t j)
    (fiberedNeighbors S t) _
    (fun x y h => (mem_fiberedNeighbors S t x y).mpr h)
    (card_fiberedNeighbors_le S t) R x

theorem vertexUnion_uniform_balls (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    @UniformFiniteBalls VertexUnion (vertexUnionMetric S t).toPseudoMetricSpace := by
  let := componentUnionMetric S t
  let := vertexUnionMetric S t
  apply uniform_balls_of_equiv (Equiv.sigmaAssoc (fun j u => Quotient (discDepth j u)))
    (fun _ _ => rfl)
  exact componentUnion_uniform_balls S t

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteTransferMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The controlled fiber maps on the separated coarse union

Within a component these are compositions of graph-edge maps. On the
finitely many relevant cross-component pairs they are rank-one constant
maps. This discharges the second geometric hypothesis of the transfer
criterion on the actual coarse spaces.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

variable (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)

theorem vertexUnion_dist_same {j : ℕ} (u v : Disc j)
    (q : Quotient (discDepth j u)) (r : Quotient (discDepth j v)) :
    @dist VertexUnion (vertexUnionMetric S t).toDist
      ⟨⟨j, u⟩, q⟩ ⟨⟨j, v⟩, r⟩ =
      ((fiberedGraph S t j).dist ⟨u, q⟩ ⟨v, r⟩ : ℝ) := by
  let := componentMetric S t
  have hdist := separatedDist_same fiberBoundaryBase j ⟨u, q⟩ ⟨v, r⟩
  change _ = @dist _ (componentMetric S t j).toDist ⟨u, q⟩ ⟨v, r⟩ at hdist
  rw [componentMetric_eq S t j] at hdist
  exact hdist

theorem concrete_controlled_fiber_maps :
    letI : MetricSpace VertexUnion := vertexUnionMetric S t
    ControlledFiberMaps BaseFiber := by
  classical
  let : MetricSpace VertexUnion := vertexUnionMetric S t
  intro R hR
  let e := Equiv.sigmaAssoc (fun j u => Quotient (discDepth j u))
  let initial := componentPrefix (V := FiberVertex) ⌈R⌉₊
  let W : Set VertexUnion := e.symm '' (initial : Set ((j : ℕ) × FiberVertex j))
  have hW : W.Finite := initial.finite_toSet.image e.symm
  obtain ⟨B, hB⟩ := Metric.isBounded_iff.mp hW.isBounded
  let s : ℝ := max (⌈R⌉₊ : ℝ) B
  have hs : 0 ≤ s := (Nat.cast_nonneg _).trans (le_max_left _ _)
  have hex : ∀ u v : BaseUnion, ∃ O :
      lp (fun _ : BaseFiber v => ℂ) 2 →L[ℂ] lp (fun _ : BaseFiber u => ℂ) 2,
      dist u v ≤ R → ‖O‖ ≤ 1 ∧
        O (fiberConstant (BaseFiber v) (1 : ℂ)) = fiberConstant (BaseFiber u) 1 ∧
        ∀ q r, s < dist (⟨u, q⟩ : VertexUnion) ⟨v, r⟩ → O (lp.single 2 r 1) q = 0 := by
    rintro ⟨i, u⟩ ⟨j, v⟩
    by_cases hij : i = j
    · subst j
      obtain ⟨p, hp⟩ := (discGraph_connected i).exists_walk_length_eq_dist v u
      obtain ⟨O, hO, hOc, hOs⟩ := exists_base_walk_operator S t p
      refine ⟨O, fun huv => ⟨hO, hOc, ?_⟩⟩
      intro q r hdist
      by_contra hn
      obtain ⟨w, hw⟩ := hOs r q hn
      have hbase : ((discGraph i).dist v u : ℝ) ≤ R := by
        change separatedDist discBoundaryBase ⟨i, u⟩ ⟨i, v⟩ ≤ R at huv
        rw [separatedDist_same, discGraphMetric_eq] at huv
        change ((discGraph i).dist u v : ℝ) ≤ R at huv
        rwa [SimpleGraph.dist_comm]
      have hlen : (p.length : ℝ) ≤ (⌈R⌉₊ : ℝ) := by
        rw [hp]
        exact hbase.trans (Nat.le_ceil R)
      have hup : dist (⟨⟨i, u⟩, q⟩ : VertexUnion) ⟨⟨i, v⟩, r⟩ ≤ s := by
        rw [dist_comm, vertexUnion_dist_same S t]
        exact (show ((fiberedGraph S t i).dist ⟨v, r⟩ ⟨u, q⟩ : ℝ) ≤ p.length by
          exact_mod_cast (SimpleGraph.dist_le w).trans_eq hw).trans (hlen.trans (le_max_left _ _))
      exact (not_lt_of_ge hup) hdist
    · refine ⟨constantMap ⟨i, u⟩ ⟨j, v⟩, fun huv =>
        ⟨constantMap_norm _ _, constantMap_constant _ _, ?_⟩⟩
      intro q r hdist
      have hidx := separatedDist_indices discBoundaryBase ⟨i, u⟩ ⟨j, v⟩ hij huv
      have hi : i ≤ ⌈R⌉₊ := by exact_mod_cast hidx.1.trans (Nat.le_ceil R)
      have hj : j ≤ ⌈R⌉₊ := by exact_mod_cast hidx.2.trans (Nat.le_ceil R)
      have hq : (⟨⟨i, u⟩, q⟩ : VertexUnion) ∈ W := by
        exact ⟨⟨i, ⟨u, q⟩⟩, (mem_componentPrefix _ _).mpr hi, rfl⟩
      have hr : (⟨⟨j, v⟩, r⟩ : VertexUnion) ∈ W := by
        exact ⟨⟨j, ⟨v, r⟩⟩, (mem_componentPrefix _ _).mpr hj, rfl⟩
      exact False.elim ((not_lt_of_ge ((hB hq hr).trans (le_max_right _ _))) hdist)
  choose O hO using hex
  exact ⟨s, hs, O, hO⟩

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The transfer on the actual coarse spaces

All metric and inter-fiber hypotheses have been discharged. Only the
averaging projection approximation remains in this intermediate theorem;
it is an own-paper obligation, not an assumed published theorem.
-/

noncomputable section

namespace CoarseAssembly

open DiscreteRoe
open scoped Topology

theorem concrete_transfer_of_approximation
    (S : Finset Congruence.ArithmeticGroup) (t : ℤ_[2]ˣ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Pn : ℕ → Operator VertexUnion H)
    (hlim : Filter.Tendsto Pn Filter.atTop (nhds (fiberProjection BaseFiber))) :
    letI : MetricSpace VertexUnion := vertexUnionMetric S t
    (∀ n, ∃ r : ℝ, 0 ≤ r ∧ PropagationLE r (Pn n)) →
      MapsToRoe (fiberEmbedding (H := H) BaseFiber) := by
  classical
  let : MetricSpace VertexUnion := vertexUnionMetric S t
  intro hprop
  have hX : ∀ x : VertexUnion, ∀ r : ℝ, (Metric.closedBall x r).Finite :=
    (vertexUnion_uniform_balls S t).finite_closedBall
  exact finite_fiber_transfer (D := BaseUnion) (Q := BaseFiber) (H := H)
    baseUnion_uniform_balls hX (concrete_controlled_fiber_maps S t) Pn hlim hprop

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ProjectionBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial block projections

Adjoints commute with uniformly bounded Hilbert direct sums. Under the
explicit flattening equivalence, the sum of constant-fiber projections is
exactly the spatial projection `V V*` used by the Roe transfer.
-/

noncomputable section

namespace CoarseAssembly

open scoped Topology

variable {I : Type*} {E F : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
variable [∀ i, CompleteSpace (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
variable [∀ i, CompleteSpace (F i)]

variable {Q : I → Type*} [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem block_constantProjection :
    blockOperator (fun i => constantProjection (H := H) (Q i)) 1 zero_le_one
      (fun i => constantProjection_norm_le (Q i)) =
    operatorConjugation (blockIsometry (fun i => fiberConstantIsometry (H := H) (Q i))) 1 := by
  rw [operatorConjugation, blockIsometry_toCLM, blockOperator_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SpatialAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform spatial approximation from the published gap

The gap hypothesis is the norm estimate for the explicitly defined lazy
regular-representation averages. The direct-sum convergence and its
identification with the actual spatial constant-fiber projection are proved
here, as required by the transfer construction.
-/

noncomputable section

namespace CoarseAssembly

open Congruence DiscreteRoe
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fiberAveragingPower_norm (S : Finset ArithmeticGroup) (n : ℕ) (u : BaseUnion) :
    ‖lazyAverage (H := H) S (discDepth u.1 u.2) ^ (n + 1)‖ ≤ 1 := by
  calc
    _ ≤ ‖lazyAverage (H := H) S (discDepth u.1 u.2)‖ ^ (n + 1) :=
      norm_pow_le' _ (Nat.succ_pos n)
    _ ≤ 1 ^ (n + 1) := by gcongr; exact lazyAverage_norm_le S _
    _ = 1 := one_pow _

def spatialAveragingPower (S : Finset ArithmeticGroup) (n : ℕ) : Operator VertexUnion H :=
  flattenOperator (Q := BaseFiber) (blockOperator
    (fun u : BaseUnion => lazyAverage (H := H) S (discDepth u.1 u.2) ^ (n + 1))
    1 zero_le_one (fiberAveragingPower_norm (H := H) S n))

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_AveragingPropagation
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

def spatialLazyAverage (S : Finset ArithmeticGroup) : Operator VertexUnion H :=
  flattenOperator (Q := BaseFiber) (blockOperator
    (fun u : BaseUnion => lazyAverage (H := H) S (discDepth u.1 u.2))
    1 zero_le_one (fun _ => lazyAverage_norm_le S _))

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact boundary components in the actual boundary metric

The disjoint family of finite boundary vertex sets is isometric to the
depth-zero subtype used for the spatial boundary maps.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips

theorem boundaryEdgeBound (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) {j : ℕ}
    (x y : BoundaryComponent j) (h : (boundaryGraph j).Adj x y) :
    @dist (BoundaryComponent j) (boundaryComponentMetric S t j).toDist x y ≤ 1 := by
  change @dist _ (componentMetric S t j).toDist
    (boundaryFiberEmbedding j x) (boundaryFiberEmbedding j y) ≤ 1
  rw [componentMetric_eq]
  change ((fiberedGraph S t j).dist (boundaryFiberEmbedding j x) (boundaryFiberEmbedding j y) : ℝ) ≤ 1
  exact_mod_cast (show (fiberedGraph S t j).dist (boundaryFiberEmbedding j x)
      (boundaryFiberEmbedding j y) ≤ 1 by
    simpa using (fiberedGraph S t j).dist_le (boundaryFiber_adj S t h).toWalk)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryLoopMaps
attribute [-simp] _root_.OAI.CoarseAssembly.Rips.sqrtCoordinate_selfAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same boundary family maps to the filled base and detected total space

The source class is defined on the actual boundary Rips complex. Its base
image is identified with the previously constructed filled loop family.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric7

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric8

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric1
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric2
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric3
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric5
def boundaryLoops (j : ℕ) : C(WindingCircle, Point (BoundaryComponent j) 1) :=
  loopCircle (walkPath (by norm_num) (boundaryEdgeBound elementaryMoves chosenHolonomyUnit)
    (hexagonalWalk j))

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric6
theorem boundaryComponentToBase_nonexpanding (j : ℕ) (x y : BoundaryComponent j) :
    dist (boundaryComponentToBase j x) (boundaryComponentToBase j y) ≤ dist x y :=
  fiberProjection_nonexpanding elementaryMoves chosenHolonomyUnit j
    (boundaryFiberEmbedding j x) (boundaryFiberEmbedding j y)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_MultiplierBoundaryHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norm homotopy invariance of the Roe multiplier boundary class -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance multiplierHomotopyScalarTower_r7c6448_1 : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance multiplierHomotopyScalarComm_r7c6448_1 : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp
theorem multiplierBoundaryClass_homotopy
    (F : Interval → multiplierAlgebra (X := X) (H := H))
    (hF : ∀ t, IsSelfAdjoint (F t))
    (hdefect : ∀ t, (F t).val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hcont : Continuous F) :
    multiplierBoundaryClass (F start) (hF start) (hdefect start) =
      multiplierBoundaryClass (F finish) (hF finish) (hdefect finish) := by
  have hU : Continuous (fun t => (multiplierBoundaryUnitary (F t) (hF t) : Operator X H)) := by
    convert! (show Continuous
      (fun T : multiplierAlgebra (X := X) (H := H) => T.val) from
        continuous_subtype_val).comp (continuous_rationalBoundaryUnitary F hF hcont)
  exact OperatorKTheory.relativeClass_homotopy (hS := algebra_isClosed)
    (algebra (X := X) (H := H)) (fun t => multiplierBoundaryUnitary (F t) (hF t))
    (fun t => multiplierBoundaryUnitary_sub_one_mem (F t) (hF t) (hdefect t)) hU

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryRoePerturbation
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.homotopySlice_finish _root_.OAI.CoarseAssembly.Analytic.homotopySlice_start _root_.OAI.CoarseAssembly.Analytic.intervalGrid_finish _root_.OAI.CoarseAssembly.Analytic.intervalGrid_start _root_.OAI.CoarseAssembly.Analytic.involutionUnitaryPath_finish _root_.OAI.CoarseAssembly.Analytic.involutionUnitaryPath_start _root_.OAI.CoarseAssembly.Analytic.lastEndpointFirst_succ _root_.OAI.CoarseAssembly.Analytic.lastEndpointFirst_zero _root_.OAI.CoarseAssembly.Analytic.partialIsometryDilationPath_finish _root_.OAI.CoarseAssembly.Analytic.partialIsometryDilationPath_start _root_.OAI.CoarseAssembly.Analytic.projectionSignPath_finish _root_.OAI.CoarseAssembly.Analytic.projectionSignPath_start _root_.OAI.CoarseAssembly.Analytic.semicircleUnitary_finish _root_.OAI.CoarseAssembly.Analytic.semicircleUnitary_start _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_adjoint_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coordinate_partitionMap _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalFamily_apply _root_.OAI.CoarseAssembly.DiscreteRoe.entry_diagonalFamily_same _root_.OAI.CoarseAssembly.DiscreteRoe.familyCoefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.partitionIsometry_toContinuousLinearMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply _root_.OAI.CoarseAssembly.TopologicalK1.nearbyUnitPath_finish _root_.OAI.CoarseAssembly.TopologicalK1.nearbyUnitPath_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Roe perturbations do not change the analytic boundary class -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance roePerturbationScalarTower_r7c6448_1 : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance roePerturbationScalarComm_r7c6448_1 : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp
theorem multiplierBoundaryClass_roePerturbation
    (F G : multiplierAlgebra (X := X) (H := H))
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hGd : G.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hGF : G.val - F.val ∈ algebra (X := X) (H := H)) :
    multiplierBoundaryClass F hF hFd = multiplierBoundaryClass G hG hGd := by
  let L : Interval → multiplierAlgebra (X := X) (H := H) :=
    fun t => F + (t.val : ℂ) • (G - F)
  have hL : ∀ t, IsSelfAdjoint (L t) := by
    intro t
    change star (F + (t.val : ℂ) • (G - F)) = F + (t.val : ℂ) • (G - F)
    simp only [star_add, star_smul, star_sub, hF.star_eq, hG.star_eq,
      Complex.star_def, Complex.conj_ofReal]
  have hLd : ∀ t, (L t).val ^ 2 - 1 ∈ algebra (X := X) (H := H) := by
    intro t
    let K : Operator X H := (t.val : ℂ) • (G.val - F.val)
    have hK : K ∈ algebra (X := X) (H := H) := (algebra (X := X) (H := H)).smul_mem _ hGF
    have hm := F.property ⟨K, hK⟩
    have he : (L t).val ^ 2 - 1 = (F.val ^ 2 - 1) + F.val * K + K * F.val + K * K := by
      change (F.val + K) ^ 2 - 1 = _
      noncomm_ring
    rw [he]
    exact add_mem (add_mem (add_mem hFd hm.1) hm.2) (mul_mem hK hK)
  have hc : Continuous L := by
    exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_subtype_val).smul
      continuous_const)
  have h0 : L start = F := by simp [L, start]
  have h1 : L finish = G := by simp [L, finish]
  have h := multiplierBoundaryClass_homotopy L hL hLd hc
  simpa only [h0, h1] using h

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_WindingIndexEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing the winding index formula to one generator evaluation

The pairing, its naturality, homotopy invariance and power law are proved.
Only an actual circle class with coordinate index one remains to construct.
-/

noncomputable section

namespace CoarseAssembly

open Analytic unitInterval

theorem winding_index_hom (g : C(WindingCircle, WindingCircle)) (n : ℤ)
    (L : Path (0 : ℝ) (n : ℝ))
    (hL : ∀ t : unitInterval, g (t : ℝ) = (L t : WindingCircle)) :
    compactIndexPairing (circleUnitary g) =
      n • compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle)) := by
  let toCircleMap : C(WindingCircle, Circle) := ⟨AddCircle.toCircle, AddCircle.continuous_toCircle⟩
  have h := compactIndexPairing_homotopy
    ((ContinuousMap.Homotopy.refl toCircleMap).comp (windingHomotopy g n L hL))
  change compactIndexPairing (circleUnitary g) = compactIndexPairing (circleUnitary (circleDegree n)) at h
  rw [circleUnitary_degree, compactIndexPairing_zpow] at h
  exact h

theorem winding_index (g : C(WindingCircle, WindingCircle)) (n : ℤ)
    (L : Path (0 : ℝ) (n : ℝ))
    (hL : ∀ t : unitInterval, g (t : ℝ) = (L t : WindingCircle))
    (α : LocallyFiniteK1 WindingCircle) :
    compactIndexPairing (circleUnitary g) α =
      n * compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle)) α := by
  simpa only [AddMonoidHom.smul_apply, zsmul_eq_mul, Int.cast_id] using
    DFunLike.congr_fun (winding_index_hom g n L hL) α

/-- All the published circle fields follow from a single coordinate-index-one class. -/
def circleInputOfIndexOne (α : LocallyFiniteK1 WindingCircle)
    (hα : compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle)) α = 1) :
    PublishedCircleInput where
  fundamental := α
  pairing f := compactIndexPairing (circleUnitary f)
  loop_naturality f γ := by
    have h := DFunLike.congr_fun (compactIndexPairing_natural (circleUnitary f) γ) α
    exact h
  winding g n L hL := by
    rw [winding_index g n L hL α, hα, mul_one]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CircleCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An unconditional circle class of coordinate index one -/

noncomputable section

namespace CoarseAssembly

open Analytic

theorem circleFundamental_coordinate_index :
    compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle)) circleFundamental = 1 := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have he : (circleUnitary (ContinuousMap.id WindingCircle)).comp (e.symm : C(Circle, WindingCircle)) =
      ContinuousMap.id Circle := by
    apply ContinuousMap.ext
    intro z
    change AddCircle.toCircle (e.symm z) = z
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact e.apply_symm_apply z
  change compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle))
    (pushforward (compactMap (e.symm : C(Circle, WindingCircle))) negativeCircleClass) = 1
  have h := DFunLike.congr_fun
    (compactIndexPairing_natural (circleUnitary (ContinuousMap.id WindingCircle)) (e.symm : C(Circle, WindingCircle)))
    negativeCircleClass
  rw [he] at h
  exact h.trans negativeCircleClass_coordinate_index

open Congruence Rips

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsBoundaryDegeneracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degenerate families have zero whole-union Roe boundary

Vanishing is proved from an exact global involution, not from vanishing of
the individual finite-component K-theory classes.
-/

noncomputable section

namespace CoarseAssembly

namespace DiscreteRoe

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem separatedFamilyBoundary_involution (o : ∀ i, V i) (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (r : ℝ) (hr : 0 ≤ r) (hp : ∀ i, PropagationLE r (A i))
    (hself : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H)))
    (hinv : ∀ i, A i * A i = 1) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hself hsq = 0 := by
  let := separatedMetric o
  refine multiplierBoundaryClass_eq_zero _
    (separatedFamilyMultiplier_selfAdjoint o A C hC hA r hr hp hself)
    (diagonalFamily_square_mem_roe o A C hC hA r hr hp hself hsq) ?_
  apply Subtype.ext
  change diagonalFamily A C hC hA * diagonalFamily A C hC hA = 1
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext z
  rcases z with ⟨i, x⟩
  have hi := DFunLike.congr_fun (hinv i) (rowVector v i)
  have hix := congrArg (fun w : Module (V i) H => w x) hi
  simpa only [mul_apply_eq_comp, one_apply_eq_self, diagonalFamily_apply,
    rowVector_diagonalFamily, rowVector] using hix

end DiscreteRoe

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsUnitaryLocalization
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unitary equivalence commutes with finite-Rips localization -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)
  {c d : OddCycle C(Point X r, ℂ)}

theorem ripsCompression_unitary (e : c.UnitaryEquivalent d) :
    partitionCompression (representedSqrt r d) d.operator =
      operatorConjugation e.unitary.toLinearIsometry
        (partitionCompression (representedSqrt r c) c.operator) := by
  rw [partitionCompression_eq_sum, partitionCompression_eq_sum]
  let φ := operatorConjugationHom e.unitary.toLinearIsometry
  have hr (x : X) : representedSqrt r d x = φ (representedSqrt r c x) :=
    e.representation_eq (sqrtCoordinate r x)
  have ho : d.operator = φ c.operator := e.operator_eq
  change (∑ x, star (representedSqrt r d x) * (d.operator * representedSqrt r d x)) =
    φ (∑ x, star (representedSqrt r c x) * (c.operator * representedSqrt r c x))
  simp only [hr, ho, ← map_star, ← map_mul, ← map_sum]

end Rips
end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsScaleCompatibility
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Increasing-scale compatibility of the explicit Rips representatives

The barycentric coordinate functions pull back identically under increasing
the Rips scale. Consequently the localized operators themselves agree,
before taking a K-theory class.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X]
  {r s : ℝ} (hrs : r ≤ s)

variable [DecidableEq X]

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

theorem ampleRipsFamilyBoundary_scale (o : ∀ i, V i) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (c : ∀ i, OddCycle C(Point (V i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hnorm : ∀ i, ‖(c i).operator‖ ≤ C) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o s hs (fun i => coarsenedCycle hrs (c i))
      (fun i => coarsenedCycle_unital hrs (c i) (hπ i)) hF C hC hnorm =
      ampleRipsFamilyBoundary o r hr c hπ hF C hC hnorm := rfl

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ControlledRipsCoarsening
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.circleRepresentation_coordinate _root_.OAI.CoarseAssembly.Analytic.compactIndexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.indexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero _root_.OAI.CoarseAssembly.separatedRipsMap_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarsening and the constructed controlled assembly homomorphism -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r s : ℝ}

omit [∀ i, DecidableEq (Q i)] in
@[simp] theorem ControlledCycleFamily.coarsen_refl (c : ControlledCycleFamily Q r) :
    c.coarsen le_rfl = c := by
  cases c
  rfl

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitCircleFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The circle-family class without a countable-additivity assumption -/

noncomputable section

namespace CoarseAssembly

open Analytic
open scoped ZeroAtInfty

def windingCircleCycle : OddCycle C(WindingCircle, ℂ) :=
  negativeCircleCycle.precomp
    (ContinuousMap.compStarAlgHom' ℂ ℂ
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm :
        C(Circle, WindingCircle))).toNonUnitalStarAlgHom

theorem windingCircleCycle_norm : ‖windingCircleCycle.operator‖ ≤ 1 :=
  involution_norm_le_one _ negativeCircleOperator_selfAdjoint negativeCircleOperator_sq

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitBoundaryRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Roe representative of the counterexample's boundary cycle

This constructs the index representative from the explicit circle Fredholm
operator and the paper's hexagonal loops. Identification with the descended
canonical coarse assembly map remains a separate theorem.
-/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

variable {X : Type} [PseudoMetricSpace X] [Fintype X]

attribute [local instance] OAI.CoarseAssembly.explicitRepComponentDecidableEq
local instance explicitRepComponentMetric_r7c6448_1 (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit j
local instance explicitRepComponentPseudoMetric_r7c6448_1 (j : ℕ) : PseudoMetricSpace (BoundaryComponent j) :=
  (boundaryComponentMetric elementaryMoves chosenHolonomyUnit j).toPseudoMetricSpace
attribute [local instance] OAI.CoarseAssembly.explicitRepUnionMetric
local instance explicitRepBoundaryMetric_r7c6448_1 : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
local instance explicitRepBoundaryPseudoMetric_r7c6448_1 : PseudoMetricSpace BoundaryVertex :=
  (boundaryMetric elementaryMoves chosenHolonomyUnit).toPseudoMetricSpace
def boundaryReindexRoeHom :
    algebra (X := Sigma BoundaryComponent) (H := AmpleSpace) →⋆ₙₐ[ℂ] BoundaryRoe :=
  inclusionHom boundaryReindex.toEmbedding
    (fun x y => (boundaryReindex_dist elementaryMoves chosenHolonomyUnit x y).le)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsInclusionNaturality
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-Rips localization respects an actual vertex inclusion -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  (r : ℝ) (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) ≤ dist x y)

omit [DecidableEq X] [DecidableEq Y] in
theorem includedCycle_representedSqrt (c : OddCycle C(Point X r, ℂ)) (x : X) :
    representedSqrt r (includedCycle r e he c) (e x) = representedSqrt r c x := by
  change c.representation (inclusionFunctionHom r e he (sqrtCoordinate r (e x))) = _
  rw [inclusionFunctionHom_sqrt]
  rfl

omit [DecidableEq X] [DecidableEq Y] in
theorem includedCycle_representedSqrt_zero (c : OddCycle C(Point X r, ℂ))
    (y : Y) (hy : y ∉ Set.range e) :
    representedSqrt r (includedCycle r e he c) y = 0 := by
  change c.representation (inclusionFunctionHom r e he (sqrtCoordinate r y)) = 0
  rw [inclusionFunctionHom_sqrt_zero r e he y hy, map_zero]

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedFamilyNearby
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform small perturbation preserves the whole-union boundary

The difference need not be compact. The argument uses the short invertible
path in the actual Roe unitization, with no componentwise K-theory inference.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem separatedFamilyBoundary_eq_of_nearby (o : ∀ i, Q i)
    (A B : ∀ i, Operator (Q i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r : ℝ) (hr : 0 ≤ r) (hpA : ∀ i, PropagationLE r (A i))
    (hpB : ∀ i, PropagationLE r (B i))
    (hsA : ∀ i, IsSelfAdjoint (A i)) (hsB : ∀ i, IsSelfAdjoint (B i))
    (hqA : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) H)))
    (hqB : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (Q i) H)))
    (δ : ℝ) (hδ : 0 ≤ δ) (hδsmall : δ < 1 / 4)
    (hnear : ∀ i, ‖B i - A i‖ ≤ δ) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hpA hsA hqA =
      separatedFamilyBoundary o B D hD hB r hr hpB hsB hqB := by
  let := separatedMetric o
  apply multiplierBoundaryClass_eq_of_nearby _ _
    (separatedFamilyMultiplier_selfAdjoint o A C hC hA r hr hpA hsA)
    (separatedFamilyMultiplier_selfAdjoint o B D hD hB r hr hpB hsB)
    (diagonalFamily_square_mem_roe o A C hC hA r hr hpA hsA hqA)
    (diagonalFamily_square_mem_roe o B D hD hB r hr hpB hsB hqB)
  exact (diagonalFamily_sub_norm_le B A D C hD hC hB hA δ hδ hnear).trans_lt hδsmall

end CoarseAssembly.DiscreteRoe

end

end OAI
end


