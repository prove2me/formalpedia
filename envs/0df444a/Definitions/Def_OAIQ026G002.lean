-- Prove2me | Definitions.Def_OAIQ026G002
-- name    : OAIQ026G002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:35:25.60899+00:00
-- url     : https://prove2.me/theorems/8082a915-20e2-4f5a-9eba-f671f1ab05bf
-- title:
--   Definitions bundle OAIQ026G002 of the split of OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.GeneralMahler.general_mahler`, carved from OpenAI's openai/math development (OpenAI, *The Mahler Conjecture for General Convex Bodies (result family 087)*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 909 declarations of OpenAI's Lean: 817 definitions, 10 inductive types or structures and 82 theorems. The definitions and types are `OAI.GeneralMahler.ProjField.BB`, `OAI.GeneralMahler.ProjField.BDiff`, `OAI.GeneralMahler.ProjField.BL`, `OAI.GeneralMahler.ProjField.Balanced`, `OAI.GeneralMahler.ProjField.Bgap`, `OAI.GeneralMahler.ProjField.Ct`, `OAI.GeneralMahler.ProjField.DD`, `OAI.GeneralMahler.ProjField.DLMat`, `OAI.GeneralMahler.ProjField.DVec`, `OAI.GeneralMahler.ProjField.DelP`, `OAI.GeneralMahler.ProjField.Dnorm`, `OAI.GeneralMahler.ProjField.Dterm`, `OAI.GeneralMahler.ProjField.EZ`, `OAI.GeneralMahler.ProjField.FA`, `OAI.GeneralMahler.ProjField.FL`, `OAI.GeneralMahler.ProjField.Hcov`, `OAI.GeneralMahler.ProjField.Hp0`, `OAI.GeneralMahler.ProjField.Hpart`, `OAI.GeneralMahler.ProjField.Idw`, `OAI.GeneralMahler.ProjField.Iw`, `OAI.GeneralMahler.ProjField.J`, `OAI.GeneralMahler.ProjField.JVec`, `OAI.GeneralMahler.ProjField.Jtest`, `OAI.GeneralMahler.ProjField.LDel`, `OAI.GeneralMahler.ProjField.LLw`, `OAI.GeneralMahler.ProjField.Ld`, `OAI.GeneralMahler.ProjField.Lmat`, `OAI.GeneralMahler.ProjField.Lr`, `OAI.GeneralMahler.ProjField.M`, `OAI.GeneralMahler.ProjField.MB`, `OAI.GeneralMahler.ProjField.NK`, `OAI.GeneralMahler.ProjField.Nt`, `OAI.GeneralMahler.ProjField.RM`, `OAI.GeneralMahler.ProjField.RR`, `OAI.GeneralMahler.ProjField.RadiusE`, `OAI.GeneralMahler.ProjField.Ro`, `OAI.GeneralMahler.ProjField.WH`, `OAI.GeneralMahler.ProjField.WK`, `OAI.GeneralMahler.ProjField.WW`, `OAI.GeneralMahler.ProjField.Xb` and 787 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Convex_GeneralMahler_Angle`, `Convex_GeneralMahler_Beta`, `Convex_GeneralMahler_BiWeight`, `Convex_GeneralMahler_BoundField`, `Convex_GeneralMahler_Budget_Blocks`, `Convex_GeneralMahler_Budget_Eq19`, `Convex_GeneralMahler_Budget_Eq23`, `Convex_GeneralMahler_Budget_Extract`, `Convex_GeneralMahler_Budget_Parity`, `Convex_GeneralMahler_Budget_Penalty`, `Convex_GeneralMahler_Budget_Segment`, `Convex_GeneralMahler_Compare`, `Convex_GeneralMahler_Contact`, `Convex_GeneralMahler_CovHerm`, `Convex_GeneralMahler_Cutoff`, `Convex_GeneralMahler_DefectIBP`, `Convex_GeneralMahler_DefectLayer`, `Convex_GeneralMahler_Edge`, `Convex_GeneralMahler_EntScalar`, `Convex_GeneralMahler_EntropyMap`, `Convex_GeneralMahler_Eq18`, `Convex_GeneralMahler_Field`, `Convex_GeneralMahler_Forms`, `Convex_GeneralMahler_GainFinal`, `Convex_GeneralMahler_GaussianTail`, `Convex_GeneralMahler_GradientLayer`, `Convex_GeneralMahler_HLayer`, `Convex_GeneralMahler_HMatrix`, `Convex_GeneralMahler_IBP`, `Convex_GeneralMahler_Indicator`, `Convex_GeneralMahler_Kernel`, `Convex_GeneralMahler_LFun`, `Convex_GeneralMahler_LayerMeasure`, `Convex_GeneralMahler_Linear_Eq26`, `Convex_GeneralMahler_Linear_Eq27`, `Convex_GeneralMahler_Linear_Final`, `Convex_GeneralMahler_Linear_Nu`, `Convex_GeneralMahler_Linear_SpectralIBP`, `Convex_GeneralMahler_Main`, `Convex_GeneralMahler_MatrixBox`, `Convex_GeneralMahler_MatrixDeriv`, `Convex_GeneralMahler_Middle_Bound2`, `Convex_GeneralMahler_Middle_Cells`, `Convex_GeneralMahler_Middle_Features`, `Convex_GeneralMahler_Middle_Poly`, `Convex_GeneralMahler_Middle_Prefix`, `Convex_GeneralMahler_Middle_Tab`, `Convex_GeneralMahler_Middle_Tiles`, `Convex_GeneralMahler_Middle_Trap`, `Convex_GeneralMahler_Middle_Traversal`, `Convex_GeneralMahler_MixedField`, `Convex_GeneralMahler_ParamA`, `Convex_GeneralMahler_Qprimitive`, `Convex_GeneralMahler_Rapid`, `Convex_GeneralMahler_Rigid_Basis`, `Convex_GeneralMahler_ScalarForm`, `Convex_GeneralMahler_Scalar_BoxJ`, `Convex_GeneralMahler_Scalar_Circle`, `Convex_GeneralMahler_Scalar_Data`, `Convex_GeneralMahler_Scalar_Grid`, `Convex_GeneralMahler_Scalar_HBox`, `Convex_GeneralMahler_Scalar_Integr`, `Convex_GeneralMahler_Scalar_LapBox`, `Convex_GeneralMahler_Scalar_LayerAlg`, `Convex_GeneralMahler_Scalar_Moments`, `Convex_GeneralMahler_Scalar_NodesTbl`, `Convex_GeneralMahler_Scalar_Pass`, `Convex_GeneralMahler_Scalar_QuantJ`, `Convex_GeneralMahler_Scalar_RealJ`, `Convex_GeneralMahler_Scalar_Stable`, `Convex_GeneralMahler_Scalar_Tail_Base`, `Convex_GeneralMahler_Scalar_Tail_Coords`, `Convex_GeneralMahler_Scalar_Tail_Enclose`, `Convex_GeneralMahler_Scalar_Tail_Limit`, `Convex_GeneralMahler_Scalar_Tail_PassTail`, `Convex_GeneralMahler_Scalar_Tail_Tower`, `Convex_GeneralMahler_Scalar_Universal`, `Convex_GeneralMahler_Scatter`, `Convex_GeneralMahler_ScatterField`, `Convex_GeneralMahler_Segment_Average`, `Convex_GeneralMahler_Segment_Chord`, `Convex_GeneralMahler_Segment_Cost`, `Convex_GeneralMahler_Segment_Disp`, `Convex_GeneralMahler_Segment_First`, `Convex_GeneralMahler_Segment_Mean`, `Convex_GeneralMahler_Segment_Phase`, `Convex_GeneralMahler_Segment_Small`, `Convex_GeneralMahler_ShiftBound`, `Convex_GeneralMahler_SimplexCone`, `Convex_GeneralMahler_Threshold`, `Convex_GeneralMahler_Update`, `Convex_GeneralMahler_Variation`.
--
--   **Imports.** It imports the published bundle `Def_GeneralMahler`; the bundles `OAIQ026G000` and `OAIQ026G001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.GeneralMahler.ProjField.C_bound`, `OAI.GeneralMahler.ProjField.budget`, `OAI.GeneralMahler.ProjField.entropy_decomp`, `OAI.GeneralMahler.ProjField.reserve`, `OAI.GeneralMahler.SCal.Eq04full`, `OAI.GeneralMahler.SCal.Grid.Nodes.by0_20`, `OAI.GeneralMahler.SCal.Grid.Nodes.by100_120`, `OAI.GeneralMahler.SCal.Grid.Nodes.by120_140`, `OAI.GeneralMahler.SCal.Grid.Nodes.by140_160`, `OAI.GeneralMahler.SCal.Grid.Nodes.by160_180`, `OAI.GeneralMahler.SCal.Grid.Nodes.by180_200`, `OAI.GeneralMahler.SCal.Grid.Nodes.by200_220`, `OAI.GeneralMahler.SCal.Grid.Nodes.by20_40`, `OAI.GeneralMahler.SCal.Grid.Nodes.by220_240`, `OAI.GeneralMahler.SCal.Grid.Nodes.by240_260`, `OAI.GeneralMahler.SCal.Grid.Nodes.by260_280`, `OAI.GeneralMahler.SCal.Grid.Nodes.by280_300`, `OAI.GeneralMahler.SCal.Grid.Nodes.by300_320`, `OAI.GeneralMahler.SCal.Grid.Nodes.by320_340`, `OAI.GeneralMahler.SCal.Grid.Nodes.by340_360`, `OAI.GeneralMahler.SCal.Grid.Nodes.by360_380`, `OAI.GeneralMahler.SCal.Grid.Nodes.by400_420`, `OAI.GeneralMahler.SCal.Grid.Nodes.by40_60`, `OAI.GeneralMahler.SCal.Grid.Nodes.by420_440`, `OAI.GeneralMahler.SCal.Grid.Nodes.by440_460`, `OAI.GeneralMahler.SCal.Grid.Nodes.by460_480`, `OAI.GeneralMahler.SCal.Grid.Nodes.by480_500`, `OAI.GeneralMahler.SCal.Grid.Nodes.by500_520`, `OAI.GeneralMahler.SCal.Grid.Nodes.by520_540`, `OAI.GeneralMahler.SCal.Grid.Nodes.by540_560`, `OAI.GeneralMahler.SCal.Grid.Nodes.by560_580`, `OAI.GeneralMahler.SCal.Grid.Nodes.by580_600`, `OAI.GeneralMahler.SCal.Grid.Nodes.by600_620`, `OAI.GeneralMahler.SCal.Grid.Nodes.by60_80`, `OAI.GeneralMahler.SCal.Grid.Nodes.by620_640`, `OAI.GeneralMahler.SCal.Grid.Nodes.by640_660`, `OAI.GeneralMahler.SCal.Grid.Nodes.by660_680`, `OAI.GeneralMahler.SCal.Grid.Nodes.by680_700`, `OAI.GeneralMahler.SCal.Grid.Nodes.by700_720`, `OAI.GeneralMahler.SCal.Grid.Nodes.by80_100`, `OAI.GeneralMahler.SCal.Grid.Nodes.covered`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_0_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_10_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_11_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_12_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_13_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_14_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_15_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_16_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_17_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_18_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_19_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_1_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_20_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_21_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_22_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_23_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_24_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_25_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_26_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_28_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_2_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_3_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_4_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_5_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_6_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_7_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_8_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_9_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_0_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_10_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_11_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_12_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_13_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_14_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_15_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_16_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_17_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_18_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_19_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_1_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_20_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_21_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_22_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_23_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_24_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_25_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_26_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_2_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_3_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_4_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_5_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_6_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_7_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_8_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_9_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.gfalse`, `OAI.GeneralMahler.SCal.Mid.Tab.gtrue`, `OAI.GeneralMahler.SCal.SE.costPos` and `OAI.GeneralMahler.SCal.SE.short`; the proofs of `OAI.GeneralMahler.Complete_profile_input`, `OAI.GeneralMahler.ProjField.C_bound`, `OAI.GeneralMahler.ProjField.budget`, `OAI.GeneralMahler.ProjField.entropy_decomp`, `OAI.GeneralMahler.ProjField.reserve`, `OAI.GeneralMahler.SCal.Eq04full`, `OAI.GeneralMahler.SCal.Grid.Nodes.by0_20`, `OAI.GeneralMahler.SCal.Grid.Nodes.by100_120`, `OAI.GeneralMahler.SCal.Grid.Nodes.by120_140`, `OAI.GeneralMahler.SCal.Grid.Nodes.by140_160`, `OAI.GeneralMahler.SCal.Grid.Nodes.by160_180`, `OAI.GeneralMahler.SCal.Grid.Nodes.by180_200`, `OAI.GeneralMahler.SCal.Grid.Nodes.by200_220`, `OAI.GeneralMahler.SCal.Grid.Nodes.by20_40`, `OAI.GeneralMahler.SCal.Grid.Nodes.by220_240`, `OAI.GeneralMahler.SCal.Grid.Nodes.by240_260`, `OAI.GeneralMahler.SCal.Grid.Nodes.by260_280`, `OAI.GeneralMahler.SCal.Grid.Nodes.by280_300`, `OAI.GeneralMahler.SCal.Grid.Nodes.by300_320`, `OAI.GeneralMahler.SCal.Grid.Nodes.by320_340`, `OAI.GeneralMahler.SCal.Grid.Nodes.by340_360`, `OAI.GeneralMahler.SCal.Grid.Nodes.by360_380`, `OAI.GeneralMahler.SCal.Grid.Nodes.by400_420`, `OAI.GeneralMahler.SCal.Grid.Nodes.by40_60`, `OAI.GeneralMahler.SCal.Grid.Nodes.by420_440`, `OAI.GeneralMahler.SCal.Grid.Nodes.by440_460`, `OAI.GeneralMahler.SCal.Grid.Nodes.by460_480`, `OAI.GeneralMahler.SCal.Grid.Nodes.by480_500`, `OAI.GeneralMahler.SCal.Grid.Nodes.by500_520`, `OAI.GeneralMahler.SCal.Grid.Nodes.by520_540`, `OAI.GeneralMahler.SCal.Grid.Nodes.by540_560`, `OAI.GeneralMahler.SCal.Grid.Nodes.by560_580`, `OAI.GeneralMahler.SCal.Grid.Nodes.by580_600`, `OAI.GeneralMahler.SCal.Grid.Nodes.by600_620`, `OAI.GeneralMahler.SCal.Grid.Nodes.by60_80`, `OAI.GeneralMahler.SCal.Grid.Nodes.by620_640`, `OAI.GeneralMahler.SCal.Grid.Nodes.by640_660`, `OAI.GeneralMahler.SCal.Grid.Nodes.by660_680`, `OAI.GeneralMahler.SCal.Grid.Nodes.by680_700`, `OAI.GeneralMahler.SCal.Grid.Nodes.by700_720`, `OAI.GeneralMahler.SCal.Grid.Nodes.by80_100`, `OAI.GeneralMahler.SCal.Grid.Nodes.covered`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_0_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_10_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_11_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_12_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_13_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_14_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_15_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_16_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_17_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_18_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_19_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_1_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_20_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_21_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_22_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_23_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_24_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_25_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_26_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_28_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_2_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_3_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_4_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_5_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_6_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_7_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_8_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.cfalse_9_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_0_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_10_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_11_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_12_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_13_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_14_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_15_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_16_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_17_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_18_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_19_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_1_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_20_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_21_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_22_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_23_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_24_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_25_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_26_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_2_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_3_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_4_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_5_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_6_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_7_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_8_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.ctrue_9_0_90`, `OAI.GeneralMahler.SCal.Mid.Tab.gfalse`, `OAI.GeneralMahler.SCal.Mid.Tab.gtrue`, `OAI.GeneralMahler.SCal.SE.costPos`, `OAI.GeneralMahler.SCal.SE.short` and `OAI.GeneralMahler.general_mahler`.
-- source:
--   OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087), OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_GeneralMahler
import Definitions.Def_OAIQ026G000
import Definitions.Def_OAIQ026G001

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_IBP
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.opCLE_apply _root_.OAI.GeneralMahler.opCLE_symm_apply _root_.OAI.GeneralMahler.opPair_apply _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Integration-by-parts formula for the normal measure.
Derived by differentiating translations; includes Lipschitz projections. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Filter Topology Set Real WithLp
open scoped RealInnerProductSpace ENNReal NNReal
namespace GeneralMahler
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem smoothG_translate_derivative {f : Rn n → F}
    (hf : PolyBound f) (hc : Continuous f) (a : Rn n)
    (hD : ∀ᵐ x ∂normal n, HasFDerivAt f (fderiv ℝ f (x+a)) (x+a))
    {g : Rn n → ℝ} (hg : Integrable g (normal n))
    (hg' : ∀ x, ∀ b ∈ ball a 1, ‖f (x+b) - f (x+a)‖ ≤ g x * ‖b-a‖) :
    Integrable (fun x => fderiv ℝ f (x+a)) (normal n) ∧
      HasFDerivAt (smoothG f) (∫ x, fderiv ℝ f (x+a) ∂normal n) a := by
  let FF := fun (y x : Rn n) => f (x+y)
  have hF (y) : AEStronglyMeasurable (FF y) (normal n) :=
    (hc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hfa := (hf.comp ((PolyBound.id (X := Rn n)).add (PolyBound.const a))).gaussian_integrable (hF a)
  have he₁ : Measurable (fun x => fderiv ℝ f (x+a)) :=
    (measurable_fderiv _ f).comp (continuous_id.add continuous_const).measurable
  apply hasFDerivAt_integral_of_dominated_loc_of_lip' (F := FF)
    (ball_mem_nhds a zero_lt_one)
    (fun y _ => hF y) hfa he₁.aestronglyMeasurable (ae_of_all _ hg') hg
  filter_upwards [hD] with x hx
  simpa only [FF,Function.comp_def, zero_add, ContinuousLinearMap.comp_id] using
    hx.comp a ((hasFDerivAt_const x a).add (hasFDerivAt_id a))

theorem normal_IBP {f : Rn n → F}
    (hf : PolyBound f) (hc : Continuous f)
    (hD : ∀ᵐ x ∂normal n, DifferentiableAt ℝ f x)
    {g : Rn n → ℝ} (hg : Integrable g (normal n))
    (hg' : ∀ x, ∀ b : Rn n, ‖b‖ < 1 → ‖f (x+b) - f x‖ ≤ g x * ‖b‖)
    (v : Rn n) :
    (∫ x, fderiv ℝ f x v ∂normal n) = ∫ x, ⟪x,v⟫ • f x ∂normal n := by
  obtain ⟨hw,hde⟩ := smoothG_translate_derivative hf hc 0
    (by simpa using (hD.mono fun x hx => hx.hasFDerivAt)) hg
    (by simpa only [sub_zero,add_zero,mem_ball,dist_zero_right] using hg')
  simp only [add_zero] at hw hde
  obtain ⟨hw',hde'⟩ := smoothG_hasFDeriv hf hc.stronglyMeasurable 0
  rw [← ContinuousLinearMap.integral_apply hw, hde.unique hde',
    ContinuousLinearMap.integral_apply hw', normal_integral]
  apply integral_congr_ae; filter_upwards with x; simp [G',smul_smul]

theorem normal_IBP_lipschitz {f : Rn n → F}
    {K : ℝ≥0} (h : LipschitzWith K f) (v : Rn n) :
    (∫ x, fderiv ℝ f x v ∂normal n) = ∫ x, ⟪x,v⟫ • f x ∂normal n :=
  normal_IBP (PolyBound.lipschitz h) h.continuous
    (normal_ac.ae_le h.ae_differentiableAt) (g := fun x => K) (integrable_const _)
    (fun x b _ => by simpa [dist_eq_norm] using h.dist_le_mul (x+b) x) v

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Field
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02, Gaussian field notation and mean equations. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Filter Real Set Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers

variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)

lemma Pmat_psd (z g) : 0 ≤ q.Pmat z g := (projJac_pos ..).nonneg
lemma Pmat_le (z g) : q.Pmat z g ≤ 1 := projJac_le_one ..
lemma Pmat_herm (z g) : (q.Pmat z g).IsHermitian := projJac_sym ..

lemma deriv_shift_mean (z : ℝ) :
    op (meanJac q.C q.root (q.shift z)) (deriv q.shift z) = p z • q.U := by
  have hD := (q.shift_cd.differentiable (by norm_num)).differentiableAt (x := z) |>.hasDerivAt
  have he := (hasFDerivAt_mean q.C q.root _).comp_hasDerivAt z hD
  have hf : (mean q.C q.root) ∘ q.shift = fun z => a z • q.U := funext fun z => q.XT_mean z
  rw [hf] at he
  exact he.unique ((d_a z).smul_const _)

def r1 (z : ℝ) := -deriv q.Bt z

lemma Bt_hasDeriv (z : ℝ) :
    HasDerivAt q.Bt (⟪q.U, p z • q.U-deriv q.shift z⟫/(m:ℝ)) z := by
  have hD := (q.shift_cd.differentiable (by norm_num)).differentiableAt (x := z) |>.hasDerivAt
  have hh : q.Bt = fun z => ⟪q.U,a z • q.U-q.shift z⟫/(m:ℝ) := funext fun z => by rw [Bt,Y_mean]
  rw [hh]
  have he := ((hasDerivAt_const z q.U).inner ℝ (((d_a z).smul_const q.U).sub hD)).div_const (m:ℝ)
  simpa only [inner_zero_left,zero_add,add_zero, Pi.sub_apply] using he

lemma r1_eq (z : ℝ) : q.r1 z = ⟪q.U,deriv q.shift z-p z • q.U⟫ / (m:ℝ) := by
  rw [r1,(q.Bt_hasDeriv z).deriv]
  simp only [inner_sub_right]; ring

lemma Bt_nonneg (z : ℝ) : 0 ≤ q.Bt z := by
  have he := affineN_integrable q.root (q.shift z)
  have hi : Integrable (q.YT z) (normal m) := by
    rw [funext (q.YT_sub z)]
    exact (sample_integrable ..).sub he
  unfold Bt
  apply div_nonneg _ (Nat.cast_nonneg m)
  change 0 ≤ (innerSL ℝ q.U) (∫ g, q.YT z g ∂_)
  rw [← (innerSL ℝ q.U).integral_comp_comm hi]
  exact integral_nonneg fun x => mem_posDual.mp (proj_mem ..) (interior_subset q.U_in)

section
variable [NeZero m]
lemma r1_pos (z : ℝ) : 0 < q.r1 z := by
  rw [q.r1_eq]
  have hp : 0 < (m:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  apply div_pos _ hp
  let A := meanJac q.C q.root (q.shift z)
  let b := deriv q.shift z
  have hu : q.U ≠ 0 := by
    intro h
    have he := q.ip
    rw [h,inner_zero_left] at he; linarith
  have hq : op A b = p z • q.U := q.deriv_shift_mean z
  let x := op A b
  have hx : x ≠ 0 := by
    change op A b ≠ _
    rw [hq]; exact smul_ne_zero (p_pos z).ne' hu
  have he : 0 < ⟪x,b-x⟫ := by
    have hpos := mean_pos q.C q.root ⟨_,q.U_in⟩ (q.shift z)
    have hless := mean_lt_one q.C q.root ⟨_,q.V_in⟩ (q.shift z)
    -- decompose b=x+y; evaluate ⟪x,y⟫ = A and I-A energies
    have h₁ := (op_posDef_iff.mp hless).2 x hx
    have h₂ : 0 ≤ ⟪b-x,op A (b-x)⟫ := (op_posSemidef_iff.mp hpos.posSemidef).2 _
    rw [_root_.map_sub,_root_.map_one,_root_.sub_apply] at h₁
    change 0 < ⟪x,x-op A x⟫ at h₁
    have hu := op_iff_hermitian.mp hpos.1 b x
    change ⟪op A b,x⟫ = ⟪b,op A x⟫ at hu
    rw [_root_.map_sub] at h₂
    change 0 ≤ ⟪b-x,x-op A x⟫ at h₂
    change ⟪x,x⟫ = ⟪b,op A x⟫ at hu
    simp only [inner_sub_left,inner_sub_right] at *
    rw [real_inner_comm b]
    linarith
  dsimp only [x] at he
  rw [hq,real_inner_smul_left] at he; exact pos_of_mul_pos_right he (p_pos z).le
end
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_HLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Equation (6): projection integration by parts; derivative
of the cumulative scalar layer kernel. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ}

local notation "std" => EuclideanSpace.basisFun (Fin m) ℝ

namespace ProjField
variable (q : ProjField m)

lemma XT_lipschitz (z : ℝ) : ∃ K, LipschitzWith K (q.XT z) := by
  exact ⟨_,(coneProj_lip q.C).comp ((q.root.toContinuousLinearMap.lipschitz).add (LipschitzWith.const _))⟩

lemma XT_diff (z : ℝ) :
    ∀ᵐ g ∂normal m, HasFDerivAt (q.XT z)
      ((op (q.Pmat z g)).comp (op q.S)) g := by
  have hh := (coneProj_lip q.C).ae_differentiableAt (μ := volume)
  filter_upwards [(tendsto_ae_affineN q.root (q.shift z)).eventually hh] with g hg
  simp only [XT,Pmat,projJac_op]
  rw [← q.matrix_eq]
  have hl := hg.hasFDerivAt.comp g
    (q.root.hasFDerivAt.add_const (q.shift z))
  exact hl

lemma normal_XT_inner (z : ℝ) (u v : Rn m) :
    (∫ g, ⟪v,op (q.Pmat z g) (op q.S u)⟫ ∂normal m) =
    ∫ g, ⟪g,u⟫ * ⟪v,q.XT z g⟫ ∂normal m := by
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ v
  obtain ⟨K,hK⟩ := q.XT_lipschitz z
  have he := normal_IBP_lipschitz (l.lipschitz.comp hK) u
  change _ = ∫ g, ⟪g,u⟫ • (l ∘ q.XT z) g ∂_
  rw [← he]
  apply integral_congr_ae
  filter_upwards [q.XT_diff z] with g hg
  rw [(l.hasFDerivAt.comp g hg).fderiv]
  rfl

lemma integral_P_ip (z : ℝ) (x y : Rn m) :
    (∫ g, ⟪x,op (q.Pmat z g) y⟫ ∂normal m) =
      ⟪x,op (meanJac q.C q.root (q.shift z)) y⟫ :=
  (op_inner_integral (meanJac_integrable ..) _ _).symm

theorem avH_as_mean_ip (z : ℝ) :
    q.avH z = (∫ g, ⟪q.XT z g,q.Z g⟫ ∂normal m) / (m:ℝ) := by
  unfold avH trN
  congr 1
  rw [q.trace_SPS]
  simp_rw [← q.integral_P_ip, q.normal_XT_inner]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with g
    have he := (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr' g
    have hu (i) : ⟪g,std i⟫ * ⟪op q.S (std i),q.XT z g⟫ =
        ⟪q.XT z g,op q.S (⟪std i,g⟫ • std i)⟫ := by
      rw [_root_.map_smul,real_inner_smul_right,real_inner_comm g,real_inner_comm (q.XT z g)]
    simp_rw [hu]
    rw [← inner_sum,← _root_.map_sum,he,q.Z_def]
  · exact fun i _ => q.integrable_pair z _ _

lemma avH_as_energy (z : ℝ) :
    q.avH z =
      (2 * meanEnergy q.C q.root (q.shift z) - ⟪q.shift z,a z • q.U⟫) / (m:ℝ) := by
  rw [q.avH_as_mean_ip]
  congr 1
  let x := q.shift z
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ x
  have hh (g) : ⟪q.XT z g,q.Z g⟫ =
      2 * energy q.C (affineN q.root x g) - l (q.XT z g) := by
    have he := q.XP z g
    rw [q.YT_sub z g,inner_sub_right,inner_add_right,real_inner_self_eq_norm_sq] at he
    change _ = 2*(‖q.XT z g‖^2/2)- ⟪q.shift z,q.XT z g⟫
    rw [real_inner_comm (q.XT z g) (q.shift z)]
    linarith
  simp_rw [hh]
  have hi : Integrable (fun g => l (q.XT z g)) (normal m) :=
    l.integrable_comp (sample_integrable ..)
  rw [integral_sub ((energy_integrable ..).const_mul _) hi, integral_const_mul,
    l.integral_comp_comm (show Integrable (q.XT z) (normal m) from sample_integrable ..),
    q.XT_mean]
  rfl

lemma deriv_avH (z : ℝ) :
    HasDerivAt q.avH ((p z)*q.Bt z + (a z)*q.r1 z) z := by
  have hz := (q.shift_cd.differentiable (by norm_num)).differentiableAt (x := z) |>.hasDerivAt
  have he := (meanEnergy_derivative q.C q.root (q.shift z)).comp_hasDerivAt z hz
  have hh := (((he.const_mul (2:ℝ)).sub (hz.inner ℝ ((d_a z).smul_const q.U))).div_const (m:ℝ))
  rw [funext q.avH_as_energy]
  have hm : mean q.C q.root (q.shift z) = a z • q.U := q.XT_mean z
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first
  | rfl
  | (rw [q.r1_eq,Bt,q.Y_mean,hm];
      simp only [inner_sub_right, innerSL_apply_apply,real_inner_smul_left,
        real_inner_smul_right]; simp only [real_inner_comm (q.U)]; ring)

section
variable [NeZero m]
-- the nonnegative variance correction in (6)
omit [NeZero m] in
lemma avH_variance (z : ℝ) :
    q.avH z = (∫ g, ‖q.XT z g-a z • q.U‖ ^ 2 ∂normal m)/(m:ℝ) +
      a z*q.Bt z := by
  let b := a z • q.U
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ b
  have he : (fun g => ‖q.XT z g - a z • q.U‖^2) =
      fun g => 2*energy q.C (affineN q.root (q.shift z) g)-2*l (q.XT z g)+‖b‖^2 := by
    ext g
    change _ = 2*(‖q.XT z g‖^2/2)-2*⟪b,q.XT z g⟫+‖b‖^2
    rw [real_inner_comm]
    have hu := norm_sub_sq_real (q.XT z g) b
    change ‖q.XT z g-b‖^2 = _
    linarith
  have hi : Integrable (fun g => l (q.XT z g)) (normal m) :=
    l.integrable_comp (sample_integrable ..)
  rw [he]
  rw [integral_add, integral_sub, integral_const, integral_const_mul,integral_const_mul]
  · rw [l.integral_comp_comm (show Integrable (q.XT z) (normal m) from sample_integrable ..),
      q.XT_mean,q.avH_as_energy,Bt,q.Y_mean]
    simp only [probReal_univ,smul_eq_mul,one_mul]
    change _ = ( _*meanEnergy q.C q.root _ - _*⟪b,b⟫+_)/_+_
    rw [← real_inner_self_eq_norm_sq]
    dsimp only [b]
    simp only [inner_sub_right,real_inner_smul_left,real_inner_smul_right]
    rw [real_inner_comm (q.U)]
    ring
  all_goals
    first | exact (energy_integrable ..).const_mul _
          | exact hi.const_mul _
          | exact integrable_const _
          | exact ((energy_integrable ..).const_mul _).sub (hi.const_mul _)
end
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_BoundField
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Uniform cone hypotheses for the full-real-line estimates.
The extra constants are not inputs to main theorems: for every field
such bounds exist. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ}
namespace ProjField

variable {q : ProjField m} {K : ℝ} (hK : q.Bound K)

section
variable (q)

lemma Bt_cd : ContDiff ℝ 1 q.Bt := by
  have he : q.Bt = fun z => ⟪q.U,a z • q.U-q.shift z⟫/(m:ℝ) := funext fun z => by rw [Bt,q.Y_mean]
  rw [he]
  exact ((contDiff_const.inner ℝ ((contDiff_a.smul contDiff_const).sub q.shift_cd))).div_const _

end
section
variable [NeZero m]

omit [NeZero m] in
lemma mul_Bt_avH (q : ProjField m) (z : ℝ) : a z * q.Bt z ≤ q.avH z := by
  rw [q.avH_variance]; exact le_add_of_nonneg_left (div_nonneg
    (integral_nonneg (fun x => sq_nonneg _)) (Nat.cast_nonneg _))

include hK in
omit [NeZero m] in
lemma XT_lip' (x y : Rn m) (z : ℝ) :
    ‖q.XT z x-q.XT z y‖ ≤ K * ‖x-y‖ := by
  apply le_trans _ (hK.normZ (x-y))
  have he : affineN q.root (q.shift z) x-affineN q.root (q.shift z) y = q.Z (x-y) := by
    unfold affineN Z; rw [_root_.map_sub]; abel
  rw [← he]
  simpa only [XT,sample,dist_eq_norm, NNReal.coe_one,one_mul] using (coneProj_lip q.C).dist_le_mul
    (affineN q.root (q.shift z) x) (affineN q.root (q.shift z) y)

end

def J (m : ℕ) := ∫ x : Rn m, ‖x‖ ∂normal m

lemma i_norm (m : ℕ) : Integrable (fun x : Rn m => ‖x‖) (normal m) :=
  (ProbabilityTheory.IsGaussian.integrable_id (μ := normal m)).norm
lemma j_nonneg (m : ℕ) : 0 ≤ J m := integral_nonneg fun _x => norm_nonneg _

-- Bounding a Lipschitz map by its mean absolute norm
lemma norm_le_mean_error {E:Type*} [NormedAddCommGroup E] {F : Rn m → E} {K : ℝ}
    (hf : Integrable F (normal m)) (hl : ∀ x y, ‖F x - F y‖ ≤ K*‖x-y‖)
    (hk : 0 ≤ K) (x : Rn m) :
    ‖F x‖ ≤ (∫ x, ‖F x‖ ∂normal m)+ K*(‖x‖+J m) := by
  let μ := normal m
  have hg : Integrable (fun y : Rn m => (‖x‖+‖y‖)) μ :=
    (integrable_const _).add (i_norm _)
  calc
    _ = ∫ y:Rn m, ‖F x‖ ∂μ := by dsimp [μ]; simp
    _ ≤ ∫ y:Rn m, (‖F y‖ + K*(‖x‖+‖y‖)) ∂μ := integral_mono (integrable_const _)
      (hf.norm.add (hg.const_mul K)) (fun y => by
        have hh := norm_add_le (F x-F y) (F y)
        rw [sub_add_cancel] at hh
        nlinarith [norm_sub_le x y, hl x y])
    _ = _ := by
      rw [integral_add hf.norm (hg.const_mul _),integral_const_mul, integral_add
        (integrable_const _) (i_norm _)]
      dsimp [μ,J]; simp
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_GaussianTail
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.opCLE_apply _root_.OAI.GeneralMahler.opCLE_symm_apply _root_.OAI.GeneralMahler.opPair_apply _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Explicit exponential tail and ball estimates for standard Gaussian.
Constants depend only on the ambient dimension (and polynomial degree). -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped Topology ENNReal NNReal
namespace GeneralMahler
variable {m : ℕ}

theorem normal_tail (m n : ℕ) :
    ∃ C ≥ (0:ℝ), ∀ s : ℝ, 0 ≤ s →
    (∫ x : Rn m in {x | s ≤ ‖x‖}, (1+‖x‖)^n ∂(normal m)) ≤ C * exp (-(s ^ 2)/4) := by
  classical
  let c := (√(2 * π))⁻¹ ^ m
  let f := fun x : Rn m => (1+‖x‖)^n * Real.exp (-(1 * ‖x‖))
  have hi : Integrable f := integrable_polynomial_exp_tail zero_lt_one _
  use (c * exp 1)*(∫ x, f x)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨mul_nonneg (by positivity) (integral_nonneg fun x => by dsimp [f]; positivity),?_⟩
  intro s hs
  let S := {x : Rn m|s ≤ ‖x‖}
  have hm : MeasurableSet S :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  let g := fun x : Rn m => (1+‖x‖)^n
  change ∫ x in S, g x ∂normal m ≤ _
  rw [← integral_indicator hm,normal_integral]
  let a := c * exp 1 * exp (-(s^2)/4)
  have HE (x) : nDensity x • S.indicator g x ≤ a*f x := by
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      change c*_ * g x ≤ _
      have h1 : exp (-(‖x‖^2)/2) ≤ exp 1 * exp (-(s^2)/4) * exp (-(1*‖x‖)) := by
        change s ≤ ‖x‖ at hx
        rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg (‖x‖-2)]
      have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc)
        (show 0 ≤ g x by dsimp [g]; positivity)
      dsimp only [g,a,f] at *
      linarith
    · rw [indicator_of_notMem hx,smul_zero]
      dsimp [a,f]; positivity
  have hu := (integrable_envelope (μ := normal m) n).indicator hm
  calc
    _ ≤ ∫ x, a*f x := integral_mono (normal_integrable_iff.mp hu) (hi.const_mul _) HE
    _ = _ := by rw [integral_const_mul]; dsimp [a]; ring

/-- Useful for absorbing large cutoff estimates into the smaller Gaussian
lower bound in Lemma Gaussian layer tails. -/
lemma tail_exp_le_a (s : ℝ) (hs : 0 ≤ s) :
    Real.exp (-( (4*(1+s))^2) / 4) ≤ (√(2*π)) * Real.exp 4 * Layers.a (-s) := by
  have h := Layers.a_low s hs
  rw [phi_apply] at h
  have hsq : 0 < √(2*π) := by positivity
  have hE : 1+s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have h₁ : Real.exp (-((4*(1+s))^2)/4) * (1+s)^2 ≤ Real.exp (-(s^2)/2) := calc
    _ ≤ Real.exp (-((4*(1+s))^2)/4) * (Real.exp s * Real.exp s) := by rw [← pow_two]; gcongr
    _ ≤ _ := by
      simp_rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have h₂ := mul_le_mul_of_nonneg_left h (show 0 ≤ √(2*π)*Real.exp 4 by positivity)
  apply le_trans _ h₂
  calc
    _ ≤ Real.exp (-(s^2)/2) / (1+s)^2 := (le_div_iff₀ (by positivity)).mpr h₁
    _ = _ := by rw [Real.exp_neg (4:ℝ)]; field_simp

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ShiftBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02 growth estimates for negative and positive bias layers. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped Topology ENNReal NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable {m : ℕ} [NeZero m]
namespace ProjField
variable (m) {K : ℝ}
theorem uniform_X_neg (hk : 1 ≤ K) :
    ∃ C ≥ (0:ℝ), ∀ q : ProjField m, q.Bound K → ∀ s ≥ (0:ℝ), ∀ x : Rn m,
      ‖q.XT (-s) x‖ ≤ C*(1+‖x‖) := by
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hk
  let d : ℝ := (√(2*π))⁻¹
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let C := K*(m*d+1+J m)
  have H := j_nonneg m
  have hm : 0 < (m:ℝ) := m_pos
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro q hq s hs x
  have he := norm_le_mean_error (q.X_int (-s))
    (fun x y => XT_lip' hq x y (-s)) hp.le x
  have hh := hq.X_mean (-s)
  have hw : a (-s) ≤ d := (a_high s hs).trans (phi_bdd s)
  have hb := mul_le_mul_of_nonneg_left hw (show 0 ≤ K*m by positivity)
  apply he.trans
  have hx := norm_nonneg x
  have hv : K*m*d + K*J m+K ≤ C := by dsimp [C]; linarith
  have hc : K ≤ C := by
    dsimp only [C]; nlinarith [mul_nonneg hd hm.le]
  nlinarith

omit [NeZero m] in
theorem norm_IP_integrable (q : ProjField m) (s:ℝ) :
    Integrable (fun g => ⟪q.XT s g,q.Z g⟫) (normal m) := by
  let f := q.XT s
  let b := q.Z
  have hh : PolyBound (fun g => ⟪f g,b g⟫) :=
    PolyBound.of_prod_le (poly_sample q.C q.root (q.shift s)) (PolyBound.clm q.root.toContinuousLinearMap)
      fun g => abs_real_inner_le_norm _ _
  exact hh.gaussian_integrable ((continuous_sample ..).inner q.root.continuous).aestronglyMeasurable

-- split the mixed moment at 4(1+s), exterior small even compared to a (-s)
theorem negative_mean (hk : 1 ≤ K) :
    ∃ C ≥ (0:ℝ), ∀ q : ProjField m, q.Bound K → ∀ s ≥ (0:ℝ),
      q.avH (-s) ≤ C*(1+s)*a (-s) ∧ q.Bt (-s) ≤ C*(1+s) := by
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hk
  obtain ⟨d,hd,hx⟩ := uniform_X_neg m hk
  obtain ⟨c,hc,hc'⟩ := normal_tail m 2
  have hm : 0 < (m:ℝ) := m_pos
  let a0 := √(2*π)*Real.exp 4
  have ha0 : 0 ≤ a0 := by dsimp [a0]; positivity
  let C := 4*K*K+d*K*c*a0/m
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro q hq s hs
  let w := q.XT (-s)
  let t := 4*(1+s)
  let S : Set (Rn m) := {x | t ≤ ‖x‖}
  have hS : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let f := fun x : Rn m => (d*K)*(1+‖x‖)^2
  have hif : Integrable f (normal m) :=
    (integrable_envelope _).const_mul _
  have hI := (q.X_int (-s)).norm
  have hu : (∫ x in S, f x ∂normal m) ≤ d*K*c*a0*a (-s) := by
    have ha : Real.exp (-(t^2)/4) ≤ a0*a (-s) := tail_exp_le_a s hs
    unfold f; rw [integral_const_mul]
    calc
      _ ≤ d*K*(c*Real.exp (-(t^2)/4)) :=
        mul_le_mul_of_nonneg_left (hc' t ht) (by positivity)
      _ ≤ d*K*(c*(a0*a (-s))) := by gcongr
      _ = _ := by ring
  classical
  have he (x:Rn m) : ⟪w x,q.Z x⟫ ≤ K*t * ‖w x‖ + S.indicator f x := by
    have hn := hq.normZ x
    apply (real_inner_le_norm ..).trans
    by_cases h : x ∈ S
    · rw [indicator_of_mem h]
      have hb := hx q hq s hs x
      apply le_trans _ (le_add_of_nonneg_left (by positivity))
      unfold f
      change ‖w x‖ ≤ _ at hb
      have hi := mul_le_mul hb hn (norm_nonneg _) (show 0 ≤ d * (1+‖x‖) by positivity)
      nlinarith [show 0 ≤ d*K*(1+‖x‖) by positivity]
    rw [indicator_of_notMem h,add_zero,mul_comm (K*t)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact hn.trans (mul_le_mul_of_nonneg_left (le_of_not_ge h) hp.le)
  have h₁ : q.avH (-s) ≤ C*(1+s)*a (-s) := by
    rw [q.avH_as_mean_ip,div_le_iff₀ hm]
    have hi : Integrable (fun x => K*t * ‖w x‖) (normal m) := hI.const_mul _
    apply (integral_mono (norm_IP_integrable m q _) (hi.add (hif.indicator hS)) he).trans
    change ∫ x, (K*t * ‖w x‖ + S.indicator f x) ∂normal m ≤ _
    rw [integral_add hi (hif.indicator hS),integral_const_mul,integral_indicator hS]
    have hh := mul_le_mul_of_nonneg_left (hq.X_mean (-s))
      (show 0 ≤ K*t by positivity)
    have hh₂ : 0 ≤ s*(d*K*c*a0*a (-s)) := by
      have ha : 0 < a (-s) := a_pos _
      positivity
    apply (add_le_add hh hu).trans
    dsimp only [C,t]
    field_simp
    nlinarith
  refine ⟨h₁,?_⟩
  have ha := a_pos (-s)
  have h := (mul_Bt_avH q (-s)).trans h₁
  exact le_of_mul_le_mul_left (by simpa only [mul_comm _ (a (-s))] using h) ha

theorem positive_mean (q : ProjField m) (hq : q.Bound K) (s : ℝ) :
    (∫ x, ‖q.YT s x‖ ∂normal m) ≤ K*m*K^2/a s := by
  apply (hq.Y_mean _).trans
  rw [le_div_iff₀ (a_pos s)]
  have h := ((mul_Bt_avH q s).trans (q.avH_le_s s)).trans hq.s0_le
  have he := mul_le_mul_of_nonneg_left h (show 0 ≤ K*m from mul_nonneg hq.positive.le (Nat.cast_nonneg _))
  linarith

-- both bias and samples pointwise at most linear growth
lemma layers_growth (hk : 1 ≤ K) :
    ∃ C ≥ (0:ℝ), ∀ q : ProjField m, q.Bound K → ∀ s,
      ‖q.shift s‖ ≤ C*(1+|s|) := by
  obtain ⟨c,hc,he⟩ := negative_mean m hk
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hk
  have hm : 0 < (m:ℝ) := m_pos
  let b := (√(2*π))⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  let Z := K*m*K^2/a 0
  have ha : 0 < a 0 := a_pos _
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let C := (b+1)*K+(K*m*c+Z)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro q hq s
  let y := ∫ x, q.YT s x ∂normal m
  have hy : ‖y‖ ≤ (K*m*c+Z)*(1+|s|) := by
    apply (norm_integral_le_integral_norm _).trans
    by_cases h : 0 ≤ s
    · apply (positive_mean m q hq _).trans
      have hh : K*m*K^2/a s ≤ Z := by
        unfold Z; gcongr; exact a_mono.monotone h
      have h' : 0 ≤ K*m*c := by positivity
      nlinarith [abs_nonneg s]
    · have hh := (he q hq (-s) (by linarith)).2
      rw [neg_neg] at hh
      apply (hq.Y_mean s).trans
      rw [abs_of_neg (by linarith)]
      have h' := mul_le_mul_of_nonneg_left hh (show 0 ≤ K*m by positivity)
      nlinarith
  have hah : a s ≤ (b+1)*(1+|s|) := by
    have h₁ := p_lt_one s
    have h₂ := p_pos s
    have h₃ : phi s ≤ b := phi_bdd s
    rw [a]
    nlinarith [le_abs_self s, abs_nonneg s]
  have heq : q.shift s = (a s) • q.U - y := by rw [show y = _ from q.Y_mean s]; abel
  rw [heq]; apply (norm_sub_le ..).trans
  rw [norm_smul,Real.norm_eq_abs, abs_of_pos (a_pos _)]
  have h' := mul_le_mul hah hq.Ub (norm_nonneg _) (show 0 ≤ (b+1)*(1+|s|) by positivity)
  dsimp only [C]
  linarith
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Cutoff
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Uniform cutoffs for the biased projections.
We strengthen the negative-tail estimate of the manuscript to an exact
cutoff (in z, depending linearly on |g|); this makes mixed-integrability
statements for the Jacobian fields simpler. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable (m : ℕ) [NeZero m] {K : ℝ}
namespace ProjField

theorem positive_exact (hk : 1 ≤ K) :
    let C := cutoffC m K
    1 ≤ C ∧ ∀ q : ProjField m, q.Bound K → ∀ (s:ℝ) x, C*(1+‖x‖) < s →
      q.Z x + q.shift s ∈ interior (q.C : Set (Rn m)) := by
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hk
  have hm : 0 < (m:ℝ) := m_pos
  let M := K*m*K^2/a 0
  have ha := a_pos 0
  have H : 0 ≤ M := by dsimp [M]; positivity
  let C := 1 + 2*K*(K+M)
  have hc : 1 ≤ C := by unfold C; nlinarith
  refine ⟨hc, fun q hq s x hs => ?_⟩
  change C*(1+‖x‖) < s at hs
  have hs' : 0 ≤ s := by nlinarith [norm_nonneg x]
  let w := ∫ x, q.YT s x ∂normal m
  have he : ‖w‖ ≤ M := calc
    _ ≤ _ := norm_integral_le_integral_norm _
    _ ≤ K*m*K^2/a s := positive_mean m q hq s
    _ ≤ M := by unfold M; gcongr; exact a_mono.monotone hs'
  have hz : q.shift s = a s • q.U - w := by dsimp [w]; rw [q.Y_mean]; abel
  have hw : ‖q.Z x - w‖ ≤ K*‖x‖+M :=
    (norm_sub_le ..).trans (add_le_add (hq.normZ _) he)
  have hb : K*(K*‖x‖+M) < a s := by
    have hh : p 0 ≤ p s := p_mono.monotone hs'
    rw [p_half] at hh
    dsimp only [C] at hs
    have hv : 0 ≤ K*M*‖x‖ := by positivity
    rw [a]; nlinarith [phi_pos s, norm_nonneg x]
  -- apply dual height criterion
  have heq : q.C = posDual q.D := (ProperCone.innerDual_innerDual _).symm
  rw [heq]
  have hid : q.Z x+q.shift s = a s • q.U+(q.Z x-w) := by rw [hz]; abel
  have hb' : 0 < a s/K - ‖q.Z x - w‖ := sub_pos.mpr (lt_div_iff₀ hp |>.mpr (by nlinarith))
  refine interior_dual_of_bound hb' (fun y hy => ?_)
  have h₁ := hq.inC _ hy
  have h₂ := abs_real_inner_le_norm (q.Z x - w) y
  rw [hid,inner_add_left, real_inner_smul_left, sub_mul]
  have hx₁ : a s / K * ‖y‖ ≤ a s * ⟪q.U,y⟫ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    have hi := mul_le_mul_of_nonneg_left h₁ (a_pos s).le
    linarith
  have h₃ := neg_le_of_abs_le h₂
  linarith

theorem positive_cutoff (hk : 1 ≤ K) :
    ∃ C ≥ (1:ℝ), ∀ q : ProjField m, q.Bound K → ∀ (s:ℝ) x, C*(1+‖x‖) < s →
      q.Z x + q.shift s ∈ interior (q.C : Set (Rn m)) :=
  ⟨_,positive_exact m hk⟩

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Rapid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Polynomial growth and rapid layer decay with polynomial loss in
the Gaussian variables. Fubini and moment estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise
namespace GeneralMahler
section
variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem poly_prod_bound {f : X → Y → E}
    (hf : PolyBound f.uncurry) : ∃ (C : ℝ) (m : ℕ), 0≤C ∧ ∀ x y,
    ‖f x y‖ ≤ C*(1+‖x‖)^m*(1+‖y‖)^m := by
  obtain ⟨C,m,hc,h⟩ := hf
  refine ⟨C,m,hc,fun x y => ?_⟩

  rw [mul_assoc, ← mul_pow]
  apply (h (x,y)).trans
  gcongr; change 1 + max ‖x‖ ‖y‖ ≤ _
  rcases max_choice ‖x‖ ‖y‖ with h|h <;> rw [h] <;> nlinarith [norm_nonneg x,norm_nonneg y]

namespace mixed
variable {f g : X → Y → E}

lemma add (hf : mixed f) (hg : mixed g) : mixed fun x y => f x y + g x y := by
  intro n
  obtain ⟨C,m,hc,h⟩ := hf n
  obtain ⟨D,l,hd,h'⟩ := hg n
  refine ⟨C+D,m+l,by positivity,fun x y => ?_⟩
  calc
    _ ≤ (‖f x y‖+‖g x y‖)*(1+‖x‖)^n := by gcongr; apply norm_add_le
    _ ≤ C*(1+‖y‖)^m+D*(1+‖y‖)^l := by rw [add_mul]; exact add_le_add (h x y) (h' x y)
    _ ≤ _ := by rw [add_mul]; gcongr <;> simp

lemma sub (hf : mixed f) (hg : mixed g) :
    mixed fun x y => f x y - g x y := by simpa [sub_eq_add_neg] using hf.add hg.neg

lemma product {G : Type*} [NormedAddCommGroup G]
    {g : X→Y→F} {h : X→Y→G} (hf : mixed f)
    (hg : PolyBound g.uncurry) (he : ∀ x y, ‖h x y‖ ≤ ‖f x y‖*‖g x y‖) : mixed h := by
  obtain ⟨C,m,hc,H⟩ := poly_prod_bound hg
  intro n
  obtain ⟨D,l,hd,H'⟩ := hf (n+m)
  refine ⟨C*D,l+m,by positivity,fun x y => ?_⟩
  calc
    _ ≤ (‖f x y‖*(C*(1+‖x‖)^m*(1+‖y‖)^m))*(1+‖x‖)^n := by
      apply mul_le_mul_of_nonneg_right ((he x y).trans (by gcongr; exact H x y)) (by positivity)
    _ = (‖f x y‖*(1+‖x‖)^(n+m))*(C*(1+‖y‖)^m) := by rw [pow_add]; ring
    _ ≤ (D*(1+‖y‖)^l)*(C*(1+‖y‖)^m) :=
      mul_le_mul_of_nonneg_right (H' x y) (by positivity)
    _ = _ := by rw [pow_add]; ring

-- Polynomial cutoff in layer
lemma of_cutoff (hf : PolyBound f.uncurry)
    {d : Y → ℝ} (hd : PolyBound d) (h : ∀ x y, d y < ‖x‖ → f x y = 0) :
    mixed f := by
  intro n
  obtain ⟨C,m,hc,H⟩ := poly_prod_bound hf
  obtain ⟨D,l,hD,H'⟩ := hd
  use C*(1+D)^(m+n),l*(m+n)+m,by positivity
  intro x y
  rcases lt_or_ge (d y) ‖x‖ with hxy|hxy
  · rw [h _ _ hxy,norm_zero, zero_mul]; positivity
  have hle : 1 + ‖x‖ ≤ (1+D)*(1+‖y‖)^l := by
    have he := H' y
    have hp : 1 ≤ (1+‖y‖)^l := one_le_pow₀ (by simp)
    have hz : d y ≤ ‖d y‖ := le_abs_self _
    linarith
  calc
    _ ≤ (C*(1+‖x‖)^m*(1+‖y‖)^m)*(1+‖x‖)^n :=
        mul_le_mul_of_nonneg_right (H x y) (by positivity)
    _ = C*(1+‖x‖)^(m+n)*(1+‖y‖)^m := by rw [pow_add]; ring
    _ ≤ C*((1+D)*(1+‖y‖)^l)^(m+n)*(1+‖y‖)^m := by gcongr
    _ = _ := by simp only [pow_mul,pow_add,mul_pow]; ring

end mixed

section Integrals
variable [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsAddHaarMeasure μ]

lemma poly_integral_left [NormedSpace ℝ E] {f : X → Y → E}
    (h : mixed f)
    (hf : ∀ y, AEStronglyMeasurable (fun x=>f x y) μ) :
    PolyBound (fun y=>∫ x, f x y ∂μ) := by
  let p := Module.finrank ℝ X+1
  let g := fun x:X => ((1+‖x‖)^p)⁻¹
  obtain ⟨C,l,hc,H⟩ := h p
  have hg : Integrable g μ := envelope_inv_int
  refine ⟨C*(∫ x,g x ∂μ),l, mul_nonneg hc (integral_nonneg (fun x=>by unfold g; positivity)),fun y=>?_⟩
  calc
    _ ≤ ∫ x, ‖f x y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C*(1+‖y‖)^l * g x ∂μ :=
      integral_mono (mixed_integrable_left h y (hf y)).norm (hg.const_mul _) (fun x=>by
        dsimp only [g]; rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
        apply H)
    _ = _ := by rw [integral_const_mul]; ring

end Integrals
end
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MixedField
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer integrals and error estimates. -/
noncomputable section
open Filter Set Real Matrix MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
open Layers
variable {m : ℕ}

lemma mixed_integral_right {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    {f : X → Rn m → F} (h : mixed f) (hm : ∀ x, AEStronglyMeasurable (f x) (normal m)) :
    rapid fun x => ∫ g, f x g ∂normal m := by
  intro n
  obtain ⟨C,k,hc,H⟩ := h n
  let F := fun g:Rn m => C*(1+‖g‖)^k
  have hi : Integrable F (normal m) := (integrable_envelope _).const_mul _
  refine ⟨(∫ g, F g ∂normal m),integral_nonneg (by intro g; dsimp only [F]; positivity), fun x => ?_⟩
  let d := (1+‖x‖)^n
  have hd : 0 < d := by dsimp [d]; positivity
  have he (g : Rn m) : ‖f x g‖ ≤ F g / d := (le_div_iff₀ hd).mpr (H _ _)
  change ‖_‖ * d ≤ _
  apply (le_div_iff₀ hd).mp
  calc
    _ ≤ _ := norm_integral_le_integral_norm _
    _ ≤ ∫ g, F g / d ∂normal m :=
      integral_mono (((hi.div_const _).mono' (hm x) (ae_of_all _ he)).norm) (hi.div_const _) he
    _ = _ := by rw [integral_div]

namespace ProjField
variable (q : ProjField m)

section
variable [NeZero m]

variable (m) in
lemma uniform_Pstep {K : ℝ} (hK : 1 ≤ K) (n : ℕ) :
    ∃ C ≥ (0:ℝ), ∀ q : ProjField m, q.Bound K → ∀ x y,
      ‖q.Pstep x y‖*(1+‖x‖)^n ≤ C*(1+‖y‖)^n := by
  obtain ⟨a,ha,hh⟩ := negative_cutoff m hK
  obtain ⟨b,hb,hi⟩ := positive_cutoff m hK
  let c := a+b
  have hc : 1 ≤ c := by dsimp [c]; linarith
  refine ⟨2*(1+c)^n,by positivity,?_⟩
  intro q hq x y
  by_cases h : ‖x‖ ≤ c*(1+‖y‖)
  · calc
      _ ≤ 2*((1+c)*(1+‖y‖))^n := by
        have hu := q.Pstep_norm x y
        have hv : 1+‖x‖ ≤ (1+c)*(1+‖y‖) := by linarith [norm_nonneg y]
        gcongr
      _ = _ := by rw [mul_pow,mul_assoc]
  · suffices he : q.Pstep x y = 0 by rw [he,norm_zero,zero_mul]; positivity
    unfold Pstep Gstep st; split_ifs with ht
    · have hx : b*(1+‖y‖) < x := by
        rw [Real.norm_of_nonneg ht] at h; dsimp [c] at h
        nlinarith [norm_nonneg y]
      have he : q.Pmat x y = 1 := projJac_id q.C (hi q hq _ y hx)
      rw [he,one_smul,sub_self]
    · have hx : a*(1+‖y‖) < -x := by
        rw [Real.norm_eq_abs,abs_of_neg (lt_of_not_ge ht)] at h; dsimp [c] at h
        nlinarith [norm_nonneg y]
      have he : q.Pmat x y = 0 := projJac_zero q.C (by simpa only [neg_neg] using hh q hq _ _ hx)
      rw [he,zero_smul,sub_zero]

lemma Pstep_mixed : mixed q.Pstep := by
  obtain ⟨k,hk⟩ := Field_isBound q
  intro n
  obtain ⟨c,hc,h⟩ := uniform_Pstep m hk.one_le n
  exact ⟨c,n,hc,h q hk⟩

lemma mixed_PD : mixed q.PD := by
  let f := fun z (_:Rn m) => (p z-st z) • (1:Mat m)
  have H : q.PD = fun z g => f z g - q.Pstep z g := by
    ext z g; simp [f,PD,Pstep,Gstep,sub_smul]
  rw [H]
  have hu : mixed f := (mixed.of_rapid (Y := Rn m) rapid_p).mono (fun x y => by
    dsimp only [f]; rw [norm_smul]; exact mul_le_of_le_one_right (by positivity) one_op_le)
  exact hu.sub q.Pstep_mixed

-- h minus its step decays rapidly
lemma tail_H : rapid (fun z : ℝ => q.avH z - st z * q.s0) := by
  let l : Mat m →L[ℝ] ℝ :=
    trL.comp (ContinuousLinearMap.mul ℝ (Mat m) q.covMat)
  have hl (A : Mat m) : l A = trN (q.covMat*A) := by simp [l]
  have hi (z) : Integrable (q.Pstep z) (normal m) :=
    (meanJac_integrable q.C q.root (q.shift z)).sub (integrable_const _)
  have he (z:ℝ) :
      q.avH z - st z * q.s0 = ∫ g, l (q.Pstep z g) ∂normal m := by
    let P (x : Rn m) := q.Pmat z x
    have hm : Integrable P (normal m) := meanJac_integrable ..
    change _ = ∫ g, l (q.Pstep z g) ∂normal m
    rw [l.integral_comp_comm (hi z)]
    have hh : (∫ g, q.Pstep z g ∂normal m) = meanJac q.C q.root (q.shift z) - Gstep z := by
      change ∫ g, (P g-Gstep z) ∂_ = _
      rw [integral_sub hm (integrable_const _)]
      simp [meanJac,P,Pmat,Z,affineN]
    rw [hh,_root_.map_sub,Gstep,_root_.map_smul,hl,hl]
    simp only [smul_eq_mul,mul_one]; rfl
  rw [show (fun z => _) = _ from funext he]
  have hu : mixed (fun z g => l (q.Pstep z g)) := by
    let f := fun (_:ℝ) (_:Rn m) => ‖l‖
    have hf : PolyBound f.uncurry := PolyBound.const ‖l‖
    exact q.Pstep_mixed.product hf (by
      intro x y
      apply (l.le_opNorm _).trans_eq
      change ‖l‖ * _ = _ * ‖‖l‖‖
      rw [Real.norm_of_nonneg (norm_nonneg l),mul_comm])
  exact mixed_integral_right hu fun x => (l.integrable_comp (hi x)).aestronglyMeasurable
end
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LayerMeasure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02 scalar measure from the derivative of avH. Real densities here. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology ENNReal
namespace GeneralMahler

-- A scalar general lemma about finite moments from fast primitive decay.
lemma weighted_primitive_moments_pos (f g F : ℝ → ℝ)
    (h : ∀ x, HasDerivAt f (g x) x) (hn : ∀ x, 0 ≤ g x)
    (c : ℝ) (hv : rapid F) (hmeas : Measurable F)
    (hf : ∀ x : ℝ, 0 < x → f x-c = F x) (n : ℕ) :
    IntegrableOn (fun x => g x*(1+x)^n) (Ioi 0) := by
  let w := fun x:ℝ => (1+x)^n
  let w' := fun x:ℝ => (n:ℝ)*(1+x)^(n-1)
  have hd (x : ℝ) : HasDerivAt w (w' x) x := by
    have he := ((hasDerivAt_id' x).const_add 1).pow n
    change HasDerivAt ((fun x:ℝ=>1+x)^n) _ x
    simpa only [w,w',mul_one] using he
  let v := fun x:ℝ => (f x-c)*w' x
  let P := fun x:ℝ => (f x - c)*w x - ∫ t in (0:ℝ)..x, v t
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (h x).continuousAt
  have hc' : Continuous v := by unfold v w'; fun_prop
  have hp (x:ℝ) : HasDerivAt P (g x*w x) x := by
    have hb := (((h x).sub_const c).mul (hd x)).sub (intervalIntegral.integral_hasDerivAt_right
      (hc'.intervalIntegrable (0:ℝ) x)
      (hc'.stronglyMeasurableAtFilter volume (𝓝 x)) hc'.continuousAt)
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (unfold v; ring)
  have hw : PolyBound (fun x:ℝ => 1+x) :=
    (PolyBound.const 1).add PolyBound.id
  have hi := (hv.product ((PolyBound.const (n:ℝ)).mul (hw.pow (n-1)))).integrable_real
    (hmeas.mul (by fun_prop))
  have hii : IntegrableOn v (Ioi 0) :=
    hi.integrableOn.congr_fun (by intro x hx; simp [v,w',hf x hx]) measurableSet_Ioi
  have he := intervalIntegral_tendsto_integral_Ioi 0 hii tendsto_id
  have he' : Tendsto (fun x => (f x-c)*w x) atTop (𝓝 0) := by
    apply Tendsto.congr' _ (hv.product (hw.pow n)).tail_limit
    filter_upwards [Ioi_mem_atTop (0:ℝ)] with x hx
    rw [hf x hx]
  apply integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hp x) (fun x hx => ?_) (he'.sub he)
  exact mul_nonneg (hn _) (pow_nonneg (by have ha : 0 < x := hx; linarith) _)

open Layers
variable {m : ℕ} [NeZero m]
namespace ProjField
variable (q : ProjField m)

def layerW (z : ℝ) := p z * q.Bt z + a z * q.r1 z
omit [NeZero m] in
lemma H_deriv (z : ℝ) : HasDerivAt q.avH (q.layerW z) z := q.deriv_avH z
omit [NeZero m] in
lemma H_cont : Continuous q.avH :=
  continuous_iff_continuousAt.mpr fun x => (q.H_deriv x).continuousAt
omit [NeZero m] in
lemma w_cont : Continuous q.layerW :=
  (cp.mul q.Bt_cd.continuous).add (ca.mul q.Bt_cd.continuous_deriv_one.neg)
lemma w_positive (z : ℝ) : 0 < q.layerW z :=
  add_pos_of_nonneg_of_pos (mul_nonneg (p_pos z).le (q.Bt_nonneg z)) (mul_pos (a_pos z) (q.r1_pos z))

theorem w_moment (n : ℕ) :
    Integrable (fun x => q.layerW x * (1+‖x‖)^n) := by
  let f := fun x => q.avH x-st x*q.s0
  have hm : Measurable f := q.H_cont.measurable.sub (measurable_st.mul measurable_const)
  let w := fun x => q.layerW x * (1+‖x‖)^n
  have hp : IntegrableOn w (Ioi 0) := by
    have h := weighted_primitive_moments_pos q.avH q.layerW f q.H_deriv (fun x =>
      (q.w_positive x).le) q.s0 q.tail_H hm (fun x hx => by simp [f,st,hx.le]) n
    exact h.congr_fun (fun x hx => by simp only [w,Real.norm_of_nonneg (mem_Ioi.mp hx).le])
      measurableSet_Ioi
  have hn : IntegrableOn w (Iio 0) := by
    let F := fun x:ℝ => -f (-x)
    have he : rapid F := by
      intro n
      obtain ⟨C,hc,h⟩ := q.tail_H n
      exact ⟨C,hc,fun x=>by simpa only [F,f,norm_neg] using h (-x)⟩
    have h := weighted_primitive_moments_pos (fun x => -q.avH (-x))
      (fun x => q.layerW (-x)) F (fun x => by
        change HasDerivAt (- (q.avH ∘ (fun x => -x))) _ _
        simpa using ((q.H_deriv (-x)).comp x (hasDerivAt_neg' x)).neg) (fun x =>
      (q.w_positive _).le) 0 he (hm.neg.comp measurable_neg)
      (fun x hx => by simp [F,f,st,not_le_of_gt hx]) n
    have h₁ : IntegrableOn (w ∘ (fun t=> -t)) ((fun t : ℝ=> -t) ⁻¹' Iio (0:ℝ)) ↔ IntegrableOn w (Iio 0) :=
      MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
        (Homeomorph.neg ℝ).measurableEmbedding
    apply h₁.mp
    have heq : (fun x : ℝ=> -x) ⁻¹' Iio (0:ℝ) = Ioi 0 := by ext; simp
    rw [heq]
    exact h.congr_fun (by intro x hx; simp [w,abs_of_nonneg (mem_Ioi.mp hx).le])
      measurableSet_Ioi
  have hw : IntegrableOn w (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio (by finiteness)).mpr hn
  have h := hw.union hp
  rw [Iic_union_Ioi,integrableOn_univ] at h; exact h

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MatrixBox
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Spectral boxes and clipping; normalization preparation. -/
noncomputable section
open Set Filter Real Matrix
open scoped Topology ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}

def clip (a b:ℝ) (A : Mat m) := cfc (fun x : ℝ => max a (min x b)) A

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_HMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
### H_f, A, L from Equation (7) and their growth bounds
-/
noncomputable section
open Set Filter Real Matrix MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
open Layers
variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)

def M (i : Fin m) := ∫ x, x i • q.Amat x ∂normal m
def Lmat (x : Rn m) := ∑ i, x i • q.M i
lemma PD_herm (z x) : (q.PD z x).IsHermitian :=
    ((Matrix.isHermitian_one).smul (show IsSelfAdjoint (p z) by simp [IsSelfAdjoint])).sub (q.Pmat_herm _ _)

variable [NeZero m] {f : ℝ→ℝ} (h : PolyBound (deriv f))

lemma H_mixed (h : PolyBound (deriv f)) : mixed (q.kerH f) :=
  q.mixed_PD.product
    (g := fun z (_ : Rn m) => deriv f z)
    (h.comp PolyBound.fst) (fun x y => by
      rw [kerH,norm_smul]; exact le_of_eq (mul_comm ..))

include h in
lemma H_poly : PolyBound (q.Hmat f) :=
  poly_integral_left (q.H_mixed h) (q.H_ams)

include h in
lemma H_left_int (y) : Integrable (fun x => q.kerH f x y) :=
  mixed_integrable_left (q.H_mixed h) y (q.H_ams y)

include h in
lemma H_hermitian (x) : (q.Hmat f x).IsHermitian :=
  hermitian_integral (q.H_left_int h _)
    (ae_of_all _ fun z => (q.PD_herm ..).smul (show IsSelfAdjoint (deriv f z) by simp [IsSelfAdjoint]))

lemma A_poly : PolyBound q.Amat := q.H_poly poly_id_der

lemma A_coord_poly (i : Fin m) : PolyBound (fun x : Rn m => (x i) • q.Amat x) :=
  (PolyBound.clm (coord i)).smul q.A_poly

lemma A_coord_int (i : Fin m) :
    Integrable (fun x : Rn m => x i • q.Amat x) (normal m) := by
  apply (q.A_coord_poly i).gaussian_integrable
  exact (((coord i).continuous.stronglyMeasurable).smul q.A_SM).aestronglyMeasurable

lemma M_sym (i) : (q.M i).IsHermitian :=
  hermitian_integral (q.A_coord_int i) (ae_of_all _ fun z => (q.H_hermitian poly_id_der _).smul (by simp [IsSelfAdjoint]))

omit [NeZero m] in
lemma L_linear : ∃ l : Rn m →L[ℝ] Mat m, (l : Rn m → Mat m) = q.Lmat := by
  classical
  use ∑ i, (coord i).smulRight (q.M i)
  ext x; simp [Lmat]

omit [NeZero m] in
lemma L_poly : PolyBound q.Lmat := by
  obtain ⟨l,hl⟩ := q.L_linear; rw [← hl]; exact PolyBound.clm _

omit [NeZero m] in
lemma L_cont : Continuous q.Lmat := by
  obtain ⟨l,hl⟩ := q.L_linear; rw [← hl]; exact l.continuous

lemma L_sym (x) : (q.Lmat x).IsHermitian :=
  by
    unfold Matrix.IsHermitian Lmat
    rw [conjTranspose_sum]; exact Finset.sum_congr rfl fun i _ => (q.M_sym i).smul (by simp [IsSelfAdjoint])

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ParamA
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02: continuity of layer expectations in normalization parameters. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ} [NeZero m] (l : Rn m →L[ℝ] ℝ) (c : ℝ)
namespace ProjField

variable (q : ProjField m)

def aun (z : ℝ) (x : Rn m) := (c+l x) • q.PD z x
def da (z : ℝ) := ∫ x,q.aun l c z x ∂normal m


end ProjField

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Angle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Inward normalization estimate: layer as seen in a unit direction. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ} [NeZero m]
namespace ProjField
variable (q : ProjField m) (v : Rn m)
def dimH (z : ℝ) : ℝ := ∫ x, ⟪v,op (q.Pmat z x) v⟫ ∂normal m

def vp := q.root.symm v

def plus := ∫ z in Ici (0:ℝ), (1-q.dimH v z)
def minus := ∫ z in Iio (0:ℝ), q.dimH v z

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Update
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02 covariance equation from scalar inequalities of §01. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler

variable {m : ℕ}

def updEq (C K T : Mat m) := lam • (T*T)+ jprod C T + K
def updGap (C T : Mat m) := -C-(2*lam) • T

namespace ProjField
variable [NeZero m]

def expL (f : ℝ→ℝ) (q : ProjField m) :=
  ∫ x, cfc f (q.Lmat x) ∂normal m

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Edge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Deterministic-endcut layer of PSD contractions. Carries the
precise data needed for log-Jacobian estimate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ}

variable [NeZero m]
namespace ProjField
variable (q:ProjField m)
lemma Field_tend :
    ∃ c≥(1:ℝ), (∀ z x,c*(1+‖x‖)<z → q.Pmat z x=1) ∧
      (∀ z x,c*(1+‖x‖)< -z → q.Pmat z x=0) := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  obtain ⟨a,ha,h⟩ := positive_cutoff m hk.one_le
  obtain ⟨b,hb,h'⟩ := negative_cutoff m hk.one_le
  refine ⟨max a b,ha.trans (le_max_left ..),?_,?_⟩
  · intro z x hx; apply projJac_id q.C (h _ hk _ x ?_)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)) hx
  intro z x hx
  have hi := h' q hk (-z) x (lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)) hx)
  rw [neg_neg] at hi
  exact projJac_zero q.C hi

def edge : Edge m where
  P := q.Pmat
  psd := q.Pmat_psd
  le_one := q.Pmat_le
  meas :=
    ((strongly_projJac q.C).comp_measurable
      ((q.root.continuous.comp continuous_snd).add (q.shift_cd.continuous.comp continuous_fst)).measurable).measurable
  C := q.Field_tend.choose
  hp := q.Field_tend.choose_spec.1
  tend_pos := q.Field_tend.choose_spec.2.1
  tend_neg := q.Field_tend.choose_spec.2.2
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scatter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! The cone-valued maps in the entropy bound. Use cutoffs proven earlier
to get pointwise spatially local Lipschitz control; this allows applying the
injective-area formula directly on a conull set. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ}

structure Scatter (m:ℕ) extends Edge m where
  cone : ProperCone ℝ (Rn m)
  B : Mat m
  inj : Function.Injective (op B)
  d : ℝ→Rn m
  dp : PolyBound d
  dc : Continuous d
  M : ℝ
  hm : 1≤M
  in_cone : ∀ (z:ℝ) x,M*(1+‖x‖)<z → op B x + d z ∈ cone
  opp : ∀ (z:ℝ) x,M*(1+‖x‖)< -z → -(op B x + d z) ∈ posDual cone
  diff : ∀ᵐ x:Rn m,∀ᵐ z:ℝ,
    HasFDerivAt (fun x=>coneProj cone (op B x+d z)) ((op (P z x)).comp (op B)) x

namespace Scatter
variable (q:Scatter m)
def y (z:ℝ) (x:Rn m) := coneProj q.cone (op q.B x+q.d z)
lemma zero_y (z x) (hz:q.M*(1+‖x‖)< -z) : q.y z x=0 :=
  proj_zero_of_dual _ _ (q.opp z x hz)

def ky (z:ℝ) (x:Rn m) := MillsW z • q.y z x

def t (x:Rn m) := ∫ z,q.ky z x

def TJ (x:Rn m) := q.toEdge.Jedge x * q.B

end Scatter
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ScatterField
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Two projection maps implementing Scatter. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Metric Real
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
lemma s_poly : PolyBound q.shift := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  obtain ⟨C,hC,h⟩ := layers_growth m hk.one_le
  refine ⟨C,1,hC,fun z=>?_⟩
  simpa using h q hk z
lemma loc_ends :
    ∃ M≥(1:ℝ), (∀ z x, M*(1+‖x‖)<z → op q.S x + q.shift z ∈ q.C) ∧
      (∀ z x, M*(1+‖x‖)< -z → -(op q.S x+q.shift z) ∈ q.D) := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  obtain ⟨a,ha,h⟩ := positive_cutoff m hk.one_le
  obtain ⟨b,hb,h'⟩ := negative_cutoff m hk.one_le
  refine ⟨max a b, ha.trans (le_max_left ..),fun z x hx=>?_,fun z x hx=>?_⟩
  · rw [← Z_def]; apply interior_subset
    exact h q hk z x (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left ..)
      (by positivity)) hx)
  rw [← Z_def]; apply interior_subset
  have hi := h' q hk (-z) x (lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)) hx)
  rwa [neg_neg] at hi

omit [NeZero m] in
lemma xt_d :
    ∀ᵐ x:Rn m,∀ᵐ z:ℝ,HasFDerivAt (q.XT z) ((op (q.Pmat z x)).comp (op q.S)) x := by
  let F (p:ℝ×Rn m) := affineN q.root (q.shift p.1) p.2
  let S := {x| DifferentiableAt ℝ (coneProj q.C) x}
  have hm : MeasurableSet (F⁻¹' S) :=
    (measurableSet_of_differentiableAt ..).preimage
      (((q.root.continuous.comp continuous_snd).add
        (q.shift_cd.continuous.comp continuous_fst)).measurable)
  have ha : ∀ᵐ x:Rn m,x∈S := (coneProj_lip q.C).ae_differentiableAt
  have he : ∀ᵐ z:ℝ,∀ᵐ x ∂normal m,(z,x)∈F⁻¹' S :=
    ae_of_all _ fun z=> (tendsto_ae_affineN q.root (q.shift z)).eventually ha
  have hi : ∀ᵐ x ∂normal m, ∀ᵐ z:ℝ,(z,x)∈F⁻¹' S := by
    rw [← ae_prod_mem_iff_ae_ae_mem] at he
    · have ha : ∀ᵐ p∂(normal m).prod (volume : Measure ℝ), p.swap∈F⁻¹' S :=
        measurePreserving_swap.quasiMeasurePreserving.tendsto_ae.eventually he
      exact ae_ae_of_ae_prod ha
    exact hm
  apply ac_normal.ae_le
  filter_upwards [hi] with x hx
  filter_upwards [hx] with z hz
  change DifferentiableAt ℝ (coneProj q.C) (affineN q.root (q.shift z) x) at hz
  have hu := hz.hasFDerivAt.comp x
    (q.root.hasFDerivAt.add_const (q.shift z))
  simp only [XT,Pmat,projJac_op]
  rw [← q.matrix_eq]
  exact hu
omit [NeZero m] in
lemma S_inj : Function.Injective (op q.S) := by rw [← q.matrix_eq]; apply q.root.injective
def primalMap : Scatter m where
  toEdge := q.edge
  cone := q.C
  B := q.S
  inj := q.S_inj
  d := q.shift
  dp := q.s_poly
  dc := q.shift_cd.continuous
  M := q.loc_ends.choose
  hm := q.loc_ends.choose_spec.1
  in_cone := q.loc_ends.choose_spec.2.1
  opp := q.loc_ends.choose_spec.2.2
  diff := by
    have h (z:ℝ) : (fun x=>coneProj q.C (op q.S x+q.shift z))=q.XT z := by
      ext x; rw [← q.Z_def]; rfl
    simp_rw [h]; exact q.xt_d

def dualMap : Scatter m where
  toEdge := q.edge.ref
  cone := q.D
  B := -q.S
  inj := by
    rw [_root_.map_neg]
    intro x y h
    exact q.S_inj (neg_injective h)
  d := fun z=> - q.shift (-z)
  dp := (q.s_poly.comp PolyBound.id.neg).neg
  dc := (q.shift_cd.continuous.comp continuous_neg).neg
  M := q.loc_ends.choose
  hm := q.loc_ends.choose_spec.1
  in_cone := by
    intro z x hz
    rw [_root_.map_neg]
    convert q.loc_ends.choose_spec.2.2 (-z) x (by simpa using hz)
    simp [add_comm]
  opp := by
    intro z x hz
    rw [show posDual q.D = q.C from ProperCone.innerDual_innerDual _,_root_.map_neg]
    convert q.loc_ends.choose_spec.2.1 (-z) x hz
    simp [add_comm]
  diff := by
    filter_upwards [q.xt_d] with x hx
    have hh := (measurePreserving_neg volume).quasiMeasurePreserving.tendsto_ae.eventually hx
    filter_upwards [hh] with z hz
    change HasFDerivAt (q.XT (-z)) ((op (q.Pmat (-z) x)).comp (op q.S)) x at hz
    have hf := hz.sub ((op q.S).hasFDerivAt.add_const (q.shift (-z)))
    have he : (fun y=> coneProj q.D (op (-q.S) y+ - q.shift (-z))) =
        q.XT (-z) - (fun y=>op q.S y+q.shift (-z)) := by
      funext y
      change coneProj q.D (op (-q.S) y + -_) = q.XT _ y - (op q.S y+q.shift (-z))
      rw [_root_.map_neg,_root_.neg_apply]
      rw [show - (op q.S y) + - q.shift (-z) = -(op q.S y + q.shift (-z)) by abel]
      rw [proj_moreau]
      rw [← q.Z_def]; rfl
    have hv : (op (1-q.Pmat (-z) x)).comp (op (-q.S)) =
        (op (q.Pmat (-z) x)).comp (op q.S) - op q.S := by
      change op (1-q.Pmat (-z) x)*op (-q.S)=op (q.Pmat (-z) x)*op q.S-op q.S
      have hi : (1-q.Pmat (-z) x)*(-q.S)= (q.Pmat (-z) x)*q.S-q.S := by noncomm_ring
      calc
        _ = op ((1-q.Pmat (-z) x)* (-q.S)) := Eq.symm (_root_.map_mul ..)
        _ = _ := by rw [hi,_root_.map_sub,_root_.map_mul]
    change HasFDerivAt (fun y=>coneProj q.D (op (-q.S) y+ - q.shift (-z)))
      ((op (1-q.Pmat (-z) x)).comp (op (-q.S))) x
    rw [he,hv]; exact hf

lemma Y_sc (z:ℝ) : q.dualMap.y z=q.YT (-z) := by
  ext x
  unfold Scatter.y dualMap YT
  dsimp
  rw [_root_.map_neg]
  simp [q.Z_def,add_comm]
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_DefectLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! μ functionals and integrable density algebra for Section §03-04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Metric Real
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile

lemma poly_st : PolyBound st := PolyBound.of_bound 1 fun x=> by unfold st; split <;> simp
lemma rapid_ar : rapid fun x=> a (-x)*st x := by
  apply rapid_phi.mono
  intro x
  unfold st; split_ifs with h
  · rw [mul_one,Real.norm_of_nonneg (a_pos _).le,
      Real.norm_of_nonneg (phi_pos _).le]; exact a_high x h
  simp

variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)

-- deltas
def dB (x:ℝ) := q.Bt x-q.s0*a (-x)
def dr (x:ℝ) := q.r1 x-q.s0*(1-p x)
def hDel (x:ℝ) := q.avH x-q.s0*p x
def dm (x:ℝ) := q.layerW x-q.s0*phi x
def delt (j:ℝ→ℝ) :=
  -(∫ x, (2*p x*q.dB x*j x + (p x*q.dr x+q.hDel x)*(2*x*j x-deriv j x)))

lemma Bt_poly : PolyBound q.Bt := by
  have he : q.Bt = fun z=> ((m:ℝ)⁻¹)*⟪q.U,a z • q.U-q.shift z⟫ := by
    ext x; rw [Bt,q.Y_mean]; ring
  rw [he]
  let l := innerSL ℝ q.U
  exact (PolyBound.const _).mul ((PolyBound.clm (show Rn m→L[ℝ]ℝ from l)).comp
    ((poly_a.smul (PolyBound.const _)).sub q.s_poly))

lemma B_tail : rapid fun z=> q.Bt z* st z := by
  let f := fun z x=> st z • q.YT z x
  let v := q.dualMap
  have hy : PolyBound q.YT.uncurry := by
    change PolyBound (fun u:ℝ×Rn m=>coneProj q.D (-(q.Z u.2+q.shift u.1)))
    have hp : PolyBound (fun u:ℝ×Rn m=> -(q.Z u.2+q.shift u.1)) :=
      (((PolyBound.clm q.root.toContinuousLinearMap).comp PolyBound.snd).add
        (q.s_poly.comp PolyBound.fst)).neg
    exact (PolyBound.lipschitz (coneProj_lip q.D)).comp hp
  have hh : mixed f := by
    apply mixed.of_cutoff (show PolyBound f.uncurry from
      (poly_st.comp PolyBound.fst).smul hy)
      (show PolyBound (fun x:Rn m=>v.M*(1+‖x‖)) from
        (PolyBound.const _).mul ((PolyBound.const _).add PolyBound.id.norm))
    intro z x hz
    unfold f st; split_ifs with h
    · rw [Real.norm_of_nonneg h] at hz
      have hi := v.zero_y (-z) x (by simpa using hz)
      rw [show v.y (-z)= _ from q.Y_sc (-z),neg_neg] at hi
      simp only [hi,smul_zero]
    simp
  let l := ((m:ℝ)⁻¹) • (innerSL ℝ q.U)
  have hl (x:Rn m) : l x=⟪q.U,x⟫/(m:ℝ) := by unfold l; simp [div_eq_inv_mul]
  have hi (z:ℝ) : Integrable (f z) (normal m) := (q.Y_int z).smul (st z)
  have he : (fun z=> q.Bt z*st z) = fun z=> ∫ x,l (f z x) ∂normal m := by
    ext z
    rw [l.integral_comp_comm (hi _)]
    unfold f; rw [integral_smul,_root_.map_smul,hl,Bt]
    rw [smul_eq_mul,mul_comm]
  rw [he]
  apply mixed_integral_right _ fun z=>(l.integrable_comp (hi z)).aestronglyMeasurable
  let c := fun (_:ℝ) (_:Rn m)=> ‖l‖
  apply hh.product (show PolyBound c.uncurry from PolyBound.const _)
  intro x y
  apply (l.le_opNorm _).trans
  change ‖l‖*_ ≤ _*‖‖l‖‖
  rw [Real.norm_of_nonneg (norm_nonneg l),mul_comm]

lemma moment_w : MomentF q.layerW := by
  intro f hm h
  obtain ⟨C,n,hc,h⟩ := h
  apply ((q.w_moment n).mul_const C).mono' (q.w_cont.measurable.mul hm).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Pi.mul_apply,norm_mul,Real.norm_of_nonneg (q.w_positive x).le]
  apply le_trans (mul_le_mul_of_nonneg_left (h x) (q.w_positive x).le)
  exact le_of_eq (by ring)
lemma a0_id (x:ℝ) : p x*a (-x)+a x*(1-p x)=phi x := by
  simp only [a,neg_phi,neg_p]; ring
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_DefectIBP
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar layer δ integration identities (including Eq 12). -/
noncomputable section
open MeasureTheory Filter Set Real Metric
open scoped Topology ENNReal NNReal
namespace GeneralMahler
open Profile Layers
variable {m:ℕ}
namespace ProjField
variable (q:ProjField m)
def pb (x:ℝ) := p x*q.dB x
def ab (x:ℝ) := a x*q.dB x
def rk (x:ℝ) := p x*q.dr x+q.hDel x
lemma Bt_d (x:ℝ) : HasDerivAt q.Bt (-q.r1 x) x := by
  have h := (q.Bt_cd.differentiable (by norm_num)).differentiableAt (x:=x)
  simp only [r1,neg_neg]; exact h.hasDerivAt
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EntropyMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Change of variables/Jensen for the projection scatter map. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Matrix Real
open scoped NNReal ENNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]

namespace Scatter
variable (q:Scatter m) (v:Rn m)
def cost := ∫ x,⟪v,q.t x⟫ ∂normal m

end Scatter
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EntScalar
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Entropy scalar simplification. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped NNReal ENNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers Profile

variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
def cBy := ∫ x,MillsW (-x)*q.Bt x

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_GainFinal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Combine the log-gains of the two matrices. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ} [NeZero m]
-- trace-and-expectation paper notation
def et (A: Rn m→Mat m) := ∫ x,trN (A x) ∂normal m
def etw (B:Mat m) (A:Rn m→Mat m) := et fun x=> B*A x

def eGain (e:Edge m) := ∫ x,logD (e.Jedge x) ∂normal m
def surplus (e:Edge m) := ∫ x,(∫ z,e.beta x z) ∂normal m

def eNt (e:Edge m) := ∫ u:Plane,∫ x,e.nt0 u x ∂normal m
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_GradientLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! The centered fields W_f from §02,04. We use coefficient
derivatives (Hermite) as justified by differentiation by parts:
rather than interchanging weak derivatives, integrate the coefficient
identity using the layer cutoff bounds. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
def Xb (z:ℝ) (x:Rn m) := (1-st z) • q.XT z x
def Yb (z:ℝ) (x:Rn m) := st z • q.YT z x

def WW (z:ℝ) (x:Rn m) :=
  p z • q.Z x-q.XT z x + a z • q.U

def WK (f:ℝ→ℝ) (z:ℝ) (x:Rn m) := deriv f z • q.WW z x
def WH (f:ℝ→ℝ) (x:Rn m) := ∫ z,q.WK f z x

def act (i:Fin m) : Mat m→L[ℝ]Rn m :=
  (ContinuousLinearMap.apply ℝ (Rn m) (op q.S (HMode.e i))).comp opCLE.toContinuousLinearMap
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_CovHerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Eq13 coefficient-pair (weighted K multiplier via coefficients). -/
noncomputable section
open Set Filter Metric MeasureTheory MeasureTheory.Measure Matrix Real
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

def Pt (B:Mat m) (A C:Rn m→Mat m) := ∫ x,Pj B (A x) (C x) ∂normal m

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Kernel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Kernel integrations for §04. Plane is Euclidean pair (with product
volume), split along diagonal. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile

def Rlo : Set Plane := {u|u.1 < u.2}

-- One-dimensional with right/left densities r=r1 or q0. Base p/a fixed.
structure rightLayer where
  r : ℝ→ℝ
  B : ℝ→ℝ
  hr : ∀ x,0 ≤ r x
  hc : Continuous r
  drB : ∀ x,HasDerivAt B (-r x) x
  hb : rapid (fun x=>B x*st x)
  poly : PolyBound B
  hw : MomentF fun x=>p x*B x+a x*r x

namespace rightLayer
variable (q:rightLayer)
def Km (x:Plane) := p (min x.1 x.2)*q.r (max x.1 x.2)
def mrg (x:ℝ) := p x*q.B x+a x*q.r x

def Q (f j:ℝ→ℝ) := ∫ u:Plane,q.Km u*(f u.1*j u.2)

end rightLayer
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Indicator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! p-to-indicator score and layer integration formulas. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile
def score (z y:ℝ) := p z-jump z y

def ss (f:ℝ→ℝ) (z y:ℝ) := score z y * deriv f z

variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
def Hcov (u:Plane) := q.s0*p u.1*p u.2 - p u.1*q.avH u.2 - q.avH u.1*p u.2+
  q.avH (min u.1 u.2)
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Threshold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Thresholds of arbitrary moderate-growth random Hermitian fields
(in particular A and L) §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}
namespace ProjField
variable [NeZero m] (q:ProjField m)
def FA : FieldMat m where
  A := q.Amat
  sym := q.H_hermitian poly_id_der
  hM := q.A_SM
  poly := q.A_poly
def FL : FieldMat m where
  A := q.Lmat
  sym := q.L_sym
  hM := q.L_cont.stronglyMeasurable
  poly := q.L_poly
end ProjField

namespace ProjField
variable [NeZero m] (q:ProjField m) (B:FieldMat m)
def EZ (z:ℝ) (x:Rn m) := q.Pmat z x-B.Θ z x

def zE (f:ℝ→ℝ) (z:ℝ) (x:Rn m) := deriv f z • q.EZ B z x

def MB (f:ℝ→ℝ) (x:Rn m) := q.Hmat f x-B.eval f x+scalar m (ga f)

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Beta
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §04 Eq15, threshold comparison. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

namespace ProjField
variable [NeZero m] (q:ProjField m) (B:FieldMat m) (W:Mat m)
def betaK (f j:ℝ→ℝ) (z:ℝ) (x:Rn m) := Pj W (q.zE B f z x) (B.eVal j z x)
def be (f j:ℝ→ℝ) := ∫ x,(∫ z,q.betaK B W f j z x) ∂normal m
def nTK (f j:ℝ→ℝ) (u:Plane) (x:Rn m) := deriv f u.1 * deriv j u.2 * trN (W*q.edge.NTm u x)
def Nt (f j:ℝ→ℝ) := ∫ x,(∫ u:Plane,q.nTK W f j u x) ∂normal m

def RadiusE (x:Rn m) := q.edge.radius x + ‖B.A x‖

def crossK (f j:ℝ→ℝ) (u:Plane) (x:Rn m) :=
  Pj W (q.zE B f u.1 x) (deriv j u.2 • B.EC u x)
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Compare
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer evaluation comparisons (16). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)
def BDiff (f:ℝ→ℝ) (x:Rn m) := B.eval f x-scalar m (ga f)
def LDel (f:ℝ→ℝ) := etw W (BDiff B f)
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MatrixDeriv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Derivative of spectral function of linear field. Avoid polynomial
approximation by exact secant identity and Borel frame compactness. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Asymptotics
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m)
def ell : Rn m→L[ℝ] Mat m := q.L_linear.choose
def Ld (x:Rn m) (f:ℝ→ℝ) : Rn m→L[ℝ]Mat m :=
  let u := q.FL.Fr x
  (u.DL u (q.Lmat x) (q.Lmat x) (bav (deriv f))).comp q.ell

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_BiWeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer functional ℒ and polynomial-growth calculus. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers

def bInt (g:Plane→ℝ) (u:Plane) := ∫ y in u.1..u.2,g (u.1,y)
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Segment
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar exterior and middle estimates via Cauchy--Schwarz. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace Interval
namespace GeneralMahler.Seg
open Roots Layers

def Om (f:Plane→ℝ) (x y z:ℝ) :=
  (|x-z| *bAv f (z,x)+|y-z| *bAv f (z,y))/2
def kz (f:Plane→ℝ) (x y z:ℝ) :=
  ((x-z)*bAv f (z,x)+(y-z)*bAv f (z,y)-rcoef x y z*(bAv f (z,x)+bAv f (z,y)))/2

end GeneralMahler.Seg

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LFun
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! ℒ evaluation; linearity and spectral form. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)
def lk (f:Plane→ℝ) (z:ℝ) (x:Rn m) :=
  Pj W (q.EZ B z x) (B.bmat (bInt f) z x)
def LLw (f:Plane→ℝ) :=
  ∫ x,(∫ z,q.lk B W f z x) ∂normal m

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Blocks
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Algebra of the positive layer blocks (with no commutation
assumptions). All entries here are in a fixed spectral frame. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Seg Roots Layers Profile
variable {m:ℕ}
def ipN (A B:Mat m) := trN (A*star B)

-- entries in frame of A, eigenvalues x_i
structure block (m:ℕ) where
  x : Fin m→ℝ
  z : ℝ
  P : Mat m
  hp : 0≤P
  hi : P≤1

namespace block
variable (b:block m)
def E : Mat m := b.P-Matrix.diagonal (fun i=>jump b.z (b.x i))
def L (i:Fin m) := signE (b.x i) b.z
def a (i:Fin m) := |b.x i-b.z|
def S : Mat m := Matrix.of fun i j=>rcoef (b.x i) (b.x j) b.z*b.E i j

end block
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Qprimitive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Eq13 mixed derivative kernel, proof via rectangle cumulative
representation of a(min)B(max). -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile
namespace rightLayer
variable (q:rightLayer)

def Kab (u:Plane) := a (min u.1 u.2)*q.B (max u.1 u.2)

def Rect (u:Plane) : Set Plane := (Icc u.1 u.2) ×ˢ Icc u.1 u.2

open Classical in
def RectF (f:Plane→ℝ) (p:Plane×Plane) := if p.2∈Rect p.1 then q.Km p.1*f p.2 else 0

end rightLayer
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Contact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer covariances and scalar contact term. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}
namespace ProjField
variable (q:ProjField m)
def Lr [NeZero m] : rightLayer where
  r := q.r1
  B := q.Bt
  hr := fun x=>(q.r1_pos x).le
  hc := q.Bt_cd.continuous_deriv_one.neg
  drB := q.Bt_d
  hb := q.B_tail
  poly := q.Bt_poly
  hw := q.moment_w

def ct (u:Plane) := (∫ x,⟪q.XT (min u.1 u.2) x,q.YT (max u.1 u.2) x⟫ ∂normal m)/(m:ℝ)
def Ct (f j:ℝ→ℝ) := ∫ u:Plane,q.ct u*(deriv f u.1*deriv j u.2)

-- local notation centered pairing with normalized inner product
def ipt (f g:Rn m→Rn m) := (∫ x,⟪f x,g x⟫ ∂normal m)/(m:ℝ)

def Xcenter (z:ℝ) (x:Rn m) := q.XT z x-a z • q.U

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Variation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Inverse-kernel and variation identity Eq14. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler
open Profile Layers

namespace rightLayer
lemma std_hb : rapid fun x=> a (-x)*st x := rapid_ar
lemma Qpos_id (x:ℝ) : p x*a (-x)+a x*p (-x)=phi x := by
  rw [neg_p]; exact ProjField.a0_id _

def stdL : rightLayer where
  r := fun x=>p (-x)
  B := fun x=>a (-x)
  hr := fun x=> (p_pos _).le
  hc := cp.comp continuous_neg
  drB := fun x=> by
    convert (d_a (-x)).comp x (hasDerivAt_neg' x) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | ring
  hb := std_hb
  poly := poly_a.comp PolyBound.id.neg
  hw := by
    simp_rw [Qpos_id]; exact MomentF.of_rapid rapid_phi c_phi.measurable

variable (q:rightLayer)

def variationK (r:ℝ→ℝ) (b c:ℝ→ℝ) (x:ℝ) :=
  (a x*r x)*(Nr b x*c x) - (p x*r x)*(Nr b x*deriv c x)
end rightLayer
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Forms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Forms on the Hermite coefficients. D and sigma in paper §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}

namespace ProjField
variable [NeZero m] (q:ProjField m)
def DLMat (l:ℝ→ℝ) (x:Rn m) (i:Fin m) := fderiv ℝ (q.FL.eval (pl l)) x (e i)
def dirF (W:Mat m) (l:ℝ→ℝ) := ∑ i:Fin m,
  Pt W (fun x=>q.DLMat l x i) (fun x=>q.DLMat l x i)

def DD (l:ℝ→ℝ) (a:MI m) := kMode a • cof (q.Hmat (fl l)) a-cof (q.FL.eval (pl l)) a
def Dterm (l:ℝ→ℝ) (a:MI m) := (1+(deg a:ℝ))*Pj q.covMat (q.DD l a) (q.DD l a)
def Dnorm (l:ℝ→ℝ) := ∑' a:MI m,q.Dterm l a

def RR (x:Rn m) := q.Amat x-q.Lmat x
def sigterm (l:ℝ→ℝ) (a:MI m) := Pj q.covMat (cof q.RR a) (q.DD l a)
def sigma (l:ℝ→ℝ) := 2 * ∑' a,q.sigterm l a

def Jtest (W:Mat m) (l:ℝ→ℝ) :=
  etw W (fun x=> q.Lmat x*q.FL.eval (pl (fun z=>l z^2)) x)-q.dirF W l
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ScalarForm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Integrating functionals; ext modulo constants. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ} [NeZero m]
-- simple contractions
namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)
def Iw (f:ℝ→ℝ) := ∫ x,q.layerW x*f x
def Idw (f:ℝ→ℝ) := ∫ x,q.dm x*f x

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Eq18
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Eq18 with fixed profiles. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m)
def JVec (W:Mat m) := q.Jtest W uc+q.Jtest W us+q.Jtest W qu
def DVec := q.Dnorm uc+q.Dnorm us+q.Dnorm qu
def DelP (T:Mat m) := LDel q.FL 1 (ps d) + LDel q.FL T (fun x=>ps d x-v x)

def Hpart (l:ℝ→ℝ) (u:Plane) := 2*(deriv (fl l) u.1*deriv (pl l) u.2)
def Hp0 (u:Plane) :=
  2*(deriv (fun x:ℝ=>x) u.1*deriv (pl FF) u.2) + deriv (fl FF) u.1*deriv (fun x=>x) u.2
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Parity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Parity of Gaussian fields and coefficient projections. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

namespace ProjField
variable (q:ProjField m)
variable [NeZero m]

def Ro (x:Rn m) := (1/2:ℝ) • (q.RR x-q.RR (-x))
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Eq19
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Budgets on remainder by Hermite degree. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers HMode Profile
variable {m:ℕ} [NeZero m]

def bmp : ℝ := bm/(1+tmax)
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Extract
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Frame decomposition of layer functionals. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ}

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)
def BL (x:Rn m) (z:ℝ) : block m where
  x := B.ev x
  z := z
  P := (B.Fr x).loc (q.Pmat z x)
  hp := (B.Fr x).loc_psd (q.Pmat_psd ..)
  hi := by
    have h := (B.Fr x).loc_le (q.Pmat_le z x)
    rwa [Frm.loc_one] at h

def bmZ (f:Plane→ℝ) (z:ℝ) (x:Rn m) :=
  Pj 1 (q.EZ B z x) (B.bmat (linW f) z x)
def BB (f:Plane→ℝ) := ∫ x,(∫ z,q.bmZ B f z x) ∂normal m

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Penalty
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Constant-layer penalty and commutator remainder accounting. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)
def NK (T:Mat m) := q.Nt T (fun x=>x) (fun x=>x)
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Eq23
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §05 reduction to matrix functionals on linear field. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (T:Mat m)

def scoreE := q.delt d-etw T (q.Hmat v)+(trN T-logD q.covMat)-q.NK 1/8

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_SpectralIBP
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 Gaussian spectral averaging functional. Eq24 in normalized trace pairing. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}

namespace ProjField
variable [NeZero m] (q:ProjField m) (W:Mat m)
def sumS : Mat m := ∑ i:Fin m,q.M i*q.M i
def locR (l:Fin m) (f:ℝ→ℝ) (x:Rn m) :=
  Pj W (q.M l) (q.DLMat f x l) -
    Pj W (q.M l*q.M l) (q.FL.eval f x)
def RM (f:ℝ→ℝ) :=
  ∑ l:Fin m,∫ x,q.locR W l f x ∂normal m

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Nu
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Positive endpoint functional Nu. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Segment
variable {m:ℕ}
namespace ProjField
open LPt
variable [NeZero m] (q:ProjField m)
def nupt (i:Fin m) (x:Rn m) : (Plane→ℝ)→ℝ :=
  npt ((q.FL.Fr x).loc (q.M i)) (q.FL.ev x)
def nu (f:Plane→ℝ) :=
  ∑ i:Fin m,(∫ x,q.nupt i x f ∂normal m)

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Eq26
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 weighted Dirichlet inequality. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open LPt HMode Profile Layers Segment
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (W:Mat m)
def locJ (i:Fin m) (f:ℝ→ℝ) (x:Rn m) :=
  Pj W (q.M i) (q.DLMat (fun x=>f x^2) x i)-Pj W (q.DLMat f x i) (q.DLMat f x i)
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Eq27
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 final commutator comparison. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open LPt Profile HMode Segment Layers
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
def cmbf (x:ℝ) := Kp x+tc*Cp x
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Final
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 final inequalities before rigidity. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open HMode Profile Segment Layers
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m) (T:Mat m)

def Bgap (u:Plane) := ww u-ww0 u

-- normal form after covariance updates
structure Balanced : Prop where
  ht:T∈specBox m tmin tmax
  cov : 1+T=q.covMat
  eqn : updEq (q.expL Cp) (q.expL Kp) T=0
  avg : q.avgA=0
  gap : scalar m mstar ≤ updGap (q.expL Cp) T

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Rigid_Basis
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Joint eigenbasis and transfer of diagonality to projection.
Allows a nonorthogonal eigenbasis too. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Function
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]

def diagDeriv (C: ProperCone ℝ (Rn m)) (b:Basis (Fin m) ℝ (Rn m)) :=
  ∀ᵐ x:Rn m,∀ j:Fin m,∃ l:ℝ, fderiv ℝ (coneProj C) x (b j) = l • b j

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_SimplexCone
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.opCLE_apply _root_.OAI.GeneralMahler.opCLE_symm_apply _root_.OAI.GeneralMahler.opPair_apply _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! §§01,06: Full-dimensional simplicial cones and simplex sections. -/
noncomputable section
open Set Module
open scoped RealInnerProductSpace ENNReal Topology
namespace GeneralMahler
variable {n : ℕ}

-- two projection maps for finite linear combinations
def hgtL : LiftSpace n →ₗ[ℝ] ℝ where
  toFun := hgt
  map_add' := hgt_add
  map_smul' := hgt_smul
def horizL : LiftSpace n →ₗ[ℝ] Rn n where
  toFun := horiz
  map_add' := horiz_add
  map_smul' := horiz_smul
@[simp] theorem hgtL_apply (x) : @hgtL n x = hgt x := rfl
@[simp] theorem horizL_apply (x) : @horizL n x = horiz x := rfl

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_HBox
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Jet.instZeroIV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
open Cert Cert.IV Finset

def cB (i j:Nat):IV:=IV.c (Int.ofNat ((i+j).choose j))

def bsumH (U:IV) (i:Nat): ℕ→ IV×IV
  | 0=>(1,0)
  | n+1=>
    let (a,b):=bsumH U i n
    (a*U,b+((cB i n)*a)/(IV.c (Int.ofNat (i+n+2))))
-- hBox assumes real u in the designated range
def hBox (U:IV) (i n:Nat):IV :=
  let (a,b):= bsumH U i n
  b + IV.span 0 (cB i n*a*(1/(1-U))^(i+1))
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Moments
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 stable Laplace moments. Define using the translated Gaussian variable
on (x,∞). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal
namespace GeneralMahler.SCal
open Profile Layers
def Lpn (n:Nat) (x y:ℝ):= phi y*((y-x)^n / phi x)
def Ymk (n:Nat) (x:ℝ):= ∫ y in Ioi x,Lpn n x y

-- continued fraction
def cRat (n:Nat) (x:ℝ):= Ymk (n+1) x/Ymk n x

end GeneralMahler.SCal

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_LapBox
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Jet.instZeroIV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 interval enclosures for the Ymk via Taylor and CF. -/
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
open Profile Layers Cert Cert.IV
def phi0B:= (rtB ((2:IV)*piB))⁻¹
def cxB (X:IV):= -(sq X)/(2:IV)
def phiB (X:IV):=phi0B*ebox 14 (cxB X)

def pSeries (C:IV) : ℕ → IV×IV
  | 0=>(1,0)
  | n+1=> let (a,b):=pSeries C n
          (a*C/IV.c (Int.ofNat (n+1)),b+a/IV.c (Int.ofNat (2*n+1)))
def pTaylor (X:IV):=
  ((1/2:IV)+ (X*phi0B)*((pSeries (cxB X) 25).2+terr))

open Finset

def cEncl (X:IV):ℕ→ℕ→IV
  | 0,n=> span (0:IV) ((IV.c (Int.ofNat (n+1)))/X)
  | j+1,n=> IV.c (Int.ofNat (n+1))/(X+cEncl X j (n+1))

def forward (X Y:IV) : ℕ→IV
  | 0=>Y
  | 1=>1-X*Y
  | n+2=> IV.c (Int.ofNat (n+1))*(forward X Y n)-X*(forward X Y (n+1))

def prodCF (X:IV) (e:ℕ) : ℕ→IV
  | 0=>(X+cEncl X e 0)⁻¹
  | n+1=>cEncl X (e-n) n*prodCF X e n

def ymBox (n:Nat) (X:IV):IV :=
  if LeB (Zabs (cxB X)) 1 then forward X ((1-pTaylor X)/phiB X) n
  else if Less 0 X then prodCF X (if Less (IV.c 4) X then 42 else 112) n
  else unk
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Stable
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 stable algebra shared by finite and infinite estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
open Profile Layers
def sY:=Ymk 0
def sB:=Ymk 1
def sU (x:ℝ):=sY x*phi x
def sP (x:ℝ):=1-sU x
def sJ (x:ℝ):= x*x/2+Real.log (√(2*π))-Real.log (sY x)-sP x
def sH (x:ℝ):= Qh 0 (sU x)
def sW (x:ℝ):=1-sP x*sB x
def sd (x:ℝ):= sB x*sB x*sJ x+sW x*sW x*sH x
def sK (x:ℝ):= sd x+sY x*sY x*(sJ x+sP x*sP x*sH x)-1
def sg1 (x:ℝ):=sY x*(sB x*sJ x-sW x*sP x*sH x)
def sC (x:ℝ):= -(sd x)+(ar-1)*(x*sg1 x-sK x)
def sRv (x:ℝ):= phi x/sP x - sB x/sY x
def sV2 (x:ℝ):= let m:=phi x/sP x; 2-m*(x+m)-sB x/(sY x*sY x)

def xs (t:ℝ):=sb*Real.sinh t
def ast (t:ℝ):=sb*Real.cosh t
def liftF (f:ℝ→ℝ) (t:ℝ):=f (xs t)
end GeneralMahler.SCal

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_RealJ
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Finite-real-variable towers in t coordinate. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
open Profile Layers Jet
def xj : RF := fun x n=> if Even n then xs x else ast x
def aj (x:ℝ):=tail (xj x)

def momRF (i:Nat):RF:= fun x n=> (-1)^n*Ymk (i+n) x
def hfRF:RF:=fun x n=> n.factorial*Qh n x

namespace CJet
def halfS (x:ℝ) := mulJ (ray (1/2)) (mulJ (xj x) (xj x))
def etaS (x:ℝ):= negJ (halfS x)
def ph (x:ℝ):= mulJ (ray (phi 0)) (expSub (etaS x) (Real.exp (etaS x 0)))
def ym (i:Nat) (x:ℝ):= compJ (momRF i (xj x 0)) (xj x)
def Y:RF:= ym 0
def B:RF:=ym 1
def u (x:ℝ):= mulJ (Y x) (ph x)
def p0 (x:ℝ):= subJ (ray 1) (u x)
def h (x:ℝ):= compJ (hfRF (u x 0)) (u x)
def j (x:ℝ):=
  subJ (subJ (plusJ (halfS x) (ray (Real.log (√(2*π)))))
    (logSub vn (Y x) (Real.log (Y x 0)))) (p0 x)
def w (x:ℝ):= subJ (ray 1) (mulJ (p0 x) (B x))
def dj (x:ℝ):= plusJ (mulJ (mulJ (B x) (B x)) (j x)) (mulJ (mulJ (w x) (w x)) (h x))
def gp (x:ℝ):=mulJ (Y x) (subJ (mulJ (B x) (j x)) (mulJ (mulJ (w x) (p0 x)) (h x)))
def kj (x:ℝ):=subJ (plusJ (dj x)
  (mulJ (mulJ (Y x) (Y x)) (plusJ (j x) (mulJ (mulJ (p0 x) (p0 x)) (h x))))) (ray 1)
def cj (x:ℝ):= plusJ (negJ (dj x)) (mulJ (ray (ar-1)) (subJ (mulJ (xj x) (gp x)) (kj x)))
def mc (x:ℝ):=mulJ (ph x) (invSub vn (p0 x))
def jy (x:ℝ):= invSub vn (Y x)
def rv (x:ℝ):= subJ (mc x) (mulJ (B x) (jy x))
def vv (x:ℝ):=
  subJ (subJ (ray (2:ℝ)) (mulJ (mc x) (plusJ (xj x) (mc x)))) (mulJ (mulJ (B x) (jy x)) (jy x))

end CJet
end GeneralMahler.SCal

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_BoxJ
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interval enclosures for profile derivative towers from hyperbolic coordinates
and bounds for the Laplace moments `Ymk`. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Profile Layers Jet Cert Cert.IV
structure Row0 where
  X:IV
  T:IV
  mm:ℕ→IV

namespace Row0
def sbB: IV:= IV.c 36/IV.c 10
def arB: IV:=IV.c 75/IV.c 10
def bSinh (U:IV):IV:= (ebox 5 U-(ebox 5 U)⁻¹)/ (2:IV)
def bCosh (U:IV):IV:= (ebox 5 U+(ebox 5 U)⁻¹)/ (2:IV)
def point (x:IV):Row0 :=
  let T:=sbB*bSinh x
  ⟨T,sbB*bCosh x,fun i=>ymBox i T⟩

def around (x y:Row0): Row0:=
  ⟨IV.span x.X y.X,IV.span x.T y.T,fun i=>IV.span (y.mm i) (x.mm i)⟩

structure At (x:ℝ) (w:Row0): Prop where
  X: xs x∈ w.X
  T: ast x∈ w.T
  mm:∀ n,Ymk n (xs x)∈ w.mm n
variable (w:Row0)
def Xj : J IV:=fun n=> if n%2=0 then w.X else w.T
def Ym (i:Nat) := compJ (fun n=> (-(1:IV))^n*w.mm (i+n)) w.Xj
def Y:= w.Ym 0
def B := w.Ym 1
def hsS:= mulJ (ray (1/2:IV)) (mulJ w.Xj w.Xj)
def Ph :=
  let f:=negJ w.hsS
  mulJ (ray phi0B) (expSub f (ebox 14 (f 0)))
def U := mulJ w.Y w.Ph
def P0:= subJ (ray 1) w.U
def W0:= subJ (ray 1) (mulJ w.P0 w.B)
def Hj:=
  let R:=w.U 0
  compJ (fun n=> IV.c (Int.ofNat n.factorial)*hBox R n (if LeB R (IV.c 8/IV.c 100) then 18 else 42)) w.U
def J0:=
  let A:=rtB ((2:IV)*piB)
  subJ (subJ (plusJ w.hsS (ray (lbox 6 A)))
    (logSub ub w.Y (lbox 6 (w.Y 0)))) w.P0
def Dj:= plusJ (mulJ (mulJ w.B w.B) w.J0) (mulJ (mulJ w.W0 w.W0) w.Hj)
def Kj:= subJ (plusJ w.Dj (mulJ (mulJ w.Y w.Y)
  (plusJ w.J0 (mulJ (mulJ w.P0 w.P0) w.Hj)))) (ray 1)
def Gp:= mulJ w.Y (subJ (mulJ w.B w.J0) (mulJ (mulJ w.W0 w.P0) w.Hj))
def Cj:=plusJ (negJ w.Dj) (mulJ (ray (arB-1)) (subJ (mulJ w.Xj w.Gp) w.Kj))
def Mc:=mulJ w.Ph (invSub ub w.P0)
def JY:=invSub ub w.Y
def Rv:=subJ w.Mc (mulJ w.B w.JY)
def Vv:=subJ (subJ (ray (2:IV)) (mulJ w.Mc (plusJ w.Xj w.Mc))) (mulJ (mulJ w.B w.JY) w.JY)

end Row0
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_QuantJ
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Towers for q, N profiles and field composition identities. -/
open Set Filter MeasureTheory MeasureTheory.Measure Real
namespace GeneralMahler.SCal
open Profile Layers Jet
noncomputable section
def DotF (f:ℝ→ℝ):=deriv (liftF f)
def DDot (f:ℝ→ℝ):=deriv (DotF f)
def thR (x:ℝ):=xs x/ ast x
def NNf (f:ℝ→ℝ) (x:ℝ):= DDot f x-thR x * DotF f x

namespace CJet
def radK:=bb-r*r
def rj (x:ℝ):=subJ (ray radK) (dj x)
def el (x:ℝ):=rootSub (1/2) vn (rj x) (Real.sqrt (rj x 0))
def qj (x:ℝ):=subJ (ray kk) (el x)
def it (x:ℝ):=invSub vn (aj x)
def tj (x:ℝ):=mulJ (xj x) (it x)
def NJ (X:RF) (x:ℝ):=
  subJ (tail (tail (X x))) (mulJ (tj x) (tail (X x)))
def Sf (X:RF) (x:ℝ):=
  subJ (plusJ (mulJ (ray 2) (X x)) (mulJ (tj x) (tail (X x))))
    (mulJ (mulJ (it x) (it x)) (NJ X x))

def RadH := ∀ x, 0 < rad x
end CJet
end

open Cert Cert.IV
namespace Row0
variable (w:Row0)
def bbB:IV:=IV.c 602/IV.c 1000
def ccB:IV:=IV.c 365/IV.c 1000
def rB:IV:=IV.c 22/IV.c 100
def kkB:IV:= rtB (bbB-ccB)
def radB:=bbB-rB*rB
def Rj:=subJ (ray radB) w.Dj
def elB:=rootSub (1/2) ub w.Rj (rtB (w.Rj 0))
def Qj:=subJ (ray kkB) w.elB
def itB:=invSub ub (tail w.Xj)
def tjB:=mulJ w.Xj w.itB
def NB (X:J IV):=subJ (tail (tail X)) (mulJ w.tjB (tail X))
def SF (X:J IV):=
  subJ (plusJ (mulJ (ray 2) X) (mulJ w.tjB (tail X)))
    (mulJ (mulJ w.itB w.itB) (w.NB X))

end Row0
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Grid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Finite interval cells of appendix §07. Actual tagged values. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Profile Jet CJet
namespace Tag

noncomputable def Fld : Tag→RF
  | R=>rj
  | K=>kj
  | C=>cj
  | Q=>qj
  | dK=> fun x=> tail (kj x)
  | dC=> fun x=> tail (cj x)
  | dQ=> fun x=> tail (qj x)
  | ddK=> fun x=>tail (tail (kj x))
  | ddC=> fun x=>tail (tail (cj x))
  | ddQ=> fun x=>tail (tail (qj x))
  | NK=> NJ kj
  | NC=> NJ cj
  | NQ=> NJ qj
  | RV=>rv
  | V=>vv
  | S=>Sf qj

noncomputable def act : Tag→ℝ→ℝ
  | R=> liftF rad
  | K=> liftF Kp
  | C=> liftF Cp
  | Q=> liftF qu
  | dK=> DotF Kp
  | dC=> DotF Cp
  | dQ=> DotF qu
  | ddK=> DDot Kp
  | ddC=> DDot Cp
  | ddQ=> DDot qu
  | NK=> NNf Kp
  | NC=> NNf Cp
  | NQ=> NNf qu
  | RV=> liftF fun x=> deriv v x-x
  | V=> liftF (deriv (deriv v))
  | S=> liftF (N2 qu)

open Cert Cert.IV
def Jt (t:Tag) (w:Row0): J IV := match t with
  | R=>w.Rj
  | K=>w.Kj
  | C=>w.Cj
  | Q=>w.Qj
  | dK=>tail w.Kj
  | dC=>tail w.Cj
  | dQ=>tail w.Qj
  | ddK=>tail (tail w.Kj)
  | ddC=>tail (tail w.Cj)
  | ddQ=>tail (tail w.Qj)
  | NK=>w.NB w.Kj
  | NC=>w.NB w.Cj
  | NQ=>w.NB w.Qj
  | RV=>w.Rv
  | V=>w.Vv
  | S=>w.SF w.Qj

end Tag

namespace Grid
open Tag Cert Cert.IV
def deltG:IV:= (1:IV)/(IV.c 200)
def nbox (n:ℕ):IV:= IV.c (Int.ofNat n)/IV.c 200

def pG (n:ℕ): Row0:=Row0.point (nbox n)
def pc (n:ℕ):Row0:=Row0.around (pG n) (pG (n+1))

def cb0 (n:ℕ) (t:Tag) (i:ℕ) (F:IV):IV:= bcChord deltG
  (t.Jt (pG n) i) (t.Jt (pG (n+1)) i) F
def cb (n:ℕ) (t:Tag) (i:ℕ):IV:= cb0 n t i (t.Jt (pc n) (i+2))
def tot (n:ℕ) (t:Tag):IV:= if sharp t then cb0 n t 0 (cb n t 2) else cb n t 0
end Grid
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Pass
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Range assertions and combined first derivative assertion for §07.
Integers in tables denote exact multiples 1/10000. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Profile Layers Jet Tag Cert Cert.IV

namespace Grid
-- exact scale
def bandD : Int:=den / 10000
def bd (n:Int):IV:= box (n*bandD) (n*bandD)
def band (l u:Int) : IV:= box (l*bandD) (u*bandD)

def rng : Tag→IV
  | R => band 530 1680
  | K => band (-70) 275
  | C => band (-5010) (-3410)
  | Q => band 775 2559
  | dK => band (-660) 660
  | dC => band (-2470) 2470
  | dQ => band (-1930) 1930
  | ddK=>band (-2600) 2600
  | ddC=>band (-9500) 9500
  | ddQ=>band (-5600) 5600
  | NK=>band (-3000) 3000
  | NC=>band (-9500) 9500
  | NQ=>band (-5600) 5600
  | RV=>band (-3190) 3190
  | V =>band 7250 10600
  | S =>band 1130 5140
def roff : Tag→IV
  | K=>band (-1) 191
  | C=>band (-5010) (-4950)
  | Q=>band 2350 2559
  | dK=>band (-211) 211
  | dC=>band (-84) 84
  | NK=>band 0 3000
  | _=>unk

structure Panel where
  lo:Nat -- beginning t-index, inclusive
  hi:Nat
  qR:IV
  sr:IV
  vR:IV
  rh:Int -- rho max tick
def pan (a b:Nat) (l u v w x y z:Int):Panel:=
  ⟨a,b, band (10*l) (10*u),band (10*v) (10*w),band (10*x) (10*y),10*z⟩
def panel : Nat→Panel
  | 0=> pan 0 20 77 81 113 132 725 743 804
  | 1=> pan 20 40 80 88 125 166 740 785 814
  | 2=> pan 40 60 87 100 159 220 782 848 831
  | 3=> pan 60 80 99 116 213 288 845 920 853
  | 4=> pan 80 100 115 134 281 359 917 986 877
  | 5=> pan 100 140 133 171 352 464 983 1055 927
  | 6=> pan 140 200 170 211 457 504 1041 1059 992
  | 7=> pan 200 340 210 245 497 513 1009 1044 1072
  | _=> pan 340 720 244 256 506 514 999 1012 1104

def checkSR (b:Tag→IV) (k:Panel):Bool :=
  SubB (b Q) k.qR && SubB (b S) k.sr && SubB (b V) k.vR
def SIn (b:Tag→ℝ) (k:Panel):Prop:=
  b Q∈k.qR∧b S∈k.sr∧b V∈k.vR

noncomputable def Ucost (f:Tag→ℝ):ℝ:=
  (1507/1000)*max 0 (-(f NK))+
    ((12*(8/10))/mstar^2)*
      (125/100*(f dK+tc*f dC)^2+5*Profile.tr^2*f dC^2)
def Ubox (b:Tag→IV):IV:=
  bd 15070*Zmax 0 (-(b NK))+(bd 96000 /sq (bd 3520))*
    (bd 12500 * sq (b dK+bd 210*b dC)+ (IV.c 5)*sq (bd 430)*sq (b dC))
noncomputable def Ur:=54/100*r^2*omegaP^2
def UrB:IV:=bd 5400*sq (bd 2200)*sq (bd 46000)
noncomputable def Cor (k c:ℝ) (r:ℝ):=lam*r^2+r*c+k
noncomputable def Ta (k c:ℝ):=2*ell0*c-ell0^2-4*lam*k
def CorB (k c r:IV):IV:=bd 6500*sq r+r*c+k
def TaB (k c:IV):IV:=bd (-7400)*c-sq (bd 3700)-bd 26000*k
def Corr (f:Tag→ℝ): Prop:=
  0<Cor (f K) (f C) tmin ∧
    Cor (f K) (f C) tmax<0 ∧ mstar^2<Ta (f K) (f C) ∧ Ucost f≤ Ur
def joint (b:Tag→IV):Bool :=
  Less 0 (CorB (b K) (b C) (bd (-220))) &&
    Less (CorB (b K) (b C) (bd 640)) 0 &&
    Less (sq (bd 3520)) (TaB (b K) (b C)) &&
    LeB (Ubox b) UrB
def checkIn (b w:Tag→IV):Bool:= allT.all (fun i=>SubB (b i) (w i))

def x5:=band 2203 2559
def pass0 (n:ℕ) (b:Tag→IV):Bool :=
  checkIn b rng && joint b &&
    (if n ≥ 280 then checkIn b roff else true) &&
    checkSR b (panel (stage n)) &&
    (if n ≥ 225 then SubB (b Q) x5 else true)

def pass (n:ℕ):Bool:=pass0 n (tot n)

structure passR (n:ℕ) (a:Tag→ℝ):Prop where
  gr:∀ i,a i∈rng i
  uu:Corr a
  off:280≤n → ∀ i,a i∈ roff i
  pn:SIn a (panel (stage n))
  five:225≤n → a Q∈x5

end Grid
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Circle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Circular profile and layer bound envelopes. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Tag Grid Jet Profile Layers Cert Cert.IV
noncomputable section
abbrev lc:=liftF uc
abbrev ls:=liftF us
def ca (x:ℝ):=2+omegaP^2*(ast x)⁻¹^2
def cb1 (x:ℝ):=(1+(ast x)⁻¹^2)*omegaP* thR x

def ro2 (x:ℝ):=r^2*(ca x^2+cb1 x^2)
def aY (x:ℝ):=(1-x)/sb^2
def rPoly (x:ℝ):=
  r^2*((2+omegaP^2*aY x)^2+(1+aY x)^2*omegaP^2*x)

end
def omegaB:=bd 46000
def rBox (A:Row0):IV:=
  let p:=omegaB
  let y:=A.X/A.T
  let h:=IV.sq (A.T)⁻¹
  IV.sq (bd 2200)*(IV.sq (2+IV.sq p*h)+IV.sq ((1+h)*p*y))
noncomputable def rPanel (k:ℕ):ℝ:= ((panel k).rh:ℝ)/10000
-- finite arithmetic at upper cells
def testPn (k:Nat):Bool:=
  if (panel k).hi < 720 then LeB (rBox (pG (panel k).hi)) (sq (bd (panel k).rh))
  else true
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_LayerAlg
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 layer rectangles. Evaluate only 4 vertices in H and V2. -/
open Set Filter Real
namespace GeneralMahler.SCal.PA
open Tag Grid Jet Profile Cert Cert.IV
def endp (k:Bool):IV→Int
  | unk=>0
  | box a b=> if k then b else a
noncomputable def eR (k:Bool)(A:IV):ℝ := IV.w (endp k A)
def eB (k:Bool)(A:IV):IV:=box (endp k A) (endp k A)

noncomputable def Ldef (x v:ℝ):=
  let j:= x+v-2*kar
  x+tc*j-(Profile.tr/(2*h₀)+1/alpha)* j^2
noncomputable def Lcost (x y:ℝ):=
  2*(bb+eta+(bb+eta-kar)*tmin)+ 2*bm*x*y +2*e₀*(2*Profile.tr)^2+Profile.tr*h₀/2
noncomputable def HV (q s:ℝ):= 4*cc+4*kk*q+2*(kk-q)*s
def defB (x v:IV):=
  let j:=x+v-2*bd 11600
  x+bd 210*j-(bd 430/(2*bd 5000)+(1:IV)/bd 22600)*sq j
def bmb:IV:=
  ((1:IV)+bd 640)*(bd 6020-3*bd 220)/
    (3*(3*(bd 6020+bd 220)-4*bd 3650))
def costB (s t:IV):=
  2*(bd 6020 +bd 220+(bd 6020+bd 220-bd 11600)*bd (-220))+
    2*bmb*s*t+2*bd 2560*sq (2*bd 430) + bd 430*bd 5000/2
def hvB (x v:IV):=4*bd 3650+4*Row0.kkB*x+2*(Row0.kkB-x)*v

noncomputable def Hbnd (k:Bool) (x z:Nat):=
  HV (eR k (panel x).qR) (eR k (panel z).sr) + (if k then 2*r*rPanel z else -(2*r*rPanel z))
def hbB (k:Bool)(x z:Nat):=
  let V:=2*bd 2200*bd (panel z).rh
  hvB (eB k (panel x).qR) (eB k (panel z).sr)+ (if k then V else -V)
def cond (x z:ℕ) (a b:Bool):Bool:= Less
  (costB (eB true (panel x).sr) (eB true (panel z).sr))
  (defB (hbB a x z) (eB b (panel x).vR))
def corners (x z:ℕ):Bool:=
  cond x z true true && cond x z true false && cond x z false true && cond x z false false
def allCn (x:Nat): Bool:= (List.range 9).all (corners x)
end GeneralMahler.SCal.PA

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Data
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Compact certificate for §07 and table for later quadrature. -/
open Set Filter Real
namespace GeneralMahler.SCal.Grid
open Tag CJet Jet Profile Cert Cert.IV

def GB (a:Int):IV:=box ((a-3)*dn8) ((a+3)*dn8) -- ±3e-8

def inData (n:Nat) (L:Line): Bool:=
  let A := pG n
  let cv:=trbox 8 (bd 46000*nbox n)
  SubB A.X (GB L.x) &&
    SubB (A.Kj 0) (GB L.k) && SubB (A.Cj 0) (GB L.c) &&
    SubB (A.Qj 0) (GB L.q) && SubB (bd 2200*cv.1) (GB L.u) &&
    SubB (bd 2200*cv.2) (GB L.v)
def checkL (n:Nat) (L:Line):Bool:=
  inData n L && (if n<720 then pass n && LeB (tot n K) (GP L.mx) else true)

structure NodeTrue (n:ℕ) (L:Line) : Prop where
  xx: xs (nd n)∈ GB L.x
  k : K.act (nd n)∈ GB L.k
  c : C.act (nd n)∈ GB L.c
  q : Q.act (nd n)∈ GB L.q
  u : uc (xs (nd n)) ∈ GB L.u
  v : us (xs (nd n)) ∈ GB L.v
end GeneralMahler.SCal.Grid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_NodesTbl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
def passesAt (n:ℕ):Bool:=checkL n (A n)
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Base
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Tail jets use log coordinate t, denoted y here. This implements D=x∂_x. -/
open Set Filter Real
noncomputable section
namespace GeneralMahler.SCal.Tail
open Profile Layers Jet
def Mk (n:Nat) (y:ℝ):=(XX y)^(n+1)*Ymk n (XX y)
def Qp (n:Nat) (y:ℝ):= (XX y)^n*phi (XX y)

namespace JT
def IJ (y:ℝ): J ℝ:=fun n=> (-2:ℝ)^n*ev y
def Wrec (w i:J ℝ) : ℕ→ℝ
  | 0=> w 0
  | n+1=> -2*Wrec w i n + i n
def WW (y:ℝ):= Wrec (ray (Wv y)) (IJ y)
def Prec:ℕ→ℕ→ℝ→ℝ
  | 0,m,y=> Qp m y
  | n+1,m,y=> m*Prec n m y - Prec n (m+2) y
def TP (m:ℕ):RF:=fun y n=>Prec n m y
-- Z=ξ^i Mk
def Mrec:ℕ→ℕ→ℕ→ℝ→ℝ
  | 0,m,i,y=>(ev y)^i*Mk m y
  | n+1,m,i,y=> -2*i*Mrec n m i y + Mrec n (m+2) (i+1) y
def TM (m i:ℕ):RF:= fun y n=> Mrec n m i y

end JT
end GeneralMahler.SCal.Tail

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Limit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 log domain elementary envelope values. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail
open JT Grid Profile Tag Cert Cert.IV Jet Layers

-- base envelope Boxes
def xiMax:IV:=(1:IV)/IV.c 4096
def XI : IV:= IV.span 0 xiMax
def BI : J IV:= fun n=> (-(2:IV))^n * XI
def wb:IV:= IV.span 0 (IV.c 113/IV.c 100000)
def wr : J IV
  | 0=> wb
  | n+1=> -(2:IV)*wr n+BI n
def pf0 : IV:= IV.span 0 (1/IV.c 1000000000)
def pr : ℕ→ℕ→IV
  | 0,i=> if i ≤ 10 then pf0 else unk
  | n+1,i=> (ub i)*pr n i-pr n (i+2)

def m0B (m:Nat):IV:=
  if m=0 then IV.span ((1:IV)-xiMax) 1
  else if m=1 then IV.span ((1:IV)- (IV.c 3)*xiMax) 1
  else IV.span 0 (ub m.factorial)
def mr:ℕ→ℕ→ℕ→IV
  | 0,m,i=>XI^i*m0B m
  | n+1,m,i=> -(2:IV)*ub i*mr n m i + mr n (m+2) (i+1)

end GeneralMahler.SCal.Tail

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Tower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 tail profile identities using normalized log towers. -/
open Set Filter Real
open scoped Topology
noncomputable section
namespace GeneralMahler.SCal.Tail.JT
open Profile Layers Jet
variable (x:ℝ) -- logarithmic point

def MJ:= TM 0 0
def NJ:= TM 1 0
def Pt (x:ℝ):= mulJ (TP 1 x) (MJ x)
def U (x:ℝ):= mulJ (IJ x) (Pt x)
def PP (x:ℝ):=subJ (ray 1) (U x)
def PQ (x:ℝ):= mulJ (PP x) (PP x)
def HH (x:ℝ):=compJ (hfRF (U x 0)) (U x)
def H1 (x:ℝ):=compJ (tail (hfRF (U x 0))) (U x)
def DH (x:ℝ):=mulJ (mulJ (ray (1/2)) (Pt x)) (subJ (invSub vn (PP x)) (H1 x))
def M2 (x:ℝ):=mulJ (MJ x) (MJ x)
def NN (x:ℝ):=mulJ (NJ x) (NJ x)
def del (x:ℝ):=plusJ (subJ (negJ (logSub vn (MJ x) (Real.log (MJ x 0)))) (subJ (PP x) (ray 1)))
  (subJ (mulJ (PQ x) (HH x)) (ray (1/2)))
def wZ (x:ℝ):=plusJ (WW x) (mulJ (IJ x) (del x))
def A (x:ℝ):=subJ (mulJ (ray (1/2)) (NN x))
  (mulJ (mulJ (mulJ (ray 2) (PP x)) (HH x)) (NJ x))
def mi (x:ℝ):= mulJ (NJ x) (plusJ (ray 1) (MJ x))
def N1 (x:ℝ):= mulJ (IJ x) (NN x)
def DD (x:ℝ):= plusJ (plusJ (DH x) (A x)) (mulJ (NN x) (wZ x))
def G0 (x:ℝ):= subJ (mulJ (mulJ (ray (1/4)) (IJ x)) (mi x))
  (mulJ (mulJ (ray (1/2)) (M2 x)) (wZ x))
def KR (x:ℝ):=
  plusJ (plusJ (plusJ (plusJ (subJ (plusJ (DH x) (A x)) (NJ x))
    (mulJ (ray (1/2)) (N1 x))) (ray (3/2)))
    (mulJ (plusJ (M2 x) (N1 x)) (del x)))
    (mulJ (subJ (NN x) (mi x)) (WW x))
def CQ (x:ℝ):= subJ (mulJ (ray (ar-1)) (subJ (tail (tail (G0 x))) (tail (G0 x)))) (DD x)
def dF (x:ℝ):= plusJ (ray (1/2)) (mulJ (IJ x) (DD x))
def kF (x:ℝ):= plusJ (WW x) (mulJ (IJ x) (subJ (KR x) (ray (3/2))))
def gF (x:ℝ):= plusJ (G0 x) (ray (1/4))
def cF (x:ℝ):= subJ (mulJ (IJ x) (CQ x)) (ray (1/2))

end GeneralMahler.SCal.Tail.JT

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Enclose
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interval AD bounding envelopes DD, CQ, KR. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail.JTB
open JT Grid Profile Tag Cert Cert.IV Jet Layers
def bmJ : J IV:= fun n=> mr n 0 0
def bnJ : J IV:= fun n=> mr n 1 0
def bt1: J IV:= fun n=> pr n 1
def bPt:=mulJ bt1 bmJ
def bU := mulJ BI bPt
def bPP:= subJ (ray 1) bU
def bPQ:= mulJ bPP bPP
def hf0:J IV:= fun n=> ub n.factorial * hBox (bU 0) n 7
def bHH:=compJ hf0 bU
def bH1:=compJ (tail hf0) bU
def bDH:=mulJ (mulJ (ray (1/2)) bPt) (subJ (invSub ub bPP) bH1)
def bM:=mulJ bmJ bmJ
def bN:=mulJ bnJ bnJ
def bDel:=plusJ (subJ (negJ (logSub ub bmJ (lbox 5 (bmJ 0)))) (subJ bPP (ray 1)))
  (subJ (mulJ bPQ bHH) (ray (1/2)))
def bZ:=plusJ wr (mulJ BI bDel)
def bA:=subJ (mulJ (ray (1/2)) bN)
  (mulJ (mulJ (mulJ (ray 2) bPP) bHH) bnJ)
def bMi:=mulJ bnJ (plusJ (ray 1) bmJ)
def bN1:=mulJ BI bN
def bDD:= plusJ (plusJ bDH bA) (mulJ bN bZ)
def bG:=subJ (mulJ (mulJ (ray (1/4)) BI) bMi)
  (mulJ (mulJ (ray (1/2)) bM) bZ)
def bKR:=
  plusJ (plusJ (plusJ (plusJ (subJ (plusJ bDH bA) bnJ)
    (mulJ (ray (1/2)) bN1)) (ray (3/2)))
    (mulJ (plusJ bM bN1) bDel))
    (mulJ (subJ bN bMi) wr)
def bCQ:=
  subJ (mulJ (ray (Row0.arB-1)) (subJ (tail (tail bG)) (tail bG))) bDD
def bdF:=plusJ (ray (1/2)) (mulJ BI bDD)
def bkF:=plusJ wr (mulJ BI (subJ bKR (ray (3/2))))
def bcF:=subJ (mulJ BI bCQ) (ray (1/2))

end GeneralMahler.SCal.Tail.JTB

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Coords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Convert tail jets into coordinate and number operator bounds. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail
open JT JTB Grid Jet Tag Cert Cert.IV Profile Layers
noncomputable section
def rrF (x:ℝ):= subJ (ray CJet.radK) (dF x)
def ql (x:ℝ):=
  let A:=rrF x
  subJ (ray kk) (rootSub (1/2) vn A (Real.sqrt (A 0)))

def bt (t y:ℝ):= ast t*iv y
end

def bRat:=IV.span 0 (IV.c 1002/IV.c 1000)
def bRj:=subJ (ray Row0.radB) bdF
def bQj:=subJ (ray Row0.kkB)
  (rootSub (1/2) ub bRj (rtB (bRj 0)))
def ba (f:J IV):= bRat*f 1
def bbN (f:J IV):= sq bRat*(f 2-f 1)
def bdN (f:J IV):= bbN f+f 1
def bS2 (f:J IV):=2*f 0+f 1-XI*(f 2-f 1)

end GeneralMahler.SCal.Tail

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_PassTail
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Uniform global (after 64) certificates of value and Euler derivative bounds. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail
open JT JTB Grid Jet Tag Cert Cert.IV Profile Layers

-- profiles v' correction and v''
def ivb:IV:= IV.span 0 ((1:IV)/IV.c 64)
def mxB:=pf0/(bPP 0)
def rvb:IV:= mxB - ivb*(bnJ 0)/(bmJ 0)
def vvb:IV:= 2-mxB-mxB*mxB-(bnJ 0)/sq (bmJ 0)

def tabT : Tag→ IV
  | R=> bRj 0
  | K=> band 0 8
  | C=> bcF 0
  | Q=> bQj 0
  | dK=>ba bkF
  | dC=>ba bcF
  | dQ=>ba bQj
  | ddK=>bdN bkF
  | ddC=>bdN bcF
  | ddQ=>bdN bQj
  | NK=>clampNN (bbN bkF)
  | NC=>bbN bcF
  | NQ=>bbN bQj
  | RV=>rvb
  | V=>vvb
  | S=>bS2 bQj

end GeneralMahler.SCal.Tail

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Universal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Propagate and combine the finite/infinite and reflected ranges. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Grid Tag Profile CJet Cert Cert.IV
def NG:=By Nodes.passesAt 0 721
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Mean
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §08 segment coordinates and physical averages. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Segment Jet
variable {m h:ℝ}
def seg (m h:ℝ):Plane:=(xs (left m h),xs (right m h))
end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Integr
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Finite-area bound and infinite tail for K. -/
open MeasureTheory Set Filter Real
open scoped Topology Interval
namespace GeneralMahler.SCal
open Grid Tag Jet Profile Cert Cert.IV Nodes
noncomputable section
def KP0 (x:ℝ):=max 0 (Kp x)
def ikp (x:ℝ):=∫ y in (0:ℝ)..x,KP0 y
def zn (n:ℕ):= xs (nd n)
def maxArea (n:ℕ):= (zn (n+1)-zn n)*max 0 (gv (A n).mx)
def arSum : ℕ→ℝ
  | 0=>0
  | n+1=>arSum n+maxArea n
end
def distB (n:ℕ):IV:= GB (A (n+1)).x-GB (A n).x
def AC : ℕ→IV
  | 0=>0
  | n+1=>AC n+distB n*Zmax 0 (GP (A n).mx)
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Bound2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interval on t; second derivative majorants. -/
noncomputable section
open Set Filter Real MeasureTheory
open scoped Topology Interval
namespace GeneralMahler.SCal.Mid
open Tag Grid Jet Profile Segment SE

structure Guard (f:ℝ→ℝ)(A:Cap):Prop where
  h: Differentiable ℝ f
  g: Differentiable ℝ (deriv f)
  c: Continuous (ddf f)
  fa: ∀ x,|f x|≤A.a
  fb: ∀ x,|deriv f x|≤A.b
  fc: ∀ x,|ddf f x|≤A.c

end GeneralMahler.SCal.Mid

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Cost
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Algebraic reduction of equation (4). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Segment Jet
-- for interval pair v in physical coordinates; subscript a,d average/half-difference
variable (v:Plane)
def pPlus := mdis uc v+mdis us v
def qPlus := mdis qu v
def pa:= (pPlus v+pPlus v.swap)/2
def pd:= (pPlus v-pPlus v.swap)/2
def ba:= (qPlus v+qPlus v.swap)/2
def bd0:= (qPlus v-qPlus v.swap)/2
def ca0:= bav Cp v-(Cp v.2+Cp v.1)/2
def cd0 := (Cp v.2-Cp v.1)/2
def ek:= bav Kp v-(Kp v.2+Kp v.1)/2
def costs:ℝ:= ek v+sgamma v+
  ((ca0 v-pa v-ba v)^2+(cd0 v-pd v-bd0 v)^2)/(4*lam)+ tmax*(pa v+ ba v)

-- Reflection combined with swapping
def refPt (x:Plane):Plane :=(-x.2,-x.1)

end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Phase
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Circular means on normalized interval and variance inequality. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Segment Jet
variable (m h:ℝ)
local notation "w" => Profile.omegaP
def PhiA (h:ℝ):=(cos (w*h)+w*cott h*sin (w*h))/(1+w^2)
def PhiB (h:ℝ):=(cott h*sin (w*h)-w*cos (w*h))/(1+w^2)
def fstar (h:ℝ):= r^2/(1+w^2)*(w^2 - sin (w*h)^2/sinh h^2)
def Pastar (h:ℝ):= 2*r^2*(1-PhiA h*cos (w*h))
def Pdstar (m h:ℝ):= -2*r^2* PhiB h*tanh m*sin (w*h)

abbrev Fxc (m:ℝ)(t:ℝ):= Real.cos (w*(t-m))
abbrev Fxs (m:ℝ)(t:ℝ):= Real.sin (w*(t-m))
end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Features
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Center profiles for direct evaluation in compact region. -/
open Set Filter Real
namespace GeneralMahler.SCal.Mid
open Tag Grid Jet Profile Segment SE

noncomputable section
namespace Ft
def f: Ft→ℝ→ℝ
  | K=> fun x=> Kp x-k0
  | C=> fun x=> Cp x-c0
  | Q=> fun x=> qu x-q0
  | M=> fun x=> (qu x-q0)^2
  | J=>uc
  | V=>us
def g(p:Ft):= liftF p.f
end Ft
end
end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Traversal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Uniform second derivative bound of endpoint spectral averages for smooth profiles. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology Interval
namespace GeneralMahler.SCal.Mid
open Tag Grid Jet Profile Segment SE
-- integral parametrization
variable {f g:ℝ→ℝ→ℝ}
variable (a:ℝ)(f₀:ℝ→ℝ)

variable {f₀}
def G2 (x t:ℝ):=
  s t^2 * (W0 a x t*ddf f₀ (T0 a x t)+
    2*Wd a x t*deriv f₀ (T0 a x t)+ W0 a x t*f₀ (T0 a x t))

end GeneralMahler.SCal.Mid

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Poly
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Middle-width certificate uses second derivative envelope on the
actual endpoint functional. Syntax shares proof of interval and profile estimates. -/
open Set Filter MeasureTheory MeasureTheory.Measure Real
namespace GeneralMahler.SCal.Mid
open Grid Jet Profile Segment SE Cert Cert.IV Ft
namespace Op
def boxE (k:Fin 3→Ft→IV):Op→IV
  | src n feat=> k n feat
  | num a b=> c a/c b
  | add a b=>boxE k a+boxE k b
  | sub a b=>boxE k a-boxE k b
  | mul a b=>boxE k a*boxE k b

end Op
noncomputable section
-- choose s=g t profiles
def inp (x y:ℝ):Fin 3→Ft→ℝ:=
  fun n f=> if n=0 then f.g x else if n=1 then f.g y else trav x f.g y
def Fval (x y:ℝ):= Op.eval (inp x y) Op.E
end
end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Trap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! A posteriori approximation of functional via actual f bounded derivatives. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Interval
namespace GeneralMahler.SCal.Mid
open Tag Grid Profile Jet Segment SE
-- cosh ratio ≤ e^δ
open Cert Cert.IV

def rectA (p:Ft) (n:Nat):=(zn (n+1)-zn n)*((p.f (zn n)+p.f (zn (n+1)))/2)
def areaP (p:Ft) (x:ℝ):=∫ t in (0:ℝ)..x,p.f t

def accum (p:Ft) : ℕ →ℝ
  | 0=>0
  | n+1=>accum p n+rectA p n
end GeneralMahler.SCal.Mid

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Prefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Vertex checking via prefix integrals. -/
open Set Filter MeasureTheory Real
namespace GeneralMahler.SCal.Mid
open Grid Nodes Tag Profile Segment SE Jet Cert Cert.IV
def ptF (n:Nat):Ft→IV
  | Ft.K=>GB (A n).k-bd 100
  | Ft.C=>GB (A n).c-bd (-4200)
  | Ft.Q=>GB (A n).q-bd 1600
  | Ft.J=>GB (A n).u
  | Ft.V=>GB (A n).v
  | Ft.M=>IV.sq (GB (A n).q-bd 1600)
def pz (n:ℕ):IV:=GB (A n).x
def aStep (n:ℕ)(p:Ft):IV:= (pz (n+1) - pz n)*((ptF n p+ptF (n+1) p)/(2:IV))
abbrev PrefixC:= ℕ→Ft→IV
def Works (B:PrefixC):Prop:=
   (∀ p, SubB 0 (B 0 p)=true) ∧ ∀ n:Nat,n<720→∀ p,SubB (B n p+aStep n p) (B (n+1) p)=true

def EB:IV:= 1/(IV.c 40000)
def mj (b:Bool)(i j:Nat)(B:PrefixC)(p:Ft):IV:=
  (B j p - sP b p (B i p))/(pz j-signF b (pz i)) + IV.span (-EB) EB

def ins (B:PrefixC)(b:Bool)(i j:ℕ):Fin 3→Ft→IV:=fun n p=>
  if n=0 then sFt b p (ptF i p) else if n=1 then ptF j p else mj b i j B p
def dotE (B:PrefixC)(b:Bool)(i j:ℕ):IV:=Op.boxE (ins B b i j) Op.E
end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Cells
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Adaptive grid interpolation verification. -/
open Set Filter Real
namespace GeneralMahler.SCal.Mid
open Grid Jet Profile Segment SE Cert Cert.IV
variable (B:PrefixC)(b:Bool)

def wlt0 (d:Nat):IV:= IV.c (Int.ofNat d)/IV.c 200
def berr (d:Nat):IV:= - (((IV.c 37)/(IV.c 4))*IV.sq (wlt0 d))
def ckF (i j d:ℕ):Bool:=
  gtwt b i j && Less (dotE B b i j) (berr d)
def quad (i j d:ℕ):Bool:=
  ckF B b i j d && ckF B b (i+d) j d &&
    ckF B b i (j+d) d && ckF B b (i+d) (j+d) d
def stepCheck (i j d:Nat):Bool:= vac b i j d || quad B b i j d
def quadRun : ℕ→ℕ→ℕ→Bool
  | 0,i,j=>stepCheck B b i j 1
  | n+1,i,j=>let d:=2^n
             stepCheck B b i j (d+d) || (quadRun n i j && quadRun n (i+d) j &&
               quadRun n i (j+d) && quadRun n (i+d) (j+d))
end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Tiles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Arithmetic verification of compact region. -/
open Set Filter Real
namespace GeneralMahler.SCal.Mid
open Grid Jet Profile Segment SE Cert Cert.IV
variable (B:PrefixC)
def initC:=everyF (fun t=>SubB 0 (B 0 t))
def ctStep (n:Nat):=everyF (fun t=>SubB (B n t+aStep n t) (B (n+1) t))

-- Blocks left i≤280 step8, right j≤720 step8
def tile (b:Bool)(i j:Nat):Bool:=quadRun B b 3 (8*i) (8*j)
def GoodS (b:Bool):Prop:=∀ i,i<35→By (tile B b i) 0 90
def Good := GoodS B true∧ GoodS B false

end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Tab
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
def cK0_22 (n:Nat):IV:=(if n < 11 then (if n < 5 then (if n < 2 then (if n < 1 then (box (0) (0)) else (box (-304463000000000000000000000) (-304459000000000000000000000))) else (if n < 3 then (box (-608827000000000000000000000) (-608819000000000000000000000)) else (if n < 4 then (box (-912995000000000000000000000) (-912983000000000000000000000)) else (box (-1216868000000000000000000000) (-1216852000000000000000000000))))) else (if n < 8 then (if n < 6 then (box (-1520348000000000000000000000) (-1520327000000000000000000000)) else (if n < 7 then (box (-1823336000000000000000000000) (-1823311000000000000000000000)) else (box (-2125735000000000000000000000) (-2125706000000000000000000000)))) else (if n < 9 then (box (-2427446000000000000000000000) (-2427413000000000000000000000)) else (if n < 10 then (box (-2728372000000000000000000000) (-2728335000000000000000000000)) else (box (-3028414000000000000000000000) (-3028373000000000000000000000)))))) else (if n < 16 then (if n < 13 then (if n < 12 then (box (-3327475000000000000000000000) (-3327430000000000000000000000)) else (box (-3625457000000000000000000000) (-3625408000000000000000000000))) else (if n < 14 then (box (-3922263000000000000000000000) (-3922210000000000000000000000)) else (if n < 15 then (box (-4217795000000000000000000000) (-4217738000000000000000000000)) else (box (-4511956000000000000000000000) (-4511895000000000000000000000))))) else (if n < 19 then (if n < 17 then (box (-4804649000000000000000000000) (-4804584000000000000000000000)) else (if n < 18 then (box (-5095777000000000000000000000) (-5095708000000000000000000000)) else (box (-5385244000000000000000000000) (-5385171000000000000000000000)))) else (if n < 20 then (box (-5672953000000000000000000000) (-5672876000000000000000000000)) else (if n < 21 then (box (-5958808000000000000000000000) (-5958727000000000000000000000)) else (box (-6242713000000000000000000000) (-6242628000000000000000000000)))))))
def cK22_45 (n:Nat):IV:=(if n < 33 then (if n < 27 then (if n < 24 then (if n < 23 then (box (-6524573000000000000000000000) (-6524484000000000000000000000)) else (box (-6804292000000000000000000000) (-6804199000000000000000000000))) else (if n < 25 then (box (-7081775000000000000000000000) (-7081678000000000000000000000)) else (if n < 26 then (box (-7356928000000000000000000000) (-7356827000000000000000000000)) else (box (-7629655000000000000000000000) (-7629551000000000000000000000))))) else (if n < 30 then (if n < 28 then (box (-7899864000000000000000000000) (-7899756000000000000000000000)) else (if n < 29 then (box (-8167460000000000000000000000) (-8167348000000000000000000000)) else (box (-8432350000000000000000000000) (-8432234000000000000000000000)))) else (if n < 31 then (box (-8694441000000000000000000000) (-8694321000000000000000000000)) else (if n < 32 then (box (-8953641000000000000000000000) (-8953517000000000000000000000)) else (box (-9209858000000000000000000000) (-9209730000000000000000000000)))))) else (if n < 39 then (if n < 36 then (if n < 34 then (box (-9463001000000000000000000000) (-9462869000000000000000000000)) else (if n < 35 then (box (-9712978000000000000000000000) (-9712843000000000000000000000)) else (box (-9959699000000000000000000000) (-9959561000000000000000000000)))) else (if n < 37 then (box (-10203075000000000000000000000) (-10202933000000000000000000000)) else (if n < 38 then (box (-10443016000000000000000000000) (-10442870000000000000000000000)) else (box (-10679433000000000000000000000) (-10679284000000000000000000000))))) else (if n < 42 then (if n < 40 then (box (-10912239000000000000000000000) (-10912086000000000000000000000)) else (if n < 41 then (box (-11141346000000000000000000000) (-11141189000000000000000000000)) else (box (-11366667000000000000000000000) (-11366507000000000000000000000)))) else (if n < 43 then (box (-11588117000000000000000000000) (-11587953000000000000000000000)) else (if n < 44 then (box (-11805610000000000000000000000) (-11805442000000000000000000000)) else (box (-12019061000000000000000000000) (-12018890000000000000000000000)))))))
def cK0_45 (n:Nat):IV:=(if n < 22 then (cK0_22 n) else (cK22_45 n))
def cK45_67 (n:Nat):IV:=(if n < 56 then (if n < 50 then (if n < 47 then (if n < 46 then (box (-12228387000000000000000000000) (-12228213000000000000000000000)) else (box (-12433505000000000000000000000) (-12433328000000000000000000000))) else (if n < 48 then (box (-12634334000000000000000000000) (-12634153000000000000000000000)) else (if n < 49 then (box (-12830792000000000000000000000) (-12830607000000000000000000000)) else (box (-13022799000000000000000000000) (-13022610000000000000000000000))))) else (if n < 53 then (if n < 51 then (box (-13210276000000000000000000000) (-13210083000000000000000000000)) else (if n < 52 then (box (-13393144000000000000000000000) (-13392948000000000000000000000)) else (box (-13571326000000000000000000000) (-13571127000000000000000000000)))) else (if n < 54 then (box (-13744746000000000000000000000) (-13744544000000000000000000000)) else (if n < 55 then (box (-13913329000000000000000000000) (-13913124000000000000000000000)) else (box (-14077001000000000000000000000) (-14076793000000000000000000000)))))) else (if n < 61 then (if n < 58 then (if n < 57 then (box (-14235690000000000000000000000) (-14235479000000000000000000000)) else (box (-14389324000000000000000000000) (-14389110000000000000000000000))) else (if n < 59 then (box (-14537832000000000000000000000) (-14537615000000000000000000000)) else (if n < 60 then (box (-14681145000000000000000000000) (-14680925000000000000000000000)) else (box (-14819196000000000000000000000) (-14818973000000000000000000000))))) else (if n < 64 then (if n < 62 then (box (-14951918000000000000000000000) (-14951692000000000000000000000)) else (if n < 63 then (box (-15079246000000000000000000000) (-15079017000000000000000000000)) else (box (-15201116000000000000000000000) (-15200884000000000000000000000)))) else (if n < 65 then (box (-15317466000000000000000000000) (-15317231000000000000000000000)) else (if n < 66 then (box (-15428236000000000000000000000) (-15427998000000000000000000000)) else (box (-15533366000000000000000000000) (-15533125000000000000000000000)))))))
def cK67_90 (n:Nat):IV:=(if n < 78 then (if n < 72 then (if n < 69 then (if n < 68 then (box (-15632799000000000000000000000) (-15632555000000000000000000000)) else (box (-15726478000000000000000000000) (-15726232000000000000000000000))) else (if n < 70 then (box (-15814349000000000000000000000) (-15814101000000000000000000000)) else (if n < 71 then (box (-15896360000000000000000000000) (-15896109000000000000000000000)) else (box (-15972459000000000000000000000) (-15972206000000000000000000000))))) else (if n < 75 then (if n < 73 then (box (-16042598000000000000000000000) (-16042342000000000000000000000)) else (if n < 74 then (box (-16106728000000000000000000000) (-16106470000000000000000000000)) else (box (-16164804000000000000000000000) (-16164544000000000000000000000)))) else (if n < 76 then (box (-16216782000000000000000000000) (-16216520000000000000000000000)) else (if n < 77 then (box (-16262621000000000000000000000) (-16262356000000000000000000000)) else (box (-16302280000000000000000000000) (-16302012000000000000000000000)))))) else (if n < 84 then (if n < 81 then (if n < 79 then (box (-16335721000000000000000000000) (-16335450000000000000000000000)) else (if n < 80 then (box (-16362908000000000000000000000) (-16362634000000000000000000000)) else (box (-16383807000000000000000000000) (-16383530000000000000000000000)))) else (if n < 82 then (box (-16398385000000000000000000000) (-16398106000000000000000000000)) else (if n < 83 then (box (-16406613000000000000000000000) (-16406332000000000000000000000)) else (box (-16408463000000000000000000000) (-16408180000000000000000000000))))) else (if n < 87 then (if n < 85 then (box (-16403909000000000000000000000) (-16403624000000000000000000000)) else (if n < 86 then (box (-16392928000000000000000000000) (-16392641000000000000000000000)) else (box (-16375498000000000000000000000) (-16375209000000000000000000000)))) else (if n < 88 then (box (-16351600000000000000000000000) (-16351309000000000000000000000)) else (if n < 89 then (box (-16321217000000000000000000000) (-16320924000000000000000000000)) else (box (-16284334000000000000000000000) (-16284038000000000000000000000)))))))
def cK45_90 (n:Nat):IV:=(if n < 67 then (cK45_67 n) else (cK67_90 n))
def cK0_90 (n:Nat):IV:=(if n < 45 then (cK0_45 n) else (cK45_90 n))
def cK90_112 (n:Nat):IV:=(if n < 101 then (if n < 95 then (if n < 92 then (if n < 91 then (box (-16240938000000000000000000000) (-16240640000000000000000000000)) else (box (-16191020000000000000000000000) (-16190719000000000000000000000))) else (if n < 93 then (box (-16134571000000000000000000000) (-16134267000000000000000000000)) else (if n < 94 then (box (-16071585000000000000000000000) (-16071279000000000000000000000)) else (box (-16002059000000000000000000000) (-16001751000000000000000000000))))) else (if n < 98 then (if n < 96 then (box (-15925993000000000000000000000) (-15925682000000000000000000000)) else (if n < 97 then (box (-15843387000000000000000000000) (-15843073000000000000000000000)) else (box (-15754245000000000000000000000) (-15753928000000000000000000000)))) else (if n < 99 then (box (-15658573000000000000000000000) (-15658253000000000000000000000)) else (if n < 100 then (box (-15556379000000000000000000000) (-15556056000000000000000000000)) else (box (-15447674000000000000000000000) (-15447348000000000000000000000)))))) else (if n < 106 then (if n < 103 then (if n < 102 then (box (-15332470000000000000000000000) (-15332142000000000000000000000)) else (box (-15210784000000000000000000000) (-15210453000000000000000000000))) else (if n < 104 then (box (-15082632000000000000000000000) (-15082298000000000000000000000)) else (if n < 105 then (box (-14948035000000000000000000000) (-14947698000000000000000000000)) else (box (-14807014000000000000000000000) (-14806674000000000000000000000))))) else (if n < 109 then (if n < 107 then (box (-14659595000000000000000000000) (-14659252000000000000000000000)) else (if n < 108 then (box (-14505804000000000000000000000) (-14505458000000000000000000000)) else (box (-14345670000000000000000000000) (-14345321000000000000000000000)))) else (if n < 110 then (box (-14179224000000000000000000000) (-14178872000000000000000000000)) else (if n < 111 then (box (-14006500000000000000000000000) (-14006145000000000000000000000)) else (box (-13827534000000000000000000000) (-13827176000000000000000000000)))))))
def cK112_135 (n:Nat):IV:=(if n < 123 then (if n < 117 then (if n < 114 then (if n < 113 then (box (-13642363000000000000000000000) (-13642002000000000000000000000)) else (box (-13451028000000000000000000000) (-13450663000000000000000000000))) else (if n < 115 then (box (-13253570000000000000000000000) (-13253202000000000000000000000)) else (if n < 116 then (box (-13050034000000000000000000000) (-13049663000000000000000000000)) else (box (-12840466000000000000000000000) (-12840092000000000000000000000))))) else (if n < 120 then (if n < 118 then (box (-12624914000000000000000000000) (-12624537000000000000000000000)) else (if n < 119 then (box (-12403428000000000000000000000) (-12403048000000000000000000000)) else (box (-12176061000000000000000000000) (-12175677000000000000000000000)))) else (if n < 121 then (box (-11942866000000000000000000000) (-11942479000000000000000000000)) else (if n < 122 then (box (-11703899000000000000000000000) (-11703508000000000000000000000)) else (box (-11459218000000000000000000000) (-11458823000000000000000000000)))))) else (if n < 129 then (if n < 126 then (if n < 124 then (box (-11208882000000000000000000000) (-11208483000000000000000000000)) else (if n < 125 then (box (-10952951000000000000000000000) (-10952549000000000000000000000)) else (box (-10691489000000000000000000000) (-10691083000000000000000000000)))) else (if n < 127 then (box (-10424560000000000000000000000) (-10424150000000000000000000000)) else (if n < 128 then (box (-10152229000000000000000000000) (-10151815000000000000000000000)) else (box (-9874564000000000000000000000) (-9874146000000000000000000000))))) else (if n < 132 then (if n < 130 then (box (-9591633000000000000000000000) (-9591211000000000000000000000)) else (if n < 131 then (box (-9303506000000000000000000000) (-9303080000000000000000000000)) else (box (-9010254000000000000000000000) (-9009824000000000000000000000)))) else (if n < 133 then (box (-8711950000000000000000000000) (-8711516000000000000000000000)) else (if n < 134 then (box (-8408668000000000000000000000) (-8408230000000000000000000000)) else (box (-8100482000000000000000000000) (-8100040000000000000000000000)))))))
def cK90_135 (n:Nat):IV:=(if n < 112 then (cK90_112 n) else (cK112_135 n))
def cK135_157 (n:Nat):IV:=(if n < 146 then (if n < 140 then (if n < 137 then (if n < 136 then (box (-7787468000000000000000000000) (-7787022000000000000000000000)) else (box (-7469703000000000000000000000) (-7469253000000000000000000000))) else (if n < 138 then (box (-7147265000000000000000000000) (-7146811000000000000000000000)) else (if n < 139 then (box (-6820233000000000000000000000) (-6819775000000000000000000000)) else (box (-6488686000000000000000000000) (-6488224000000000000000000000))))) else (if n < 143 then (if n < 141 then (box (-6152704000000000000000000000) (-6152238000000000000000000000)) else (if n < 142 then (box (-5812368000000000000000000000) (-5811898000000000000000000000)) else (box (-5467759000000000000000000000) (-5467285000000000000000000000)))) else (if n < 144 then (box (-5118960000000000000000000000) (-5118482000000000000000000000)) else (if n < 145 then (box (-4766053000000000000000000000) (-4765571000000000000000000000)) else (box (-4409121000000000000000000000) (-4408635000000000000000000000)))))) else (if n < 151 then (if n < 148 then (if n < 147 then (box (-4048248000000000000000000000) (-4047758000000000000000000000)) else (box (-3683517000000000000000000000) (-3683023000000000000000000000))) else (if n < 149 then (box (-3315013000000000000000000000) (-3314514000000000000000000000)) else (if n < 150 then (box (-2942819000000000000000000000) (-2942315000000000000000000000)) else (box (-2567020000000000000000000000) (-2566511000000000000000000000))))) else (if n < 154 then (if n < 152 then (box (-2187700000000000000000000000) (-2187186000000000000000000000)) else (if n < 153 then (box (-1804943000000000000000000000) (-1804425000000000000000000000)) else (box (-1418834000000000000000000000) (-1418312000000000000000000000)))) else (if n < 155 then (box (-1029457000000000000000000000) (-1028931000000000000000000000)) else (if n < 156 then (box (-636897000000000000000000000) (-636366000000000000000000000)) else (box (-241237000000000000000000000) (-240702000000000000000000000)))))))
def cK157_180 (n:Nat):IV:=(if n < 168 then (if n < 162 then (if n < 159 then (if n < 158 then (box (157438000000000000000000000) (157978000000000000000000000)) else (box (559045000000000000000000000) (559590000000000000000000000))) else (if n < 160 then (box (963501000000000000000000000) (964051000000000000000000000)) else (if n < 161 then (box (1370723000000000000000000000) (1371277000000000000000000000)) else (box (1780628000000000000000000000) (1781187000000000000000000000))))) else (if n < 165 then (if n < 163 then (box (2193134000000000000000000000) (2193698000000000000000000000)) else (if n < 164 then (box (2608160000000000000000000000) (2608729000000000000000000000)) else (box (3025625000000000000000000000) (3026198000000000000000000000)))) else (if n < 166 then (box (3445448000000000000000000000) (3446025000000000000000000000)) else (if n < 167 then (box (3867548000000000000000000000) (3868130000000000000000000000)) else (box (4291847000000000000000000000) (4292434000000000000000000000)))))) else (if n < 174 then (if n < 171 then (if n < 169 then (box (4718266000000000000000000000) (4718858000000000000000000000)) else (if n < 170 then (box (5146727000000000000000000000) (5147324000000000000000000000)) else (box (5577152000000000000000000000) (5577754000000000000000000000)))) else (if n < 172 then (box (6009465000000000000000000000) (6010072000000000000000000000)) else (if n < 173 then (box (6443590000000000000000000000) (6444201000000000000000000000)) else (box (6879451000000000000000000000) (6880067000000000000000000000))))) else (if n < 177 then (if n < 175 then (box (7316974000000000000000000000) (7317595000000000000000000000)) else (if n < 176 then (box (7756086000000000000000000000) (7756712000000000000000000000)) else (box (8196714000000000000000000000) (8197344000000000000000000000)))) else (if n < 178 then (box (8638786000000000000000000000) (8639420000000000000000000000)) else (if n < 179 then (box (9082230000000000000000000000) (9082869000000000000000000000)) else (box (9526977000000000000000000000) (9527620000000000000000000000)))))))
def cK135_180 (n:Nat):IV:=(if n < 157 then (cK135_157 n) else (cK157_180 n))
def cK90_180 (n:Nat):IV:=(if n < 135 then (cK90_135 n) else (cK135_180 n))
def cK0_180 (n:Nat):IV:=(if n < 90 then (cK0_90 n) else (cK90_180 n))
def cK180_202 (n:Nat):IV:=(if n < 191 then (if n < 185 then (if n < 182 then (if n < 181 then (box (9972957000000000000000000000) (9973604000000000000000000000)) else (box (10420101000000000000000000000) (10420752000000000000000000000))) else (if n < 183 then (box (10868342000000000000000000000) (10868997000000000000000000000)) else (if n < 184 then (box (11317612000000000000000000000) (11318272000000000000000000000)) else (box (11767846000000000000000000000) (11768511000000000000000000000))))) else (if n < 188 then (if n < 186 then (box (12218979000000000000000000000) (12219649000000000000000000000)) else (if n < 187 then (box (12670947000000000000000000000) (12671622000000000000000000000)) else (box (13123686000000000000000000000) (13124366000000000000000000000)))) else (if n < 189 then (box (13577135000000000000000000000) (13577819000000000000000000000)) else (if n < 190 then (box (14031231000000000000000000000) (14031920000000000000000000000)) else (box (14485914000000000000000000000) (14486608000000000000000000000)))))) else (if n < 196 then (if n < 193 then (if n < 192 then (box (14941124000000000000000000000) (14941823000000000000000000000)) else (box (15396803000000000000000000000) (15397506000000000000000000000))) else (if n < 194 then (box (15852892000000000000000000000) (15853600000000000000000000000)) else (if n < 195 then (box (16309334000000000000000000000) (16310047000000000000000000000)) else (box (16766073000000000000000000000) (16766791000000000000000000000))))) else (if n < 199 then (if n < 197 then (box (17223053000000000000000000000) (17223776000000000000000000000)) else (if n < 198 then (box (17680221000000000000000000000) (17680948000000000000000000000)) else (box (18137522000000000000000000000) (18138253000000000000000000000)))) else (if n < 200 then (box (18594903000000000000000000000) (18595639000000000000000000000)) else (if n < 201 then (box (19052312000000000000000000000) (19053053000000000000000000000)) else (box (19509698000000000000000000000) (19510444000000000000000000000)))))))
def cK202_225 (n:Nat):IV:=(if n < 213 then (if n < 207 then (if n < 204 then (if n < 203 then (box (19967011000000000000000000000) (19967761000000000000000000000)) else (box (20424201000000000000000000000) (20424955000000000000000000000))) else (if n < 205 then (box (20881218000000000000000000000) (20881977000000000000000000000)) else (if n < 206 then (box (21338015000000000000000000000) (21338779000000000000000000000)) else (box (21794544000000000000000000000) (21795313000000000000000000000))))) else (if n < 210 then (if n < 208 then (box (22250759000000000000000000000) (22251532000000000000000000000)) else (if n < 209 then (box (22706613000000000000000000000) (22707391000000000000000000000)) else (box (23162062000000000000000000000) (23162844000000000000000000000)))) else (if n < 211 then (box (23617060000000000000000000000) (23617847000000000000000000000)) else (if n < 212 then (box (24071564000000000000000000000) (24072356000000000000000000000)) else (box (24525531000000000000000000000) (24526328000000000000000000000)))))) else (if n < 219 then (if n < 216 then (if n < 214 then (box (24978918000000000000000000000) (24979720000000000000000000000)) else (if n < 215 then (box (25431684000000000000000000000) (25432490000000000000000000000)) else (box (25883787000000000000000000000) (25884598000000000000000000000)))) else (if n < 217 then (box (26335186000000000000000000000) (26336002000000000000000000000)) else (if n < 218 then (box (26785842000000000000000000000) (26786663000000000000000000000)) else (box (27235715000000000000000000000) (27236541000000000000000000000))))) else (if n < 222 then (if n < 220 then (box (27684766000000000000000000000) (27685597000000000000000000000)) else (if n < 221 then (box (28132958000000000000000000000) (28133793000000000000000000000)) else (box (28580252000000000000000000000) (28581092000000000000000000000)))) else (if n < 223 then (box (29026612000000000000000000000) (29027456000000000000000000000)) else (if n < 224 then (box (29472000000000000000000000000) (29472849000000000000000000000)) else (box (29916381000000000000000000000) (29917235000000000000000000000)))))))
def cK180_225 (n:Nat):IV:=(if n < 202 then (cK180_202 n) else (cK202_225 n))
def cK225_247 (n:Nat):IV:=(if n < 236 then (if n < 230 then (if n < 227 then (if n < 226 then (box (30359720000000000000000000000) (30360578000000000000000000000)) else (box (30801981000000000000000000000) (30802843000000000000000000000))) else (if n < 228 then (box (31243130000000000000000000000) (31243996000000000000000000000)) else (if n < 229 then (box (31683132000000000000000000000) (31684003000000000000000000000)) else (box (32121955000000000000000000000) (32122830000000000000000000000))))) else (if n < 233 then (if n < 231 then (box (32559564000000000000000000000) (32560444000000000000000000000)) else (if n < 232 then (box (32995928000000000000000000000) (32996812000000000000000000000)) else (box (33431014000000000000000000000) (33431903000000000000000000000)))) else (if n < 234 then (box (33864790000000000000000000000) (33865684000000000000000000000)) else (if n < 235 then (box (34297225000000000000000000000) (34298124000000000000000000000)) else (box (34728289000000000000000000000) (34729192000000000000000000000)))))) else (if n < 241 then (if n < 238 then (if n < 237 then (box (35157950000000000000000000000) (35158858000000000000000000000)) else (box (35586178000000000000000000000) (35587091000000000000000000000))) else (if n < 239 then (box (36012944000000000000000000000) (36013861000000000000000000000)) else (if n < 240 then (box (36438218000000000000000000000) (36439140000000000000000000000)) else (box (36861971000000000000000000000) (36862898000000000000000000000))))) else (if n < 244 then (if n < 242 then (box (37284175000000000000000000000) (37285106000000000000000000000)) else (if n < 243 then (box (37704801000000000000000000000) (37705736000000000000000000000)) else (box (38123821000000000000000000000) (38124760000000000000000000000)))) else (if n < 245 then (box (38541207000000000000000000000) (38542150000000000000000000000)) else (if n < 246 then (box (38956932000000000000000000000) (38957879000000000000000000000)) else (box (39370969000000000000000000000) (39371920000000000000000000000)))))))
def cK247_270 (n:Nat):IV:=(if n < 258 then (if n < 252 then (if n < 249 then (if n < 248 then (box (39783291000000000000000000000) (39784247000000000000000000000)) else (box (40193872000000000000000000000) (40194832000000000000000000000))) else (if n < 250 then (box (40602686000000000000000000000) (40603650000000000000000000000)) else (if n < 251 then (box (41009706000000000000000000000) (41010675000000000000000000000)) else (box (41414908000000000000000000000) (41415881000000000000000000000))))) else (if n < 255 then (if n < 253 then (box (41818265000000000000000000000) (41819243000000000000000000000)) else (if n < 254 then (box (42219753000000000000000000000) (42220736000000000000000000000)) else (box (42619347000000000000000000000) (42620335000000000000000000000)))) else (if n < 256 then (box (43017023000000000000000000000) (43018015000000000000000000000)) else (if n < 257 then (box (43412756000000000000000000000) (43413752000000000000000000000)) else (box (43806522000000000000000000000) (43807523000000000000000000000)))))) else (if n < 264 then (if n < 261 then (if n < 259 then (box (44198298000000000000000000000) (44199303000000000000000000000)) else (if n < 260 then (box (44588059000000000000000000000) (44589069000000000000000000000)) else (box (44975783000000000000000000000) (44976797000000000000000000000)))) else (if n < 262 then (box (45361446000000000000000000000) (45362464000000000000000000000)) else (if n < 263 then (box (45745025000000000000000000000) (45746048000000000000000000000)) else (box (46126497000000000000000000000) (46127525000000000000000000000))))) else (if n < 267 then (if n < 265 then (box (46505841000000000000000000000) (46506873000000000000000000000)) else (if n < 266 then (box (46883033000000000000000000000) (46884070000000000000000000000)) else (box (47258052000000000000000000000) (47259093000000000000000000000)))) else (if n < 268 then (box (47630875000000000000000000000) (47631921000000000000000000000)) else (if n < 269 then (box (48001481000000000000000000000) (48002531000000000000000000000)) else (box (48369848000000000000000000000) (48370902000000000000000000000)))))))
def cK225_270 (n:Nat):IV:=(if n < 247 then (cK225_247 n) else (cK247_270 n))
def cK180_270 (n:Nat):IV:=(if n < 225 then (cK180_225 n) else (cK225_270 n))
def cK270_292 (n:Nat):IV:=(if n < 281 then (if n < 275 then (if n < 272 then (if n < 271 then (box (48735955000000000000000000000) (48737013000000000000000000000)) else (box (49099780000000000000000000000) (49100843000000000000000000000))) else (if n < 273 then (box (49461303000000000000000000000) (49462370000000000000000000000)) else (if n < 274 then (box (49820502000000000000000000000) (49821573000000000000000000000)) else (box (50177357000000000000000000000) (50178432000000000000000000000))))) else (if n < 278 then (if n < 276 then (box (50531846000000000000000000000) (50532926000000000000000000000)) else (if n < 277 then (box (50883950000000000000000000000) (50885034000000000000000000000)) else (box (51233648000000000000000000000) (51234737000000000000000000000)))) else (if n < 279 then (box (51580920000000000000000000000) (51582014000000000000000000000)) else (if n < 280 then (box (51925746000000000000000000000) (51926844000000000000000000000)) else (box (52268106000000000000000000000) (52269208000000000000000000000)))))) else (if n < 286 then (if n < 283 then (if n < 282 then (box (52607980000000000000000000000) (52609086000000000000000000000)) else (box (52945348000000000000000000000) (52946459000000000000000000000))) else (if n < 284 then (box (53280192000000000000000000000) (53281307000000000000000000000)) else (if n < 285 then (box (53612491000000000000000000000) (53613610000000000000000000000)) else (box (53942226000000000000000000000) (53943349000000000000000000000))))) else (if n < 289 then (if n < 287 then (box (54269378000000000000000000000) (54270505000000000000000000000)) else (if n < 288 then (box (54593928000000000000000000000) (54595059000000000000000000000)) else (box (54915857000000000000000000000) (54916992000000000000000000000)))) else (if n < 290 then (box (55235146000000000000000000000) (55236285000000000000000000000)) else (if n < 291 then (box (55551776000000000000000000000) (55552919000000000000000000000)) else (box (55865728000000000000000000000) (55866876000000000000000000000)))))))
def cK292_315 (n:Nat):IV:=(if n < 303 then (if n < 297 then (if n < 294 then (if n < 293 then (box (56176984000000000000000000000) (56178136000000000000000000000)) else (box (56485525000000000000000000000) (56486682000000000000000000000))) else (if n < 295 then (box (56791333000000000000000000000) (56792495000000000000000000000)) else (if n < 296 then (box (57094390000000000000000000000) (57095556000000000000000000000)) else (box (57394677000000000000000000000) (57395848000000000000000000000))))) else (if n < 300 then (if n < 298 then (box (57692177000000000000000000000) (57693352000000000000000000000)) else (if n < 299 then (box (57986871000000000000000000000) (57988050000000000000000000000)) else (box (58278741000000000000000000000) (58279924000000000000000000000)))) else (if n < 301 then (box (58567769000000000000000000000) (58568956000000000000000000000)) else (if n < 302 then (box (58853937000000000000000000000) (58855129000000000000000000000)) else (box (59137228000000000000000000000) (59138424000000000000000000000)))))) else (if n < 309 then (if n < 306 then (if n < 304 then (box (59417624000000000000000000000) (59418824000000000000000000000)) else (if n < 305 then (box (59695107000000000000000000000) (59696311000000000000000000000)) else (box (59969659000000000000000000000) (59970868000000000000000000000)))) else (if n < 307 then (box (60241263000000000000000000000) (60242477000000000000000000000)) else (if n < 308 then (box (60509902000000000000000000000) (60511120000000000000000000000)) else (box (60775558000000000000000000000) (60776781000000000000000000000))))) else (if n < 312 then (if n < 310 then (box (61038214000000000000000000000) (61039441000000000000000000000)) else (if n < 311 then (box (61297853000000000000000000000) (61299084000000000000000000000)) else (box (61554457000000000000000000000) (61555692000000000000000000000)))) else (if n < 313 then (box (61808009000000000000000000000) (61809248000000000000000000000)) else (if n < 314 then (box (62058492000000000000000000000) (62059735000000000000000000000)) else (box (62305889000000000000000000000) (62307136000000000000000000000)))))))
def cK270_315 (n:Nat):IV:=(if n < 292 then (cK270_292 n) else (cK292_315 n))
def cK315_337 (n:Nat):IV:=(if n < 326 then (if n < 320 then (if n < 317 then (if n < 316 then (box (62550182000000000000000000000) (62551434000000000000000000000)) else (box (62791355000000000000000000000) (62792611000000000000000000000))) else (if n < 318 then (box (63029391000000000000000000000) (63030651000000000000000000000)) else (if n < 319 then (box (63264273000000000000000000000) (63265537000000000000000000000)) else (box (63495983000000000000000000000) (63497252000000000000000000000))))) else (if n < 323 then (if n < 321 then (box (63724506000000000000000000000) (63725779000000000000000000000)) else (if n < 322 then (box (63949824000000000000000000000) (63951101000000000000000000000)) else (box (64171920000000000000000000000) (64173201000000000000000000000)))) else (if n < 324 then (box (64390778000000000000000000000) (64392063000000000000000000000)) else (if n < 325 then (box (64606381000000000000000000000) (64607670000000000000000000000)) else (box (64818712000000000000000000000) (64820005000000000000000000000)))))) else (if n < 331 then (if n < 328 then (if n < 327 then (box (65027754000000000000000000000) (65029052000000000000000000000)) else (box (65233491000000000000000000000) (65234793000000000000000000000))) else (if n < 329 then (box (65435906000000000000000000000) (65437213000000000000000000000)) else (if n < 330 then (box (65634983000000000000000000000) (65636294000000000000000000000)) else (box (65830705000000000000000000000) (65832020000000000000000000000))))) else (if n < 334 then (if n < 332 then (box (66023055000000000000000000000) (66024374000000000000000000000)) else (if n < 333 then (box (66212017000000000000000000000) (66213340000000000000000000000)) else (box (66397574000000000000000000000) (66398902000000000000000000000)))) else (if n < 335 then (box (66579710000000000000000000000) (66581042000000000000000000000)) else (if n < 336 then (box (66758408000000000000000000000) (66759745000000000000000000000)) else (box (66933652000000000000000000000) (66934993000000000000000000000)))))))
def cK337_360 (n:Nat):IV:=(if n < 348 then (if n < 342 then (if n < 339 then (if n < 338 then (box (67105425000000000000000000000) (67106771000000000000000000000)) else (box (67273711000000000000000000000) (67275061000000000000000000000))) else (if n < 340 then (box (67438493000000000000000000000) (67439848000000000000000000000)) else (if n < 341 then (box (67599755000000000000000000000) (67601115000000000000000000000)) else (box (67757480000000000000000000000) (67758845000000000000000000000))))) else (if n < 345 then (if n < 343 then (box (67911652000000000000000000000) (67913022000000000000000000000)) else (if n < 344 then (box (68062255000000000000000000000) (68063630000000000000000000000)) else (box (68209272000000000000000000000) (68210652000000000000000000000)))) else (if n < 346 then (box (68352687000000000000000000000) (68354071000000000000000000000)) else (if n < 347 then (box (68492483000000000000000000000) (68493871000000000000000000000)) else (box (68628644000000000000000000000) (68630036000000000000000000000)))))) else (if n < 354 then (if n < 351 then (if n < 349 then (box (68761153000000000000000000000) (68762549000000000000000000000)) else (if n < 350 then (box (68889994000000000000000000000) (68891394000000000000000000000)) else (box (69015150000000000000000000000) (69016555000000000000000000000)))) else (if n < 352 then (box (69136605000000000000000000000) (69138015000000000000000000000)) else (if n < 353 then (box (69254343000000000000000000000) (69255757000000000000000000000)) else (box (69368347000000000000000000000) (69369765000000000000000000000))))) else (if n < 357 then (if n < 355 then (box (69478601000000000000000000000) (69480023000000000000000000000)) else (if n < 356 then (box (69585087000000000000000000000) (69586514000000000000000000000)) else (box (69687790000000000000000000000) (69689221000000000000000000000)))) else (if n < 358 then (box (69786693000000000000000000000) (69788129000000000000000000000)) else (if n < 359 then (box (69881780000000000000000000000) (69883220000000000000000000000)) else (box (69973034000000000000000000000) (69974478000000000000000000000)))))))
def cK315_360 (n:Nat):IV:=(if n < 337 then (cK315_337 n) else (cK337_360 n))
def cK270_360 (n:Nat):IV:=(if n < 315 then (cK270_315 n) else (cK315_360 n))
def cK180_360 (n:Nat):IV:=(if n < 270 then (cK180_270 n) else (cK270_360 n))
def cK0_360 (n:Nat):IV:=(if n < 180 then (cK0_180 n) else (cK180_360 n))
def cK360_382 (n:Nat):IV:=(if n < 371 then (if n < 365 then (if n < 362 then (if n < 361 then (box (70060438000000000000000000000) (70061887000000000000000000000)) else (box (70143976000000000000000000000) (70145430000000000000000000000))) else (if n < 363 then (box (70223632000000000000000000000) (70225090000000000000000000000)) else (if n < 364 then (box (70299388000000000000000000000) (70300851000000000000000000000)) else (box (70371229000000000000000000000) (70372696000000000000000000000))))) else (if n < 368 then (if n < 366 then (box (70439137000000000000000000000) (70440609000000000000000000000)) else (if n < 367 then (box (70503096000000000000000000000) (70504573000000000000000000000)) else (box (70563089000000000000000000000) (70564571000000000000000000000)))) else (if n < 369 then (box (70619100000000000000000000000) (70620587000000000000000000000)) else (if n < 370 then (box (70671112000000000000000000000) (70672604000000000000000000000)) else (box (70719108000000000000000000000) (70720605000000000000000000000)))))) else (if n < 376 then (if n < 373 then (if n < 372 then (box (70763072000000000000000000000) (70764573000000000000000000000)) else (box (70802986000000000000000000000) (70804492000000000000000000000))) else (if n < 374 then (box (70838834000000000000000000000) (70840345000000000000000000000)) else (if n < 375 then (box (70870599000000000000000000000) (70872115000000000000000000000)) else (box (70898264000000000000000000000) (70899785000000000000000000000))))) else (if n < 379 then (if n < 377 then (box (70921813000000000000000000000) (70923338000000000000000000000)) else (if n < 378 then (box (70941228000000000000000000000) (70942758000000000000000000000)) else (box (70956492000000000000000000000) (70958027000000000000000000000)))) else (if n < 380 then (box (70967589000000000000000000000) (70969129000000000000000000000)) else (if n < 381 then (box (70974501000000000000000000000) (70976046000000000000000000000)) else (box (70977212000000000000000000000) (70978762000000000000000000000)))))))
def cK382_405 (n:Nat):IV:=(if n < 393 then (if n < 387 then (if n < 384 then (if n < 383 then (box (70975704000000000000000000000) (70977259000000000000000000000)) else (box (70969960000000000000000000000) (70971520000000000000000000000))) else (if n < 385 then (box (70959964000000000000000000000) (70961528000000000000000000000)) else (if n < 386 then (box (70945698000000000000000000000) (70947267000000000000000000000)) else (box (70927144000000000000000000000) (70928718000000000000000000000))))) else (if n < 390 then (if n < 388 then (box (70904286000000000000000000000) (70905865000000000000000000000)) else (if n < 389 then (box (70877106000000000000000000000) (70878690000000000000000000000)) else (box (70845587000000000000000000000) (70847176000000000000000000000)))) else (if n < 391 then (box (70809712000000000000000000000) (70811306000000000000000000000)) else (if n < 392 then (box (70769463000000000000000000000) (70771062000000000000000000000)) else (box (70724823000000000000000000000) (70726427000000000000000000000)))))) else (if n < 399 then (if n < 396 then (if n < 394 then (box (70675774000000000000000000000) (70677383000000000000000000000)) else (if n < 395 then (box (70622299000000000000000000000) (70623913000000000000000000000)) else (box (70564380000000000000000000000) (70565999000000000000000000000)))) else (if n < 397 then (box (70502000000000000000000000000) (70503624000000000000000000000)) else (if n < 398 then (box (70435141000000000000000000000) (70436770000000000000000000000)) else (box (70363785000000000000000000000) (70365419000000000000000000000))))) else (if n < 402 then (if n < 400 then (box (70287915000000000000000000000) (70289554000000000000000000000)) else (if n < 401 then (box (70207512000000000000000000000) (70209156000000000000000000000)) else (box (70122559000000000000000000000) (70124208000000000000000000000)))) else (if n < 403 then (box (70033038000000000000000000000) (70034692000000000000000000000)) else (if n < 404 then (box (69938931000000000000000000000) (69940590000000000000000000000)) else (box (69840220000000000000000000000) (69841885000000000000000000000)))))))
def cK360_405 (n:Nat):IV:=(if n < 382 then (cK360_382 n) else (cK382_405 n))
def cK405_427 (n:Nat):IV:=(if n < 416 then (if n < 410 then (if n < 407 then (if n < 406 then (box (69736887000000000000000000000) (69738558000000000000000000000)) else (box (69628914000000000000000000000) (69630591000000000000000000000))) else (if n < 408 then (box (69516283000000000000000000000) (69517966000000000000000000000)) else (if n < 409 then (box (69398976000000000000000000000) (69400664000000000000000000000)) else (box (69276974000000000000000000000) (69278668000000000000000000000))))) else (if n < 413 then (if n < 411 then (box (69150259000000000000000000000) (69151959000000000000000000000)) else (if n < 412 then (box (69018813000000000000000000000) (69020519000000000000000000000)) else (box (68882618000000000000000000000) (68884329000000000000000000000)))) else (if n < 414 then (box (68741654000000000000000000000) (68743371000000000000000000000)) else (if n < 415 then (box (68595904000000000000000000000) (68597626000000000000000000000)) else (box (68445349000000000000000000000) (68447076000000000000000000000)))))) else (if n < 421 then (if n < 418 then (if n < 417 then (box (68289970000000000000000000000) (68291703000000000000000000000)) else (box (68129749000000000000000000000) (68131487000000000000000000000))) else (if n < 419 then (box (67964666000000000000000000000) (67966410000000000000000000000)) else (if n < 420 then (box (67794703000000000000000000000) (67796453000000000000000000000)) else (box (67619841000000000000000000000) (67621597000000000000000000000))))) else (if n < 424 then (if n < 422 then (box (67440061000000000000000000000) (67441823000000000000000000000)) else (if n < 423 then (box (67255345000000000000000000000) (67257113000000000000000000000)) else (box (67065673000000000000000000000) (67067447000000000000000000000)))) else (if n < 425 then (box (66871026000000000000000000000) (66872805000000000000000000000)) else (if n < 426 then (box (66671384000000000000000000000) (66673169000000000000000000000)) else (box (66466729000000000000000000000) (66468520000000000000000000000)))))))
def cK427_450 (n:Nat):IV:=(if n < 438 then (if n < 432 then (if n < 429 then (if n < 428 then (box (66257041000000000000000000000) (66258838000000000000000000000)) else (box (66042301000000000000000000000) (66044104000000000000000000000))) else (if n < 430 then (box (65822489000000000000000000000) (65824298000000000000000000000)) else (if n < 431 then (box (65597586000000000000000000000) (65599401000000000000000000000)) else (box (65367572000000000000000000000) (65369394000000000000000000000))))) else (if n < 435 then (if n < 433 then (box (65132428000000000000000000000) (65134256000000000000000000000)) else (if n < 434 then (box (64892134000000000000000000000) (64893968000000000000000000000)) else (box (64646670000000000000000000000) (64648510000000000000000000000)))) else (if n < 436 then (box (64396016000000000000000000000) (64397862000000000000000000000)) else (if n < 437 then (box (64140152000000000000000000000) (64142004000000000000000000000)) else (box (63879058000000000000000000000) (63880917000000000000000000000)))))) else (if n < 444 then (if n < 441 then (if n < 439 then (box (63612714000000000000000000000) (63614580000000000000000000000)) else (if n < 440 then (box (63341100000000000000000000000) (63342973000000000000000000000)) else (box (63064196000000000000000000000) (63066076000000000000000000000)))) else (if n < 442 then (box (62781982000000000000000000000) (62783868000000000000000000000)) else (if n < 443 then (box (62494437000000000000000000000) (62496329000000000000000000000)) else (box (62201541000000000000000000000) (62203439000000000000000000000))))) else (if n < 447 then (if n < 445 then (box (61903272000000000000000000000) (61905177000000000000000000000)) else (if n < 446 then (box (61599611000000000000000000000) (61601522000000000000000000000)) else (box (61290536000000000000000000000) (61292454000000000000000000000)))) else (if n < 448 then (box (60976027000000000000000000000) (60977952000000000000000000000)) else (if n < 449 then (box (60656063000000000000000000000) (60657995000000000000000000000)) else (box (60330623000000000000000000000) (60332562000000000000000000000)))))))
def cK405_450 (n:Nat):IV:=(if n < 427 then (cK405_427 n) else (cK427_450 n))
def cK360_450 (n:Nat):IV:=(if n < 405 then (cK360_405 n) else (cK405_450 n))
def cK450_472 (n:Nat):IV:=(if n < 461 then (if n < 455 then (if n < 452 then (if n < 451 then (box (59999686000000000000000000000) (60001632000000000000000000000)) else (box (59663231000000000000000000000) (59665183000000000000000000000))) else (if n < 453 then (box (59321236000000000000000000000) (59323195000000000000000000000)) else (if n < 454 then (box (58973681000000000000000000000) (58975646000000000000000000000)) else (box (58620544000000000000000000000) (58622516000000000000000000000))))) else (if n < 458 then (if n < 456 then (box (58261803000000000000000000000) (58263782000000000000000000000)) else (if n < 457 then (box (57897437000000000000000000000) (57899423000000000000000000000)) else (box (57527425000000000000000000000) (57529417000000000000000000000)))) else (if n < 459 then (box (57151744000000000000000000000) (57153743000000000000000000000)) else (if n < 460 then (box (56770373000000000000000000000) (56772379000000000000000000000)) else (box (56383290000000000000000000000) (56385303000000000000000000000)))))) else (if n < 466 then (if n < 463 then (if n < 462 then (box (55990473000000000000000000000) (55992493000000000000000000000)) else (box (55591900000000000000000000000) (55593927000000000000000000000))) else (if n < 464 then (box (55187548000000000000000000000) (55189582000000000000000000000)) else (if n < 465 then (box (54777396000000000000000000000) (54779437000000000000000000000)) else (box (54361421000000000000000000000) (54363469000000000000000000000))))) else (if n < 469 then (if n < 467 then (box (53939600000000000000000000000) (53941655000000000000000000000)) else (if n < 468 then (box (53511911000000000000000000000) (53513973000000000000000000000)) else (box (53078332000000000000000000000) (53080401000000000000000000000)))) else (if n < 470 then (box (52638839000000000000000000000) (52640915000000000000000000000)) else (if n < 471 then (box (52193410000000000000000000000) (52195493000000000000000000000)) else (box (51742022000000000000000000000) (51744112000000000000000000000)))))))
def cK472_495 (n:Nat):IV:=(if n < 483 then (if n < 477 then (if n < 474 then (if n < 473 then (box (51284652000000000000000000000) (51286749000000000000000000000)) else (box (50821276000000000000000000000) (50823381000000000000000000000))) else (if n < 475 then (box (50351872000000000000000000000) (50353984000000000000000000000)) else (if n < 476 then (box (49876416000000000000000000000) (49878535000000000000000000000)) else (box (49394884000000000000000000000) (49397011000000000000000000000))))) else (if n < 480 then (if n < 478 then (box (48907253000000000000000000000) (48909388000000000000000000000)) else (if n < 479 then (box (48413500000000000000000000000) (48415642000000000000000000000)) else (box (47913600000000000000000000000) (47915750000000000000000000000)))) else (if n < 481 then (box (47407530000000000000000000000) (47409688000000000000000000000)) else (if n < 482 then (box (46895266000000000000000000000) (46897432000000000000000000000)) else (box (46376784000000000000000000000) (46378958000000000000000000000)))))) else (if n < 489 then (if n < 486 then (if n < 484 then (box (45852060000000000000000000000) (45854241000000000000000000000)) else (if n < 485 then (box (45321069000000000000000000000) (45323258000000000000000000000)) else (box (44783787000000000000000000000) (44785984000000000000000000000)))) else (if n < 487 then (box (44240190000000000000000000000) (44242394000000000000000000000)) else (if n < 488 then (box (43690253000000000000000000000) (43692465000000000000000000000)) else (box (43133951000000000000000000000) (43136170000000000000000000000))))) else (if n < 492 then (if n < 490 then (box (42571259000000000000000000000) (42573485000000000000000000000)) else (if n < 491 then (box (42002152000000000000000000000) (42004386000000000000000000000)) else (box (41426606000000000000000000000) (41428848000000000000000000000)))) else (if n < 493 then (box (40844595000000000000000000000) (40846845000000000000000000000)) else (if n < 494 then (box (40256094000000000000000000000) (40258352000000000000000000000)) else (box (39661077000000000000000000000) (39663343000000000000000000000)))))))
def cK450_495 (n:Nat):IV:=(if n < 472 then (cK450_472 n) else (cK472_495 n))
def cK495_517 (n:Nat):IV:=(if n < 506 then (if n < 500 then (if n < 497 then (if n < 496 then (box (39059519000000000000000000000) (39061793000000000000000000000)) else (box (38451394000000000000000000000) (38453676000000000000000000000))) else (if n < 498 then (box (37836677000000000000000000000) (37838967000000000000000000000)) else (if n < 499 then (box (37215342000000000000000000000) (37217640000000000000000000000)) else (box (36587362000000000000000000000) (36589668000000000000000000000))))) else (if n < 503 then (if n < 501 then (box (35952711000000000000000000000) (35955026000000000000000000000)) else (if n < 502 then (box (35311364000000000000000000000) (35313687000000000000000000000)) else (box (34663294000000000000000000000) (34665625000000000000000000000)))) else (if n < 504 then (box (34008474000000000000000000000) (34010814000000000000000000000)) else (if n < 505 then (box (33346878000000000000000000000) (33349227000000000000000000000)) else (box (32678479000000000000000000000) (32680837000000000000000000000)))))) else (if n < 511 then (if n < 508 then (if n < 507 then (box (32003250000000000000000000000) (32005617000000000000000000000)) else (box (31321165000000000000000000000) (31323540000000000000000000000))) else (if n < 509 then (box (30632196000000000000000000000) (30634579000000000000000000000)) else (if n < 510 then (box (29936316000000000000000000000) (29938707000000000000000000000)) else (box (29233497000000000000000000000) (29235897000000000000000000000))))) else (if n < 514 then (if n < 512 then (box (28523712000000000000000000000) (28526121000000000000000000000)) else (if n < 513 then (box (27806934000000000000000000000) (27809352000000000000000000000)) else (box (27083135000000000000000000000) (27085561000000000000000000000)))) else (if n < 515 then (box (26352286000000000000000000000) (26354721000000000000000000000)) else (if n < 516 then (box (25614359000000000000000000000) (25616803000000000000000000000)) else (box (24869327000000000000000000000) (24871780000000000000000000000)))))))
def cK517_540 (n:Nat):IV:=(if n < 528 then (if n < 522 then (if n < 519 then (if n < 518 then (box (24117162000000000000000000000) (24119624000000000000000000000)) else (box (23357835000000000000000000000) (23360306000000000000000000000))) else (if n < 520 then (box (22591317000000000000000000000) (22593797000000000000000000000)) else (if n < 521 then (box (21817580000000000000000000000) (21820069000000000000000000000)) else (box (21036595000000000000000000000) (21039093000000000000000000000))))) else (if n < 525 then (if n < 523 then (box (20248332000000000000000000000) (20250839000000000000000000000)) else (if n < 524 then (box (19452763000000000000000000000) (19455279000000000000000000000)) else (box (18649858000000000000000000000) (18652384000000000000000000000)))) else (if n < 526 then (box (17839588000000000000000000000) (17842124000000000000000000000)) else (if n < 527 then (box (17021923000000000000000000000) (17024469000000000000000000000)) else (box (16196834000000000000000000000) (16199389000000000000000000000)))))) else (if n < 534 then (if n < 531 then (if n < 529 then (box (15364291000000000000000000000) (15366856000000000000000000000)) else (if n < 530 then (box (14524264000000000000000000000) (14526838000000000000000000000)) else (box (13676723000000000000000000000) (13679306000000000000000000000)))) else (if n < 532 then (box (12821638000000000000000000000) (12824230000000000000000000000)) else (if n < 533 then (box (11958977000000000000000000000) (11961579000000000000000000000)) else (box (11088710000000000000000000000) (11091322000000000000000000000))))) else (if n < 537 then (if n < 535 then (box (10210807000000000000000000000) (10213429000000000000000000000)) else (if n < 536 then (box (9325237000000000000000000000) (9327869000000000000000000000)) else (box (8431969000000000000000000000) (8434611000000000000000000000)))) else (if n < 538 then (box (7530972000000000000000000000) (7533624000000000000000000000)) else (if n < 539 then (box (6622214000000000000000000000) (6624876000000000000000000000)) else (box (5705664000000000000000000000) (5708336000000000000000000000)))))))
def cK495_540 (n:Nat):IV:=(if n < 517 then (cK495_517 n) else (cK517_540 n))
def cK450_540 (n:Nat):IV:=(if n < 495 then (cK450_495 n) else (cK495_540 n))
def cK360_540 (n:Nat):IV:=(if n < 450 then (cK360_450 n) else (cK450_540 n))
def cK540_562 (n:Nat):IV:=(if n < 551 then (if n < 545 then (if n < 542 then (if n < 541 then (box (4781291000000000000000000000) (4783973000000000000000000000)) else (box (3849062000000000000000000000) (3851754000000000000000000000))) else (if n < 543 then (box (2908946000000000000000000000) (2911648000000000000000000000)) else (if n < 544 then (box (1960910000000000000000000000) (1963622000000000000000000000)) else (box (1004922000000000000000000000) (1007644000000000000000000000))))) else (if n < 548 then (if n < 546 then (box (40950000000000000000000000) (43682000000000000000000000)) else (if n < 547 then (box (-931039000000000000000000000) (-928297000000000000000000000)) else (box (-1911078000000000000000000000) (-1908326000000000000000000000)))) else (if n < 549 then (box (-2899200000000000000000000000) (-2896438000000000000000000000)) else (if n < 550 then (box (-3895438000000000000000000000) (-3892665000000000000000000000)) else (box (-4899824000000000000000000000) (-4897041000000000000000000000)))))) else (if n < 556 then (if n < 553 then (if n < 552 then (box (-5912392000000000000000000000) (-5909599000000000000000000000)) else (box (-6933176000000000000000000000) (-6930373000000000000000000000))) else (if n < 554 then (box (-7962210000000000000000000000) (-7959397000000000000000000000)) else (if n < 555 then (box (-8999528000000000000000000000) (-8996705000000000000000000000)) else (box (-10045163000000000000000000000) (-10042330000000000000000000000))))) else (if n < 559 then (if n < 557 then (box (-11099151000000000000000000000) (-11096307000000000000000000000)) else (if n < 558 then (box (-12161525000000000000000000000) (-12158670000000000000000000000)) else (box (-13232320000000000000000000000) (-13229454000000000000000000000)))) else (if n < 560 then (box (-14311571000000000000000000000) (-14308694000000000000000000000)) else (if n < 561 then (box (-15399312000000000000000000000) (-15396425000000000000000000000)) else (box (-16495579000000000000000000000) (-16492681000000000000000000000)))))))
def cK562_585 (n:Nat):IV:=(if n < 573 then (if n < 567 then (if n < 564 then (if n < 563 then (box (-17600407000000000000000000000) (-17597498000000000000000000000)) else (box (-18713832000000000000000000000) (-18710912000000000000000000000))) else (if n < 565 then (box (-19835890000000000000000000000) (-19832959000000000000000000000)) else (if n < 566 then (box (-20966616000000000000000000000) (-20963674000000000000000000000)) else (box (-22106046000000000000000000000) (-22103093000000000000000000000))))) else (if n < 570 then (if n < 568 then (box (-23254217000000000000000000000) (-23251253000000000000000000000)) else (if n < 569 then (box (-24411165000000000000000000000) (-24408190000000000000000000000)) else (box (-25576926000000000000000000000) (-25573940000000000000000000000)))) else (if n < 571 then (box (-26751537000000000000000000000) (-26748540000000000000000000000)) else (if n < 572 then (box (-27935036000000000000000000000) (-27932027000000000000000000000)) else (box (-29127459000000000000000000000) (-29124439000000000000000000000)))))) else (if n < 579 then (if n < 576 then (if n < 574 then (box (-30328844000000000000000000000) (-30325812000000000000000000000)) else (if n < 575 then (box (-31539228000000000000000000000) (-31536185000000000000000000000)) else (box (-32758649000000000000000000000) (-32755594000000000000000000000)))) else (if n < 577 then (box (-33987144000000000000000000000) (-33984078000000000000000000000)) else (if n < 578 then (box (-35224752000000000000000000000) (-35221675000000000000000000000)) else (box (-36471511000000000000000000000) (-36468423000000000000000000000))))) else (if n < 582 then (if n < 580 then (box (-37727460000000000000000000000) (-37724360000000000000000000000)) else (if n < 581 then (box (-38992637000000000000000000000) (-38989525000000000000000000000)) else (box (-40267082000000000000000000000) (-40263958000000000000000000000)))) else (if n < 583 then (box (-41550833000000000000000000000) (-41547697000000000000000000000)) else (if n < 584 then (box (-42843929000000000000000000000) (-42840781000000000000000000000)) else (box (-44146410000000000000000000000) (-44143250000000000000000000000)))))))
def cK540_585 (n:Nat):IV:=(if n < 562 then (cK540_562 n) else (cK562_585 n))
def cK585_607 (n:Nat):IV:=(if n < 596 then (if n < 590 then (if n < 587 then (if n < 586 then (box (-45458315000000000000000000000) (-45455143000000000000000000000)) else (box (-46779686000000000000000000000) (-46776501000000000000000000000))) else (if n < 588 then (box (-48110562000000000000000000000) (-48107365000000000000000000000)) else (if n < 589 then (box (-49450982000000000000000000000) (-49447773000000000000000000000)) else (box (-50800988000000000000000000000) (-50797767000000000000000000000))))) else (if n < 593 then (if n < 591 then (box (-52160620000000000000000000000) (-52157387000000000000000000000)) else (if n < 592 then (box (-53529918000000000000000000000) (-53526673000000000000000000000)) else (box (-54908925000000000000000000000) (-54905667000000000000000000000)))) else (if n < 594 then (box (-56297681000000000000000000000) (-56294411000000000000000000000)) else (if n < 595 then (box (-57696228000000000000000000000) (-57692946000000000000000000000)) else (box (-59104609000000000000000000000) (-59101314000000000000000000000)))))) else (if n < 601 then (if n < 598 then (if n < 597 then (box (-60522864000000000000000000000) (-60519557000000000000000000000)) else (box (-61951036000000000000000000000) (-61947716000000000000000000000))) else (if n < 599 then (box (-63389167000000000000000000000) (-63385834000000000000000000000)) else (if n < 600 then (box (-64837300000000000000000000000) (-64833955000000000000000000000)) else (box (-66295478000000000000000000000) (-66292121000000000000000000000))))) else (if n < 604 then (if n < 602 then (box (-67763744000000000000000000000) (-67760375000000000000000000000)) else (if n < 603 then (box (-69242142000000000000000000000) (-69238760000000000000000000000)) else (box (-70730714000000000000000000000) (-70727319000000000000000000000)))) else (if n < 605 then (box (-72229505000000000000000000000) (-72226097000000000000000000000)) else (if n < 606 then (box (-73738558000000000000000000000) (-73735137000000000000000000000)) else (box (-75257918000000000000000000000) (-75254483000000000000000000000)))))))
def cK607_630 (n:Nat):IV:=(if n < 618 then (if n < 612 then (if n < 609 then (if n < 608 then (box (-76787629000000000000000000000) (-76784181000000000000000000000)) else (box (-78327736000000000000000000000) (-78324274000000000000000000000))) else (if n < 610 then (box (-79878282000000000000000000000) (-79874807000000000000000000000)) else (if n < 611 then (box (-81439313000000000000000000000) (-81435825000000000000000000000)) else (box (-83010876000000000000000000000) (-83007375000000000000000000000))))) else (if n < 615 then (if n < 613 then (box (-84593016000000000000000000000) (-84589501000000000000000000000)) else (if n < 614 then (box (-86185777000000000000000000000) (-86182249000000000000000000000)) else (box (-87789207000000000000000000000) (-87785665000000000000000000000)))) else (if n < 616 then (box (-89403351000000000000000000000) (-89399796000000000000000000000)) else (if n < 617 then (box (-91028256000000000000000000000) (-91024688000000000000000000000)) else (box (-92663969000000000000000000000) (-92660387000000000000000000000)))))) else (if n < 624 then (if n < 621 then (if n < 619 then (box (-94310537000000000000000000000) (-94306941000000000000000000000)) else (if n < 620 then (box (-95968008000000000000000000000) (-95964398000000000000000000000)) else (box (-97636428000000000000000000000) (-97632804000000000000000000000)))) else (if n < 622 then (box (-99315845000000000000000000000) (-99312207000000000000000000000)) else (if n < 623 then (box (-101006308000000000000000000000) (-101002655000000000000000000000)) else (box (-102707864000000000000000000000) (-102704196000000000000000000000))))) else (if n < 627 then (if n < 625 then (box (-104420562000000000000000000000) (-104416880000000000000000000000)) else (if n < 626 then (box (-106144452000000000000000000000) (-106140755000000000000000000000)) else (box (-107879581000000000000000000000) (-107875869000000000000000000000)))) else (if n < 628 then (box (-109625999000000000000000000000) (-109622272000000000000000000000)) else (if n < 629 then (box (-111383755000000000000000000000) (-111380013000000000000000000000)) else (box (-113152898000000000000000000000) (-113149142000000000000000000000)))))))
def cK585_630 (n:Nat):IV:=(if n < 607 then (cK585_607 n) else (cK607_630 n))
def cK540_630 (n:Nat):IV:=(if n < 585 then (cK540_585 n) else (cK585_630 n))
def cK630_652 (n:Nat):IV:=(if n < 641 then (if n < 635 then (if n < 632 then (if n < 631 then (box (-114933480000000000000000000000) (-114929709000000000000000000000)) else (box (-116725551000000000000000000000) (-116721765000000000000000000000))) else (if n < 633 then (box (-118529160000000000000000000000) (-118525360000000000000000000000)) else (if n < 634 then (box (-120344358000000000000000000000) (-120340544000000000000000000000)) else (box (-122171197000000000000000000000) (-122167369000000000000000000000))))) else (if n < 638 then (if n < 636 then (box (-124009728000000000000000000000) (-124005885000000000000000000000)) else (if n < 637 then (box (-125860003000000000000000000000) (-125856145000000000000000000000)) else (box (-127722074000000000000000000000) (-127718201000000000000000000000)))) else (if n < 639 then (box (-129595993000000000000000000000) (-129592105000000000000000000000)) else (if n < 640 then (box (-131481812000000000000000000000) (-131477908000000000000000000000)) else (box (-133379583000000000000000000000) (-133375664000000000000000000000)))))) else (if n < 646 then (if n < 643 then (if n < 642 then (box (-135289359000000000000000000000) (-135285425000000000000000000000)) else (box (-137211194000000000000000000000) (-137207245000000000000000000000))) else (if n < 644 then (box (-139145141000000000000000000000) (-139141177000000000000000000000)) else (if n < 645 then (box (-141091254000000000000000000000) (-141087274000000000000000000000)) else (box (-143049587000000000000000000000) (-143045592000000000000000000000))))) else (if n < 649 then (if n < 647 then (box (-145020194000000000000000000000) (-145016184000000000000000000000)) else (if n < 648 then (box (-147003130000000000000000000000) (-146999105000000000000000000000)) else (box (-148998450000000000000000000000) (-148994409000000000000000000000)))) else (if n < 650 then (box (-151006208000000000000000000000) (-151002151000000000000000000000)) else (if n < 651 then (box (-153026461000000000000000000000) (-153022388000000000000000000000)) else (box (-155059264000000000000000000000) (-155055175000000000000000000000)))))))
def cK652_675 (n:Nat):IV:=(if n < 663 then (if n < 657 then (if n < 654 then (if n < 653 then (box (-157104674000000000000000000000) (-157100569000000000000000000000)) else (box (-159162746000000000000000000000) (-159158625000000000000000000000))) else (if n < 655 then (box (-161233537000000000000000000000) (-161229399000000000000000000000)) else (if n < 656 then (box (-163317104000000000000000000000) (-163312949000000000000000000000)) else (box (-165413504000000000000000000000) (-165409332000000000000000000000))))) else (if n < 660 then (if n < 658 then (box (-167522794000000000000000000000) (-167518606000000000000000000000)) else (if n < 659 then (box (-169645032000000000000000000000) (-169640828000000000000000000000)) else (box (-171780277000000000000000000000) (-171776056000000000000000000000)))) else (if n < 661 then (box (-173928587000000000000000000000) (-173924349000000000000000000000)) else (if n < 662 then (box (-176090020000000000000000000000) (-176085766000000000000000000000)) else (box (-178264636000000000000000000000) (-178260366000000000000000000000)))))) else (if n < 669 then (if n < 666 then (if n < 664 then (box (-180452494000000000000000000000) (-180448207000000000000000000000)) else (if n < 665 then (box (-182653653000000000000000000000) (-182649349000000000000000000000)) else (box (-184868173000000000000000000000) (-184863852000000000000000000000)))) else (if n < 667 then (box (-187096114000000000000000000000) (-187091776000000000000000000000)) else (if n < 668 then (box (-189337537000000000000000000000) (-189333182000000000000000000000)) else (box (-191592503000000000000000000000) (-191588131000000000000000000000))))) else (if n < 672 then (if n < 670 then (box (-193861074000000000000000000000) (-193856684000000000000000000000)) else (if n < 671 then (box (-196143311000000000000000000000) (-196138904000000000000000000000)) else (box (-198439275000000000000000000000) (-198434850000000000000000000000)))) else (if n < 673 then (box (-200749027000000000000000000000) (-200744585000000000000000000000)) else (if n < 674 then (box (-203072632000000000000000000000) (-203068172000000000000000000000)) else (box (-205410152000000000000000000000) (-205405675000000000000000000000)))))))
def cK630_675 (n:Nat):IV:=(if n < 652 then (cK630_652 n) else (cK652_675 n))
def cK675_698 (n:Nat):IV:=(if n < 686 then (if n < 680 then (if n < 677 then (if n < 676 then (box (-207761651000000000000000000000) (-207757156000000000000000000000)) else (box (-210127191000000000000000000000) (-210122678000000000000000000000))) else (if n < 678 then (box (-212506836000000000000000000000) (-212502305000000000000000000000)) else (if n < 679 then (box (-214900649000000000000000000000) (-214896100000000000000000000000)) else (box (-217308696000000000000000000000) (-217304128000000000000000000000))))) else (if n < 683 then (if n < 681 then (box (-219731041000000000000000000000) (-219726455000000000000000000000)) else (if n < 682 then (box (-222167749000000000000000000000) (-222163145000000000000000000000)) else (box (-224618885000000000000000000000) (-224614263000000000000000000000)))) else (if n < 684 then (box (-227084517000000000000000000000) (-227079876000000000000000000000)) else (if n < 685 then (box (-229564709000000000000000000000) (-229560050000000000000000000000)) else (box (-232059528000000000000000000000) (-232054850000000000000000000000)))))) else (if n < 692 then (if n < 689 then (if n < 687 then (box (-234569041000000000000000000000) (-234564345000000000000000000000)) else (if n < 688 then (box (-237093316000000000000000000000) (-237088601000000000000000000000)) else (box (-239632419000000000000000000000) (-239627685000000000000000000000)))) else (if n < 690 then (box (-242186417000000000000000000000) (-242181664000000000000000000000)) else (if n < 691 then (box (-244755379000000000000000000000) (-244750607000000000000000000000)) else (box (-247339374000000000000000000000) (-247334583000000000000000000000))))) else (if n < 695 then (if n < 693 then (box (-249938472000000000000000000000) (-249933661000000000000000000000)) else (if n < 694 then (box (-252552741000000000000000000000) (-252547911000000000000000000000)) else (box (-255182252000000000000000000000) (-255177402000000000000000000000)))) else (if n < 696 then (box (-257827074000000000000000000000) (-257822205000000000000000000000)) else (if n < 697 then (box (-260487278000000000000000000000) (-260482389000000000000000000000)) else (box (-263162934000000000000000000000) (-263158025000000000000000000000)))))))
def cK698_721 (n:Nat):IV:=(if n < 709 then (if n < 703 then (if n < 700 then (if n < 699 then (box (-265854112000000000000000000000) (-265849183000000000000000000000)) else (box (-268560883000000000000000000000) (-268555934000000000000000000000))) else (if n < 701 then (box (-271283320000000000000000000000) (-271278351000000000000000000000)) else (if n < 702 then (box (-274021496000000000000000000000) (-274016507000000000000000000000)) else (box (-276775482000000000000000000000) (-276770473000000000000000000000))))) else (if n < 706 then (if n < 704 then (box (-279545352000000000000000000000) (-279540322000000000000000000000)) else (if n < 705 then (box (-282331179000000000000000000000) (-282326128000000000000000000000)) else (box (-285133037000000000000000000000) (-285127965000000000000000000000)))) else (if n < 707 then (box (-287950999000000000000000000000) (-287945907000000000000000000000)) else (if n < 708 then (box (-290785141000000000000000000000) (-290780028000000000000000000000)) else (box (-293635537000000000000000000000) (-293630403000000000000000000000)))))) else (if n < 715 then (if n < 712 then (if n < 710 then (box (-296502261000000000000000000000) (-296497106000000000000000000000)) else (if n < 711 then (box (-299385390000000000000000000000) (-299380215000000000000000000000)) else (box (-302285002000000000000000000000) (-302279806000000000000000000000)))) else (if n < 713 then (box (-305201172000000000000000000000) (-305195954000000000000000000000)) else (if n < 714 then (box (-308133975000000000000000000000) (-308128736000000000000000000000)) else (box (-311083490000000000000000000000) (-311078229000000000000000000000))))) else (if n < 718 then (if n < 716 then (box (-314049793000000000000000000000) (-314044510000000000000000000000)) else (if n < 717 then (box (-317032962000000000000000000000) (-317027657000000000000000000000)) else (box (-320033077000000000000000000000) (-320027751000000000000000000000)))) else (if n < 719 then (box (-323050216000000000000000000000) (-323044868000000000000000000000)) else (if n < 720 then (box (-326084457000000000000000000000) (-326079087000000000000000000000)) else (box (-329135882000000000000000000000) (-329130490000000000000000000000)))))))
def cK675_721 (n:Nat):IV:=(if n < 698 then (cK675_698 n) else (cK698_721 n))
def cK630_721 (n:Nat):IV:=(if n < 675 then (cK630_675 n) else (cK675_721 n))
def cK540_721 (n:Nat):IV:=(if n < 630 then (cK540_630 n) else (cK630_721 n))
def cK360_721 (n:Nat):IV:=(if n < 540 then (cK360_540 n) else (cK540_721 n))
def cK0_721 (n:Nat):IV:=(if n < 360 then (cK0_360 n) else (cK360_721 n))
def cC0_22 (n:Nat):IV:=(if n < 11 then (if n < 5 then (if n < 2 then (if n < 1 then (box (0) (0)) else (box (1415772000000000000000000000) (1415783000000000000000000000))) else (if n < 3 then (box (2831228000000000000000000000) (2831251000000000000000000000)) else (if n < 4 then (box (4246052000000000000000000000) (4246087000000000000000000000)) else (box (5659931000000000000000000000) (5659977000000000000000000000))))) else (if n < 8 then (if n < 6 then (box (7072547000000000000000000000) (7072605000000000000000000000)) else (if n < 7 then (box (8483587000000000000000000000) (8483656000000000000000000000)) else (box (9892733000000000000000000000) (9892814000000000000000000000)))) else (if n < 9 then (box (11299672000000000000000000000) (11299765000000000000000000000)) else (if n < 10 then (box (12704088000000000000000000000) (12704192000000000000000000000)) else (box (14105664000000000000000000000) (14105780000000000000000000000)))))) else (if n < 16 then (if n < 13 then (if n < 12 then (box (15504088000000000000000000000) (15504215000000000000000000000)) else (box (16899042000000000000000000000) (16899180000000000000000000000))) else (if n < 14 then (box (18290211000000000000000000000) (18290360000000000000000000000)) else (if n < 15 then (box (19677282000000000000000000000) (19677442000000000000000000000)) else (box (21059937000000000000000000000) (21060109000000000000000000000))))) else (if n < 19 then (if n < 17 then (box (22437863000000000000000000000) (22438047000000000000000000000)) else (if n < 18 then (box (23810745000000000000000000000) (23810941000000000000000000000)) else (box (25178269000000000000000000000) (25178476000000000000000000000)))) else (if n < 20 then (box (26540119000000000000000000000) (26540337000000000000000000000)) else (if n < 21 then (box (27895982000000000000000000000) (27896211000000000000000000000)) else (box (29245542000000000000000000000) (29245782000000000000000000000)))))))
def cC22_45 (n:Nat):IV:=(if n < 33 then (if n < 27 then (if n < 24 then (if n < 23 then (box (30588487000000000000000000000) (30588738000000000000000000000)) else (box (31924502000000000000000000000) (31924764000000000000000000000))) else (if n < 25 then (box (33253274000000000000000000000) (33253547000000000000000000000)) else (if n < 26 then (box (34574490000000000000000000000) (34574774000000000000000000000)) else (box (35887836000000000000000000000) (35888131000000000000000000000))))) else (if n < 30 then (if n < 28 then (box (37193001000000000000000000000) (37193306000000000000000000000)) else (if n < 29 then (box (38489671000000000000000000000) (38489987000000000000000000000)) else (box (39777535000000000000000000000) (39777862000000000000000000000)))) else (if n < 31 then (box (41056282000000000000000000000) (41056620000000000000000000000)) else (if n < 32 then (box (42325602000000000000000000000) (42325950000000000000000000000)) else (box (43585182000000000000000000000) (43585541000000000000000000000)))))) else (if n < 39 then (if n < 36 then (if n < 34 then (box (44834715000000000000000000000) (44835084000000000000000000000)) else (if n < 35 then (box (46073891000000000000000000000) (46074271000000000000000000000)) else (box (47302402000000000000000000000) (47302792000000000000000000000)))) else (if n < 37 then (box (48519940000000000000000000000) (48520340000000000000000000000)) else (if n < 38 then (box (49726199000000000000000000000) (49726609000000000000000000000)) else (box (50920872000000000000000000000) (50921292000000000000000000000))))) else (if n < 42 then (if n < 40 then (box (52103655000000000000000000000) (52104085000000000000000000000)) else (if n < 41 then (box (53274243000000000000000000000) (53274683000000000000000000000)) else (box (54432334000000000000000000000) (54432784000000000000000000000)))) else (if n < 43 then (box (55577627000000000000000000000) (55578086000000000000000000000)) else (if n < 44 then (box (56709821000000000000000000000) (56710289000000000000000000000)) else (box (57828616000000000000000000000) (57829093000000000000000000000)))))))
def cC0_45 (n:Nat):IV:=(if n < 22 then (cC0_22 n) else (cC22_45 n))
def cC45_67 (n:Nat):IV:=(if n < 56 then (if n < 50 then (if n < 47 then (if n < 46 then (box (58933715000000000000000000000) (58934202000000000000000000000)) else (box (60024822000000000000000000000) (60025318000000000000000000000))) else (if n < 48 then (box (61101642000000000000000000000) (61102147000000000000000000000)) else (if n < 49 then (box (62163882000000000000000000000) (62164396000000000000000000000)) else (box (63211251000000000000000000000) (63211774000000000000000000000))))) else (if n < 53 then (if n < 51 then (box (64243460000000000000000000000) (64243991000000000000000000000)) else (if n < 52 then (box (65260221000000000000000000000) (65260760000000000000000000000)) else (box (66261248000000000000000000000) (66261796000000000000000000000)))) else (if n < 54 then (box (67246259000000000000000000000) (67246815000000000000000000000)) else (if n < 55 then (box (68214973000000000000000000000) (68215537000000000000000000000)) else (box (69167111000000000000000000000) (69167683000000000000000000000)))))) else (if n < 61 then (if n < 58 then (if n < 57 then (box (70102397000000000000000000000) (70102977000000000000000000000)) else (box (71020559000000000000000000000) (71021147000000000000000000000))) else (if n < 59 then (box (71921325000000000000000000000) (71921920000000000000000000000)) else (if n < 60 then (box (72804427000000000000000000000) (72805030000000000000000000000)) else (box (73669602000000000000000000000) (73670212000000000000000000000))))) else (if n < 64 then (if n < 62 then (box (74516587000000000000000000000) (74517205000000000000000000000)) else (if n < 63 then (box (75345124000000000000000000000) (75345749000000000000000000000)) else (box (76154958000000000000000000000) (76155590000000000000000000000)))) else (if n < 65 then (box (76945838000000000000000000000) (76946477000000000000000000000)) else (if n < 66 then (box (77717516000000000000000000000) (77718162000000000000000000000)) else (box (78469748000000000000000000000) (78470400000000000000000000000)))))))
def cC67_90 (n:Nat):IV:=(if n < 78 then (if n < 72 then (if n < 69 then (if n < 68 then (box (79202293000000000000000000000) (79202952000000000000000000000)) else (box (79914916000000000000000000000) (79915581000000000000000000000))) else (if n < 70 then (box (80607384000000000000000000000) (80608056000000000000000000000)) else (if n < 71 then (box (81279471000000000000000000000) (81280149000000000000000000000)) else (box (81930953000000000000000000000) (81931637000000000000000000000))))) else (if n < 75 then (if n < 73 then (box (82561611000000000000000000000) (82562301000000000000000000000)) else (if n < 74 then (box (83171232000000000000000000000) (83171928000000000000000000000)) else (box (83759607000000000000000000000) (83760309000000000000000000000)))) else (if n < 76 then (box (84326532000000000000000000000) (84327240000000000000000000000)) else (if n < 77 then (box (84871808000000000000000000000) (84872522000000000000000000000)) else (box (85395242000000000000000000000) (85395962000000000000000000000)))))) else (if n < 84 then (if n < 81 then (if n < 79 then (box (85896646000000000000000000000) (85897371000000000000000000000)) else (if n < 80 then (box (86375837000000000000000000000) (86376568000000000000000000000)) else (box (86832639000000000000000000000) (86833375000000000000000000000)))) else (if n < 82 then (box (87266880000000000000000000000) (87267621000000000000000000000)) else (if n < 83 then (box (87678395000000000000000000000) (87679141000000000000000000000)) else (box (88067025000000000000000000000) (88067776000000000000000000000))))) else (if n < 87 then (if n < 85 then (box (88432618000000000000000000000) (88433373000000000000000000000)) else (if n < 86 then (box (88775026000000000000000000000) (88775785000000000000000000000)) else (box (89094109000000000000000000000) (89094872000000000000000000000)))) else (if n < 88 then (box (89389733000000000000000000000) (89390500000000000000000000000)) else (if n < 89 then (box (89661771000000000000000000000) (89662542000000000000000000000)) else (box (89910103000000000000000000000) (89910877000000000000000000000)))))))
def cC45_90 (n:Nat):IV:=(if n < 67 then (cC45_67 n) else (cC67_90 n))
def cC0_90 (n:Nat):IV:=(if n < 45 then (cC0_45 n) else (cC45_90 n))
def cC90_112 (n:Nat):IV:=(if n < 101 then (if n < 95 then (if n < 92 then (if n < 91 then (box (90134614000000000000000000000) (90135392000000000000000000000)) else (box (90335198000000000000000000000) (90335979000000000000000000000))) else (if n < 93 then (box (90511755000000000000000000000) (90512539000000000000000000000)) else (if n < 94 then (box (90664191000000000000000000000) (90664978000000000000000000000)) else (box (90792421000000000000000000000) (90793211000000000000000000000))))) else (if n < 98 then (if n < 96 then (box (90896365000000000000000000000) (90897158000000000000000000000)) else (if n < 97 then (box (90975952000000000000000000000) (90976748000000000000000000000)) else (box (91031118000000000000000000000) (91031917000000000000000000000)))) else (if n < 99 then (box (91061806000000000000000000000) (91062607000000000000000000000)) else (if n < 100 then (box (91067966000000000000000000000) (91068769000000000000000000000)) else (box (91049555000000000000000000000) (91050360000000000000000000000)))))) else (if n < 106 then (if n < 103 then (if n < 102 then (box (91006538000000000000000000000) (91007345000000000000000000000)) else (box (90938887000000000000000000000) (90939697000000000000000000000))) else (if n < 104 then (box (90846583000000000000000000000) (90847395000000000000000000000)) else (if n < 105 then (box (90729612000000000000000000000) (90730427000000000000000000000)) else (box (90587968000000000000000000000) (90588786000000000000000000000))))) else (if n < 109 then (if n < 107 then (box (90421654000000000000000000000) (90422475000000000000000000000)) else (if n < 108 then (box (90230678000000000000000000000) (90231502000000000000000000000)) else (box (90015057000000000000000000000) (90015884000000000000000000000)))) else (if n < 110 then (box (89774814000000000000000000000) (89775644000000000000000000000)) else (if n < 111 then (box (89509980000000000000000000000) (89510813000000000000000000000)) else (box (89220592000000000000000000000) (89221429000000000000000000000)))))))
def cC112_135 (n:Nat):IV:=(if n < 123 then (if n < 117 then (if n < 114 then (if n < 113 then (box (88906696000000000000000000000) (88907537000000000000000000000)) else (box (88568343000000000000000000000) (88569188000000000000000000000))) else (if n < 115 then (box (88205591000000000000000000000) (88206441000000000000000000000)) else (if n < 116 then (box (87818507000000000000000000000) (87819361000000000000000000000)) else (box (87407162000000000000000000000) (87408020000000000000000000000))))) else (if n < 120 then (if n < 118 then (box (86971634000000000000000000000) (86972497000000000000000000000)) else (if n < 119 then (box (86512009000000000000000000000) (86512877000000000000000000000)) else (box (86028378000000000000000000000) (86029251000000000000000000000)))) else (if n < 121 then (box (85520838000000000000000000000) (85521716000000000000000000000)) else (if n < 122 then (box (84989493000000000000000000000) (84990376000000000000000000000)) else (box (84434452000000000000000000000) (84435340000000000000000000000)))))) else (if n < 129 then (if n < 126 then (if n < 124 then (box (83855830000000000000000000000) (83856723000000000000000000000)) else (if n < 125 then (box (83253747000000000000000000000) (83254645000000000000000000000)) else (box (82628329000000000000000000000) (82629232000000000000000000000)))) else (if n < 127 then (box (81979707000000000000000000000) (81980616000000000000000000000)) else (if n < 128 then (box (81308017000000000000000000000) (81308932000000000000000000000)) else (box (80613399000000000000000000000) (80614320000000000000000000000))))) else (if n < 132 then (if n < 130 then (box (79895999000000000000000000000) (79896926000000000000000000000)) else (if n < 131 then (box (79155966000000000000000000000) (79156900000000000000000000000)) else (box (78393455000000000000000000000) (78394395000000000000000000000)))) else (if n < 133 then (box (77608623000000000000000000000) (77609570000000000000000000000)) else (if n < 134 then (box (76801632000000000000000000000) (76802586000000000000000000000)) else (box (75972647000000000000000000000) (75973608000000000000000000000)))))))
def cC90_135 (n:Nat):IV:=(if n < 112 then (cC90_112 n) else (cC112_135 n))
def cC135_157 (n:Nat):IV:=(if n < 146 then (if n < 140 then (if n < 137 then (if n < 136 then (box (75121837000000000000000000000) (75122805000000000000000000000)) else (box (74249373000000000000000000000) (74250348000000000000000000000))) else (if n < 138 then (box (73355431000000000000000000000) (73356413000000000000000000000)) else (if n < 139 then (box (72440187000000000000000000000) (72441176000000000000000000000)) else (box (71503821000000000000000000000) (71504817000000000000000000000))))) else (if n < 143 then (if n < 141 then (box (70546515000000000000000000000) (70547518000000000000000000000)) else (if n < 142 then (box (69568453000000000000000000000) (69569464000000000000000000000)) else (box (68569820000000000000000000000) (68570839000000000000000000000)))) else (if n < 144 then (box (67550805000000000000000000000) (67551832000000000000000000000)) else (if n < 145 then (box (66511595000000000000000000000) (66512630000000000000000000000)) else (box (65452381000000000000000000000) (65453424000000000000000000000)))))) else (if n < 151 then (if n < 148 then (if n < 147 then (box (64373353000000000000000000000) (64374404000000000000000000000)) else (box (63274703000000000000000000000) (63275762000000000000000000000))) else (if n < 149 then (box (62156623000000000000000000000) (62157690000000000000000000000)) else (if n < 150 then (box (61019304000000000000000000000) (61020379000000000000000000000)) else (box (59862939000000000000000000000) (59864023000000000000000000000))))) else (if n < 154 then (if n < 152 then (box (58687720000000000000000000000) (58688812000000000000000000000)) else (if n < 153 then (box (57493839000000000000000000000) (57494939000000000000000000000)) else (box (56281487000000000000000000000) (56282595000000000000000000000)))) else (if n < 155 then (box (55050854000000000000000000000) (55051970000000000000000000000)) else (if n < 156 then (box (53802130000000000000000000000) (53803255000000000000000000000)) else (box (52535504000000000000000000000) (52536638000000000000000000000)))))))
def cC157_180 (n:Nat):IV:=(if n < 168 then (if n < 162 then (if n < 159 then (if n < 158 then (box (51251162000000000000000000000) (51252305000000000000000000000)) else (box (49949292000000000000000000000) (49950444000000000000000000000))) else (if n < 160 then (box (48630076000000000000000000000) (48631237000000000000000000000)) else (if n < 161 then (box (47293698000000000000000000000) (47294868000000000000000000000)) else (box (45940337000000000000000000000) (45941517000000000000000000000))))) else (if n < 165 then (if n < 163 then (box (44570174000000000000000000000) (44571363000000000000000000000)) else (if n < 164 then (box (43183383000000000000000000000) (43184582000000000000000000000)) else (box (41780140000000000000000000000) (41781349000000000000000000000)))) else (if n < 166 then (box (40360616000000000000000000000) (40361834000000000000000000000)) else (if n < 167 then (box (38924981000000000000000000000) (38926208000000000000000000000)) else (box (37473400000000000000000000000) (37474636000000000000000000000)))))) else (if n < 174 then (if n < 171 then (if n < 169 then (box (36006038000000000000000000000) (36007284000000000000000000000)) else (if n < 170 then (box (34523055000000000000000000000) (34524311000000000000000000000)) else (box (33024611000000000000000000000) (33025876000000000000000000000)))) else (if n < 172 then (box (31510859000000000000000000000) (31512133000000000000000000000)) else (if n < 173 then (box (29981952000000000000000000000) (29983235000000000000000000000)) else (box (28438038000000000000000000000) (28439331000000000000000000000))))) else (if n < 177 then (if n < 175 then (box (26879263000000000000000000000) (26880566000000000000000000000)) else (if n < 176 then (box (25305769000000000000000000000) (25307082000000000000000000000)) else (box (23717695000000000000000000000) (23719018000000000000000000000)))) else (if n < 178 then (box (22115177000000000000000000000) (22116510000000000000000000000)) else (if n < 179 then (box (20498347000000000000000000000) (20499690000000000000000000000)) else (box (18867333000000000000000000000) (18868686000000000000000000000)))))))
def cC135_180 (n:Nat):IV:=(if n < 157 then (cC135_157 n) else (cC157_180 n))
def cC90_180 (n:Nat):IV:=(if n < 135 then (cC90_135 n) else (cC135_180 n))
def cC0_180 (n:Nat):IV:=(if n < 90 then (cC0_90 n) else (cC90_180 n))
def cC180_202 (n:Nat):IV:=(if n < 191 then (if n < 185 then (if n < 182 then (if n < 181 then (box (17222260000000000000000000000) (17223624000000000000000000000)) else (box (15563251000000000000000000000) (15564625000000000000000000000))) else (if n < 183 then (box (13890423000000000000000000000) (13891807000000000000000000000)) else (if n < 184 then (box (12203891000000000000000000000) (12205285000000000000000000000)) else (box (10503766000000000000000000000) (10505171000000000000000000000))))) else (if n < 188 then (if n < 186 then (box (8790155000000000000000000000) (8791571000000000000000000000)) else (if n < 187 then (box (7063163000000000000000000000) (7064590000000000000000000000)) else (box (5322891000000000000000000000) (5324328000000000000000000000)))) else (if n < 189 then (box (3569434000000000000000000000) (3570882000000000000000000000)) else (if n < 190 then (box (1802886000000000000000000000) (1804345000000000000000000000)) else (box (23338000000000000000000000) (24807000000000000000000000)))))) else (if n < 196 then (if n < 193 then (if n < 192 then (box (-1769124000000000000000000000) (-1767645000000000000000000000)) else (box (-3574418000000000000000000000) (-3572928000000000000000000000))) else (if n < 194 then (box (-5392464000000000000000000000) (-5390963000000000000000000000)) else (if n < 195 then (box (-7223185000000000000000000000) (-7221673000000000000000000000)) else (box (-9066510000000000000000000000) (-9064987000000000000000000000))))) else (if n < 199 then (if n < 197 then (box (-10922367000000000000000000000) (-10920834000000000000000000000)) else (if n < 198 then (box (-12790692000000000000000000000) (-12789148000000000000000000000)) else (box (-14671421000000000000000000000) (-14669866000000000000000000000)))) else (if n < 200 then (box (-16564494000000000000000000000) (-16562929000000000000000000000)) else (if n < 201 then (box (-18469855000000000000000000000) (-18468279000000000000000000000)) else (box (-20387451000000000000000000000) (-20385864000000000000000000000)))))))
def cC202_225 (n:Nat):IV:=(if n < 213 then (if n < 207 then (if n < 204 then (if n < 203 then (box (-22317231000000000000000000000) (-22315633000000000000000000000)) else (box (-24259147000000000000000000000) (-24257538000000000000000000000))) else (if n < 205 then (box (-26213155000000000000000000000) (-26211535000000000000000000000)) else (if n < 206 then (box (-28179214000000000000000000000) (-28177583000000000000000000000)) else (box (-30157285000000000000000000000) (-30155643000000000000000000000))))) else (if n < 210 then (if n < 208 then (box (-32147332000000000000000000000) (-32145679000000000000000000000)) else (if n < 209 then (box (-34149323000000000000000000000) (-34147659000000000000000000000)) else (box (-36163227000000000000000000000) (-36161552000000000000000000000)))) else (if n < 211 then (box (-38189017000000000000000000000) (-38187331000000000000000000000)) else (if n < 212 then (box (-40226667000000000000000000000) (-40224970000000000000000000000)) else (box (-42276156000000000000000000000) (-42274448000000000000000000000)))))) else (if n < 219 then (if n < 216 then (if n < 214 then (box (-44337463000000000000000000000) (-44335744000000000000000000000)) else (if n < 215 then (box (-46410571000000000000000000000) (-46408840000000000000000000000)) else (box (-48495466000000000000000000000) (-48493723000000000000000000000)))) else (if n < 217 then (box (-50592133000000000000000000000) (-50590379000000000000000000000)) else (if n < 218 then (box (-52700563000000000000000000000) (-52698798000000000000000000000)) else (box (-54820749000000000000000000000) (-54818973000000000000000000000))))) else (if n < 222 then (if n < 220 then (box (-56952684000000000000000000000) (-56950896000000000000000000000)) else (if n < 221 then (box (-59096365000000000000000000000) (-59094566000000000000000000000)) else (box (-61251790000000000000000000000) (-61249979000000000000000000000)))) else (if n < 223 then (box (-63418960000000000000000000000) (-63417138000000000000000000000)) else (if n < 224 then (box (-65597877000000000000000000000) (-65596044000000000000000000000)) else (box (-67788546000000000000000000000) (-67786701000000000000000000000)))))))
def cC180_225 (n:Nat):IV:=(if n < 202 then (cC180_202 n) else (cC202_225 n))
def cC225_247 (n:Nat):IV:=(if n < 236 then (if n < 230 then (if n < 227 then (if n < 226 then (box (-69990974000000000000000000000) (-69989117000000000000000000000)) else (box (-72205169000000000000000000000) (-72203300000000000000000000000))) else (if n < 228 then (box (-74431141000000000000000000000) (-74429261000000000000000000000)) else (if n < 229 then (box (-76668903000000000000000000000) (-76667011000000000000000000000)) else (box (-78918469000000000000000000000) (-78916565000000000000000000000))))) else (if n < 233 then (if n < 231 then (box (-81179853000000000000000000000) (-81177937000000000000000000000)) else (if n < 232 then (box (-83453073000000000000000000000) (-83451145000000000000000000000)) else (box (-85738149000000000000000000000) (-85736209000000000000000000000)))) else (if n < 234 then (box (-88035100000000000000000000000) (-88033148000000000000000000000)) else (if n < 235 then (box (-90343950000000000000000000000) (-90341986000000000000000000000)) else (box (-92664721000000000000000000000) (-92662746000000000000000000000)))))) else (if n < 241 then (if n < 238 then (if n < 237 then (box (-94997440000000000000000000000) (-94995453000000000000000000000)) else (box (-97342132000000000000000000000) (-97340134000000000000000000000))) else (if n < 239 then (box (-99698826000000000000000000000) (-99696817000000000000000000000)) else (if n < 240 then (box (-102067552000000000000000000000) (-102065531000000000000000000000)) else (box (-104448340000000000000000000000) (-104446308000000000000000000000))))) else (if n < 244 then (if n < 242 then (box (-106841224000000000000000000000) (-106839180000000000000000000000)) else (if n < 243 then (box (-109246236000000000000000000000) (-109244180000000000000000000000)) else (box (-111663411000000000000000000000) (-111661343000000000000000000000)))) else (if n < 245 then (box (-114092786000000000000000000000) (-114090706000000000000000000000)) else (if n < 246 then (box (-116534397000000000000000000000) (-116532305000000000000000000000)) else (box (-118988284000000000000000000000) (-118986181000000000000000000000)))))))
def cC247_270 (n:Nat):IV:=(if n < 258 then (if n < 252 then (if n < 249 then (if n < 248 then (box (-121454487000000000000000000000) (-121452372000000000000000000000)) else (box (-123933046000000000000000000000) (-123930919000000000000000000000))) else (if n < 250 then (box (-126424004000000000000000000000) (-126421865000000000000000000000)) else (if n < 251 then (box (-128927403000000000000000000000) (-128925252000000000000000000000)) else (box (-131443289000000000000000000000) (-131441126000000000000000000000))))) else (if n < 255 then (if n < 253 then (box (-133971706000000000000000000000) (-133969531000000000000000000000)) else (if n < 254 then (box (-136512702000000000000000000000) (-136510515000000000000000000000)) else (box (-139066323000000000000000000000) (-139064124000000000000000000000)))) else (if n < 256 then (box (-141632618000000000000000000000) (-141630407000000000000000000000)) else (if n < 257 then (box (-144211636000000000000000000000) (-144209413000000000000000000000)) else (box (-146803428000000000000000000000) (-146801193000000000000000000000)))))) else (if n < 264 then (if n < 261 then (if n < 259 then (box (-149408045000000000000000000000) (-149405798000000000000000000000)) else (if n < 260 then (box (-152025539000000000000000000000) (-152023280000000000000000000000)) else (box (-154655965000000000000000000000) (-154653694000000000000000000000)))) else (if n < 262 then (box (-157299376000000000000000000000) (-157297093000000000000000000000)) else (if n < 263 then (box (-159955827000000000000000000000) (-159953532000000000000000000000)) else (box (-162625373000000000000000000000) (-162623066000000000000000000000))))) else (if n < 267 then (if n < 265 then (box (-165308072000000000000000000000) (-165305753000000000000000000000)) else (if n < 266 then (box (-168003982000000000000000000000) (-168001651000000000000000000000)) else (box (-170713160000000000000000000000) (-170710817000000000000000000000)))) else (if n < 268 then (box (-173435666000000000000000000000) (-173433311000000000000000000000)) else (if n < 269 then (box (-176171560000000000000000000000) (-176169193000000000000000000000)) else (box (-178920902000000000000000000000) (-178918523000000000000000000000)))))))
def cC225_270 (n:Nat):IV:=(if n < 247 then (cC225_247 n) else (cC247_270 n))
def cC180_270 (n:Nat):IV:=(if n < 225 then (cC180_225 n) else (cC225_270 n))
def cC270_292 (n:Nat):IV:=(if n < 281 then (if n < 275 then (if n < 272 then (if n < 271 then (box (-181683755000000000000000000000) (-181681364000000000000000000000)) else (box (-184460181000000000000000000000) (-184457778000000000000000000000))) else (if n < 273 then (box (-187250242000000000000000000000) (-187247827000000000000000000000)) else (if n < 274 then (box (-190054003000000000000000000000) (-190051575000000000000000000000)) else (box (-192871528000000000000000000000) (-192869088000000000000000000000))))) else (if n < 278 then (if n < 276 then (box (-195702882000000000000000000000) (-195700430000000000000000000000)) else (if n < 277 then (box (-198548132000000000000000000000) (-198545668000000000000000000000)) else (box (-201407343000000000000000000000) (-201404867000000000000000000000)))) else (if n < 279 then (box (-204280585000000000000000000000) (-204278096000000000000000000000)) else (if n < 280 then (box (-207167924000000000000000000000) (-207165423000000000000000000000)) else (box (-210069429000000000000000000000) (-210066916000000000000000000000)))))) else (if n < 286 then (if n < 283 then (if n < 282 then (box (-212985170000000000000000000000) (-212982645000000000000000000000)) else (box (-215915216000000000000000000000) (-215912679000000000000000000000))) else (if n < 284 then (box (-218859639000000000000000000000) (-218857090000000000000000000000)) else (if n < 285 then (box (-221818510000000000000000000000) (-221815948000000000000000000000)) else (box (-224791900000000000000000000000) (-224789326000000000000000000000))))) else (if n < 289 then (if n < 287 then (box (-227779882000000000000000000000) (-227777296000000000000000000000)) else (if n < 288 then (box (-230782530000000000000000000000) (-230779932000000000000000000000)) else (box (-233799917000000000000000000000) (-233797307000000000000000000000)))) else (if n < 290 then (box (-236832118000000000000000000000) (-236829495000000000000000000000)) else (if n < 291 then (box (-239879208000000000000000000000) (-239876572000000000000000000000)) else (box (-242941262000000000000000000000) (-242938614000000000000000000000)))))))
def cC292_315 (n:Nat):IV:=(if n < 303 then (if n < 297 then (if n < 294 then (if n < 293 then (box (-246018356000000000000000000000) (-246015696000000000000000000000)) else (box (-249110568000000000000000000000) (-249107895000000000000000000000))) else (if n < 295 then (box (-252217975000000000000000000000) (-252215290000000000000000000000)) else (if n < 296 then (box (-255340655000000000000000000000) (-255337957000000000000000000000)) else (box (-258478686000000000000000000000) (-258475975000000000000000000000))))) else (if n < 300 then (if n < 298 then (box (-261632147000000000000000000000) (-261629423000000000000000000000)) else (if n < 299 then (box (-264801119000000000000000000000) (-264798382000000000000000000000)) else (box (-267985680000000000000000000000) (-267982930000000000000000000000)))) else (if n < 301 then (box (-271185912000000000000000000000) (-271183150000000000000000000000)) else (if n < 302 then (box (-274401897000000000000000000000) (-274399122000000000000000000000)) else (box (-277633715000000000000000000000) (-277630928000000000000000000000)))))) else (if n < 309 then (if n < 306 then (if n < 304 then (box (-280881450000000000000000000000) (-280878651000000000000000000000)) else (if n < 305 then (box (-284145185000000000000000000000) (-284142373000000000000000000000)) else (box (-287425003000000000000000000000) (-287422178000000000000000000000)))) else (if n < 307 then (box (-290720987000000000000000000000) (-290718149000000000000000000000)) else (if n < 308 then (box (-294033223000000000000000000000) (-294030372000000000000000000000)) else (box (-297361796000000000000000000000) (-297358932000000000000000000000))))) else (if n < 312 then (if n < 310 then (box (-300706791000000000000000000000) (-300703914000000000000000000000)) else (if n < 311 then (box (-304068293000000000000000000000) (-304065404000000000000000000000)) else (box (-307446391000000000000000000000) (-307443489000000000000000000000)))) else (if n < 313 then (box (-310841171000000000000000000000) (-310838256000000000000000000000)) else (if n < 314 then (box (-314252720000000000000000000000) (-314249793000000000000000000000)) else (box (-317681127000000000000000000000) (-317678187000000000000000000000)))))))
def cC270_315 (n:Nat):IV:=(if n < 292 then (cC270_292 n) else (cC292_315 n))
def cC315_337 (n:Nat):IV:=(if n < 326 then (if n < 320 then (if n < 317 then (if n < 316 then (box (-321126480000000000000000000000) (-321123527000000000000000000000)) else (box (-324588870000000000000000000000) (-324585904000000000000000000000))) else (if n < 318 then (box (-328068385000000000000000000000) (-328065406000000000000000000000)) else (if n < 319 then (box (-331565115000000000000000000000) (-331562123000000000000000000000)) else (box (-335079152000000000000000000000) (-335076147000000000000000000000))))) else (if n < 323 then (if n < 321 then (box (-338610587000000000000000000000) (-338607569000000000000000000000)) else (if n < 322 then (box (-342159511000000000000000000000) (-342156480000000000000000000000)) else (box (-345726017000000000000000000000) (-345722973000000000000000000000)))) else (if n < 324 then (box (-349310198000000000000000000000) (-349307141000000000000000000000)) else (if n < 325 then (box (-352912147000000000000000000000) (-352909077000000000000000000000)) else (box (-356531957000000000000000000000) (-356528874000000000000000000000)))))) else (if n < 331 then (if n < 328 then (if n < 327 then (box (-360169722000000000000000000000) (-360166626000000000000000000000)) else (box (-363825539000000000000000000000) (-363822430000000000000000000000))) else (if n < 329 then (box (-367499501000000000000000000000) (-367496379000000000000000000000)) else (if n < 330 then (box (-371191705000000000000000000000) (-371188570000000000000000000000)) else (box (-374902248000000000000000000000) (-374899099000000000000000000000))))) else (if n < 334 then (if n < 332 then (box (-378631225000000000000000000000) (-378628062000000000000000000000)) else (if n < 333 then (box (-382378734000000000000000000000) (-382375558000000000000000000000)) else (box (-386144873000000000000000000000) (-386141684000000000000000000000)))) else (if n < 335 then (box (-389929740000000000000000000000) (-389926538000000000000000000000)) else (if n < 336 then (box (-393733434000000000000000000000) (-393730219000000000000000000000)) else (box (-397556055000000000000000000000) (-397552826000000000000000000000)))))))
def cC337_360 (n:Nat):IV:=(if n < 348 then (if n < 342 then (if n < 339 then (if n < 338 then (box (-401397701000000000000000000000) (-401394459000000000000000000000)) else (box (-405258473000000000000000000000) (-405255218000000000000000000000))) else (if n < 340 then (box (-409138473000000000000000000000) (-409135205000000000000000000000)) else (if n < 341 then (box (-413037802000000000000000000000) (-413034521000000000000000000000)) else (box (-416956561000000000000000000000) (-416953267000000000000000000000))))) else (if n < 345 then (if n < 343 then (box (-420894853000000000000000000000) (-420891546000000000000000000000)) else (if n < 344 then (box (-424852780000000000000000000000) (-424849460000000000000000000000)) else (box (-428830446000000000000000000000) (-428827113000000000000000000000)))) else (if n < 346 then (box (-432827956000000000000000000000) (-432824610000000000000000000000)) else (if n < 347 then (box (-436845412000000000000000000000) (-436842053000000000000000000000)) else (box (-440882921000000000000000000000) (-440879549000000000000000000000)))))) else (if n < 354 then (if n < 351 then (if n < 349 then (box (-444940587000000000000000000000) (-444937202000000000000000000000)) else (if n < 350 then (box (-449018517000000000000000000000) (-449015119000000000000000000000)) else (box (-453116816000000000000000000000) (-453113405000000000000000000000)))) else (if n < 352 then (box (-457235592000000000000000000000) (-457232168000000000000000000000)) else (if n < 353 then (box (-461374953000000000000000000000) (-461371516000000000000000000000)) else (box (-465535006000000000000000000000) (-465531555000000000000000000000))))) else (if n < 357 then (if n < 355 then (box (-469715860000000000000000000000) (-469712396000000000000000000000)) else (if n < 356 then (box (-473917623000000000000000000000) (-473914146000000000000000000000)) else (box (-478140406000000000000000000000) (-478136916000000000000000000000)))) else (if n < 358 then (box (-482384319000000000000000000000) (-482380815000000000000000000000)) else (if n < 359 then (box (-486649472000000000000000000000) (-486645955000000000000000000000)) else (box (-490935976000000000000000000000) (-490932446000000000000000000000)))))))
def cC315_360 (n:Nat):IV:=(if n < 337 then (cC315_337 n) else (cC337_360 n))
def cC270_360 (n:Nat):IV:=(if n < 315 then (cC270_315 n) else (cC315_360 n))
def cC180_360 (n:Nat):IV:=(if n < 270 then (cC180_270 n) else (cC270_360 n))
def cC0_360 (n:Nat):IV:=(if n < 180 then (cC0_180 n) else (cC180_360 n))
def cC360_382 (n:Nat):IV:=(if n < 371 then (if n < 365 then (if n < 362 then (if n < 361 then (box (-495243943000000000000000000000) (-495240400000000000000000000000)) else (box (-499573486000000000000000000000) (-499569929000000000000000000000))) else (if n < 363 then (box (-503924717000000000000000000000) (-503921146000000000000000000000)) else (if n < 364 then (box (-508297749000000000000000000000) (-508294164000000000000000000000)) else (box (-512692696000000000000000000000) (-512689097000000000000000000000))))) else (if n < 368 then (if n < 366 then (box (-517109672000000000000000000000) (-517106060000000000000000000000)) else (if n < 367 then (box (-521548793000000000000000000000) (-521545167000000000000000000000)) else (box (-526010173000000000000000000000) (-526006533000000000000000000000)))) else (if n < 369 then (box (-530493930000000000000000000000) (-530490276000000000000000000000)) else (if n < 370 then (box (-535000178000000000000000000000) (-534996511000000000000000000000)) else (box (-539529037000000000000000000000) (-539525356000000000000000000000)))))) else (if n < 376 then (if n < 373 then (if n < 372 then (box (-544080622000000000000000000000) (-544076927000000000000000000000)) else (box (-548655053000000000000000000000) (-548651344000000000000000000000))) else (if n < 374 then (box (-553252448000000000000000000000) (-553248725000000000000000000000)) else (if n < 375 then (box (-557872926000000000000000000000) (-557869189000000000000000000000)) else (box (-562516608000000000000000000000) (-562512857000000000000000000000))))) else (if n < 379 then (if n < 377 then (box (-567183614000000000000000000000) (-567179849000000000000000000000)) else (if n < 378 then (box (-571874064000000000000000000000) (-571870285000000000000000000000)) else (box (-576588081000000000000000000000) (-576584288000000000000000000000)))) else (if n < 380 then (box (-581325787000000000000000000000) (-581321980000000000000000000000)) else (if n < 381 then (box (-586087304000000000000000000000) (-586083483000000000000000000000)) else (box (-590872756000000000000000000000) (-590868921000000000000000000000)))))))
def cC382_405 (n:Nat):IV:=(if n < 393 then (if n < 387 then (if n < 384 then (if n < 383 then (box (-595682267000000000000000000000) (-595678418000000000000000000000)) else (box (-600515960000000000000000000000) (-600512097000000000000000000000))) else (if n < 385 then (box (-605373962000000000000000000000) (-605370085000000000000000000000)) else (if n < 386 then (box (-610256397000000000000000000000) (-610252506000000000000000000000)) else (box (-615163393000000000000000000000) (-615159488000000000000000000000))))) else (if n < 390 then (if n < 388 then (box (-620095077000000000000000000000) (-620091157000000000000000000000)) else (if n < 389 then (box (-625051575000000000000000000000) (-625047641000000000000000000000)) else (box (-630033015000000000000000000000) (-630029067000000000000000000000)))) else (if n < 391 then (box (-635039526000000000000000000000) (-635035564000000000000000000000)) else (if n < 392 then (box (-640071238000000000000000000000) (-640067262000000000000000000000)) else (box (-645128280000000000000000000000) (-645124290000000000000000000000)))))) else (if n < 399 then (if n < 396 then (if n < 394 then (box (-650210784000000000000000000000) (-650206779000000000000000000000)) else (if n < 395 then (box (-655318879000000000000000000000) (-655314860000000000000000000000)) else (box (-660452698000000000000000000000) (-660448665000000000000000000000)))) else (if n < 397 then (box (-665612373000000000000000000000) (-665608326000000000000000000000)) else (if n < 398 then (box (-670798037000000000000000000000) (-670793976000000000000000000000)) else (box (-676009824000000000000000000000) (-676005749000000000000000000000))))) else (if n < 402 then (if n < 400 then (box (-681247869000000000000000000000) (-681243779000000000000000000000)) else (if n < 401 then (box (-686512305000000000000000000000) (-686508200000000000000000000000)) else (box (-691803269000000000000000000000) (-691799149000000000000000000000)))) else (if n < 403 then (box (-697120896000000000000000000000) (-697116761000000000000000000000)) else (if n < 404 then (box (-702465323000000000000000000000) (-702461173000000000000000000000)) else (box (-707836687000000000000000000000) (-707832523000000000000000000000)))))))
def cC360_405 (n:Nat):IV:=(if n < 382 then (cC360_382 n) else (cC382_405 n))
def cC405_427 (n:Nat):IV:=(if n < 416 then (if n < 410 then (if n < 407 then (if n < 406 then (box (-713235127000000000000000000000) (-713230949000000000000000000000)) else (box (-718660781000000000000000000000) (-718656589000000000000000000000))) else (if n < 408 then (box (-724113790000000000000000000000) (-724109583000000000000000000000)) else (if n < 409 then (box (-729594292000000000000000000000) (-729590071000000000000000000000)) else (box (-735102429000000000000000000000) (-735098194000000000000000000000))))) else (if n < 413 then (if n < 411 then (box (-740638342000000000000000000000) (-740634092000000000000000000000)) else (if n < 412 then (box (-746202173000000000000000000000) (-746197908000000000000000000000)) else (box (-751794065000000000000000000000) (-751789786000000000000000000000)))) else (if n < 414 then (box (-757414161000000000000000000000) (-757409867000000000000000000000)) else (if n < 415 then (box (-763062605000000000000000000000) (-763058296000000000000000000000)) else (box (-768739542000000000000000000000) (-768735219000000000000000000000)))))) else (if n < 421 then (if n < 418 then (if n < 417 then (box (-774445118000000000000000000000) (-774440780000000000000000000000)) else (box (-780179479000000000000000000000) (-780175126000000000000000000000))) else (if n < 419 then (box (-785942771000000000000000000000) (-785938404000000000000000000000)) else (if n < 420 then (box (-791735142000000000000000000000) (-791730760000000000000000000000)) else (box (-797556741000000000000000000000) (-797552345000000000000000000000))))) else (if n < 424 then (if n < 422 then (box (-803407716000000000000000000000) (-803403305000000000000000000000)) else (if n < 423 then (box (-809288217000000000000000000000) (-809283791000000000000000000000)) else (box (-815198394000000000000000000000) (-815193953000000000000000000000)))) else (if n < 425 then (box (-821138399000000000000000000000) (-821133943000000000000000000000)) else (if n < 426 then (box (-827108383000000000000000000000) (-827103912000000000000000000000)) else (box (-833108499000000000000000000000) (-833104013000000000000000000000)))))))
def cC427_450 (n:Nat):IV:=(if n < 438 then (if n < 432 then (if n < 429 then (if n < 428 then (box (-839138899000000000000000000000) (-839134398000000000000000000000)) else (box (-845199739000000000000000000000) (-845195223000000000000000000000))) else (if n < 430 then (box (-851291172000000000000000000000) (-851286641000000000000000000000)) else (if n < 431 then (box (-857413355000000000000000000000) (-857408808000000000000000000000)) else (box (-863566443000000000000000000000) (-863561881000000000000000000000))))) else (if n < 435 then (if n < 433 then (box (-869750594000000000000000000000) (-869746016000000000000000000000)) else (if n < 434 then (box (-875965964000000000000000000000) (-875961371000000000000000000000)) else (box (-882212714000000000000000000000) (-882208106000000000000000000000)))) else (if n < 436 then (box (-888491001000000000000000000000) (-888486378000000000000000000000)) else (if n < 437 then (box (-894800986000000000000000000000) (-894796348000000000000000000000)) else (box (-901142829000000000000000000000) (-901138176000000000000000000000)))))) else (if n < 444 then (if n < 441 then (if n < 439 then (box (-907516692000000000000000000000) (-907512024000000000000000000000)) else (if n < 440 then (box (-913922739000000000000000000000) (-913918056000000000000000000000)) else (box (-920361131000000000000000000000) (-920356433000000000000000000000)))) else (if n < 442 then (box (-926832033000000000000000000000) (-926827319000000000000000000000)) else (if n < 443 then (box (-933335609000000000000000000000) (-933330880000000000000000000000)) else (box (-939872024000000000000000000000) (-939867280000000000000000000000))))) else (if n < 447 then (if n < 445 then (box (-946441446000000000000000000000) (-946436686000000000000000000000)) else (if n < 446 then (box (-953044041000000000000000000000) (-953039265000000000000000000000)) else (box (-959679976000000000000000000000) (-959675185000000000000000000000)))) else (if n < 448 then (box (-966349422000000000000000000000) (-966344615000000000000000000000)) else (if n < 449 then (box (-973052545000000000000000000000) (-973047723000000000000000000000)) else (box (-979789519000000000000000000000) (-979784681000000000000000000000)))))))
def cC405_450 (n:Nat):IV:=(if n < 427 then (cC405_427 n) else (cC427_450 n))
def cC360_450 (n:Nat):IV:=(if n < 405 then (cC360_405 n) else (cC405_450 n))
def cC450_472 (n:Nat):IV:=(if n < 461 then (if n < 455 then (if n < 452 then (if n < 451 then (box (-986560514000000000000000000000) (-986555660000000000000000000000)) else (box (-993365700000000000000000000000) (-993360830000000000000000000000))) else (if n < 453 then (box (-1000205252000000000000000000000) (-1000200366000000000000000000000)) else (if n < 454 then (box (-1007079342000000000000000000000) (-1007074441000000000000000000000)) else (box (-1013988147000000000000000000000) (-1013983230000000000000000000000))))) else (if n < 458 then (if n < 456 then (box (-1020931839000000000000000000000) (-1020926906000000000000000000000)) else (if n < 457 then (box (-1027910597000000000000000000000) (-1027905648000000000000000000000)) else (box (-1034924597000000000000000000000) (-1034919632000000000000000000000)))) else (if n < 459 then (box (-1041974016000000000000000000000) (-1041969035000000000000000000000)) else (if n < 460 then (box (-1049059034000000000000000000000) (-1049054037000000000000000000000)) else (box (-1056179830000000000000000000000) (-1056174817000000000000000000000)))))) else (if n < 466 then (if n < 463 then (if n < 462 then (box (-1063336585000000000000000000000) (-1063331556000000000000000000000)) else (box (-1070529479000000000000000000000) (-1070524434000000000000000000000))) else (if n < 464 then (box (-1077758696000000000000000000000) (-1077753635000000000000000000000)) else (if n < 465 then (box (-1085024418000000000000000000000) (-1085019341000000000000000000000)) else (box (-1092326830000000000000000000000) (-1092321737000000000000000000000))))) else (if n < 469 then (if n < 467 then (box (-1099666116000000000000000000000) (-1099661007000000000000000000000)) else (if n < 468 then (box (-1107042462000000000000000000000) (-1107037337000000000000000000000)) else (box (-1114456055000000000000000000000) (-1114450914000000000000000000000)))) else (if n < 470 then (box (-1121907083000000000000000000000) (-1121901925000000000000000000000)) else (if n < 471 then (box (-1129395734000000000000000000000) (-1129390560000000000000000000000)) else (box (-1136922197000000000000000000000) (-1136917007000000000000000000000)))))))
def cC472_495 (n:Nat):IV:=(if n < 483 then (if n < 477 then (if n < 474 then (if n < 473 then (box (-1144486664000000000000000000000) (-1144481457000000000000000000000)) else (box (-1152089325000000000000000000000) (-1152084101000000000000000000000))) else (if n < 475 then (box (-1159730372000000000000000000000) (-1159725131000000000000000000000)) else (if n < 476 then (box (-1167409999000000000000000000000) (-1167404742000000000000000000000)) else (box (-1175128400000000000000000000000) (-1175123127000000000000000000000))))) else (if n < 480 then (if n < 478 then (box (-1182885770000000000000000000000) (-1182880481000000000000000000000)) else (if n < 479 then (box (-1190682305000000000000000000000) (-1190676999000000000000000000000)) else (box (-1198518202000000000000000000000) (-1198512880000000000000000000000)))) else (if n < 481 then (box (-1206393659000000000000000000000) (-1206388320000000000000000000000)) else (if n < 482 then (box (-1214308875000000000000000000000) (-1214303520000000000000000000000)) else (box (-1222264050000000000000000000000) (-1222258679000000000000000000000)))))) else (if n < 489 then (if n < 486 then (if n < 484 then (box (-1230259384000000000000000000000) (-1230253997000000000000000000000)) else (if n < 485 then (box (-1238295080000000000000000000000) (-1238289677000000000000000000000)) else (box (-1246371341000000000000000000000) (-1246365921000000000000000000000)))) else (if n < 487 then (box (-1254488369000000000000000000000) (-1254482933000000000000000000000)) else (if n < 488 then (box (-1262646371000000000000000000000) (-1262640918000000000000000000000)) else (box (-1270845553000000000000000000000) (-1270840083000000000000000000000))))) else (if n < 492 then (if n < 490 then (box (-1279086120000000000000000000000) (-1279080634000000000000000000000)) else (if n < 491 then (box (-1287368281000000000000000000000) (-1287362778000000000000000000000)) else (box (-1295692245000000000000000000000) (-1295686726000000000000000000000)))) else (if n < 493 then (box (-1304058222000000000000000000000) (-1304052686000000000000000000000)) else (if n < 494 then (box (-1312466422000000000000000000000) (-1312460869000000000000000000000)) else (box (-1320917058000000000000000000000) (-1320911488000000000000000000000)))))))
def cC450_495 (n:Nat):IV:=(if n < 472 then (cC450_472 n) else (cC472_495 n))
def cC495_517 (n:Nat):IV:=(if n < 506 then (if n < 500 then (if n < 497 then (if n < 496 then (box (-1329410344000000000000000000000) (-1329404757000000000000000000000)) else (box (-1337946492000000000000000000000) (-1337940888000000000000000000000))) else (if n < 498 then (box (-1346525719000000000000000000000) (-1346520098000000000000000000000)) else (if n < 499 then (box (-1355148239000000000000000000000) (-1355142601000000000000000000000)) else (box (-1363814272000000000000000000000) (-1363808617000000000000000000000))))) else (if n < 503 then (if n < 501 then (box (-1372524034000000000000000000000) (-1372518362000000000000000000000)) else (if n < 502 then (box (-1381277746000000000000000000000) (-1381272056000000000000000000000)) else (box (-1390075627000000000000000000000) (-1390069920000000000000000000000)))) else (if n < 504 then (box (-1398917901000000000000000000000) (-1398912177000000000000000000000)) else (if n < 505 then (box (-1407804788000000000000000000000) (-1407799047000000000000000000000)) else (box (-1416736514000000000000000000000) (-1416730755000000000000000000000)))))) else (if n < 511 then (if n < 508 then (if n < 507 then (box (-1425713302000000000000000000000) (-1425707526000000000000000000000)) else (box (-1434735380000000000000000000000) (-1434729587000000000000000000000))) else (if n < 509 then (box (-1443802973000000000000000000000) (-1443797163000000000000000000000)) else (if n < 510 then (box (-1452916311000000000000000000000) (-1452910484000000000000000000000)) else (box (-1462075622000000000000000000000) (-1462069777000000000000000000000))))) else (if n < 514 then (if n < 512 then (box (-1471281138000000000000000000000) (-1471275276000000000000000000000)) else (if n < 513 then (box (-1480533090000000000000000000000) (-1480527210000000000000000000000)) else (box (-1489831710000000000000000000000) (-1489825812000000000000000000000)))) else (if n < 515 then (box (-1499177234000000000000000000000) (-1499171318000000000000000000000)) else (if n < 516 then (box (-1508569895000000000000000000000) (-1508563961000000000000000000000)) else (box (-1518009930000000000000000000000) (-1518003978000000000000000000000)))))))
def cC517_540 (n:Nat):IV:=(if n < 528 then (if n < 522 then (if n < 519 then (if n < 518 then (box (-1527497575000000000000000000000) (-1527491606000000000000000000000)) else (box (-1537033072000000000000000000000) (-1537027085000000000000000000000))) else (if n < 520 then (box (-1546616658000000000000000000000) (-1546610654000000000000000000000)) else (if n < 521 then (box (-1556248575000000000000000000000) (-1556242553000000000000000000000)) else (box (-1565929065000000000000000000000) (-1565923025000000000000000000000))))) else (if n < 525 then (if n < 523 then (box (-1575658372000000000000000000000) (-1575652314000000000000000000000)) else (if n < 524 then (box (-1585436740000000000000000000000) (-1585430664000000000000000000000)) else (box (-1595264414000000000000000000000) (-1595258320000000000000000000000)))) else (if n < 526 then (box (-1605141641000000000000000000000) (-1605135529000000000000000000000)) else (if n < 527 then (box (-1615068671000000000000000000000) (-1615062541000000000000000000000)) else (box (-1625045752000000000000000000000) (-1625039604000000000000000000000)))))) else (if n < 534 then (if n < 531 then (if n < 529 then (box (-1635073135000000000000000000000) (-1635066969000000000000000000000)) else (if n < 530 then (box (-1645151073000000000000000000000) (-1645144889000000000000000000000)) else (box (-1655279818000000000000000000000) (-1655273616000000000000000000000)))) else (if n < 532 then (box (-1665459626000000000000000000000) (-1665453405000000000000000000000)) else (if n < 533 then (box (-1675690751000000000000000000000) (-1675684511000000000000000000000)) else (box (-1685973450000000000000000000000) (-1685967192000000000000000000000))))) else (if n < 537 then (if n < 535 then (box (-1696307983000000000000000000000) (-1696301707000000000000000000000)) else (if n < 536 then (box (-1706694609000000000000000000000) (-1706688314000000000000000000000)) else (box (-1717133588000000000000000000000) (-1717127274000000000000000000000)))) else (if n < 538 then (box (-1727625182000000000000000000000) (-1727618850000000000000000000000)) else (if n < 539 then (box (-1738169655000000000000000000000) (-1738163305000000000000000000000)) else (box (-1748767271000000000000000000000) (-1748760903000000000000000000000)))))))
def cC495_540 (n:Nat):IV:=(if n < 517 then (cC495_517 n) else (cC517_540 n))
def cC450_540 (n:Nat):IV:=(if n < 495 then (cC450_495 n) else (cC495_540 n))
def cC360_540 (n:Nat):IV:=(if n < 450 then (cC360_450 n) else (cC450_540 n))
def cC540_562 (n:Nat):IV:=(if n < 551 then (if n < 545 then (if n < 542 then (if n < 541 then (box (-1759418297000000000000000000000) (-1759411911000000000000000000000)) else (box (-1770123000000000000000000000000) (-1770116596000000000000000000000))) else (if n < 543 then (box (-1780881648000000000000000000000) (-1780875226000000000000000000000)) else (if n < 544 then (box (-1791694512000000000000000000000) (-1791688072000000000000000000000)) else (box (-1802561864000000000000000000000) (-1802555405000000000000000000000))))) else (if n < 548 then (if n < 546 then (box (-1813483976000000000000000000000) (-1813477498000000000000000000000)) else (if n < 547 then (box (-1824461122000000000000000000000) (-1824454625000000000000000000000)) else (box (-1835493578000000000000000000000) (-1835487062000000000000000000000)))) else (if n < 549 then (box (-1846581620000000000000000000000) (-1846575085000000000000000000000)) else (if n < 550 then (box (-1857725527000000000000000000000) (-1857718973000000000000000000000)) else (box (-1868925579000000000000000000000) (-1868919006000000000000000000000)))))) else (if n < 556 then (if n < 553 then (if n < 552 then (box (-1880182056000000000000000000000) (-1880175464000000000000000000000)) else (box (-1891495241000000000000000000000) (-1891488630000000000000000000000))) else (if n < 554 then (box (-1902865417000000000000000000000) (-1902858786000000000000000000000)) else (if n < 555 then (box (-1914292869000000000000000000000) (-1914286219000000000000000000000)) else (box (-1925777886000000000000000000000) (-1925771217000000000000000000000))))) else (if n < 559 then (if n < 557 then (box (-1937320754000000000000000000000) (-1937314066000000000000000000000)) else (if n < 558 then (box (-1948921763000000000000000000000) (-1948915056000000000000000000000)) else (box (-1960581204000000000000000000000) (-1960574478000000000000000000000)))) else (if n < 560 then (box (-1972299369000000000000000000000) (-1972292624000000000000000000000)) else (if n < 561 then (box (-1984076552000000000000000000000) (-1984069788000000000000000000000)) else (box (-1995913049000000000000000000000) (-1995906266000000000000000000000)))))))
def cC562_585 (n:Nat):IV:=(if n < 573 then (if n < 567 then (if n < 564 then (if n < 563 then (box (-2007809156000000000000000000000) (-2007802353000000000000000000000)) else (box (-2019765173000000000000000000000) (-2019758350000000000000000000000))) else (if n < 565 then (box (-2031781398000000000000000000000) (-2031774555000000000000000000000)) else (if n < 566 then (box (-2043858133000000000000000000000) (-2043851270000000000000000000000)) else (box (-2055995680000000000000000000000) (-2055988797000000000000000000000))))) else (if n < 570 then (if n < 568 then (box (-2068194344000000000000000000000) (-2068187442000000000000000000000)) else (if n < 569 then (box (-2080454430000000000000000000000) (-2080447508000000000000000000000)) else (box (-2092776247000000000000000000000) (-2092769305000000000000000000000)))) else (if n < 571 then (box (-2105160102000000000000000000000) (-2105153140000000000000000000000)) else (if n < 572 then (box (-2117606306000000000000000000000) (-2117599324000000000000000000000)) else (box (-2130115171000000000000000000000) (-2130108169000000000000000000000)))))) else (if n < 579 then (if n < 576 then (if n < 574 then (box (-2142687012000000000000000000000) (-2142679990000000000000000000000)) else (if n < 575 then (box (-2155322142000000000000000000000) (-2155315100000000000000000000000)) else (box (-2168020878000000000000000000000) (-2168013816000000000000000000000)))) else (if n < 577 then (box (-2180783540000000000000000000000) (-2180776458000000000000000000000)) else (if n < 578 then (box (-2193610445000000000000000000000) (-2193603343000000000000000000000)) else (box (-2206501916000000000000000000000) (-2206494794000000000000000000000))))) else (if n < 582 then (if n < 580 then (box (-2219458276000000000000000000000) (-2219451133000000000000000000000)) else (if n < 581 then (box (-2232479849000000000000000000000) (-2232472686000000000000000000000)) else (box (-2245566963000000000000000000000) (-2245559779000000000000000000000)))) else (if n < 583 then (box (-2258719944000000000000000000000) (-2258712739000000000000000000000)) else (if n < 584 then (box (-2271939123000000000000000000000) (-2271931897000000000000000000000)) else (box (-2285224831000000000000000000000) (-2285217585000000000000000000000)))))))
def cC540_585 (n:Nat):IV:=(if n < 562 then (cC540_562 n) else (cC562_585 n))
def cC585_607 (n:Nat):IV:=(if n < 596 then (if n < 590 then (if n < 587 then (if n < 586 then (box (-2298577399000000000000000000000) (-2298570133000000000000000000000)) else (box (-2311997163000000000000000000000) (-2311989876000000000000000000000))) else (if n < 588 then (box (-2325484458000000000000000000000) (-2325477151000000000000000000000)) else (if n < 589 then (box (-2339039624000000000000000000000) (-2339032296000000000000000000000)) else (box (-2352662998000000000000000000000) (-2352655649000000000000000000000))))) else (if n < 593 then (if n < 591 then (box (-2366354924000000000000000000000) (-2366347554000000000000000000000)) else (if n < 592 then (box (-2380115742000000000000000000000) (-2380108352000000000000000000000)) else (box (-2393945799000000000000000000000) (-2393938388000000000000000000000)))) else (if n < 594 then (box (-2407845441000000000000000000000) (-2407838009000000000000000000000)) else (if n < 595 then (box (-2421815014000000000000000000000) (-2421807561000000000000000000000)) else (box (-2435854870000000000000000000000) (-2435847396000000000000000000000)))))) else (if n < 601 then (if n < 598 then (if n < 597 then (box (-2449965360000000000000000000000) (-2449957865000000000000000000000)) else (box (-2464146838000000000000000000000) (-2464139322000000000000000000000))) else (if n < 599 then (box (-2478399659000000000000000000000) (-2478392121000000000000000000000)) else (if n < 600 then (box (-2492724179000000000000000000000) (-2492716620000000000000000000000)) else (box (-2507120756000000000000000000000) (-2507113176000000000000000000000))))) else (if n < 604 then (if n < 602 then (box (-2521589753000000000000000000000) (-2521582152000000000000000000000)) else (if n < 603 then (box (-2536131532000000000000000000000) (-2536123910000000000000000000000)) else (box (-2550746455000000000000000000000) (-2550738812000000000000000000000)))) else (if n < 605 then (box (-2565434890000000000000000000000) (-2565427225000000000000000000000)) else (if n < 606 then (box (-2580197204000000000000000000000) (-2580189517000000000000000000000)) else (box (-2595033765000000000000000000000) (-2595026057000000000000000000000)))))))
def cC607_630 (n:Nat):IV:=(if n < 618 then (if n < 612 then (if n < 609 then (if n < 608 then (box (-2609944945000000000000000000000) (-2609937216000000000000000000000)) else (box (-2624931119000000000000000000000) (-2624923368000000000000000000000))) else (if n < 610 then (box (-2639992662000000000000000000000) (-2639984889000000000000000000000)) else (if n < 611 then (box (-2655129950000000000000000000000) (-2655122155000000000000000000000)) else (box (-2670343362000000000000000000000) (-2670335545000000000000000000000))))) else (if n < 615 then (if n < 613 then (box (-2685633280000000000000000000000) (-2685625441000000000000000000000)) else (if n < 614 then (box (-2701000086000000000000000000000) (-2700992225000000000000000000000)) else (box (-2716444164000000000000000000000) (-2716436281000000000000000000000)))) else (if n < 616 then (box (-2731965902000000000000000000000) (-2731957996000000000000000000000)) else (if n < 617 then (box (-2747565688000000000000000000000) (-2747557760000000000000000000000)) else (box (-2763243911000000000000000000000) (-2763235961000000000000000000000)))))) else (if n < 624 then (if n < 621 then (if n < 619 then (box (-2779000965000000000000000000000) (-2778992993000000000000000000000)) else (if n < 620 then (box (-2794837244000000000000000000000) (-2794829250000000000000000000000)) else (box (-2810753144000000000000000000000) (-2810745128000000000000000000000)))) else (if n < 622 then (box (-2826749064000000000000000000000) (-2826741025000000000000000000000)) else (if n < 623 then (box (-2842825404000000000000000000000) (-2842817343000000000000000000000)) else (box (-2858982567000000000000000000000) (-2858974483000000000000000000000))))) else (if n < 627 then (if n < 625 then (box (-2875220956000000000000000000000) (-2875212849000000000000000000000)) else (if n < 626 then (box (-2891540978000000000000000000000) (-2891532848000000000000000000000)) else (box (-2907943043000000000000000000000) (-2907934890000000000000000000000)))) else (if n < 628 then (box (-2924427558000000000000000000000) (-2924419382000000000000000000000)) else (if n < 629 then (box (-2940994938000000000000000000000) (-2940986739000000000000000000000)) else (box (-2957645598000000000000000000000) (-2957637376000000000000000000000)))))))
def cC585_630 (n:Nat):IV:=(if n < 607 then (cC585_607 n) else (cC607_630 n))
def cC540_630 (n:Nat):IV:=(if n < 585 then (cC540_585 n) else (cC585_630 n))
def cC630_652 (n:Nat):IV:=(if n < 641 then (if n < 635 then (if n < 632 then (if n < 631 then (box (-2974379955000000000000000000000) (-2974371710000000000000000000000)) else (box (-2991198426000000000000000000000) (-2991190158000000000000000000000))) else (if n < 633 then (box (-3008101431000000000000000000000) (-3008093140000000000000000000000)) else (if n < 634 then (box (-3025089395000000000000000000000) (-3025081081000000000000000000000)) else (box (-3042162743000000000000000000000) (-3042154405000000000000000000000))))) else (if n < 638 then (if n < 636 then (box (-3059321902000000000000000000000) (-3059313540000000000000000000000)) else (if n < 637 then (box (-3076567302000000000000000000000) (-3076558916000000000000000000000)) else (box (-3093899373000000000000000000000) (-3093890964000000000000000000000)))) else (if n < 639 then (box (-3111318549000000000000000000000) (-3111310117000000000000000000000)) else (if n < 640 then (box (-3128825267000000000000000000000) (-3128816812000000000000000000000)) else (box (-3146419964000000000000000000000) (-3146411485000000000000000000000)))))) else (if n < 646 then (if n < 643 then (if n < 642 then (box (-3164103082000000000000000000000) (-3164094579000000000000000000000)) else (box (-3181875062000000000000000000000) (-3181866535000000000000000000000))) else (if n < 644 then (box (-3199736347000000000000000000000) (-3199727796000000000000000000000)) else (if n < 645 then (box (-3217687386000000000000000000000) (-3217678811000000000000000000000)) else (box (-3235728627000000000000000000000) (-3235720028000000000000000000000))))) else (if n < 649 then (if n < 647 then (box (-3253860522000000000000000000000) (-3253851898000000000000000000000)) else (if n < 648 then (box (-3272083525000000000000000000000) (-3272074877000000000000000000000)) else (box (-3290398092000000000000000000000) (-3290389419000000000000000000000)))) else (if n < 650 then (box (-3308804681000000000000000000000) (-3308795983000000000000000000000)) else (if n < 651 then (box (-3327303751000000000000000000000) (-3327295028000000000000000000000)) else (box (-3345895767000000000000000000000) (-3345887019000000000000000000000)))))))
def cC652_675 (n:Nat):IV:=(if n < 663 then (if n < 657 then (if n < 654 then (if n < 653 then (box (-3364581193000000000000000000000) (-3364572421000000000000000000000)) else (box (-3383360496000000000000000000000) (-3383351699000000000000000000000))) else (if n < 655 then (box (-3402234145000000000000000000000) (-3402225324000000000000000000000)) else (if n < 656 then (box (-3421202615000000000000000000000) (-3421193770000000000000000000000)) else (box (-3440266378000000000000000000000) (-3440257508000000000000000000000))))) else (if n < 660 then (if n < 658 then (box (-3459425913000000000000000000000) (-3459417018000000000000000000000)) else (if n < 659 then (box (-3478681699000000000000000000000) (-3478672779000000000000000000000)) else (box (-3498034216000000000000000000000) (-3498025271000000000000000000000)))) else (if n < 661 then (box (-3517483949000000000000000000000) (-3517474979000000000000000000000)) else (if n < 662 then (box (-3537031384000000000000000000000) (-3537022389000000000000000000000)) else (box (-3556677011000000000000000000000) (-3556667991000000000000000000000)))))) else (if n < 669 then (if n < 666 then (if n < 664 then (box (-3576421322000000000000000000000) (-3576412276000000000000000000000)) else (if n < 665 then (box (-3596264809000000000000000000000) (-3596255738000000000000000000000)) else (box (-3616207970000000000000000000000) (-3616198873000000000000000000000)))) else (if n < 667 then (box (-3636251301000000000000000000000) (-3636242179000000000000000000000)) else (if n < 668 then (box (-3656395305000000000000000000000) (-3656386158000000000000000000000)) else (box (-3676640487000000000000000000000) (-3676631314000000000000000000000))))) else (if n < 672 then (if n < 670 then (box (-3696987354000000000000000000000) (-3696978155000000000000000000000)) else (if n < 671 then (box (-3717436413000000000000000000000) (-3717427188000000000000000000000)) else (box (-3737988174000000000000000000000) (-3737978923000000000000000000000)))) else (if n < 673 then (box (-3758643155000000000000000000000) (-3758633878000000000000000000000)) else (if n < 674 then (box (-3779401870000000000000000000000) (-3779392567000000000000000000000)) else (box (-3800264840000000000000000000000) (-3800255510000000000000000000000)))))))
def cC630_675 (n:Nat):IV:=(if n < 652 then (cC630_652 n) else (cC652_675 n))
def cC675_698 (n:Nat):IV:=(if n < 686 then (if n < 680 then (if n < 677 then (if n < 676 then (box (-3821232586000000000000000000000) (-3821223229000000000000000000000)) else (box (-3842305631000000000000000000000) (-3842296248000000000000000000000))) else (if n < 678 then (box (-3863484503000000000000000000000) (-3863475094000000000000000000000)) else (if n < 679 then (box (-3884769731000000000000000000000) (-3884760296000000000000000000000)) else (box (-3906161849000000000000000000000) (-3906152387000000000000000000000))))) else (if n < 683 then (if n < 681 then (box (-3927661391000000000000000000000) (-3927651903000000000000000000000)) else (if n < 682 then (box (-3949268896000000000000000000000) (-3949259381000000000000000000000)) else (box (-3970984904000000000000000000000) (-3970975362000000000000000000000)))) else (if n < 684 then (box (-3992809957000000000000000000000) (-3992800388000000000000000000000)) else (if n < 685 then (box (-4014744602000000000000000000000) (-4014735006000000000000000000000)) else (box (-4036789387000000000000000000000) (-4036779764000000000000000000000)))))) else (if n < 692 then (if n < 689 then (if n < 687 then (box (-4058944862000000000000000000000) (-4058935212000000000000000000000)) else (if n < 688 then (box (-4081211582000000000000000000000) (-4081201905000000000000000000000)) else (box (-4103590106000000000000000000000) (-4103580401000000000000000000000)))) else (if n < 690 then (box (-4126080992000000000000000000000) (-4126071259000000000000000000000)) else (if n < 691 then (box (-4148684801000000000000000000000) (-4148675041000000000000000000000)) else (box (-4171402100000000000000000000000) (-4171392313000000000000000000000))))) else (if n < 695 then (if n < 693 then (box (-4194233457000000000000000000000) (-4194223642000000000000000000000)) else (if n < 694 then (box (-4217179443000000000000000000000) (-4217169600000000000000000000000)) else (box (-4240240632000000000000000000000) (-4240230761000000000000000000000)))) else (if n < 696 then (box (-4263417601000000000000000000000) (-4263407702000000000000000000000)) else (if n < 697 then (box (-4286710928000000000000000000000) (-4286701001000000000000000000000)) else (box (-4310121197000000000000000000000) (-4310111242000000000000000000000)))))))
def cC698_721 (n:Nat):IV:=(if n < 709 then (if n < 703 then (if n < 700 then (if n < 699 then (box (-4333648991000000000000000000000) (-4333639008000000000000000000000)) else (box (-4357294900000000000000000000000) (-4357284888000000000000000000000))) else (if n < 701 then (box (-4381059516000000000000000000000) (-4381049476000000000000000000000)) else (if n < 702 then (box (-4404943435000000000000000000000) (-4404933366000000000000000000000)) else (box (-4428947252000000000000000000000) (-4428937154000000000000000000000))))) else (if n < 706 then (if n < 704 then (box (-4453071567000000000000000000000) (-4453061441000000000000000000000)) else (if n < 705 then (box (-4477316984000000000000000000000) (-4477306829000000000000000000000)) else (box (-4501684108000000000000000000000) (-4501673924000000000000000000000)))) else (if n < 707 then (box (-4526173550000000000000000000000) (-4526163337000000000000000000000)) else (if n < 708 then (box (-4550785922000000000000000000000) (-4550775680000000000000000000000)) else (box (-4575521839000000000000000000000) (-4575511568000000000000000000000)))))) else (if n < 715 then (if n < 712 then (if n < 710 then (box (-4600381920000000000000000000000) (-4600371620000000000000000000000)) else (if n < 711 then (box (-4625366787000000000000000000000) (-4625356457000000000000000000000)) else (box (-4650477063000000000000000000000) (-4650466703000000000000000000000)))) else (if n < 713 then (box (-4675713378000000000000000000000) (-4675702988000000000000000000000)) else (if n < 714 then (box (-4701076363000000000000000000000) (-4701065944000000000000000000000)) else (box (-4726566651000000000000000000000) (-4726556203000000000000000000000))))) else (if n < 718 then (if n < 716 then (box (-4752184879000000000000000000000) (-4752174402000000000000000000000)) else (if n < 717 then (box (-4777931687000000000000000000000) (-4777921180000000000000000000000)) else (box (-4803807723000000000000000000000) (-4803797186000000000000000000000)))) else (if n < 719 then (box (-4829813630000000000000000000000) (-4829803063000000000000000000000)) else (if n < 720 then (box (-4855950059000000000000000000000) (-4855939462000000000000000000000)) else (box (-4882217665000000000000000000000) (-4882207038000000000000000000000)))))))
def cC675_721 (n:Nat):IV:=(if n < 698 then (cC675_698 n) else (cC698_721 n))
def cC630_721 (n:Nat):IV:=(if n < 675 then (cC630_675 n) else (cC675_721 n))
def cC540_721 (n:Nat):IV:=(if n < 630 then (cC540_630 n) else (cC630_721 n))
def cC360_721 (n:Nat):IV:=(if n < 540 then (cC360_540 n) else (cC540_721 n))
def cC0_721 (n:Nat):IV:=(if n < 360 then (cC0_360 n) else (cC360_721 n))
def cQ0_22 (n:Nat):IV:=(if n < 11 then (if n < 5 then (if n < 2 then (if n < 1 then (box (0) (0)) else (box (-1479622000000000000000000000) (-1479610000000000000000000000))) else (if n < 3 then (box (-2959052000000000000000000000) (-2959028000000000000000000000)) else (if n < 4 then (box (-4438099000000000000000000000) (-4438063000000000000000000000)) else (box (-5916574000000000000000000000) (-5916526000000000000000000000))))) else (if n < 8 then (if n < 6 then (box (-7394283000000000000000000000) (-7394223000000000000000000000)) else (if n < 7 then (box (-8871037000000000000000000000) (-8870965000000000000000000000)) else (box (-10346644000000000000000000000) (-10346560000000000000000000000)))) else (if n < 9 then (box (-11820913000000000000000000000) (-11820817000000000000000000000)) else (if n < 10 then (box (-13293652000000000000000000000) (-13293544000000000000000000000)) else (box (-14764669000000000000000000000) (-14764549000000000000000000000)))))) else (if n < 16 then (if n < 13 then (if n < 12 then (box (-16233774000000000000000000000) (-16233643000000000000000000000)) else (box (-17700774000000000000000000000) (-17700631000000000000000000000))) else (if n < 14 then (box (-19165477000000000000000000000) (-19165323000000000000000000000)) else (if n < 15 then (box (-20627693000000000000000000000) (-20627528000000000000000000000)) else (box (-22087228000000000000000000000) (-22087051000000000000000000000))))) else (if n < 19 then (if n < 17 then (box (-23543891000000000000000000000) (-23543702000000000000000000000)) else (if n < 18 then (box (-24997489000000000000000000000) (-24997289000000000000000000000)) else (box (-26447830000000000000000000000) (-26447619000000000000000000000)))) else (if n < 20 then (box (-27894722000000000000000000000) (-27894499000000000000000000000)) else (if n < 21 then (box (-29337972000000000000000000000) (-29337737000000000000000000000)) else (box (-30777385000000000000000000000) (-30777139000000000000000000000)))))))
def cQ22_45 (n:Nat):IV:=(if n < 33 then (if n < 27 then (if n < 24 then (if n < 23 then (box (-32212771000000000000000000000) (-32212514000000000000000000000)) else (box (-33643935000000000000000000000) (-33643666000000000000000000000))) else (if n < 25 then (box (-35070685000000000000000000000) (-35070404000000000000000000000)) else (if n < 26 then (box (-36492826000000000000000000000) (-36492534000000000000000000000)) else (box (-37910165000000000000000000000) (-37909861000000000000000000000))))) else (if n < 30 then (if n < 28 then (box (-39322508000000000000000000000) (-39322193000000000000000000000)) else (if n < 29 then (box (-40729661000000000000000000000) (-40729335000000000000000000000)) else (box (-42131430000000000000000000000) (-42131093000000000000000000000)))) else (if n < 31 then (box (-43527621000000000000000000000) (-43527273000000000000000000000)) else (if n < 32 then (box (-44918040000000000000000000000) (-44917681000000000000000000000)) else (box (-46302490000000000000000000000) (-46302120000000000000000000000)))))) else (if n < 39 then (if n < 36 then (if n < 34 then (box (-47680779000000000000000000000) (-47680398000000000000000000000)) else (if n < 35 then (box (-49052711000000000000000000000) (-49052319000000000000000000000)) else (box (-50418091000000000000000000000) (-50417688000000000000000000000)))) else (if n < 37 then (box (-51776724000000000000000000000) (-51776310000000000000000000000)) else (if n < 38 then (box (-53128415000000000000000000000) (-53127990000000000000000000000)) else (box (-54472969000000000000000000000) (-54472533000000000000000000000))))) else (if n < 42 then (if n < 40 then (box (-55810191000000000000000000000) (-55809744000000000000000000000)) else (if n < 41 then (box (-57139884000000000000000000000) (-57139426000000000000000000000)) else (box (-58461855000000000000000000000) (-58461386000000000000000000000)))) else (if n < 43 then (box (-59775907000000000000000000000) (-59775428000000000000000000000)) else (if n < 44 then (box (-61081845000000000000000000000) (-61081356000000000000000000000)) else (box (-62379474000000000000000000000) (-62378974000000000000000000000)))))))
def cQ0_45 (n:Nat):IV:=(if n < 22 then (cQ0_22 n) else (cQ22_45 n))
def cQ45_67 (n:Nat):IV:=(if n < 56 then (if n < 50 then (if n < 47 then (if n < 46 then (box (-63668599000000000000000000000) (-63668089000000000000000000000)) else (box (-64949025000000000000000000000) (-64948504000000000000000000000))) else (if n < 48 then (box (-66220556000000000000000000000) (-66220025000000000000000000000)) else (if n < 49 then (box (-67482998000000000000000000000) (-67482457000000000000000000000)) else (box (-68736156000000000000000000000) (-68735604000000000000000000000))))) else (if n < 53 then (if n < 51 then (box (-69979836000000000000000000000) (-69979274000000000000000000000)) else (if n < 52 then (box (-71213843000000000000000000000) (-71213271000000000000000000000)) else (box (-72437983000000000000000000000) (-72437401000000000000000000000)))) else (if n < 54 then (box (-73652063000000000000000000000) (-73651471000000000000000000000)) else (if n < 55 then (box (-74855889000000000000000000000) (-74855288000000000000000000000)) else (box (-76049268000000000000000000000) (-76048657000000000000000000000)))))) else (if n < 61 then (if n < 58 then (if n < 57 then (box (-77232008000000000000000000000) (-77231387000000000000000000000)) else (box (-78403917000000000000000000000) (-78403287000000000000000000000))) else (if n < 59 then (box (-79564803000000000000000000000) (-79564163000000000000000000000)) else (if n < 60 then (box (-80714475000000000000000000000) (-80713826000000000000000000000)) else (box (-81852743000000000000000000000) (-81852085000000000000000000000))))) else (if n < 64 then (if n < 62 then (box (-82979417000000000000000000000) (-82978750000000000000000000000)) else (if n < 63 then (box (-84094308000000000000000000000) (-84093632000000000000000000000)) else (box (-85197227000000000000000000000) (-85196542000000000000000000000)))) else (if n < 65 then (box (-86287987000000000000000000000) (-86287293000000000000000000000)) else (if n < 66 then (box (-87366402000000000000000000000) (-87365699000000000000000000000)) else (box (-88432286000000000000000000000) (-88431574000000000000000000000)))))))
def cQ67_90 (n:Nat):IV:=(if n < 78 then (if n < 72 then (if n < 69 then (if n < 68 then (box (-89485453000000000000000000000) (-89484732000000000000000000000)) else (box (-90525721000000000000000000000) (-90524991000000000000000000000))) else (if n < 70 then (box (-91552906000000000000000000000) (-91552167000000000000000000000)) else (if n < 71 then (box (-92566827000000000000000000000) (-92566079000000000000000000000)) else (box (-93567303000000000000000000000) (-93566546000000000000000000000))))) else (if n < 75 then (if n < 73 then (box (-94554156000000000000000000000) (-94553390000000000000000000000)) else (if n < 74 then (box (-95527207000000000000000000000) (-95526433000000000000000000000)) else (box (-96486280000000000000000000000) (-96485498000000000000000000000)))) else (if n < 76 then (box (-97431200000000000000000000000) (-97430410000000000000000000000)) else (if n < 77 then (box (-98361794000000000000000000000) (-98360996000000000000000000000)) else (box (-99277889000000000000000000000) (-99277083000000000000000000000)))))) else (if n < 84 then (if n < 81 then (if n < 79 then (box (-100179316000000000000000000000) (-100178502000000000000000000000)) else (if n < 80 then (box (-101065906000000000000000000000) (-101065084000000000000000000000)) else (box (-101937492000000000000000000000) (-101936662000000000000000000000)))) else (if n < 82 then (box (-102793909000000000000000000000) (-102793072000000000000000000000)) else (if n < 83 then (box (-103634994000000000000000000000) (-103634150000000000000000000000)) else (box (-104460586000000000000000000000) (-104459735000000000000000000000))))) else (if n < 87 then (if n < 85 then (box (-105270527000000000000000000000) (-105269668000000000000000000000)) else (if n < 86 then (box (-106064659000000000000000000000) (-106063793000000000000000000000)) else (box (-106842827000000000000000000000) (-106841954000000000000000000000)))) else (if n < 88 then (box (-107604879000000000000000000000) (-107603999000000000000000000000)) else (if n < 89 then (box (-108350664000000000000000000000) (-108349778000000000000000000000)) else (box (-109080035000000000000000000000) (-109079143000000000000000000000)))))))
def cQ45_90 (n:Nat):IV:=(if n < 67 then (cQ45_67 n) else (cQ67_90 n))
def cQ0_90 (n:Nat):IV:=(if n < 45 then (cQ0_45 n) else (cQ45_90 n))
def cQ90_112 (n:Nat):IV:=(if n < 101 then (if n < 95 then (if n < 92 then (if n < 91 then (box (-109792847000000000000000000000) (-109791948000000000000000000000)) else (box (-110488956000000000000000000000) (-110488050000000000000000000000))) else (if n < 93 then (box (-111168222000000000000000000000) (-111167310000000000000000000000)) else (if n < 94 then (box (-111830507000000000000000000000) (-111829589000000000000000000000)) else (box (-112475676000000000000000000000) (-112474752000000000000000000000))))) else (if n < 98 then (if n < 96 then (box (-113103597000000000000000000000) (-113102667000000000000000000000)) else (if n < 97 then (box (-113714139000000000000000000000) (-113713204000000000000000000000)) else (box (-114307177000000000000000000000) (-114306236000000000000000000000)))) else (if n < 99 then (box (-114882586000000000000000000000) (-114881639000000000000000000000)) else (if n < 100 then (box (-115440245000000000000000000000) (-115439293000000000000000000000)) else (box (-115980036000000000000000000000) (-115979079000000000000000000000)))))) else (if n < 106 then (if n < 103 then (if n < 102 then (box (-116501845000000000000000000000) (-116500883000000000000000000000)) else (box (-117005559000000000000000000000) (-117004591000000000000000000000))) else (if n < 104 then (box (-117491070000000000000000000000) (-117490096000000000000000000000)) else (if n < 105 then (box (-117958271000000000000000000000) (-117957292000000000000000000000)) else (box (-118407061000000000000000000000) (-118406077000000000000000000000))))) else (if n < 109 then (if n < 107 then (box (-118837340000000000000000000000) (-118836351000000000000000000000)) else (if n < 108 then (box (-119249012000000000000000000000) (-119248018000000000000000000000)) else (box (-119641984000000000000000000000) (-119640986000000000000000000000)))) else (if n < 110 then (box (-120016167000000000000000000000) (-120015165000000000000000000000)) else (if n < 111 then (box (-120371475000000000000000000000) (-120370469000000000000000000000)) else (box (-120707825000000000000000000000) (-120706814000000000000000000000)))))))
def cQ112_135 (n:Nat):IV:=(if n < 123 then (if n < 117 then (if n < 114 then (if n < 113 then (box (-121025137000000000000000000000) (-121024122000000000000000000000)) else (box (-121323335000000000000000000000) (-121322316000000000000000000000))) else (if n < 115 then (box (-121602347000000000000000000000) (-121601324000000000000000000000)) else (if n < 116 then (box (-121862103000000000000000000000) (-121861077000000000000000000000)) else (box (-122102538000000000000000000000) (-122101508000000000000000000000))))) else (if n < 120 then (if n < 118 then (box (-122323588000000000000000000000) (-122322555000000000000000000000)) else (if n < 119 then (box (-122525194000000000000000000000) (-122524158000000000000000000000)) else (box (-122707300000000000000000000000) (-122706261000000000000000000000)))) else (if n < 121 then (box (-122869854000000000000000000000) (-122868812000000000000000000000)) else (if n < 122 then (box (-123012806000000000000000000000) (-123011761000000000000000000000)) else (box (-123136111000000000000000000000) (-123135063000000000000000000000)))))) else (if n < 129 then (if n < 126 then (if n < 124 then (box (-123239725000000000000000000000) (-123238674000000000000000000000)) else (if n < 125 then (box (-123323609000000000000000000000) (-123322555000000000000000000000)) else (box (-123387727000000000000000000000) (-123386670000000000000000000000)))) else (if n < 127 then (box (-123432045000000000000000000000) (-123430986000000000000000000000)) else (if n < 128 then (box (-123456533000000000000000000000) (-123455472000000000000000000000)) else (box (-123461165000000000000000000000) (-123460101000000000000000000000))))) else (if n < 132 then (if n < 130 then (box (-123445916000000000000000000000) (-123444850000000000000000000000)) else (if n < 131 then (box (-123410765000000000000000000000) (-123409697000000000000000000000)) else (box (-123355695000000000000000000000) (-123354624000000000000000000000)))) else (if n < 133 then (box (-123280690000000000000000000000) (-123279616000000000000000000000)) else (if n < 134 then (box (-123185738000000000000000000000) (-123184661000000000000000000000)) else (box (-123070828000000000000000000000) (-123069749000000000000000000000)))))))
def cQ90_135 (n:Nat):IV:=(if n < 112 then (cQ90_112 n) else (cQ112_135 n))
def cQ135_157 (n:Nat):IV:=(if n < 146 then (if n < 140 then (if n < 137 then (if n < 136 then (box (-122935955000000000000000000000) (-122934873000000000000000000000)) else (box (-122781113000000000000000000000) (-122780028000000000000000000000))) else (if n < 138 then (box (-122606301000000000000000000000) (-122605213000000000000000000000)) else (if n < 139 then (box (-122411520000000000000000000000) (-122410428000000000000000000000)) else (box (-122196772000000000000000000000) (-122195677000000000000000000000))))) else (if n < 143 then (if n < 141 then (box (-121962063000000000000000000000) (-121960964000000000000000000000)) else (if n < 142 then (box (-121707400000000000000000000000) (-121706298000000000000000000000)) else (box (-121432793000000000000000000000) (-121431687000000000000000000000)))) else (if n < 144 then (box (-121138254000000000000000000000) (-121137144000000000000000000000)) else (if n < 145 then (box (-120823797000000000000000000000) (-120822683000000000000000000000)) else (box (-120489437000000000000000000000) (-120488319000000000000000000000)))))) else (if n < 151 then (if n < 148 then (if n < 147 then (box (-120135192000000000000000000000) (-120134070000000000000000000000)) else (box (-119761082000000000000000000000) (-119759955000000000000000000000))) else (if n < 149 then (box (-119367127000000000000000000000) (-119365995000000000000000000000)) else (if n < 150 then (box (-118953349000000000000000000000) (-118952213000000000000000000000)) else (box (-118519773000000000000000000000) (-118518632000000000000000000000))))) else (if n < 154 then (if n < 152 then (box (-118066424000000000000000000000) (-118065278000000000000000000000)) else (if n < 153 then (box (-117593328000000000000000000000) (-117592177000000000000000000000)) else (box (-117100513000000000000000000000) (-117099357000000000000000000000)))) else (if n < 155 then (box (-116588008000000000000000000000) (-116586847000000000000000000000)) else (if n < 156 then (box (-116055843000000000000000000000) (-116054677000000000000000000000)) else (box (-115504049000000000000000000000) (-115502878000000000000000000000)))))))
def cQ157_180 (n:Nat):IV:=(if n < 168 then (if n < 162 then (if n < 159 then (if n < 158 then (box (-114932658000000000000000000000) (-114931481000000000000000000000)) else (box (-114341702000000000000000000000) (-114340520000000000000000000000))) else (if n < 160 then (box (-113731215000000000000000000000) (-113730027000000000000000000000)) else (if n < 161 then (box (-113101230000000000000000000000) (-113100036000000000000000000000)) else (box (-112451781000000000000000000000) (-112450581000000000000000000000))))) else (if n < 165 then (if n < 163 then (box (-111782904000000000000000000000) (-111781698000000000000000000000)) else (if n < 164 then (box (-111094633000000000000000000000) (-111093421000000000000000000000)) else (box (-110387004000000000000000000000) (-110385786000000000000000000000)))) else (if n < 166 then (box (-109660052000000000000000000000) (-109658828000000000000000000000)) else (if n < 167 then (box (-108913813000000000000000000000) (-108912583000000000000000000000)) else (box (-108148323000000000000000000000) (-108147087000000000000000000000)))))) else (if n < 174 then (if n < 171 then (if n < 169 then (box (-107363618000000000000000000000) (-107362376000000000000000000000)) else (if n < 170 then (box (-106559733000000000000000000000) (-106558485000000000000000000000)) else (box (-105736704000000000000000000000) (-105735450000000000000000000000)))) else (if n < 172 then (box (-104894567000000000000000000000) (-104893306000000000000000000000)) else (if n < 173 then (box (-104033356000000000000000000000) (-104032089000000000000000000000)) else (box (-103153106000000000000000000000) (-103151833000000000000000000000))))) else (if n < 177 then (if n < 175 then (box (-102253852000000000000000000000) (-102252573000000000000000000000)) else (if n < 176 then (box (-101335628000000000000000000000) (-101334342000000000000000000000)) else (box (-100398467000000000000000000000) (-100397174000000000000000000000)))) else (if n < 178 then (box (-99442402000000000000000000000) (-99441102000000000000000000000)) else (if n < 179 then (box (-98467466000000000000000000000) (-98466159000000000000000000000)) else (box (-97473690000000000000000000000) (-97472375000000000000000000000)))))))
def cQ135_180 (n:Nat):IV:=(if n < 157 then (cQ135_157 n) else (cQ157_180 n))
def cQ90_180 (n:Nat):IV:=(if n < 135 then (cQ90_135 n) else (cQ135_180 n))
def cQ0_180 (n:Nat):IV:=(if n < 90 then (cQ0_90 n) else (cQ90_180 n))
def cQ180_202 (n:Nat):IV:=(if n < 191 then (if n < 185 then (if n < 182 then (if n < 181 then (box (-96461105000000000000000000000) (-96459783000000000000000000000)) else (box (-95429742000000000000000000000) (-95428412000000000000000000000))) else (if n < 183 then (box (-94379630000000000000000000000) (-94378292000000000000000000000)) else (if n < 184 then (box (-93310798000000000000000000000) (-93309452000000000000000000000)) else (box (-92223274000000000000000000000) (-92221920000000000000000000000))))) else (if n < 188 then (if n < 186 then (box (-91117085000000000000000000000) (-91115723000000000000000000000)) else (if n < 187 then (box (-89992257000000000000000000000) (-89990887000000000000000000000)) else (box (-88848816000000000000000000000) (-88847439000000000000000000000)))) else (if n < 189 then (box (-87686786000000000000000000000) (-87685402000000000000000000000)) else (if n < 190 then (box (-86506191000000000000000000000) (-86504799000000000000000000000)) else (box (-85307053000000000000000000000) (-85305653000000000000000000000)))))) else (if n < 196 then (if n < 193 then (if n < 192 then (box (-84089394000000000000000000000) (-84087986000000000000000000000)) else (box (-82853234000000000000000000000) (-82851817000000000000000000000))) else (if n < 194 then (box (-81598592000000000000000000000) (-81597167000000000000000000000)) else (if n < 195 then (box (-80325487000000000000000000000) (-80324054000000000000000000000)) else (box (-79033936000000000000000000000) (-79032495000000000000000000000))))) else (if n < 199 then (if n < 197 then (box (-77723956000000000000000000000) (-77722507000000000000000000000)) else (if n < 198 then (box (-76395561000000000000000000000) (-76394104000000000000000000000)) else (box (-75048766000000000000000000000) (-75047301000000000000000000000)))) else (if n < 200 then (box (-73683584000000000000000000000) (-73682110000000000000000000000)) else (if n < 201 then (box (-72300027000000000000000000000) (-72298544000000000000000000000)) else (box (-70898105000000000000000000000) (-70896614000000000000000000000)))))))
def cQ202_225 (n:Nat):IV:=(if n < 213 then (if n < 207 then (if n < 204 then (if n < 203 then (box (-69477828000000000000000000000) (-69476328000000000000000000000)) else (box (-68039205000000000000000000000) (-68037696000000000000000000000))) else (if n < 205 then (box (-66582243000000000000000000000) (-66580725000000000000000000000)) else (if n < 206 then (box (-65106949000000000000000000000) (-65105422000000000000000000000)) else (box (-63613327000000000000000000000) (-63611791000000000000000000000))))) else (if n < 210 then (if n < 208 then (box (-62101382000000000000000000000) (-62099837000000000000000000000)) else (if n < 209 then (box (-60571117000000000000000000000) (-60569563000000000000000000000)) else (box (-59022534000000000000000000000) (-59020970000000000000000000000)))) else (if n < 211 then (box (-57455633000000000000000000000) (-57454060000000000000000000000)) else (if n < 212 then (box (-55870415000000000000000000000) (-55868832000000000000000000000)) else (box (-54266877000000000000000000000) (-54265284000000000000000000000)))))) else (if n < 219 then (if n < 216 then (if n < 214 then (box (-52645017000000000000000000000) (-52643415000000000000000000000)) else (if n < 215 then (box (-51004833000000000000000000000) (-51003221000000000000000000000)) else (box (-49346318000000000000000000000) (-49344696000000000000000000000)))) else (if n < 217 then (box (-47669468000000000000000000000) (-47667836000000000000000000000)) else (if n < 218 then (box (-45974275000000000000000000000) (-45972634000000000000000000000)) else (box (-44260731000000000000000000000) (-44259081000000000000000000000))))) else (if n < 222 then (if n < 220 then (box (-42528829000000000000000000000) (-42527169000000000000000000000)) else (if n < 221 then (box (-40778557000000000000000000000) (-40776887000000000000000000000)) else (box (-39009905000000000000000000000) (-39008225000000000000000000000)))) else (if n < 223 then (box (-37222860000000000000000000000) (-37221170000000000000000000000)) else (if n < 224 then (box (-35417410000000000000000000000) (-35415710000000000000000000000)) else (box (-33593541000000000000000000000) (-33591831000000000000000000000)))))))
def cQ180_225 (n:Nat):IV:=(if n < 202 then (cQ180_202 n) else (cQ202_225 n))
def cQ225_247 (n:Nat):IV:=(if n < 236 then (if n < 230 then (if n < 227 then (if n < 226 then (box (-31751237000000000000000000000) (-31749517000000000000000000000)) else (box (-29890483000000000000000000000) (-29888753000000000000000000000))) else (if n < 228 then (box (-28011261000000000000000000000) (-28009521000000000000000000000)) else (if n < 229 then (box (-26113553000000000000000000000) (-26111803000000000000000000000)) else (box (-24197340000000000000000000000) (-24195580000000000000000000000))))) else (if n < 233 then (if n < 231 then (box (-22262603000000000000000000000) (-22260832000000000000000000000)) else (if n < 232 then (box (-20309320000000000000000000000) (-20307539000000000000000000000)) else (box (-18337469000000000000000000000) (-18335677000000000000000000000)))) else (if n < 234 then (box (-16347028000000000000000000000) (-16345225000000000000000000000)) else (if n < 235 then (box (-14337972000000000000000000000) (-14336158000000000000000000000)) else (box (-12310277000000000000000000000) (-12308452000000000000000000000)))))) else (if n < 241 then (if n < 238 then (if n < 237 then (box (-10263917000000000000000000000) (-10262081000000000000000000000)) else (box (-8198866000000000000000000000) (-8197019000000000000000000000))) else (if n < 239 then (box (-6115096000000000000000000000) (-6113238000000000000000000000)) else (if n < 240 then (box (-4012578000000000000000000000) (-4010710000000000000000000000)) else (box (-1891284000000000000000000000) (-1889405000000000000000000000))))) else (if n < 244 then (if n < 242 then (box (248818000000000000000000000) (250707000000000000000000000)) else (if n < 243 then (box (2407757000000000000000000000) (2409657000000000000000000000)) else (box (4585566000000000000000000000) (4587477000000000000000000000)))) else (if n < 245 then (box (6782277000000000000000000000) (6784199000000000000000000000)) else (if n < 246 then (box (8997924000000000000000000000) (8999857000000000000000000000)) else (box (11232543000000000000000000000) (11234487000000000000000000000)))))))
def cQ247_270 (n:Nat):IV:=(if n < 258 then (if n < 252 then (if n < 249 then (if n < 248 then (box (13486168000000000000000000000) (13488123000000000000000000000)) else (box (15758835000000000000000000000) (15760801000000000000000000000))) else (if n < 250 then (box (18050582000000000000000000000) (18052559000000000000000000000)) else (if n < 251 then (box (20361446000000000000000000000) (20363434000000000000000000000)) else (box (22691466000000000000000000000) (22693466000000000000000000000))))) else (if n < 255 then (if n < 253 then (box (25040682000000000000000000000) (25042693000000000000000000000)) else (if n < 254 then (box (27409135000000000000000000000) (27411157000000000000000000000)) else (box (29796864000000000000000000000) (29798897000000000000000000000)))) else (if n < 256 then (box (32203912000000000000000000000) (32205957000000000000000000000)) else (if n < 257 then (box (34630322000000000000000000000) (34632379000000000000000000000)) else (box (37076138000000000000000000000) (37078206000000000000000000000)))))) else (if n < 264 then (if n < 261 then (if n < 259 then (box (39541404000000000000000000000) (39543483000000000000000000000)) else (if n < 260 then (box (42026164000000000000000000000) (42028255000000000000000000000)) else (box (44530466000000000000000000000) (44532568000000000000000000000)))) else (if n < 262 then (box (47054355000000000000000000000) (47056469000000000000000000000)) else (if n < 263 then (box (49597880000000000000000000000) (49600005000000000000000000000)) else (box (52161088000000000000000000000) (52163224000000000000000000000))))) else (if n < 267 then (if n < 265 then (box (54744028000000000000000000000) (54746176000000000000000000000)) else (if n < 266 then (box (57346751000000000000000000000) (57348910000000000000000000000)) else (box (59969306000000000000000000000) (59971477000000000000000000000)))) else (if n < 268 then (box (62611745000000000000000000000) (62613928000000000000000000000)) else (if n < 269 then (box (65274121000000000000000000000) (65276315000000000000000000000)) else (box (67956485000000000000000000000) (67958691000000000000000000000)))))))
def cQ225_270 (n:Nat):IV:=(if n < 247 then (cQ225_247 n) else (cQ247_270 n))
def cQ180_270 (n:Nat):IV:=(if n < 225 then (cQ180_225 n) else (cQ225_270 n))
def cQ270_292 (n:Nat):IV:=(if n < 281 then (if n < 275 then (if n < 272 then (if n < 271 then (box (70658892000000000000000000000) (70661110000000000000000000000)) else (box (73381396000000000000000000000) (73383626000000000000000000000))) else (if n < 273 then (box (76124051000000000000000000000) (76126293000000000000000000000)) else (if n < 274 then (box (78886914000000000000000000000) (78889168000000000000000000000)) else (box (81670041000000000000000000000) (81672307000000000000000000000))))) else (if n < 278 then (if n < 276 then (box (84473489000000000000000000000) (84475767000000000000000000000)) else (if n < 277 then (box (87297317000000000000000000000) (87299607000000000000000000000)) else (box (90141582000000000000000000000) (90143884000000000000000000000)))) else (if n < 279 then (box (93006345000000000000000000000) (93008659000000000000000000000)) else (if n < 280 then (box (95891665000000000000000000000) (95893992000000000000000000000)) else (box (98797604000000000000000000000) (98799943000000000000000000000)))))) else (if n < 286 then (if n < 283 then (if n < 282 then (box (101724222000000000000000000000) (101726574000000000000000000000)) else (box (104671582000000000000000000000) (104673947000000000000000000000))) else (if n < 284 then (box (107639748000000000000000000000) (107642125000000000000000000000)) else (if n < 285 then (box (110628783000000000000000000000) (110631172000000000000000000000)) else (box (113638751000000000000000000000) (113641152000000000000000000000))))) else (if n < 289 then (if n < 287 then (box (116669717000000000000000000000) (116672131000000000000000000000)) else (if n < 288 then (box (119721748000000000000000000000) (119724174000000000000000000000)) else (box (122794909000000000000000000000) (122797347000000000000000000000)))) else (if n < 290 then (box (125889268000000000000000000000) (125891719000000000000000000000)) else (if n < 291 then (box (129004893000000000000000000000) (129007357000000000000000000000)) else (box (132141853000000000000000000000) (132144330000000000000000000000)))))))
def cQ292_315 (n:Nat):IV:=(if n < 303 then (if n < 297 then (if n < 294 then (if n < 293 then (box (135300216000000000000000000000) (135302706000000000000000000000)) else (box (138480053000000000000000000000) (138482556000000000000000000000))) else (if n < 295 then (box (141681436000000000000000000000) (141683951000000000000000000000)) else (if n < 296 then (box (144904434000000000000000000000) (144906962000000000000000000000)) else (box (148149120000000000000000000000) (148151661000000000000000000000))))) else (if n < 300 then (if n < 298 then (box (151415567000000000000000000000) (151418121000000000000000000000)) else (if n < 299 then (box (154703849000000000000000000000) (154706416000000000000000000000)) else (box (158014039000000000000000000000) (158016619000000000000000000000)))) else (if n < 301 then (box (161346213000000000000000000000) (161348806000000000000000000000)) else (if n < 302 then (box (164700446000000000000000000000) (164703052000000000000000000000)) else (box (168076814000000000000000000000) (168079433000000000000000000000)))))) else (if n < 309 then (if n < 306 then (if n < 304 then (box (171475395000000000000000000000) (171478027000000000000000000000)) else (if n < 305 then (box (174896265000000000000000000000) (174898910000000000000000000000)) else (box (178339504000000000000000000000) (178342162000000000000000000000)))) else (if n < 307 then (box (181805189000000000000000000000) (181807860000000000000000000000)) else (if n < 308 then (box (185293401000000000000000000000) (185296086000000000000000000000)) else (box (188804221000000000000000000000) (188806919000000000000000000000))))) else (if n < 312 then (if n < 310 then (box (192337730000000000000000000000) (192340441000000000000000000000)) else (if n < 311 then (box (195894008000000000000000000000) (195896732000000000000000000000)) else (box (199473139000000000000000000000) (199475876000000000000000000000)))) else (if n < 313 then (box (203075206000000000000000000000) (203077956000000000000000000000)) else (if n < 314 then (box (206700292000000000000000000000) (206703056000000000000000000000)) else (box (210348482000000000000000000000) (210351259000000000000000000000)))))))
def cQ270_315 (n:Nat):IV:=(if n < 292 then (cQ270_292 n) else (cQ292_315 n))
def cQ315_337 (n:Nat):IV:=(if n < 326 then (if n < 320 then (if n < 317 then (if n < 316 then (box (214019860000000000000000000000) (214022651000000000000000000000)) else (box (217714514000000000000000000000) (217717319000000000000000000000))) else (if n < 318 then (box (221432530000000000000000000000) (221435348000000000000000000000)) else (if n < 319 then (box (225173994000000000000000000000) (225176826000000000000000000000)) else (box (228938995000000000000000000000) (228941841000000000000000000000))))) else (if n < 323 then (if n < 321 then (box (232727622000000000000000000000) (232730482000000000000000000000)) else (if n < 322 then (box (236539963000000000000000000000) (236542837000000000000000000000)) else (box (240376109000000000000000000000) (240378997000000000000000000000)))) else (if n < 324 then (box (244236150000000000000000000000) (244239052000000000000000000000)) else (if n < 325 then (box (248120178000000000000000000000) (248123094000000000000000000000)) else (box (252028285000000000000000000000) (252031215000000000000000000000)))))) else (if n < 331 then (if n < 328 then (if n < 327 then (box (255960563000000000000000000000) (255963507000000000000000000000)) else (box (259917107000000000000000000000) (259920065000000000000000000000))) else (if n < 329 then (box (263898010000000000000000000000) (263900982000000000000000000000)) else (if n < 330 then (box (267903367000000000000000000000) (267906353000000000000000000000)) else (box (271933274000000000000000000000) (271936274000000000000000000000))))) else (if n < 334 then (if n < 332 then (box (275987826000000000000000000000) (275990840000000000000000000000)) else (if n < 333 then (box (280067121000000000000000000000) (280070149000000000000000000000)) else (box (284171256000000000000000000000) (284174298000000000000000000000)))) else (if n < 335 then (box (288300330000000000000000000000) (288303386000000000000000000000)) else (if n < 336 then (box (292454442000000000000000000000) (292457512000000000000000000000)) else (box (296633691000000000000000000000) (296636775000000000000000000000)))))))
def cQ337_360 (n:Nat):IV:=(if n < 348 then (if n < 342 then (if n < 339 then (if n < 338 then (box (300838178000000000000000000000) (300841276000000000000000000000)) else (box (305068004000000000000000000000) (305071116000000000000000000000))) else (if n < 340 then (box (309323271000000000000000000000) (309326397000000000000000000000)) else (if n < 341 then (box (313604081000000000000000000000) (313607222000000000000000000000)) else (box (317910537000000000000000000000) (317913692000000000000000000000))))) else (if n < 345 then (if n < 343 then (box (322242744000000000000000000000) (322245913000000000000000000000)) else (if n < 344 then (box (326600806000000000000000000000) (326603989000000000000000000000)) else (box (330984829000000000000000000000) (330988026000000000000000000000)))) else (if n < 346 then (box (335394919000000000000000000000) (335398130000000000000000000000)) else (if n < 347 then (box (339831181000000000000000000000) (339834407000000000000000000000)) else (box (344293725000000000000000000000) (344296965000000000000000000000)))))) else (if n < 354 then (if n < 351 then (if n < 349 then (box (348782658000000000000000000000) (348785912000000000000000000000)) else (if n < 350 then (box (353298090000000000000000000000) (353301358000000000000000000000)) else (box (357840129000000000000000000000) (357843411000000000000000000000)))) else (if n < 352 then (box (362408886000000000000000000000) (362412183000000000000000000000)) else (if n < 353 then (box (367004473000000000000000000000) (367007785000000000000000000000)) else (box (371627001000000000000000000000) (371630327000000000000000000000))))) else (if n < 357 then (if n < 355 then (box (376276584000000000000000000000) (376279924000000000000000000000)) else (if n < 356 then (box (380953333000000000000000000000) (380956687000000000000000000000)) else (box (385657363000000000000000000000) (385660732000000000000000000000)))) else (if n < 358 then (box (390388789000000000000000000000) (390392173000000000000000000000)) else (if n < 359 then (box (395147727000000000000000000000) (395151125000000000000000000000)) else (box (399934292000000000000000000000) (399937705000000000000000000000)))))))
def cQ315_360 (n:Nat):IV:=(if n < 337 then (cQ315_337 n) else (cQ337_360 n))
def cQ270_360 (n:Nat):IV:=(if n < 315 then (cQ270_315 n) else (cQ315_360 n))
def cQ180_360 (n:Nat):IV:=(if n < 270 then (cQ180_270 n) else (cQ270_360 n))
def cQ0_360 (n:Nat):IV:=(if n < 180 then (cQ0_180 n) else (cQ180_360 n))
def cQ360_382 (n:Nat):IV:=(if n < 371 then (if n < 365 then (if n < 362 then (if n < 361 then (box (404748602000000000000000000000) (404752030000000000000000000000)) else (box (409590775000000000000000000000) (409594217000000000000000000000))) else (if n < 363 then (box (414460929000000000000000000000) (414464386000000000000000000000)) else (if n < 364 then (box (419359182000000000000000000000) (419362654000000000000000000000)) else (box (424285655000000000000000000000) (424289142000000000000000000000))))) else (if n < 368 then (if n < 366 then (box (429240470000000000000000000000) (429243972000000000000000000000)) else (if n < 367 then (box (434223747000000000000000000000) (434227263000000000000000000000)) else (box (439235608000000000000000000000) (439239138000000000000000000000)))) else (if n < 369 then (box (444276177000000000000000000000) (444279722000000000000000000000)) else (if n < 370 then (box (449345576000000000000000000000) (449349136000000000000000000000)) else (box (454443932000000000000000000000) (454447507000000000000000000000)))))) else (if n < 376 then (if n < 373 then (if n < 372 then (box (459571368000000000000000000000) (459574958000000000000000000000)) else (box (464728012000000000000000000000) (464731617000000000000000000000))) else (if n < 374 then (box (469913989000000000000000000000) (469917609000000000000000000000)) else (if n < 375 then (box (475129428000000000000000000000) (475133063000000000000000000000)) else (box (480374457000000000000000000000) (480378107000000000000000000000))))) else (if n < 379 then (if n < 377 then (box (485649205000000000000000000000) (485652870000000000000000000000)) else (if n < 378 then (box (490953800000000000000000000000) (490957480000000000000000000000)) else (box (496288375000000000000000000000) (496292070000000000000000000000)))) else (if n < 380 then (box (501653062000000000000000000000) (501656772000000000000000000000)) else (if n < 381 then (box (507047992000000000000000000000) (507051717000000000000000000000)) else (box (512473297000000000000000000000) (512477038000000000000000000000)))))))
def cQ382_405 (n:Nat):IV:=(if n < 393 then (if n < 387 then (if n < 384 then (if n < 383 then (box (517929113000000000000000000000) (517932869000000000000000000000)) else (box (523415573000000000000000000000) (523419344000000000000000000000))) else (if n < 385 then (box (528932814000000000000000000000) (528936600000000000000000000000)) else (if n < 386 then (box (534480971000000000000000000000) (534484772000000000000000000000)) else (box (540060181000000000000000000000) (540063997000000000000000000000))))) else (if n < 390 then (if n < 388 then (box (545670582000000000000000000000) (545674414000000000000000000000)) else (if n < 389 then (box (551312313000000000000000000000) (551316160000000000000000000000)) else (box (556985514000000000000000000000) (556989376000000000000000000000)))) else (if n < 391 then (box (562690324000000000000000000000) (562694202000000000000000000000)) else (if n < 392 then (box (568426885000000000000000000000) (568430778000000000000000000000)) else (box (574195338000000000000000000000) (574199246000000000000000000000)))))) else (if n < 399 then (if n < 396 then (if n < 394 then (box (579995827000000000000000000000) (579999750000000000000000000000)) else (if n < 395 then (box (585828494000000000000000000000) (585832433000000000000000000000)) else (box (591693485000000000000000000000) (591697440000000000000000000000)))) else (if n < 397 then (box (597590945000000000000000000000) (597594915000000000000000000000)) else (if n < 398 then (box (603521019000000000000000000000) (603525005000000000000000000000)) else (box (609483855000000000000000000000) (609487857000000000000000000000))))) else (if n < 402 then (if n < 400 then (box (615479600000000000000000000000) (615483618000000000000000000000)) else (if n < 401 then (box (621508403000000000000000000000) (621512436000000000000000000000)) else (box (627570414000000000000000000000) (627574463000000000000000000000)))) else (if n < 403 then (box (633665782000000000000000000000) (633669847000000000000000000000)) else (if n < 404 then (box (639794659000000000000000000000) (639798740000000000000000000000)) else (box (645957196000000000000000000000) (645961293000000000000000000000)))))))
def cQ360_405 (n:Nat):IV:=(if n < 382 then (cQ360_382 n) else (cQ382_405 n))
def cQ405_427 (n:Nat):IV:=(if n < 416 then (if n < 410 then (if n < 407 then (if n < 406 then (box (652153548000000000000000000000) (652157660000000000000000000000)) else (box (658383867000000000000000000000) (658387995000000000000000000000))) else (if n < 408 then (box (664648308000000000000000000000) (664652452000000000000000000000)) else (if n < 409 then (box (670947027000000000000000000000) (670951187000000000000000000000)) else (box (677280180000000000000000000000) (677284356000000000000000000000))))) else (if n < 413 then (if n < 411 then (box (683647924000000000000000000000) (683652116000000000000000000000)) else (if n < 412 then (box (690050417000000000000000000000) (690054625000000000000000000000)) else (box (696487819000000000000000000000) (696492044000000000000000000000)))) else (if n < 414 then (box (702960290000000000000000000000) (702964531000000000000000000000)) else (if n < 415 then (box (709467989000000000000000000000) (709472246000000000000000000000)) else (box (716011079000000000000000000000) (716015352000000000000000000000)))))) else (if n < 421 then (if n < 418 then (if n < 417 then (box (722589723000000000000000000000) (722594013000000000000000000000)) else (box (729204085000000000000000000000) (729208391000000000000000000000))) else (if n < 419 then (box (735854328000000000000000000000) (735858650000000000000000000000)) else (if n < 420 then (box (742540617000000000000000000000) (742544955000000000000000000000)) else (box (749263120000000000000000000000) (749267474000000000000000000000))))) else (if n < 424 then (if n < 422 then (box (756022003000000000000000000000) (756026373000000000000000000000)) else (if n < 423 then (box (762817435000000000000000000000) (762821821000000000000000000000)) else (box (769649584000000000000000000000) (769653986000000000000000000000)))) else (if n < 425 then (box (776518620000000000000000000000) (776523039000000000000000000000)) else (if n < 426 then (box (783424715000000000000000000000) (783429150000000000000000000000)) else (box (790368040000000000000000000000) (790372492000000000000000000000)))))))
def cQ427_450 (n:Nat):IV:=(if n < 438 then (if n < 432 then (if n < 429 then (if n < 428 then (box (797348767000000000000000000000) (797353236000000000000000000000)) else (box (804367072000000000000000000000) (804371558000000000000000000000))) else (if n < 430 then (box (811423129000000000000000000000) (811427631000000000000000000000)) else (if n < 431 then (box (818517112000000000000000000000) (818521631000000000000000000000)) else (box (825649198000000000000000000000) (825653734000000000000000000000))))) else (if n < 435 then (if n < 433 then (box (832819566000000000000000000000) (832824119000000000000000000000)) else (if n < 434 then (box (840028394000000000000000000000) (840032964000000000000000000000)) else (box (847275862000000000000000000000) (847280449000000000000000000000)))) else (if n < 436 then (box (854562150000000000000000000000) (854566753000000000000000000000)) else (if n < 437 then (box (861887439000000000000000000000) (861892059000000000000000000000)) else (box (869251911000000000000000000000) (869256548000000000000000000000)))))) else (if n < 444 then (if n < 441 then (if n < 439 then (box (876655751000000000000000000000) (876660405000000000000000000000)) else (if n < 440 then (box (884099144000000000000000000000) (884103815000000000000000000000)) else (box (891582274000000000000000000000) (891586961000000000000000000000)))) else (if n < 442 then (box (899105327000000000000000000000) (899110031000000000000000000000)) else (if n < 443 then (box (906668493000000000000000000000) (906673214000000000000000000000)) else (box (914271957000000000000000000000) (914276695000000000000000000000))))) else (if n < 447 then (if n < 445 then (box (921915911000000000000000000000) (921920666000000000000000000000)) else (if n < 446 then (box (929600545000000000000000000000) (929605317000000000000000000000)) else (box (937326051000000000000000000000) (937330840000000000000000000000)))) else (if n < 448 then (box (945092622000000000000000000000) (945097428000000000000000000000)) else (if n < 449 then (box (952900448000000000000000000000) (952905272000000000000000000000)) else (box (960749728000000000000000000000) (960754569000000000000000000000)))))))
def cQ405_450 (n:Nat):IV:=(if n < 427 then (cQ405_427 n) else (cQ427_450 n))
def cQ360_450 (n:Nat):IV:=(if n < 405 then (cQ360_405 n) else (cQ405_450 n))
def cQ450_472 (n:Nat):IV:=(if n < 461 then (if n < 455 then (if n < 452 then (if n < 451 then (box (968640657000000000000000000000) (968645515000000000000000000000)) else (box (976573429000000000000000000000) (976578305000000000000000000000))) else (if n < 453 then (box (984548245000000000000000000000) (984553138000000000000000000000)) else (if n < 454 then (box (992565302000000000000000000000) (992570213000000000000000000000)) else (box (1000624802000000000000000000000) (1000629730000000000000000000000))))) else (if n < 458 then (if n < 456 then (box (1008726943000000000000000000000) (1008731888000000000000000000000)) else (if n < 457 then (box (1016871929000000000000000000000) (1016876892000000000000000000000)) else (box (1025059964000000000000000000000) (1025064944000000000000000000000)))) else (if n < 459 then (box (1033291251000000000000000000000) (1033296248000000000000000000000)) else (if n < 460 then (box (1041565995000000000000000000000) (1041571010000000000000000000000)) else (box (1049884403000000000000000000000) (1049889435000000000000000000000)))))) else (if n < 466 then (if n < 463 then (if n < 462 then (box (1058246683000000000000000000000) (1058251733000000000000000000000)) else (box (1066653043000000000000000000000) (1066658110000000000000000000000))) else (if n < 464 then (box (1075103693000000000000000000000) (1075108778000000000000000000000)) else (if n < 465 then (box (1083598844000000000000000000000) (1083603946000000000000000000000)) else (box (1092138708000000000000000000000) (1092143828000000000000000000000))))) else (if n < 469 then (if n < 467 then (box (1100723498000000000000000000000) (1100728635000000000000000000000)) else (if n < 468 then (box (1109353428000000000000000000000) (1109358583000000000000000000000)) else (box (1118028714000000000000000000000) (1118033886000000000000000000000)))) else (if n < 470 then (box (1126749571000000000000000000000) (1126754761000000000000000000000)) else (if n < 471 then (box (1135516219000000000000000000000) (1135521426000000000000000000000)) else (box (1144328875000000000000000000000) (1144334100000000000000000000000)))))))
def cQ472_495 (n:Nat):IV:=(if n < 483 then (if n < 477 then (if n < 474 then (if n < 473 then (box (1153187761000000000000000000000) (1153193003000000000000000000000)) else (box (1162093096000000000000000000000) (1162098356000000000000000000000))) else (if n < 475 then (box (1171045102000000000000000000000) (1171050380000000000000000000000)) else (if n < 476 then (box (1180044004000000000000000000000) (1180049300000000000000000000000)) else (box (1189090027000000000000000000000) (1189095340000000000000000000000))))) else (if n < 480 then (if n < 478 then (box (1198183396000000000000000000000) (1198188727000000000000000000000)) else (if n < 479 then (box (1207324338000000000000000000000) (1207329687000000000000000000000)) else (box (1216513082000000000000000000000) (1216518449000000000000000000000)))) else (if n < 481 then (box (1225749856000000000000000000000) (1225755241000000000000000000000)) else (if n < 482 then (box (1235034892000000000000000000000) (1235040296000000000000000000000)) else (box (1244368422000000000000000000000) (1244373844000000000000000000000)))))) else (if n < 489 then (if n < 486 then (if n < 484 then (box (1253750678000000000000000000000) (1253756118000000000000000000000)) else (if n < 485 then (box (1263181894000000000000000000000) (1263187353000000000000000000000)) else (box (1272662307000000000000000000000) (1272667785000000000000000000000)))) else (if n < 487 then (box (1282192153000000000000000000000) (1282197649000000000000000000000)) else (if n < 488 then (box (1291771669000000000000000000000) (1291777184000000000000000000000)) else (box (1301401096000000000000000000000) (1301406630000000000000000000000))))) else (if n < 492 then (if n < 490 then (box (1311080674000000000000000000000) (1311086226000000000000000000000)) else (if n < 491 then (box (1320810644000000000000000000000) (1320816214000000000000000000000)) else (box (1330591250000000000000000000000) (1330596839000000000000000000000)))) else (if n < 493 then (box (1340422736000000000000000000000) (1340428344000000000000000000000)) else (if n < 494 then (box (1350305347000000000000000000000) (1350310973000000000000000000000)) else (box (1360239331000000000000000000000) (1360244975000000000000000000000)))))))
def cQ450_495 (n:Nat):IV:=(if n < 472 then (cQ450_472 n) else (cQ472_495 n))
def cQ495_517 (n:Nat):IV:=(if n < 506 then (if n < 500 then (if n < 497 then (if n < 496 then (box (1370224935000000000000000000000) (1370230598000000000000000000000)) else (box (1380262409000000000000000000000) (1380268090000000000000000000000))) else (if n < 498 then (box (1390352004000000000000000000000) (1390357704000000000000000000000)) else (if n < 499 then (box (1400493971000000000000000000000) (1400499689000000000000000000000)) else (box (1410688565000000000000000000000) (1410694301000000000000000000000))))) else (if n < 503 then (if n < 501 then (box (1420936039000000000000000000000) (1420941793000000000000000000000)) else (if n < 502 then (box (1431236649000000000000000000000) (1431242422000000000000000000000)) else (box (1441590653000000000000000000000) (1441596444000000000000000000000)))) else (if n < 504 then (box (1451998311000000000000000000000) (1452004121000000000000000000000)) else (if n < 505 then (box (1462459881000000000000000000000) (1462465710000000000000000000000)) else (box (1472975625000000000000000000000) (1472981473000000000000000000000)))))) else (if n < 511 then (if n < 508 then (if n < 507 then (box (1483545805000000000000000000000) (1483551672000000000000000000000)) else (box (1494170687000000000000000000000) (1494176573000000000000000000000))) else (if n < 509 then (box (1504850534000000000000000000000) (1504856439000000000000000000000)) else (if n < 510 then (box (1515585616000000000000000000000) (1515591540000000000000000000000)) else (box (1526376198000000000000000000000) (1526382141000000000000000000000))))) else (if n < 514 then (if n < 512 then (box (1537222552000000000000000000000) (1537228514000000000000000000000)) else (if n < 513 then (box (1548124948000000000000000000000) (1548130929000000000000000000000)) else (box (1559083657000000000000000000000) (1559089658000000000000000000000)))) else (if n < 515 then (box (1570098955000000000000000000000) (1570104976000000000000000000000)) else (if n < 516 then (box (1581171116000000000000000000000) (1581177156000000000000000000000)) else (box (1592300418000000000000000000000) (1592306477000000000000000000000)))))))
def cQ517_540 (n:Nat):IV:=(if n < 528 then (if n < 522 then (if n < 519 then (if n < 518 then (box (1603487137000000000000000000000) (1603493216000000000000000000000)) else (box (1614731555000000000000000000000) (1614737654000000000000000000000))) else (if n < 520 then (box (1626033952000000000000000000000) (1626040070000000000000000000000)) else (if n < 521 then (box (1637394610000000000000000000000) (1637400747000000000000000000000)) else (box (1648813812000000000000000000000) (1648819969000000000000000000000))))) else (if n < 525 then (if n < 523 then (box (1660291846000000000000000000000) (1660298022000000000000000000000)) else (if n < 524 then (box (1671828997000000000000000000000) (1671835193000000000000000000000)) else (box (1683425554000000000000000000000) (1683431769000000000000000000000)))) else (if n < 526 then (box (1695081806000000000000000000000) (1695088041000000000000000000000)) else (if n < 527 then (box (1706798045000000000000000000000) (1706804300000000000000000000000)) else (box (1718574563000000000000000000000) (1718580837000000000000000000000)))))) else (if n < 534 then (if n < 531 then (if n < 529 then (box (1730411655000000000000000000000) (1730417949000000000000000000000)) else (if n < 530 then (box (1742309617000000000000000000000) (1742315931000000000000000000000)) else (box (1754268745000000000000000000000) (1754275079000000000000000000000)))) else (if n < 532 then (box (1766289340000000000000000000000) (1766295693000000000000000000000)) else (if n < 533 then (box (1778371701000000000000000000000) (1778378074000000000000000000000)) else (box (1790516130000000000000000000000) (1790522523000000000000000000000))))) else (if n < 537 then (if n < 535 then (box (1802722932000000000000000000000) (1802729345000000000000000000000)) else (if n < 536 then (box (1814992410000000000000000000000) (1814998843000000000000000000000)) else (box (1827324871000000000000000000000) (1827331324000000000000000000000)))) else (if n < 538 then (box (1839720624000000000000000000000) (1839727097000000000000000000000)) else (if n < 539 then (box (1852179979000000000000000000000) (1852186472000000000000000000000)) else (box (1864703247000000000000000000000) (1864709760000000000000000000000)))))))
def cQ495_540 (n:Nat):IV:=(if n < 517 then (cQ495_517 n) else (cQ517_540 n))
def cQ450_540 (n:Nat):IV:=(if n < 495 then (cQ450_495 n) else (cQ495_540 n))
def cQ360_540 (n:Nat):IV:=(if n < 450 then (cQ360_450 n) else (cQ450_540 n))
def cQ540_562 (n:Nat):IV:=(if n < 551 then (if n < 545 then (if n < 542 then (if n < 541 then (box (1877290742000000000000000000000) (1877297275000000000000000000000)) else (box (1889942777000000000000000000000) (1889949330000000000000000000000))) else (if n < 543 then (box (1902659667000000000000000000000) (1902666241000000000000000000000)) else (if n < 544 then (box (1915441732000000000000000000000) (1915448327000000000000000000000)) else (box (1928289292000000000000000000000) (1928295907000000000000000000000))))) else (if n < 548 then (if n < 546 then (box (1941202667000000000000000000000) (1941209303000000000000000000000)) else (if n < 547 then (box (1954182180000000000000000000000) (1954188836000000000000000000000)) else (box (1967228156000000000000000000000) (1967234832000000000000000000000)))) else (if n < 549 then (box (1980340919000000000000000000000) (1980347616000000000000000000000)) else (if n < 550 then (box (1993520799000000000000000000000) (1993527517000000000000000000000)) else (box (2006768126000000000000000000000) (2006774864000000000000000000000)))))) else (if n < 556 then (if n < 553 then (if n < 552 then (box (2020083228000000000000000000000) (2020089987000000000000000000000)) else (box (2033466441000000000000000000000) (2033473220000000000000000000000))) else (if n < 554 then (box (2046918097000000000000000000000) (2046924897000000000000000000000)) else (if n < 555 then (box (2060438533000000000000000000000) (2060445354000000000000000000000)) else (box (2074028089000000000000000000000) (2074034931000000000000000000000))))) else (if n < 559 then (if n < 557 then (box (2087687102000000000000000000000) (2087693965000000000000000000000)) else (if n < 558 then (box (2101415914000000000000000000000) (2101422798000000000000000000000)) else (box (2115214870000000000000000000000) (2115221775000000000000000000000)))) else (if n < 560 then (box (2129084314000000000000000000000) (2129091240000000000000000000000)) else (if n < 561 then (box (2143024591000000000000000000000) (2143031538000000000000000000000)) else (box (2157036051000000000000000000000) (2157043019000000000000000000000)))))))
def cQ562_585 (n:Nat):IV:=(if n < 573 then (if n < 567 then (if n < 564 then (if n < 563 then (box (2171119043000000000000000000000) (2171126032000000000000000000000)) else (box (2185273921000000000000000000000) (2185280931000000000000000000000))) else (if n < 565 then (box (2199501037000000000000000000000) (2199508068000000000000000000000)) else (if n < 566 then (box (2213800748000000000000000000000) (2213807800000000000000000000000)) else (box (2228173410000000000000000000000) (2228180483000000000000000000000))))) else (if n < 570 then (if n < 568 then (box (2242619384000000000000000000000) (2242626478000000000000000000000)) else (if n < 569 then (box (2257139030000000000000000000000) (2257146145000000000000000000000)) else (box (2271732712000000000000000000000) (2271739849000000000000000000000)))) else (if n < 571 then (box (2286400793000000000000000000000) (2286407952000000000000000000000)) else (if n < 572 then (box (2301143641000000000000000000000) (2301150821000000000000000000000)) else (box (2315961624000000000000000000000) (2315968825000000000000000000000)))))) else (if n < 579 then (if n < 576 then (if n < 574 then (box (2330855112000000000000000000000) (2330862335000000000000000000000)) else (if n < 575 then (box (2345824478000000000000000000000) (2345831723000000000000000000000)) else (box (2360870096000000000000000000000) (2360877363000000000000000000000)))) else (if n < 577 then (box (2375992343000000000000000000000) (2375999632000000000000000000000)) else (if n < 578 then (box (2391191595000000000000000000000) (2391198906000000000000000000000)) else (box (2406468234000000000000000000000) (2406475567000000000000000000000))))) else (if n < 582 then (if n < 580 then (box (2421822640000000000000000000000) (2421829995000000000000000000000)) else (if n < 581 then (box (2437255199000000000000000000000) (2437262576000000000000000000000)) else (box (2452766296000000000000000000000) (2452773695000000000000000000000)))) else (if n < 583 then (box (2468356317000000000000000000000) (2468363738000000000000000000000)) else (if n < 584 then (box (2484025653000000000000000000000) (2484033096000000000000000000000)) else (box (2499774697000000000000000000000) (2499782162000000000000000000000)))))))
def cQ540_585 (n:Nat):IV:=(if n < 562 then (cQ540_562 n) else (cQ562_585 n))
def cQ585_607 (n:Nat):IV:=(if n < 596 then (if n < 590 then (if n < 587 then (if n < 586 then (box (2515603840000000000000000000000) (2515611328000000000000000000000)) else (box (2531513480000000000000000000000) (2531520990000000000000000000000))) else (if n < 588 then (box (2547504014000000000000000000000) (2547511546000000000000000000000)) else (if n < 589 then (box (2563575843000000000000000000000) (2563583397000000000000000000000)) else (box (2579729365000000000000000000000) (2579736942000000000000000000000))))) else (if n < 593 then (if n < 591 then (box (2595964988000000000000000000000) (2595972588000000000000000000000)) else (if n < 592 then (box (2612283115000000000000000000000) (2612290737000000000000000000000)) else (box (2628684155000000000000000000000) (2628691800000000000000000000000)))) else (if n < 594 then (box (2645168519000000000000000000000) (2645176187000000000000000000000)) else (if n < 595 then (box (2661736617000000000000000000000) (2661744308000000000000000000000)) else (box (2678388864000000000000000000000) (2678396578000000000000000000000)))))) else (if n < 601 then (if n < 598 then (if n < 597 then (box (2695125677000000000000000000000) (2695133414000000000000000000000)) else (box (2711947475000000000000000000000) (2711955235000000000000000000000))) else (if n < 599 then (box (2728854678000000000000000000000) (2728862461000000000000000000000)) else (if n < 600 then (box (2745847708000000000000000000000) (2745855514000000000000000000000)) else (box (2762926989000000000000000000000) (2762934818000000000000000000000))))) else (if n < 604 then (if n < 602 then (box (2780092950000000000000000000000) (2780100802000000000000000000000)) else (if n < 603 then (box (2797346019000000000000000000000) (2797353894000000000000000000000)) else (box (2814686626000000000000000000000) (2814694524000000000000000000000)))) else (if n < 605 then (box (2832115207000000000000000000000) (2832123129000000000000000000000)) else (if n < 606 then (box (2849632197000000000000000000000) (2849640142000000000000000000000)) else (box (2867238032000000000000000000000) (2867246000000000000000000000000)))))))
def cQ607_630 (n:Nat):IV:=(if n < 618 then (if n < 612 then (if n < 609 then (if n < 608 then (box (2884933154000000000000000000000) (2884941145000000000000000000000)) else (box (2902718006000000000000000000000) (2902726020000000000000000000000))) else (if n < 610 then (box (2920593031000000000000000000000) (2920601068000000000000000000000)) else (if n < 611 then (box (2938558676000000000000000000000) (2938566737000000000000000000000)) else (box (2956615391000000000000000000000) (2956623476000000000000000000000))))) else (if n < 615 then (if n < 613 then (box (2974763626000000000000000000000) (2974771735000000000000000000000)) else (if n < 614 then (box (2993003836000000000000000000000) (2993011969000000000000000000000)) else (box (3011336477000000000000000000000) (3011344634000000000000000000000)))) else (if n < 616 then (box (3029762007000000000000000000000) (3029770188000000000000000000000)) else (if n < 617 then (box (3048280888000000000000000000000) (3048289093000000000000000000000)) else (box (3066893580000000000000000000000) (3066901809000000000000000000000)))))) else (if n < 624 then (if n < 621 then (if n < 619 then (box (3085600550000000000000000000000) (3085608803000000000000000000000)) else (if n < 620 then (box (3104402266000000000000000000000) (3104410543000000000000000000000)) else (box (3123299198000000000000000000000) (3123307500000000000000000000000)))) else (if n < 622 then (box (3142291818000000000000000000000) (3142300145000000000000000000000)) else (if n < 623 then (box (3161380601000000000000000000000) (3161388952000000000000000000000)) else (box (3180566023000000000000000000000) (3180574399000000000000000000000))))) else (if n < 627 then (if n < 625 then (box (3199848565000000000000000000000) (3199856966000000000000000000000)) else (if n < 626 then (box (3219228708000000000000000000000) (3219237134000000000000000000000)) else (box (3238706938000000000000000000000) (3238715389000000000000000000000)))) else (if n < 628 then (box (3258283740000000000000000000000) (3258292215000000000000000000000)) else (if n < 629 then (box (3277959605000000000000000000000) (3277968105000000000000000000000)) else (box (3297735025000000000000000000000) (3297743550000000000000000000000)))))))
def cQ585_630 (n:Nat):IV:=(if n < 607 then (cQ585_607 n) else (cQ607_630 n))
def cQ540_630 (n:Nat):IV:=(if n < 585 then (cQ540_585 n) else (cQ585_630 n))
def cQ630_652 (n:Nat):IV:=(if n < 641 then (if n < 635 then (if n < 632 then (if n < 631 then (box (3317610494000000000000000000000) (3317619044000000000000000000000)) else (box (3337586509000000000000000000000) (3337595084000000000000000000000))) else (if n < 633 then (box (3357663568000000000000000000000) (3357672168000000000000000000000)) else (if n < 634 then (box (3377842175000000000000000000000) (3377850800000000000000000000000)) else (box (3398122833000000000000000000000) (3398131483000000000000000000000))))) else (if n < 638 then (if n < 636 then (box (3418506049000000000000000000000) (3418514724000000000000000000000)) else (if n < 637 then (box (3438992334000000000000000000000) (3439001034000000000000000000000)) else (box (3459582198000000000000000000000) (3459590924000000000000000000000)))) else (if n < 639 then (box (3480276158000000000000000000000) (3480284909000000000000000000000)) else (if n < 640 then (box (3501074732000000000000000000000) (3501083508000000000000000000000)) else (box (3521978436000000000000000000000) (3521987238000000000000000000000)))))) else (if n < 646 then (if n < 643 then (if n < 642 then (box (3542987795000000000000000000000) (3542996623000000000000000000000)) else (box (3564103334000000000000000000000) (3564112188000000000000000000000))) else (if n < 644 then (box (3585325579000000000000000000000) (3585334459000000000000000000000)) else (if n < 645 then (box (3606655065000000000000000000000) (3606663971000000000000000000000)) else (box (3628092321000000000000000000000) (3628101253000000000000000000000))))) else (if n < 649 then (if n < 647 then (box (3649637885000000000000000000000) (3649646843000000000000000000000)) else (if n < 648 then (box (3671292298000000000000000000000) (3671301282000000000000000000000)) else (box (3693056098000000000000000000000) (3693065108000000000000000000000)))) else (if n < 650 then (box (3714929829000000000000000000000) (3714938865000000000000000000000)) else (if n < 651 then (box (3736914037000000000000000000000) (3736923099000000000000000000000)) else (box (3759009275000000000000000000000) (3759018363000000000000000000000)))))))
def cQ652_675 (n:Nat):IV:=(if n < 663 then (if n < 657 then (if n < 654 then (if n < 653 then (box (3781216094000000000000000000000) (3781225208000000000000000000000)) else (box (3803535048000000000000000000000) (3803544189000000000000000000000))) else (if n < 655 then (box (3825966695000000000000000000000) (3825975863000000000000000000000)) else (if n < 656 then (box (3848511598000000000000000000000) (3848520792000000000000000000000)) else (box (3871170317000000000000000000000) (3871179538000000000000000000000))))) else (if n < 660 then (if n < 658 then (box (3893943422000000000000000000000) (3893952670000000000000000000000)) else (if n < 659 then (box (3916831481000000000000000000000) (3916840756000000000000000000000)) else (box (3939835065000000000000000000000) (3939844367000000000000000000000)))) else (if n < 661 then (box (3962954751000000000000000000000) (3962964080000000000000000000000)) else (if n < 662 then (box (3986191116000000000000000000000) (3986200472000000000000000000000)) else (box (4009544742000000000000000000000) (4009554125000000000000000000000)))))) else (if n < 669 then (if n < 666 then (if n < 664 then (box (4033016211000000000000000000000) (4033025621000000000000000000000)) else (if n < 665 then (box (4056606110000000000000000000000) (4056615547000000000000000000000)) else (box (4080315031000000000000000000000) (4080324495000000000000000000000)))) else (if n < 667 then (box (4104143565000000000000000000000) (4104153056000000000000000000000)) else (if n < 668 then (box (4128092308000000000000000000000) (4128101826000000000000000000000)) else (box (4152161857000000000000000000000) (4152171403000000000000000000000))))) else (if n < 672 then (if n < 670 then (box (4176352817000000000000000000000) (4176362390000000000000000000000)) else (if n < 671 then (box (4200665792000000000000000000000) (4200675392000000000000000000000)) else (box (4225101387000000000000000000000) (4225111015000000000000000000000)))) else (if n < 673 then (box (4249660214000000000000000000000) (4249669870000000000000000000000)) else (if n < 674 then (box (4274342888000000000000000000000) (4274352572000000000000000000000)) else (box (4299150026000000000000000000000) (4299159739000000000000000000000)))))))
def cQ630_675 (n:Nat):IV:=(if n < 652 then (cQ630_652 n) else (cQ652_675 n))
def cQ675_698 (n:Nat):IV:=(if n < 686 then (if n < 680 then (if n < 677 then (if n < 676 then (box (4324082249000000000000000000000) (4324091990000000000000000000000)) else (box (4349140178000000000000000000000) (4349149948000000000000000000000))) else (if n < 678 then (box (4374324442000000000000000000000) (4374334241000000000000000000000)) else (if n < 679 then (box (4399635669000000000000000000000) (4399645497000000000000000000000)) else (box (4425074493000000000000000000000) (4425084349000000000000000000000))))) else (if n < 683 then (if n < 681 then (box (4450641549000000000000000000000) (4450651434000000000000000000000)) else (if n < 682 then (box (4476337477000000000000000000000) (4476347390000000000000000000000)) else (box (4502162918000000000000000000000) (4502172860000000000000000000000)))) else (if n < 684 then (box (4528118519000000000000000000000) (4528128490000000000000000000000)) else (if n < 685 then (box (4554204928000000000000000000000) (4554214928000000000000000000000)) else (box (4580422797000000000000000000000) (4580432825000000000000000000000)))))) else (if n < 692 then (if n < 689 then (if n < 687 then (box (4606772783000000000000000000000) (4606782840000000000000000000000)) else (if n < 688 then (box (4633255543000000000000000000000) (4633265629000000000000000000000)) else (box (4659871739000000000000000000000) (4659881854000000000000000000000)))) else (if n < 690 then (box (4686622039000000000000000000000) (4686632183000000000000000000000)) else (if n < 691 then (box (4713507110000000000000000000000) (4713517283000000000000000000000)) else (box (4740527623000000000000000000000) (4740537826000000000000000000000))))) else (if n < 695 then (if n < 693 then (box (4767684254000000000000000000000) (4767694487000000000000000000000)) else (if n < 694 then (box (4794977684000000000000000000000) (4794987946000000000000000000000)) else (box (4822408592000000000000000000000) (4822418884000000000000000000000)))) else (if n < 696 then (box (4849977665000000000000000000000) (4849987987000000000000000000000)) else (if n < 697 then (box (4877685592000000000000000000000) (4877695944000000000000000000000)) else (box (4905533067000000000000000000000) (4905543449000000000000000000000)))))))
def cQ698_721 (n:Nat):IV:=(if n < 709 then (if n < 703 then (if n < 700 then (if n < 699 then (box (4933520786000000000000000000000) (4933531198000000000000000000000)) else (box (4961649448000000000000000000000) (4961659890000000000000000000000))) else (if n < 701 then (box (4989919759000000000000000000000) (4989930231000000000000000000000)) else (if n < 702 then (box (5018332422000000000000000000000) (5018342925000000000000000000000)) else (box (5046888148000000000000000000000) (5046898682000000000000000000000))))) else (if n < 706 then (if n < 704 then (box (5075587653000000000000000000000) (5075598217000000000000000000000)) else (if n < 705 then (box (5104431653000000000000000000000) (5104442247000000000000000000000)) else (box (5133420867000000000000000000000) (5133431492000000000000000000000)))) else (if n < 707 then (box (5162556022000000000000000000000) (5162566678000000000000000000000)) else (if n < 708 then (box (5191837847000000000000000000000) (5191848534000000000000000000000)) else (box (5221267074000000000000000000000) (5221277792000000000000000000000)))))) else (if n < 715 then (if n < 712 then (if n < 710 then (box (5250844438000000000000000000000) (5250855187000000000000000000000)) else (if n < 711 then (box (5280570678000000000000000000000) (5280581459000000000000000000000)) else (box (5310446538000000000000000000000) (5310457351000000000000000000000)))) else (if n < 713 then (box (5340472765000000000000000000000) (5340483609000000000000000000000)) else (if n < 714 then (box (5370650109000000000000000000000) (5370660985000000000000000000000)) else (box (5400979325000000000000000000000) (5400990233000000000000000000000))))) else (if n < 718 then (if n < 716 then (box (5431461171000000000000000000000) (5431472111000000000000000000000)) else (if n < 717 then (box (5462096408000000000000000000000) (5462107380000000000000000000000)) else (box (5492885804000000000000000000000) (5492896808000000000000000000000)))) else (if n < 719 then (box (5523830128000000000000000000000) (5523841164000000000000000000000)) else (if n < 720 then (box (5554930153000000000000000000000) (5554941221000000000000000000000)) else (box (5586186656000000000000000000000) (5586197756000000000000000000000)))))))
def cQ675_721 (n:Nat):IV:=(if n < 698 then (cQ675_698 n) else (cQ698_721 n))
def cQ630_721 (n:Nat):IV:=(if n < 675 then (cQ630_675 n) else (cQ675_721 n))
def cQ540_721 (n:Nat):IV:=(if n < 630 then (cQ540_630 n) else (cQ630_721 n))
def cQ360_721 (n:Nat):IV:=(if n < 540 then (cQ360_540 n) else (cQ540_721 n))
def cQ0_721 (n:Nat):IV:=(if n < 360 then (cQ0_360 n) else (cQ360_721 n))
def cJ0_22 (n:Nat):IV:=(if n < 11 then (if n < 5 then (if n < 2 then (if n < 1 then (box (0) (0)) else (box (3959480000000000000000000000) (3959508000000000000000000000))) else (if n < 3 then (box (7916964000000000000000000000) (7917021000000000000000000000)) else (if n < 4 then (box (11870456000000000000000000000) (11870541000000000000000000000)) else (box (15817966000000000000000000000) (15818080000000000000000000000))))) else (if n < 8 then (if n < 6 then (box (19757500000000000000000000000) (19757642000000000000000000000)) else (if n < 7 then (box (23687074000000000000000000000) (23687245000000000000000000000)) else (box (27604701000000000000000000000) (27604900000000000000000000000)))) else (if n < 9 then (box (31508406000000000000000000000) (31508633000000000000000000000)) else (if n < 10 then (box (35396213000000000000000000000) (35396468000000000000000000000)) else (box (39266153000000000000000000000) (39266436000000000000000000000)))))) else (if n < 16 then (if n < 13 then (if n < 12 then (box (43116273000000000000000000000) (43116584000000000000000000000)) else (box (46944614000000000000000000000) (46944953000000000000000000000))) else (if n < 14 then (box (50749236000000000000000000000) (50749602000000000000000000000)) else (if n < 15 then (box (54528208000000000000000000000) (54528601000000000000000000000)) else (box (58279601000000000000000000000) (58280021000000000000000000000))))) else (if n < 19 then (if n < 17 then (box (62001506000000000000000000000) (62001953000000000000000000000)) else (if n < 18 then (box (65692023000000000000000000000) (65692497000000000000000000000)) else (box (69349264000000000000000000000) (69349764000000000000000000000)))) else (if n < 20 then (box (72971353000000000000000000000) (72971880000000000000000000000)) else (if n < 21 then (box (76556433000000000000000000000) (76556985000000000000000000000)) else (box (80102653000000000000000000000) (80103231000000000000000000000)))))))
def cJ22_45 (n:Nat):IV:=(if n < 33 then (if n < 27 then (if n < 24 then (if n < 23 then (box (83608189000000000000000000000) (83608792000000000000000000000)) else (box (87071223000000000000000000000) (87071851000000000000000000000))) else (if n < 25 then (box (90489963000000000000000000000) (90490616000000000000000000000)) else (if n < 26 then (box (93862630000000000000000000000) (93863307000000000000000000000)) else (box (97187462000000000000000000000) (97188163000000000000000000000))))) else (if n < 30 then (if n < 28 then (box (100462721000000000000000000000) (100463446000000000000000000000)) else (if n < 29 then (box (103686686000000000000000000000) (103687434000000000000000000000)) else (box (106857658000000000000000000000) (106858429000000000000000000000)))) else (if n < 31 then (box (109973960000000000000000000000) (109974754000000000000000000000)) else (if n < 32 then (box (113033939000000000000000000000) (113034755000000000000000000000)) else (box (116035958000000000000000000000) (116036796000000000000000000000)))))) else (if n < 39 then (if n < 36 then (if n < 34 then (box (118978412000000000000000000000) (118979272000000000000000000000)) else (if n < 35 then (box (121859717000000000000000000000) (121860598000000000000000000000)) else (box (124678313000000000000000000000) (124679214000000000000000000000)))) else (if n < 37 then (box (127432667000000000000000000000) (127433588000000000000000000000)) else (if n < 38 then (box (130121273000000000000000000000) (130122214000000000000000000000)) else (box (132742651000000000000000000000) (132743611000000000000000000000))))) else (if n < 42 then (if n < 40 then (box (135295350000000000000000000000) (135296329000000000000000000000)) else (if n < 41 then (box (137777945000000000000000000000) (137778943000000000000000000000)) else (box (140189045000000000000000000000) (140190061000000000000000000000)))) else (if n < 43 then (box (142527285000000000000000000000) (142528318000000000000000000000)) else (if n < 44 then (box (144791331000000000000000000000) (144792381000000000000000000000)) else (box (146979879000000000000000000000) (146980945000000000000000000000)))))))
def cJ0_45 (n:Nat):IV:=(if n < 22 then (cJ0_22 n) else (cJ22_45 n))
def cJ45_67 (n:Nat):IV:=(if n < 56 then (if n < 50 then (if n < 47 then (if n < 46 then (box (149091660000000000000000000000) (149092742000000000000000000000)) else (box (151125434000000000000000000000) (151126532000000000000000000000))) else (if n < 48 then (box (153079995000000000000000000000) (153081108000000000000000000000)) else (if n < 49 then (box (154954172000000000000000000000) (154955299000000000000000000000)) else (box (156746825000000000000000000000) (156747965000000000000000000000))))) else (if n < 53 then (if n < 51 then (box (158456851000000000000000000000) (158458005000000000000000000000)) else (if n < 52 then (box (160083181000000000000000000000) (160084348000000000000000000000)) else (box (161624783000000000000000000000) (161625962000000000000000000000)))) else (if n < 54 then (box (163080659000000000000000000000) (163081850000000000000000000000)) else (if n < 55 then (box (164449851000000000000000000000) (164451053000000000000000000000)) else (box (165731435000000000000000000000) (165732648000000000000000000000)))))) else (if n < 61 then (if n < 58 then (if n < 57 then (box (166924527000000000000000000000) (166925750000000000000000000000)) else (box (168028282000000000000000000000) (168029514000000000000000000000))) else (if n < 59 then (box (169041891000000000000000000000) (169043131000000000000000000000)) else (if n < 60 then (box (169964586000000000000000000000) (169965834000000000000000000000)) else (box (170795639000000000000000000000) (170796894000000000000000000000))))) else (if n < 64 then (if n < 62 then (box (171534362000000000000000000000) (171535624000000000000000000000)) else (if n < 63 then (box (172180107000000000000000000000) (172181375000000000000000000000)) else (box (172732268000000000000000000000) (172733541000000000000000000000)))) else (if n < 65 then (box (173190279000000000000000000000) (173191557000000000000000000000)) else (if n < 66 then (box (173553618000000000000000000000) (173554901000000000000000000000)) else (box (173821804000000000000000000000) (173823091000000000000000000000)))))))
def cJ67_90 (n:Nat):IV:=(if n < 78 then (if n < 72 then (if n < 69 then (if n < 68 then (box (173994399000000000000000000000) (173995689000000000000000000000)) else (box (174071008000000000000000000000) (174072300000000000000000000000))) else (if n < 70 then (box (174051278000000000000000000000) (174052573000000000000000000000)) else (if n < 71 then (box (173934902000000000000000000000) (173936200000000000000000000000)) else (box (173721615000000000000000000000) (173722916000000000000000000000))))) else (if n < 75 then (if n < 73 then (box (173411197000000000000000000000) (173412502000000000000000000000)) else (if n < 74 then (box (173003473000000000000000000000) (173004783000000000000000000000)) else (box (172498313000000000000000000000) (172499628000000000000000000000)))) else (if n < 76 then (box (171895632000000000000000000000) (171896953000000000000000000000)) else (if n < 77 then (box (171195390000000000000000000000) (171196717000000000000000000000)) else (box (170397592000000000000000000000) (170398926000000000000000000000)))))) else (if n < 84 then (if n < 81 then (if n < 79 then (box (169502290000000000000000000000) (169503632000000000000000000000)) else (if n < 80 then (box (168509582000000000000000000000) (168510932000000000000000000000)) else (box (167419611000000000000000000000) (167420970000000000000000000000)))) else (if n < 82 then (box (166232567000000000000000000000) (166233935000000000000000000000)) else (if n < 83 then (box (164948687000000000000000000000) (164950065000000000000000000000)) else (box (163568254000000000000000000000) (163569642000000000000000000000))))) else (if n < 87 then (if n < 85 then (box (162091597000000000000000000000) (162092996000000000000000000000)) else (if n < 86 then (box (160519093000000000000000000000) (160520504000000000000000000000)) else (box (158851165000000000000000000000) (158852589000000000000000000000)))) else (if n < 88 then (box (157088285000000000000000000000) (157089722000000000000000000000)) else (if n < 89 then (box (155230968000000000000000000000) (155232419000000000000000000000)) else (box (153279780000000000000000000000) (153281245000000000000000000000)))))))
def cJ45_90 (n:Nat):IV:=(if n < 67 then (cJ45_67 n) else (cJ67_90 n))
def cJ0_90 (n:Nat):IV:=(if n < 45 then (cJ0_45 n) else (cJ45_90 n))
def cJ90_112 (n:Nat):IV:=(if n < 101 then (if n < 95 then (if n < 92 then (if n < 91 then (box (151235331000000000000000000000) (151236810000000000000000000000)) else (box (149098281000000000000000000000) (149099775000000000000000000000))) else (if n < 93 then (box (146869333000000000000000000000) (146870842000000000000000000000)) else (if n < 94 then (box (144549240000000000000000000000) (144550765000000000000000000000)) else (box (142138802000000000000000000000) (142140343000000000000000000000))))) else (if n < 98 then (if n < 96 then (box (139638862000000000000000000000) (139640421000000000000000000000)) else (if n < 97 then (box (137050315000000000000000000000) (137051891000000000000000000000)) else (box (134374096000000000000000000000) (134375690000000000000000000000)))) else (if n < 99 then (box (131611194000000000000000000000) (131612806000000000000000000000)) else (if n < 100 then (box (128762637000000000000000000000) (128764268000000000000000000000)) else (box (125829503000000000000000000000) (125831154000000000000000000000)))))) else (if n < 106 then (if n < 103 then (if n < 102 then (box (122812913000000000000000000000) (122814584000000000000000000000)) else (box (119714040000000000000000000000) (119715731000000000000000000000))) else (if n < 104 then (box (116534092000000000000000000000) (116535804000000000000000000000)) else (if n < 105 then (box (113274331000000000000000000000) (113276064000000000000000000000)) else (box (109936058000000000000000000000) (109937813000000000000000000000))))) else (if n < 109 then (if n < 107 then (box (106520621000000000000000000000) (106522399000000000000000000000)) else (if n < 108 then (box (103029413000000000000000000000) (103031214000000000000000000000)) else (box (99463868000000000000000000000) (99465692000000000000000000000)))) else (if n < 110 then (box (95825464000000000000000000000) (95827312000000000000000000000)) else (if n < 111 then (box (92115722000000000000000000000) (92117594000000000000000000000)) else (box (88336208000000000000000000000) (88338104000000000000000000000)))))))
def cJ112_135 (n:Nat):IV:=(if n < 123 then (if n < 117 then (if n < 114 then (if n < 113 then (box (84488528000000000000000000000) (84490448000000000000000000000)) else (box (80574328000000000000000000000) (80576273000000000000000000000))) else (if n < 115 then (box (76595297000000000000000000000) (76597267000000000000000000000)) else (if n < 116 then (box (72553165000000000000000000000) (72555161000000000000000000000)) else (box (68449701000000000000000000000) (68451723000000000000000000000))))) else (if n < 120 then (if n < 118 then (box (64286714000000000000000000000) (64288762000000000000000000000)) else (if n < 119 then (box (60066053000000000000000000000) (60068127000000000000000000000)) else (box (55789602000000000000000000000) (55791703000000000000000000000)))) else (if n < 121 then (box (51459288000000000000000000000) (51461416000000000000000000000)) else (if n < 122 then (box (47077071000000000000000000000) (47079226000000000000000000000)) else (box (42644947000000000000000000000) (42647129000000000000000000000)))))) else (if n < 129 then (if n < 126 then (if n < 124 then (box (38164954000000000000000000000) (38167163000000000000000000000)) else (if n < 125 then (box (33639157000000000000000000000) (33641394000000000000000000000)) else (box (29069660000000000000000000000) (29071925000000000000000000000)))) else (if n < 127 then (box (24458602000000000000000000000) (24460895000000000000000000000)) else (if n < 128 then (box (19808153000000000000000000000) (19810474000000000000000000000)) else (box (15120514000000000000000000000) (15122863000000000000000000000))))) else (if n < 132 then (if n < 130 then (box (10397918000000000000000000000) (10400295000000000000000000000)) else (if n < 131 then (box (5642630000000000000000000000) (5645035000000000000000000000)) else (box (856946000000000000000000000) (859379000000000000000000000)))) else (if n < 133 then (box (-3956814000000000000000000000) (-3954352000000000000000000000)) else (if n < 134 then (box (-8796298000000000000000000000) (-8793808000000000000000000000)) else (box (-13659128000000000000000000000) (-13656610000000000000000000000)))))))
def cJ90_135 (n:Nat):IV:=(if n < 112 then (cJ90_112 n) else (cJ112_135 n))
def cJ135_157 (n:Nat):IV:=(if n < 146 then (if n < 140 then (if n < 137 then (if n < 136 then (box (-18542899000000000000000000000) (-18540352000000000000000000000)) else (box (-23445184000000000000000000000) (-23442608000000000000000000000))) else (if n < 138 then (box (-28363526000000000000000000000) (-28360921000000000000000000000)) else (if n < 139 then (box (-33295447000000000000000000000) (-33292813000000000000000000000)) else (box (-38238449000000000000000000000) (-38235787000000000000000000000))))) else (if n < 143 then (if n < 141 then (box (-43190011000000000000000000000) (-43187321000000000000000000000)) else (if n < 142 then (box (-48147591000000000000000000000) (-48144872000000000000000000000)) else (box (-53108631000000000000000000000) (-53105883000000000000000000000)))) else (if n < 144 then (box (-58070546000000000000000000000) (-58067769000000000000000000000)) else (if n < 145 then (box (-63030744000000000000000000000) (-63027938000000000000000000000)) else (box (-67986613000000000000000000000) (-67983778000000000000000000000)))))) else (if n < 151 then (if n < 148 then (if n < 147 then (box (-72935524000000000000000000000) (-72932661000000000000000000000)) else (box (-77874836000000000000000000000) (-77871945000000000000000000000))) else (if n < 149 then (box (-82801893000000000000000000000) (-82798974000000000000000000000)) else (if n < 150 then (box (-87714035000000000000000000000) (-87711088000000000000000000000)) else (box (-92608581000000000000000000000) (-92605607000000000000000000000))))) else (if n < 154 then (if n < 152 then (box (-97482848000000000000000000000) (-97479847000000000000000000000)) else (if n < 153 then (box (-102334143000000000000000000000) (-102331115000000000000000000000)) else (box (-107159767000000000000000000000) (-107156712000000000000000000000)))) else (if n < 155 then (box (-111957015000000000000000000000) (-111953933000000000000000000000)) else (if n < 156 then (box (-116723176000000000000000000000) (-116720067000000000000000000000)) else (box (-121455536000000000000000000000) (-121452401000000000000000000000)))))))
def cJ157_180 (n:Nat):IV:=(if n < 168 then (if n < 162 then (if n < 159 then (if n < 158 then (box (-126151385000000000000000000000) (-126148224000000000000000000000)) else (box (-130808004000000000000000000000) (-130804817000000000000000000000))) else (if n < 160 then (box (-135422682000000000000000000000) (-135419470000000000000000000000)) else (if n < 161 then (box (-139992705000000000000000000000) (-139989468000000000000000000000)) else (box (-144515367000000000000000000000) (-144512105000000000000000000000))))) else (if n < 165 then (if n < 163 then (box (-148987961000000000000000000000) (-148984674000000000000000000000)) else (if n < 164 then (box (-153407794000000000000000000000) (-153404482000000000000000000000)) else (box (-157772171000000000000000000000) (-157768835000000000000000000000)))) else (if n < 166 then (box (-162078416000000000000000000000) (-162075056000000000000000000000)) else (if n < 167 then (box (-166323853000000000000000000000) (-166320470000000000000000000000)) else (box (-170505827000000000000000000000) (-170502421000000000000000000000)))))) else (if n < 174 then (if n < 171 then (if n < 169 then (box (-174621687000000000000000000000) (-174618258000000000000000000000)) else (if n < 170 then (box (-178668805000000000000000000000) (-178665353000000000000000000000)) else (box (-182644560000000000000000000000) (-182641087000000000000000000000)))) else (if n < 172 then (box (-186546357000000000000000000000) (-186542863000000000000000000000)) else (if n < 173 then (box (-190371612000000000000000000000) (-190368097000000000000000000000)) else (box (-194117765000000000000000000000) (-194114230000000000000000000000))))) else (if n < 177 then (if n < 175 then (box (-197782275000000000000000000000) (-197778720000000000000000000000)) else (if n < 176 then (box (-201362628000000000000000000000) (-201359054000000000000000000000)) else (box (-204856329000000000000000000000) (-204852736000000000000000000000)))) else (if n < 178 then (box (-208260911000000000000000000000) (-208257299000000000000000000000)) else (if n < 179 then (box (-211573933000000000000000000000) (-211570303000000000000000000000)) else (box (-214792985000000000000000000000) (-214789337000000000000000000000)))))))
def cJ135_180 (n:Nat):IV:=(if n < 157 then (cJ135_157 n) else (cJ157_180 n))
def cJ90_180 (n:Nat):IV:=(if n < 135 then (cJ90_135 n) else (cJ135_180 n))
def cJ0_180 (n:Nat):IV:=(if n < 90 then (cJ0_90 n) else (cJ90_180 n))
def cJ180_202 (n:Nat):IV:=(if n < 191 then (if n < 185 then (if n < 182 then (if n < 181 then (box (-217915683000000000000000000000) (-217912018000000000000000000000)) else (box (-220939676000000000000000000000) (-220935994000000000000000000000))) else (if n < 183 then (box (-223862647000000000000000000000) (-223858949000000000000000000000)) else (if n < 184 then (box (-226682310000000000000000000000) (-226678597000000000000000000000)) else (box (-229396417000000000000000000000) (-229392689000000000000000000000))))) else (if n < 188 then (if n < 186 then (box (-232002756000000000000000000000) (-231999013000000000000000000000)) else (if n < 187 then (box (-234499153000000000000000000000) (-234495396000000000000000000000)) else (box (-236883472000000000000000000000) (-236879702000000000000000000000)))) else (if n < 189 then (box (-239153622000000000000000000000) (-239149839000000000000000000000)) else (if n < 190 then (box (-241307552000000000000000000000) (-241303757000000000000000000000)) else (box (-243343254000000000000000000000) (-243339447000000000000000000000)))))) else (if n < 196 then (if n < 193 then (if n < 192 then (box (-245258766000000000000000000000) (-245254948000000000000000000000)) else (box (-247052173000000000000000000000) (-247048344000000000000000000000))) else (if n < 194 then (box (-248721607000000000000000000000) (-248717768000000000000000000000)) else (if n < 195 then (box (-250265249000000000000000000000) (-250261400000000000000000000000)) else (box (-251681332000000000000000000000) (-251677474000000000000000000000))))) else (if n < 199 then (if n < 197 then (box (-252968138000000000000000000000) (-252964272000000000000000000000)) else (if n < 198 then (box (-254124005000000000000000000000) (-254120132000000000000000000000)) else (box (-255147324000000000000000000000) (-255143444000000000000000000000)))) else (if n < 200 then (box (-256036541000000000000000000000) (-256032655000000000000000000000)) else (if n < 201 then (box (-256790160000000000000000000000) (-256786268000000000000000000000)) else (box (-257406743000000000000000000000) (-257402846000000000000000000000)))))))
def cJ202_225 (n:Nat):IV:=(if n < 213 then (if n < 207 then (if n < 204 then (if n < 203 then (box (-257884911000000000000000000000) (-257881009000000000000000000000)) else (box (-258223345000000000000000000000) (-258219439000000000000000000000))) else (if n < 205 then (box (-258420788000000000000000000000) (-258416879000000000000000000000)) else (if n < 206 then (box (-258476047000000000000000000000) (-258472135000000000000000000000)) else (box (-258387992000000000000000000000) (-258384077000000000000000000000))))) else (if n < 210 then (if n < 208 then (box (-258155558000000000000000000000) (-258151639000000000000000000000)) else (if n < 209 then (box (-257777747000000000000000000000) (-257773824000000000000000000000)) else (box (-257253627000000000000000000000) (-257249699000000000000000000000)))) else (if n < 211 then (box (-256582336000000000000000000000) (-256578403000000000000000000000)) else (if n < 212 then (box (-255763081000000000000000000000) (-255759141000000000000000000000)) else (box (-254795137000000000000000000000) (-254791191000000000000000000000)))))) else (if n < 219 then (if n < 216 then (if n < 214 then (box (-253677854000000000000000000000) (-253673901000000000000000000000)) else (if n < 215 then (box (-252410652000000000000000000000) (-252406692000000000000000000000)) else (box (-250993025000000000000000000000) (-250989056000000000000000000000)))) else (if n < 217 then (box (-249424542000000000000000000000) (-249420563000000000000000000000)) else (if n < 218 then (box (-247704845000000000000000000000) (-247700856000000000000000000000)) else (box (-245833652000000000000000000000) (-245829653000000000000000000000))))) else (if n < 222 then (if n < 220 then (box (-243810761000000000000000000000) (-243806751000000000000000000000)) else (if n < 221 then (box (-241636043000000000000000000000) (-241632022000000000000000000000)) else (box (-239309451000000000000000000000) (-239305418000000000000000000000)))) else (if n < 223 then (box (-236831014000000000000000000000) (-236826968000000000000000000000)) else (if n < 224 then (box (-234200843000000000000000000000) (-234196784000000000000000000000)) else (box (-231419128000000000000000000000) (-231415055000000000000000000000)))))))
def cJ180_225 (n:Nat):IV:=(if n < 202 then (cJ180_202 n) else (cJ202_225 n))
def cJ225_247 (n:Nat):IV:=(if n < 236 then (if n < 230 then (if n < 227 then (if n < 226 then (box (-228486139000000000000000000000) (-228482052000000000000000000000)) else (box (-225402230000000000000000000000) (-225398128000000000000000000000))) else (if n < 228 then (box (-222167834000000000000000000000) (-222163717000000000000000000000)) else (if n < 229 then (box (-218783469000000000000000000000) (-218779336000000000000000000000)) else (box (-215249733000000000000000000000) (-215245584000000000000000000000))))) else (if n < 233 then (if n < 231 then (box (-211567312000000000000000000000) (-211563146000000000000000000000)) else (if n < 232 then (box (-207736973000000000000000000000) (-207732789000000000000000000000)) else (box (-203759565000000000000000000000) (-203755363000000000000000000000)))) else (if n < 234 then (box (-199636027000000000000000000000) (-199631807000000000000000000000)) else (if n < 235 then (box (-195367377000000000000000000000) (-195363138000000000000000000000)) else (box (-190954722000000000000000000000) (-190950464000000000000000000000)))))) else (if n < 241 then (if n < 238 then (if n < 237 then (box (-186399253000000000000000000000) (-186394975000000000000000000000)) else (box (-181702245000000000000000000000) (-181697947000000000000000000000))) else (if n < 239 then (box (-176865061000000000000000000000) (-176860742000000000000000000000)) else (if n < 240 then (box (-171889148000000000000000000000) (-171884807000000000000000000000)) else (box (-166776038000000000000000000000) (-166771675000000000000000000000))))) else (if n < 244 then (if n < 242 then (box (-161527348000000000000000000000) (-161522963000000000000000000000)) else (if n < 243 then (box (-156144784000000000000000000000) (-156140377000000000000000000000)) else (box (-150630135000000000000000000000) (-150625704000000000000000000000)))) else (if n < 245 then (box (-144985275000000000000000000000) (-144980820000000000000000000000)) else (if n < 246 then (box (-139212164000000000000000000000) (-139207685000000000000000000000)) else (box (-133312844000000000000000000000) (-133308340000000000000000000000)))))))
def cJ247_270 (n:Nat):IV:=(if n < 258 then (if n < 252 then (if n < 249 then (if n < 248 then (box (-127289445000000000000000000000) (-127284916000000000000000000000)) else (box (-121144179000000000000000000000) (-121139626000000000000000000000))) else (if n < 250 then (box (-114879344000000000000000000000) (-114874765000000000000000000000)) else (if n < 251 then (box (-108497320000000000000000000000) (-108492715000000000000000000000)) else (box (-102000568000000000000000000000) (-101995937000000000000000000000))))) else (if n < 255 then (if n < 253 then (box (-95391635000000000000000000000) (-95386977000000000000000000000)) else (if n < 254 then (box (-88673145000000000000000000000) (-88668460000000000000000000000)) else (box (-81847809000000000000000000000) (-81843098000000000000000000000)))) else (if n < 256 then (box (-74918415000000000000000000000) (-74913677000000000000000000000)) else (if n < 257 then (box (-67887831000000000000000000000) (-67883065000000000000000000000)) else (box (-60759003000000000000000000000) (-60754210000000000000000000000)))))) else (if n < 264 then (if n < 261 then (if n < 259 then (box (-53534958000000000000000000000) (-53530137000000000000000000000)) else (if n < 260 then (box (-46218800000000000000000000000) (-46213951000000000000000000000)) else (box (-38813705000000000000000000000) (-38808828000000000000000000000)))) else (if n < 262 then (box (-31322930000000000000000000000) (-31318025000000000000000000000)) else (if n < 263 then (box (-23749803000000000000000000000) (-23744869000000000000000000000)) else (box (-16097728000000000000000000000) (-16092765000000000000000000000))))) else (if n < 267 then (if n < 265 then (box (-8370180000000000000000000000) (-8365188000000000000000000000)) else (if n < 266 then (box (-570703000000000000000000000) (-565682000000000000000000000)) else (box (7297085000000000000000000000) (7302135000000000000000000000)))) else (if n < 268 then (box (15229501000000000000000000000) (15234580000000000000000000000)) else (if n < 269 then (box (23222793000000000000000000000) (23227901000000000000000000000)) else (box (31273141000000000000000000000) (31278279000000000000000000000)))))))
def cJ225_270 (n:Nat):IV:=(if n < 247 then (cJ225_247 n) else (cJ247_270 n))
def cJ180_270 (n:Nat):IV:=(if n < 225 then (cJ180_225 n) else (cJ225_270 n))
def cJ270_292 (n:Nat):IV:=(if n < 281 then (if n < 275 then (if n < 272 then (if n < 271 then (box (39376665000000000000000000000) (39381833000000000000000000000)) else (box (47529419000000000000000000000) (47534616000000000000000000000))) else (if n < 273 then (box (55727393000000000000000000000) (55732619000000000000000000000)) else (if n < 274 then (box (63966520000000000000000000000) (63971776000000000000000000000)) else (box (72242675000000000000000000000) (72247961000000000000000000000))))) else (if n < 278 then (if n < 276 then (box (80551673000000000000000000000) (80556989000000000000000000000)) else (if n < 277 then (box (88889279000000000000000000000) (88894624000000000000000000000)) else (box (97251196000000000000000000000) (97256570000000000000000000000)))) else (if n < 279 then (box (105633084000000000000000000000) (105638487000000000000000000000)) else (if n < 280 then (box (114030547000000000000000000000) (114035980000000000000000000000)) else (box (122439144000000000000000000000) (122444606000000000000000000000)))))) else (if n < 286 then (if n < 283 then (if n < 282 then (box (130854387000000000000000000000) (130859878000000000000000000000)) else (box (139271741000000000000000000000) (139277261000000000000000000000))) else (if n < 284 then (box (147686635000000000000000000000) (147692184000000000000000000000)) else (if n < 285 then (box (156094452000000000000000000000) (156100030000000000000000000000)) else (box (164490538000000000000000000000) (164496145000000000000000000000))))) else (if n < 289 then (if n < 287 then (box (172870204000000000000000000000) (172875840000000000000000000000)) else (if n < 288 then (box (181228729000000000000000000000) (181234394000000000000000000000)) else (box (189561355000000000000000000000) (189567049000000000000000000000)))) else (if n < 290 then (box (197863299000000000000000000000) (197869021000000000000000000000)) else (if n < 291 then (box (206129750000000000000000000000) (206135500000000000000000000000)) else (box (214355872000000000000000000000) (214361650000000000000000000000)))))))
def cJ292_315 (n:Nat):IV:=(if n < 303 then (if n < 297 then (if n < 294 then (if n < 293 then (box (222536802000000000000000000000) (222542608000000000000000000000)) else (box (230667663000000000000000000000) (230673497000000000000000000000))) else (if n < 295 then (box (238743559000000000000000000000) (238749420000000000000000000000)) else (if n < 296 then (box (246759574000000000000000000000) (246765462000000000000000000000)) else (box (254710784000000000000000000000) (254716699000000000000000000000))))) else (if n < 300 then (if n < 298 then (box (262592253000000000000000000000) (262598195000000000000000000000)) else (if n < 299 then (box (270399039000000000000000000000) (270405007000000000000000000000)) else (box (278126189000000000000000000000) (278132183000000000000000000000)))) else (if n < 301 then (box (285768753000000000000000000000) (285774772000000000000000000000)) else (if n < 302 then (box (293321780000000000000000000000) (293327824000000000000000000000)) else (box (300780318000000000000000000000) (300786387000000000000000000000)))))) else (if n < 309 then (if n < 306 then (if n < 304 then (box (308139425000000000000000000000) (308145519000000000000000000000)) else (if n < 305 then (box (315394164000000000000000000000) (315400281000000000000000000000)) else (box (322539609000000000000000000000) (322545749000000000000000000000)))) else (if n < 307 then (box (329570846000000000000000000000) (329577009000000000000000000000)) else (if n < 308 then (box (336482981000000000000000000000) (336489167000000000000000000000)) else (box (343271137000000000000000000000) (343277345000000000000000000000))))) else (if n < 312 then (if n < 310 then (box (349930458000000000000000000000) (349936687000000000000000000000)) else (if n < 311 then (box (356456111000000000000000000000) (356462361000000000000000000000)) else (box (362843294000000000000000000000) (362849565000000000000000000000)))) else (if n < 313 then (box (369087234000000000000000000000) (369093525000000000000000000000)) else (if n < 314 then (box (375183189000000000000000000000) (375189500000000000000000000000)) else (box (381126455000000000000000000000) (381132785000000000000000000000)))))))
def cJ270_315 (n:Nat):IV:=(if n < 292 then (cJ270_292 n) else (cJ292_315 n))
def cJ315_337 (n:Nat):IV:=(if n < 326 then (if n < 320 then (if n < 317 then (if n < 316 then (box (386912365000000000000000000000) (386918714000000000000000000000)) else (box (392536297000000000000000000000) (392542664000000000000000000000))) else (if n < 318 then (box (397993669000000000000000000000) (398000054000000000000000000000)) else (if n < 319 then (box (403279949000000000000000000000) (403286352000000000000000000000)) else (box (408390657000000000000000000000) (408397077000000000000000000000))))) else (if n < 323 then (if n < 321 then (box (413321364000000000000000000000) (413327800000000000000000000000)) else (if n < 322 then (box (418067695000000000000000000000) (418074147000000000000000000000)) else (box (422625338000000000000000000000) (422631806000000000000000000000)))) else (if n < 324 then (box (426990041000000000000000000000) (426996524000000000000000000000)) else (if n < 325 then (box (431157617000000000000000000000) (431164114000000000000000000000)) else (box (435123946000000000000000000000) (435130457000000000000000000000)))))) else (if n < 331 then (if n < 328 then (if n < 327 then (box (438884979000000000000000000000) (438891504000000000000000000000)) else (box (442436743000000000000000000000) (442443280000000000000000000000))) else (if n < 329 then (box (445775336000000000000000000000) (445781886000000000000000000000)) else (if n < 330 then (box (448896939000000000000000000000) (448903501000000000000000000000)) else (box (451797815000000000000000000000) (451804388000000000000000000000))))) else (if n < 334 then (if n < 332 then (box (454474309000000000000000000000) (454480892000000000000000000000)) else (if n < 333 then (box (456922856000000000000000000000) (456929448000000000000000000000)) else (box (459139979000000000000000000000) (459146581000000000000000000000)))) else (if n < 335 then (box (461122296000000000000000000000) (461128907000000000000000000000)) else (if n < 336 then (box (462866521000000000000000000000) (462873140000000000000000000000)) else (box (464369465000000000000000000000) (464376092000000000000000000000)))))))
def cJ337_360 (n:Nat):IV:=(if n < 348 then (if n < 342 then (if n < 339 then (if n < 338 then (box (465628041000000000000000000000) (465634675000000000000000000000)) else (box (466639266000000000000000000000) (466645906000000000000000000000))) else (if n < 340 then (box (467400262000000000000000000000) (467406908000000000000000000000)) else (if n < 341 then (box (467908262000000000000000000000) (467914913000000000000000000000)) else (box (468160609000000000000000000000) (468167264000000000000000000000))))) else (if n < 345 then (if n < 343 then (box (468154761000000000000000000000) (468161420000000000000000000000)) else (if n < 344 then (box (467888291000000000000000000000) (467894955000000000000000000000)) else (box (467358893000000000000000000000) (467365562000000000000000000000)))) else (if n < 346 then (box (466564381000000000000000000000) (466571056000000000000000000000)) else (if n < 347 then (box (465502695000000000000000000000) (465509376000000000000000000000)) else (box (464171898000000000000000000000) (464178587000000000000000000000)))))) else (if n < 354 then (if n < 351 then (if n < 349 then (box (462570185000000000000000000000) (462576881000000000000000000000)) else (if n < 350 then (box (460695878000000000000000000000) (460702582000000000000000000000)) else (box (458547434000000000000000000000) (458554147000000000000000000000)))) else (if n < 352 then (box (456123444000000000000000000000) (456130167000000000000000000000)) else (if n < 353 then (box (453422637000000000000000000000) (453429370000000000000000000000)) else (box (450443880000000000000000000000) (450450624000000000000000000000))))) else (if n < 357 then (if n < 355 then (box (447186181000000000000000000000) (447192937000000000000000000000)) else (if n < 356 then (box (443648693000000000000000000000) (443655461000000000000000000000)) else (box (439830711000000000000000000000) (439837492000000000000000000000)))) else (if n < 358 then (box (435731678000000000000000000000) (435738472000000000000000000000)) else (if n < 359 then (box (431351185000000000000000000000) (431357993000000000000000000000)) else (box (426688974000000000000000000000) (426695796000000000000000000000)))))))
def cJ315_360 (n:Nat):IV:=(if n < 337 then (cJ315_337 n) else (cJ337_360 n))
def cJ270_360 (n:Nat):IV:=(if n < 315 then (cJ270_315 n) else (cJ315_360 n))
def cJ180_360 (n:Nat):IV:=(if n < 270 then (cJ180_270 n) else (cJ270_360 n))
def cJ0_360 (n:Nat):IV:=(if n < 180 then (cJ0_180 n) else (cJ180_360 n))
def cJ360_382 (n:Nat):IV:=(if n < 371 then (if n < 365 then (if n < 362 then (if n < 361 then (box (421744937000000000000000000000) (421751774000000000000000000000)) else (box (416519119000000000000000000000) (416525972000000000000000000000))) else (if n < 363 then (box (411011721000000000000000000000) (411018590000000000000000000000)) else (if n < 364 then (box (405223100000000000000000000000) (405229986000000000000000000000)) else (box (399153769000000000000000000000) (399160672000000000000000000000))))) else (if n < 368 then (if n < 366 then (box (392804400000000000000000000000) (392811320000000000000000000000)) else (if n < 367 then (box (386175825000000000000000000000) (386182763000000000000000000000)) else (box (379269038000000000000000000000) (379275995000000000000000000000)))) else (if n < 369 then (box (372085192000000000000000000000) (372092168000000000000000000000)) else (if n < 370 then (box (364625606000000000000000000000) (364632602000000000000000000000)) else (box (356891761000000000000000000000) (356898777000000000000000000000)))))) else (if n < 376 then (if n < 373 then (if n < 372 then (box (348885304000000000000000000000) (348892341000000000000000000000)) else (box (340608045000000000000000000000) (340615103000000000000000000000))) else (if n < 374 then (box (332061962000000000000000000000) (332069042000000000000000000000)) else (if n < 375 then (box (323249197000000000000000000000) (323256300000000000000000000000)) else (box (314172062000000000000000000000) (314179187000000000000000000000))))) else (if n < 379 then (if n < 377 then (box (304833034000000000000000000000) (304840182000000000000000000000)) else (if n < 378 then (box (295234760000000000000000000000) (295241932000000000000000000000)) else (box (285380051000000000000000000000) (285387247000000000000000000000)))) else (if n < 380 then (box (275271887000000000000000000000) (275279108000000000000000000000)) else (if n < 381 then (box (264913419000000000000000000000) (264920665000000000000000000000)) else (box (254307964000000000000000000000) (254315235000000000000000000000)))))))
def cJ382_405 (n:Nat):IV:=(if n < 393 then (if n < 387 then (if n < 384 then (if n < 383 then (box (243459005000000000000000000000) (243466301000000000000000000000)) else (box (232370195000000000000000000000) (232377517000000000000000000000))) else (if n < 385 then (box (221045350000000000000000000000) (221052699000000000000000000000)) else (if n < 386 then (box (209488459000000000000000000000) (209495834000000000000000000000)) else (box (197703671000000000000000000000) (197711073000000000000000000000))))) else (if n < 390 then (if n < 388 then (box (185695302000000000000000000000) (185702732000000000000000000000)) else (if n < 389 then (box (173467836000000000000000000000) (173475294000000000000000000000)) else (box (161025917000000000000000000000) (161033403000000000000000000000)))) else (if n < 391 then (box (148374353000000000000000000000) (148381868000000000000000000000)) else (if n < 392 then (box (135518115000000000000000000000) (135525658000000000000000000000)) else (box (122462335000000000000000000000) (122469907000000000000000000000)))))) else (if n < 399 then (if n < 396 then (if n < 394 then (box (109212300000000000000000000000) (109219901000000000000000000000)) else (if n < 395 then (box (95773462000000000000000000000) (95781093000000000000000000000)) else (box (82151425000000000000000000000) (82159085000000000000000000000)))) else (if n < 397 then (box (68351950000000000000000000000) (68359640000000000000000000000)) else (if n < 398 then (box (54380952000000000000000000000) (54388672000000000000000000000)) else (box (40244496000000000000000000000) (40252247000000000000000000000))))) else (if n < 402 then (if n < 400 then (box (25948799000000000000000000000) (25956581000000000000000000000)) else (if n < 401 then (box (11500228000000000000000000000) (11508040000000000000000000000)) else (box (-3094711000000000000000000000) (-3086869000000000000000000000)))) else (if n < 403 then (box (-17829360000000000000000000000) (-17821487000000000000000000000)) else (if n < 404 then (box (-32696923000000000000000000000) (-32689019000000000000000000000)) else (box (-47690464000000000000000000000) (-47682528000000000000000000000)))))))
def cJ360_405 (n:Nat):IV:=(if n < 382 then (cJ360_382 n) else (cJ382_405 n))
def cJ405_427 (n:Nat):IV:=(if n < 416 then (if n < 410 then (if n < 407 then (if n < 406 then (box (-62802911000000000000000000000) (-62794944000000000000000000000)) else (box (-78027055000000000000000000000) (-78019056000000000000000000000))) else (if n < 408 then (box (-93355559000000000000000000000) (-93347528000000000000000000000)) else (if n < 409 then (box (-108780953000000000000000000000) (-108772890000000000000000000000)) else (box (-124295643000000000000000000000) (-124287549000000000000000000000))))) else (if n < 413 then (if n < 411 then (box (-139891911000000000000000000000) (-139883785000000000000000000000)) else (if n < 412 then (box (-155561917000000000000000000000) (-155553760000000000000000000000)) else (box (-171297708000000000000000000000) (-171289519000000000000000000000)))) else (if n < 414 then (box (-187091212000000000000000000000) (-187082991000000000000000000000)) else (if n < 415 then (box (-202934248000000000000000000000) (-202925996000000000000000000000)) else (box (-218818530000000000000000000000) (-218810246000000000000000000000)))))) else (if n < 421 then (if n < 418 then (if n < 417 then (box (-234735666000000000000000000000) (-234727351000000000000000000000)) else (box (-250677164000000000000000000000) (-250668817000000000000000000000))) else (if n < 419 then (box (-266634434000000000000000000000) (-266626056000000000000000000000)) else (if n < 420 then (box (-282598794000000000000000000000) (-282590385000000000000000000000)) else (box (-298561478000000000000000000000) (-298553038000000000000000000000))))) else (if n < 424 then (if n < 422 then (box (-314513627000000000000000000000) (-314505155000000000000000000000)) else (if n < 423 then (box (-330446305000000000000000000000) (-330437802000000000000000000000)) else (box (-346350498000000000000000000000) (-346341964000000000000000000000)))) else (if n < 425 then (box (-362217122000000000000000000000) (-362208558000000000000000000000)) else (if n < 426 then (box (-378037022000000000000000000000) (-378028427000000000000000000000)) else (box (-393800980000000000000000000000) (-393792354000000000000000000000)))))))
def cJ427_450 (n:Nat):IV:=(if n < 438 then (if n < 432 then (if n < 429 then (if n < 428 then (box (-409499714000000000000000000000) (-409491058000000000000000000000)) else (box (-425123897000000000000000000000) (-425115211000000000000000000000))) else (if n < 430 then (box (-440664141000000000000000000000) (-440655425000000000000000000000)) else (if n < 431 then (box (-456111017000000000000000000000) (-456102271000000000000000000000)) else (box (-471455053000000000000000000000) (-471446278000000000000000000000))))) else (if n < 435 then (if n < 433 then (box (-486686746000000000000000000000) (-486677942000000000000000000000)) else (if n < 434 then (box (-501796554000000000000000000000) (-501787721000000000000000000000)) else (box (-516774914000000000000000000000) (-516766053000000000000000000000)))) else (if n < 436 then (box (-531612238000000000000000000000) (-531603349000000000000000000000)) else (if n < 437 then (box (-546298925000000000000000000000) (-546290008000000000000000000000)) else (box (-560825357000000000000000000000) (-560816413000000000000000000000)))))) else (if n < 444 then (if n < 441 then (if n < 439 then (box (-575181917000000000000000000000) (-575172946000000000000000000000)) else (if n < 440 then (box (-589358984000000000000000000000) (-589349987000000000000000000000)) else (box (-603346939000000000000000000000) (-603337915000000000000000000000)))) else (if n < 442 then (box (-617136176000000000000000000000) (-617127126000000000000000000000)) else (if n < 443 then (box (-630717104000000000000000000000) (-630708029000000000000000000000)) else (box (-644080149000000000000000000000) (-644071049000000000000000000000))))) else (if n < 447 then (if n < 445 then (box (-657215768000000000000000000000) (-657206643000000000000000000000)) else (if n < 446 then (box (-670114446000000000000000000000) (-670105297000000000000000000000)) else (box (-682766707000000000000000000000) (-682757534000000000000000000000)))) else (if n < 448 then (box (-695163119000000000000000000000) (-695153923000000000000000000000)) else (if n < 449 then (box (-707294292000000000000000000000) (-707285073000000000000000000000)) else (box (-719150899000000000000000000000) (-719141657000000000000000000000)))))))
def cJ405_450 (n:Nat):IV:=(if n < 427 then (cJ405_427 n) else (cJ427_450 n))
def cJ360_450 (n:Nat):IV:=(if n < 405 then (cJ360_405 n) else (cJ405_450 n))
def cJ450_472 (n:Nat):IV:=(if n < 461 then (if n < 455 then (if n < 452 then (if n < 451 then (box (-730723667000000000000000000000) (-730714403000000000000000000000)) else (box (-742003387000000000000000000000) (-741994101000000000000000000000))) else (if n < 453 then (box (-752980927000000000000000000000) (-752971619000000000000000000000)) else (if n < 454 then (box (-763647226000000000000000000000) (-763637897000000000000000000000)) else (box (-773993311000000000000000000000) (-773983961000000000000000000000))))) else (if n < 458 then (if n < 456 then (box (-784010292000000000000000000000) (-784000922000000000000000000000)) else (if n < 457 then (box (-793689377000000000000000000000) (-793679988000000000000000000000)) else (box (-803021873000000000000000000000) (-803012465000000000000000000000)))) else (if n < 459 then (box (-811999192000000000000000000000) (-811989765000000000000000000000)) else (if n < 460 then (box (-820612859000000000000000000000) (-820603414000000000000000000000)) else (box (-828854515000000000000000000000) (-828845053000000000000000000000)))))) else (if n < 466 then (if n < 463 then (if n < 462 then (box (-836715926000000000000000000000) (-836706447000000000000000000000)) else (box (-844188983000000000000000000000) (-844179488000000000000000000000))) else (if n < 464 then (box (-851265716000000000000000000000) (-851256205000000000000000000000)) else (if n < 465 then (box (-857938293000000000000000000000) (-857928766000000000000000000000)) else (box (-864199030000000000000000000000) (-864189488000000000000000000000))))) else (if n < 469 then (if n < 467 then (box (-870040392000000000000000000000) (-870030836000000000000000000000)) else (if n < 468 then (box (-875455004000000000000000000000) (-875445435000000000000000000000)) else (box (-880435653000000000000000000000) (-880426071000000000000000000000)))) else (if n < 470 then (box (-884975296000000000000000000000) (-884965701000000000000000000000)) else (if n < 471 then (box (-889067062000000000000000000000) (-889057455000000000000000000000)) else (box (-892704261000000000000000000000) (-892694643000000000000000000000)))))))
def cJ472_495 (n:Nat):IV:=(if n < 483 then (if n < 477 then (if n < 474 then (if n < 473 then (box (-895880390000000000000000000000) (-895870761000000000000000000000)) else (box (-898589134000000000000000000000) (-898579495000000000000000000000))) else (if n < 475 then (box (-900824376000000000000000000000) (-900814728000000000000000000000)) else (if n < 476 then (box (-902580200000000000000000000000) (-902570543000000000000000000000)) else (box (-903850897000000000000000000000) (-903841232000000000000000000000))))) else (if n < 480 then (if n < 478 then (box (-904630970000000000000000000000) (-904621297000000000000000000000)) else (if n < 479 then (box (-904915138000000000000000000000) (-904905458000000000000000000000)) else (box (-904698344000000000000000000000) (-904688657000000000000000000000)))) else (if n < 481 then (box (-903975758000000000000000000000) (-903966063000000000000000000000)) else (if n < 482 then (box (-902742781000000000000000000000) (-902733078000000000000000000000)) else (box (-900995052000000000000000000000) (-900985340000000000000000000000)))))) else (if n < 489 then (if n < 486 then (if n < 484 then (box (-898728452000000000000000000000) (-898718730000000000000000000000)) else (if n < 485 then (box (-895939108000000000000000000000) (-895929375000000000000000000000)) else (box (-892623397000000000000000000000) (-892613653000000000000000000000)))) else (if n < 487 then (box (-888777953000000000000000000000) (-888768198000000000000000000000)) else (if n < 488 then (box (-884399670000000000000000000000) (-884389903000000000000000000000)) else (box (-879485705000000000000000000000) (-879475925000000000000000000000))))) else (if n < 492 then (if n < 490 then (box (-874033486000000000000000000000) (-874023692000000000000000000000)) else (if n < 491 then (box (-868040711000000000000000000000) (-868030903000000000000000000000)) else (box (-861505356000000000000000000000) (-861495534000000000000000000000)))) else (if n < 493 then (box (-854425678000000000000000000000) (-854415840000000000000000000000)) else (if n < 494 then (box (-846800218000000000000000000000) (-846790364000000000000000000000)) else (box (-838627803000000000000000000000) (-838617932000000000000000000000)))))))
def cJ450_495 (n:Nat):IV:=(if n < 472 then (cJ450_472 n) else (cJ472_495 n))
def cJ495_517 (n:Nat):IV:=(if n < 506 then (if n < 500 then (if n < 497 then (if n < 496 then (box (-829907553000000000000000000000) (-829897665000000000000000000000)) else (box (-820638885000000000000000000000) (-820628979000000000000000000000))) else (if n < 498 then (box (-810821509000000000000000000000) (-810811585000000000000000000000)) else (if n < 499 then (box (-800455442000000000000000000000) (-800445499000000000000000000000)) else (box (-789540999000000000000000000000) (-789531037000000000000000000000))))) else (if n < 503 then (if n < 501 then (box (-778078808000000000000000000000) (-778068826000000000000000000000)) else (if n < 502 then (box (-766069803000000000000000000000) (-766059801000000000000000000000)) else (box (-753515234000000000000000000000) (-753505210000000000000000000000)))) else (if n < 504 then (box (-740416659000000000000000000000) (-740406614000000000000000000000)) else (if n < 505 then (box (-726775962000000000000000000000) (-726765894000000000000000000000)) else (box (-712595339000000000000000000000) (-712585248000000000000000000000)))))) else (if n < 511 then (if n < 508 then (if n < 507 then (box (-697877312000000000000000000000) (-697867198000000000000000000000)) else (box (-682624721000000000000000000000) (-682614583000000000000000000000))) else (if n < 509 then (box (-666840737000000000000000000000) (-666830575000000000000000000000)) else (if n < 510 then (box (-650528850000000000000000000000) (-650518664000000000000000000000)) else (box (-633692886000000000000000000000) (-633682675000000000000000000000))))) else (if n < 514 then (if n < 512 then (box (-616336991000000000000000000000) (-616326754000000000000000000000)) else (if n < 513 then (box (-598465645000000000000000000000) (-598455382000000000000000000000)) else (box (-580083659000000000000000000000) (-580073370000000000000000000000)))) else (if n < 515 then (box (-561196172000000000000000000000) (-561185856000000000000000000000)) else (if n < 516 then (box (-541808659000000000000000000000) (-541798315000000000000000000000)) else (box (-521926922000000000000000000000) (-521916549000000000000000000000)))))))
def cJ517_540 (n:Nat):IV:=(if n < 528 then (if n < 522 then (if n < 519 then (if n < 518 then (box (-501557099000000000000000000000) (-501546698000000000000000000000)) else (box (-480705655000000000000000000000) (-480695225000000000000000000000))) else (if n < 520 then (box (-459379392000000000000000000000) (-459368933000000000000000000000)) else (if n < 521 then (box (-437585440000000000000000000000) (-437574951000000000000000000000)) else (box (-415331260000000000000000000000) (-415320741000000000000000000000))))) else (if n < 525 then (if n < 523 then (box (-392624641000000000000000000000) (-392614091000000000000000000000)) else (if n < 524 then (box (-369473703000000000000000000000) (-369463122000000000000000000000)) else (box (-345886893000000000000000000000) (-345876280000000000000000000000)))) else (if n < 526 then (box (-321872983000000000000000000000) (-321862339000000000000000000000)) else (if n < 527 then (box (-297441069000000000000000000000) (-297430393000000000000000000000)) else (box (-272600573000000000000000000000) (-272589865000000000000000000000)))))) else (if n < 534 then (if n < 531 then (if n < 529 then (box (-247361232000000000000000000000) (-247350491000000000000000000000)) else (if n < 530 then (box (-221733104000000000000000000000) (-221722330000000000000000000000)) else (box (-195726567000000000000000000000) (-195715760000000000000000000000)))) else (if n < 532 then (box (-169352305000000000000000000000) (-169341464000000000000000000000)) else (if n < 533 then (box (-142621317000000000000000000000) (-142610443000000000000000000000)) else (box (-115544908000000000000000000000) (-115534001000000000000000000000))))) else (if n < 537 then (if n < 535 then (box (-88134689000000000000000000000) (-88123748000000000000000000000)) else (if n < 536 then (box (-60402573000000000000000000000) (-60391597000000000000000000000)) else (box (-32360768000000000000000000000) (-32349757000000000000000000000)))) else (if n < 538 then (box (-4021774000000000000000000000) (-4010728000000000000000000000)) else (if n < 539 then (box (24601616000000000000000000000) (24612696000000000000000000000)) else (box (53496323000000000000000000000) (53507438000000000000000000000)))))))
def cJ495_540 (n:Nat):IV:=(if n < 517 then (cJ495_517 n) else (cJ517_540 n))
def cJ450_540 (n:Nat):IV:=(if n < 495 then (cJ450_495 n) else (cJ495_540 n))
def cJ360_540 (n:Nat):IV:=(if n < 450 then (cJ360_450 n) else (cJ450_540 n))
def cJ540_562 (n:Nat):IV:=(if n < 551 then (if n < 545 then (if n < 542 then (if n < 541 then (box (82648993000000000000000000000) (82660143000000000000000000000)) else (box (112045987000000000000000000000) (112057172000000000000000000000))) else (if n < 543 then (box (141673398000000000000000000000) (141684618000000000000000000000)) else (if n < 544 then (box (171517056000000000000000000000) (171528312000000000000000000000)) else (box (201562526000000000000000000000) (201573817000000000000000000000))))) else (if n < 548 then (if n < 546 then (box (231795116000000000000000000000) (231806443000000000000000000000)) else (if n < 547 then (box (262199886000000000000000000000) (262211249000000000000000000000)) else (box (292761651000000000000000000000) (292773049000000000000000000000)))) else (if n < 549 then (box (323464983000000000000000000000) (323476417000000000000000000000)) else (if n < 550 then (box (354294230000000000000000000000) (354305700000000000000000000000)) else (box (385233507000000000000000000000) (385245012000000000000000000000)))))) else (if n < 556 then (if n < 553 then (if n < 552 then (box (416266707000000000000000000000) (416278248000000000000000000000)) else (box (447377522000000000000000000000) (447389098000000000000000000000))) else (if n < 554 then (box (478549425000000000000000000000) (478561037000000000000000000000)) else (if n < 555 then (box (509765696000000000000000000000) (509777344000000000000000000000)) else (box (541009426000000000000000000000) (541021109000000000000000000000))))) else (if n < 559 then (if n < 557 then (box (572263515000000000000000000000) (572275234000000000000000000000)) else (if n < 558 then (box (603510691000000000000000000000) (603522445000000000000000000000)) else (box (634733513000000000000000000000) (634745303000000000000000000000)))) else (if n < 560 then (box (665914382000000000000000000000) (665926207000000000000000000000)) else (if n < 561 then (box (697035538000000000000000000000) (697047399000000000000000000000)) else (box (728079086000000000000000000000) (728090982000000000000000000000)))))))
def cJ562_585 (n:Nat):IV:=(if n < 573 then (if n < 567 then (if n < 564 then (if n < 563 then (box (759026989000000000000000000000) (759038920000000000000000000000)) else (box (789861090000000000000000000000) (789873055000000000000000000000))) else (if n < 565 then (box (820563104000000000000000000000) (820575104000000000000000000000)) else (if n < 566 then (box (851114645000000000000000000000) (851126679000000000000000000000)) else (box (881497222000000000000000000000) (881509291000000000000000000000))))) else (if n < 570 then (if n < 568 then (box (911692258000000000000000000000) (911704361000000000000000000000)) else (if n < 569 then (box (941681088000000000000000000000) (941693225000000000000000000000)) else (box (971444983000000000000000000000) (971457153000000000000000000000)))) else (if n < 571 then (box (1000965143000000000000000000000) (1000977346000000000000000000000)) else (if n < 572 then (box (1030222722000000000000000000000) (1030234958000000000000000000000)) else (box (1059198829000000000000000000000) (1059211097000000000000000000000)))))) else (if n < 579 then (if n < 576 then (if n < 574 then (box (1087874542000000000000000000000) (1087886842000000000000000000000)) else (if n < 575 then (box (1116230913000000000000000000000) (1116243245000000000000000000000)) else (box (1144248984000000000000000000000) (1144261348000000000000000000000)))) else (if n < 577 then (box (1171909801000000000000000000000) (1171922196000000000000000000000)) else (if n < 578 then (box (1199194410000000000000000000000) (1199206836000000000000000000000)) else (box (1226083882000000000000000000000) (1226096338000000000000000000000))))) else (if n < 582 then (if n < 580 then (box (1252559315000000000000000000000) (1252571801000000000000000000000)) else (if n < 581 then (box (1278601853000000000000000000000) (1278614369000000000000000000000)) else (box (1304192688000000000000000000000) (1304205234000000000000000000000)))) else (if n < 583 then (box (1329313073000000000000000000000) (1329325648000000000000000000000)) else (if n < 584 then (box (1353944339000000000000000000000) (1353956943000000000000000000000)) else (box (1378067903000000000000000000000) (1378080535000000000000000000000)))))))
def cJ540_585 (n:Nat):IV:=(if n < 562 then (cJ540_562 n) else (cJ562_585 n))
def cJ585_607 (n:Nat):IV:=(if n < 596 then (if n < 590 then (if n < 587 then (if n < 586 then (box (1401665273000000000000000000000) (1401677933000000000000000000000)) else (box (1424718070000000000000000000000) (1424730757000000000000000000000))) else (if n < 588 then (box (1447208030000000000000000000000) (1447220744000000000000000000000)) else (if n < 589 then (box (1469117021000000000000000000000) (1469129762000000000000000000000)) else (box (1490427049000000000000000000000) (1490439816000000000000000000000))))) else (if n < 593 then (if n < 591 then (box (1511120279000000000000000000000) (1511133072000000000000000000000)) else (if n < 592 then (box (1531179035000000000000000000000) (1531191853000000000000000000000)) else (box (1550585820000000000000000000000) (1550598662000000000000000000000)))) else (if n < 594 then (box (1569323323000000000000000000000) (1569336190000000000000000000000)) else (if n < 595 then (box (1587374430000000000000000000000) (1587387321000000000000000000000)) else (box (1604722240000000000000000000000) (1604735154000000000000000000000)))))) else (if n < 601 then (if n < 598 then (if n < 597 then (box (1621350073000000000000000000000) (1621363010000000000000000000000)) else (box (1637241482000000000000000000000) (1637254442000000000000000000000))) else (if n < 599 then (box (1652380264000000000000000000000) (1652393246000000000000000000000)) else (if n < 600 then (box (1666750473000000000000000000000) (1666763477000000000000000000000)) else (box (1680336430000000000000000000000) (1680349455000000000000000000000))))) else (if n < 604 then (if n < 602 then (box (1693122737000000000000000000000) (1693135782000000000000000000000)) else (if n < 603 then (box (1705094283000000000000000000000) (1705107348000000000000000000000)) else (box (1716236261000000000000000000000) (1716249345000000000000000000000)))) else (if n < 605 then (box (1726534177000000000000000000000) (1726547280000000000000000000000)) else (if n < 606 then (box (1735973861000000000000000000000) (1735986982000000000000000000000)) else (box (1744541477000000000000000000000) (1744554615000000000000000000000)))))))
def cJ607_630 (n:Nat):IV:=(if n < 618 then (if n < 612 then (if n < 609 then (if n < 608 then (box (1752223535000000000000000000000) (1752236690000000000000000000000)) else (box (1759006904000000000000000000000) (1759020076000000000000000000000))) else (if n < 610 then (box (1764878820000000000000000000000) (1764892008000000000000000000000)) else (if n < 611 then (box (1769826897000000000000000000000) (1769840101000000000000000000000)) else (box (1773839141000000000000000000000) (1773852360000000000000000000000))))) else (if n < 615 then (if n < 613 then (box (1776903957000000000000000000000) (1776917190000000000000000000000)) else (if n < 614 then (box (1779010160000000000000000000000) (1779023407000000000000000000000)) else (box (1780146986000000000000000000000) (1780160246000000000000000000000)))) else (if n < 616 then (box (1780304102000000000000000000000) (1780317375000000000000000000000)) else (if n < 617 then (box (1779471617000000000000000000000) (1779484903000000000000000000000)) else (box (1777640091000000000000000000000) (1777653391000000000000000000000)))))) else (if n < 624 then (if n < 621 then (if n < 619 then (box (1774800545000000000000000000000) (1774813859000000000000000000000)) else (if n < 620 then (box (1770944468000000000000000000000) (1770957798000000000000000000000)) else (box (1766063833000000000000000000000) (1766077179000000000000000000000)))) else (if n < 622 then (box (1760151101000000000000000000000) (1760164464000000000000000000000)) else (if n < 623 then (box (1753199230000000000000000000000) (1753212610000000000000000000000)) else (box (1745201685000000000000000000000) (1745215083000000000000000000000))))) else (if n < 627 then (if n < 625 then (box (1736152450000000000000000000000) (1736165866000000000000000000000)) else (if n < 626 then (box (1726046030000000000000000000000) (1726059465000000000000000000000)) else (box (1714877464000000000000000000000) (1714890919000000000000000000000)))) else (if n < 628 then (box (1702642333000000000000000000000) (1702655809000000000000000000000)) else (if n < 629 then (box (1689336764000000000000000000000) (1689350262000000000000000000000)) else (box (1674957445000000000000000000000) (1674970964000000000000000000000)))))))
def cJ585_630 (n:Nat):IV:=(if n < 607 then (cJ585_607 n) else (cJ607_630 n))
def cJ540_630 (n:Nat):IV:=(if n < 585 then (cJ540_585 n) else (cJ585_630 n))
def cJ630_652 (n:Nat):IV:=(if n < 641 then (if n < 635 then (if n < 632 then (if n < 631 then (box (1659501624000000000000000000000) (1659515165000000000000000000000)) else (box (1642967120000000000000000000000) (1642980684000000000000000000000))) else (if n < 633 then (box (1625352333000000000000000000000) (1625365921000000000000000000000)) else (if n < 634 then (box (1606656245000000000000000000000) (1606669858000000000000000000000)) else (box (1586878432000000000000000000000) (1586892070000000000000000000000))))) else (if n < 638 then (if n < 636 then (box (1566019064000000000000000000000) (1566032727000000000000000000000)) else (if n < 637 then (box (1544078914000000000000000000000) (1544092603000000000000000000000)) else (box (1521059366000000000000000000000) (1521073082000000000000000000000)))) else (if n < 639 then (box (1496962418000000000000000000000) (1496976162000000000000000000000)) else (if n < 640 then (box (1471790686000000000000000000000) (1471804458000000000000000000000)) else (box (1445547413000000000000000000000) (1445561213000000000000000000000)))))) else (if n < 646 then (if n < 643 then (if n < 642 then (box (1418236463000000000000000000000) (1418250292000000000000000000000)) else (box (1389862340000000000000000000000) (1389876199000000000000000000000))) else (if n < 644 then (box (1360430185000000000000000000000) (1360444074000000000000000000000)) else (if n < 645 then (box (1329945772000000000000000000000) (1329959691000000000000000000000)) else (box (1298415523000000000000000000000) (1298429473000000000000000000000))))) else (if n < 649 then (if n < 647 then (box (1265846505000000000000000000000) (1265860487000000000000000000000)) else (if n < 648 then (box (1232246432000000000000000000000) (1232260446000000000000000000000)) else (box (1197623672000000000000000000000) (1197637719000000000000000000000)))) else (if n < 650 then (box (1161987243000000000000000000000) (1162001323000000000000000000000)) else (if n < 651 then (box (1125346820000000000000000000000) (1125360934000000000000000000000)) else (box (1087712730000000000000000000000) (1087726879000000000000000000000)))))))
def cJ652_675 (n:Nat):IV:=(if n < 663 then (if n < 657 then (if n < 654 then (if n < 653 then (box (1049095958000000000000000000000) (1049110142000000000000000000000)) else (box (1009508146000000000000000000000) (1009522366000000000000000000000))) else (if n < 655 then (box (968961593000000000000000000000) (968975849000000000000000000000)) else (if n < 656 then (box (927469249000000000000000000000) (927483541000000000000000000000)) else (box (885044731000000000000000000000) (885059060000000000000000000000))))) else (if n < 660 then (if n < 658 then (box (841702301000000000000000000000) (841716667000000000000000000000)) else (if n < 659 then (box (797456881000000000000000000000) (797471284000000000000000000000)) else (box (752324041000000000000000000000) (752338482000000000000000000000)))) else (if n < 661 then (box (706320002000000000000000000000) (706334482000000000000000000000)) else (if n < 662 then (box (659461634000000000000000000000) (659476152000000000000000000000)) else (box (611766446000000000000000000000) (611781003000000000000000000000)))))) else (if n < 669 then (if n < 666 then (if n < 664 then (box (563252593000000000000000000000) (563267190000000000000000000000)) else (if n < 665 then (box (513938869000000000000000000000) (513953506000000000000000000000)) else (box (463844695000000000000000000000) (463859373000000000000000000000)))) else (if n < 667 then (box (412990128000000000000000000000) (413004846000000000000000000000)) else (if n < 668 then (box (361395842000000000000000000000) (361410601000000000000000000000)) else (box (309083136000000000000000000000) (309097936000000000000000000000))))) else (if n < 672 then (if n < 670 then (box (256073919000000000000000000000) (256088760000000000000000000000)) else (if n < 671 then (box (202390707000000000000000000000) (202405590000000000000000000000)) else (box (148056620000000000000000000000) (148071545000000000000000000000)))) else (if n < 673 then (box (93095367000000000000000000000) (93110334000000000000000000000)) else (if n < 674 then (box (37531249000000000000000000000) (37546258000000000000000000000)) else (box (-18610860000000000000000000000) (-18595809000000000000000000000)))))))
def cJ630_675 (n:Nat):IV:=(if n < 652 then (cJ630_652 n) else (cJ652_675 n))
def cJ675_698 (n:Nat):IV:=(if n < 686 then (if n < 680 then (if n < 677 then (if n < 676 then (box (-75305510000000000000000000000) (-75290416000000000000000000000)) else (box (-132526687000000000000000000000) (-132511551000000000000000000000))) else (if n < 678 then (box (-190247830000000000000000000000) (-190232651000000000000000000000)) else (if n < 679 then (box (-248441826000000000000000000000) (-248426604000000000000000000000)) else (box (-307081033000000000000000000000) (-307065768000000000000000000000))))) else (if n < 683 then (if n < 681 then (box (-366137278000000000000000000000) (-366121970000000000000000000000)) else (if n < 682 then (box (-425581881000000000000000000000) (-425566529000000000000000000000)) else (box (-485385652000000000000000000000) (-485370256000000000000000000000)))) else (if n < 684 then (box (-545518910000000000000000000000) (-545503470000000000000000000000)) else (if n < 685 then (box (-605951494000000000000000000000) (-605936010000000000000000000000)) else (box (-666652771000000000000000000000) (-666637244000000000000000000000)))))) else (if n < 692 then (if n < 689 then (if n < 687 then (box (-727591655000000000000000000000) (-727576084000000000000000000000)) else (if n < 688 then (box (-788736614000000000000000000000) (-788720999000000000000000000000)) else (box (-850055686000000000000000000000) (-850040027000000000000000000000)))) else (if n < 690 then (box (-911516492000000000000000000000) (-911500789000000000000000000000)) else (if n < 691 then (box (-973086245000000000000000000000) (-973070498000000000000000000000)) else (box (-1034731772000000000000000000000) (-1034715981000000000000000000000))))) else (if n < 695 then (if n < 693 then (box (-1096419524000000000000000000000) (-1096403689000000000000000000000)) else (if n < 694 then (box (-1158115594000000000000000000000) (-1158099715000000000000000000000)) else (box (-1219785727000000000000000000000) (-1219769804000000000000000000000)))) else (if n < 696 then (box (-1281395342000000000000000000000) (-1281379375000000000000000000000)) else (if n < 697 then (box (-1342909542000000000000000000000) (-1342893531000000000000000000000)) else (box (-1404293134000000000000000000000) (-1404277079000000000000000000000)))))))
def cJ698_721 (n:Nat):IV:=(if n < 709 then (if n < 703 then (if n < 700 then (if n < 699 then (box (-1465510642000000000000000000000) (-1465494544000000000000000000000)) else (box (-1526526329000000000000000000000) (-1526510187000000000000000000000))) else (if n < 701 then (box (-1587304215000000000000000000000) (-1587288030000000000000000000000)) else (if n < 702 then (box (-1647808086000000000000000000000) (-1647791858000000000000000000000)) else (box (-1708001516000000000000000000000) (-1707985245000000000000000000000))))) else (if n < 706 then (if n < 704 then (box (-1767847892000000000000000000000) (-1767831578000000000000000000000)) else (if n < 705 then (box (-1827310425000000000000000000000) (-1827294068000000000000000000000)) else (box (-1886352164000000000000000000000) (-1886335764000000000000000000000)))) else (if n < 707 then (box (-1944936029000000000000000000000) (-1944919586000000000000000000000)) else (if n < 708 then (box (-2003024820000000000000000000000) (-2003008335000000000000000000000)) else (box (-2060581238000000000000000000000) (-2060564711000000000000000000000)))))) else (if n < 715 then (if n < 712 then (if n < 710 then (box (-2117567908000000000000000000000) (-2117551340000000000000000000000)) else (if n < 711 then (box (-2173947396000000000000000000000) (-2173930787000000000000000000000)) else (box (-2229682229000000000000000000000) (-2229665579000000000000000000000)))) else (if n < 713 then (box (-2284734919000000000000000000000) (-2284718228000000000000000000000)) else (if n < 714 then (box (-2339067980000000000000000000000) (-2339051248000000000000000000000)) else (box (-2392643947000000000000000000000) (-2392627175000000000000000000000))))) else (if n < 718 then (if n < 716 then (box (-2445425408000000000000000000000) (-2445408596000000000000000000000)) else (if n < 717 then (box (-2497375010000000000000000000000) (-2497358159000000000000000000000)) else (box (-2548455494000000000000000000000) (-2548438604000000000000000000000)))) else (if n < 719 then (box (-2598629704000000000000000000000) (-2598612775000000000000000000000)) else (if n < 720 then (box (-2647860620000000000000000000000) (-2647843652000000000000000000000)) else (box (-2696111377000000000000000000000) (-2696094371000000000000000000000)))))))
def cJ675_721 (n:Nat):IV:=(if n < 698 then (cJ675_698 n) else (cJ698_721 n))
def cJ630_721 (n:Nat):IV:=(if n < 675 then (cJ630_675 n) else (cJ675_721 n))
def cJ540_721 (n:Nat):IV:=(if n < 630 then (cJ540_630 n) else (cJ630_721 n))
def cJ360_721 (n:Nat):IV:=(if n < 540 then (cJ360_540 n) else (cJ540_721 n))
def cJ0_721 (n:Nat):IV:=(if n < 360 then (cJ0_360 n) else (cJ360_721 n))
def cV0_22 (n:Nat):IV:=(if n < 11 then (if n < 5 then (if n < 2 then (if n < 1 then (box (0) (0)) else (box (45535000000000000000000000) (45537000000000000000000000))) else (if n < 3 then (box (182121000000000000000000000) (182126000000000000000000000)) else (if n < 4 then (box (409697000000000000000000000) (409705000000000000000000000)) else (box (728159000000000000000000000) (728171000000000000000000000))))) else (if n < 8 then (if n < 6 then (box (1137362000000000000000000000) (1137379000000000000000000000)) else (if n < 7 then (box (1637121000000000000000000000) (1637143000000000000000000000)) else (box (2227208000000000000000000000) (2227236000000000000000000000)))) else (if n < 9 then (box (2907356000000000000000000000) (2907390000000000000000000000)) else (if n < 10 then (box (3677255000000000000000000000) (3677296000000000000000000000)) else (box (4536555000000000000000000000) (4536604000000000000000000000)))))) else (if n < 16 then (if n < 13 then (if n < 12 then (box (5484866000000000000000000000) (5484924000000000000000000000)) else (box (6521755000000000000000000000) (6521822000000000000000000000))) else (if n < 14 then (box (7646751000000000000000000000) (7646828000000000000000000000)) else (if n < 15 then (box (8859343000000000000000000000) (8859430000000000000000000000)) else (box (10158976000000000000000000000) (10159073000000000000000000000))))) else (if n < 19 then (if n < 17 then (box (11545058000000000000000000000) (11545167000000000000000000000)) else (if n < 18 then (box (13016958000000000000000000000) (13017078000000000000000000000)) else (box (14574003000000000000000000000) (14574135000000000000000000000)))) else (if n < 20 then (box (16215482000000000000000000000) (16215627000000000000000000000)) else (if n < 21 then (box (17940645000000000000000000000) (17940803000000000000000000000)) else (box (19748700000000000000000000000) (19748872000000000000000000000)))))))
def cV22_45 (n:Nat):IV:=(if n < 33 then (if n < 27 then (if n < 24 then (if n < 23 then (box (21638823000000000000000000000) (21639009000000000000000000000)) else (box (23610144000000000000000000000) (23610346000000000000000000000))) else (if n < 25 then (box (25661762000000000000000000000) (25661980000000000000000000000)) else (if n < 26 then (box (27792734000000000000000000000) (27792968000000000000000000000)) else (box (30002079000000000000000000000) (30002330000000000000000000000))))) else (if n < 30 then (if n < 28 then (box (32288782000000000000000000000) (32289051000000000000000000000)) else (if n < 29 then (box (34651789000000000000000000000) (34652076000000000000000000000)) else (box (37090011000000000000000000000) (37090316000000000000000000000)))) else (if n < 31 then (box (39602322000000000000000000000) (39602646000000000000000000000)) else (if n < 32 then (box (42187563000000000000000000000) (42187906000000000000000000000)) else (box (44844533000000000000000000000) (44844896000000000000000000000)))))) else (if n < 39 then (if n < 36 then (if n < 34 then (box (47572005000000000000000000000) (47572388000000000000000000000)) else (if n < 35 then (box (50368712000000000000000000000) (50369115000000000000000000000)) else (box (53233353000000000000000000000) (53233777000000000000000000000)))) else (if n < 37 then (box (56164596000000000000000000000) (56165042000000000000000000000)) else (if n < 38 then (box (59161076000000000000000000000) (59161544000000000000000000000)) else (box (62221393000000000000000000000) (62221883000000000000000000000))))) else (if n < 42 then (if n < 40 then (box (65344118000000000000000000000) (65344631000000000000000000000)) else (if n < 41 then (box (68527786000000000000000000000) (68528322000000000000000000000)) else (box (71770907000000000000000000000) (71771467000000000000000000000)))) else (if n < 43 then (box (75071956000000000000000000000) (75072540000000000000000000000)) else (if n < 44 then (box (78429380000000000000000000000) (78429988000000000000000000000)) else (box (81841593000000000000000000000) (81842225000000000000000000000)))))))
def cV0_45 (n:Nat):IV:=(if n < 22 then (cV0_22 n) else (cV22_45 n))
def cV45_67 (n:Nat):IV:=(if n < 56 then (if n < 50 then (if n < 47 then (if n < 46 then (box (85306987000000000000000000000) (85307644000000000000000000000)) else (box (88823920000000000000000000000) (88824602000000000000000000000))) else (if n < 48 then (box (92390724000000000000000000000) (92391431000000000000000000000)) else (if n < 49 then (box (96005705000000000000000000000) (96006437000000000000000000000)) else (box (99667139000000000000000000000) (99667897000000000000000000000))))) else (if n < 53 then (if n < 51 then (box (103373283000000000000000000000) (103374067000000000000000000000)) else (if n < 52 then (box (107122361000000000000000000000) (107123171000000000000000000000)) else (box (110912577000000000000000000000) (110913414000000000000000000000)))) else (if n < 54 then (box (114742110000000000000000000000) (114742973000000000000000000000)) else (if n < 55 then (box (118609118000000000000000000000) (118610008000000000000000000000)) else (box (122511731000000000000000000000) (122512648000000000000000000000)))))) else (if n < 61 then (if n < 58 then (if n < 57 then (box (126448062000000000000000000000) (126449006000000000000000000000)) else (box (130416203000000000000000000000) (130417175000000000000000000000))) else (if n < 59 then (box (134414221000000000000000000000) (134415221000000000000000000000)) else (if n < 60 then (box (138440168000000000000000000000) (138441196000000000000000000000)) else (box (142492076000000000000000000000) (142493132000000000000000000000))))) else (if n < 64 then (if n < 62 then (box (146567958000000000000000000000) (146569042000000000000000000000)) else (if n < 63 then (box (150665808000000000000000000000) (150666920000000000000000000000)) else (box (154783606000000000000000000000) (154784746000000000000000000000)))) else (if n < 65 then (box (158919315000000000000000000000) (158920483000000000000000000000)) else (if n < 66 then (box (163070884000000000000000000000) (163072081000000000000000000000)) else (box (167236247000000000000000000000) (167237472000000000000000000000)))))))
def cV67_90 (n:Nat):IV:=(if n < 78 then (if n < 72 then (if n < 69 then (if n < 68 then (box (171413320000000000000000000000) (171414574000000000000000000000)) else (box (175600017000000000000000000000) (175601300000000000000000000000))) else (if n < 70 then (box (179794228000000000000000000000) (179795539000000000000000000000)) else (if n < 71 then (box (183993842000000000000000000000) (183995182000000000000000000000)) else (box (188196730000000000000000000000) (188198099000000000000000000000))))) else (if n < 75 then (if n < 73 then (box (192400760000000000000000000000) (192402157000000000000000000000)) else (if n < 74 then (box (196603789000000000000000000000) (196605214000000000000000000000)) else (box (200803664000000000000000000000) (200805117000000000000000000000)))) else (if n < 76 then (box (204998227000000000000000000000) (204999708000000000000000000000)) else (if n < 77 then (box (209185316000000000000000000000) (209186826000000000000000000000)) else (box (213362763000000000000000000000) (213364301000000000000000000000)))))) else (if n < 84 then (if n < 81 then (if n < 79 then (box (217528395000000000000000000000) (217529961000000000000000000000)) else (if n < 80 then (box (221680038000000000000000000000) (221681632000000000000000000000)) else (box (225815513000000000000000000000) (225817134000000000000000000000)))) else (if n < 82 then (box (229932642000000000000000000000) (229934290000000000000000000000)) else (if n < 83 then (box (234029244000000000000000000000) (234030919000000000000000000000)) else (box (238103140000000000000000000000) (238104843000000000000000000000))))) else (if n < 87 then (if n < 85 then (box (242152156000000000000000000000) (242153886000000000000000000000)) else (if n < 86 then (box (246174116000000000000000000000) (246175872000000000000000000000)) else (box (250166847000000000000000000000) (250168630000000000000000000000)))) else (if n < 88 then (box (254128183000000000000000000000) (254129992000000000000000000000)) else (if n < 89 then (box (258055963000000000000000000000) (258057798000000000000000000000)) else (box (261948031000000000000000000000) (261949892000000000000000000000)))))))
def cV45_90 (n:Nat):IV:=(if n < 67 then (cV45_67 n) else (cV67_90 n))
def cV0_90 (n:Nat):IV:=(if n < 45 then (cV0_45 n) else (cV45_90 n))
def cV90_112 (n:Nat):IV:=(if n < 101 then (if n < 95 then (if n < 92 then (if n < 91 then (box (265802240000000000000000000000) (265804127000000000000000000000)) else (box (269616448000000000000000000000) (269618360000000000000000000000))) else (if n < 93 then (box (273388528000000000000000000000) (273390465000000000000000000000)) else (if n < 94 then (box (277116356000000000000000000000) (277118317000000000000000000000)) else (box (280797823000000000000000000000) (280799808000000000000000000000))))) else (if n < 98 then (if n < 96 then (box (284430834000000000000000000000) (284432842000000000000000000000)) else (if n < 97 then (box (288013302000000000000000000000) (288015334000000000000000000000)) else (box (291543161000000000000000000000) (291545216000000000000000000000)))) else (if n < 99 then (box (295018351000000000000000000000) (295020429000000000000000000000)) else (if n < 100 then (box (298436837000000000000000000000) (298438938000000000000000000000)) else (box (301796596000000000000000000000) (301798719000000000000000000000)))))) else (if n < 106 then (if n < 103 then (if n < 102 then (box (305095626000000000000000000000) (305097771000000000000000000000)) else (box (308331939000000000000000000000) (308334105000000000000000000000))) else (if n < 104 then (box (311503574000000000000000000000) (311505761000000000000000000000)) else (if n < 105 then (box (314608585000000000000000000000) (314610793000000000000000000000)) else (box (317645052000000000000000000000) (317647280000000000000000000000))))) else (if n < 109 then (if n < 107 then (box (320611075000000000000000000000) (320613323000000000000000000000)) else (if n < 108 then (box (323504780000000000000000000000) (323507047000000000000000000000)) else (box (326324317000000000000000000000) (326326603000000000000000000000)))) else (if n < 110 then (box (329067863000000000000000000000) (329070168000000000000000000000)) else (if n < 111 then (box (331733622000000000000000000000) (331735945000000000000000000000)) else (box (334319824000000000000000000000) (334322164000000000000000000000)))))))
def cV112_135 (n:Nat):IV:=(if n < 123 then (if n < 117 then (if n < 114 then (if n < 113 then (box (336824728000000000000000000000) (336827085000000000000000000000)) else (box (339246626000000000000000000000) (339248999000000000000000000000))) else (if n < 115 then (box (341583837000000000000000000000) (341586225000000000000000000000)) else (if n < 116 then (box (343834713000000000000000000000) (343837116000000000000000000000)) else (box (345997639000000000000000000000) (346000057000000000000000000000))))) else (if n < 120 then (if n < 118 then (box (348071034000000000000000000000) (348073466000000000000000000000)) else (if n < 119 then (box (350053350000000000000000000000) (350055795000000000000000000000)) else (box (351943076000000000000000000000) (351945534000000000000000000000)))) else (if n < 121 then (box (353738736000000000000000000000) (353741206000000000000000000000)) else (if n < 122 then (box (355438893000000000000000000000) (355441374000000000000000000000)) else (box (357042147000000000000000000000) (357044639000000000000000000000)))))) else (if n < 129 then (if n < 126 then (if n < 124 then (box (358547136000000000000000000000) (358549638000000000000000000000)) else (if n < 125 then (box (359952540000000000000000000000) (359955052000000000000000000000)) else (box (361257079000000000000000000000) (361259600000000000000000000000)))) else (if n < 127 then (box (362459514000000000000000000000) (362462044000000000000000000000)) else (if n < 128 then (box (363558649000000000000000000000) (363561187000000000000000000000)) else (box (364553331000000000000000000000) (364555877000000000000000000000))))) else (if n < 132 then (if n < 130 then (box (365442453000000000000000000000) (365445006000000000000000000000)) else (if n < 131 then (box (366224950000000000000000000000) (366227510000000000000000000000)) else (box (366899805000000000000000000000) (366902371000000000000000000000)))) else (if n < 133 then (box (367466047000000000000000000000) (367468618000000000000000000000)) else (if n < 134 then (box (367922752000000000000000000000) (367925328000000000000000000000)) else (box (368269044000000000000000000000) (368271624000000000000000000000)))))))
def cV90_135 (n:Nat):IV:=(if n < 112 then (cV90_112 n) else (cV112_135 n))
def cV135_157 (n:Nat):IV:=(if n < 146 then (if n < 140 then (if n < 137 then (if n < 136 then (box (368504096000000000000000000000) (368506680000000000000000000000)) else (box (368627131000000000000000000000) (368629718000000000000000000000))) else (if n < 138 then (box (368637422000000000000000000000) (368640012000000000000000000000)) else (if n < 139 then (box (368534292000000000000000000000) (368536885000000000000000000000)) else (box (368317117000000000000000000000) (368319714000000000000000000000))))) else (if n < 143 then (if n < 141 then (box (367985325000000000000000000000) (367987926000000000000000000000)) else (if n < 142 then (box (367538396000000000000000000000) (367541002000000000000000000000)) else (box (366975865000000000000000000000) (366978476000000000000000000000)))) else (if n < 144 then (box (366297320000000000000000000000) (366299937000000000000000000000)) else (if n < 145 then (box (365502405000000000000000000000) (365505028000000000000000000000)) else (box (364590818000000000000000000000) (364593448000000000000000000000)))))) else (if n < 151 then (if n < 148 then (if n < 147 then (box (363562314000000000000000000000) (363564951000000000000000000000)) else (box (362416704000000000000000000000) (362419349000000000000000000000))) else (if n < 149 then (box (361153856000000000000000000000) (361156510000000000000000000000)) else (if n < 150 then (box (359773694000000000000000000000) (359776357000000000000000000000)) else (box (358276202000000000000000000000) (358278876000000000000000000000))))) else (if n < 154 then (if n < 152 then (box (356661422000000000000000000000) (356664106000000000000000000000)) else (if n < 153 then (box (354929454000000000000000000000) (354932149000000000000000000000)) else (box (353080456000000000000000000000) (353083163000000000000000000000)))) else (if n < 155 then (box (351114648000000000000000000000) (351117367000000000000000000000)) else (if n < 156 then (box (349032308000000000000000000000) (349035040000000000000000000000)) else (box (346833776000000000000000000000) (346836521000000000000000000000)))))))
def cV157_180 (n:Nat):IV:=(if n < 168 then (if n < 162 then (if n < 159 then (if n < 158 then (box (344519449000000000000000000000) (344522208000000000000000000000)) else (box (342089789000000000000000000000) (342092563000000000000000000000))) else (if n < 160 then (box (339545315000000000000000000000) (339548105000000000000000000000)) else (if n < 161 then (box (336886612000000000000000000000) (336889417000000000000000000000)) else (box (334114320000000000000000000000) (334117141000000000000000000000))))) else (if n < 165 then (if n < 163 then (box (331229147000000000000000000000) (331231985000000000000000000000)) else (if n < 164 then (box (328231858000000000000000000000) (328234713000000000000000000000)) else (box (325123283000000000000000000000) (325126156000000000000000000000)))) else (if n < 166 then (box (321904310000000000000000000000) (321907201000000000000000000000)) else (if n < 167 then (box (318575895000000000000000000000) (318578804000000000000000000000)) else (box (315139048000000000000000000000) (315141977000000000000000000000)))))) else (if n < 174 then (if n < 171 then (if n < 169 then (box (311594850000000000000000000000) (311597798000000000000000000000)) else (if n < 170 then (box (307944435000000000000000000000) (307947403000000000000000000000)) else (box (304189007000000000000000000000) (304191996000000000000000000000)))) else (if n < 172 then (box (300329825000000000000000000000) (300332835000000000000000000000)) else (if n < 173 then (box (296368214000000000000000000000) (296371246000000000000000000000)) else (box (292305559000000000000000000000) (292308613000000000000000000000))))) else (if n < 177 then (if n < 175 then (box (288143308000000000000000000000) (288146384000000000000000000000)) else (if n < 176 then (box (283882966000000000000000000000) (283886064000000000000000000000)) else (box (279526103000000000000000000000) (279529224000000000000000000000)))) else (if n < 178 then (box (275074349000000000000000000000) (275077493000000000000000000000)) else (if n < 179 then (box (270529393000000000000000000000) (270532561000000000000000000000)) else (box (265892982000000000000000000000) (265896174000000000000000000000)))))))
def cV135_180 (n:Nat):IV:=(if n < 157 then (cV135_157 n) else (cV157_180 n))
def cV90_180 (n:Nat):IV:=(if n < 135 then (cV90_135 n) else (cV135_180 n))
def cV0_180 (n:Nat):IV:=(if n < 90 then (cV0_90 n) else (cV90_180 n))
def cV180_202 (n:Nat):IV:=(if n < 191 then (if n < 185 then (if n < 182 then (if n < 181 then (box (261166928000000000000000000000) (261170145000000000000000000000)) else (box (256353100000000000000000000000) (256356342000000000000000000000))) else (if n < 183 then (box (251453422000000000000000000000) (251456689000000000000000000000)) else (if n < 184 then (box (246469881000000000000000000000) (246473174000000000000000000000)) else (box (241404521000000000000000000000) (241407840000000000000000000000))))) else (if n < 188 then (if n < 186 then (box (236259441000000000000000000000) (236262786000000000000000000000)) else (if n < 187 then (box (231036798000000000000000000000) (231040170000000000000000000000)) else (box (225738808000000000000000000000) (225742207000000000000000000000)))) else (if n < 189 then (box (220367738000000000000000000000) (220371164000000000000000000000)) else (if n < 190 then (box (214925910000000000000000000000) (214929363000000000000000000000)) else (box (209415705000000000000000000000) (209419185000000000000000000000)))))) else (if n < 196 then (if n < 193 then (if n < 192 then (box (203839554000000000000000000000) (203843061000000000000000000000)) else (box (198199938000000000000000000000) (198203473000000000000000000000))) else (if n < 194 then (box (192499394000000000000000000000) (192502957000000000000000000000)) else (if n < 195 then (box (186740512000000000000000000000) (186744103000000000000000000000)) else (box (180925924000000000000000000000) (180929543000000000000000000000))))) else (if n < 199 then (if n < 197 then (box (175058320000000000000000000000) (175061968000000000000000000000)) else (if n < 198 then (box (169140431000000000000000000000) (169144108000000000000000000000)) else (box (163175043000000000000000000000) (163178749000000000000000000000)))) else (if n < 200 then (box (157164982000000000000000000000) (157168716000000000000000000000)) else (if n < 201 then (box (151113123000000000000000000000) (151116886000000000000000000000)) else (box (145022384000000000000000000000) (145026176000000000000000000000)))))))
def cV202_225 (n:Nat):IV:=(if n < 213 then (if n < 207 then (if n < 204 then (if n < 203 then (box (138895725000000000000000000000) (138899546000000000000000000000)) else (box (132736151000000000000000000000) (132740001000000000000000000000))) else (if n < 205 then (box (126546708000000000000000000000) (126550587000000000000000000000)) else (if n < 206 then (box (120330478000000000000000000000) (120334386000000000000000000000)) else (box (114090586000000000000000000000) (114094523000000000000000000000))))) else (if n < 210 then (if n < 208 then (box (107830192000000000000000000000) (107834158000000000000000000000)) else (if n < 209 then (box (101552491000000000000000000000) (101556486000000000000000000000)) else (box (95260715000000000000000000000) (95264739000000000000000000000)))) else (if n < 211 then (box (88958129000000000000000000000) (88962182000000000000000000000)) else (if n < 212 then (box (82648032000000000000000000000) (82652114000000000000000000000)) else (box (76333748000000000000000000000) (76337858000000000000000000000)))))) else (if n < 219 then (if n < 216 then (if n < 214 then (box (70018637000000000000000000000) (70022776000000000000000000000)) else (if n < 215 then (box (63706084000000000000000000000) (63710251000000000000000000000)) else (box (57399496000000000000000000000) (57403691000000000000000000000)))) else (if n < 217 then (box (51102314000000000000000000000) (51106538000000000000000000000)) else (if n < 218 then (box (44817996000000000000000000000) (44822248000000000000000000000)) else (box (38550020000000000000000000000) (38554300000000000000000000000))))) else (if n < 222 then (if n < 220 then (box (32301893000000000000000000000) (32306201000000000000000000000)) else (if n < 221 then (box (26077130000000000000000000000) (26081466000000000000000000000)) else (box (19879272000000000000000000000) (19883636000000000000000000000)))) else (if n < 223 then (box (13711868000000000000000000000) (13716260000000000000000000000)) else (if n < 224 then (box (7578488000000000000000000000) (7582907000000000000000000000)) else (box (1482709000000000000000000000) (1487154000000000000000000000)))))))
def cV180_225 (n:Nat):IV:=(if n < 202 then (cV180_202 n) else (cV202_225 n))
def cV225_247 (n:Nat):IV:=(if n < 236 then (if n < 230 then (if n < 227 then (if n < 226 then (box (-4571883000000000000000000000) (-4567411000000000000000000000)) else (box (-10581690000000000000000000000) (-10577192000000000000000000000))) else (if n < 228 then (box (-16543109000000000000000000000) (-16538585000000000000000000000)) else (if n < 229 then (box (-22452531000000000000000000000) (-22447982000000000000000000000)) else (box (-28306347000000000000000000000) (-28301772000000000000000000000))))) else (if n < 233 then (if n < 231 then (box (-34100940000000000000000000000) (-34096339000000000000000000000)) else (if n < 232 then (box (-39832699000000000000000000000) (-39828073000000000000000000000)) else (box (-45498016000000000000000000000) (-45493366000000000000000000000)))) else (if n < 234 then (box (-51093283000000000000000000000) (-51088609000000000000000000000)) else (if n < 235 then (box (-56614904000000000000000000000) (-56610206000000000000000000000)) else (box (-62059285000000000000000000000) (-62054564000000000000000000000)))))) else (if n < 241 then (if n < 238 then (if n < 237 then (box (-67422846000000000000000000000) (-67418102000000000000000000000)) else (box (-72702017000000000000000000000) (-72697251000000000000000000000))) else (if n < 239 then (box (-77893243000000000000000000000) (-77888455000000000000000000000)) else (if n < 240 then (box (-82992985000000000000000000000) (-82988176000000000000000000000)) else (box (-87997722000000000000000000000) (-87992891000000000000000000000))))) else (if n < 244 then (if n < 242 then (box (-92903953000000000000000000000) (-92899101000000000000000000000)) else (if n < 243 then (box (-97708195000000000000000000000) (-97703322000000000000000000000)) else (box (-102406994000000000000000000000) (-102402101000000000000000000000)))) else (if n < 245 then (box (-106996919000000000000000000000) (-106992007000000000000000000000)) else (if n < 246 then (box (-111474567000000000000000000000) (-111469636000000000000000000000)) else (box (-115836568000000000000000000000) (-115831619000000000000000000000)))))))
def cV247_270 (n:Nat):IV:=(if n < 258 then (if n < 252 then (if n < 249 then (if n < 248 then (box (-120079580000000000000000000000) (-120074613000000000000000000000)) else (box (-124200296000000000000000000000) (-124195312000000000000000000000))) else (if n < 250 then (box (-128195446000000000000000000000) (-128190445000000000000000000000)) else (if n < 251 then (box (-132061797000000000000000000000) (-132056779000000000000000000000)) else (box (-135796157000000000000000000000) (-135791123000000000000000000000))))) else (if n < 255 then (if n < 253 then (box (-139395375000000000000000000000) (-139390325000000000000000000000)) else (if n < 254 then (box (-142856346000000000000000000000) (-142851281000000000000000000000)) else (box (-146176007000000000000000000000) (-146170927000000000000000000000)))) else (if n < 256 then (box (-149351347000000000000000000000) (-149346253000000000000000000000)) else (if n < 257 then (box (-152379404000000000000000000000) (-152374297000000000000000000000)) else (box (-155257269000000000000000000000) (-155252149000000000000000000000)))))) else (if n < 264 then (if n < 261 then (if n < 259 then (box (-157982085000000000000000000000) (-157976953000000000000000000000)) else (if n < 260 then (box (-160551053000000000000000000000) (-160545909000000000000000000000)) else (box (-162961432000000000000000000000) (-162956276000000000000000000000)))) else (if n < 262 then (box (-165210540000000000000000000000) (-165205373000000000000000000000)) else (if n < 263 then (box (-167295759000000000000000000000) (-167290581000000000000000000000)) else (box (-169214532000000000000000000000) (-169209345000000000000000000000))))) else (if n < 267 then (if n < 265 then (box (-170964371000000000000000000000) (-170959175000000000000000000000)) else (if n < 266 then (box (-172542855000000000000000000000) (-172537651000000000000000000000)) else (box (-173947632000000000000000000000) (-173942421000000000000000000000)))) else (if n < 268 then (box (-175176423000000000000000000000) (-175171205000000000000000000000)) else (if n < 269 then (box (-176227022000000000000000000000) (-176221797000000000000000000000)) else (box (-177097297000000000000000000000) (-177092066000000000000000000000)))))))
def cV225_270 (n:Nat):IV:=(if n < 247 then (cV225_247 n) else (cV247_270 n))
def cV180_270 (n:Nat):IV:=(if n < 225 then (cV180_225 n) else (cV225_270 n))
def cV270_292 (n:Nat):IV:=(if n < 281 then (if n < 275 then (if n < 272 then (if n < 271 then (box (-177785196000000000000000000000) (-177779959000000000000000000000)) else (box (-178288743000000000000000000000) (-178283501000000000000000000000))) else (if n < 273 then (box (-178606045000000000000000000000) (-178600799000000000000000000000)) else (if n < 274 then (box (-178735291000000000000000000000) (-178730041000000000000000000000)) else (box (-178674754000000000000000000000) (-178669500000000000000000000000))))) else (if n < 278 then (if n < 276 then (box (-178422794000000000000000000000) (-178417536000000000000000000000)) else (if n < 277 then (box (-177977857000000000000000000000) (-177972594000000000000000000000)) else (box (-177338480000000000000000000000) (-177333211000000000000000000000)))) else (if n < 279 then (box (-176503289000000000000000000000) (-176498014000000000000000000000)) else (if n < 280 then (box (-175471004000000000000000000000) (-175465723000000000000000000000)) else (box (-174240439000000000000000000000) (-174235151000000000000000000000)))))) else (if n < 286 then (if n < 283 then (if n < 282 then (box (-172810503000000000000000000000) (-172805207000000000000000000000)) else (box (-171180202000000000000000000000) (-171174897000000000000000000000))) else (if n < 284 then (box (-169348640000000000000000000000) (-169343326000000000000000000000)) else (if n < 285 then (box (-167315022000000000000000000000) (-167309698000000000000000000000)) else (box (-165078654000000000000000000000) (-165073320000000000000000000000))))) else (if n < 289 then (if n < 287 then (box (-162638944000000000000000000000) (-162633599000000000000000000000)) else (if n < 288 then (box (-159995404000000000000000000000) (-159990048000000000000000000000)) else (box (-157147652000000000000000000000) (-157142284000000000000000000000)))) else (if n < 290 then (box (-154095412000000000000000000000) (-154090031000000000000000000000)) else (if n < 291 then (box (-150838513000000000000000000000) (-150833119000000000000000000000)) else (box (-147376896000000000000000000000) (-147371488000000000000000000000)))))))
def cV292_315 (n:Nat):IV:=(if n < 303 then (if n < 297 then (if n < 294 then (if n < 293 then (box (-143710610000000000000000000000) (-143705188000000000000000000000)) else (box (-139839815000000000000000000000) (-139834378000000000000000000000))) else (if n < 295 then (box (-135764781000000000000000000000) (-135759328000000000000000000000)) else (if n < 296 then (box (-131485893000000000000000000000) (-131480425000000000000000000000)) else (box (-127003649000000000000000000000) (-126998164000000000000000000000))))) else (if n < 300 then (if n < 298 then (box (-122318659000000000000000000000) (-122313157000000000000000000000)) else (if n < 299 then (box (-117431649000000000000000000000) (-117426129000000000000000000000)) else (box (-112343462000000000000000000000) (-112337924000000000000000000000)))) else (if n < 301 then (box (-107055056000000000000000000000) (-107049499000000000000000000000)) else (if n < 302 then (box (-101567505000000000000000000000) (-101561929000000000000000000000)) else (box (-95882004000000000000000000000) (-95876408000000000000000000000)))))) else (if n < 309 then (if n < 306 then (if n < 304 then (box (-89999861000000000000000000000) (-89994245000000000000000000000)) else (if n < 305 then (box (-83922506000000000000000000000) (-83916870000000000000000000000)) else (box (-77651486000000000000000000000) (-77645829000000000000000000000)))) else (if n < 307 then (box (-71188470000000000000000000000) (-71182791000000000000000000000)) else (if n < 308 then (box (-64535240000000000000000000000) (-64529540000000000000000000000)) else (box (-57693702000000000000000000000) (-57687980000000000000000000000))))) else (if n < 312 then (if n < 310 then (box (-50665882000000000000000000000) (-50660137000000000000000000000)) else (if n < 311 then (box (-43453925000000000000000000000) (-43448157000000000000000000000)) else (box (-36060093000000000000000000000) (-36054302000000000000000000000)))) else (if n < 313 then (box (-28486770000000000000000000000) (-28480955000000000000000000000)) else (if n < 314 then (box (-20736459000000000000000000000) (-20730620000000000000000000000)) else (box (-12811783000000000000000000000) (-12805919000000000000000000000)))))))
def cV270_315 (n:Nat):IV:=(if n < 292 then (cV270_292 n) else (cV292_315 n))
def cV315_337 (n:Nat):IV:=(if n < 326 then (if n < 320 then (if n < 317 then (if n < 316 then (box (-4715483000000000000000000000) (-4709594000000000000000000000)) else (box (3549584000000000000000000000) (3555499000000000000000000000))) else (if n < 318 then (box (11980437000000000000000000000) (11986378000000000000000000000)) else (if n < 319 then (box (20573981000000000000000000000) (20579948000000000000000000000)) else (box (29327005000000000000000000000) (29332999000000000000000000000))))) else (if n < 323 then (if n < 321 then (box (38236180000000000000000000000) (38242201000000000000000000000)) else (if n < 322 then (box (47298056000000000000000000000) (47304105000000000000000000000)) else (box (56509077000000000000000000000) (56515154000000000000000000000)))) else (if n < 324 then (box (65865567000000000000000000000) (65871671000000000000000000000)) else (if n < 325 then (box (75363738000000000000000000000) (75369870000000000000000000000)) else (box (84999687000000000000000000000) (85005847000000000000000000000)))))) else (if n < 331 then (if n < 328 then (if n < 327 then (box (94769401000000000000000000000) (94775589000000000000000000000)) else (box (104668760000000000000000000000) (104674977000000000000000000000))) else (if n < 329 then (box (114693530000000000000000000000) (114699776000000000000000000000)) else (if n < 330 then (box (124839370000000000000000000000) (124845645000000000000000000000)) else (box (135101835000000000000000000000) (135108139000000000000000000000))))) else (if n < 334 then (if n < 332 then (box (145476368000000000000000000000) (145482701000000000000000000000)) else (if n < 333 then (box (155958317000000000000000000000) (155964680000000000000000000000)) else (box (166542920000000000000000000000) (166549313000000000000000000000)))) else (if n < 335 then (box (177225318000000000000000000000) (177231741000000000000000000000)) else (if n < 336 then (box (188000552000000000000000000000) (188007005000000000000000000000)) else (box (198863566000000000000000000000) (198870049000000000000000000000)))))))
def cV337_360 (n:Nat):IV:=(if n < 348 then (if n < 342 then (if n < 339 then (if n < 338 then (box (209809206000000000000000000000) (209815719000000000000000000000)) else (box (220832225000000000000000000000) (220838768000000000000000000000))) else (if n < 340 then (box (231927287000000000000000000000) (231933860000000000000000000000)) else (if n < 341 then (box (243088963000000000000000000000) (243095567000000000000000000000)) else (box (254311735000000000000000000000) (254318370000000000000000000000))))) else (if n < 345 then (if n < 343 then (box (265590005000000000000000000000) (265596670000000000000000000000)) else (if n < 344 then (box (276918085000000000000000000000) (276924780000000000000000000000)) else (box (288290208000000000000000000000) (288296934000000000000000000000)))) else (if n < 346 then (box (299700533000000000000000000000) (299707289000000000000000000000)) else (if n < 347 then (box (311143131000000000000000000000) (311149917000000000000000000000)) else (box (322612011000000000000000000000) (322618827000000000000000000000)))))) else (if n < 354 then (if n < 351 then (if n < 349 then (box (334101103000000000000000000000) (334107949000000000000000000000)) else (if n < 350 then (box (345604273000000000000000000000) (345611149000000000000000000000)) else (box (357115315000000000000000000000) (357122221000000000000000000000)))) else (if n < 352 then (box (368627964000000000000000000000) (368634900000000000000000000000)) else (if n < 353 then (box (380135894000000000000000000000) (380142860000000000000000000000)) else (box (391632718000000000000000000000) (391639713000000000000000000000))))) else (if n < 357 then (if n < 355 then (box (403111999000000000000000000000) (403119024000000000000000000000)) else (if n < 356 then (box (414567240000000000000000000000) (414574294000000000000000000000)) else (box (425991903000000000000000000000) (425998987000000000000000000000)))) else (if n < 358 then (box (437379402000000000000000000000) (437386515000000000000000000000)) else (if n < 359 then (box (448723105000000000000000000000) (448730247000000000000000000000)) else (box (460016343000000000000000000000) (460023513000000000000000000000)))))))
def cV315_360 (n:Nat):IV:=(if n < 337 then (cV315_337 n) else (cV337_360 n))
def cV270_360 (n:Nat):IV:=(if n < 315 then (cV270_315 n) else (cV315_360 n))
def cV180_360 (n:Nat):IV:=(if n < 270 then (cV180_270 n) else (cV270_360 n))
def cV0_360 (n:Nat):IV:=(if n < 180 then (cV0_180 n) else (cV180_360 n))
def cV360_382 (n:Nat):IV:=(if n < 371 then (if n < 365 then (if n < 362 then (if n < 361 then (box (471252410000000000000000000000) (471259608000000000000000000000)) else (box (482424567000000000000000000000) (482431793000000000000000000000))) else (if n < 363 then (box (493526046000000000000000000000) (493533300000000000000000000000)) else (if n < 364 then (box (504550050000000000000000000000) (504557331000000000000000000000)) else (box (515489761000000000000000000000) (515497070000000000000000000000))))) else (if n < 368 then (if n < 366 then (box (526338344000000000000000000000) (526345680000000000000000000000)) else (if n < 367 then (box (537088944000000000000000000000) (537096307000000000000000000000)) else (box (547734694000000000000000000000) (547742084000000000000000000000)))) else (if n < 369 then (box (558268724000000000000000000000) (558276140000000000000000000000)) else (if n < 370 then (box (568684150000000000000000000000) (568691592000000000000000000000)) else (box (578974094000000000000000000000) (578981561000000000000000000000)))))) else (if n < 376 then (if n < 373 then (if n < 372 then (box (589131675000000000000000000000) (589139167000000000000000000000)) else (box (599150023000000000000000000000) (599157540000000000000000000000))) else (if n < 374 then (box (609022274000000000000000000000) (609029816000000000000000000000)) else (if n < 375 then (box (618741581000000000000000000000) (618749148000000000000000000000)) else (box (628301114000000000000000000000) (628308705000000000000000000000))))) else (if n < 379 then (if n < 377 then (box (637694064000000000000000000000) (637701678000000000000000000000)) else (if n < 378 then (box (646913645000000000000000000000) (646921282000000000000000000000)) else (box (655953105000000000000000000000) (655960765000000000000000000000)))) else (if n < 380 then (box (664805724000000000000000000000) (664813406000000000000000000000)) else (if n < 381 then (box (673464819000000000000000000000) (673472522000000000000000000000)) else (box (681923747000000000000000000000) (681931471000000000000000000000)))))))
def cV382_405 (n:Nat):IV:=(if n < 393 then (if n < 387 then (if n < 384 then (if n < 383 then (box (690175913000000000000000000000) (690183658000000000000000000000)) else (box (698214770000000000000000000000) (698222535000000000000000000000))) else (if n < 385 then (box (706033826000000000000000000000) (706041611000000000000000000000)) else (if n < 386 then (box (713626645000000000000000000000) (713634449000000000000000000000)) else (box (720986854000000000000000000000) (720994677000000000000000000000))))) else (if n < 390 then (if n < 388 then (box (728108147000000000000000000000) (728115988000000000000000000000)) else (if n < 389 then (box (734984286000000000000000000000) (734992144000000000000000000000)) else (box (741609107000000000000000000000) (741616982000000000000000000000)))) else (if n < 391 then (box (747976526000000000000000000000) (747984418000000000000000000000)) else (if n < 392 then (box (754080540000000000000000000000) (754088448000000000000000000000)) else (box (759915232000000000000000000000) (759923156000000000000000000000)))))) else (if n < 399 then (if n < 396 then (if n < 394 then (box (765474778000000000000000000000) (765482717000000000000000000000)) else (if n < 395 then (box (770753445000000000000000000000) (770761399000000000000000000000)) else (box (775745602000000000000000000000) (775753570000000000000000000000)))) else (if n < 397 then (box (780445718000000000000000000000) (780453699000000000000000000000)) else (if n < 398 then (box (784848370000000000000000000000) (784856364000000000000000000000)) else (box (788948246000000000000000000000) (788956253000000000000000000000))))) else (if n < 402 then (if n < 400 then (box (792740149000000000000000000000) (792748168000000000000000000000)) else (if n < 401 then (box (796218999000000000000000000000) (796227030000000000000000000000)) else (box (799379842000000000000000000000) (799387883000000000000000000000)))) else (if n < 403 then (box (802217847000000000000000000000) (802225898000000000000000000000)) else (if n < 404 then (box (804728315000000000000000000000) (804736375000000000000000000000)) else (box (806906682000000000000000000000) (806914751000000000000000000000)))))))
def cV360_405 (n:Nat):IV:=(if n < 382 then (cV360_382 n) else (cV382_405 n))
def cV405_427 (n:Nat):IV:=(if n < 416 then (if n < 410 then (if n < 407 then (if n < 406 then (box (808748521000000000000000000000) (808756599000000000000000000000)) else (box (810249549000000000000000000000) (810257635000000000000000000000))) else (if n < 408 then (box (811405627000000000000000000000) (811413720000000000000000000000)) else (if n < 409 then (box (812212767000000000000000000000) (812220866000000000000000000000)) else (box (812667132000000000000000000000) (812675237000000000000000000000))))) else (if n < 413 then (if n < 411 then (box (812765044000000000000000000000) (812773154000000000000000000000)) else (if n < 412 then (box (812502983000000000000000000000) (812511099000000000000000000000)) else (box (811877594000000000000000000000) (811885716000000000000000000000)))) else (if n < 414 then (box (810885690000000000000000000000) (810893819000000000000000000000)) else (if n < 415 then (box (809524254000000000000000000000) (809532390000000000000000000000)) else (box (807790443000000000000000000000) (807798588000000000000000000000)))))) else (if n < 421 then (if n < 418 then (if n < 417 then (box (805681592000000000000000000000) (805689746000000000000000000000)) else (box (803195217000000000000000000000) (803203380000000000000000000000))) else (if n < 419 then (box (800329016000000000000000000000) (800337189000000000000000000000)) else (if n < 420 then (box (797080876000000000000000000000) (797089059000000000000000000000)) else (box (793448871000000000000000000000) (793457065000000000000000000000))))) else (if n < 424 then (if n < 422 then (box (789431270000000000000000000000) (789439476000000000000000000000)) else (if n < 423 then (box (785026537000000000000000000000) (785034755000000000000000000000)) else (box (780233335000000000000000000000) (780241566000000000000000000000)))) else (if n < 425 then (box (775050526000000000000000000000) (775058771000000000000000000000)) else (if n < 426 then (box (769477179000000000000000000000) (769485438000000000000000000000)) else (box (763512566000000000000000000000) (763520840000000000000000000000)))))))
def cV427_450 (n:Nat):IV:=(if n < 438 then (if n < 432 then (if n < 429 then (if n < 428 then (box (757156171000000000000000000000) (757164461000000000000000000000)) else (box (750407685000000000000000000000) (750415991000000000000000000000))) else (if n < 430 then (box (743267015000000000000000000000) (743275338000000000000000000000)) else (if n < 431 then (box (735734284000000000000000000000) (735742624000000000000000000000)) else (box (727809832000000000000000000000) (727818189000000000000000000000))))) else (if n < 435 then (if n < 433 then (box (719494216000000000000000000000) (719502591000000000000000000000)) else (if n < 434 then (box (710788217000000000000000000000) (710796611000000000000000000000)) else (box (701692838000000000000000000000) (701701252000000000000000000000)))) else (if n < 436 then (box (692209309000000000000000000000) (692217743000000000000000000000)) else (if n < 437 then (box (682339083000000000000000000000) (682347537000000000000000000000)) else (box (672083844000000000000000000000) (672092319000000000000000000000)))))) else (if n < 444 then (if n < 441 then (if n < 439 then (box (661445502000000000000000000000) (661453999000000000000000000000)) else (if n < 440 then (box (650426198000000000000000000000) (650434717000000000000000000000)) else (box (639028308000000000000000000000) (639036850000000000000000000000)))) else (if n < 442 then (box (627254437000000000000000000000) (627263002000000000000000000000)) else (if n < 443 then (box (615107422000000000000000000000) (615116011000000000000000000000)) else (box (602590340000000000000000000000) (602598953000000000000000000000))))) else (if n < 447 then (if n < 445 then (box (589706496000000000000000000000) (589715133000000000000000000000)) else (if n < 446 then (box (576459434000000000000000000000) (576468096000000000000000000000)) else (box (562852934000000000000000000000) (562861621000000000000000000000)))) else (if n < 448 then (box (548891007000000000000000000000) (548899720000000000000000000000)) else (if n < 449 then (box (534577908000000000000000000000) (534586648000000000000000000000)) else (box (519918120000000000000000000000) (519926886000000000000000000000)))))))
def cV405_450 (n:Nat):IV:=(if n < 427 then (cV405_427 n) else (cV427_450 n))
def cV360_450 (n:Nat):IV:=(if n < 405 then (cV360_405 n) else (cV405_450 n))
def cV450_472 (n:Nat):IV:=(if n < 461 then (if n < 455 then (if n < 452 then (if n < 451 then (box (504916365000000000000000000000) (504925158000000000000000000000)) else (box (489577605000000000000000000000) (489586426000000000000000000000))) else (if n < 453 then (box (473907029000000000000000000000) (473915877000000000000000000000)) else (if n < 454 then (box (457910067000000000000000000000) (457918943000000000000000000000)) else (box (441592377000000000000000000000) (441601282000000000000000000000))))) else (if n < 458 then (if n < 456 then (box (424959860000000000000000000000) (424968794000000000000000000000)) else (if n < 457 then (box (408018638000000000000000000000) (408027601000000000000000000000)) else (box (390775071000000000000000000000) (390784064000000000000000000000)))) else (if n < 459 then (box (373235750000000000000000000000) (373244773000000000000000000000)) else (if n < 460 then (box (355407489000000000000000000000) (355416542000000000000000000000)) else (box (337297334000000000000000000000) (337306418000000000000000000000)))))) else (if n < 466 then (if n < 463 then (if n < 462 then (box (318912551000000000000000000000) (318921666000000000000000000000)) else (box (300260638000000000000000000000) (300269784000000000000000000000))) else (if n < 464 then (box (281349308000000000000000000000) (281358485000000000000000000000)) else (if n < 465 then (box (262186498000000000000000000000) (262195707000000000000000000000)) else (box (242780358000000000000000000000) (242789599000000000000000000000))))) else (if n < 469 then (if n < 467 then (box (223139258000000000000000000000) (223148530000000000000000000000)) else (if n < 468 then (box (203271778000000000000000000000) (203281082000000000000000000000)) else (box (183186709000000000000000000000) (183196045000000000000000000000)))) else (if n < 470 then (box (162893049000000000000000000000) (162902417000000000000000000000)) else (if n < 471 then (box (142399999000000000000000000000) (142409400000000000000000000000)) else (box (121716968000000000000000000000) (121726402000000000000000000000)))))))
def cV472_495 (n:Nat):IV:=(if n < 483 then (if n < 477 then (if n < 474 then (if n < 473 then (box (100853552000000000000000000000) (100863019000000000000000000000)) else (box (79819553000000000000000000000) (79829053000000000000000000000))) else (if n < 475 then (box (58624959000000000000000000000) (58634492000000000000000000000)) else (if n < 476 then (box (37279946000000000000000000000) (37289512000000000000000000000)) else (box (15794875000000000000000000000) (15804474000000000000000000000))))) else (if n < 480 then (if n < 478 then (box (-5819714000000000000000000000) (-5810081000000000000000000000)) else (if n < 479 then (box (-27553102000000000000000000000) (-27543436000000000000000000000)) else (box (-49394403000000000000000000000) (-49384704000000000000000000000)))) else (if n < 481 then (box (-71332557000000000000000000000) (-71322824000000000000000000000)) else (if n < 482 then (box (-93356347000000000000000000000) (-93346581000000000000000000000)) else (box (-115454393000000000000000000000) (-115444594000000000000000000000)))))) else (if n < 489 then (if n < 486 then (if n < 484 then (box (-137615161000000000000000000000) (-137605329000000000000000000000)) else (if n < 485 then (box (-159826972000000000000000000000) (-159817107000000000000000000000)) else (box (-182078001000000000000000000000) (-182068103000000000000000000000)))) else (if n < 487 then (box (-204356279000000000000000000000) (-204346348000000000000000000000)) else (if n < 488 then (box (-226649710000000000000000000000) (-226639746000000000000000000000)) else (box (-248946069000000000000000000000) (-248936072000000000000000000000))))) else (if n < 492 then (if n < 490 then (box (-271233003000000000000000000000) (-271222973000000000000000000000)) else (if n < 491 then (box (-293498045000000000000000000000) (-293487982000000000000000000000)) else (box (-315728618000000000000000000000) (-315718522000000000000000000000)))) else (if n < 493 then (box (-337912036000000000000000000000) (-337901907000000000000000000000)) else (if n < 494 then (box (-360035511000000000000000000000) (-360025350000000000000000000000)) else (box (-382086170000000000000000000000) (-382075977000000000000000000000)))))))
def cV450_495 (n:Nat):IV:=(if n < 472 then (cV450_472 n) else (cV472_495 n))
def cV495_517 (n:Nat):IV:=(if n < 506 then (if n < 500 then (if n < 497 then (if n < 496 then (box (-404051046000000000000000000000) (-404040821000000000000000000000)) else (box (-425917089000000000000000000000) (-425906832000000000000000000000))) else (if n < 498 then (box (-447671181000000000000000000000) (-447660893000000000000000000000)) else (if n < 499 then (box (-469300128000000000000000000000) (-469289808000000000000000000000)) else (box (-490790682000000000000000000000) (-490780331000000000000000000000))))) else (if n < 503 then (if n < 501 then (box (-512129533000000000000000000000) (-512119151000000000000000000000)) else (if n < 502 then (box (-533303328000000000000000000000) (-533292915000000000000000000000)) else (box (-554298668000000000000000000000) (-554288225000000000000000000000)))) else (if n < 504 then (box (-575102127000000000000000000000) (-575091654000000000000000000000)) else (if n < 505 then (box (-595700243000000000000000000000) (-595689741000000000000000000000)) else (box (-616079541000000000000000000000) (-616069010000000000000000000000)))))) else (if n < 511 then (if n < 508 then (if n < 507 then (box (-636226528000000000000000000000) (-636215968000000000000000000000)) else (box (-656127713000000000000000000000) (-656117124000000000000000000000))) else (if n < 509 then (box (-675769597000000000000000000000) (-675758979000000000000000000000)) else (if n < 510 then (box (-695138700000000000000000000000) (-695128054000000000000000000000)) else (box (-714221550000000000000000000000) (-714210877000000000000000000000))))) else (if n < 514 then (if n < 512 then (box (-733004711000000000000000000000) (-732994010000000000000000000000)) else (if n < 513 then (box (-751474770000000000000000000000) (-751464042000000000000000000000)) else (box (-769618357000000000000000000000) (-769607602000000000000000000000)))) else (if n < 515 then (box (-787422152000000000000000000000) (-787411371000000000000000000000)) else (if n < 516 then (box (-804872887000000000000000000000) (-804862080000000000000000000000)) else (box (-821957362000000000000000000000) (-821946530000000000000000000000)))))))
def cV517_540 (n:Nat):IV:=(if n < 528 then (if n < 522 then (if n < 519 then (if n < 518 then (box (-838662445000000000000000000000) (-838651588000000000000000000000)) else (box (-854975088000000000000000000000) (-854964207000000000000000000000))) else (if n < 520 then (box (-870882326000000000000000000000) (-870871421000000000000000000000)) else (if n < 521 then (box (-886371293000000000000000000000) (-886360365000000000000000000000)) else (box (-901429225000000000000000000000) (-901418274000000000000000000000))))) else (if n < 525 then (if n < 523 then (box (-916043473000000000000000000000) (-916032500000000000000000000000)) else (if n < 524 then (box (-930201505000000000000000000000) (-930190510000000000000000000000)) else (box (-943890917000000000000000000000) (-943879900000000000000000000000)))) else (if n < 526 then (box (-957099444000000000000000000000) (-957088405000000000000000000000)) else (if n < 527 then (box (-969814964000000000000000000000) (-969803904000000000000000000000)) else (box (-982025507000000000000000000000) (-982014427000000000000000000000)))))) else (if n < 534 then (if n < 531 then (if n < 529 then (box (-993719267000000000000000000000) (-993708168000000000000000000000)) else (if n < 530 then (box (-1004884605000000000000000000000) (-1004873487000000000000000000000)) else (box (-1015510057000000000000000000000) (-1015498921000000000000000000000)))) else (if n < 532 then (box (-1025584350000000000000000000000) (-1025573195000000000000000000000)) else (if n < 533 then (box (-1035096399000000000000000000000) (-1035085226000000000000000000000)) else (box (-1044035323000000000000000000000) (-1044024133000000000000000000000))))) else (if n < 537 then (if n < 535 then (box (-1052390450000000000000000000000) (-1052379244000000000000000000000)) else (if n < 536 then (box (-1060151326000000000000000000000) (-1060140104000000000000000000000)) else (box (-1067307722000000000000000000000) (-1067296485000000000000000000000)))) else (if n < 538 then (box (-1073849644000000000000000000000) (-1073838392000000000000000000000)) else (if n < 539 then (box (-1079767337000000000000000000000) (-1079756071000000000000000000000)) else (box (-1085051297000000000000000000000) (-1085040017000000000000000000000)))))))
def cV495_540 (n:Nat):IV:=(if n < 517 then (cV495_517 n) else (cV517_540 n))
def cV450_540 (n:Nat):IV:=(if n < 495 then (cV450_495 n) else (cV495_540 n))
def cV360_540 (n:Nat):IV:=(if n < 450 then (cV360_450 n) else (cV450_540 n))
def cV540_562 (n:Nat):IV:=(if n < 551 then (if n < 545 then (if n < 542 then (if n < 541 then (box (-1089692277000000000000000000000) (-1089680983000000000000000000000)) else (box (-1093681293000000000000000000000) (-1093669986000000000000000000000))) else (if n < 543 then (box (-1097009634000000000000000000000) (-1096998315000000000000000000000)) else (if n < 544 then (box (-1099668870000000000000000000000) (-1099657540000000000000000000000)) else (box (-1101650858000000000000000000000) (-1101639517000000000000000000000))))) else (if n < 548 then (if n < 546 then (box (-1102947748000000000000000000000) (-1102936396000000000000000000000)) else (if n < 547 then (box (-1103551994000000000000000000000) (-1103540632000000000000000000000)) else (box (-1103456359000000000000000000000) (-1103444987000000000000000000000)))) else (if n < 549 then (box (-1102653922000000000000000000000) (-1102642540000000000000000000000)) else (if n < 550 then (box (-1101138085000000000000000000000) (-1101126692000000000000000000000)) else (box (-1098902580000000000000000000000) (-1098891176000000000000000000000)))))) else (if n < 556 then (if n < 553 then (if n < 552 then (box (-1095941477000000000000000000000) (-1095930061000000000000000000000)) else (box (-1092249189000000000000000000000) (-1092237760000000000000000000000))) else (if n < 554 then (box (-1087820480000000000000000000000) (-1087809038000000000000000000000)) else (if n < 555 then (box (-1082650469000000000000000000000) (-1082639014000000000000000000000)) else (box (-1076734639000000000000000000000) (-1076723169000000000000000000000))))) else (if n < 559 then (if n < 557 then (box (-1070068842000000000000000000000) (-1070057357000000000000000000000)) else (if n < 558 then (box (-1062649305000000000000000000000) (-1062637805000000000000000000000)) else (box (-1054472636000000000000000000000) (-1054461120000000000000000000000)))) else (if n < 560 then (box (-1045535830000000000000000000000) (-1045524297000000000000000000000)) else (if n < 561 then (box (-1035836274000000000000000000000) (-1035824723000000000000000000000)) else (box (-1025371751000000000000000000000) (-1025360181000000000000000000000)))))))
def cV562_585 (n:Nat):IV:=(if n < 573 then (if n < 567 then (if n < 564 then (if n < 563 then (box (-1014140448000000000000000000000) (-1014128859000000000000000000000)) else (box (-1002140959000000000000000000000) (-1002129351000000000000000000000))) else (if n < 565 then (box (-989372294000000000000000000000) (-989360665000000000000000000000)) else (if n < 566 then (box (-975833875000000000000000000000) (-975822225000000000000000000000)) else (box (-961525549000000000000000000000) (-961513877000000000000000000000))))) else (if n < 570 then (if n < 568 then (box (-946447588000000000000000000000) (-946435894000000000000000000000)) else (if n < 569 then (box (-930600697000000000000000000000) (-930588980000000000000000000000)) else (box (-913986010000000000000000000000) (-913974270000000000000000000000)))) else (if n < 571 then (box (-896605103000000000000000000000) (-896593339000000000000000000000)) else (if n < 572 then (box (-878459992000000000000000000000) (-878448204000000000000000000000)) else (box (-859553137000000000000000000000) (-859541325000000000000000000000)))))) else (if n < 579 then (if n < 576 then (if n < 574 then (box (-839887447000000000000000000000) (-839875610000000000000000000000)) else (if n < 575 then (box (-819466283000000000000000000000) (-819454420000000000000000000000)) else (box (-798293457000000000000000000000) (-798281567000000000000000000000)))) else (if n < 577 then (box (-776373235000000000000000000000) (-776361318000000000000000000000)) else (if n < 578 then (box (-753710346000000000000000000000) (-753698401000000000000000000000)) else (box (-730309974000000000000000000000) (-730298001000000000000000000000))))) else (if n < 582 then (if n < 580 then (box (-706177768000000000000000000000) (-706165767000000000000000000000)) else (if n < 581 then (box (-681319836000000000000000000000) (-681307806000000000000000000000)) else (box (-655742754000000000000000000000) (-655730695000000000000000000000)))) else (if n < 583 then (box (-629453565000000000000000000000) (-629441476000000000000000000000)) else (if n < 584 then (box (-602459774000000000000000000000) (-602447654000000000000000000000)) else (box (-574769352000000000000000000000) (-574757201000000000000000000000)))))))
def cV540_585 (n:Nat):IV:=(if n < 562 then (cV540_562 n) else (cV562_585 n))
def cV585_607 (n:Nat):IV:=(if n < 596 then (if n < 590 then (if n < 587 then (if n < 586 then (box (-546390743000000000000000000000) (-546378560000000000000000000000)) else (box (-517332850000000000000000000000) (-517320636000000000000000000000))) else (if n < 588 then (box (-487605048000000000000000000000) (-487592802000000000000000000000)) else (if n < 589 then (box (-457217174000000000000000000000) (-457204895000000000000000000000)) else (box (-426179538000000000000000000000) (-426167226000000000000000000000))))) else (if n < 593 then (if n < 591 then (box (-394502902000000000000000000000) (-394490557000000000000000000000)) else (if n < 592 then (box (-362198504000000000000000000000) (-362186125000000000000000000000)) else (box (-329278032000000000000000000000) (-329265619000000000000000000000)))) else (if n < 594 then (box (-295753638000000000000000000000) (-295741190000000000000000000000)) else (if n < 595 then (box (-261637936000000000000000000000) (-261625453000000000000000000000)) else (box (-226943988000000000000000000000) (-226931469000000000000000000000)))))) else (if n < 601 then (if n < 598 then (if n < 597 then (box (-191685309000000000000000000000) (-191672754000000000000000000000)) else (box (-155875865000000000000000000000) (-155863275000000000000000000000))) else (if n < 599 then (box (-119530068000000000000000000000) (-119517442000000000000000000000)) else (if n < 600 then (box (-82662770000000000000000000000) (-82650108000000000000000000000)) else (box (-45289267000000000000000000000) (-45276569000000000000000000000))))) else (if n < 604 then (if n < 602 then (box (-7425282000000000000000000000) (-7412547000000000000000000000)) else (if n < 603 then (box (30913027000000000000000000000) (30925799000000000000000000000)) else (box (69709077000000000000000000000) (69721886000000000000000000000)))) else (if n < 605 then (box (108945867000000000000000000000) (108958714000000000000000000000)) else (if n < 606 then (box (148605980000000000000000000000) (148618865000000000000000000000)) else (box (188671586000000000000000000000) (188684508000000000000000000000)))))))
def cV607_630 (n:Nat):IV:=(if n < 618 then (if n < 612 then (if n < 609 then (if n < 608 then (box (229124454000000000000000000000) (229137414000000000000000000000)) else (box (269945958000000000000000000000) (269958956000000000000000000000))) else (if n < 610 then (box (311117074000000000000000000000) (311130111000000000000000000000)) else (if n < 611 then (box (352618399000000000000000000000) (352631474000000000000000000000)) else (box (394430151000000000000000000000) (394443265000000000000000000000))))) else (if n < 615 then (if n < 613 then (box (436532173000000000000000000000) (436545325000000000000000000000)) else (if n < 614 then (box (478903949000000000000000000000) (478917140000000000000000000000)) else (box (521524607000000000000000000000) (521537837000000000000000000000)))) else (if n < 616 then (box (564372928000000000000000000000) (564386197000000000000000000000)) else (if n < 617 then (box (607427354000000000000000000000) (607440662000000000000000000000)) else (box (650665992000000000000000000000) (650679339000000000000000000000)))))) else (if n < 624 then (if n < 621 then (if n < 619 then (box (694066633000000000000000000000) (694080019000000000000000000000)) else (if n < 620 then (box (737606755000000000000000000000) (737620180000000000000000000000)) else (box (781263530000000000000000000000) (781276994000000000000000000000)))) else (if n < 622 then (box (825013837000000000000000000000) (825027340000000000000000000000)) else (if n < 623 then (box (868834272000000000000000000000) (868847815000000000000000000000)) else (box (912701159000000000000000000000) (912714742000000000000000000000))))) else (if n < 627 then (if n < 625 then (box (956590559000000000000000000000) (956604181000000000000000000000)) else (if n < 626 then (box (1000478277000000000000000000000) (1000491938000000000000000000000)) else (box (1044339882000000000000000000000) (1044353582000000000000000000000)))) else (if n < 628 then (box (1088150706000000000000000000000) (1088164444000000000000000000000)) else (if n < 629 then (box (1131885869000000000000000000000) (1131899645000000000000000000000)) else (box (1175520279000000000000000000000) (1175534094000000000000000000000)))))))
def cV585_630 (n:Nat):IV:=(if n < 607 then (cV585_607 n) else (cV607_630 n))
def cV540_630 (n:Nat):IV:=(if n < 585 then (cV540_585 n) else (cV585_630 n))
def cV630_652 (n:Nat):IV:=(if n < 641 then (if n < 635 then (if n < 632 then (if n < 631 then (box (1219028651000000000000000000000) (1219042504000000000000000000000)) else (box (1262385517000000000000000000000) (1262399409000000000000000000000))) else (if n < 633 then (box (1305565234000000000000000000000) (1305579164000000000000000000000)) else (if n < 634 then (box (1348542007000000000000000000000) (1348555975000000000000000000000)) else (box (1391289890000000000000000000000) (1391303896000000000000000000000))))) else (if n < 638 then (if n < 636 then (box (1433782808000000000000000000000) (1433796851000000000000000000000)) else (if n < 637 then (box (1475994565000000000000000000000) (1476008645000000000000000000000)) else (box (1517898857000000000000000000000) (1517912974000000000000000000000)))) else (if n < 639 then (box (1559469290000000000000000000000) (1559483444000000000000000000000)) else (if n < 640 then (box (1600679392000000000000000000000) (1600693582000000000000000000000)) else (box (1641502619000000000000000000000) (1641516845000000000000000000000)))))) else (if n < 646 then (if n < 643 then (if n < 642 then (box (1681912386000000000000000000000) (1681926648000000000000000000000)) else (box (1721882066000000000000000000000) (1721896364000000000000000000000))) else (if n < 644 then (box (1761385008000000000000000000000) (1761399342000000000000000000000)) else (if n < 645 then (box (1800394562000000000000000000000) (1800408932000000000000000000000)) else (box (1838884074000000000000000000000) (1838898479000000000000000000000))))) else (if n < 649 then (if n < 647 then (box (1876826919000000000000000000000) (1876841359000000000000000000000)) else (if n < 648 then (box (1914196511000000000000000000000) (1914210985000000000000000000000)) else (box (1950966309000000000000000000000) (1950980817000000000000000000000)))) else (if n < 650 then (box (1987109846000000000000000000000) (1987124387000000000000000000000)) else (if n < 651 then (box (2022600734000000000000000000000) (2022615308000000000000000000000)) else (box (2057412686000000000000000000000) (2057427293000000000000000000000)))))))
def cV652_675 (n:Nat):IV:=(if n < 663 then (if n < 657 then (if n < 654 then (if n < 653 then (box (2091519527000000000000000000000) (2091534167000000000000000000000)) else (box (2124895213000000000000000000000) (2124909885000000000000000000000))) else (if n < 655 then (box (2157513846000000000000000000000) (2157528550000000000000000000000)) else (if n < 656 then (box (2189349691000000000000000000000) (2189364426000000000000000000000)) else (box (2220377184000000000000000000000) (2220391950000000000000000000000))))) else (if n < 660 then (if n < 658 then (box (2250570962000000000000000000000) (2250585759000000000000000000000)) else (if n < 659 then (box (2279905867000000000000000000000) (2279920694000000000000000000000)) else (box (2308356966000000000000000000000) (2308371823000000000000000000000)))) else (if n < 661 then (box (2335899570000000000000000000000) (2335914457000000000000000000000)) else (if n < 662 then (box (2362509247000000000000000000000) (2362524163000000000000000000000)) else (box (2388161839000000000000000000000) (2388176783000000000000000000000)))))) else (if n < 669 then (if n < 666 then (if n < 664 then (box (2412833478000000000000000000000) (2412848450000000000000000000000)) else (if n < 665 then (box (2436500602000000000000000000000) (2436515602000000000000000000000)) else (box (2459139972000000000000000000000) (2459154999000000000000000000000)))) else (if n < 667 then (box (2480728686000000000000000000000) (2480743740000000000000000000000)) else (if n < 668 then (box (2501244200000000000000000000000) (2501259280000000000000000000000)) else (box (2520664339000000000000000000000) (2520679444000000000000000000000))))) else (if n < 672 then (if n < 670 then (box (2538967314000000000000000000000) (2538982444000000000000000000000)) else (if n < 671 then (box (2556131739000000000000000000000) (2556146894000000000000000000000)) else (box (2572136649000000000000000000000) (2572151828000000000000000000000)))) else (if n < 673 then (box (2586961514000000000000000000000) (2586976716000000000000000000000)) else (if n < 674 then (box (2600586251000000000000000000000) (2600601476000000000000000000000)) else (box (2612991246000000000000000000000) (2613006494000000000000000000000)))))))
def cV630_675 (n:Nat):IV:=(if n < 652 then (cV630_652 n) else (cV652_675 n))
def cV675_698 (n:Nat):IV:=(if n < 686 then (if n < 680 then (if n < 677 then (if n < 676 then (box (2624157367000000000000000000000) (2624172637000000000000000000000)) else (box (2634065977000000000000000000000) (2634081269000000000000000000000))) else (if n < 678 then (box (2642698954000000000000000000000) (2642714267000000000000000000000)) else (if n < 679 then (box (2650038702000000000000000000000) (2650054035000000000000000000000)) else (box (2656068169000000000000000000000) (2656083522000000000000000000000))))) else (if n < 683 then (if n < 681 then (box (2660770862000000000000000000000) (2660786234000000000000000000000)) else (if n < 682 then (box (2664130860000000000000000000000) (2664146251000000000000000000000)) else (box (2666132828000000000000000000000) (2666148237000000000000000000000)))) else (if n < 684 then (box (2666762032000000000000000000000) (2666777459000000000000000000000)) else (if n < 685 then (box (2666004357000000000000000000000) (2666019802000000000000000000000)) else (box (2663846315000000000000000000000) (2663861778000000000000000000000)))))) else (if n < 692 then (if n < 689 then (if n < 687 then (box (2660275063000000000000000000000) (2660290545000000000000000000000)) else (if n < 688 then (box (2655278416000000000000000000000) (2655293918000000000000000000000)) else (box (2648844860000000000000000000000) (2648860383000000000000000000000)))) else (if n < 690 then (box (2640963564000000000000000000000) (2640979108000000000000000000000)) else (if n < 691 then (box (2631624394000000000000000000000) (2631639959000000000000000000000)) else (box (2620817926000000000000000000000) (2620833514000000000000000000000))))) else (if n < 695 then (if n < 693 then (box (2608535457000000000000000000000) (2608551068000000000000000000000)) else (if n < 694 then (box (2594769018000000000000000000000) (2594784653000000000000000000000)) else (box (2579511387000000000000000000000) (2579527047000000000000000000000)))) else (if n < 696 then (box (2562756096000000000000000000000) (2562771782000000000000000000000)) else (if n < 697 then (box (2544497449000000000000000000000) (2544513161000000000000000000000)) else (box (2524730528000000000000000000000) (2524746267000000000000000000000)))))))
def cV698_721 (n:Nat):IV:=(if n < 709 then (if n < 703 then (if n < 700 then (if n < 699 then (box (2503451206000000000000000000000) (2503466973000000000000000000000)) else (box (2480656155000000000000000000000) (2480671950000000000000000000000))) else (if n < 701 then (box (2456342855000000000000000000000) (2456358679000000000000000000000)) else (if n < 702 then (box (2430509608000000000000000000000) (2430525461000000000000000000000)) else (box (2403155545000000000000000000000) (2403171427000000000000000000000))))) else (if n < 706 then (if n < 704 then (box (2374280633000000000000000000000) (2374296545000000000000000000000)) else (if n < 705 then (box (2343885684000000000000000000000) (2343901627000000000000000000000)) else (box (2311972367000000000000000000000) (2311988342000000000000000000000)))) else (if n < 707 then (box (2278543210000000000000000000000) (2278559217000000000000000000000)) else (if n < 708 then (box (2243601610000000000000000000000) (2243617650000000000000000000000)) else (box (2207151843000000000000000000000) (2207167917000000000000000000000)))))) else (if n < 715 then (if n < 712 then (if n < 710 then (box (2169199063000000000000000000000) (2169215171000000000000000000000)) else (if n < 711 then (box (2129749314000000000000000000000) (2129765457000000000000000000000)) else (box (2088809533000000000000000000000) (2088825712000000000000000000000)))) else (if n < 713 then (box (2046387556000000000000000000000) (2046403771000000000000000000000)) else (if n < 714 then (box (2002492122000000000000000000000) (2002508373000000000000000000000)) else (box (1957132879000000000000000000000) (1957149167000000000000000000000))))) else (if n < 718 then (if n < 716 then (box (1910320384000000000000000000000) (1910336710000000000000000000000)) else (if n < 717 then (box (1862066113000000000000000000000) (1862082477000000000000000000000)) else (box (1812382453000000000000000000000) (1812398855000000000000000000000)))) else (if n < 719 then (box (1761282718000000000000000000000) (1761299159000000000000000000000)) else (if n < 720 then (box (1708781139000000000000000000000) (1708797620000000000000000000000)) else (box (1654892870000000000000000000000) (1654909391000000000000000000000)))))))
def cV675_721 (n:Nat):IV:=(if n < 698 then (cV675_698 n) else (cV698_721 n))
def cV630_721 (n:Nat):IV:=(if n < 675 then (cV630_675 n) else (cV675_721 n))
def cV540_721 (n:Nat):IV:=(if n < 630 then (cV540_630 n) else (cV630_721 n))
def cV360_721 (n:Nat):IV:=(if n < 540 then (cV360_540 n) else (cV540_721 n))
def cV0_721 (n:Nat):IV:=(if n < 360 then (cV0_360 n) else (cV360_721 n))
def cM0_22 (n:Nat):IV:=(if n < 11 then (if n < 5 then (if n < 2 then (if n < 1 then (box (0) (0)) else (box (121624000000000000000000000) (121626000000000000000000000))) else (if n < 3 then (box (243214000000000000000000000) (243218000000000000000000000)) else (if n < 4 then (box (364735000000000000000000000) (364741000000000000000000000)) else (box (486152000000000000000000000) (486160000000000000000000000))))) else (if n < 8 then (if n < 6 then (box (607432000000000000000000000) (607442000000000000000000000)) else (if n < 7 then (box (728540000000000000000000000) (728552000000000000000000000)) else (box (849442000000000000000000000) (849456000000000000000000000)))) else (if n < 9 then (box (970103000000000000000000000) (970119000000000000000000000)) else (if n < 10 then (box (1090490000000000000000000000) (1090508000000000000000000000)) else (box (1210569000000000000000000000) (1210589000000000000000000000)))))) else (if n < 16 then (if n < 13 then (if n < 12 then (box (1330306000000000000000000000) (1330328000000000000000000000)) else (box (1449667000000000000000000000) (1449691000000000000000000000))) else (if n < 14 then (box (1568619000000000000000000000) (1568645000000000000000000000)) else (if n < 15 then (box (1687129000000000000000000000) (1687157000000000000000000000)) else (box (1805164000000000000000000000) (1805194000000000000000000000))))) else (if n < 19 then (if n < 17 then (box (1922690000000000000000000000) (1922722000000000000000000000)) else (if n < 18 then (box (2039676000000000000000000000) (2039710000000000000000000000)) else (box (2156089000000000000000000000) (2156125000000000000000000000)))) else (if n < 20 then (box (2271897000000000000000000000) (2271935000000000000000000000)) else (if n < 21 then (box (2387068000000000000000000000) (2387108000000000000000000000)) else (box (2501570000000000000000000000) (2501612000000000000000000000)))))))
def cM22_45 (n:Nat):IV:=(if n < 33 then (if n < 27 then (if n < 24 then (if n < 23 then (box (2615373000000000000000000000) (2615417000000000000000000000)) else (box (2728446000000000000000000000) (2728492000000000000000000000))) else (if n < 25 then (box (2840758000000000000000000000) (2840806000000000000000000000)) else (if n < 26 then (box (2952279000000000000000000000) (2952329000000000000000000000)) else (box (3062979000000000000000000000) (3063031000000000000000000000))))) else (if n < 30 then (if n < 28 then (box (3172829000000000000000000000) (3172883000000000000000000000)) else (if n < 29 then (box (3281800000000000000000000000) (3281856000000000000000000000)) else (box (3389864000000000000000000000) (3389922000000000000000000000)))) else (if n < 31 then (box (3496992000000000000000000000) (3497052000000000000000000000)) else (if n < 32 then (box (3603157000000000000000000000) (3603219000000000000000000000)) else (box (3708332000000000000000000000) (3708396000000000000000000000)))))) else (if n < 39 then (if n < 36 then (if n < 34 then (box (3812490000000000000000000000) (3812556000000000000000000000)) else (if n < 35 then (box (3915606000000000000000000000) (3915673000000000000000000000)) else (box (4017653000000000000000000000) (4017722000000000000000000000)))) else (if n < 37 then (box (4118607000000000000000000000) (4118677000000000000000000000)) else (if n < 38 then (box (4218443000000000000000000000) (4218515000000000000000000000)) else (box (4317137000000000000000000000) (4317211000000000000000000000))))) else (if n < 42 then (if n < 40 then (box (4414666000000000000000000000) (4414742000000000000000000000)) else (if n < 41 then (box (4511007000000000000000000000) (4511085000000000000000000000)) else (box (4606138000000000000000000000) (4606218000000000000000000000)))) else (if n < 43 then (box (4700038000000000000000000000) (4700120000000000000000000000)) else (if n < 44 then (box (4792686000000000000000000000) (4792770000000000000000000000)) else (box (4884062000000000000000000000) (4884148000000000000000000000)))))))
def cM0_45 (n:Nat):IV:=(if n < 22 then (cM0_22 n) else (cM22_45 n))
def cM45_67 (n:Nat):IV:=(if n < 56 then (if n < 50 then (if n < 47 then (if n < 46 then (box (4974147000000000000000000000) (4974235000000000000000000000)) else (box (5062922000000000000000000000) (5063012000000000000000000000))) else (if n < 48 then (box (5150369000000000000000000000) (5150461000000000000000000000)) else (if n < 49 then (box (5236471000000000000000000000) (5236565000000000000000000000)) else (box (5321212000000000000000000000) (5321307000000000000000000000))))) else (if n < 53 then (if n < 51 then (box (5404576000000000000000000000) (5404672000000000000000000000)) else (if n < 52 then (box (5486548000000000000000000000) (5486645000000000000000000000)) else (box (5567113000000000000000000000) (5567212000000000000000000000)))) else (if n < 54 then (box (5646259000000000000000000000) (5646360000000000000000000000)) else (if n < 55 then (box (5723973000000000000000000000) (5724076000000000000000000000)) else (box (5800244000000000000000000000) (5800348000000000000000000000)))))) else (if n < 61 then (if n < 58 then (if n < 57 then (box (5875061000000000000000000000) (5875166000000000000000000000)) else (box (5948414000000000000000000000) (5948520000000000000000000000))) else (if n < 59 then (box (6020293000000000000000000000) (6020401000000000000000000000)) else (if n < 60 then (box (6090691000000000000000000000) (6090801000000000000000000000)) else (box (6159601000000000000000000000) (6159712000000000000000000000))))) else (if n < 64 then (if n < 62 then (box (6227016000000000000000000000) (6227128000000000000000000000)) else (if n < 63 then (box (6292931000000000000000000000) (6293044000000000000000000000)) else (box (6357341000000000000000000000) (6357456000000000000000000000)))) else (if n < 65 then (box (6420243000000000000000000000) (6420359000000000000000000000)) else (if n < 66 then (box (6481634000000000000000000000) (6481752000000000000000000000)) else (box (6541513000000000000000000000) (6541632000000000000000000000)))))))
def cM67_90 (n:Nat):IV:=(if n < 78 then (if n < 72 then (if n < 69 then (if n < 68 then (box (6599878000000000000000000000) (6599999000000000000000000000)) else (box (6656731000000000000000000000) (6656853000000000000000000000))) else (if n < 70 then (box (6712072000000000000000000000) (6712196000000000000000000000)) else (if n < 71 then (box (6765904000000000000000000000) (6766029000000000000000000000)) else (box (6818230000000000000000000000) (6818356000000000000000000000))))) else (if n < 75 then (if n < 73 then (box (6869054000000000000000000000) (6869181000000000000000000000)) else (if n < 74 then (box (6918381000000000000000000000) (6918510000000000000000000000)) else (box (6966218000000000000000000000) (6966348000000000000000000000)))) else (if n < 76 then (box (7012571000000000000000000000) (7012703000000000000000000000)) else (if n < 77 then (box (7057449000000000000000000000) (7057582000000000000000000000)) else (box (7100861000000000000000000000) (7100995000000000000000000000)))))) else (if n < 84 then (if n < 81 then (if n < 79 then (box (7142817000000000000000000000) (7142952000000000000000000000)) else (if n < 80 then (box (7183328000000000000000000000) (7183464000000000000000000000)) else (box (7222406000000000000000000000) (7222543000000000000000000000)))) else (if n < 82 then (box (7260064000000000000000000000) (7260203000000000000000000000)) else (if n < 83 then (box (7296316000000000000000000000) (7296457000000000000000000000)) else (box (7331178000000000000000000000) (7331320000000000000000000000))))) else (if n < 87 then (if n < 85 then (box (7364665000000000000000000000) (7364808000000000000000000000)) else (if n < 86 then (box (7396794000000000000000000000) (7396938000000000000000000000)) else (box (7427582000000000000000000000) (7427727000000000000000000000)))) else (if n < 88 then (box (7457049000000000000000000000) (7457195000000000000000000000)) else (if n < 89 then (box (7485214000000000000000000000) (7485361000000000000000000000)) else (box (7512097000000000000000000000) (7512245000000000000000000000)))))))
def cM45_90 (n:Nat):IV:=(if n < 67 then (cM45_67 n) else (cM67_90 n))
def cM0_90 (n:Nat):IV:=(if n < 45 then (cM0_45 n) else (cM45_90 n))
def cM90_112 (n:Nat):IV:=(if n < 101 then (if n < 95 then (if n < 92 then (if n < 91 then (box (7537720000000000000000000000) (7537869000000000000000000000)) else (box (7562105000000000000000000000) (7562255000000000000000000000))) else (if n < 93 then (box (7585275000000000000000000000) (7585426000000000000000000000)) else (if n < 94 then (box (7607254000000000000000000000) (7607406000000000000000000000)) else (box (7628066000000000000000000000) (7628220000000000000000000000))))) else (if n < 98 then (if n < 96 then (box (7647738000000000000000000000) (7647893000000000000000000000)) else (if n < 97 then (box (7666295000000000000000000000) (7666451000000000000000000000)) else (box (7683764000000000000000000000) (7683922000000000000000000000)))) else (if n < 99 then (box (7700174000000000000000000000) (7700333000000000000000000000)) else (if n < 100 then (box (7715552000000000000000000000) (7715712000000000000000000000)) else (box (7729928000000000000000000000) (7730089000000000000000000000)))))) else (if n < 106 then (if n < 103 then (if n < 102 then (box (7743331000000000000000000000) (7743493000000000000000000000)) else (box (7755792000000000000000000000) (7755955000000000000000000000))) else (if n < 104 then (box (7767342000000000000000000000) (7767506000000000000000000000)) else (if n < 105 then (box (7778012000000000000000000000) (7778177000000000000000000000)) else (box (7787835000000000000000000000) (7788001000000000000000000000))))) else (if n < 109 then (if n < 107 then (box (7796843000000000000000000000) (7797010000000000000000000000)) else (if n < 108 then (box (7805069000000000000000000000) (7805237000000000000000000000)) else (box (7812547000000000000000000000) (7812716000000000000000000000)))) else (if n < 110 then (box (7819310000000000000000000000) (7819480000000000000000000000)) else (if n < 111 then (box (7825393000000000000000000000) (7825565000000000000000000000)) else (box (7830831000000000000000000000) (7831005000000000000000000000)))))))
def cM112_135 (n:Nat):IV:=(if n < 123 then (if n < 117 then (if n < 114 then (if n < 113 then (box (7835660000000000000000000000) (7835835000000000000000000000)) else (box (7839914000000000000000000000) (7840090000000000000000000000))) else (if n < 115 then (box (7843629000000000000000000000) (7843806000000000000000000000)) else (if n < 116 then (box (7846841000000000000000000000) (7847019000000000000000000000)) else (box (7849587000000000000000000000) (7849766000000000000000000000))))) else (if n < 120 then (if n < 118 then (box (7851902000000000000000000000) (7852082000000000000000000000)) else (if n < 119 then (box (7853824000000000000000000000) (7854005000000000000000000000)) else (box (7855389000000000000000000000) (7855571000000000000000000000)))) else (if n < 121 then (box (7856633000000000000000000000) (7856816000000000000000000000)) else (if n < 122 then (box (7857594000000000000000000000) (7857778000000000000000000000)) else (box (7858308000000000000000000000) (7858493000000000000000000000)))))) else (if n < 129 then (if n < 126 then (if n < 124 then (box (7858812000000000000000000000) (7858998000000000000000000000)) else (if n < 125 then (box (7859143000000000000000000000) (7859330000000000000000000000)) else (box (7859337000000000000000000000) (7859525000000000000000000000)))) else (if n < 127 then (box (7859432000000000000000000000) (7859621000000000000000000000)) else (if n < 128 then (box (7859464000000000000000000000) (7859654000000000000000000000)) else (box (7859469000000000000000000000) (7859660000000000000000000000))))) else (if n < 132 then (if n < 130 then (box (7859484000000000000000000000) (7859676000000000000000000000)) else (if n < 131 then (box (7859544000000000000000000000) (7859737000000000000000000000)) else (box (7859686000000000000000000000) (7859880000000000000000000000)))) else (if n < 133 then (box (7859945000000000000000000000) (7860140000000000000000000000)) else (if n < 134 then (box (7860357000000000000000000000) (7860553000000000000000000000)) else (box (7860957000000000000000000000) (7861154000000000000000000000)))))))
def cM90_135 (n:Nat):IV:=(if n < 112 then (cM90_112 n) else (cM112_135 n))
def cM135_157 (n:Nat):IV:=(if n < 146 then (if n < 140 then (if n < 137 then (if n < 136 then (box (7861779000000000000000000000) (7861977000000000000000000000)) else (box (7862858000000000000000000000) (7863057000000000000000000000))) else (if n < 138 then (box (7864229000000000000000000000) (7864429000000000000000000000)) else (if n < 139 then (box (7865925000000000000000000000) (7866126000000000000000000000)) else (box (7867979000000000000000000000) (7868181000000000000000000000))))) else (if n < 143 then (if n < 141 then (box (7870425000000000000000000000) (7870628000000000000000000000)) else (if n < 142 then (box (7873295000000000000000000000) (7873499000000000000000000000)) else (box (7876621000000000000000000000) (7876826000000000000000000000)))) else (if n < 144 then (box (7880435000000000000000000000) (7880641000000000000000000000)) else (if n < 145 then (box (7884769000000000000000000000) (7884976000000000000000000000)) else (box (7889653000000000000000000000) (7889861000000000000000000000)))))) else (if n < 151 then (if n < 148 then (if n < 147 then (box (7895118000000000000000000000) (7895327000000000000000000000)) else (box (7901194000000000000000000000) (7901404000000000000000000000))) else (if n < 149 then (box (7907910000000000000000000000) (7908121000000000000000000000)) else (if n < 150 then (box (7915295000000000000000000000) (7915507000000000000000000000)) else (box (7923378000000000000000000000) (7923591000000000000000000000))))) else (if n < 154 then (if n < 152 then (box (7932186000000000000000000000) (7932400000000000000000000000)) else (if n < 153 then (box (7941748000000000000000000000) (7941963000000000000000000000)) else (box (7952090000000000000000000000) (7952306000000000000000000000)))) else (if n < 155 then (box (7963238000000000000000000000) (7963455000000000000000000000)) else (if n < 156 then (box (7975219000000000000000000000) (7975437000000000000000000000)) else (box (7988058000000000000000000000) (7988277000000000000000000000)))))))
def cM157_180 (n:Nat):IV:=(if n < 168 then (if n < 162 then (if n < 159 then (if n < 158 then (box (8001780000000000000000000000) (8002000000000000000000000000)) else (box (8016410000000000000000000000) (8016631000000000000000000000))) else (if n < 160 then (box (8031971000000000000000000000) (8032193000000000000000000000)) else (if n < 161 then (box (8048487000000000000000000000) (8048710000000000000000000000)) else (box (8065981000000000000000000000) (8066205000000000000000000000))))) else (if n < 165 then (if n < 163 then (box (8084475000000000000000000000) (8084701000000000000000000000)) else (if n < 164 then (box (8103992000000000000000000000) (8104219000000000000000000000)) else (box (8124553000000000000000000000) (8124781000000000000000000000)))) else (if n < 166 then (box (8146179000000000000000000000) (8146408000000000000000000000)) else (if n < 167 then (box (8168890000000000000000000000) (8169120000000000000000000000)) else (box (8192707000000000000000000000) (8192938000000000000000000000)))))) else (if n < 174 then (if n < 171 then (if n < 169 then (box (8217649000000000000000000000) (8217881000000000000000000000)) else (if n < 170 then (box (8243735000000000000000000000) (8243968000000000000000000000)) else (box (8270984000000000000000000000) (8271218000000000000000000000)))) else (if n < 172 then (box (8299415000000000000000000000) (8299650000000000000000000000)) else (if n < 173 then (box (8329045000000000000000000000) (8329281000000000000000000000)) else (box (8359892000000000000000000000) (8360129000000000000000000000))))) else (if n < 177 then (if n < 175 then (box (8391973000000000000000000000) (8392211000000000000000000000)) else (if n < 176 then (box (8425304000000000000000000000) (8425544000000000000000000000)) else (box (8459902000000000000000000000) (8460143000000000000000000000)))) else (if n < 178 then (box (8495783000000000000000000000) (8496025000000000000000000000)) else (if n < 179 then (box (8532962000000000000000000000) (8533206000000000000000000000)) else (box (8571455000000000000000000000) (8571700000000000000000000000)))))))
def cM135_180 (n:Nat):IV:=(if n < 157 then (cM135_157 n) else (cM157_180 n))
def cM90_180 (n:Nat):IV:=(if n < 135 then (cM90_135 n) else (cM135_180 n))
def cM0_180 (n:Nat):IV:=(if n < 90 then (cM0_90 n) else (cM90_180 n))
def cM180_202 (n:Nat):IV:=(if n < 191 then (if n < 185 then (if n < 182 then (if n < 181 then (box (8611276000000000000000000000) (8611523000000000000000000000)) else (box (8652440000000000000000000000) (8652688000000000000000000000))) else (if n < 183 then (box (8694961000000000000000000000) (8695211000000000000000000000)) else (if n < 184 then (box (8738853000000000000000000000) (8739104000000000000000000000)) else (box (8784130000000000000000000000) (8784382000000000000000000000))))) else (if n < 188 then (if n < 186 then (box (8830804000000000000000000000) (8831058000000000000000000000)) else (if n < 187 then (box (8878889000000000000000000000) (8879144000000000000000000000)) else (box (8928397000000000000000000000) (8928653000000000000000000000)))) else (if n < 189 then (box (8979341000000000000000000000) (8979598000000000000000000000)) else (if n < 190 then (box (9031733000000000000000000000) (9031991000000000000000000000)) else (box (9085584000000000000000000000) (9085844000000000000000000000)))))) else (if n < 196 then (if n < 193 then (if n < 192 then (box (9140907000000000000000000000) (9141168000000000000000000000)) else (box (9197712000000000000000000000) (9197975000000000000000000000))) else (if n < 194 then (box (9256011000000000000000000000) (9256275000000000000000000000)) else (if n < 195 then (box (9315815000000000000000000000) (9316080000000000000000000000)) else (box (9377134000000000000000000000) (9377401000000000000000000000))))) else (if n < 199 then (if n < 197 then (box (9439979000000000000000000000) (9440248000000000000000000000)) else (if n < 198 then (box (9504361000000000000000000000) (9504631000000000000000000000)) else (box (9570289000000000000000000000) (9570560000000000000000000000)))) else (if n < 200 then (box (9637773000000000000000000000) (9638046000000000000000000000)) else (if n < 201 then (box (9706824000000000000000000000) (9707098000000000000000000000)) else (box (9777450000000000000000000000) (9777726000000000000000000000)))))))
def cM202_225 (n:Nat):IV:=(if n < 213 then (if n < 207 then (if n < 204 then (if n < 203 then (box (9849661000000000000000000000) (9849939000000000000000000000)) else (box (9923467000000000000000000000) (9923746000000000000000000000))) else (if n < 205 then (box (9998876000000000000000000000) (9999157000000000000000000000)) else (if n < 206 then (box (10075898000000000000000000000) (10076180000000000000000000000)) else (box (10154541000000000000000000000) (10154825000000000000000000000))))) else (if n < 210 then (if n < 208 then (box (10234814000000000000000000000) (10235100000000000000000000000)) else (if n < 209 then (box (10316726000000000000000000000) (10317014000000000000000000000)) else (box (10400285000000000000000000000) (10400575000000000000000000000)))) else (if n < 211 then (box (10485500000000000000000000000) (10485791000000000000000000000)) else (if n < 212 then (box (10572378000000000000000000000) (10572671000000000000000000000)) else (box (10660928000000000000000000000) (10661223000000000000000000000)))))) else (if n < 219 then (if n < 216 then (if n < 214 then (box (10751158000000000000000000000) (10751455000000000000000000000)) else (if n < 215 then (box (10843076000000000000000000000) (10843375000000000000000000000)) else (box (10936690000000000000000000000) (10936990000000000000000000000)))) else (if n < 217 then (box (11032007000000000000000000000) (11032309000000000000000000000)) else (if n < 218 then (box (11129035000000000000000000000) (11129339000000000000000000000)) else (box (11227782000000000000000000000) (11228088000000000000000000000))))) else (if n < 222 then (if n < 220 then (box (11328255000000000000000000000) (11328563000000000000000000000)) else (if n < 221 then (box (11430462000000000000000000000) (11430771000000000000000000000)) else (box (11534410000000000000000000000) (11534720000000000000000000000)))) else (if n < 223 then (box (11640106000000000000000000000) (11640418000000000000000000000)) else (if n < 224 then (box (11747557000000000000000000000) (11747871000000000000000000000)) else (box (11856771000000000000000000000) (11857087000000000000000000000)))))))
def cM180_225 (n:Nat):IV:=(if n < 202 then (cM180_202 n) else (cM202_225 n))
def cM225_247 (n:Nat):IV:=(if n < 236 then (if n < 230 then (if n < 227 then (if n < 226 then (box (11967755000000000000000000000) (11968073000000000000000000000)) else (box (12080516000000000000000000000) (12080836000000000000000000000))) else (if n < 228 then (box (12195061000000000000000000000) (12195382000000000000000000000)) else (if n < 229 then (box (12311397000000000000000000000) (12311719000000000000000000000)) else (box (12429531000000000000000000000) (12429854000000000000000000000))))) else (if n < 233 then (if n < 231 then (box (12549469000000000000000000000) (12549794000000000000000000000)) else (if n < 232 then (box (12671219000000000000000000000) (12671545000000000000000000000)) else (box (12794787000000000000000000000) (12795115000000000000000000000)))) else (if n < 234 then (box (12920180000000000000000000000) (12920510000000000000000000000)) else (if n < 235 then (box (13047405000000000000000000000) (13047737000000000000000000000)) else (box (13176469000000000000000000000) (13176802000000000000000000000)))))) else (if n < 241 then (if n < 238 then (if n < 237 then (box (13307378000000000000000000000) (13307713000000000000000000000)) else (box (13440139000000000000000000000) (13440476000000000000000000000))) else (if n < 239 then (box (13574759000000000000000000000) (13575097000000000000000000000)) else (if n < 240 then (box (13711244000000000000000000000) (13711583000000000000000000000)) else (box (13849601000000000000000000000) (13849941000000000000000000000))))) else (if n < 244 then (if n < 242 then (box (13989836000000000000000000000) (13990178000000000000000000000)) else (if n < 243 then (box (14131956000000000000000000000) (14132300000000000000000000000)) else (box (14275967000000000000000000000) (14276313000000000000000000000)))) else (if n < 245 then (box (14421876000000000000000000000) (14422224000000000000000000000)) else (if n < 246 then (box (14569690000000000000000000000) (14570040000000000000000000000)) else (box (14719415000000000000000000000) (14719767000000000000000000000)))))))
def cM247_270 (n:Nat):IV:=(if n < 258 then (if n < 252 then (if n < 249 then (if n < 248 then (box (14871057000000000000000000000) (14871411000000000000000000000)) else (box (15024623000000000000000000000) (15024979000000000000000000000))) else (if n < 250 then (box (15180120000000000000000000000) (15180478000000000000000000000)) else (if n < 251 then (box (15337554000000000000000000000) (15337914000000000000000000000)) else (box (15496931000000000000000000000) (15497293000000000000000000000))))) else (if n < 255 then (if n < 253 then (box (15658258000000000000000000000) (15658622000000000000000000000)) else (if n < 254 then (box (15821542000000000000000000000) (15821908000000000000000000000)) else (box (15986789000000000000000000000) (15987157000000000000000000000)))) else (if n < 256 then (box (16154005000000000000000000000) (16154375000000000000000000000)) else (if n < 257 then (box (16323197000000000000000000000) (16323569000000000000000000000)) else (box (16494372000000000000000000000) (16494746000000000000000000000)))))) else (if n < 264 then (if n < 261 then (if n < 259 then (box (16667536000000000000000000000) (16667912000000000000000000000)) else (if n < 260 then (box (16842695000000000000000000000) (16843073000000000000000000000)) else (box (17019856000000000000000000000) (17020236000000000000000000000)))) else (if n < 262 then (box (17199026000000000000000000000) (17199408000000000000000000000)) else (if n < 263 then (box (17380211000000000000000000000) (17380595000000000000000000000)) else (box (17563418000000000000000000000) (17563804000000000000000000000))))) else (if n < 267 then (if n < 265 then (box (17748653000000000000000000000) (17749041000000000000000000000)) else (if n < 266 then (box (17935923000000000000000000000) (17936313000000000000000000000)) else (box (18125234000000000000000000000) (18125626000000000000000000000)))) else (if n < 268 then (box (18316593000000000000000000000) (18316987000000000000000000000)) else (if n < 269 then (box (18510007000000000000000000000) (18510403000000000000000000000)) else (box (18705482000000000000000000000) (18705880000000000000000000000)))))))
def cM225_270 (n:Nat):IV:=(if n < 247 then (cM225_247 n) else (cM247_270 n))
def cM180_270 (n:Nat):IV:=(if n < 225 then (cM180_225 n) else (cM225_270 n))
def cM270_292 (n:Nat):IV:=(if n < 281 then (if n < 275 then (if n < 272 then (if n < 271 then (box (18903025000000000000000000000) (18903425000000000000000000000)) else (box (19102643000000000000000000000) (19103045000000000000000000000))) else (if n < 273 then (box (19304342000000000000000000000) (19304746000000000000000000000)) else (if n < 274 then (box (19508130000000000000000000000) (19508536000000000000000000000)) else (box (19714013000000000000000000000) (19714421000000000000000000000))))) else (if n < 278 then (if n < 276 then (box (19921997000000000000000000000) (19922407000000000000000000000)) else (if n < 277 then (box (20132090000000000000000000000) (20132502000000000000000000000)) else (box (20344298000000000000000000000) (20344712000000000000000000000)))) else (if n < 279 then (box (20558629000000000000000000000) (20559045000000000000000000000)) else (if n < 280 then (box (20775089000000000000000000000) (20775507000000000000000000000)) else (box (20993685000000000000000000000) (20994105000000000000000000000)))))) else (if n < 286 then (if n < 283 then (if n < 282 then (box (21214424000000000000000000000) (21214846000000000000000000000)) else (box (21437313000000000000000000000) (21437737000000000000000000000))) else (if n < 284 then (box (21662359000000000000000000000) (21662785000000000000000000000)) else (if n < 285 then (box (21889569000000000000000000000) (21889997000000000000000000000)) else (box (22118950000000000000000000000) (22119380000000000000000000000))))) else (if n < 289 then (if n < 287 then (box (22350509000000000000000000000) (22350941000000000000000000000)) else (if n < 288 then (box (22584253000000000000000000000) (22584687000000000000000000000)) else (box (22820189000000000000000000000) (22820625000000000000000000000)))) else (if n < 290 then (box (23058325000000000000000000000) (23058763000000000000000000000)) else (if n < 291 then (box (23298668000000000000000000000) (23299108000000000000000000000)) else (box (23541225000000000000000000000) (23541667000000000000000000000)))))))
def cM292_315 (n:Nat):IV:=(if n < 303 then (if n < 297 then (if n < 294 then (if n < 293 then (box (23786003000000000000000000000) (23786447000000000000000000000)) else (box (24033010000000000000000000000) (24033456000000000000000000000))) else (if n < 295 then (box (24282253000000000000000000000) (24282701000000000000000000000)) else (if n < 296 then (box (24533739000000000000000000000) (24534190000000000000000000000)) else (box (24787476000000000000000000000) (24787930000000000000000000000))))) else (if n < 300 then (if n < 298 then (box (25043472000000000000000000000) (25043928000000000000000000000)) else (if n < 299 then (box (25301734000000000000000000000) (25302192000000000000000000000)) else (box (25562269000000000000000000000) (25562729000000000000000000000)))) else (if n < 301 then (box (25825085000000000000000000000) (25825547000000000000000000000)) else (if n < 302 then (box (26090190000000000000000000000) (26090654000000000000000000000)) else (box (26357591000000000000000000000) (26358057000000000000000000000)))))) else (if n < 309 then (if n < 306 then (if n < 304 then (box (26627296000000000000000000000) (26627765000000000000000000000)) else (if n < 305 then (box (26899313000000000000000000000) (26899784000000000000000000000)) else (box (27173650000000000000000000000) (27174123000000000000000000000)))) else (if n < 307 then (box (27450314000000000000000000000) (27450790000000000000000000000)) else (if n < 308 then (box (27729314000000000000000000000) (27729792000000000000000000000)) else (box (28010657000000000000000000000) (28011137000000000000000000000))))) else (if n < 312 then (if n < 310 then (box (28294351000000000000000000000) (28294834000000000000000000000)) else (if n < 311 then (box (28580405000000000000000000000) (28580890000000000000000000000)) else (box (28868826000000000000000000000) (28869313000000000000000000000)))) else (if n < 313 then (box (29159623000000000000000000000) (29160112000000000000000000000)) else (if n < 314 then (box (29452803000000000000000000000) (29453294000000000000000000000)) else (box (29748375000000000000000000000) (29748868000000000000000000000)))))))
def cM270_315 (n:Nat):IV:=(if n < 292 then (cM270_292 n) else (cM292_315 n))
def cM315_337 (n:Nat):IV:=(if n < 326 then (if n < 320 then (if n < 317 then (if n < 316 then (box (30046347000000000000000000000) (30046842000000000000000000000)) else (box (30346727000000000000000000000) (30347225000000000000000000000))) else (if n < 318 then (box (30649524000000000000000000000) (30650024000000000000000000000)) else (if n < 319 then (box (30954746000000000000000000000) (30955248000000000000000000000)) else (box (31262402000000000000000000000) (31262906000000000000000000000))))) else (if n < 323 then (if n < 321 then (box (31572500000000000000000000000) (31573006000000000000000000000)) else (if n < 322 then (box (31885048000000000000000000000) (31885557000000000000000000000)) else (box (32200056000000000000000000000) (32200567000000000000000000000)))) else (if n < 324 then (box (32517531000000000000000000000) (32518045000000000000000000000)) else (if n < 325 then (box (32837483000000000000000000000) (32837999000000000000000000000)) else (box (33159920000000000000000000000) (33160438000000000000000000000)))))) else (if n < 331 then (if n < 328 then (if n < 327 then (box (33484851000000000000000000000) (33485371000000000000000000000)) else (box (33812285000000000000000000000) (33812807000000000000000000000))) else (if n < 329 then (box (34142231000000000000000000000) (34142755000000000000000000000)) else (if n < 330 then (box (34474697000000000000000000000) (34475224000000000000000000000)) else (box (34809693000000000000000000000) (34810222000000000000000000000))))) else (if n < 334 then (if n < 332 then (box (35147228000000000000000000000) (35147759000000000000000000000)) else (if n < 333 then (box (35487311000000000000000000000) (35487844000000000000000000000)) else (box (35829951000000000000000000000) (35830486000000000000000000000)))) else (if n < 335 then (box (36175157000000000000000000000) (36175694000000000000000000000)) else (if n < 336 then (box (36522939000000000000000000000) (36523478000000000000000000000)) else (box (36873305000000000000000000000) (36873847000000000000000000000)))))))
def cM337_360 (n:Nat):IV:=(if n < 348 then (if n < 342 then (if n < 339 then (if n < 338 then (box (37226266000000000000000000000) (37226810000000000000000000000)) else (box (37581830000000000000000000000) (37582377000000000000000000000))) else (if n < 340 then (box (37940007000000000000000000000) (37940557000000000000000000000)) else (if n < 341 then (box (38300807000000000000000000000) (38301360000000000000000000000)) else (box (38664239000000000000000000000) (38664795000000000000000000000))))) else (if n < 345 then (if n < 343 then (box (39030313000000000000000000000) (39030872000000000000000000000)) else (if n < 344 then (box (39399039000000000000000000000) (39399601000000000000000000000)) else (box (39770427000000000000000000000) (39770991000000000000000000000)))) else (if n < 346 then (box (40144486000000000000000000000) (40145052000000000000000000000)) else (if n < 347 then (box (40521226000000000000000000000) (40521795000000000000000000000)) else (box (40900657000000000000000000000) (40901229000000000000000000000)))))) else (if n < 354 then (if n < 351 then (if n < 349 then (box (41282790000000000000000000000) (41283364000000000000000000000)) else (if n < 350 then (box (41667634000000000000000000000) (41668210000000000000000000000)) else (box (42055199000000000000000000000) (42055778000000000000000000000)))) else (if n < 352 then (box (42445496000000000000000000000) (42446078000000000000000000000)) else (if n < 353 then (box (42838535000000000000000000000) (42839120000000000000000000000)) else (box (43234326000000000000000000000) (43234914000000000000000000000))))) else (if n < 357 then (if n < 355 then (box (43632880000000000000000000000) (43633471000000000000000000000)) else (if n < 356 then (box (44034207000000000000000000000) (44034800000000000000000000000)) else (box (44438318000000000000000000000) (44438913000000000000000000000)))) else (if n < 358 then (box (44845223000000000000000000000) (44845820000000000000000000000)) else (if n < 359 then (box (45254933000000000000000000000) (45255532000000000000000000000)) else (box (45667458000000000000000000000) (45668060000000000000000000000)))))))
def cM315_360 (n:Nat):IV:=(if n < 337 then (cM315_337 n) else (cM337_360 n))
def cM270_360 (n:Nat):IV:=(if n < 315 then (cM270_315 n) else (cM315_360 n))
def cM180_360 (n:Nat):IV:=(if n < 270 then (cM180_270 n) else (cM270_360 n))
def cM0_360 (n:Nat):IV:=(if n < 180 then (cM0_180 n) else (cM180_360 n))
def cM360_382 (n:Nat):IV:=(if n < 371 then (if n < 365 then (if n < 362 then (if n < 361 then (box (46082809000000000000000000000) (46083414000000000000000000000)) else (box (46500998000000000000000000000) (46501605000000000000000000000))) else (if n < 363 then (box (46922035000000000000000000000) (46922644000000000000000000000)) else (if n < 364 then (box (47345931000000000000000000000) (47346542000000000000000000000)) else (box (47772697000000000000000000000) (47773310000000000000000000000))))) else (if n < 368 then (if n < 366 then (box (48202344000000000000000000000) (48202959000000000000000000000)) else (if n < 367 then (box (48634883000000000000000000000) (48635500000000000000000000000)) else (box (49070325000000000000000000000) (49070945000000000000000000000)))) else (if n < 369 then (box (49508682000000000000000000000) (49509305000000000000000000000)) else (if n < 370 then (box (49949965000000000000000000000) (49950591000000000000000000000)) else (box (50394186000000000000000000000) (50394815000000000000000000000)))))) else (if n < 376 then (if n < 373 then (if n < 372 then (box (50841356000000000000000000000) (50841988000000000000000000000)) else (box (51291487000000000000000000000) (51292121000000000000000000000))) else (if n < 374 then (box (51744590000000000000000000000) (51745227000000000000000000000)) else (if n < 375 then (box (52200677000000000000000000000) (52201317000000000000000000000)) else (box (52659760000000000000000000000) (52660402000000000000000000000))))) else (if n < 379 then (if n < 377 then (box (53121850000000000000000000000) (53122495000000000000000000000)) else (if n < 378 then (box (53586960000000000000000000000) (53587607000000000000000000000)) else (box (54055101000000000000000000000) (54055751000000000000000000000)))) else (if n < 380 then (box (54526286000000000000000000000) (54526939000000000000000000000)) else (if n < 381 then (box (55000527000000000000000000000) (55001182000000000000000000000)) else (box (55477836000000000000000000000) (55478493000000000000000000000)))))))
def cM382_405 (n:Nat):IV:=(if n < 393 then (if n < 387 then (if n < 384 then (if n < 383 then (box (55958225000000000000000000000) (55958884000000000000000000000)) else (box (56441706000000000000000000000) (56442368000000000000000000000))) else (if n < 385 then (box (56928292000000000000000000000) (56928957000000000000000000000)) else (if n < 386 then (box (57417996000000000000000000000) (57418663000000000000000000000)) else (box (57910830000000000000000000000) (57911499000000000000000000000))))) else (if n < 390 then (if n < 388 then (box (58406806000000000000000000000) (58407478000000000000000000000)) else (if n < 389 then (box (58905938000000000000000000000) (58906612000000000000000000000)) else (box (59408238000000000000000000000) (59408914000000000000000000000)))) else (if n < 391 then (box (59913719000000000000000000000) (59914397000000000000000000000)) else (if n < 392 then (box (60422394000000000000000000000) (60423074000000000000000000000)) else (box (60934276000000000000000000000) (60934958000000000000000000000)))))) else (if n < 399 then (if n < 396 then (if n < 394 then (box (61449378000000000000000000000) (61450062000000000000000000000)) else (if n < 395 then (box (61967713000000000000000000000) (61968400000000000000000000000)) else (box (62489294000000000000000000000) (62489984000000000000000000000)))) else (if n < 397 then (box (63014135000000000000000000000) (63014828000000000000000000000)) else (if n < 398 then (box (63542249000000000000000000000) (63542945000000000000000000000)) else (box (64073650000000000000000000000) (64074349000000000000000000000))))) else (if n < 402 then (if n < 400 then (box (64608351000000000000000000000) (64609053000000000000000000000)) else (if n < 401 then (box (65146366000000000000000000000) (65147071000000000000000000000)) else (box (65687709000000000000000000000) (65688417000000000000000000000)))) else (if n < 403 then (box (66232393000000000000000000000) (66233104000000000000000000000)) else (if n < 404 then (box (66780432000000000000000000000) (66781146000000000000000000000)) else (box (67331841000000000000000000000) (67332557000000000000000000000)))))))
def cM360_405 (n:Nat):IV:=(if n < 382 then (cM360_382 n) else (cM382_405 n))
def cM405_427 (n:Nat):IV:=(if n < 416 then (if n < 410 then (if n < 407 then (if n < 406 then (box (67886633000000000000000000000) (67887352000000000000000000000)) else (box (68444822000000000000000000000) (68445544000000000000000000000))) else (if n < 408 then (box (69006423000000000000000000000) (69007148000000000000000000000)) else (if n < 409 then (box (69571450000000000000000000000) (69572177000000000000000000000)) else (box (70139917000000000000000000000) (70140647000000000000000000000))))) else (if n < 413 then (if n < 411 then (box (70711839000000000000000000000) (70712571000000000000000000000)) else (if n < 412 then (box (71287230000000000000000000000) (71287964000000000000000000000)) else (box (71866105000000000000000000000) (71866841000000000000000000000)))) else (if n < 414 then (box (72448478000000000000000000000) (72449217000000000000000000000)) else (if n < 415 then (box (73034364000000000000000000000) (73035106000000000000000000000)) else (box (73623779000000000000000000000) (73624523000000000000000000000)))))) else (if n < 421 then (if n < 418 then (if n < 417 then (box (74216737000000000000000000000) (74217484000000000000000000000)) else (box (74813253000000000000000000000) (74814003000000000000000000000))) else (if n < 419 then (box (75413342000000000000000000000) (75414095000000000000000000000)) else (if n < 420 then (box (76017020000000000000000000000) (76017775000000000000000000000)) else (box (76624302000000000000000000000) (76625059000000000000000000000))))) else (if n < 424 then (if n < 422 then (box (77235203000000000000000000000) (77235963000000000000000000000)) else (if n < 423 then (box (77849739000000000000000000000) (77850501000000000000000000000)) else (box (78467925000000000000000000000) (78468690000000000000000000000)))) else (if n < 425 then (box (79089777000000000000000000000) (79090544000000000000000000000)) else (if n < 426 then (box (79715310000000000000000000000) (79716080000000000000000000000)) else (box (80344541000000000000000000000) (80345314000000000000000000000)))))))
def cM427_450 (n:Nat):IV:=(if n < 438 then (if n < 432 then (if n < 429 then (if n < 428 then (box (80977485000000000000000000000) (80978261000000000000000000000)) else (box (81614159000000000000000000000) (81614937000000000000000000000))) else (if n < 430 then (box (82254578000000000000000000000) (82255359000000000000000000000)) else (if n < 431 then (box (82898759000000000000000000000) (82899543000000000000000000000)) else (box (83546718000000000000000000000) (83547505000000000000000000000))))) else (if n < 435 then (if n < 433 then (box (84198471000000000000000000000) (84199261000000000000000000000)) else (if n < 434 then (box (84854035000000000000000000000) (84854828000000000000000000000)) else (box (85513426000000000000000000000) (85514222000000000000000000000)))) else (if n < 436 then (box (86176661000000000000000000000) (86177460000000000000000000000)) else (if n < 437 then (box (86843757000000000000000000000) (86844559000000000000000000000)) else (box (87514731000000000000000000000) (87515536000000000000000000000)))))) else (if n < 444 then (if n < 441 then (if n < 439 then (box (88189600000000000000000000000) (88190407000000000000000000000)) else (if n < 440 then (box (88868380000000000000000000000) (88869190000000000000000000000)) else (box (89551089000000000000000000000) (89551902000000000000000000000)))) else (if n < 442 then (box (90237744000000000000000000000) (90238560000000000000000000000)) else (if n < 443 then (box (90928362000000000000000000000) (90929181000000000000000000000)) else (box (91622961000000000000000000000) (91623783000000000000000000000))))) else (if n < 447 then (if n < 445 then (box (92321558000000000000000000000) (92322383000000000000000000000)) else (if n < 446 then (box (93024171000000000000000000000) (93024999000000000000000000000)) else (box (93730818000000000000000000000) (93731649000000000000000000000)))) else (if n < 448 then (box (94441516000000000000000000000) (94442350000000000000000000000)) else (if n < 449 then (box (95156284000000000000000000000) (95157120000000000000000000000)) else (box (95875139000000000000000000000) (95875978000000000000000000000)))))))
def cM405_450 (n:Nat):IV:=(if n < 427 then (cM405_427 n) else (cM427_450 n))
def cM360_450 (n:Nat):IV:=(if n < 405 then (cM360_405 n) else (cM405_450 n))
def cM450_472 (n:Nat):IV:=(if n < 461 then (if n < 455 then (if n < 452 then (if n < 451 then (box (96598100000000000000000000000) (96598942000000000000000000000)) else (box (97325184000000000000000000000) (97326029000000000000000000000))) else (if n < 453 then (box (98056410000000000000000000000) (98057258000000000000000000000)) else (if n < 454 then (box (98791797000000000000000000000) (98792648000000000000000000000)) else (box (99531363000000000000000000000) (99532217000000000000000000000))))) else (if n < 458 then (if n < 456 then (box (100275126000000000000000000000) (100275983000000000000000000000)) else (if n < 457 then (box (101023105000000000000000000000) (101023965000000000000000000000)) else (box (101775320000000000000000000000) (101776183000000000000000000000)))) else (if n < 459 then (box (102531789000000000000000000000) (102532655000000000000000000000)) else (if n < 460 then (box (103292531000000000000000000000) (103293400000000000000000000000)) else (box (104057565000000000000000000000) (104058437000000000000000000000)))))) else (if n < 466 then (if n < 463 then (if n < 462 then (box (104826910000000000000000000000) (104827785000000000000000000000)) else (box (105600586000000000000000000000) (105601464000000000000000000000))) else (if n < 464 then (box (106378613000000000000000000000) (106379494000000000000000000000)) else (if n < 465 then (box (107161009000000000000000000000) (107161893000000000000000000000)) else (box (107947795000000000000000000000) (107948682000000000000000000000))))) else (if n < 469 then (if n < 467 then (box (108738990000000000000000000000) (108739880000000000000000000000)) else (if n < 468 then (box (109534615000000000000000000000) (109535508000000000000000000000)) else (box (110334689000000000000000000000) (110335585000000000000000000000)))) else (if n < 470 then (box (111139232000000000000000000000) (111140131000000000000000000000)) else (if n < 471 then (box (111948265000000000000000000000) (111949167000000000000000000000)) else (box (112761808000000000000000000000) (112762713000000000000000000000)))))))
def cM472_495 (n:Nat):IV:=(if n < 483 then (if n < 477 then (if n < 474 then (if n < 473 then (box (113579881000000000000000000000) (113580789000000000000000000000)) else (box (114402505000000000000000000000) (114403416000000000000000000000))) else (if n < 475 then (box (115229701000000000000000000000) (115230615000000000000000000000)) else (if n < 476 then (box (116061489000000000000000000000) (116062406000000000000000000000)) else (box (116897890000000000000000000000) (116898810000000000000000000000))))) else (if n < 480 then (if n < 478 then (box (117738926000000000000000000000) (117739849000000000000000000000)) else (if n < 479 then (box (118584617000000000000000000000) (118585543000000000000000000000)) else (box (119434985000000000000000000000) (119435914000000000000000000000)))) else (if n < 481 then (box (120290051000000000000000000000) (120290983000000000000000000000)) else (if n < 482 then (box (121149836000000000000000000000) (121150771000000000000000000000)) else (box (122014362000000000000000000000) (122015301000000000000000000000)))))) else (if n < 489 then (if n < 486 then (if n < 484 then (box (122883651000000000000000000000) (122884593000000000000000000000)) else (if n < 485 then (box (123757725000000000000000000000) (123758670000000000000000000000)) else (box (124636605000000000000000000000) (124637553000000000000000000000)))) else (if n < 487 then (box (125520314000000000000000000000) (125521265000000000000000000000)) else (if n < 488 then (box (126408874000000000000000000000) (126409828000000000000000000000)) else (box (127302307000000000000000000000) (127303264000000000000000000000))))) else (if n < 492 then (if n < 490 then (box (128200635000000000000000000000) (128201596000000000000000000000)) else (if n < 491 then (box (129103881000000000000000000000) (129104846000000000000000000000)) else (box (130012068000000000000000000000) (130013036000000000000000000000)))) else (if n < 493 then (box (130925219000000000000000000000) (130926190000000000000000000000)) else (if n < 494 then (box (131843356000000000000000000000) (131844330000000000000000000000)) else (box (132766503000000000000000000000) (132767480000000000000000000000)))))))
def cM450_495 (n:Nat):IV:=(if n < 472 then (cM450_472 n) else (cM472_495 n))
def cM495_517 (n:Nat):IV:=(if n < 506 then (if n < 500 then (if n < 497 then (if n < 496 then (box (133694682000000000000000000000) (133695663000000000000000000000)) else (box (134627917000000000000000000000) (134628902000000000000000000000))) else (if n < 498 then (box (135566232000000000000000000000) (135567220000000000000000000000)) else (if n < 499 then (box (136509650000000000000000000000) (136510641000000000000000000000)) else (box (137458194000000000000000000000) (137459188000000000000000000000))))) else (if n < 503 then (if n < 501 then (box (138411888000000000000000000000) (138412886000000000000000000000)) else (if n < 502 then (box (139370757000000000000000000000) (139371758000000000000000000000)) else (box (140334824000000000000000000000) (140335828000000000000000000000)))) else (if n < 504 then (box (141304114000000000000000000000) (141305121000000000000000000000)) else (if n < 505 then (box (142278650000000000000000000000) (142279661000000000000000000000)) else (box (143258457000000000000000000000) (143259472000000000000000000000)))))) else (if n < 511 then (if n < 508 then (if n < 507 then (box (144243560000000000000000000000) (144244578000000000000000000000)) else (box (145233984000000000000000000000) (145235005000000000000000000000))) else (if n < 509 then (box (146229753000000000000000000000) (146230777000000000000000000000)) else (if n < 510 then (box (147230892000000000000000000000) (147231920000000000000000000000)) else (box (148237427000000000000000000000) (148238458000000000000000000000))))) else (if n < 514 then (if n < 512 then (box (149249382000000000000000000000) (149250417000000000000000000000)) else (if n < 513 then (box (150266783000000000000000000000) (150267822000000000000000000000)) else (box (151289656000000000000000000000) (151290698000000000000000000000)))) else (if n < 515 then (box (152318026000000000000000000000) (152319071000000000000000000000)) else (if n < 516 then (box (153351919000000000000000000000) (153352967000000000000000000000)) else (box (154391360000000000000000000000) (154392412000000000000000000000)))))))
def cM517_540 (n:Nat):IV:=(if n < 528 then (if n < 522 then (if n < 519 then (if n < 518 then (box (155436376000000000000000000000) (155437432000000000000000000000)) else (box (156486993000000000000000000000) (156488053000000000000000000000))) else (if n < 520 then (box (157543238000000000000000000000) (157544301000000000000000000000)) else (if n < 521 then (box (158605136000000000000000000000) (158606203000000000000000000000)) else (box (159672715000000000000000000000) (159673785000000000000000000000))))) else (if n < 525 then (if n < 523 then (box (160746001000000000000000000000) (160747074000000000000000000000)) else (if n < 524 then (box (161825021000000000000000000000) (161826097000000000000000000000)) else (box (162909802000000000000000000000) (162910882000000000000000000000)))) else (if n < 526 then (box (164000371000000000000000000000) (164001455000000000000000000000)) else (if n < 527 then (box (165096756000000000000000000000) (165097843000000000000000000000)) else (box (166198984000000000000000000000) (166200074000000000000000000000)))))) else (if n < 534 then (if n < 531 then (if n < 529 then (box (167307083000000000000000000000) (167308176000000000000000000000)) else (if n < 530 then (box (168421080000000000000000000000) (168422177000000000000000000000)) else (box (169541003000000000000000000000) (169542104000000000000000000000)))) else (if n < 532 then (box (170666881000000000000000000000) (170667985000000000000000000000)) else (if n < 533 then (box (171798741000000000000000000000) (171799849000000000000000000000)) else (box (172936612000000000000000000000) (172937724000000000000000000000))))) else (if n < 537 then (if n < 535 then (box (174080523000000000000000000000) (174081638000000000000000000000)) else (if n < 536 then (box (175230502000000000000000000000) (175231620000000000000000000000)) else (box (176386577000000000000000000000) (176387699000000000000000000000)))) else (if n < 538 then (box (177548778000000000000000000000) (177549904000000000000000000000)) else (if n < 539 then (box (178717134000000000000000000000) (178718264000000000000000000000)) else (box (179891674000000000000000000000) (179892808000000000000000000000)))))))
def cM495_540 (n:Nat):IV:=(if n < 517 then (cM495_517 n) else (cM517_540 n))
def cM450_540 (n:Nat):IV:=(if n < 495 then (cM450_495 n) else (cM495_540 n))
def cM360_540 (n:Nat):IV:=(if n < 450 then (cM360_450 n) else (cM450_540 n))
def cM540_562 (n:Nat):IV:=(if n < 551 then (if n < 545 then (if n < 542 then (if n < 541 then (box (181072428000000000000000000000) (181073566000000000000000000000)) else (box (182259425000000000000000000000) (182260567000000000000000000000))) else (if n < 543 then (box (183452695000000000000000000000) (183453840000000000000000000000)) else (if n < 544 then (box (184652267000000000000000000000) (184653416000000000000000000000)) else (box (185858172000000000000000000000) (185859325000000000000000000000))))) else (if n < 548 then (if n < 546 then (box (187070440000000000000000000000) (187071597000000000000000000000)) else (if n < 547 then (box (188289101000000000000000000000) (188290262000000000000000000000)) else (box (189514186000000000000000000000) (189515351000000000000000000000)))) else (if n < 549 then (box (190745726000000000000000000000) (190746894000000000000000000000)) else (if n < 550 then (box (191983751000000000000000000000) (191984923000000000000000000000)) else (box (193228292000000000000000000000) (193229468000000000000000000000)))))) else (if n < 556 then (if n < 553 then (if n < 552 then (box (194479381000000000000000000000) (194480560000000000000000000000)) else (box (195737049000000000000000000000) (195738231000000000000000000000))) else (if n < 554 then (box (197001327000000000000000000000) (197002512000000000000000000000)) else (if n < 555 then (box (198272247000000000000000000000) (198273435000000000000000000000)) else (box (199549840000000000000000000000) (199551032000000000000000000000))))) else (if n < 559 then (if n < 557 then (box (200834139000000000000000000000) (200835335000000000000000000000)) else (if n < 558 then (box (202125176000000000000000000000) (202126376000000000000000000000)) else (box (203422983000000000000000000000) (203424187000000000000000000000)))) else (if n < 560 then (box (204727593000000000000000000000) (204728801000000000000000000000)) else (if n < 561 then (box (206039038000000000000000000000) (206040250000000000000000000000)) else (box (207357351000000000000000000000) (207358567000000000000000000000)))))))
def cM562_585 (n:Nat):IV:=(if n < 573 then (if n < 567 then (if n < 564 then (if n < 563 then (box (208682565000000000000000000000) (208683785000000000000000000000)) else (box (210014713000000000000000000000) (210015937000000000000000000000))) else (if n < 565 then (box (211353829000000000000000000000) (211355057000000000000000000000)) else (if n < 566 then (box (212699946000000000000000000000) (212701178000000000000000000000)) else (box (214053098000000000000000000000) (214054334000000000000000000000))))) else (if n < 570 then (if n < 568 then (box (215413318000000000000000000000) (215414558000000000000000000000)) else (if n < 569 then (box (216780641000000000000000000000) (216781885000000000000000000000)) else (box (218155101000000000000000000000) (218156349000000000000000000000)))) else (if n < 571 then (box (219536732000000000000000000000) (219537984000000000000000000000)) else (if n < 572 then (box (220925569000000000000000000000) (220926825000000000000000000000)) else (box (222321647000000000000000000000) (222322907000000000000000000000)))))) else (if n < 579 then (if n < 576 then (if n < 574 then (box (223725000000000000000000000000) (223726264000000000000000000000)) else (if n < 575 then (box (225135664000000000000000000000) (225136932000000000000000000000)) else (box (226553674000000000000000000000) (226554946000000000000000000000)))) else (if n < 577 then (box (227979066000000000000000000000) (227980341000000000000000000000)) else (if n < 578 then (box (229411874000000000000000000000) (229413153000000000000000000000)) else (box (230852135000000000000000000000) (230853418000000000000000000000))))) else (if n < 582 then (if n < 580 then (box (232299885000000000000000000000) (232301172000000000000000000000)) else (if n < 581 then (box (233755161000000000000000000000) (233756452000000000000000000000)) else (box (235217998000000000000000000000) (235219293000000000000000000000)))) else (if n < 583 then (box (236688433000000000000000000000) (236689732000000000000000000000)) else (if n < 584 then (box (238166503000000000000000000000) (238167806000000000000000000000)) else (box (239652245000000000000000000000) (239653552000000000000000000000)))))))
def cM540_585 (n:Nat):IV:=(if n < 562 then (cM540_562 n) else (cM562_585 n))
def cM585_607 (n:Nat):IV:=(if n < 596 then (if n < 590 then (if n < 587 then (if n < 586 then (box (241145696000000000000000000000) (241147007000000000000000000000)) else (box (242646894000000000000000000000) (242648209000000000000000000000))) else (if n < 588 then (box (244155876000000000000000000000) (244157195000000000000000000000)) else (if n < 589 then (box (245672680000000000000000000000) (245674003000000000000000000000)) else (box (247197344000000000000000000000) (247198671000000000000000000000))))) else (if n < 593 then (if n < 591 then (box (248729906000000000000000000000) (248731237000000000000000000000)) else (if n < 592 then (box (250270404000000000000000000000) (250271739000000000000000000000)) else (box (251818877000000000000000000000) (251820216000000000000000000000)))) else (if n < 594 then (box (253375363000000000000000000000) (253376706000000000000000000000)) else (if n < 595 then (box (254939901000000000000000000000) (254941248000000000000000000000)) else (box (256512531000000000000000000000) (256513882000000000000000000000)))))) else (if n < 601 then (if n < 598 then (if n < 597 then (box (258093292000000000000000000000) (258094647000000000000000000000)) else (box (259682223000000000000000000000) (259683583000000000000000000000))) else (if n < 599 then (box (261279365000000000000000000000) (261280729000000000000000000000)) else (if n < 600 then (box (262884757000000000000000000000) (262886125000000000000000000000)) else (box (264498439000000000000000000000) (264499811000000000000000000000))))) else (if n < 604 then (if n < 602 then (box (266120452000000000000000000000) (266121828000000000000000000000)) else (if n < 603 then (box (267750836000000000000000000000) (267752216000000000000000000000)) else (box (269389632000000000000000000000) (269391016000000000000000000000)))) else (if n < 605 then (box (271036881000000000000000000000) (271038269000000000000000000000)) else (if n < 606 then (box (272692624000000000000000000000) (272694017000000000000000000000)) else (box (274356903000000000000000000000) (274358300000000000000000000000)))))))
def cM607_630 (n:Nat):IV:=(if n < 618 then (if n < 612 then (if n < 609 then (if n < 608 then (box (276029759000000000000000000000) (276031160000000000000000000000)) else (box (277711234000000000000000000000) (277712639000000000000000000000))) else (if n < 610 then (box (279401370000000000000000000000) (279402780000000000000000000000)) else (if n < 611 then (box (281100210000000000000000000000) (281101624000000000000000000000)) else (box (282807796000000000000000000000) (282809214000000000000000000000))))) else (if n < 615 then (if n < 613 then (box (284524170000000000000000000000) (284525593000000000000000000000)) else (if n < 614 then (box (286249376000000000000000000000) (286250803000000000000000000000)) else (box (287983457000000000000000000000) (287984888000000000000000000000)))) else (if n < 616 then (box (289726456000000000000000000000) (289727891000000000000000000000)) else (if n < 617 then (box (291478417000000000000000000000) (291479856000000000000000000000)) else (box (293239383000000000000000000000) (293240826000000000000000000000)))))) else (if n < 624 then (if n < 621 then (if n < 619 then (box (295009398000000000000000000000) (295010846000000000000000000000)) else (if n < 620 then (box (296788507000000000000000000000) (296789959000000000000000000000)) else (box (298576755000000000000000000000) (298578211000000000000000000000)))) else (if n < 622 then (box (300374186000000000000000000000) (300375646000000000000000000000)) else (if n < 623 then (box (302180844000000000000000000000) (302182309000000000000000000000)) else (box (303996776000000000000000000000) (303998245000000000000000000000))))) else (if n < 627 then (if n < 625 then (box (305822026000000000000000000000) (305823499000000000000000000000)) else (if n < 626 then (box (307656640000000000000000000000) (307658118000000000000000000000)) else (box (309500664000000000000000000000) (309502147000000000000000000000)))) else (if n < 628 then (box (311354144000000000000000000000) (311355632000000000000000000000)) else (if n < 629 then (box (313217127000000000000000000000) (313218619000000000000000000000)) else (box (315089659000000000000000000000) (315091156000000000000000000000)))))))
def cM585_630 (n:Nat):IV:=(if n < 607 then (cM585_607 n) else (cM607_630 n))
def cM540_630 (n:Nat):IV:=(if n < 585 then (cM540_585 n) else (cM585_630 n))
def cM630_652 (n:Nat):IV:=(if n < 641 then (if n < 635 then (if n < 632 then (if n < 631 then (box (316971787000000000000000000000) (316973289000000000000000000000)) else (box (318863558000000000000000000000) (318865065000000000000000000000))) else (if n < 633 then (box (320765019000000000000000000000) (320766531000000000000000000000)) else (if n < 634 then (box (322676218000000000000000000000) (322677735000000000000000000000)) else (box (324597203000000000000000000000) (324598725000000000000000000000))))) else (if n < 638 then (if n < 636 then (box (326528022000000000000000000000) (326529548000000000000000000000)) else (if n < 637 then (box (328468723000000000000000000000) (328470253000000000000000000000)) else (box (330419354000000000000000000000) (330420889000000000000000000000)))) else (if n < 639 then (box (332379965000000000000000000000) (332381504000000000000000000000)) else (if n < 640 then (box (334350604000000000000000000000) (334352148000000000000000000000)) else (box (336331321000000000000000000000) (336332869000000000000000000000)))))) else (if n < 646 then (if n < 643 then (if n < 642 then (box (338322165000000000000000000000) (338323717000000000000000000000)) else (box (340323186000000000000000000000) (340324742000000000000000000000))) else (if n < 644 then (box (342334433000000000000000000000) (342335994000000000000000000000)) else (if n < 645 then (box (344355958000000000000000000000) (344357524000000000000000000000)) else (box (346387811000000000000000000000) (346389381000000000000000000000))))) else (if n < 649 then (if n < 647 then (box (348430042000000000000000000000) (348431617000000000000000000000)) else (if n < 648 then (box (350482703000000000000000000000) (350484283000000000000000000000)) else (box (352545845000000000000000000000) (352547430000000000000000000000)))) else (if n < 650 then (box (354619520000000000000000000000) (354621109000000000000000000000)) else (if n < 651 then (box (356703779000000000000000000000) (356705373000000000000000000000)) else (box (358798675000000000000000000000) (358800273000000000000000000000)))))))
def cM652_675 (n:Nat):IV:=(if n < 663 then (if n < 657 then (if n < 654 then (if n < 653 then (box (360904260000000000000000000000) (360905863000000000000000000000)) else (box (363020586000000000000000000000) (363022194000000000000000000000))) else (if n < 655 then (box (365147707000000000000000000000) (365149320000000000000000000000)) else (if n < 656 then (box (367285676000000000000000000000) (367287293000000000000000000000)) else (box (369434546000000000000000000000) (369436167000000000000000000000))))) else (if n < 660 then (if n < 658 then (box (371594371000000000000000000000) (371595997000000000000000000000)) else (if n < 659 then (box (373765205000000000000000000000) (373766835000000000000000000000)) else (box (375947102000000000000000000000) (375948737000000000000000000000)))) else (if n < 661 then (box (378140117000000000000000000000) (378141756000000000000000000000)) else (if n < 662 then (box (380344304000000000000000000000) (380345948000000000000000000000)) else (box (382559719000000000000000000000) (382561368000000000000000000000)))))) else (if n < 669 then (if n < 666 then (if n < 664 then (box (384786417000000000000000000000) (384788071000000000000000000000)) else (if n < 665 then (box (387024454000000000000000000000) (387026113000000000000000000000)) else (box (389273886000000000000000000000) (389275549000000000000000000000)))) else (if n < 667 then (box (391534769000000000000000000000) (391536436000000000000000000000)) else (if n < 668 then (box (393807159000000000000000000000) (393808831000000000000000000000)) else (box (396091113000000000000000000000) (396092790000000000000000000000))))) else (if n < 672 then (if n < 670 then (box (398386689000000000000000000000) (398388371000000000000000000000)) else (if n < 671 then (box (400693944000000000000000000000) (400695631000000000000000000000)) else (box (403012935000000000000000000000) (403014627000000000000000000000)))) else (if n < 673 then (box (405343720000000000000000000000) (405345417000000000000000000000)) else (if n < 674 then (box (407686358000000000000000000000) (407688060000000000000000000000)) else (box (410040908000000000000000000000) (410042615000000000000000000000)))))))
def cM630_675 (n:Nat):IV:=(if n < 652 then (cM630_652 n) else (cM652_675 n))
def cM675_698 (n:Nat):IV:=(if n < 686 then (if n < 680 then (if n < 677 then (if n < 676 then (box (412407428000000000000000000000) (412409140000000000000000000000)) else (box (414785977000000000000000000000) (414787694000000000000000000000))) else (if n < 678 then (box (417176615000000000000000000000) (417178337000000000000000000000)) else (if n < 679 then (box (419579402000000000000000000000) (419581129000000000000000000000)) else (box (421994398000000000000000000000) (421996130000000000000000000000))))) else (if n < 683 then (if n < 681 then (box (424421663000000000000000000000) (424423400000000000000000000000)) else (if n < 682 then (box (426861258000000000000000000000) (426863000000000000000000000000)) else (box (429313243000000000000000000000) (429314991000000000000000000000)))) else (if n < 684 then (box (431777681000000000000000000000) (431779434000000000000000000000)) else (if n < 685 then (box (434254632000000000000000000000) (434256390000000000000000000000)) else (box (436744159000000000000000000000) (436745922000000000000000000000)))))) else (if n < 692 then (if n < 689 then (if n < 687 then (box (439246324000000000000000000000) (439248092000000000000000000000)) else (if n < 688 then (box (441761189000000000000000000000) (441762962000000000000000000000)) else (box (444288817000000000000000000000) (444290596000000000000000000000)))) else (if n < 690 then (box (446829272000000000000000000000) (446831056000000000000000000000)) else (if n < 691 then (box (449382617000000000000000000000) (449384407000000000000000000000)) else (box (451948916000000000000000000000) (451950711000000000000000000000))))) else (if n < 695 then (if n < 693 then (box (454528233000000000000000000000) (454530033000000000000000000000)) else (if n < 694 then (box (457120633000000000000000000000) (457122438000000000000000000000)) else (box (459726180000000000000000000000) (459727990000000000000000000000)))) else (if n < 696 then (box (462344939000000000000000000000) (462346755000000000000000000000)) else (if n < 697 then (box (464976976000000000000000000000) (464978798000000000000000000000)) else (box (467622357000000000000000000000) (467624184000000000000000000000)))))))
def cM698_721 (n:Nat):IV:=(if n < 709 then (if n < 703 then (if n < 700 then (if n < 699 then (box (470281148000000000000000000000) (470282980000000000000000000000)) else (box (472953415000000000000000000000) (472955253000000000000000000000))) else (if n < 701 then (box (475639226000000000000000000000) (475641069000000000000000000000)) else (if n < 702 then (box (478338647000000000000000000000) (478340496000000000000000000000)) else (box (481051746000000000000000000000) (481053600000000000000000000000))))) else (if n < 706 then (if n < 704 then (box (483778591000000000000000000000) (483780450000000000000000000000)) else (if n < 705 then (box (486519250000000000000000000000) (486521114000000000000000000000)) else (box (489273791000000000000000000000) (489275660000000000000000000000)))) else (if n < 707 then (box (492042283000000000000000000000) (492044158000000000000000000000)) else (if n < 708 then (box (494824796000000000000000000000) (494826676000000000000000000000)) else (box (497621399000000000000000000000) (497623284000000000000000000000)))))) else (if n < 715 then (if n < 712 then (if n < 710 then (box (500432162000000000000000000000) (500434052000000000000000000000)) else (if n < 711 then (box (503257155000000000000000000000) (503259051000000000000000000000)) else (box (506096449000000000000000000000) (506098351000000000000000000000)))) else (if n < 713 then (box (508950115000000000000000000000) (508952022000000000000000000000)) else (if n < 714 then (box (511818224000000000000000000000) (511820137000000000000000000000)) else (box (514700848000000000000000000000) (514702767000000000000000000000))))) else (if n < 718 then (if n < 716 then (box (517598059000000000000000000000) (517599984000000000000000000000)) else (if n < 717 then (box (520509929000000000000000000000) (520511860000000000000000000000)) else (box (523436532000000000000000000000) (523438468000000000000000000000)))) else (if n < 719 then (box (526377940000000000000000000000) (526379882000000000000000000000)) else (if n < 720 then (box (529334227000000000000000000000) (529336175000000000000000000000)) else (box (532305467000000000000000000000) (532307421000000000000000000000)))))))
def cM675_721 (n:Nat):IV:=(if n < 698 then (cM675_698 n) else (cM698_721 n))
def cM630_721 (n:Nat):IV:=(if n < 675 then (cM630_675 n) else (cM675_721 n))
def cM540_721 (n:Nat):IV:=(if n < 630 then (cM540_630 n) else (cM630_721 n))
def cM360_721 (n:Nat):IV:=(if n < 540 then (cM360_540 n) else (cM540_721 n))
def cM0_721 (n:Nat):IV:=(if n < 360 then (cM0_360 n) else (cM360_721 n))
def Cn (n:Nat):Ft→IV
  | Ft.K=> cK0_721 n
  | Ft.C=> cC0_721 n
  | Ft.Q=> cQ0_721 n
  | Ft.J=> cJ0_721 n
  | Ft.V=> cV0_721 n
  | Ft.M=> cM0_721 n
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Chord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §08 chord kernel W for signed comparison. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal.SE
open Profile Tag Jet
variable (m h:ℝ)
def leng:= (seg m h).2-(seg m h).1
def cθ (x:ℝ):=(xs (loc m h x)-(seg m h).1)/leng m h
def omega (x:ℝ):=6*cθ m h x*(1-cθ m h x)*cosh m/(de m h x)*shv h
end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Small
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Small angle scale estimates. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet
local notation "w" => Profile.omegaP
def wp:= r^2*w^2
def ubase (h:ℝ):= wp*h^2/3
def qsmall (h:ℝ):= (1-2*w^4*h^2/(15*(1+w^2)))/(1+h^2/3)
end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Disp
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §08 Short-width budgets. Endpoint deviations. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Jet Profile Segment
variable {f g:ℝ→ℝ}
def errorF (m h:ℝ)(f:ℝ→ℝ)(s:ℝ)(x:ℝ):=(liftF f (loc m h x)-liftF f (loc m h s))^2
end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_First
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Combine chord and endpoint variation using pointwise U star. -/
noncomputable section
open Set Filter Real MeasureTheory
open scoped Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet Segment
variable (m:ℝ){h:ℝ}
def alongD (m h:ℝ)(f:ℝ→ℝ):=fun x=> DotF f (loc m h x)
def alongN (m h:ℝ)(f:ℝ→ℝ):=fun x=> NNf f (loc m h x)

def GammaB (f g:ℝ):=(12*(8/10:ℝ)/mstar^2)*(125/100*(f+tc*g)^2+5*Profile.tr^2*g^2)

def negN (m h:ℝ):= fun x=> -(omega m h x*alongN m h Kp x)
end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Average
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Uniform endpoint and mean estimates for larger widths. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet Segment
variable {m h:ℝ} {f:ℝ→ℝ}

-- convex endpoint budget bound
def Yval (x y z:ℝ):=
    -(x+y)/2 + (80/100:ℝ)/mstar^2*((125/100)*(y-x+tc*z)^2+5*Profile.tr^2*z^2)
end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general Mahler inequality, equality characterization, and Santaló minimum. -/

namespace GeneralMahler

open SCal SCal.Grid SCal.Mid Set MeasureTheory

def ofSet {n : ℕ} (K : Set (Rn n)) (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) : Body n where
  carrier := K
  convex' := hc
  isCompact' := hK
  nonempty' := hi.mono interior_subset
  solid := hi

end GeneralMahler

end OAI
end


