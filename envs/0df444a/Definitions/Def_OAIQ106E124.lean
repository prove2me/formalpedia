-- Prove2me | Definitions.Def_OAIQ106E124
-- name    : OAIQ106E124
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:03:27.977751+00:00
-- url     : https://prove2.me/theorems/573373aa-ca91-43d3-be34-6ef1f9c02889
-- title:
--   Definitions bundle OAIQ106E124 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 737 declarations of OpenAI's Lean: 737 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource0`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource10`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource100`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1000`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1001`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1002`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1003`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1004`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1005`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1006`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1007`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1008`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1009`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource101`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1010`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1011`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1012`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1013`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1014`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1015`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1016`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1017`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1018`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1019`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource102`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1020`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1021`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1022`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1023`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1024`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1025`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1026`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1027`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1028`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1029`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource103`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1030`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1031`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1032` and 697 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSources_Arithmetic0`, `MutuallyUnbiased_MixedSources_Arithmetic1`, `MutuallyUnbiased_MixedSources_Arithmetic10`, `MutuallyUnbiased_MixedSources_Arithmetic100`, `MutuallyUnbiased_MixedSources_Arithmetic101`, `MutuallyUnbiased_MixedSources_Arithmetic102`, `MutuallyUnbiased_MixedSources_Arithmetic103`, `MutuallyUnbiased_MixedSources_Arithmetic6`, `MutuallyUnbiased_MixedSources_Arithmetic62`, `MutuallyUnbiased_MixedSources_Arithmetic63`, `MutuallyUnbiased_MixedSources_Arithmetic64`, `MutuallyUnbiased_MixedSources_Arithmetic65`, `MutuallyUnbiased_MixedSources_Arithmetic66`, `MutuallyUnbiased_MixedSources_Arithmetic67`, `MutuallyUnbiased_MixedSources_Arithmetic68`, `MutuallyUnbiased_MixedSources_Arithmetic69`, `MutuallyUnbiased_MixedSources_Arithmetic7`, `MutuallyUnbiased_MixedSources_Arithmetic70`, `MutuallyUnbiased_MixedSources_Arithmetic71`, `MutuallyUnbiased_MixedSources_Arithmetic72`, `MutuallyUnbiased_MixedSources_Arithmetic73`, `MutuallyUnbiased_MixedSources_Arithmetic74`, `MutuallyUnbiased_MixedSources_Arithmetic75`, `MutuallyUnbiased_MixedSources_Arithmetic76`, `MutuallyUnbiased_MixedSources_Arithmetic77`, `MutuallyUnbiased_MixedSources_Arithmetic78`, `MutuallyUnbiased_MixedSources_Arithmetic79`, `MutuallyUnbiased_MixedSources_Arithmetic8`, `MutuallyUnbiased_MixedSources_Arithmetic80`, `MutuallyUnbiased_MixedSources_Arithmetic81`, `MutuallyUnbiased_MixedSources_Arithmetic82`, `MutuallyUnbiased_MixedSources_Arithmetic83`, `MutuallyUnbiased_MixedSources_Arithmetic84`, `MutuallyUnbiased_MixedSources_Arithmetic85`, `MutuallyUnbiased_MixedSources_Arithmetic86`, `MutuallyUnbiased_MixedSources_Arithmetic87`, `MutuallyUnbiased_MixedSources_Arithmetic88`, `MutuallyUnbiased_MixedSources_Arithmetic89`, `MutuallyUnbiased_MixedSources_Arithmetic9`, `MutuallyUnbiased_MixedSources_Arithmetic90`, `MutuallyUnbiased_MixedSources_Arithmetic91`, `MutuallyUnbiased_MixedSources_Arithmetic92`, `MutuallyUnbiased_MixedSources_Arithmetic93`, `MutuallyUnbiased_MixedSources_Arithmetic94`, `MutuallyUnbiased_MixedSources_Arithmetic95`, `MutuallyUnbiased_MixedSources_Arithmetic96`, `MutuallyUnbiased_MixedSources_Arithmetic97`, `MutuallyUnbiased_MixedSources_Arithmetic98`, `MutuallyUnbiased_MixedSources_Arithmetic99`.
--
--   **Imports.** It imports the bundles `OAIQ106E043` and `OAIQ106E084` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e` and `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`; the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound71_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1030_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E084

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource0 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue4899 x + ((6 : ℝ) * Sparse.eval nodeValue5302 x + ((2 : ℝ) * Sparse.eval nodeValue5310 x + ((6 : ℝ) * Sparse.eval nodeValue5412 x + ((6 : ℝ) * Sparse.eval nodeValue5443 x + ((3 : ℝ) * Sparse.eval nodeValue5453 x + ((2 : ℝ) * Sparse.eval nodeValue5455 x + 0)))))))

noncomputable def reducedSource1 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((4 : ℝ) * Sparse.eval nodeValue5411 x + ((4 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5452 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))

noncomputable def reducedSource10 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4094 x + ((3 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((6 : ℝ) * Sparse.eval nodeValue5439 x + ((3 : ℝ) * Sparse.eval nodeValue5441 x + ((3 : ℝ) * Sparse.eval nodeValue5443 x + ((3 : ℝ) * Sparse.eval nodeValue5453 x + ((4 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + ((3 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5496 x + 0)))))))))))

noncomputable def reducedSource11 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + ((12 : ℝ) * Sparse.eval nodeValue4092 x + ((8 : ℝ) * Sparse.eval nodeValue4093 x + ((1 : ℝ) * Sparse.eval nodeValue4097 x + 0))))

noncomputable def reducedSource12 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5283 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((4 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5447 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5452 x + ((2 : ℝ) * Sparse.eval nodeValue5453 x + ((4 : ℝ) * Sparse.eval nodeValue5454 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))

noncomputable def reducedSource13 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3076 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3801 x + ((4 : ℝ) * Sparse.eval nodeValue3809 x + ((2 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue4009 x + ((2 : ℝ) * Sparse.eval nodeValue4010 x + ((2 : ℝ) * Sparse.eval nodeValue4016 x + ((2 : ℝ) * Sparse.eval nodeValue4025 x + ((2 : ℝ) * Sparse.eval nodeValue4029 x + ((2 : ℝ) * Sparse.eval nodeValue4033 x + ((2 : ℝ) * Sparse.eval nodeValue4039 x + ((4 : ℝ) * Sparse.eval nodeValue4040 x + 0)))))))))))))

noncomputable def reducedSource14 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4887 x + ((4 : ℝ) * Sparse.eval nodeValue4888 x + ((4 : ℝ) * Sparse.eval nodeValue5405 x + ((4 : ℝ) * Sparse.eval nodeValue5433 x + ((8 : ℝ) * Sparse.eval nodeValue5434 x + ((4 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5498 x + ((4 : ℝ) * Sparse.eval nodeValue5499 x + 0)))))))

noncomputable def reducedSource15 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5481 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + ((1 : ℝ) * Sparse.eval nodeValue5495 x + 0)))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource16 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((2 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue3914 x + ((2 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((2 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((2 : ℝ) * Sparse.eval nodeValue4017 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4020 x + ((1 : ℝ) * Sparse.eval nodeValue4021 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource160 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource161 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2124 x + ((1 : ℝ) * Sparse.eval nodeValue2125 x + ((1 : ℝ) * Sparse.eval nodeValue2126 x + ((1 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2513 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource162 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1030 x + ((1 : ℝ) * Sparse.eval nodeValue2014 x + ((1 : ℝ) * Sparse.eval nodeValue2097 x + ((1 : ℝ) * Sparse.eval nodeValue2126 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource163 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue793 x + ((1 : ℝ) * Sparse.eval nodeValue794 x + ((1 : ℝ) * Sparse.eval nodeValue796 x + ((1 : ℝ) * Sparse.eval nodeValue808 x + ((1 : ℝ) * Sparse.eval nodeValue825 x + ((1 : ℝ) * Sparse.eval nodeValue1902 x + ((1 : ℝ) * Sparse.eval nodeValue1904 x + ((1 : ℝ) * Sparse.eval nodeValue1910 x + ((1 : ℝ) * Sparse.eval nodeValue1923 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2039 x + ((1 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource164 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((2 : ℝ) * Sparse.eval nodeValue3809 x + ((2 : ℝ) * Sparse.eval nodeValue3814 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

noncomputable def reducedSource165 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1463 x + ((2 : ℝ) * Sparse.eval nodeValue1465 x + ((2 : ℝ) * Sparse.eval nodeValue1466 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

noncomputable def reducedSource166 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1463 x + ((2 : ℝ) * Sparse.eval nodeValue3170 x + ((2 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

noncomputable def reducedSource167 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2474 x + ((2 : ℝ) * Sparse.eval nodeValue3217 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

noncomputable def reducedSource168 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1466 x + ((1 : ℝ) * Sparse.eval nodeValue3174 x + ((1 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3217 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1600 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4056 x + ((4 : ℝ) * Sparse.eval nodeValue4057 x + ((4 : ℝ) * Sparse.eval nodeValue4063 x + ((4 : ℝ) * Sparse.eval nodeValue4068 x + ((12 : ℝ) * Sparse.eval nodeValue4069 x + ((1 : ℝ) * Sparse.eval nodeValue4079 x + ((4 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1601 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue940 x + ((1 : ℝ) * Sparse.eval nodeValue1820 x + ((2 : ℝ) * Sparse.eval nodeValue1971 x + ((1 : ℝ) * Sparse.eval nodeValue2063 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource1602 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2222 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2282 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1603 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue931 x + ((1 : ℝ) * Sparse.eval nodeValue1813 x + ((1 : ℝ) * Sparse.eval nodeValue1965 x + ((1 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1604 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue914 x + ((1 : ℝ) * Sparse.eval nodeValue1797 x + ((1 : ℝ) * Sparse.eval nodeValue1957 x + ((1 : ℝ) * Sparse.eval nodeValue1980 x + ((1 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1605 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue949 x + ((1 : ℝ) * Sparse.eval nodeValue1828 x + ((1 : ℝ) * Sparse.eval nodeValue1976 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1606 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2219 x + ((2 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2221 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))

noncomputable def reducedSource1607 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue925 x + ((1 : ℝ) * Sparse.eval nodeValue1808 x + ((1 : ℝ) * Sparse.eval nodeValue1961 x + ((1 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1608 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1137 x + ((1 : ℝ) * Sparse.eval nodeValue2340 x + ((1 : ℝ) * Sparse.eval nodeValue2430 x + ((1 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1609 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1948 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue3358 x + ((1 : ℝ) * Sparse.eval nodeValue3437 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1610 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1910 x + ((1 : ℝ) * Sparse.eval nodeValue1916 x + ((1 : ℝ) * Sparse.eval nodeValue1917 x + ((1 : ℝ) * Sparse.eval nodeValue1948 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1611 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1612 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue905 x + ((1 : ℝ) * Sparse.eval nodeValue1790 x + ((1 : ℝ) * Sparse.eval nodeValue1973 x + ((1 : ℝ) * Sparse.eval nodeValue2009 x + ((1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1613 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1116 x + ((1 : ℝ) * Sparse.eval nodeValue2323 x + ((1 : ℝ) * Sparse.eval nodeValue2440 x + ((2 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1614 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1940 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue3350 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3481 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1615 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue909 x + ((1 : ℝ) * Sparse.eval nodeValue1793 x + ((1 : ℝ) * Sparse.eval nodeValue1976 x + ((2 : ℝ) * Sparse.eval nodeValue2010 x + ((1 : ℝ) * Sparse.eval nodeValue2023 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1616 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1903 x + ((1 : ℝ) * Sparse.eval nodeValue1904 x + ((1 : ℝ) * Sparse.eval nodeValue1913 x + ((1 : ℝ) * Sparse.eval nodeValue1925 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1617 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue954 x + ((1 : ℝ) * Sparse.eval nodeValue1832 x + ((2 : ℝ) * Sparse.eval nodeValue1980 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1618 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue945 x + ((1 : ℝ) * Sparse.eval nodeValue1825 x + ((1 : ℝ) * Sparse.eval nodeValue1973 x + ((1 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1619 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1121 x + ((1 : ℝ) * Sparse.eval nodeValue2327 x + ((1 : ℝ) * Sparse.eval nodeValue2423 x + ((1 : ℝ) * Sparse.eval nodeValue2443 x + ((1 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1620 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1946 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue3355 x + ((1 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1621 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1622 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1923 x + ((1 : ℝ) * Sparse.eval nodeValue1927 x + ((1 : ℝ) * Sparse.eval nodeValue1928 x + ((1 : ℝ) * Sparse.eval nodeValue1949 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1623 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1146 x + ((1 : ℝ) * Sparse.eval nodeValue2346 x + ((2 : ℝ) * Sparse.eval nodeValue2435 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1624 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1951 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((2 : ℝ) * Sparse.eval nodeValue2837 x + ((1 : ℝ) * Sparse.eval nodeValue2842 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1625 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1132 x + ((1 : ℝ) * Sparse.eval nodeValue2335 x + ((1 : ℝ) * Sparse.eval nodeValue2426 x + ((1 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1626 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1917 x + ((1 : ℝ) * Sparse.eval nodeValue3343 x + ((1 : ℝ) * Sparse.eval nodeValue3368 x + ((1 : ℝ) * Sparse.eval nodeValue3385 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1627 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((2 : ℝ) * Sparse.eval nodeValue3481 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))

noncomputable def reducedSource1628 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1112 x + ((1 : ℝ) * Sparse.eval nodeValue2320 x + ((1 : ℝ) * Sparse.eval nodeValue2437 x + ((1 : ℝ) * Sparse.eval nodeValue2470 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1629 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1907 x + ((1 : ℝ) * Sparse.eval nodeValue3339 x + ((1 : ℝ) * Sparse.eval nodeValue3443 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3468 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1630 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1317 x + ((1 : ℝ) * Sparse.eval nodeValue2426 x + ((1 : ℝ) * Sparse.eval nodeValue2434 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1631 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1155 x + ((1 : ℝ) * Sparse.eval nodeValue2352 x + ((1 : ℝ) * Sparse.eval nodeValue2434 x + ((1 : ℝ) * Sparse.eval nodeValue2524 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1632 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1337 x + ((1 : ℝ) * Sparse.eval nodeValue2437 x + ((1 : ℝ) * Sparse.eval nodeValue2442 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1633 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2047 x + ((1 : ℝ) * Sparse.eval nodeValue3385 x + ((1 : ℝ) * Sparse.eval nodeValue3443 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1634 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1998 x + ((1 : ℝ) * Sparse.eval nodeValue2004 x + ((1 : ℝ) * Sparse.eval nodeValue2006 x + ((1 : ℝ) * Sparse.eval nodeValue2049 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1635 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((2 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3615 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))

noncomputable def reducedSource1636 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2006 x + ((1 : ℝ) * Sparse.eval nodeValue3339 x + ((1 : ℝ) * Sparse.eval nodeValue3343 x + ((1 : ℝ) * Sparse.eval nodeValue3353 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1637 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2118 x + ((1 : ℝ) * Sparse.eval nodeValue2121 x + ((1 : ℝ) * Sparse.eval nodeValue2123 x + ((1 : ℝ) * Sparse.eval nodeValue2129 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1638 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1148 x + ((1 : ℝ) * Sparse.eval nodeValue2347 x + ((1 : ℝ) * Sparse.eval nodeValue2425 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2542 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1639 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3432 x + ((1 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3437 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1640 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1986 x + ((1 : ℝ) * Sparse.eval nodeValue1989 x + ((1 : ℝ) * Sparse.eval nodeValue1996 x + ((1 : ℝ) * Sparse.eval nodeValue2015 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1641 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1996 x + ((1 : ℝ) * Sparse.eval nodeValue3368 x + ((1 : ℝ) * Sparse.eval nodeValue3432 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1642 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3608 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1643 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue2422 x + ((1 : ℝ) * Sparse.eval nodeValue2429 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1644 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1150 x + ((1 : ℝ) * Sparse.eval nodeValue2349 x + ((1 : ℝ) * Sparse.eval nodeValue2429 x + ((2 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1645 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2071 x + ((1 : ℝ) * Sparse.eval nodeValue2073 x + ((1 : ℝ) * Sparse.eval nodeValue2077 x + ((1 : ℝ) * Sparse.eval nodeValue2086 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))))

noncomputable def reducedSource1646 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2454 x + ((1 : ℝ) * Sparse.eval nodeValue2456 x + ((1 : ℝ) * Sparse.eval nodeValue2462 x + ((1 : ℝ) * Sparse.eval nodeValue2491 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))))

noncomputable def reducedSource1647 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1992 x + ((1 : ℝ) * Sparse.eval nodeValue1994 x + ((1 : ℝ) * Sparse.eval nodeValue2000 x + ((1 : ℝ) * Sparse.eval nodeValue2031 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1648 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4551 x + ((1 : ℝ) * Sparse.eval nodeValue4555 x + ((2 : ℝ) * Sparse.eval nodeValue4559 x + ((2 : ℝ) * Sparse.eval nodeValue4625 x + ((4 : ℝ) * Sparse.eval nodeValue4970 x + ((1 : ℝ) * Sparse.eval nodeValue4979 x + ((2 : ℝ) * Sparse.eval nodeValue5113 x + ((4 : ℝ) * Sparse.eval nodeValue5168 x + ((4 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + 0))))))))))))

noncomputable def reducedSource1649 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1136 x + ((1 : ℝ) * Sparse.eval nodeValue1140 x + ((2 : ℝ) * Sparse.eval nodeValue1145 x + ((2 : ℝ) * Sparse.eval nodeValue1307 x + ((4 : ℝ) * Sparse.eval nodeValue2815 x + ((1 : ℝ) * Sparse.eval nodeValue2820 x + ((2 : ℝ) * Sparse.eval nodeValue2894 x + ((4 : ℝ) * Sparse.eval nodeValue2963 x + ((4 : ℝ) * Sparse.eval nodeValue2965 x + ((2 : ℝ) * Sparse.eval nodeValue2968 x + ((2 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3126 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))

noncomputable def reducedSource1650 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4350 x + ((2 : ℝ) * Sparse.eval nodeValue4360 x + ((2 : ℝ) * Sparse.eval nodeValue4460 x + ((4 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4952 x + ((2 : ℝ) * Sparse.eval nodeValue5033 x + ((4 : ℝ) * Sparse.eval nodeValue5075 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))

noncomputable def reducedSource1651 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue928 x + ((2 : ℝ) * Sparse.eval nodeValue938 x + ((2 : ℝ) * Sparse.eval nodeValue1043 x + ((4 : ℝ) * Sparse.eval nodeValue2334 x + ((1 : ℝ) * Sparse.eval nodeValue2344 x + ((2 : ℝ) * Sparse.eval nodeValue2425 x + ((4 : ℝ) * Sparse.eval nodeValue2482 x + ((4 : ℝ) * Sparse.eval nodeValue2595 x + ((2 : ℝ) * Sparse.eval nodeValue2605 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue4000 x + 0))))))))))))

noncomputable def reducedSource1652 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4352 x + ((1 : ℝ) * Sparse.eval nodeValue4356 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((2 : ℝ) * Sparse.eval nodeValue4546 x + ((1 : ℝ) * Sparse.eval nodeValue4558 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((2 : ℝ) * Sparse.eval nodeValue4948 x + ((1 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4972 x + ((2 : ℝ) * Sparse.eval nodeValue5037 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + 0))))))))))))))))))))

noncomputable def reducedSource1653 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue930 x + ((1 : ℝ) * Sparse.eval nodeValue934 x + ((1 : ℝ) * Sparse.eval nodeValue939 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((2 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue1144 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((2 : ℝ) * Sparse.eval nodeValue2339 x + ((1 : ℝ) * Sparse.eval nodeValue2345 x + ((2 : ℝ) * Sparse.eval nodeValue2429 x + ((2 : ℝ) * Sparse.eval nodeValue2434 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((2 : ℝ) * Sparse.eval nodeValue2599 x + ((2 : ℝ) * Sparse.eval nodeValue2601 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((2 : ℝ) * Sparse.eval nodeValue2960 x + ((1 : ℝ) * Sparse.eval nodeValue2969 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + 0))))))))))))))))))))

noncomputable def reducedSource1654 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4841 x + ((2 : ℝ) * Sparse.eval nodeValue4843 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((4 : ℝ) * Sparse.eval nodeValue5075 x + ((4 : ℝ) * Sparse.eval nodeValue5078 x + ((2 : ℝ) * Sparse.eval nodeValue5107 x + ((2 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5128 x + ((4 : ℝ) * Sparse.eval nodeValue5139 x + ((2 : ℝ) * Sparse.eval nodeValue5171 x + 0))))))))))

noncomputable def reducedSource1655 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4237 x + ((1 : ℝ) * Sparse.eval nodeValue4240 x + ((1 : ℝ) * Sparse.eval nodeValue4243 x + ((1 : ℝ) * Sparse.eval nodeValue4276 x + ((2 : ℝ) * Sparse.eval nodeValue4538 x + ((1 : ℝ) * Sparse.eval nodeValue4557 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((2 : ℝ) * Sparse.eval nodeValue4686 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4723 x + ((2 : ℝ) * Sparse.eval nodeValue4727 x + ((2 : ℝ) * Sparse.eval nodeValue4747 x + ((2 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + 0))))))))))))))))))))

noncomputable def reducedSource1656 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue737 x + ((1 : ℝ) * Sparse.eval nodeValue740 x + ((1 : ℝ) * Sparse.eval nodeValue743 x + ((1 : ℝ) * Sparse.eval nodeValue828 x + ((2 : ℝ) * Sparse.eval nodeValue1123 x + ((1 : ℝ) * Sparse.eval nodeValue1143 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((2 : ℝ) * Sparse.eval nodeValue1812 x + ((1 : ℝ) * Sparse.eval nodeValue1819 x + ((2 : ℝ) * Sparse.eval nodeValue1877 x + ((2 : ℝ) * Sparse.eval nodeValue1881 x + ((2 : ℝ) * Sparse.eval nodeValue1926 x + ((2 : ℝ) * Sparse.eval nodeValue2110 x + ((2 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((2 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

noncomputable def reducedSource1657 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4353 x + ((1 : ℝ) * Sparse.eval nodeValue4358 x + ((1 : ℝ) * Sparse.eval nodeValue4362 x + ((2 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4374 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4464 x + ((2 : ℝ) * Sparse.eval nodeValue4699 x + ((1 : ℝ) * Sparse.eval nodeValue4705 x + ((2 : ℝ) * Sparse.eval nodeValue4772 x + ((2 : ℝ) * Sparse.eval nodeValue4777 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4853 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5175 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + 0))))))))))))))))))))

noncomputable def reducedSource1658 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1686 x + ((1 : ℝ) * Sparse.eval nodeValue1687 x + ((1 : ℝ) * Sparse.eval nodeValue1695 x + ((2 : ℝ) * Sparse.eval nodeValue1720 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1748 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((2 : ℝ) * Sparse.eval nodeValue2198 x + ((2 : ℝ) * Sparse.eval nodeValue2223 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((2 : ℝ) * Sparse.eval nodeValue2256 x + ((2 : ℝ) * Sparse.eval nodeValue2259 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2286 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource100 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1061 x + ((1 : ℝ) * Sparse.eval nodeValue1064 x + ((1 : ℝ) * Sparse.eval nodeValue1092 x + ((3 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue1445 x + ((6 : ℝ) * Sparse.eval nodeValue2497 x + ((3 : ℝ) * Sparse.eval nodeValue2520 x + ((3 : ℝ) * Sparse.eval nodeValue2642 x + ((3 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((3 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3231 x + 0))))))))))))

noncomputable def reducedSource101 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1729 x + ((3 : ℝ) * Sparse.eval nodeValue1746 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((1 : ℝ) * Sparse.eval nodeValue1757 x + ((6 : ℝ) * Sparse.eval nodeValue2207 x + ((3 : ℝ) * Sparse.eval nodeValue2230 x + ((3 : ℝ) * Sparse.eval nodeValue2266 x + ((3 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((3 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + 0))))))))))))

noncomputable def reducedSource102 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource103 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1064 x + ((3 : ℝ) * Sparse.eval nodeValue1369 x + ((1 : ℝ) * Sparse.eval nodeValue1438 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource104 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1369 x + ((2 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource105 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1059 x + ((2 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2134 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource106 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1438 x + ((3 : ℝ) * Sparse.eval nodeValue2134 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource107 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1091 x + ((3 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource108 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1059 x + ((1 : ℝ) * Sparse.eval nodeValue1064 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource109 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4500 x + ((1 : ℝ) * Sparse.eval nodeValue4508 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((6 : ℝ) * Sparse.eval nodeValue4836 x + ((3 : ℝ) * Sparse.eval nodeValue4844 x + ((3 : ℝ) * Sparse.eval nodeValue4845 x + ((3 : ℝ) * Sparse.eval nodeValue4890 x + ((3 : ℝ) * Sparse.eval nodeValue4892 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue4900 x + ((3 : ℝ) * Sparse.eval nodeValue5268 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + 0))))))))))))

noncomputable def reducedSource110 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue1438 x + ((1 : ℝ) * Sparse.eval nodeValue1454 x + ((3 : ℝ) * Sparse.eval nodeValue2136 x + ((3 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((6 : ℝ) * Sparse.eval nodeValue2716 x + ((3 : ℝ) * Sparse.eval nodeValue2734 x + ((3 : ℝ) * Sparse.eval nodeValue2755 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((3 : ℝ) * Sparse.eval nodeValue3095 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + 0))))))))))))

noncomputable def reducedSource111 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((6 : ℝ) * Sparse.eval nodeValue2197 x + ((3 : ℝ) * Sparse.eval nodeValue2218 x + ((3 : ℝ) * Sparse.eval nodeValue2222 x + ((3 : ℝ) * Sparse.eval nodeValue2247 x + ((3 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((3 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + 0))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1000 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue633 x + ((2 : ℝ) * Sparse.eval nodeValue1115 x + ((1 : ℝ) * Sparse.eval nodeValue1140 x + ((1 : ℝ) * Sparse.eval nodeValue1221 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1001 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1615 x + ((1 : ℝ) * Sparse.eval nodeValue1620 x + ((1 : ℝ) * Sparse.eval nodeValue1629 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue3298 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0)))))

noncomputable def reducedSource1002 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1752 x + ((3 : ℝ) * Sparse.eval nodeValue3298 x + ((1 : ℝ) * Sparse.eval nodeValue3313 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0)))

noncomputable def reducedSource1003 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue989 x + ((1 : ℝ) * Sparse.eval nodeValue994 x + ((1 : ℝ) * Sparse.eval nodeValue1009 x + ((1 : ℝ) * Sparse.eval nodeValue1055 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1004 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue994 x + ((2 : ℝ) * Sparse.eval nodeValue1179 x + ((1 : ℝ) * Sparse.eval nodeValue1190 x + ((1 : ℝ) * Sparse.eval nodeValue1258 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1005 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue971 x + ((1 : ℝ) * Sparse.eval nodeValue975 x + ((2 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue1019 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1006 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue975 x + ((1 : ℝ) * Sparse.eval nodeValue1194 x + ((1 : ℝ) * Sparse.eval nodeValue1202 x + ((2 : ℝ) * Sparse.eval nodeValue1211 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1007 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4187 x + ((1 : ℝ) * Sparse.eval nodeValue4194 x + ((12 : ℝ) * Sparse.eval nodeValue4555 x + ((8 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1008 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue615 x + ((1 : ℝ) * Sparse.eval nodeValue622 x + ((12 : ℝ) * Sparse.eval nodeValue1140 x + ((8 : ℝ) * Sparse.eval nodeValue1307 x + ((1 : ℝ) * Sparse.eval nodeValue3126 x + 0))))

noncomputable def reducedSource1009 (x : Master → ℝ) : ℝ :=
  (16 : ℝ) * Sparse.eval nodeValue4468 x + ((2 : ℝ) * Sparse.eval nodeValue4512 x + ((12 : ℝ) * Sparse.eval nodeValue4594 x + 0))

noncomputable def reducedSource1010 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue1051 x + ((1 : ℝ) * Sparse.eval nodeValue1096 x + ((12 : ℝ) * Sparse.eval nodeValue1221 x + ((8 : ℝ) * Sparse.eval nodeValue1275 x + ((1 : ℝ) * Sparse.eval nodeValue1456 x + 0))))

noncomputable def reducedSource1011 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1758 x + ((1 : ℝ) * Sparse.eval nodeValue3313 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0)))

noncomputable def reducedSource1012 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4156 x + ((3 : ℝ) * Sparse.eval nodeValue4159 x + ((1 : ℝ) * Sparse.eval nodeValue4163 x + ((1 : ℝ) * Sparse.eval nodeValue4187 x + ((1 : ℝ) * Sparse.eval nodeValue4189 x + ((6 : ℝ) * Sparse.eval nodeValue4330 x + ((3 : ℝ) * Sparse.eval nodeValue4356 x + ((3 : ℝ) * Sparse.eval nodeValue4370 x + ((3 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((3 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + 0))))))))))))

noncomputable def reducedSource1013 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue587 x + ((1 : ℝ) * Sparse.eval nodeValue591 x + ((1 : ℝ) * Sparse.eval nodeValue617 x + ((3 : ℝ) * Sparse.eval nodeValue633 x + ((1 : ℝ) * Sparse.eval nodeValue650 x + ((6 : ℝ) * Sparse.eval nodeValue1118 x + ((3 : ℝ) * Sparse.eval nodeValue1142 x + ((3 : ℝ) * Sparse.eval nodeValue1173 x + ((3 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1308 x + ((3 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue1450 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + 0))))))))))))

noncomputable def reducedSource1014 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1516 x + ((3 : ℝ) * Sparse.eval nodeValue1532 x + ((1 : ℝ) * Sparse.eval nodeValue1534 x + ((1 : ℝ) * Sparse.eval nodeValue1537 x + ((1 : ℝ) * Sparse.eval nodeValue1540 x + ((6 : ℝ) * Sparse.eval nodeValue1672 x + ((3 : ℝ) * Sparse.eval nodeValue1692 x + ((3 : ℝ) * Sparse.eval nodeValue1722 x + ((3 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((3 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + 0))))))))))))

noncomputable def reducedSource1015 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue591 x + ((3 : ℝ) * Sparse.eval nodeValue628 x + ((1 : ℝ) * Sparse.eval nodeValue643 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource1016 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue628 x + ((2 : ℝ) * Sparse.eval nodeValue908 x + ((1 : ℝ) * Sparse.eval nodeValue934 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1017 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue584 x + ((2 : ℝ) * Sparse.eval nodeValue908 x + ((1 : ℝ) * Sparse.eval nodeValue948 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1018 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue643 x + ((3 : ℝ) * Sparse.eval nodeValue948 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource1019 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue615 x + ((3 : ℝ) * Sparse.eval nodeValue934 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((1 : ℝ) * Sparse.eval nodeValue1089 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource1020 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4108 x + ((1 : ℝ) * Sparse.eval nodeValue4112 x + ((1 : ℝ) * Sparse.eval nodeValue4134 x + ((3 : ℝ) * Sparse.eval nodeValue4146 x + ((1 : ℝ) * Sparse.eval nodeValue4181 x + ((6 : ℝ) * Sparse.eval nodeValue4293 x + ((3 : ℝ) * Sparse.eval nodeValue4315 x + ((3 : ℝ) * Sparse.eval nodeValue4356 x + ((3 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((3 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + 0))))))))))))

noncomputable def reducedSource1021 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue545 x + ((1 : ℝ) * Sparse.eval nodeValue549 x + ((1 : ℝ) * Sparse.eval nodeValue564 x + ((3 : ℝ) * Sparse.eval nodeValue574 x + ((1 : ℝ) * Sparse.eval nodeValue609 x + ((6 : ℝ) * Sparse.eval nodeValue871 x + ((3 : ℝ) * Sparse.eval nodeValue893 x + ((3 : ℝ) * Sparse.eval nodeValue934 x + ((3 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((3 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + 0))))))))))))

noncomputable def reducedSource1022 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue855 x + ((3 : ℝ) * Sparse.eval nodeValue1620 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1758 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0))))

noncomputable def reducedSource1023 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue826 x + ((1 : ℝ) * Sparse.eval nodeValue832 x + ((1 : ℝ) * Sparse.eval nodeValue859 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1024 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue564 x + ((3 : ℝ) * Sparse.eval nodeValue726 x + ((1 : ℝ) * Sparse.eval nodeValue832 x + ((1 : ℝ) * Sparse.eval nodeValue859 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

noncomputable def reducedSource1025 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue832 x + ((3 : ℝ) * Sparse.eval nodeValue1186 x + ((1 : ℝ) * Sparse.eval nodeValue1289 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

noncomputable def reducedSource1026 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue785 x + ((1 : ℝ) * Sparse.eval nodeValue791 x + ((2 : ℝ) * Sparse.eval nodeValue812 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

noncomputable def reducedSource1027 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue545 x + ((2 : ℝ) * Sparse.eval nodeValue705 x + ((1 : ℝ) * Sparse.eval nodeValue740 x + ((1 : ℝ) * Sparse.eval nodeValue791 x + ((1 : ℝ) * Sparse.eval nodeValue812 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1028 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue791 x + ((2 : ℝ) * Sparse.eval nodeValue1199 x + ((2 : ℝ) * Sparse.eval nodeValue1231 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

noncomputable def reducedSource1029 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue979 x + ((1 : ℝ) * Sparse.eval nodeValue986 x + ((1 : ℝ) * Sparse.eval nodeValue1007 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((1 : ℝ) * Sparse.eval nodeValue2208 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1030 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4085 x + ((8 : ℝ) * Sparse.eval nodeValue4181 x + ((1 : ℝ) * Sparse.eval nodeValue4194 x + ((12 : ℝ) * Sparse.eval nodeValue4350 x + ((8 : ℝ) * Sparse.eval nodeValue4501 x + 0))))

noncomputable def reducedSource1031 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue1521 x + ((1 : ℝ) * Sparse.eval nodeValue1541 x + ((12 : ℝ) * Sparse.eval nodeValue1677 x + ((8 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource1032 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue609 x + ((1 : ℝ) * Sparse.eval nodeValue622 x + ((1 : ℝ) * Sparse.eval nodeValue1096 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

noncomputable def reducedSource1033 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4072 x + ((8 : ℝ) * Sparse.eval nodeValue4274 x + ((12 : ℝ) * Sparse.eval nodeValue4405 x + ((8 : ℝ) * Sparse.eval nodeValue4468 x + ((1 : ℝ) * Sparse.eval nodeValue4629 x + 0))))

noncomputable def reducedSource1034 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4070 x + ((3 : ℝ) * Sparse.eval nodeValue4103 x + ((1 : ℝ) * Sparse.eval nodeValue4112 x + ((1 : ℝ) * Sparse.eval nodeValue4131 x + ((3 : ℝ) * Sparse.eval nodeValue4142 x + ((1 : ℝ) * Sparse.eval nodeValue4168 x + ((6 : ℝ) * Sparse.eval nodeValue4198 x + ((3 : ℝ) * Sparse.eval nodeValue4222 x + ((3 : ℝ) * Sparse.eval nodeValue4235 x + ((3 : ℝ) * Sparse.eval nodeValue4266 x + ((3 : ℝ) * Sparse.eval nodeValue4421 x + ((1 : ℝ) * Sparse.eval nodeValue4493 x + ((1 : ℝ) * Sparse.eval nodeValue4501 x + 0))))))))))))

noncomputable def reducedSource1035 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue665 x + ((1 : ℝ) * Sparse.eval nodeValue686 x + ((1 : ℝ) * Sparse.eval nodeValue691 x + ((6 : ℝ) * Sparse.eval nodeValue750 x + ((3 : ℝ) * Sparse.eval nodeValue765 x + ((3 : ℝ) * Sparse.eval nodeValue770 x + ((3 : ℝ) * Sparse.eval nodeValue801 x + ((3 : ℝ) * Sparse.eval nodeValue809 x + ((1 : ℝ) * Sparse.eval nodeValue845 x + ((3 : ℝ) * Sparse.eval nodeValue1002 x + ((1 : ℝ) * Sparse.eval nodeValue1077 x + ((1 : ℝ) * Sparse.eval nodeValue1085 x + ((1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))))))))))

noncomputable def reducedSource1036 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue549 x + ((3 : ℝ) * Sparse.eval nodeValue570 x + ((1 : ℝ) * Sparse.eval nodeValue596 x + ((1 : ℝ) * Sparse.eval nodeValue817 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

noncomputable def reducedSource1037 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue540 x + ((2 : ℝ) * Sparse.eval nodeValue701 x + ((1 : ℝ) * Sparse.eval nodeValue735 x + ((1 : ℝ) * Sparse.eval nodeValue809 x + ((1 : ℝ) * Sparse.eval nodeValue817 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1038 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue596 x + ((3 : ℝ) * Sparse.eval nodeValue735 x + ((1 : ℝ) * Sparse.eval nodeValue817 x + ((1 : ℝ) * Sparse.eval nodeValue1077 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

noncomputable def reducedSource1039 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4060 x + ((1 : ℝ) * Sparse.eval nodeValue4062 x + ((12 : ℝ) * Sparse.eval nodeValue4066 x + ((8 : ℝ) * Sparse.eval nodeValue4070 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1040 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue621 x + ((3 : ℝ) * Sparse.eval nodeValue940 x + ((1 : ℝ) * Sparse.eval nodeValue1092 x + ((1 : ℝ) * Sparse.eval nodeValue1094 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource1041 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1093 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((3 : ℝ) * Sparse.eval nodeValue2064 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

noncomputable def reducedSource1042 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

noncomputable def reducedSource1043 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue860 x + ((3 : ℝ) * Sparse.eval nodeValue1628 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

noncomputable def reducedSource1044 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue612 x + ((2 : ℝ) * Sparse.eval nodeValue931 x + ((1 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1061 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1045 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue590 x + ((2 : ℝ) * Sparse.eval nodeValue914 x + ((1 : ℝ) * Sparse.eval nodeValue954 x + ((1 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1046 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue951 x + ((2 : ℝ) * Sparse.eval nodeValue1336 x + ((1 : ℝ) * Sparse.eval nodeValue1348 x + ((1 : ℝ) * Sparse.eval nodeValue1408 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1047 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1072 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((2 : ℝ) * Sparse.eval nodeValue2045 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1048 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1049 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue853 x + ((2 : ℝ) * Sparse.eval nodeValue1619 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1050 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue606 x + ((2 : ℝ) * Sparse.eval nodeValue925 x + ((1 : ℝ) * Sparse.eval nodeValue1059 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1051 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1142 x + ((2 : ℝ) * Sparse.eval nodeValue1317 x + ((1 : ℝ) * Sparse.eval nodeValue1324 x + ((1 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1052 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1952 x + ((2 : ℝ) * Sparse.eval nodeValue3242 x + ((1 : ℝ) * Sparse.eval nodeValue3247 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1053 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue808 x + ((1 : ℝ) * Sparse.eval nodeValue814 x + ((1 : ℝ) * Sparse.eval nodeValue815 x + ((1 : ℝ) * Sparse.eval nodeValue857 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1054 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1055 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue857 x + ((2 : ℝ) * Sparse.eval nodeValue1624 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1056 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue815 x + ((2 : ℝ) * Sparse.eval nodeValue1604 x + ((1 : ℝ) * Sparse.eval nodeValue1652 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1057 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue936 x + ((2 : ℝ) * Sparse.eval nodeValue1315 x + ((1 : ℝ) * Sparse.eval nodeValue1323 x + ((1 : ℝ) * Sparse.eval nodeValue1369 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1058 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1011 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((1 : ℝ) * Sparse.eval nodeValue1952 x + ((2 : ℝ) * Sparse.eval nodeValue2005 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1059 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue581 x + ((1 : ℝ) * Sparse.eval nodeValue905 x + ((1 : ℝ) * Sparse.eval nodeValue945 x + ((1 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1060 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1118 x + ((1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue1333 x + ((1 : ℝ) * Sparse.eval nodeValue1337 x + ((1 : ℝ) * Sparse.eval nodeValue1388 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1061 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue1942 x + ((1 : ℝ) * Sparse.eval nodeValue3279 x + ((1 : ℝ) * Sparse.eval nodeValue3283 x + ((2 : ℝ) * Sparse.eval nodeValue3300 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1062 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue847 x + ((1 : ℝ) * Sparse.eval nodeValue1613 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue1744 x + ((2 : ℝ) * Sparse.eval nodeValue1750 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1063 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue804 x + ((1 : ℝ) * Sparse.eval nodeValue1596 x + ((1 : ℝ) * Sparse.eval nodeValue1643 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((2 : ℝ) * Sparse.eval nodeValue1725 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1064 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue585 x + ((1 : ℝ) * Sparse.eval nodeValue909 x + ((1 : ℝ) * Sparse.eval nodeValue949 x + ((2 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1065 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue911 x + ((1 : ℝ) * Sparse.eval nodeValue1326 x + ((1 : ℝ) * Sparse.eval nodeValue1332 x + ((1 : ℝ) * Sparse.eval nodeValue1336 x + ((1 : ℝ) * Sparse.eval nodeValue1385 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1066 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue997 x + ((1 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue1942 x + ((1 : ℝ) * Sparse.eval nodeValue1995 x + ((2 : ℝ) * Sparse.eval nodeValue2226 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1067 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1355 x + ((1 : ℝ) * Sparse.eval nodeValue1902 x + ((1 : ℝ) * Sparse.eval nodeValue1915 x + ((1 : ℝ) * Sparse.eval nodeValue1926 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue3024 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1068 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1132 x + ((1 : ℝ) * Sparse.eval nodeValue1142 x + ((1 : ℝ) * Sparse.eval nodeValue1145 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1069 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue636 x + ((1 : ℝ) * Sparse.eval nodeValue1145 x + ((2 : ℝ) * Sparse.eval nodeValue1155 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1070 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue641 x + ((2 : ℝ) * Sparse.eval nodeValue1159 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1071 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1643 x + ((1 : ℝ) * Sparse.eval nodeValue1647 x + ((1 : ℝ) * Sparse.eval nodeValue1652 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1072 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1619 x + ((1 : ℝ) * Sparse.eval nodeValue1628 x + ((1 : ℝ) * Sparse.eval nodeValue1630 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1073 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1756 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((3 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

noncomputable def reducedSource1074 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1725 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1075 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1630 x + ((1 : ℝ) * Sparse.eval nodeValue3247 x + ((2 : ℝ) * Sparse.eval nodeValue3283 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1076 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1258 x + ((2 : ℝ) * Sparse.eval nodeValue2119 x + ((1 : ℝ) * Sparse.eval nodeValue2130 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1077 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1111 x + ((1 : ℝ) * Sparse.eval nodeValue1115 x + ((1 : ℝ) * Sparse.eval nodeValue1119 x + ((1 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1078 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue626 x + ((1 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue1148 x + ((1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1079 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue630 x + ((1 : ℝ) * Sparse.eval nodeValue1136 x + ((1 : ℝ) * Sparse.eval nodeValue1150 x + ((2 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1080 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1112 x + ((1 : ℝ) * Sparse.eval nodeValue1118 x + ((1 : ℝ) * Sparse.eval nodeValue1120 x + ((1 : ℝ) * Sparse.eval nodeValue1136 x + ((1 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1081 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1613 x + ((1 : ℝ) * Sparse.eval nodeValue1617 x + ((1 : ℝ) * Sparse.eval nodeValue1619 x + ((1 : ℝ) * Sparse.eval nodeValue1624 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))))

noncomputable def reducedSource1082 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1596 x + ((1 : ℝ) * Sparse.eval nodeValue1599 x + ((1 : ℝ) * Sparse.eval nodeValue1604 x + ((1 : ℝ) * Sparse.eval nodeValue1617 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))))

noncomputable def reducedSource1083 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1084 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1617 x + ((1 : ℝ) * Sparse.eval nodeValue3242 x + ((1 : ℝ) * Sparse.eval nodeValue3279 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1085 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1599 x + ((1 : ℝ) * Sparse.eval nodeValue1995 x + ((1 : ℝ) * Sparse.eval nodeValue2005 x + ((1 : ℝ) * Sparse.eval nodeValue2045 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))))

noncomputable def reducedSource1086 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1211 x + ((1 : ℝ) * Sparse.eval nodeValue2070 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2087 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1087 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1181 x + ((1 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2453 x + ((1 : ℝ) * Sparse.eval nodeValue2492 x + ((1 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1088 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1178 x + ((1 : ℝ) * Sparse.eval nodeValue1181 x + ((1 : ℝ) * Sparse.eval nodeValue1182 x + ((1 : ℝ) * Sparse.eval nodeValue1188 x + ((1 : ℝ) * Sparse.eval nodeValue1257 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1089 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1179 x + ((1 : ℝ) * Sparse.eval nodeValue1991 x + ((1 : ℝ) * Sparse.eval nodeValue2003 x + ((1 : ℝ) * Sparse.eval nodeValue2032 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1090 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1195 x + ((2 : ℝ) * Sparse.eval nodeValue2449 x + ((1 : ℝ) * Sparse.eval nodeValue2469 x + ((1 : ℝ) * Sparse.eval nodeValue2691 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

noncomputable def reducedSource1091 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1195 x + ((1 : ℝ) * Sparse.eval nodeValue1196 x + ((1 : ℝ) * Sparse.eval nodeValue1200 x + ((2 : ℝ) * Sparse.eval nodeValue1210 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

noncomputable def reducedSource1092 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1194 x + ((2 : ℝ) * Sparse.eval nodeValue1987 x + ((1 : ℝ) * Sparse.eval nodeValue2008 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2693 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1093 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4183 x + ((1 : ℝ) * Sparse.eval nodeValue4187 x + ((1 : ℝ) * Sparse.eval nodeValue4192 x + ((6 : ℝ) * Sparse.eval nodeValue4551 x + ((3 : ℝ) * Sparse.eval nodeValue4555 x + ((3 : ℝ) * Sparse.eval nodeValue4559 x + ((3 : ℝ) * Sparse.eval nodeValue4623 x + ((3 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((1 : ℝ) * Sparse.eval nodeValue4629 x + ((3 : ℝ) * Sparse.eval nodeValue5171 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + 0))))))))))))

noncomputable def reducedSource1094 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue611 x + ((1 : ℝ) * Sparse.eval nodeValue615 x + ((1 : ℝ) * Sparse.eval nodeValue620 x + ((6 : ℝ) * Sparse.eval nodeValue1136 x + ((3 : ℝ) * Sparse.eval nodeValue1140 x + ((3 : ℝ) * Sparse.eval nodeValue1145 x + ((3 : ℝ) * Sparse.eval nodeValue1305 x + ((3 : ℝ) * Sparse.eval nodeValue1307 x + ((1 : ℝ) * Sparse.eval nodeValue1311 x + ((1 : ℝ) * Sparse.eval nodeValue1313 x + ((3 : ℝ) * Sparse.eval nodeValue2965 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3126 x + 0))))))))))))

noncomputable def reducedSource1095 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4177 x + ((1 : ℝ) * Sparse.eval nodeValue4181 x + ((1 : ℝ) * Sparse.eval nodeValue4191 x + ((3 : ℝ) * Sparse.eval nodeValue4356 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((6 : ℝ) * Sparse.eval nodeValue4546 x + ((3 : ℝ) * Sparse.eval nodeValue4558 x + ((3 : ℝ) * Sparse.eval nodeValue4608 x + ((3 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + ((3 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + 0))))))))))))

noncomputable def reducedSource1096 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue605 x + ((1 : ℝ) * Sparse.eval nodeValue609 x + ((1 : ℝ) * Sparse.eval nodeValue619 x + ((3 : ℝ) * Sparse.eval nodeValue934 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((6 : ℝ) * Sparse.eval nodeValue1131 x + ((3 : ℝ) * Sparse.eval nodeValue1144 x + ((3 : ℝ) * Sparse.eval nodeValue1242 x + ((3 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + ((3 : ℝ) * Sparse.eval nodeValue2601 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + 0))))))))))))

noncomputable def reducedSource1097 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4460 x + ((3 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4501 x + ((2 : ℝ) * Sparse.eval nodeValue4505 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((6 : ℝ) * Sparse.eval nodeValue4591 x + ((3 : ℝ) * Sparse.eval nodeValue4605 x + ((6 : ℝ) * Sparse.eval nodeValue4608 x + ((3 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + 0))))))))))

noncomputable def reducedSource1098 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1089 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((6 : ℝ) * Sparse.eval nodeValue1217 x + ((3 : ℝ) * Sparse.eval nodeValue1242 x + ((3 : ℝ) * Sparse.eval nodeValue1243 x + ((3 : ℝ) * Sparse.eval nodeValue1269 x + ((3 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((1 : ℝ) * Sparse.eval nodeValue1308 x + ((3 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue1450 x + ((1 : ℝ) * Sparse.eval nodeValue1452 x + 0))))))))))))

noncomputable def reducedSource1099 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((1 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

noncomputable def reducedSource1100 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((1 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

noncomputable def reducedSource1101 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1754 x + ((3 : ℝ) * Sparse.eval nodeValue3300 x + ((2 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))

noncomputable def reducedSource1102 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4184 x + ((1 : ℝ) * Sparse.eval nodeValue4189 x + ((1 : ℝ) * Sparse.eval nodeValue4193 x + ((3 : ℝ) * Sparse.eval nodeValue4370 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((6 : ℝ) * Sparse.eval nodeValue4552 x + ((3 : ℝ) * Sparse.eval nodeValue4560 x + ((3 : ℝ) * Sparse.eval nodeValue4605 x + ((3 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4626 x + ((3 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + 0))))))))))))

noncomputable def reducedSource1103 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue612 x + ((1 : ℝ) * Sparse.eval nodeValue617 x + ((1 : ℝ) * Sparse.eval nodeValue621 x + ((6 : ℝ) * Sparse.eval nodeValue1137 x + ((3 : ℝ) * Sparse.eval nodeValue1142 x + ((3 : ℝ) * Sparse.eval nodeValue1146 x + ((3 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1275 x + ((3 : ℝ) * Sparse.eval nodeValue1306 x + ((1 : ℝ) * Sparse.eval nodeValue1310 x + ((3 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3125 x + 0))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1104 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1530 x + ((1 : ℝ) * Sparse.eval nodeValue1531 x + ((1 : ℝ) * Sparse.eval nodeValue1540 x + ((3 : ℝ) * Sparse.eval nodeValue1722 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((6 : ℝ) * Sparse.eval nodeValue2200 x + ((3 : ℝ) * Sparse.eval nodeValue2226 x + ((3 : ℝ) * Sparse.eval nodeValue2258 x + ((3 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((3 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2780 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + 0))))))))))))

noncomputable def reducedSource1105 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue639 x + ((1 : ℝ) * Sparse.eval nodeValue643 x + ((1 : ℝ) * Sparse.eval nodeValue654 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource1106 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue639 x + ((2 : ℝ) * Sparse.eval nodeValue1157 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue1292 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1107 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue948 x + ((2 : ℝ) * Sparse.eval nodeValue1157 x + ((1 : ℝ) * Sparse.eval nodeValue1174 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1108 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4166 x + ((1 : ℝ) * Sparse.eval nodeValue4168 x + ((1 : ℝ) * Sparse.eval nodeValue4190 x + ((3 : ℝ) * Sparse.eval nodeValue4240 x + ((1 : ℝ) * Sparse.eval nodeValue4280 x + ((6 : ℝ) * Sparse.eval nodeValue4538 x + ((3 : ℝ) * Sparse.eval nodeValue4557 x + ((3 : ℝ) * Sparse.eval nodeValue4572 x + ((3 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((3 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))

noncomputable def reducedSource1109 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue594 x + ((1 : ℝ) * Sparse.eval nodeValue596 x + ((1 : ℝ) * Sparse.eval nodeValue618 x + ((3 : ℝ) * Sparse.eval nodeValue740 x + ((1 : ℝ) * Sparse.eval nodeValue832 x + ((6 : ℝ) * Sparse.eval nodeValue1123 x + ((3 : ℝ) * Sparse.eval nodeValue1143 x + ((3 : ℝ) * Sparse.eval nodeValue1190 x + ((3 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1311 x + ((3 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0))))))))))))

noncomputable def reducedSource1110 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1037 x + ((1 : ℝ) * Sparse.eval nodeValue1077 x + ((1 : ℝ) * Sparse.eval nodeValue1085 x + ((6 : ℝ) * Sparse.eval nodeValue1211 x + ((3 : ℝ) * Sparse.eval nodeValue1231 x + ((3 : ℝ) * Sparse.eval nodeValue1239 x + ((3 : ℝ) * Sparse.eval nodeValue1258 x + ((3 : ℝ) * Sparse.eval nodeValue1264 x + ((1 : ℝ) * Sparse.eval nodeValue1289 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((3 : ℝ) * Sparse.eval nodeValue1408 x + ((1 : ℝ) * Sparse.eval nodeValue1438 x + ((1 : ℝ) * Sparse.eval nodeValue1445 x + 0))))))))))))

noncomputable def reducedSource1111 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((1 : ℝ) * Sparse.eval nodeValue1092 x + ((6 : ℝ) * Sparse.eval nodeValue1218 x + ((3 : ℝ) * Sparse.eval nodeValue1243 x + ((3 : ℝ) * Sparse.eval nodeValue1244 x + ((3 : ℝ) * Sparse.eval nodeValue1271 x + ((3 : ℝ) * Sparse.eval nodeValue1272 x + ((1 : ℝ) * Sparse.eval nodeValue1307 x + ((1 : ℝ) * Sparse.eval nodeValue1309 x + ((3 : ℝ) * Sparse.eval nodeValue1417 x + ((1 : ℝ) * Sparse.eval nodeValue1452 x + ((1 : ℝ) * Sparse.eval nodeValue1453 x + 0))))))))))))

noncomputable def reducedSource1112 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1077 x + ((3 : ℝ) * Sparse.eval nodeValue1647 x + ((1 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

noncomputable def reducedSource1113 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1289 x + ((3 : ℝ) * Sparse.eval nodeValue1657 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((1 : ℝ) * Sparse.eval nodeValue2780 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

noncomputable def reducedSource1114 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4153 x + ((1 : ℝ) * Sparse.eval nodeValue4156 x + ((1 : ℝ) * Sparse.eval nodeValue4161 x + ((1 : ℝ) * Sparse.eval nodeValue4178 x + ((2 : ℝ) * Sparse.eval nodeValue4528 x + ((2 : ℝ) * Sparse.eval nodeValue4531 x + ((2 : ℝ) * Sparse.eval nodeValue4535 x + ((2 : ℝ) * Sparse.eval nodeValue4546 x + ((2 : ℝ) * Sparse.eval nodeValue4547 x + ((1 : ℝ) * Sparse.eval nodeValue4555 x + ((1 : ℝ) * Sparse.eval nodeValue4558 x + ((2 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4594 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + 0))))))))))))))))))))

noncomputable def reducedSource1115 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue581 x + ((1 : ℝ) * Sparse.eval nodeValue584 x + ((1 : ℝ) * Sparse.eval nodeValue589 x + ((1 : ℝ) * Sparse.eval nodeValue606 x + ((2 : ℝ) * Sparse.eval nodeValue1112 x + ((2 : ℝ) * Sparse.eval nodeValue1115 x + ((2 : ℝ) * Sparse.eval nodeValue1120 x + ((2 : ℝ) * Sparse.eval nodeValue1132 x + ((2 : ℝ) * Sparse.eval nodeValue1165 x + ((1 : ℝ) * Sparse.eval nodeValue1168 x + ((1 : ℝ) * Sparse.eval nodeValue1176 x + ((2 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1221 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((2 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue1302 x + ((2 : ℝ) * Sparse.eval nodeValue2939 x + ((1 : ℝ) * Sparse.eval nodeValue3002 x + ((1 : ℝ) * Sparse.eval nodeValue3090 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + 0))))))))))))))))))))

noncomputable def reducedSource1116 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1514 x + ((1 : ℝ) * Sparse.eval nodeValue1516 x + ((1 : ℝ) * Sparse.eval nodeValue1520 x + ((1 : ℝ) * Sparse.eval nodeValue1533 x + ((2 : ℝ) * Sparse.eval nodeValue3260 x + ((2 : ℝ) * Sparse.eval nodeValue3262 x + ((2 : ℝ) * Sparse.eval nodeValue3264 x + ((2 : ℝ) * Sparse.eval nodeValue3266 x + ((2 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3275 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3298 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((2 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3484 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + 0))))))))))))))))))))

noncomputable def reducedSource1117 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue626 x + ((1 : ℝ) * Sparse.eval nodeValue633 x + ((1 : ℝ) * Sparse.eval nodeValue635 x + ((1 : ℝ) * Sparse.eval nodeValue641 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1118 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1115 x + ((1 : ℝ) * Sparse.eval nodeValue1148 x + ((1 : ℝ) * Sparse.eval nodeValue1154 x + ((1 : ℝ) * Sparse.eval nodeValue1159 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1119 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue1140 x + ((1 : ℝ) * Sparse.eval nodeValue1144 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue2517 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource112 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1094 x + ((3 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource113 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4253 x + ((1 : ℝ) * Sparse.eval nodeValue4257 x + ((2 : ℝ) * Sparse.eval nodeValue4270 x + ((2 : ℝ) * Sparse.eval nodeValue4583 x + ((2 : ℝ) * Sparse.eval nodeValue4605 x + ((2 : ℝ) * Sparse.eval nodeValue4729 x + ((4 : ℝ) * Sparse.eval nodeValue4742 x + ((4 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4843 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + 0)))))))))))))

noncomputable def reducedSource114 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue791 x + ((2 : ℝ) * Sparse.eval nodeValue813 x + ((2 : ℝ) * Sparse.eval nodeValue1202 x + ((2 : ℝ) * Sparse.eval nodeValue1239 x + ((2 : ℝ) * Sparse.eval nodeValue1898 x + ((4 : ℝ) * Sparse.eval nodeValue1915 x + ((4 : ℝ) * Sparse.eval nodeValue2025 x + ((2 : ℝ) * Sparse.eval nodeValue2062 x + ((2 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2266 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + 0)))))))))))))

noncomputable def reducedSource115 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4440 x + ((2 : ℝ) * Sparse.eval nodeValue4442 x + ((1 : ℝ) * Sparse.eval nodeValue4445 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((2 : ℝ) * Sparse.eval nodeValue4464 x + ((2 : ℝ) * Sparse.eval nodeValue4792 x + ((4 : ℝ) * Sparse.eval nodeValue4807 x + ((4 : ℝ) * Sparse.eval nodeValue4853 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + 0)))))))))))))

noncomputable def reducedSource116 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue1027 x + ((2 : ℝ) * Sparse.eval nodeValue1047 x + ((2 : ℝ) * Sparse.eval nodeValue1388 x + ((2 : ℝ) * Sparse.eval nodeValue1413 x + ((2 : ℝ) * Sparse.eval nodeValue2471 x + ((4 : ℝ) * Sparse.eval nodeValue2486 x + ((4 : ℝ) * Sparse.eval nodeValue2574 x + ((2 : ℝ) * Sparse.eval nodeValue2602 x + ((2 : ℝ) * Sparse.eval nodeValue2754 x + ((2 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((2 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0)))))))))))))

noncomputable def reducedSource117 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1723 x + ((2 : ℝ) * Sparse.eval nodeValue1744 x + ((2 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1749 x + ((2 : ℝ) * Sparse.eval nodeValue1750 x + ((2 : ℝ) * Sparse.eval nodeValue2201 x + ((4 : ℝ) * Sparse.eval nodeValue2224 x + ((4 : ℝ) * Sparse.eval nodeValue2259 x + ((2 : ℝ) * Sparse.eval nodeValue2262 x + ((2 : ℝ) * Sparse.eval nodeValue2287 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + ((2 : ℝ) * Sparse.eval nodeValue2738 x + ((2 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + 0)))))))))))))

noncomputable def reducedSource118 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue3623 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource119 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1027 x + ((2 : ℝ) * Sparse.eval nodeValue1385 x + ((2 : ℝ) * Sparse.eval nodeValue1408 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource120 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1385 x + ((1 : ℝ) * Sparse.eval nodeValue2009 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource121 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue2009 x + ((2 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource122 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1408 x + ((2 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource123 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1046 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource124 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue1027 x + ((2 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource125 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4494 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((2 : ℝ) * Sparse.eval nodeValue4500 x + ((2 : ℝ) * Sparse.eval nodeValue4830 x + ((2 : ℝ) * Sparse.eval nodeValue4832 x + ((4 : ℝ) * Sparse.eval nodeValue4836 x + ((2 : ℝ) * Sparse.eval nodeValue4886 x + ((5 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4892 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue4899 x + ((2 : ℝ) * Sparse.eval nodeValue5252 x + ((2 : ℝ) * Sparse.eval nodeValue5296 x + 0))))))))))))

noncomputable def reducedSource126 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1435 x + ((2 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue1451 x + ((2 : ℝ) * Sparse.eval nodeValue2235 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2255 x + ((2 : ℝ) * Sparse.eval nodeValue2707 x + ((2 : ℝ) * Sparse.eval nodeValue2712 x + ((4 : ℝ) * Sparse.eval nodeValue2716 x + ((4 : ℝ) * Sparse.eval nodeValue2755 x + ((2 : ℝ) * Sparse.eval nodeValue2770 x + ((2 : ℝ) * Sparse.eval nodeValue2778 x + ((2 : ℝ) * Sparse.eval nodeValue3082 x + ((2 : ℝ) * Sparse.eval nodeValue3114 x + 0)))))))))))))

noncomputable def reducedSource127 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1700 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((2 : ℝ) * Sparse.eval nodeValue1716 x + ((2 : ℝ) * Sparse.eval nodeValue2187 x + ((2 : ℝ) * Sparse.eval nodeValue2193 x + ((4 : ℝ) * Sparse.eval nodeValue2197 x + ((2 : ℝ) * Sparse.eval nodeValue2235 x + ((4 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2255 x + ((2 : ℝ) * Sparse.eval nodeValue2268 x + ((2 : ℝ) * Sparse.eval nodeValue2281 x + ((2 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((2 : ℝ) * Sparse.eval nodeValue2770 x + 0)))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1120 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4144 x + ((1 : ℝ) * Sparse.eval nodeValue4146 x + ((1 : ℝ) * Sparse.eval nodeValue4148 x + ((1 : ℝ) * Sparse.eval nodeValue4177 x + ((2 : ℝ) * Sparse.eval nodeValue4293 x + ((1 : ℝ) * Sparse.eval nodeValue4315 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((2 : ℝ) * Sparse.eval nodeValue4517 x + ((1 : ℝ) * Sparse.eval nodeValue4520 x + ((2 : ℝ) * Sparse.eval nodeValue4523 x + ((2 : ℝ) * Sparse.eval nodeValue4526 x + ((2 : ℝ) * Sparse.eval nodeValue4546 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((2 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + 0))))))))))))))))))))

noncomputable def reducedSource1121 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue572 x + ((1 : ℝ) * Sparse.eval nodeValue574 x + ((1 : ℝ) * Sparse.eval nodeValue576 x + ((1 : ℝ) * Sparse.eval nodeValue605 x + ((2 : ℝ) * Sparse.eval nodeValue871 x + ((1 : ℝ) * Sparse.eval nodeValue893 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((2 : ℝ) * Sparse.eval nodeValue1101 x + ((1 : ℝ) * Sparse.eval nodeValue1104 x + ((2 : ℝ) * Sparse.eval nodeValue1107 x + ((2 : ℝ) * Sparse.eval nodeValue1110 x + ((2 : ℝ) * Sparse.eval nodeValue1131 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + 0))))))))))))))))))))

noncomputable def reducedSource1122 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1617 x + ((1 : ℝ) * Sparse.eval nodeValue1625 x + ((1 : ℝ) * Sparse.eval nodeValue1630 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1123 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4157 x + ((1 : ℝ) * Sparse.eval nodeValue4159 x + ((1 : ℝ) * Sparse.eval nodeValue4162 x + ((1 : ℝ) * Sparse.eval nodeValue4184 x + ((2 : ℝ) * Sparse.eval nodeValue4330 x + ((1 : ℝ) * Sparse.eval nodeValue4356 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((2 : ℝ) * Sparse.eval nodeValue4532 x + ((2 : ℝ) * Sparse.eval nodeValue4536 x + ((2 : ℝ) * Sparse.eval nodeValue4543 x + ((2 : ℝ) * Sparse.eval nodeValue4552 x + ((1 : ℝ) * Sparse.eval nodeValue4557 x + ((2 : ℝ) * Sparse.eval nodeValue4600 x + ((2 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4611 x + ((1 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + 0))))))))))))))))))))

noncomputable def reducedSource1124 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue585 x + ((1 : ℝ) * Sparse.eval nodeValue587 x + ((1 : ℝ) * Sparse.eval nodeValue590 x + ((1 : ℝ) * Sparse.eval nodeValue612 x + ((2 : ℝ) * Sparse.eval nodeValue1116 x + ((2 : ℝ) * Sparse.eval nodeValue1118 x + ((2 : ℝ) * Sparse.eval nodeValue1121 x + ((2 : ℝ) * Sparse.eval nodeValue1137 x + ((2 : ℝ) * Sparse.eval nodeValue1170 x + ((1 : ℝ) * Sparse.eval nodeValue1173 x + ((1 : ℝ) * Sparse.eval nodeValue1177 x + ((2 : ℝ) * Sparse.eval nodeValue1270 x + ((2 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1273 x + ((1 : ℝ) * Sparse.eval nodeValue1275 x + ((1 : ℝ) * Sparse.eval nodeValue1306 x + ((1 : ℝ) * Sparse.eval nodeValue1308 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue3004 x + ((1 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + 0))))))))))))))))))))

noncomputable def reducedSource1125 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1528 x + ((1 : ℝ) * Sparse.eval nodeValue1529 x + ((1 : ℝ) * Sparse.eval nodeValue1530 x + ((1 : ℝ) * Sparse.eval nodeValue1532 x + ((2 : ℝ) * Sparse.eval nodeValue1672 x + ((1 : ℝ) * Sparse.eval nodeValue1692 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((2 : ℝ) * Sparse.eval nodeValue2149 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((2 : ℝ) * Sparse.eval nodeValue2172 x + ((2 : ℝ) * Sparse.eval nodeValue2184 x + ((2 : ℝ) * Sparse.eval nodeValue2200 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((2 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((2 : ℝ) * Sparse.eval nodeValue2702 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + 0))))))))))))))))))))

noncomputable def reducedSource1126 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue624 x + ((1 : ℝ) * Sparse.eval nodeValue628 x + ((1 : ℝ) * Sparse.eval nodeValue634 x + ((1 : ℝ) * Sparse.eval nodeValue639 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1127 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue624 x + ((1 : ℝ) * Sparse.eval nodeValue1128 x + ((1 : ℝ) * Sparse.eval nodeValue1147 x + ((1 : ℝ) * Sparse.eval nodeValue1234 x + ((2 : ℝ) * Sparse.eval nodeValue1239 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1128 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue908 x + ((1 : ℝ) * Sparse.eval nodeValue1147 x + ((1 : ℝ) * Sparse.eval nodeValue1153 x + ((1 : ℝ) * Sparse.eval nodeValue1157 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1129 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue934 x + ((2 : ℝ) * Sparse.eval nodeValue1128 x + ((1 : ℝ) * Sparse.eval nodeValue1143 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue2060 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1130 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4140 x + ((1 : ℝ) * Sparse.eval nodeValue4142 x + ((1 : ℝ) * Sparse.eval nodeValue4147 x + ((1 : ℝ) * Sparse.eval nodeValue4174 x + ((2 : ℝ) * Sparse.eval nodeValue4202 x + ((1 : ℝ) * Sparse.eval nodeValue4225 x + ((1 : ℝ) * Sparse.eval nodeValue4257 x + ((2 : ℝ) * Sparse.eval nodeValue4514 x + ((1 : ℝ) * Sparse.eval nodeValue4519 x + ((2 : ℝ) * Sparse.eval nodeValue4521 x + ((2 : ℝ) * Sparse.eval nodeValue4525 x + ((2 : ℝ) * Sparse.eval nodeValue4543 x + ((2 : ℝ) * Sparse.eval nodeValue4583 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + 0))))))))))))))))))))

noncomputable def reducedSource1131 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue568 x + ((1 : ℝ) * Sparse.eval nodeValue570 x + ((1 : ℝ) * Sparse.eval nodeValue575 x + ((1 : ℝ) * Sparse.eval nodeValue602 x + ((2 : ℝ) * Sparse.eval nodeValue705 x + ((1 : ℝ) * Sparse.eval nodeValue726 x + ((1 : ℝ) * Sparse.eval nodeValue791 x + ((2 : ℝ) * Sparse.eval nodeValue1098 x + ((1 : ℝ) * Sparse.eval nodeValue1103 x + ((2 : ℝ) * Sparse.eval nodeValue1105 x + ((2 : ℝ) * Sparse.eval nodeValue1109 x + ((2 : ℝ) * Sparse.eval nodeValue1128 x + ((2 : ℝ) * Sparse.eval nodeValue1202 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + 0))))))))))))))))))))

noncomputable def reducedSource1132 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1002 x + ((2 : ℝ) * Sparse.eval nodeValue1599 x + ((1 : ℝ) * Sparse.eval nodeValue1625 x + ((1 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1133 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1231 x + ((2 : ℝ) * Sparse.eval nodeValue1637 x + ((1 : ℝ) * Sparse.eval nodeValue1650 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1134 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1191 x + ((2 : ℝ) * Sparse.eval nodeValue2391 x + ((1 : ℝ) * Sparse.eval nodeValue2407 x + ((1 : ℝ) * Sparse.eval nodeValue2680 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0)))))

noncomputable def reducedSource1135 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1185 x + ((1 : ℝ) * Sparse.eval nodeValue1191 x + ((1 : ℝ) * Sparse.eval nodeValue1193 x + ((1 : ℝ) * Sparse.eval nodeValue1288 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1136 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1190 x + ((2 : ℝ) * Sparse.eval nodeValue1924 x + ((1 : ℝ) * Sparse.eval nodeValue1950 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1137 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue893 x + ((2 : ℝ) * Sparse.eval nodeValue1098 x + ((1 : ℝ) * Sparse.eval nodeValue1103 x + ((1 : ℝ) * Sparse.eval nodeValue1190 x + ((1 : ℝ) * Sparse.eval nodeValue1950 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1138 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1184 x + ((1 : ℝ) * Sparse.eval nodeValue1190 x + ((1 : ℝ) * Sparse.eval nodeValue1192 x + ((1 : ℝ) * Sparse.eval nodeValue1287 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1139 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1186 x + ((2 : ℝ) * Sparse.eval nodeValue1608 x + ((1 : ℝ) * Sparse.eval nodeValue1627 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1140 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1203 x + ((1 : ℝ) * Sparse.eval nodeValue2377 x + ((2 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1141 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1198 x + ((1 : ℝ) * Sparse.eval nodeValue1203 x + ((1 : ℝ) * Sparse.eval nodeValue1205 x + ((2 : ℝ) * Sparse.eval nodeValue1230 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1142 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1202 x + ((1 : ℝ) * Sparse.eval nodeValue1897 x + ((2 : ℝ) * Sparse.eval nodeValue1914 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1143 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue871 x + ((1 : ℝ) * Sparse.eval nodeValue1105 x + ((1 : ℝ) * Sparse.eval nodeValue1109 x + ((1 : ℝ) * Sparse.eval nodeValue1123 x + ((1 : ℝ) * Sparse.eval nodeValue1202 x + ((1 : ℝ) * Sparse.eval nodeValue1914 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1144 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1197 x + ((1 : ℝ) * Sparse.eval nodeValue1202 x + ((1 : ℝ) * Sparse.eval nodeValue1204 x + ((2 : ℝ) * Sparse.eval nodeValue1229 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1145 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1199 x + ((1 : ℝ) * Sparse.eval nodeValue1592 x + ((2 : ℝ) * Sparse.eval nodeValue1602 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1146 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1055 x + ((2 : ℝ) * Sparse.eval nodeValue2032 x + ((1 : ℝ) * Sparse.eval nodeValue2130 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1147 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1053 x + ((1 : ℝ) * Sparse.eval nodeValue1055 x + ((1 : ℝ) * Sparse.eval nodeValue1062 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1148 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue991 x + ((1 : ℝ) * Sparse.eval nodeValue1926 x + ((1 : ℝ) * Sparse.eval nodeValue1992 x + ((1 : ℝ) * Sparse.eval nodeValue2121 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1149 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue991 x + ((1 : ℝ) * Sparse.eval nodeValue993 x + ((1 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1150 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue989 x + ((1 : ℝ) * Sparse.eval nodeValue1924 x + ((1 : ℝ) * Sparse.eval nodeValue1991 x + ((1 : ℝ) * Sparse.eval nodeValue2119 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1151 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue987 x + ((1 : ℝ) * Sparse.eval nodeValue989 x + ((1 : ℝ) * Sparse.eval nodeValue992 x + ((1 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1053 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1152 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1019 x + ((1 : ℝ) * Sparse.eval nodeValue2008 x + ((2 : ℝ) * Sparse.eval nodeValue2087 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1153 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1017 x + ((1 : ℝ) * Sparse.eval nodeValue1019 x + ((1 : ℝ) * Sparse.eval nodeValue1025 x + ((2 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1154 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue972 x + ((1 : ℝ) * Sparse.eval nodeValue1898 x + ((2 : ℝ) * Sparse.eval nodeValue2071 x + ((1 : ℝ) * Sparse.eval nodeValue2187 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

noncomputable def reducedSource1155 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue972 x + ((1 : ℝ) * Sparse.eval nodeValue974 x + ((2 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue1018 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

noncomputable def reducedSource1156 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue971 x + ((1 : ℝ) * Sparse.eval nodeValue1897 x + ((2 : ℝ) * Sparse.eval nodeValue2070 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1157 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue971 x + ((1 : ℝ) * Sparse.eval nodeValue973 x + ((2 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue1017 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1158 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4153 x + ((1 : ℝ) * Sparse.eval nodeValue4159 x + ((1 : ℝ) * Sparse.eval nodeValue4161 x + ((1 : ℝ) * Sparse.eval nodeValue4183 x + ((2 : ℝ) * Sparse.eval nodeValue4327 x + ((2 : ℝ) * Sparse.eval nodeValue4333 x + ((2 : ℝ) * Sparse.eval nodeValue4335 x + ((2 : ℝ) * Sparse.eval nodeValue4352 x + ((1 : ℝ) * Sparse.eval nodeValue4358 x + ((2 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4374 x + ((2 : ℝ) * Sparse.eval nodeValue4440 x + ((1 : ℝ) * Sparse.eval nodeValue4445 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + 0))))))))))))))))))))

noncomputable def reducedSource1159 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue626 x + ((1 : ℝ) * Sparse.eval nodeValue628 x + ((1 : ℝ) * Sparse.eval nodeValue635 x + ((1 : ℝ) * Sparse.eval nodeValue645 x + ((2 : ℝ) * Sparse.eval nodeValue911 x + ((1 : ℝ) * Sparse.eval nodeValue936 x + ((1 : ℝ) * Sparse.eval nodeValue1027 x + ((2 : ℝ) * Sparse.eval nodeValue1317 x + ((1 : ℝ) * Sparse.eval nodeValue1324 x + ((2 : ℝ) * Sparse.eval nodeValue1327 x + ((2 : ℝ) * Sparse.eval nodeValue1333 x + ((2 : ℝ) * Sparse.eval nodeValue1340 x + ((2 : ℝ) * Sparse.eval nodeValue1388 x + ((2 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue1413 x + ((1 : ℝ) * Sparse.eval nodeValue1420 x + ((1 : ℝ) * Sparse.eval nodeValue1447 x + ((2 : ℝ) * Sparse.eval nodeValue2574 x + ((1 : ℝ) * Sparse.eval nodeValue2602 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))

noncomputable def reducedSource1160 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1514 x + ((1 : ℝ) * Sparse.eval nodeValue1532 x + ((1 : ℝ) * Sparse.eval nodeValue1533 x + ((1 : ℝ) * Sparse.eval nodeValue1535 x + ((2 : ℝ) * Sparse.eval nodeValue1670 x + ((2 : ℝ) * Sparse.eval nodeValue1688 x + ((2 : ℝ) * Sparse.eval nodeValue1689 x + ((2 : ℝ) * Sparse.eval nodeValue1690 x + ((1 : ℝ) * Sparse.eval nodeValue1695 x + ((2 : ℝ) * Sparse.eval nodeValue1720 x + ((2 : ℝ) * Sparse.eval nodeValue1723 x + ((2 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1748 x + ((1 : ℝ) * Sparse.eval nodeValue1749 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue1753 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + 0))))))))))))))))))))

noncomputable def reducedSource1161 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue581 x + ((1 : ℝ) * Sparse.eval nodeValue587 x + ((1 : ℝ) * Sparse.eval nodeValue589 x + ((1 : ℝ) * Sparse.eval nodeValue611 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1162 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue611 x + ((2 : ℝ) * Sparse.eval nodeValue930 x + ((2 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource1163 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue945 x + ((1 : ℝ) * Sparse.eval nodeValue951 x + ((1 : ℝ) * Sparse.eval nodeValue953 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1164 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue905 x + ((1 : ℝ) * Sparse.eval nodeValue911 x + ((1 : ℝ) * Sparse.eval nodeValue913 x + ((1 : ℝ) * Sparse.eval nodeValue930 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1165 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4105 x + ((1 : ℝ) * Sparse.eval nodeValue4108 x + ((1 : ℝ) * Sparse.eval nodeValue4111 x + ((1 : ℝ) * Sparse.eval nodeValue4128 x + ((2 : ℝ) * Sparse.eval nodeValue4290 x + ((2 : ℝ) * Sparse.eval nodeValue4293 x + ((2 : ℝ) * Sparse.eval nodeValue4296 x + ((2 : ℝ) * Sparse.eval nodeValue4309 x + ((2 : ℝ) * Sparse.eval nodeValue4352 x + ((1 : ℝ) * Sparse.eval nodeValue4356 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + 0))))))))))))))))))))

noncomputable def reducedSource1166 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4253 x + ((1 : ℝ) * Sparse.eval nodeValue4269 x + ((1 : ℝ) * Sparse.eval nodeValue4270 x + ((1 : ℝ) * Sparse.eval nodeValue4276 x + ((2 : ℝ) * Sparse.eval nodeValue4391 x + ((2 : ℝ) * Sparse.eval nodeValue4401 x + ((2 : ℝ) * Sparse.eval nodeValue4402 x + ((2 : ℝ) * Sparse.eval nodeValue4410 x + ((2 : ℝ) * Sparse.eval nodeValue4440 x + ((2 : ℝ) * Sparse.eval nodeValue4442 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4464 x + ((1 : ℝ) * Sparse.eval nodeValue4476 x + ((1 : ℝ) * Sparse.eval nodeValue4478 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((2 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + 0))))))))))))))))))))

noncomputable def reducedSource1167 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue812 x + ((1 : ℝ) * Sparse.eval nodeValue813 x + ((1 : ℝ) * Sparse.eval nodeValue828 x + ((2 : ℝ) * Sparse.eval nodeValue972 x + ((2 : ℝ) * Sparse.eval nodeValue982 x + ((2 : ℝ) * Sparse.eval nodeValue983 x + ((2 : ℝ) * Sparse.eval nodeValue991 x + ((2 : ℝ) * Sparse.eval nodeValue1022 x + ((2 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((2 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1059 x + ((1 : ℝ) * Sparse.eval nodeValue1061 x + ((1 : ℝ) * Sparse.eval nodeValue1089 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((2 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1269 x + ((1 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1307 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1168 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue847 x + ((1 : ℝ) * Sparse.eval nodeValue851 x + ((1 : ℝ) * Sparse.eval nodeValue853 x + ((1 : ℝ) * Sparse.eval nodeValue857 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1169 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4151 x + ((1 : ℝ) * Sparse.eval nodeValue4156 x + ((1 : ℝ) * Sparse.eval nodeValue4160 x + ((1 : ℝ) * Sparse.eval nodeValue4177 x + ((2 : ℝ) * Sparse.eval nodeValue4326 x + ((2 : ℝ) * Sparse.eval nodeValue4330 x + ((2 : ℝ) * Sparse.eval nodeValue4334 x + ((2 : ℝ) * Sparse.eval nodeValue4346 x + ((2 : ℝ) * Sparse.eval nodeValue4365 x + ((1 : ℝ) * Sparse.eval nodeValue4370 x + ((1 : ℝ) * Sparse.eval nodeValue4373 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + 0))))))))))))))))))))

noncomputable def reducedSource1170 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue630 x + ((1 : ℝ) * Sparse.eval nodeValue633 x + ((1 : ℝ) * Sparse.eval nodeValue636 x + ((1 : ℝ) * Sparse.eval nodeValue647 x + ((2 : ℝ) * Sparse.eval nodeValue1118 x + ((1 : ℝ) * Sparse.eval nodeValue1142 x + ((1 : ℝ) * Sparse.eval nodeValue1275 x + ((2 : ℝ) * Sparse.eval nodeValue1320 x + ((1 : ℝ) * Sparse.eval nodeValue1325 x + ((2 : ℝ) * Sparse.eval nodeValue1329 x + ((2 : ℝ) * Sparse.eval nodeValue1334 x + ((2 : ℝ) * Sparse.eval nodeValue1342 x + ((2 : ℝ) * Sparse.eval nodeValue1414 x + ((2 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue1419 x + ((1 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue1450 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource1171 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1505 x + ((1 : ℝ) * Sparse.eval nodeValue1516 x + ((1 : ℝ) * Sparse.eval nodeValue1518 x + ((1 : ℝ) * Sparse.eval nodeValue1523 x + ((2 : ℝ) * Sparse.eval nodeValue1663 x + ((2 : ℝ) * Sparse.eval nodeValue1672 x + ((2 : ℝ) * Sparse.eval nodeValue1674 x + ((2 : ℝ) * Sparse.eval nodeValue1679 x + ((2 : ℝ) * Sparse.eval nodeValue1704 x + ((2 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1722 x + ((2 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + 0))))))))))))))))))))

noncomputable def reducedSource1172 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue579 x + ((1 : ℝ) * Sparse.eval nodeValue584 x + ((1 : ℝ) * Sparse.eval nodeValue588 x + ((1 : ℝ) * Sparse.eval nodeValue605 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1173 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue605 x + ((2 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((1 : ℝ) * Sparse.eval nodeValue1082 x + ((1 : ℝ) * Sparse.eval nodeValue1089 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1174 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue943 x + ((1 : ℝ) * Sparse.eval nodeValue948 x + ((1 : ℝ) * Sparse.eval nodeValue952 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1175 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue579 x + ((1 : ℝ) * Sparse.eval nodeValue904 x + ((1 : ℝ) * Sparse.eval nodeValue943 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((2 : ℝ) * Sparse.eval nodeValue1043 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1176 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue904 x + ((1 : ℝ) * Sparse.eval nodeValue908 x + ((1 : ℝ) * Sparse.eval nodeValue912 x + ((1 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1177 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4101 x + ((1 : ℝ) * Sparse.eval nodeValue4103 x + ((1 : ℝ) * Sparse.eval nodeValue4110 x + ((1 : ℝ) * Sparse.eval nodeValue4121 x + ((2 : ℝ) * Sparse.eval nodeValue4287 x + ((2 : ℝ) * Sparse.eval nodeValue4289 x + ((2 : ℝ) * Sparse.eval nodeValue4295 x + ((2 : ℝ) * Sparse.eval nodeValue4303 x + ((2 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4350 x + ((1 : ℝ) * Sparse.eval nodeValue4360 x + ((2 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4405 x + ((1 : ℝ) * Sparse.eval nodeValue4428 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + 0))))))))))))))))))))

noncomputable def reducedSource1178 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue538 x + ((1 : ℝ) * Sparse.eval nodeValue540 x + ((1 : ℝ) * Sparse.eval nodeValue547 x + ((1 : ℝ) * Sparse.eval nodeValue555 x + ((2 : ℝ) * Sparse.eval nodeValue865 x + ((2 : ℝ) * Sparse.eval nodeValue867 x + ((2 : ℝ) * Sparse.eval nodeValue873 x + ((2 : ℝ) * Sparse.eval nodeValue881 x + ((2 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue928 x + ((1 : ℝ) * Sparse.eval nodeValue938 x + ((2 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue986 x + ((1 : ℝ) * Sparse.eval nodeValue1009 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((2 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2598 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + 0))))))))))))))))))))

noncomputable def reducedSource1179 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue1307 x + ((2 : ℝ) * Sparse.eval nodeValue1361 x + ((1 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue1373 x + ((2 : ℝ) * Sparse.eval nodeValue1379 x + ((2 : ℝ) * Sparse.eval nodeValue1388 x + ((2 : ℝ) * Sparse.eval nodeValue1389 x + ((2 : ℝ) * Sparse.eval nodeValue1397 x + ((2 : ℝ) * Sparse.eval nodeValue1399 x + ((1 : ℝ) * Sparse.eval nodeValue1413 x + ((2 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue1417 x + ((1 : ℝ) * Sparse.eval nodeValue1450 x + ((1 : ℝ) * Sparse.eval nodeValue1452 x + ((1 : ℝ) * Sparse.eval nodeValue1471 x + ((2 : ℝ) * Sparse.eval nodeValue1478 x + ((1 : ℝ) * Sparse.eval nodeValue1484 x + ((1 : ℝ) * Sparse.eval nodeValue1485 x + 0))))))))))))))))))))

noncomputable def reducedSource1180 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1037 x + ((2 : ℝ) * Sparse.eval nodeValue2018 x + ((1 : ℝ) * Sparse.eval nodeValue2103 x + ((1 : ℝ) * Sparse.eval nodeValue2208 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1181 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue594 x + ((2 : ℝ) * Sparse.eval nodeValue916 x + ((1 : ℝ) * Sparse.eval nodeValue1007 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((1 : ℝ) * Sparse.eval nodeValue1074 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1182 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1033 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((1 : ℝ) * Sparse.eval nodeValue1048 x + ((1 : ℝ) * Sparse.eval nodeValue1074 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1183 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue731 x + ((1 : ℝ) * Sparse.eval nodeValue735 x + ((1 : ℝ) * Sparse.eval nodeValue741 x + ((1 : ℝ) * Sparse.eval nodeValue809 x + ((1 : ℝ) * Sparse.eval nodeValue1647 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1184 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue978 x + ((1 : ℝ) * Sparse.eval nodeValue983 x + ((1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1185 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue1914 x + ((1 : ℝ) * Sparse.eval nodeValue1987 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1186 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1004 x + ((1 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1187 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue979 x + ((1 : ℝ) * Sparse.eval nodeValue1911 x + ((1 : ℝ) * Sparse.eval nodeValue1986 x + ((1 : ℝ) * Sparse.eval nodeValue2018 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2208 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1188 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue864 x + ((1 : ℝ) * Sparse.eval nodeValue867 x + ((1 : ℝ) * Sparse.eval nodeValue872 x + ((1 : ℝ) * Sparse.eval nodeValue880 x + ((1 : ℝ) * Sparse.eval nodeValue979 x + ((1 : ℝ) * Sparse.eval nodeValue1911 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1189 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue976 x + ((1 : ℝ) * Sparse.eval nodeValue979 x + ((1 : ℝ) * Sparse.eval nodeValue984 x + ((1 : ℝ) * Sparse.eval nodeValue999 x + ((1 : ℝ) * Sparse.eval nodeValue1033 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1190 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue698 x + ((1 : ℝ) * Sparse.eval nodeValue701 x + ((1 : ℝ) * Sparse.eval nodeValue706 x + ((1 : ℝ) * Sparse.eval nodeValue714 x + ((1 : ℝ) * Sparse.eval nodeValue809 x + ((1 : ℝ) * Sparse.eval nodeValue1599 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))))

noncomputable def reducedSource1191 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4178 x + ((1 : ℝ) * Sparse.eval nodeValue4189 x + ((1 : ℝ) * Sparse.eval nodeValue4192 x + ((6 : ℝ) * Sparse.eval nodeValue4347 x + ((3 : ℝ) * Sparse.eval nodeValue4358 x + ((3 : ℝ) * Sparse.eval nodeValue4361 x + ((3 : ℝ) * Sparse.eval nodeValue4476 x + ((1 : ℝ) * Sparse.eval nodeValue4481 x + ((3 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((3 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + 0))))))))))))

noncomputable def reducedSource1192 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1520 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((1 : ℝ) * Sparse.eval nodeValue1540 x + ((6 : ℝ) * Sparse.eval nodeValue1676 x + ((3 : ℝ) * Sparse.eval nodeValue1694 x + ((3 : ℝ) * Sparse.eval nodeValue1695 x + ((3 : ℝ) * Sparse.eval nodeValue1728 x + ((3 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1755 x + ((1 : ℝ) * Sparse.eval nodeValue1757 x + ((3 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + 0))))))))))))

noncomputable def reducedSource1193 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue925 x + ((1 : ℝ) * Sparse.eval nodeValue936 x + ((1 : ℝ) * Sparse.eval nodeValue939 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1194 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4128 x + ((1 : ℝ) * Sparse.eval nodeValue4134 x + ((1 : ℝ) * Sparse.eval nodeValue4138 x + ((6 : ℝ) * Sparse.eval nodeValue4309 x + ((3 : ℝ) * Sparse.eval nodeValue4315 x + ((3 : ℝ) * Sparse.eval nodeValue4319 x + ((3 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((3 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((3 : ℝ) * Sparse.eval nodeValue5109 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))

noncomputable def reducedSource1195 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((3 : ℝ) * Sparse.eval nodeValue4177 x + ((1 : ℝ) * Sparse.eval nodeValue4187 x + ((1 : ℝ) * Sparse.eval nodeValue4191 x + ((6 : ℝ) * Sparse.eval nodeValue4346 x + ((3 : ℝ) * Sparse.eval nodeValue4356 x + ((3 : ℝ) * Sparse.eval nodeValue4360 x + ((3 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((3 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((3 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + 0))))))))))))

noncomputable def reducedSource1196 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1518 x + ((1 : ℝ) * Sparse.eval nodeValue1537 x + ((1 : ℝ) * Sparse.eval nodeValue1538 x + ((6 : ℝ) * Sparse.eval nodeValue1674 x + ((3 : ℝ) * Sparse.eval nodeValue1692 x + ((3 : ℝ) * Sparse.eval nodeValue1693 x + ((3 : ℝ) * Sparse.eval nodeValue1725 x + ((3 : ℝ) * Sparse.eval nodeValue1727 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1755 x + ((3 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))

noncomputable def reducedSource1197 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4085 x + ((3 : ℝ) * Sparse.eval nodeValue4174 x + ((1 : ℝ) * Sparse.eval nodeValue4181 x + ((1 : ℝ) * Sparse.eval nodeValue4190 x + ((6 : ℝ) * Sparse.eval nodeValue4343 x + ((3 : ℝ) * Sparse.eval nodeValue4350 x + ((3 : ℝ) * Sparse.eval nodeValue4359 x + ((3 : ℝ) * Sparse.eval nodeValue4496 x + ((3 : ℝ) * Sparse.eval nodeValue4501 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((1 : ℝ) * Sparse.eval nodeValue4512 x + ((3 : ℝ) * Sparse.eval nodeValue4837 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + 0))))))))))))

noncomputable def reducedSource1198 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1509 x + ((1 : ℝ) * Sparse.eval nodeValue1521 x + ((1 : ℝ) * Sparse.eval nodeValue1527 x + ((6 : ℝ) * Sparse.eval nodeValue1666 x + ((3 : ℝ) * Sparse.eval nodeValue1677 x + ((3 : ℝ) * Sparse.eval nodeValue1683 x + ((3 : ℝ) * Sparse.eval nodeValue1710 x + ((3 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((1 : ℝ) * Sparse.eval nodeValue1758 x + ((3 : ℝ) * Sparse.eval nodeValue2208 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))))))))))

noncomputable def reducedSource1199 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue602 x + ((1 : ℝ) * Sparse.eval nodeValue609 x + ((1 : ℝ) * Sparse.eval nodeValue618 x + ((1 : ℝ) * Sparse.eval nodeValue1085 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1200 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue602 x + ((2 : ℝ) * Sparse.eval nodeValue921 x + ((1 : ℝ) * Sparse.eval nodeValue1080 x + ((2 : ℝ) * Sparse.eval nodeValue1085 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource1201 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1010 x + ((1 : ℝ) * Sparse.eval nodeValue1951 x + ((2 : ℝ) * Sparse.eval nodeValue2004 x + ((1 : ℝ) * Sparse.eval nodeValue2222 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1202 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1001 x + ((1 : ℝ) * Sparse.eval nodeValue1010 x + ((1 : ℝ) * Sparse.eval nodeValue1012 x + ((1 : ℝ) * Sparse.eval nodeValue1076 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1203 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1009 x + ((1 : ℝ) * Sparse.eval nodeValue1950 x + ((2 : ℝ) * Sparse.eval nodeValue2003 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1204 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1009 x + ((1 : ℝ) * Sparse.eval nodeValue1013 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1205 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4140 x + ((1 : ℝ) * Sparse.eval nodeValue4146 x + ((1 : ℝ) * Sparse.eval nodeValue4147 x + ((1 : ℝ) * Sparse.eval nodeValue4166 x + ((2 : ℝ) * Sparse.eval nodeValue4289 x + ((2 : ℝ) * Sparse.eval nodeValue4302 x + ((1 : ℝ) * Sparse.eval nodeValue4312 x + ((1 : ℝ) * Sparse.eval nodeValue4317 x + ((2 : ℝ) * Sparse.eval nodeValue4320 x + ((2 : ℝ) * Sparse.eval nodeValue4324 x + ((2 : ℝ) * Sparse.eval nodeValue4338 x + ((2 : ℝ) * Sparse.eval nodeValue4398 x + ((1 : ℝ) * Sparse.eval nodeValue4405 x + ((2 : ℝ) * Sparse.eval nodeValue4418 x + ((1 : ℝ) * Sparse.eval nodeValue4431 x + ((1 : ℝ) * Sparse.eval nodeValue4454 x + ((1 : ℝ) * Sparse.eval nodeValue4490 x + ((2 : ℝ) * Sparse.eval nodeValue4738 x + ((1 : ℝ) * Sparse.eval nodeValue4837 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + 0))))))))))))))))))))

noncomputable def reducedSource1206 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1489 x + ((1 : ℝ) * Sparse.eval nodeValue1494 x + ((1 : ℝ) * Sparse.eval nodeValue1495 x + ((1 : ℝ) * Sparse.eval nodeValue1499 x + ((2 : ℝ) * Sparse.eval nodeValue1555 x + ((2 : ℝ) * Sparse.eval nodeValue1557 x + ((1 : ℝ) * Sparse.eval nodeValue1574 x + ((1 : ℝ) * Sparse.eval nodeValue1576 x + ((2 : ℝ) * Sparse.eval nodeValue1586 x + ((2 : ℝ) * Sparse.eval nodeValue1590 x + ((2 : ℝ) * Sparse.eval nodeValue1599 x + ((2 : ℝ) * Sparse.eval nodeValue1602 x + ((1 : ℝ) * Sparse.eval nodeValue1620 x + ((1 : ℝ) * Sparse.eval nodeValue1627 x + ((2 : ℝ) * Sparse.eval nodeValue1633 x + ((1 : ℝ) * Sparse.eval nodeValue1647 x + ((1 : ℝ) * Sparse.eval nodeValue1650 x + ((2 : ℝ) * Sparse.eval nodeValue1911 x + ((1 : ℝ) * Sparse.eval nodeValue2056 x + ((1 : ℝ) * Sparse.eval nodeValue2060 x + ((1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))))))))))))))))

noncomputable def reducedSource1207 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue867 x + ((1 : ℝ) * Sparse.eval nodeValue898 x + ((1 : ℝ) * Sparse.eval nodeValue902 x + ((1 : ℝ) * Sparse.eval nodeValue916 x + ((1 : ℝ) * Sparse.eval nodeValue1007 x + ((1 : ℝ) * Sparse.eval nodeValue1911 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1208 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue793 x + ((1 : ℝ) * Sparse.eval nodeValue795 x + ((1 : ℝ) * Sparse.eval nodeValue796 x + ((1 : ℝ) * Sparse.eval nodeValue811 x + ((1 : ℝ) * Sparse.eval nodeValue827 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1209 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue825 x + ((1 : ℝ) * Sparse.eval nodeValue829 x + ((1 : ℝ) * Sparse.eval nodeValue830 x + ((1 : ℝ) * Sparse.eval nodeValue858 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1210 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue828 x + ((2 : ℝ) * Sparse.eval nodeValue1610 x + ((1 : ℝ) * Sparse.eval nodeValue1659 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1211 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue824 x + ((1 : ℝ) * Sparse.eval nodeValue828 x + ((1 : ℝ) * Sparse.eval nodeValue831 x + ((1 : ℝ) * Sparse.eval nodeValue856 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1212 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue826 x + ((2 : ℝ) * Sparse.eval nodeValue1608 x + ((1 : ℝ) * Sparse.eval nodeValue1657 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1213 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue555 x + ((2 : ℝ) * Sparse.eval nodeValue715 x + ((1 : ℝ) * Sparse.eval nodeValue826 x + ((1 : ℝ) * Sparse.eval nodeValue852 x + ((1 : ℝ) * Sparse.eval nodeValue859 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1214 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue823 x + ((1 : ℝ) * Sparse.eval nodeValue826 x + ((1 : ℝ) * Sparse.eval nodeValue830 x + ((1 : ℝ) * Sparse.eval nodeValue852 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1215 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue546 x + ((2 : ℝ) * Sparse.eval nodeValue706 x + ((1 : ℝ) * Sparse.eval nodeValue741 x + ((1 : ℝ) * Sparse.eval nodeValue809 x + ((1 : ℝ) * Sparse.eval nodeValue815 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1216 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue776 x + ((1 : ℝ) * Sparse.eval nodeValue778 x + ((3 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue1698 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1217 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue1593 x + ((2 : ℝ) * Sparse.eval nodeValue1639 x + ((1 : ℝ) * Sparse.eval nodeValue1700 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1218 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue542 x + ((1 : ℝ) * Sparse.eval nodeValue702 x + ((1 : ℝ) * Sparse.eval nodeValue737 x + ((2 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue810 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1219 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue790 x + ((2 : ℝ) * Sparse.eval nodeValue810 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1220 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue785 x + ((1 : ℝ) * Sparse.eval nodeValue1592 x + ((2 : ℝ) * Sparse.eval nodeValue1637 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1221 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue538 x + ((1 : ℝ) * Sparse.eval nodeValue699 x + ((1 : ℝ) * Sparse.eval nodeValue733 x + ((1 : ℝ) * Sparse.eval nodeValue785 x + ((1 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue812 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1222 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue782 x + ((1 : ℝ) * Sparse.eval nodeValue785 x + ((1 : ℝ) * Sparse.eval nodeValue789 x + ((2 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1223 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue536 x + ((1 : ℝ) * Sparse.eval nodeValue698 x + ((1 : ℝ) * Sparse.eval nodeValue731 x + ((1 : ℝ) * Sparse.eval nodeValue804 x + ((2 : ℝ) * Sparse.eval nodeValue809 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

noncomputable def reducedSource1224 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue813 x + ((2 : ℝ) * Sparse.eval nodeValue1603 x + ((1 : ℝ) * Sparse.eval nodeValue1651 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1225 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue548 x + ((2 : ℝ) * Sparse.eval nodeValue708 x + ((1 : ℝ) * Sparse.eval nodeValue743 x + ((1 : ℝ) * Sparse.eval nodeValue813 x + ((1 : ℝ) * Sparse.eval nodeValue816 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1226 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue807 x + ((1 : ℝ) * Sparse.eval nodeValue813 x + ((1 : ℝ) * Sparse.eval nodeValue816 x + ((1 : ℝ) * Sparse.eval nodeValue856 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1227 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4069 x + ((2 : ℝ) * Sparse.eval nodeValue4101 x + ((1 : ℝ) * Sparse.eval nodeValue4108 x + ((1 : ℝ) * Sparse.eval nodeValue4110 x + ((1 : ℝ) * Sparse.eval nodeValue4127 x + ((2 : ℝ) * Sparse.eval nodeValue4196 x + ((2 : ℝ) * Sparse.eval nodeValue4202 x + ((2 : ℝ) * Sparse.eval nodeValue4204 x + ((2 : ℝ) * Sparse.eval nodeValue4218 x + ((2 : ℝ) * Sparse.eval nodeValue4233 x + ((1 : ℝ) * Sparse.eval nodeValue4240 x + ((1 : ℝ) * Sparse.eval nodeValue4242 x + ((2 : ℝ) * Sparse.eval nodeValue4251 x + ((1 : ℝ) * Sparse.eval nodeValue4257 x + ((2 : ℝ) * Sparse.eval nodeValue4264 x + ((1 : ℝ) * Sparse.eval nodeValue4269 x + ((1 : ℝ) * Sparse.eval nodeValue4273 x + ((2 : ℝ) * Sparse.eval nodeValue4418 x + ((1 : ℝ) * Sparse.eval nodeValue4490 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + 0))))))))))))))))))))

noncomputable def reducedSource1228 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue663 x + ((1 : ℝ) * Sparse.eval nodeValue683 x + ((1 : ℝ) * Sparse.eval nodeValue684 x + ((1 : ℝ) * Sparse.eval nodeValue688 x + ((2 : ℝ) * Sparse.eval nodeValue748 x + ((2 : ℝ) * Sparse.eval nodeValue762 x + ((2 : ℝ) * Sparse.eval nodeValue763 x + ((2 : ℝ) * Sparse.eval nodeValue767 x + ((2 : ℝ) * Sparse.eval nodeValue799 x + ((2 : ℝ) * Sparse.eval nodeValue804 x + ((2 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue842 x + ((1 : ℝ) * Sparse.eval nodeValue843 x + ((1 : ℝ) * Sparse.eval nodeValue849 x + ((1 : ℝ) * Sparse.eval nodeValue851 x + ((1 : ℝ) * Sparse.eval nodeValue852 x + ((2 : ℝ) * Sparse.eval nodeValue999 x + ((1 : ℝ) * Sparse.eval nodeValue1074 x + ((1 : ℝ) * Sparse.eval nodeValue1080 x + ((1 : ℝ) * Sparse.eval nodeValue1082 x + ((1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))))))))))))))))

noncomputable def reducedSource1229 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue812 x + ((2 : ℝ) * Sparse.eval nodeValue1602 x + ((1 : ℝ) * Sparse.eval nodeValue1650 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1230 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue733 x + ((1 : ℝ) * Sparse.eval nodeValue740 x + ((1 : ℝ) * Sparse.eval nodeValue742 x + ((1 : ℝ) * Sparse.eval nodeValue812 x + ((1 : ℝ) * Sparse.eval nodeValue1650 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1231 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4070 x + ((2 : ℝ) * Sparse.eval nodeValue4099 x + ((1 : ℝ) * Sparse.eval nodeValue4103 x + ((1 : ℝ) * Sparse.eval nodeValue4109 x + ((1 : ℝ) * Sparse.eval nodeValue4120 x + ((2 : ℝ) * Sparse.eval nodeValue4195 x + ((2 : ℝ) * Sparse.eval nodeValue4198 x + ((2 : ℝ) * Sparse.eval nodeValue4203 x + ((2 : ℝ) * Sparse.eval nodeValue4211 x + ((2 : ℝ) * Sparse.eval nodeValue4231 x + ((1 : ℝ) * Sparse.eval nodeValue4235 x + ((1 : ℝ) * Sparse.eval nodeValue4241 x + ((2 : ℝ) * Sparse.eval nodeValue4251 x + ((2 : ℝ) * Sparse.eval nodeValue4266 x + ((1 : ℝ) * Sparse.eval nodeValue4269 x + ((1 : ℝ) * Sparse.eval nodeValue4272 x + ((1 : ℝ) * Sparse.eval nodeValue4274 x + ((2 : ℝ) * Sparse.eval nodeValue4398 x + ((1 : ℝ) * Sparse.eval nodeValue4454 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4501 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1232 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4071 x + ((3 : ℝ) * Sparse.eval nodeValue4121 x + ((1 : ℝ) * Sparse.eval nodeValue4134 x + ((1 : ℝ) * Sparse.eval nodeValue4137 x + ((6 : ℝ) * Sparse.eval nodeValue4212 x + ((3 : ℝ) * Sparse.eval nodeValue4225 x + ((3 : ℝ) * Sparse.eval nodeValue4228 x + ((3 : ℝ) * Sparse.eval nodeValue4272 x + ((3 : ℝ) * Sparse.eval nodeValue4273 x + ((1 : ℝ) * Sparse.eval nodeValue4280 x + ((3 : ℝ) * Sparse.eval nodeValue4431 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + 0))))))))))))

noncomputable def reducedSource1233 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4070 x + ((3 : ℝ) * Sparse.eval nodeValue4122 x + ((1 : ℝ) * Sparse.eval nodeValue4136 x + ((1 : ℝ) * Sparse.eval nodeValue4138 x + ((6 : ℝ) * Sparse.eval nodeValue4213 x + ((3 : ℝ) * Sparse.eval nodeValue4227 x + ((3 : ℝ) * Sparse.eval nodeValue4229 x + ((3 : ℝ) * Sparse.eval nodeValue4269 x + ((3 : ℝ) * Sparse.eval nodeValue4270 x + ((1 : ℝ) * Sparse.eval nodeValue4285 x + ((3 : ℝ) * Sparse.eval nodeValue4428 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + 0))))))))))))

noncomputable def reducedSource1234 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4058 x + ((1 : ℝ) * Sparse.eval nodeValue4060 x + ((1 : ℝ) * Sparse.eval nodeValue4061 x + ((6 : ℝ) * Sparse.eval nodeValue4064 x + ((3 : ℝ) * Sparse.eval nodeValue4066 x + ((3 : ℝ) * Sparse.eval nodeValue4067 x + ((3 : ℝ) * Sparse.eval nodeValue4069 x + ((3 : ℝ) * Sparse.eval nodeValue4070 x + ((1 : ℝ) * Sparse.eval nodeValue4071 x + ((1 : ℝ) * Sparse.eval nodeValue4072 x + ((3 : ℝ) * Sparse.eval nodeValue4081 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))))))))))

noncomputable def reducedSource1235 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue616 x + ((2 : ℝ) * Sparse.eval nodeValue935 x + ((1 : ℝ) * Sparse.eval nodeValue1063 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1236 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1318 x + ((1 : ℝ) * Sparse.eval nodeValue1324 x + ((1 : ℝ) * Sparse.eval nodeValue1325 x + ((1 : ℝ) * Sparse.eval nodeValue1375 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1237 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1238 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue858 x + ((2 : ℝ) * Sparse.eval nodeValue1626 x + ((2 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

noncomputable def reducedSource1239 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue830 x + ((2 : ℝ) * Sparse.eval nodeValue1611 x + ((1 : ℝ) * Sparse.eval nodeValue1660 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1240 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue586 x + ((1 : ℝ) * Sparse.eval nodeValue910 x + ((1 : ℝ) * Sparse.eval nodeValue950 x + ((1 : ℝ) * Sparse.eval nodeValue1026 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1241 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1328 x + ((1 : ℝ) * Sparse.eval nodeValue1333 x + ((1 : ℝ) * Sparse.eval nodeValue1334 x + ((1 : ℝ) * Sparse.eval nodeValue1338 x + ((1 : ℝ) * Sparse.eval nodeValue1391 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1242 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue2397 x + ((1 : ℝ) * Sparse.eval nodeValue3280 x + ((1 : ℝ) * Sparse.eval nodeValue3284 x + ((2 : ℝ) * Sparse.eval nodeValue3301 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1243 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue848 x + ((1 : ℝ) * Sparse.eval nodeValue1614 x + ((2 : ℝ) * Sparse.eval nodeValue1736 x + ((2 : ℝ) * Sparse.eval nodeValue1751 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

noncomputable def reducedSource1244 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue823 x + ((1 : ℝ) * Sparse.eval nodeValue1606 x + ((1 : ℝ) * Sparse.eval nodeValue1655 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((2 : ℝ) * Sparse.eval nodeValue1738 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1245 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1356 x + ((1 : ℝ) * Sparse.eval nodeValue2856 x + ((1 : ℝ) * Sparse.eval nodeValue2911 x + ((1 : ℝ) * Sparse.eval nodeValue2970 x + ((2 : ℝ) * Sparse.eval nodeValue3025 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1246 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1133 x + ((1 : ℝ) * Sparse.eval nodeValue1143 x + ((1 : ℝ) * Sparse.eval nodeValue1146 x + ((1 : ℝ) * Sparse.eval nodeValue1245 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1247 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue653 x + ((2 : ℝ) * Sparse.eval nodeValue1171 x + ((1 : ℝ) * Sparse.eval nodeValue1273 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1306 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1248 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1655 x + ((1 : ℝ) * Sparse.eval nodeValue1657 x + ((1 : ℝ) * Sparse.eval nodeValue1660 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1249 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1741 x + ((3 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2780 x + ((1 : ℝ) * Sparse.eval nodeValue3311 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

noncomputable def reducedSource1250 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1627 x + ((2 : ℝ) * Sparse.eval nodeValue2397 x + ((1 : ℝ) * Sparse.eval nodeValue2409 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1251 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((2 : ℝ) * Sparse.eval nodeValue3295 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3311 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1252 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1113 x + ((1 : ℝ) * Sparse.eval nodeValue1119 x + ((1 : ℝ) * Sparse.eval nodeValue1121 x + ((1 : ℝ) * Sparse.eval nodeValue1138 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1253 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue631 x + ((1 : ℝ) * Sparse.eval nodeValue1138 x + ((1 : ℝ) * Sparse.eval nodeValue1151 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1254 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1606 x + ((1 : ℝ) * Sparse.eval nodeValue1608 x + ((1 : ℝ) * Sparse.eval nodeValue1611 x + ((1 : ℝ) * Sparse.eval nodeValue1618 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue3295 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))))

noncomputable def reducedSource1255 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1114 x + ((2 : ℝ) * Sparse.eval nodeValue1120 x + ((1 : ℝ) * Sparse.eval nodeValue1139 x + ((1 : ℝ) * Sparse.eval nodeValue1220 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1256 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue632 x + ((1 : ℝ) * Sparse.eval nodeValue1139 x + ((1 : ℝ) * Sparse.eval nodeValue1152 x + ((1 : ℝ) * Sparse.eval nodeValue1220 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1257 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1614 x + ((2 : ℝ) * Sparse.eval nodeValue1618 x + ((1 : ℝ) * Sparse.eval nodeValue1626 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue3297 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1258 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1751 x + ((2 : ℝ) * Sparse.eval nodeValue3297 x + ((2 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3312 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

noncomputable def reducedSource1259 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1182 x + ((1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue2533 x + ((1 : ℝ) * Sparse.eval nodeValue2608 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1260 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1196 x + ((2 : ℝ) * Sparse.eval nodeValue2452 x + ((1 : ℝ) * Sparse.eval nodeValue2609 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2695 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

noncomputable def reducedSource1261 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4185 x + ((1 : ℝ) * Sparse.eval nodeValue4190 x + ((1 : ℝ) * Sparse.eval nodeValue4192 x + ((6 : ℝ) * Sparse.eval nodeValue4553 x + ((3 : ℝ) * Sparse.eval nodeValue4557 x + ((3 : ℝ) * Sparse.eval nodeValue4559 x + ((3 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((3 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((3 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))

noncomputable def reducedSource1262 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue613 x + ((1 : ℝ) * Sparse.eval nodeValue618 x + ((1 : ℝ) * Sparse.eval nodeValue620 x + ((6 : ℝ) * Sparse.eval nodeValue1138 x + ((3 : ℝ) * Sparse.eval nodeValue1143 x + ((3 : ℝ) * Sparse.eval nodeValue1145 x + ((3 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((3 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue1307 x + ((3 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + 0))))))))))))

noncomputable def reducedSource1263 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4510 x + ((2 : ℝ) * Sparse.eval nodeValue4511 x + ((6 : ℝ) * Sparse.eval nodeValue4592 x + ((6 : ℝ) * Sparse.eval nodeValue4611 x + ((6 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4626 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + 0)))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1264 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue1094 x + ((1 : ℝ) * Sparse.eval nodeValue1095 x + ((6 : ℝ) * Sparse.eval nodeValue1219 x + ((3 : ℝ) * Sparse.eval nodeValue1245 x + ((3 : ℝ) * Sparse.eval nodeValue1246 x + ((3 : ℝ) * Sparse.eval nodeValue1273 x + ((3 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue1310 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + ((3 : ℝ) * Sparse.eval nodeValue1419 x + ((1 : ℝ) * Sparse.eval nodeValue1454 x + ((1 : ℝ) * Sparse.eval nodeValue1455 x + 0))))))))))))

noncomputable def reducedSource1265 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1755 x + ((3 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3311 x + ((1 : ℝ) * Sparse.eval nodeValue3312 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

noncomputable def reducedSource1266 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4186 x + ((2 : ℝ) * Sparse.eval nodeValue4191 x + ((6 : ℝ) * Sparse.eval nodeValue4554 x + ((6 : ℝ) * Sparse.eval nodeValue4558 x + ((6 : ℝ) * Sparse.eval nodeValue4624 x + ((2 : ℝ) * Sparse.eval nodeValue4625 x + ((3 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5309 x + 0)))))))

noncomputable def reducedSource1267 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue614 x + ((2 : ℝ) * Sparse.eval nodeValue619 x + ((6 : ℝ) * Sparse.eval nodeValue1139 x + ((6 : ℝ) * Sparse.eval nodeValue1144 x + ((6 : ℝ) * Sparse.eval nodeValue1301 x + ((2 : ℝ) * Sparse.eval nodeValue1304 x + ((3 : ℝ) * Sparse.eval nodeValue2969 x + ((2 : ℝ) * Sparse.eval nodeValue3123 x + 0)))))))

noncomputable def reducedSource1268 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue4467 x + ((4 : ℝ) * Sparse.eval nodeValue4511 x + ((6 : ℝ) * Sparse.eval nodeValue4593 x + ((12 : ℝ) * Sparse.eval nodeValue4612 x + ((2 : ℝ) * Sparse.eval nodeValue4627 x + 0))))

noncomputable def reducedSource1269 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1050 x + ((2 : ℝ) * Sparse.eval nodeValue1095 x + ((6 : ℝ) * Sparse.eval nodeValue1220 x + ((6 : ℝ) * Sparse.eval nodeValue1246 x + ((6 : ℝ) * Sparse.eval nodeValue1274 x + ((2 : ℝ) * Sparse.eval nodeValue1311 x + ((3 : ℝ) * Sparse.eval nodeValue1420 x + ((2 : ℝ) * Sparse.eval nodeValue1455 x + 0)))))))

noncomputable def reducedSource1270 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1751 x + ((2 : ℝ) * Sparse.eval nodeValue1755 x + ((1 : ℝ) * Sparse.eval nodeValue3312 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))

noncomputable def reducedSource1271 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4158 x + ((1 : ℝ) * Sparse.eval nodeValue4160 x + ((1 : ℝ) * Sparse.eval nodeValue4161 x + ((1 : ℝ) * Sparse.eval nodeValue4188 x + ((2 : ℝ) * Sparse.eval nodeValue4533 x + ((2 : ℝ) * Sparse.eval nodeValue4534 x + ((2 : ℝ) * Sparse.eval nodeValue4535 x + ((2 : ℝ) * Sparse.eval nodeValue4549 x + ((2 : ℝ) * Sparse.eval nodeValue4556 x + ((1 : ℝ) * Sparse.eval nodeValue4558 x + ((1 : ℝ) * Sparse.eval nodeValue4559 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + 0))))))))))))))))))))

noncomputable def reducedSource1272 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue586 x + ((1 : ℝ) * Sparse.eval nodeValue588 x + ((1 : ℝ) * Sparse.eval nodeValue589 x + ((1 : ℝ) * Sparse.eval nodeValue616 x + ((2 : ℝ) * Sparse.eval nodeValue1117 x + ((2 : ℝ) * Sparse.eval nodeValue1119 x + ((2 : ℝ) * Sparse.eval nodeValue1120 x + ((2 : ℝ) * Sparse.eval nodeValue1141 x + ((2 : ℝ) * Sparse.eval nodeValue1172 x + ((1 : ℝ) * Sparse.eval nodeValue1175 x + ((1 : ℝ) * Sparse.eval nodeValue1176 x + ((2 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((2 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1269 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((1 : ℝ) * Sparse.eval nodeValue1302 x + ((2 : ℝ) * Sparse.eval nodeValue2943 x + ((1 : ℝ) * Sparse.eval nodeValue3006 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + 0))))))))))))))))))))

noncomputable def reducedSource1273 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1522 x + ((1 : ℝ) * Sparse.eval nodeValue1523 x + ((1 : ℝ) * Sparse.eval nodeValue1526 x + ((1 : ℝ) * Sparse.eval nodeValue1533 x + ((2 : ℝ) * Sparse.eval nodeValue3265 x + ((2 : ℝ) * Sparse.eval nodeValue3267 x + ((2 : ℝ) * Sparse.eval nodeValue3268 x + ((2 : ℝ) * Sparse.eval nodeValue3271 x + ((2 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((2 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((1 : ℝ) * Sparse.eval nodeValue3485 x + ((2 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + 0))))))))))))))))))))

noncomputable def reducedSource1274 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue627 x + ((1 : ℝ) * Sparse.eval nodeValue635 x + ((1 : ℝ) * Sparse.eval nodeValue636 x + ((1 : ℝ) * Sparse.eval nodeValue642 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1275 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue627 x + ((1 : ℝ) * Sparse.eval nodeValue1134 x + ((1 : ℝ) * Sparse.eval nodeValue1149 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1276 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1149 x + ((1 : ℝ) * Sparse.eval nodeValue1154 x + ((1 : ℝ) * Sparse.eval nodeValue1155 x + ((1 : ℝ) * Sparse.eval nodeValue1160 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1277 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue642 x + ((2 : ℝ) * Sparse.eval nodeValue1160 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1278 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4145 x + ((1 : ℝ) * Sparse.eval nodeValue4147 x + ((1 : ℝ) * Sparse.eval nodeValue4148 x + ((1 : ℝ) * Sparse.eval nodeValue4180 x + ((2 : ℝ) * Sparse.eval nodeValue4518 x + ((1 : ℝ) * Sparse.eval nodeValue4519 x + ((1 : ℝ) * Sparse.eval nodeValue4520 x + ((2 : ℝ) * Sparse.eval nodeValue4524 x + ((2 : ℝ) * Sparse.eval nodeValue4525 x + ((2 : ℝ) * Sparse.eval nodeValue4526 x + ((2 : ℝ) * Sparse.eval nodeValue4549 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + 0))))))))))))))))))))

noncomputable def reducedSource1279 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue573 x + ((1 : ℝ) * Sparse.eval nodeValue575 x + ((1 : ℝ) * Sparse.eval nodeValue576 x + ((1 : ℝ) * Sparse.eval nodeValue608 x + ((2 : ℝ) * Sparse.eval nodeValue1102 x + ((1 : ℝ) * Sparse.eval nodeValue1103 x + ((1 : ℝ) * Sparse.eval nodeValue1104 x + ((2 : ℝ) * Sparse.eval nodeValue1108 x + ((2 : ℝ) * Sparse.eval nodeValue1109 x + ((2 : ℝ) * Sparse.eval nodeValue1110 x + ((2 : ℝ) * Sparse.eval nodeValue1134 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource128 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1080 x + ((2 : ℝ) * Sparse.eval nodeValue2052 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue2292 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource129 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4594 x + ((2 : ℝ) * Sparse.eval nodeValue4608 x + ((2 : ℝ) * Sparse.eval nodeValue4609 x + ((4 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((2 : ℝ) * Sparse.eval nodeValue5127 x + ((4 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5201 x + ((4 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5274 x + ((2 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + 0))))))))))))

noncomputable def reducedSource130 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1221 x + ((2 : ℝ) * Sparse.eval nodeValue1243 x + ((2 : ℝ) * Sparse.eval nodeValue1269 x + ((4 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2886 x + ((2 : ℝ) * Sparse.eval nodeValue2914 x + ((4 : ℝ) * Sparse.eval nodeValue2939 x + ((1 : ℝ) * Sparse.eval nodeValue3002 x + ((4 : ℝ) * Sparse.eval nodeValue3089 x + ((2 : ℝ) * Sparse.eval nodeValue3103 x + ((2 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))

noncomputable def reducedSource131 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3298 x + ((2 : ℝ) * Sparse.eval nodeValue3300 x + ((2 : ℝ) * Sparse.eval nodeValue3302 x + ((4 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3484 x + ((2 : ℝ) * Sparse.eval nodeValue3513 x + ((4 : ℝ) * Sparse.eval nodeValue3530 x + ((4 : ℝ) * Sparse.eval nodeValue3533 x + ((2 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((2 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + 0))))))))))))

noncomputable def reducedSource132 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue3905 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource133 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue1221 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource134 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1242 x + ((2 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2517 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource135 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1264 x + ((2 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2635 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource136 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2542 x + ((1 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource137 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4405 x + ((2 : ℝ) * Sparse.eval nodeValue4428 x + ((2 : ℝ) * Sparse.eval nodeValue4460 x + ((4 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5021 x + ((2 : ℝ) * Sparse.eval nodeValue5047 x + ((4 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((4 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + 0))))))))))))

noncomputable def reducedSource138 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue986 x + ((2 : ℝ) * Sparse.eval nodeValue1009 x + ((2 : ℝ) * Sparse.eval nodeValue1043 x + ((4 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2407 x + ((2 : ℝ) * Sparse.eval nodeValue2449 x + ((4 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2598 x + ((4 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + 0))))))))))))

noncomputable def reducedSource139 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4832 x + ((1 : ℝ) * Sparse.eval nodeValue4837 x + ((2 : ℝ) * Sparse.eval nodeValue4845 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + ((4 : ℝ) * Sparse.eval nodeValue5222 x + ((1 : ℝ) * Sparse.eval nodeValue5235 x + ((2 : ℝ) * Sparse.eval nodeValue5239 x + ((4 : ℝ) * Sparse.eval nodeValue5252 x + ((5 : ℝ) * Sparse.eval nodeValue5261 x + ((2 : ℝ) * Sparse.eval nodeValue5268 x + ((2 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + 0)))))))))))

noncomputable def reducedSource140 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2208 x + ((2 : ℝ) * Sparse.eval nodeValue2218 x + ((2 : ℝ) * Sparse.eval nodeValue2268 x + ((4 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2680 x + ((2 : ℝ) * Sparse.eval nodeValue2691 x + ((4 : ℝ) * Sparse.eval nodeValue2712 x + ((4 : ℝ) * Sparse.eval nodeValue2726 x + ((2 : ℝ) * Sparse.eval nodeValue2734 x + ((2 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue2790 x + ((1 : ℝ) * Sparse.eval nodeValue3090 x + 0))))))))))))

noncomputable def reducedSource141 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((2 : ℝ) * Sparse.eval nodeValue2734 x + ((2 : ℝ) * Sparse.eval nodeValue2770 x + ((4 : ℝ) * Sparse.eval nodeValue3031 x + ((1 : ℝ) * Sparse.eval nodeValue3046 x + ((2 : ℝ) * Sparse.eval nodeValue3061 x + ((4 : ℝ) * Sparse.eval nodeValue3082 x + ((4 : ℝ) * Sparse.eval nodeValue3090 x + ((2 : ℝ) * Sparse.eval nodeValue3095 x + ((2 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3126 x + ((1 : ℝ) * Sparse.eval nodeValue3215 x + 0))))))))))))

noncomputable def reducedSource142 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2052 x + ((1 : ℝ) * Sparse.eval nodeValue2056 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource143 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4094 x + ((8 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue4629 x + ((12 : ℝ) * Sparse.eval nodeValue5171 x + ((8 : ℝ) * Sparse.eval nodeValue5308 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1280 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1192 x + ((1 : ℝ) * Sparse.eval nodeValue2410 x + ((2 : ℝ) * Sparse.eval nodeValue2538 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1281 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1193 x + ((1 : ℝ) * Sparse.eval nodeValue2411 x + ((2 : ℝ) * Sparse.eval nodeValue2539 x + ((2 : ℝ) * Sparse.eval nodeValue2686 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0))))

noncomputable def reducedSource1282 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1099 x + ((2 : ℝ) * Sparse.eval nodeValue1104 x + ((1 : ℝ) * Sparse.eval nodeValue1193 x + ((1 : ℝ) * Sparse.eval nodeValue2411 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0))))

noncomputable def reducedSource1283 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1204 x + ((2 : ℝ) * Sparse.eval nodeValue2467 x + ((1 : ℝ) * Sparse.eval nodeValue2540 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2706 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1284 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1205 x + ((2 : ℝ) * Sparse.eval nodeValue2468 x + ((1 : ℝ) * Sparse.eval nodeValue2541 x + ((2 : ℝ) * Sparse.eval nodeValue2705 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))

noncomputable def reducedSource1285 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1106 x + ((2 : ℝ) * Sparse.eval nodeValue1110 x + ((1 : ℝ) * Sparse.eval nodeValue1124 x + ((1 : ℝ) * Sparse.eval nodeValue1205 x + ((1 : ℝ) * Sparse.eval nodeValue2468 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1286 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1062 x + ((2 : ℝ) * Sparse.eval nodeValue2038 x + ((1 : ℝ) * Sparse.eval nodeValue2137 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1287 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue992 x + ((1 : ℝ) * Sparse.eval nodeValue1928 x + ((1 : ℝ) * Sparse.eval nodeValue1993 x + ((1 : ℝ) * Sparse.eval nodeValue2122 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1288 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue993 x + ((1 : ℝ) * Sparse.eval nodeValue1929 x + ((1 : ℝ) * Sparse.eval nodeValue1994 x + ((1 : ℝ) * Sparse.eval nodeValue2123 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1289 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1025 x + ((1 : ℝ) * Sparse.eval nodeValue2011 x + ((2 : ℝ) * Sparse.eval nodeValue2093 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2246 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1290 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue973 x + ((1 : ℝ) * Sparse.eval nodeValue1900 x + ((2 : ℝ) * Sparse.eval nodeValue2072 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2192 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1291 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue974 x + ((1 : ℝ) * Sparse.eval nodeValue1901 x + ((2 : ℝ) * Sparse.eval nodeValue2073 x + ((2 : ℝ) * Sparse.eval nodeValue2191 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))

noncomputable def reducedSource1292 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1048 x + ((2 : ℝ) * Sparse.eval nodeValue2027 x + ((1 : ℝ) * Sparse.eval nodeValue2114 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1293 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4154 x + ((1 : ℝ) * Sparse.eval nodeValue4160 x + ((1 : ℝ) * Sparse.eval nodeValue4162 x + ((1 : ℝ) * Sparse.eval nodeValue4185 x + ((2 : ℝ) * Sparse.eval nodeValue4328 x + ((2 : ℝ) * Sparse.eval nodeValue4334 x + ((2 : ℝ) * Sparse.eval nodeValue4336 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((2 : ℝ) * Sparse.eval nodeValue4368 x + ((1 : ℝ) * Sparse.eval nodeValue4373 x + ((1 : ℝ) * Sparse.eval nodeValue4375 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4464 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + 0))))))))))))))))))))

noncomputable def reducedSource1294 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue631 x + ((1 : ℝ) * Sparse.eval nodeValue634 x + ((1 : ℝ) * Sparse.eval nodeValue636 x + ((1 : ℝ) * Sparse.eval nodeValue648 x + ((2 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue1323 x + ((1 : ℝ) * Sparse.eval nodeValue1325 x + ((2 : ℝ) * Sparse.eval nodeValue1330 x + ((2 : ℝ) * Sparse.eval nodeValue1332 x + ((2 : ℝ) * Sparse.eval nodeValue1334 x + ((2 : ℝ) * Sparse.eval nodeValue1343 x + ((2 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1408 x + ((2 : ℝ) * Sparse.eval nodeValue1414 x + ((1 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue1442 x + ((1 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource1295 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1511 x + ((1 : ℝ) * Sparse.eval nodeValue1523 x + ((1 : ℝ) * Sparse.eval nodeValue1525 x + ((1 : ℝ) * Sparse.eval nodeValue1529 x + ((2 : ℝ) * Sparse.eval nodeValue1667 x + ((2 : ℝ) * Sparse.eval nodeValue1679 x + ((2 : ℝ) * Sparse.eval nodeValue1681 x + ((2 : ℝ) * Sparse.eval nodeValue1685 x + ((2 : ℝ) * Sparse.eval nodeValue1707 x + ((2 : ℝ) * Sparse.eval nodeValue1712 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue1743 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((2 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1296 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue582 x + ((1 : ℝ) * Sparse.eval nodeValue588 x + ((1 : ℝ) * Sparse.eval nodeValue590 x + ((1 : ℝ) * Sparse.eval nodeValue613 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1297 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue613 x + ((2 : ℝ) * Sparse.eval nodeValue932 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue1082 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1298 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue946 x + ((1 : ℝ) * Sparse.eval nodeValue952 x + ((1 : ℝ) * Sparse.eval nodeValue954 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1299 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue582 x + ((1 : ℝ) * Sparse.eval nodeValue906 x + ((1 : ℝ) * Sparse.eval nodeValue946 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1300 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4106 x + ((1 : ℝ) * Sparse.eval nodeValue4109 x + ((1 : ℝ) * Sparse.eval nodeValue4111 x + ((1 : ℝ) * Sparse.eval nodeValue4132 x + ((2 : ℝ) * Sparse.eval nodeValue4291 x + ((2 : ℝ) * Sparse.eval nodeValue4294 x + ((2 : ℝ) * Sparse.eval nodeValue4296 x + ((2 : ℝ) * Sparse.eval nodeValue4313 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4359 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((2 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4454 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4491 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + 0))))))))))))))))))))

noncomputable def reducedSource1301 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue543 x + ((1 : ℝ) * Sparse.eval nodeValue546 x + ((1 : ℝ) * Sparse.eval nodeValue548 x + ((1 : ℝ) * Sparse.eval nodeValue562 x + ((2 : ℝ) * Sparse.eval nodeValue869 x + ((2 : ℝ) * Sparse.eval nodeValue872 x + ((2 : ℝ) * Sparse.eval nodeValue874 x + ((2 : ℝ) * Sparse.eval nodeValue891 x + ((2 : ℝ) * Sparse.eval nodeValue932 x + ((1 : ℝ) * Sparse.eval nodeValue937 x + ((1 : ℝ) * Sparse.eval nodeValue939 x + ((2 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((2 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((2 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + 0))))))))))))))))))))

noncomputable def reducedSource1302 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4155 x + ((2 : ℝ) * Sparse.eval nodeValue4161 x + ((1 : ℝ) * Sparse.eval nodeValue4186 x + ((2 : ℝ) * Sparse.eval nodeValue4329 x + ((4 : ℝ) * Sparse.eval nodeValue4335 x + ((2 : ℝ) * Sparse.eval nodeValue4355 x + ((2 : ℝ) * Sparse.eval nodeValue4369 x + ((2 : ℝ) * Sparse.eval nodeValue4374 x + ((4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((2 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + 0)))))))))))))

noncomputable def reducedSource1303 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue632 x + ((2 : ℝ) * Sparse.eval nodeValue635 x + ((1 : ℝ) * Sparse.eval nodeValue649 x + ((2 : ℝ) * Sparse.eval nodeValue1322 x + ((2 : ℝ) * Sparse.eval nodeValue1324 x + ((2 : ℝ) * Sparse.eval nodeValue1331 x + ((4 : ℝ) * Sparse.eval nodeValue1333 x + ((2 : ℝ) * Sparse.eval nodeValue1344 x + ((4 : ℝ) * Sparse.eval nodeValue1411 x + ((2 : ℝ) * Sparse.eval nodeValue1413 x + ((2 : ℝ) * Sparse.eval nodeValue1447 x + ((1 : ℝ) * Sparse.eval nodeValue3188 x + ((2 : ℝ) * Sparse.eval nodeValue3207 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0)))))))))))))

noncomputable def reducedSource1304 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1515 x + ((2 : ℝ) * Sparse.eval nodeValue1533 x + ((1 : ℝ) * Sparse.eval nodeValue1536 x + ((2 : ℝ) * Sparse.eval nodeValue1671 x + ((4 : ℝ) * Sparse.eval nodeValue1689 x + ((2 : ℝ) * Sparse.eval nodeValue1691 x + ((2 : ℝ) * Sparse.eval nodeValue1721 x + ((4 : ℝ) * Sparse.eval nodeValue1724 x + ((2 : ℝ) * Sparse.eval nodeValue1748 x + ((2 : ℝ) * Sparse.eval nodeValue1750 x + ((2 : ℝ) * Sparse.eval nodeValue1753 x + ((2 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + 0)))))))))))))

noncomputable def reducedSource1305 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue583 x + ((2 : ℝ) * Sparse.eval nodeValue589 x + ((1 : ℝ) * Sparse.eval nodeValue614 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource1306 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue614 x + ((2 : ℝ) * Sparse.eval nodeValue933 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((2 : ℝ) * Sparse.eval nodeValue1086 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource1307 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue947 x + ((2 : ℝ) * Sparse.eval nodeValue953 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource1308 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue583 x + ((1 : ℝ) * Sparse.eval nodeValue907 x + ((1 : ℝ) * Sparse.eval nodeValue947 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1309 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4107 x + ((2 : ℝ) * Sparse.eval nodeValue4110 x + ((1 : ℝ) * Sparse.eval nodeValue4133 x + ((2 : ℝ) * Sparse.eval nodeValue4292 x + ((4 : ℝ) * Sparse.eval nodeValue4295 x + ((2 : ℝ) * Sparse.eval nodeValue4314 x + ((2 : ℝ) * Sparse.eval nodeValue4355 x + ((2 : ℝ) * Sparse.eval nodeValue4360 x + ((4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4460 x + ((2 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + 0)))))))))))))

noncomputable def reducedSource1310 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4256 x + ((2 : ℝ) * Sparse.eval nodeValue4273 x + ((1 : ℝ) * Sparse.eval nodeValue4279 x + ((2 : ℝ) * Sparse.eval nodeValue4393 x + ((4 : ℝ) * Sparse.eval nodeValue4404 x + ((2 : ℝ) * Sparse.eval nodeValue4412 x + ((4 : ℝ) * Sparse.eval nodeValue4444 x + ((2 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4467 x + ((2 : ℝ) * Sparse.eval nodeValue4480 x + ((2 : ℝ) * Sparse.eval nodeValue4511 x + ((2 : ℝ) * Sparse.eval nodeValue4593 x + ((2 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + 0)))))))))))))

noncomputable def reducedSource1311 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue790 x + ((2 : ℝ) * Sparse.eval nodeValue816 x + ((1 : ℝ) * Sparse.eval nodeValue831 x + ((2 : ℝ) * Sparse.eval nodeValue974 x + ((4 : ℝ) * Sparse.eval nodeValue985 x + ((2 : ℝ) * Sparse.eval nodeValue993 x + ((4 : ℝ) * Sparse.eval nodeValue1026 x + ((2 : ℝ) * Sparse.eval nodeValue1049 x + ((2 : ℝ) * Sparse.eval nodeValue1050 x + ((2 : ℝ) * Sparse.eval nodeValue1063 x + ((2 : ℝ) * Sparse.eval nodeValue1095 x + ((2 : ℝ) * Sparse.eval nodeValue1220 x + ((2 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + 0)))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1312 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1220 x + ((2 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + ((2 : ℝ) * Sparse.eval nodeValue1363 x + ((2 : ℝ) * Sparse.eval nodeValue1375 x + ((2 : ℝ) * Sparse.eval nodeValue1381 x + ((4 : ℝ) * Sparse.eval nodeValue1391 x + ((4 : ℝ) * Sparse.eval nodeValue1401 x + ((2 : ℝ) * Sparse.eval nodeValue1419 x + ((2 : ℝ) * Sparse.eval nodeValue1420 x + ((2 : ℝ) * Sparse.eval nodeValue1455 x + ((1 : ℝ) * Sparse.eval nodeValue1473 x + ((2 : ℝ) * Sparse.eval nodeValue1479 x + ((2 : ℝ) * Sparse.eval nodeValue1486 x + 0)))))))))))))

noncomputable def reducedSource1313 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue984 x + ((1 : ℝ) * Sparse.eval nodeValue1917 x + ((1 : ℝ) * Sparse.eval nodeValue1989 x + ((1 : ℝ) * Sparse.eval nodeValue2081 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1314 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1918 x + ((1 : ℝ) * Sparse.eval nodeValue1990 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1315 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue866 x + ((1 : ℝ) * Sparse.eval nodeValue873 x + ((1 : ℝ) * Sparse.eval nodeValue874 x + ((1 : ℝ) * Sparse.eval nodeValue889 x + ((1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1918 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1316 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue710 x + ((1 : ℝ) * Sparse.eval nodeValue715 x + ((1 : ℝ) * Sparse.eval nodeValue717 x + ((1 : ℝ) * Sparse.eval nodeValue724 x + ((1 : ℝ) * Sparse.eval nodeValue852 x + ((1 : ℝ) * Sparse.eval nodeValue1618 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))))

noncomputable def reducedSource1317 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4179 x + ((1 : ℝ) * Sparse.eval nodeValue4190 x + ((1 : ℝ) * Sparse.eval nodeValue4193 x + ((6 : ℝ) * Sparse.eval nodeValue4348 x + ((3 : ℝ) * Sparse.eval nodeValue4359 x + ((3 : ℝ) * Sparse.eval nodeValue4362 x + ((3 : ℝ) * Sparse.eval nodeValue4496 x + ((3 : ℝ) * Sparse.eval nodeValue4500 x + ((1 : ℝ) * Sparse.eval nodeValue4501 x + ((1 : ℝ) * Sparse.eval nodeValue4508 x + ((3 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + 0))))))))))))

noncomputable def reducedSource1318 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue653 x + ((1 : ℝ) * Sparse.eval nodeValue654 x + ((1 : ℝ) * Sparse.eval nodeValue655 x + ((6 : ℝ) * Sparse.eval nodeValue1347 x + ((3 : ℝ) * Sparse.eval nodeValue1348 x + ((3 : ℝ) * Sparse.eval nodeValue1349 x + ((3 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue1438 x + ((3 : ℝ) * Sparse.eval nodeValue1451 x + ((1 : ℝ) * Sparse.eval nodeValue1452 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((3 : ℝ) * Sparse.eval nodeValue3095 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + 0))))))))))))

noncomputable def reducedSource1319 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1513 x + ((1 : ℝ) * Sparse.eval nodeValue1527 x + ((1 : ℝ) * Sparse.eval nodeValue1531 x + ((6 : ℝ) * Sparse.eval nodeValue1669 x + ((3 : ℝ) * Sparse.eval nodeValue1683 x + ((3 : ℝ) * Sparse.eval nodeValue1687 x + ((3 : ℝ) * Sparse.eval nodeValue1710 x + ((3 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((3 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + 0))))))))))))

noncomputable def reducedSource1320 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue607 x + ((1 : ℝ) * Sparse.eval nodeValue618 x + ((1 : ℝ) * Sparse.eval nodeValue621 x + ((1 : ℝ) * Sparse.eval nodeValue1094 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource1321 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((3 : ℝ) * Sparse.eval nodeValue4180 x + ((1 : ℝ) * Sparse.eval nodeValue4191 x + ((1 : ℝ) * Sparse.eval nodeValue4192 x + ((6 : ℝ) * Sparse.eval nodeValue4349 x + ((3 : ℝ) * Sparse.eval nodeValue4360 x + ((3 : ℝ) * Sparse.eval nodeValue4361 x + ((3 : ℝ) * Sparse.eval nodeValue4498 x + ((3 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((3 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + 0))))))))))))

noncomputable def reducedSource1322 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1519 x + ((1 : ℝ) * Sparse.eval nodeValue1538 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((6 : ℝ) * Sparse.eval nodeValue1675 x + ((3 : ℝ) * Sparse.eval nodeValue1693 x + ((3 : ℝ) * Sparse.eval nodeValue1694 x + ((3 : ℝ) * Sparse.eval nodeValue1727 x + ((3 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((3 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))

noncomputable def reducedSource1323 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue608 x + ((1 : ℝ) * Sparse.eval nodeValue619 x + ((1 : ℝ) * Sparse.eval nodeValue620 x + ((1 : ℝ) * Sparse.eval nodeValue1095 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource1324 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4071 x + ((3 : ℝ) * Sparse.eval nodeValue4273 x + ((1 : ℝ) * Sparse.eval nodeValue4284 x + ((6 : ℝ) * Sparse.eval nodeValue4404 x + ((3 : ℝ) * Sparse.eval nodeValue4431 x + ((3 : ℝ) * Sparse.eval nodeValue4432 x + ((3 : ℝ) * Sparse.eval nodeValue4466 x + ((3 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((3 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + 0))))))))))))

noncomputable def reducedSource1325 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1012 x + ((1 : ℝ) * Sparse.eval nodeValue1953 x + ((2 : ℝ) * Sparse.eval nodeValue2006 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1326 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4141 x + ((2 : ℝ) * Sparse.eval nodeValue4148 x + ((1 : ℝ) * Sparse.eval nodeValue4167 x + ((2 : ℝ) * Sparse.eval nodeValue4305 x + ((2 : ℝ) * Sparse.eval nodeValue4318 x + ((2 : ℝ) * Sparse.eval nodeValue4321 x + ((4 : ℝ) * Sparse.eval nodeValue4325 x + ((2 : ℝ) * Sparse.eval nodeValue4339 x + ((4 : ℝ) * Sparse.eval nodeValue4419 x + ((2 : ℝ) * Sparse.eval nodeValue4428 x + ((2 : ℝ) * Sparse.eval nodeValue4491 x + ((2 : ℝ) * Sparse.eval nodeValue4790 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + 0)))))))))))))

noncomputable def reducedSource1327 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue569 x + ((2 : ℝ) * Sparse.eval nodeValue576 x + ((1 : ℝ) * Sparse.eval nodeValue595 x + ((1 : ℝ) * Sparse.eval nodeValue1013 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1328 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue562 x + ((2 : ℝ) * Sparse.eval nodeValue724 x + ((1 : ℝ) * Sparse.eval nodeValue830 x + ((1 : ℝ) * Sparse.eval nodeValue852 x + ((1 : ℝ) * Sparse.eval nodeValue858 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1329 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue831 x + ((2 : ℝ) * Sparse.eval nodeValue1612 x + ((1 : ℝ) * Sparse.eval nodeValue1661 x + ((2 : ℝ) * Sparse.eval nodeValue1739 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

noncomputable def reducedSource1330 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue789 x + ((1 : ℝ) * Sparse.eval nodeValue1594 x + ((2 : ℝ) * Sparse.eval nodeValue1640 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1331 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue543 x + ((1 : ℝ) * Sparse.eval nodeValue703 x + ((1 : ℝ) * Sparse.eval nodeValue738 x + ((1 : ℝ) * Sparse.eval nodeValue789 x + ((1 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue811 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1332 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue552 x + ((1 : ℝ) * Sparse.eval nodeValue710 x + ((1 : ℝ) * Sparse.eval nodeValue823 x + ((1 : ℝ) * Sparse.eval nodeValue848 x + ((2 : ℝ) * Sparse.eval nodeValue852 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

noncomputable def reducedSource1333 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue790 x + ((1 : ℝ) * Sparse.eval nodeValue1595 x + ((2 : ℝ) * Sparse.eval nodeValue1641 x + ((2 : ℝ) * Sparse.eval nodeValue1708 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1334 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue544 x + ((1 : ℝ) * Sparse.eval nodeValue704 x + ((1 : ℝ) * Sparse.eval nodeValue739 x + ((1 : ℝ) * Sparse.eval nodeValue790 x + ((2 : ℝ) * Sparse.eval nodeValue810 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1335 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4069 x + ((2 : ℝ) * Sparse.eval nodeValue4102 x + ((1 : ℝ) * Sparse.eval nodeValue4110 x + ((1 : ℝ) * Sparse.eval nodeValue4111 x + ((1 : ℝ) * Sparse.eval nodeValue4130 x + ((2 : ℝ) * Sparse.eval nodeValue4197 x + ((2 : ℝ) * Sparse.eval nodeValue4204 x + ((2 : ℝ) * Sparse.eval nodeValue4205 x + ((2 : ℝ) * Sparse.eval nodeValue4221 x + ((2 : ℝ) * Sparse.eval nodeValue4234 x + ((1 : ℝ) * Sparse.eval nodeValue4242 x + ((1 : ℝ) * Sparse.eval nodeValue4243 x + ((2 : ℝ) * Sparse.eval nodeValue4264 x + ((2 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4269 x + ((1 : ℝ) * Sparse.eval nodeValue4270 x + ((1 : ℝ) * Sparse.eval nodeValue4283 x + ((2 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4491 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + 0))))))))))))))))))))

noncomputable def reducedSource1336 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue664 x + ((1 : ℝ) * Sparse.eval nodeValue684 x + ((1 : ℝ) * Sparse.eval nodeValue685 x + ((1 : ℝ) * Sparse.eval nodeValue689 x + ((2 : ℝ) * Sparse.eval nodeValue749 x + ((2 : ℝ) * Sparse.eval nodeValue763 x + ((2 : ℝ) * Sparse.eval nodeValue764 x + ((2 : ℝ) * Sparse.eval nodeValue768 x + ((2 : ℝ) * Sparse.eval nodeValue800 x + ((2 : ℝ) * Sparse.eval nodeValue806 x + ((2 : ℝ) * Sparse.eval nodeValue807 x + ((1 : ℝ) * Sparse.eval nodeValue843 x + ((1 : ℝ) * Sparse.eval nodeValue844 x + ((1 : ℝ) * Sparse.eval nodeValue851 x + ((1 : ℝ) * Sparse.eval nodeValue853 x + ((1 : ℝ) * Sparse.eval nodeValue856 x + ((2 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((1 : ℝ) * Sparse.eval nodeValue1082 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))))))))))))))))

noncomputable def reducedSource1337 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue816 x + ((2 : ℝ) * Sparse.eval nodeValue1605 x + ((1 : ℝ) * Sparse.eval nodeValue1653 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1338 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue539 x + ((1 : ℝ) * Sparse.eval nodeValue547 x + ((1 : ℝ) * Sparse.eval nodeValue548 x + ((1 : ℝ) * Sparse.eval nodeValue561 x + ((1 : ℝ) * Sparse.eval nodeValue816 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1339 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue734 x + ((1 : ℝ) * Sparse.eval nodeValue742 x + ((1 : ℝ) * Sparse.eval nodeValue743 x + ((1 : ℝ) * Sparse.eval nodeValue816 x + ((1 : ℝ) * Sparse.eval nodeValue1653 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1340 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4071 x + ((2 : ℝ) * Sparse.eval nodeValue4115 x + ((1 : ℝ) * Sparse.eval nodeValue4121 x + ((1 : ℝ) * Sparse.eval nodeValue4123 x + ((1 : ℝ) * Sparse.eval nodeValue4132 x + ((2 : ℝ) * Sparse.eval nodeValue4207 x + ((2 : ℝ) * Sparse.eval nodeValue4212 x + ((2 : ℝ) * Sparse.eval nodeValue4214 x + ((2 : ℝ) * Sparse.eval nodeValue4223 x + ((2 : ℝ) * Sparse.eval nodeValue4255 x + ((2 : ℝ) * Sparse.eval nodeValue4256 x + ((1 : ℝ) * Sparse.eval nodeValue4272 x + ((3 : ℝ) * Sparse.eval nodeValue4273 x + ((1 : ℝ) * Sparse.eval nodeValue4278 x + ((1 : ℝ) * Sparse.eval nodeValue4279 x + ((1 : ℝ) * Sparse.eval nodeValue4284 x + ((2 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + 0)))))))))))))))))))

noncomputable def reducedSource1341 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4059 x + ((2 : ℝ) * Sparse.eval nodeValue4061 x + ((6 : ℝ) * Sparse.eval nodeValue4065 x + ((6 : ℝ) * Sparse.eval nodeValue4067 x + ((6 : ℝ) * Sparse.eval nodeValue4069 x + ((2 : ℝ) * Sparse.eval nodeValue4070 x + ((3 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))))

noncomputable def reducedSource1342 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue2521 x + ((2 : ℝ) * Sparse.eval nodeValue3022 x + ((1 : ℝ) * Sparse.eval nodeValue3049 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1343 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1344 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue604 x + ((1 : ℝ) * Sparse.eval nodeValue923 x + ((1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1345 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1335 x + ((1 : ℝ) * Sparse.eval nodeValue1337 x + ((1 : ℝ) * Sparse.eval nodeValue1338 x + ((1 : ℝ) * Sparse.eval nodeValue1347 x + ((1 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1346 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue2502 x + ((1 : ℝ) * Sparse.eval nodeValue3285 x + ((1 : ℝ) * Sparse.eval nodeValue3287 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1347 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue824 x + ((1 : ℝ) * Sparse.eval nodeValue1607 x + ((1 : ℝ) * Sparse.eval nodeValue1656 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1348 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1349 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue807 x + ((1 : ℝ) * Sparse.eval nodeValue1598 x + ((1 : ℝ) * Sparse.eval nodeValue1646 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1350 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue601 x + ((1 : ℝ) * Sparse.eval nodeValue920 x + ((1 : ℝ) * Sparse.eval nodeValue1057 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((2 : ℝ) * Sparse.eval nodeValue1083 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1351 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1316 x + ((1 : ℝ) * Sparse.eval nodeValue1320 x + ((2 : ℝ) * Sparse.eval nodeValue1322 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1352 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1709 x + ((1 : ℝ) * Sparse.eval nodeValue3241 x + ((1 : ℝ) * Sparse.eval nodeValue3245 x + ((2 : ℝ) * Sparse.eval nodeValue3246 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1353 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1705 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((2 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1354 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue811 x + ((1 : ℝ) * Sparse.eval nodeValue1601 x + ((1 : ℝ) * Sparse.eval nodeValue1649 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1355 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1314 x + ((1 : ℝ) * Sparse.eval nodeValue1317 x + ((1 : ℝ) * Sparse.eval nodeValue1318 x + ((1 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1356 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue2466 x + ((1 : ℝ) * Sparse.eval nodeValue3238 x + ((1 : ℝ) * Sparse.eval nodeValue3240 x + ((1 : ℝ) * Sparse.eval nodeValue3245 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1357 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue827 x + ((1 : ℝ) * Sparse.eval nodeValue1609 x + ((1 : ℝ) * Sparse.eval nodeValue1658 x + ((2 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1358 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue578 x + ((1 : ℝ) * Sparse.eval nodeValue942 x + ((1 : ℝ) * Sparse.eval nodeValue1020 x + ((1 : ℝ) * Sparse.eval nodeValue1039 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1359 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1705 x + ((1 : ℝ) * Sparse.eval nodeValue3281 x + ((2 : ℝ) * Sparse.eval nodeValue3282 x + ((2 : ℝ) * Sparse.eval nodeValue3299 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1360 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue782 x + ((2 : ℝ) * Sparse.eval nodeValue784 x + ((2 : ℝ) * Sparse.eval nodeValue803 x + ((1 : ℝ) * Sparse.eval nodeValue1705 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

noncomputable def reducedSource1361 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue803 x + ((1 : ℝ) * Sparse.eval nodeValue1642 x + ((1 : ℝ) * Sparse.eval nodeValue1705 x + ((1 : ℝ) * Sparse.eval nodeValue1713 x + ((2 : ℝ) * Sparse.eval nodeValue1724 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1362 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue782 x + ((2 : ℝ) * Sparse.eval nodeValue1635 x + ((1 : ℝ) * Sparse.eval nodeValue1705 x + ((2 : ℝ) * Sparse.eval nodeValue1707 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

noncomputable def reducedSource1363 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue580 x + ((1 : ℝ) * Sparse.eval nodeValue944 x + ((2 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue1039 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1364 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue1328 x + ((1 : ℝ) * Sparse.eval nodeValue1330 x + ((1 : ℝ) * Sparse.eval nodeValue1335 x + ((1 : ℝ) * Sparse.eval nodeValue1383 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1365 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue2457 x + ((1 : ℝ) * Sparse.eval nodeValue3278 x + ((1 : ℝ) * Sparse.eval nodeValue3281 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1366 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue822 x + ((1 : ℝ) * Sparse.eval nodeValue1654 x + ((2 : ℝ) * Sparse.eval nodeValue1713 x + ((2 : ℝ) * Sparse.eval nodeValue1737 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

noncomputable def reducedSource1367 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1125 x + ((1 : ℝ) * Sparse.eval nodeValue1128 x + ((2 : ℝ) * Sparse.eval nodeValue1133 x + ((1 : ℝ) * Sparse.eval nodeValue1234 x + ((1 : ℝ) * Sparse.eval nodeValue2509 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1368 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue651 x + ((1 : ℝ) * Sparse.eval nodeValue1169 x + ((3 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue1293 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource1369 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1654 x + ((2 : ℝ) * Sparse.eval nodeValue1656 x + ((1 : ℝ) * Sparse.eval nodeValue1658 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1370 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1710 x + ((2 : ℝ) * Sparse.eval nodeValue2702 x + ((2 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

noncomputable def reducedSource1371 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1602 x + ((1 : ℝ) * Sparse.eval nodeValue2457 x + ((1 : ℝ) * Sparse.eval nodeValue2466 x + ((1 : ℝ) * Sparse.eval nodeValue2502 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1372 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1373 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1127 x + ((1 : ℝ) * Sparse.eval nodeValue1132 x + ((1 : ℝ) * Sparse.eval nodeValue1134 x + ((1 : ℝ) * Sparse.eval nodeValue1141 x + ((1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1374 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue640 x + ((1 : ℝ) * Sparse.eval nodeValue1158 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1293 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1375 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1642 x + ((1 : ℝ) * Sparse.eval nodeValue1645 x + ((1 : ℝ) * Sparse.eval nodeValue1646 x + ((1 : ℝ) * Sparse.eval nodeValue1649 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1376 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1598 x + ((1 : ℝ) * Sparse.eval nodeValue1603 x + ((1 : ℝ) * Sparse.eval nodeValue1605 x + ((1 : ℝ) * Sparse.eval nodeValue1623 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1377 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1728 x + ((2 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((1 : ℝ) * Sparse.eval nodeValue3309 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1378 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1623 x + ((1 : ℝ) * Sparse.eval nodeValue3246 x + ((1 : ℝ) * Sparse.eval nodeValue3282 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1379 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3309 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1380 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1605 x + ((1 : ℝ) * Sparse.eval nodeValue3240 x + ((1 : ℝ) * Sparse.eval nodeValue3278 x + ((1 : ℝ) * Sparse.eval nodeValue3287 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1381 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1645 x + ((1 : ℝ) * Sparse.eval nodeValue3022 x + ((1 : ℝ) * Sparse.eval nodeValue3285 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1382 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1257 x + ((1 : ℝ) * Sparse.eval nodeValue2565 x + ((1 : ℝ) * Sparse.eval nodeValue2629 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((1 : ℝ) * Sparse.eval nodeValue2760 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1383 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1130 x + ((1 : ℝ) * Sparse.eval nodeValue1137 x + ((1 : ℝ) * Sparse.eval nodeValue1138 x + ((1 : ℝ) * Sparse.eval nodeValue1141 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1384 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue638 x + ((1 : ℝ) * Sparse.eval nodeValue1156 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1385 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1635 x + ((1 : ℝ) * Sparse.eval nodeValue1637 x + ((1 : ℝ) * Sparse.eval nodeValue1640 x + ((1 : ℝ) * Sparse.eval nodeValue1645 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1386 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1607 x + ((1 : ℝ) * Sparse.eval nodeValue1610 x + ((1 : ℝ) * Sparse.eval nodeValue1612 x + ((1 : ℝ) * Sparse.eval nodeValue1623 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1387 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((2 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1388 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((2 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1389 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1111 x + ((2 : ℝ) * Sparse.eval nodeValue1113 x + ((1 : ℝ) * Sparse.eval nodeValue1126 x + ((1 : ℝ) * Sparse.eval nodeValue1212 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1390 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue623 x + ((1 : ℝ) * Sparse.eval nodeValue1126 x + ((1 : ℝ) * Sparse.eval nodeValue1212 x + ((1 : ℝ) * Sparse.eval nodeValue1233 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1391 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue629 x + ((1 : ℝ) * Sparse.eval nodeValue1135 x + ((3 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1392 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1116 x + ((2 : ℝ) * Sparse.eval nodeValue1117 x + ((1 : ℝ) * Sparse.eval nodeValue1135 x + ((1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1393 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1607 x + ((1 : ℝ) * Sparse.eval nodeValue1609 x + ((1 : ℝ) * Sparse.eval nodeValue1616 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1394 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1592 x + ((1 : ℝ) * Sparse.eval nodeValue1594 x + ((2 : ℝ) * Sparse.eval nodeValue1597 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1395 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1597 x + ((1 : ℝ) * Sparse.eval nodeValue3238 x + ((1 : ℝ) * Sparse.eval nodeValue3285 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1396 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1616 x + ((1 : ℝ) * Sparse.eval nodeValue3241 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((2 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1397 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1112 x + ((1 : ℝ) * Sparse.eval nodeValue1114 x + ((1 : ℝ) * Sparse.eval nodeValue1117 x + ((1 : ℝ) * Sparse.eval nodeValue1129 x + ((1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1398 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue625 x + ((1 : ℝ) * Sparse.eval nodeValue1129 x + ((2 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1399 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1597 x + ((1 : ℝ) * Sparse.eval nodeValue1598 x + ((1 : ℝ) * Sparse.eval nodeValue1601 x + ((1 : ℝ) * Sparse.eval nodeValue1616 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue3290 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1400 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1210 x + ((1 : ℝ) * Sparse.eval nodeValue2477 x + ((1 : ℝ) * Sparse.eval nodeValue2613 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))))

noncomputable def reducedSource1401 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1180 x + ((1 : ℝ) * Sparse.eval nodeValue2383 x + ((1 : ℝ) * Sparse.eval nodeValue2607 x + ((2 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0)))))

noncomputable def reducedSource1402 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1180 x + ((1 : ℝ) * Sparse.eval nodeValue1187 x + ((1 : ℝ) * Sparse.eval nodeValue1256 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0))))

noncomputable def reducedSource1403 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1178 x + ((1 : ℝ) * Sparse.eval nodeValue2382 x + ((1 : ℝ) * Sparse.eval nodeValue2606 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1404 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1656 x + ((1 : ℝ) * Sparse.eval nodeValue1659 x + ((1 : ℝ) * Sparse.eval nodeValue1661 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1405 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1650 x + ((2 : ℝ) * Sparse.eval nodeValue2502 x + ((1 : ℝ) * Sparse.eval nodeValue2521 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1406 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1646 x + ((1 : ℝ) * Sparse.eval nodeValue1651 x + ((1 : ℝ) * Sparse.eval nodeValue1653 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1407 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1653 x + ((1 : ℝ) * Sparse.eval nodeValue3049 x + ((2 : ℝ) * Sparse.eval nodeValue3287 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1408 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1288 x + ((2 : ℝ) * Sparse.eval nodeValue2585 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue2771 x + ((1 : ℝ) * Sparse.eval nodeValue2779 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0)))))

noncomputable def reducedSource1409 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4182 x + ((1 : ℝ) * Sparse.eval nodeValue4183 x + ((2 : ℝ) * Sparse.eval nodeValue4185 x + ((2 : ℝ) * Sparse.eval nodeValue4550 x + ((2 : ℝ) * Sparse.eval nodeValue4551 x + ((4 : ℝ) * Sparse.eval nodeValue4553 x + ((2 : ℝ) * Sparse.eval nodeValue4618 x + ((2 : ℝ) * Sparse.eval nodeValue4619 x + ((4 : ℝ) * Sparse.eval nodeValue4623 x + ((2 : ℝ) * Sparse.eval nodeValue4625 x + ((2 : ℝ) * Sparse.eval nodeValue4627 x + ((2 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5308 x + 0)))))))))))))

noncomputable def reducedSource1410 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue610 x + ((1 : ℝ) * Sparse.eval nodeValue611 x + ((2 : ℝ) * Sparse.eval nodeValue613 x + ((2 : ℝ) * Sparse.eval nodeValue1135 x + ((2 : ℝ) * Sparse.eval nodeValue1136 x + ((4 : ℝ) * Sparse.eval nodeValue1138 x + ((2 : ℝ) * Sparse.eval nodeValue1293 x + ((2 : ℝ) * Sparse.eval nodeValue1294 x + ((4 : ℝ) * Sparse.eval nodeValue1305 x + ((2 : ℝ) * Sparse.eval nodeValue1307 x + ((2 : ℝ) * Sparse.eval nodeValue1311 x + ((2 : ℝ) * Sparse.eval nodeValue2963 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((2 : ℝ) * Sparse.eval nodeValue3124 x + 0)))))))))))))

noncomputable def reducedSource1411 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4172 x + ((1 : ℝ) * Sparse.eval nodeValue4174 x + ((2 : ℝ) * Sparse.eval nodeValue4180 x + ((2 : ℝ) * Sparse.eval nodeValue4541 x + ((2 : ℝ) * Sparse.eval nodeValue4543 x + ((4 : ℝ) * Sparse.eval nodeValue4549 x + ((4 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4605 x + ((2 : ℝ) * Sparse.eval nodeValue4612 x + ((2 : ℝ) * Sparse.eval nodeValue4622 x + ((2 : ℝ) * Sparse.eval nodeValue4624 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))

noncomputable def reducedSource1412 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue600 x + ((1 : ℝ) * Sparse.eval nodeValue602 x + ((2 : ℝ) * Sparse.eval nodeValue608 x + ((2 : ℝ) * Sparse.eval nodeValue1126 x + ((2 : ℝ) * Sparse.eval nodeValue1128 x + ((4 : ℝ) * Sparse.eval nodeValue1134 x + ((4 : ℝ) * Sparse.eval nodeValue1236 x + ((2 : ℝ) * Sparse.eval nodeValue1239 x + ((2 : ℝ) * Sparse.eval nodeValue1246 x + ((2 : ℝ) * Sparse.eval nodeValue1299 x + ((2 : ℝ) * Sparse.eval nodeValue1301 x + ((2 : ℝ) * Sparse.eval nodeValue2959 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + 0)))))))))))))

noncomputable def reducedSource1413 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4589 x + ((2 : ℝ) * Sparse.eval nodeValue4600 x + ((4 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((4 : ℝ) * Sparse.eval nodeValue4607 x + ((2 : ℝ) * Sparse.eval nodeValue4617 x + ((2 : ℝ) * Sparse.eval nodeValue4619 x + ((2 : ℝ) * Sparse.eval nodeValue4624 x + 0)))))))))))))

noncomputable def reducedSource1414 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((2 : ℝ) * Sparse.eval nodeValue1087 x + ((2 : ℝ) * Sparse.eval nodeValue1216 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((4 : ℝ) * Sparse.eval nodeValue1241 x + ((4 : ℝ) * Sparse.eval nodeValue1267 x + ((2 : ℝ) * Sparse.eval nodeValue1270 x + ((2 : ℝ) * Sparse.eval nodeValue1301 x + ((2 : ℝ) * Sparse.eval nodeValue1302 x + ((2 : ℝ) * Sparse.eval nodeValue1306 x + ((2 : ℝ) * Sparse.eval nodeValue1414 x + ((2 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue1451 x + 0)))))))))))))

noncomputable def reducedSource1415 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1737 x + ((2 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue1753 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

noncomputable def reducedSource1416 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1727 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((1 : ℝ) * Sparse.eval nodeValue3309 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

noncomputable def reducedSource1417 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4175 x + ((1 : ℝ) * Sparse.eval nodeValue4177 x + ((1 : ℝ) * Sparse.eval nodeValue4180 x + ((1 : ℝ) * Sparse.eval nodeValue4186 x + ((2 : ℝ) * Sparse.eval nodeValue4544 x + ((2 : ℝ) * Sparse.eval nodeValue4546 x + ((2 : ℝ) * Sparse.eval nodeValue4549 x + ((2 : ℝ) * Sparse.eval nodeValue4554 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((2 : ℝ) * Sparse.eval nodeValue4622 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((3 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + 0)))))))))))))))))))

noncomputable def reducedSource1418 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue603 x + ((1 : ℝ) * Sparse.eval nodeValue605 x + ((1 : ℝ) * Sparse.eval nodeValue608 x + ((1 : ℝ) * Sparse.eval nodeValue614 x + ((2 : ℝ) * Sparse.eval nodeValue1129 x + ((2 : ℝ) * Sparse.eval nodeValue1131 x + ((2 : ℝ) * Sparse.eval nodeValue1134 x + ((2 : ℝ) * Sparse.eval nodeValue1139 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((2 : ℝ) * Sparse.eval nodeValue1299 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((3 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + ((2 : ℝ) * Sparse.eval nodeValue2960 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + 0)))))))))))))))))))

noncomputable def reducedSource1419 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((2 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4590 x + ((4 : ℝ) * Sparse.eval nodeValue4602 x + ((4 : ℝ) * Sparse.eval nodeValue4603 x + ((4 : ℝ) * Sparse.eval nodeValue4606 x + ((2 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((2 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + 0)))))))))))

noncomputable def reducedSource1420 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4165 x + ((1 : ℝ) * Sparse.eval nodeValue4166 x + ((1 : ℝ) * Sparse.eval nodeValue4167 x + ((1 : ℝ) * Sparse.eval nodeValue4185 x + ((2 : ℝ) * Sparse.eval nodeValue4537 x + ((2 : ℝ) * Sparse.eval nodeValue4538 x + ((2 : ℝ) * Sparse.eval nodeValue4539 x + ((2 : ℝ) * Sparse.eval nodeValue4553 x + ((2 : ℝ) * Sparse.eval nodeValue4570 x + ((1 : ℝ) * Sparse.eval nodeValue4572 x + ((1 : ℝ) * Sparse.eval nodeValue4575 x + ((2 : ℝ) * Sparse.eval nodeValue4618 x + ((3 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0)))))))))))))))))))

noncomputable def reducedSource1421 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue593 x + ((1 : ℝ) * Sparse.eval nodeValue594 x + ((1 : ℝ) * Sparse.eval nodeValue595 x + ((1 : ℝ) * Sparse.eval nodeValue613 x + ((2 : ℝ) * Sparse.eval nodeValue1122 x + ((2 : ℝ) * Sparse.eval nodeValue1123 x + ((2 : ℝ) * Sparse.eval nodeValue1124 x + ((2 : ℝ) * Sparse.eval nodeValue1138 x + ((2 : ℝ) * Sparse.eval nodeValue1188 x + ((1 : ℝ) * Sparse.eval nodeValue1190 x + ((1 : ℝ) * Sparse.eval nodeValue1193 x + ((2 : ℝ) * Sparse.eval nodeValue1293 x + ((3 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue1311 x + ((2 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0)))))))))))))))))))

noncomputable def reducedSource1422 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4176 x + ((1 : ℝ) * Sparse.eval nodeValue4178 x + ((1 : ℝ) * Sparse.eval nodeValue4179 x + ((1 : ℝ) * Sparse.eval nodeValue4188 x + ((2 : ℝ) * Sparse.eval nodeValue4545 x + ((2 : ℝ) * Sparse.eval nodeValue4547 x + ((2 : ℝ) * Sparse.eval nodeValue4548 x + ((2 : ℝ) * Sparse.eval nodeValue4556 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4611 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((2 : ℝ) * Sparse.eval nodeValue4616 x + ((1 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + 0))))))))))))))))))))

noncomputable def reducedSource1423 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue604 x + ((1 : ℝ) * Sparse.eval nodeValue606 x + ((1 : ℝ) * Sparse.eval nodeValue607 x + ((1 : ℝ) * Sparse.eval nodeValue616 x + ((2 : ℝ) * Sparse.eval nodeValue1130 x + ((2 : ℝ) * Sparse.eval nodeValue1132 x + ((2 : ℝ) * Sparse.eval nodeValue1133 x + ((2 : ℝ) * Sparse.eval nodeValue1141 x + ((2 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue1245 x + ((2 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1269 x + ((1 : ℝ) * Sparse.eval nodeValue1274 x + ((2 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue1292 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((2 : ℝ) * Sparse.eval nodeValue2961 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1424 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1512 x + ((1 : ℝ) * Sparse.eval nodeValue1513 x + ((1 : ℝ) * Sparse.eval nodeValue1520 x + ((1 : ℝ) * Sparse.eval nodeValue1526 x + ((2 : ℝ) * Sparse.eval nodeValue2657 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((2 : ℝ) * Sparse.eval nodeValue3259 x + ((2 : ℝ) * Sparse.eval nodeValue3266 x + ((2 : ℝ) * Sparse.eval nodeValue3271 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((2 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((2 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((2 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + 0))))))))))))))))))))

noncomputable def reducedSource1425 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue638 x + ((1 : ℝ) * Sparse.eval nodeValue641 x + ((1 : ℝ) * Sparse.eval nodeValue642 x + ((1 : ℝ) * Sparse.eval nodeValue653 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1426 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1287 x + ((2 : ℝ) * Sparse.eval nodeValue2584 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((2 : ℝ) * Sparse.eval nodeValue2761 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))

noncomputable def reducedSource1427 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1230 x + ((1 : ℝ) * Sparse.eval nodeValue2505 x + ((1 : ℝ) * Sparse.eval nodeValue2551 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1428 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4150 x + ((1 : ℝ) * Sparse.eval nodeValue4151 x + ((2 : ℝ) * Sparse.eval nodeValue4155 x + ((1 : ℝ) * Sparse.eval nodeValue4173 x + ((1 : ℝ) * Sparse.eval nodeValue4527 x + ((2 : ℝ) * Sparse.eval nodeValue4530 x + ((1 : ℝ) * Sparse.eval nodeValue4542 x + ((1 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4551 x + ((2 : ℝ) * Sparse.eval nodeValue4554 x + ((2 : ℝ) * Sparse.eval nodeValue4590 x + ((2 : ℝ) * Sparse.eval nodeValue4591 x + ((2 : ℝ) * Sparse.eval nodeValue4593 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((2 : ℝ) * Sparse.eval nodeValue4603 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4618 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + 0))))))))))))))))))))

noncomputable def reducedSource1429 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue578 x + ((1 : ℝ) * Sparse.eval nodeValue579 x + ((2 : ℝ) * Sparse.eval nodeValue583 x + ((1 : ℝ) * Sparse.eval nodeValue601 x + ((1 : ℝ) * Sparse.eval nodeValue1111 x + ((2 : ℝ) * Sparse.eval nodeValue1114 x + ((1 : ℝ) * Sparse.eval nodeValue1127 x + ((1 : ℝ) * Sparse.eval nodeValue1162 x + ((1 : ℝ) * Sparse.eval nodeValue1163 x + ((2 : ℝ) * Sparse.eval nodeValue1167 x + ((2 : ℝ) * Sparse.eval nodeValue1213 x + ((2 : ℝ) * Sparse.eval nodeValue1215 x + ((2 : ℝ) * Sparse.eval nodeValue1220 x + ((2 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1265 x + ((2 : ℝ) * Sparse.eval nodeValue1266 x + ((1 : ℝ) * Sparse.eval nodeValue1298 x + ((1 : ℝ) * Sparse.eval nodeValue2936 x + ((1 : ℝ) * Sparse.eval nodeValue3000 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + 0))))))))))))))))))))

noncomputable def reducedSource1430 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1504 x + ((1 : ℝ) * Sparse.eval nodeValue1505 x + ((1 : ℝ) * Sparse.eval nodeValue1508 x + ((2 : ℝ) * Sparse.eval nodeValue1515 x + ((1 : ℝ) * Sparse.eval nodeValue3255 x + ((1 : ℝ) * Sparse.eval nodeValue3257 x + ((2 : ℝ) * Sparse.eval nodeValue3261 x + ((1 : ℝ) * Sparse.eval nodeValue3263 x + ((1 : ℝ) * Sparse.eval nodeValue3273 x + ((2 : ℝ) * Sparse.eval nodeValue3274 x + ((2 : ℝ) * Sparse.eval nodeValue3290 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((2 : ℝ) * Sparse.eval nodeValue3294 x + ((2 : ℝ) * Sparse.eval nodeValue3297 x + ((2 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((1 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3521 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + 0))))))))))))))))))))

noncomputable def reducedSource1431 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue625 x + ((1 : ℝ) * Sparse.eval nodeValue630 x + ((2 : ℝ) * Sparse.eval nodeValue632 x + ((1 : ℝ) * Sparse.eval nodeValue640 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1432 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1150 x + ((2 : ℝ) * Sparse.eval nodeValue1152 x + ((1 : ℝ) * Sparse.eval nodeValue1158 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1433 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4143 x + ((1 : ℝ) * Sparse.eval nodeValue4144 x + ((2 : ℝ) * Sparse.eval nodeValue4145 x + ((1 : ℝ) * Sparse.eval nodeValue4175 x + ((1 : ℝ) * Sparse.eval nodeValue4516 x + ((1 : ℝ) * Sparse.eval nodeValue4517 x + ((2 : ℝ) * Sparse.eval nodeValue4518 x + ((1 : ℝ) * Sparse.eval nodeValue4523 x + ((2 : ℝ) * Sparse.eval nodeValue4524 x + ((1 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((2 : ℝ) * Sparse.eval nodeValue4608 x + ((2 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4622 x + ((2 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((1 : ℝ) * Sparse.eval nodeValue5203 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + 0))))))))))))))))))))

noncomputable def reducedSource1434 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue571 x + ((1 : ℝ) * Sparse.eval nodeValue572 x + ((2 : ℝ) * Sparse.eval nodeValue573 x + ((1 : ℝ) * Sparse.eval nodeValue603 x + ((1 : ℝ) * Sparse.eval nodeValue1100 x + ((1 : ℝ) * Sparse.eval nodeValue1101 x + ((2 : ℝ) * Sparse.eval nodeValue1102 x + ((1 : ℝ) * Sparse.eval nodeValue1107 x + ((2 : ℝ) * Sparse.eval nodeValue1108 x + ((1 : ℝ) * Sparse.eval nodeValue1129 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1242 x + ((2 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1299 x + ((2 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue2927 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + 0))))))))))))))))))))

noncomputable def reducedSource1435 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue1004 x + ((2 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((1 : ℝ) * Sparse.eval nodeValue1180 x + ((1 : ℝ) * Sparse.eval nodeValue1188 x + ((2 : ℝ) * Sparse.eval nodeValue1189 x + ((1 : ℝ) * Sparse.eval nodeValue1200 x + ((2 : ℝ) * Sparse.eval nodeValue1201 x + ((2 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1216 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((2 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1241 x + ((2 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue1386 x + ((2 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue1414 x + 0))))))))))))))))))))

noncomputable def reducedSource1436 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4152 x + ((1 : ℝ) * Sparse.eval nodeValue4153 x + ((1 : ℝ) * Sparse.eval nodeValue4154 x + ((1 : ℝ) * Sparse.eval nodeValue4158 x + ((1 : ℝ) * Sparse.eval nodeValue4176 x + ((1 : ℝ) * Sparse.eval nodeValue4528 x + ((1 : ℝ) * Sparse.eval nodeValue4529 x + ((1 : ℝ) * Sparse.eval nodeValue4533 x + ((1 : ℝ) * Sparse.eval nodeValue4541 x + ((1 : ℝ) * Sparse.eval nodeValue4545 x + ((1 : ℝ) * Sparse.eval nodeValue4546 x + ((1 : ℝ) * Sparse.eval nodeValue4549 x + ((1 : ℝ) * Sparse.eval nodeValue4553 x + ((1 : ℝ) * Sparse.eval nodeValue4589 x + ((1 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4592 x + ((1 : ℝ) * Sparse.eval nodeValue4599 x + ((1 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4603 x + ((2 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4616 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1437 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue580 x + ((1 : ℝ) * Sparse.eval nodeValue581 x + ((1 : ℝ) * Sparse.eval nodeValue582 x + ((1 : ℝ) * Sparse.eval nodeValue586 x + ((1 : ℝ) * Sparse.eval nodeValue604 x + ((1 : ℝ) * Sparse.eval nodeValue1112 x + ((1 : ℝ) * Sparse.eval nodeValue1113 x + ((1 : ℝ) * Sparse.eval nodeValue1117 x + ((1 : ℝ) * Sparse.eval nodeValue1130 x + ((1 : ℝ) * Sparse.eval nodeValue1164 x + ((1 : ℝ) * Sparse.eval nodeValue1165 x + ((1 : ℝ) * Sparse.eval nodeValue1166 x + ((1 : ℝ) * Sparse.eval nodeValue1172 x + ((1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1260 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1269 x + ((1 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue1302 x + ((1 : ℝ) * Sparse.eval nodeValue2937 x + ((1 : ℝ) * Sparse.eval nodeValue3001 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1438 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1510 x + ((1 : ℝ) * Sparse.eval nodeValue1511 x + ((1 : ℝ) * Sparse.eval nodeValue1512 x + ((1 : ℝ) * Sparse.eval nodeValue1514 x + ((1 : ℝ) * Sparse.eval nodeValue1522 x + ((1 : ℝ) * Sparse.eval nodeValue3256 x + ((1 : ℝ) * Sparse.eval nodeValue3258 x + ((1 : ℝ) * Sparse.eval nodeValue3259 x + ((1 : ℝ) * Sparse.eval nodeValue3260 x + ((1 : ℝ) * Sparse.eval nodeValue3264 x + ((1 : ℝ) * Sparse.eval nodeValue3265 x + ((1 : ℝ) * Sparse.eval nodeValue3267 x + ((1 : ℝ) * Sparse.eval nodeValue3270 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3295 x + ((2 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1439 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue623 x + ((1 : ℝ) * Sparse.eval nodeValue626 x + ((1 : ℝ) * Sparse.eval nodeValue627 x + ((1 : ℝ) * Sparse.eval nodeValue631 x + ((1 : ℝ) * Sparse.eval nodeValue638 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource144 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4085 x + ((8 : ℝ) * Sparse.eval nodeValue4897 x + ((12 : ℝ) * Sparse.eval nodeValue5261 x + ((8 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + 0))))

noncomputable def reducedSource145 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((3 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((3 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((6 : ℝ) * Sparse.eval nodeValue4804 x + ((3 : ℝ) * Sparse.eval nodeValue4841 x + ((3 : ℝ) * Sparse.eval nodeValue4868 x + ((3 : ℝ) * Sparse.eval nodeValue4894 x + ((3 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + 0))))))))))))

noncomputable def reducedSource146 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((6 : ℝ) * Sparse.eval nodeValue2203 x + ((3 : ℝ) * Sparse.eval nodeValue2226 x + ((3 : ℝ) * Sparse.eval nodeValue2228 x + ((3 : ℝ) * Sparse.eval nodeValue2261 x + ((3 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((3 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))

noncomputable def reducedSource147 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1051 x + ((3 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource148 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1239 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2060 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource149 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1043 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource150 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1297 x + ((3 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource151 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4085 x + ((3 : ℝ) * Sparse.eval nodeValue4496 x + ((1 : ℝ) * Sparse.eval nodeValue4501 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((6 : ℝ) * Sparse.eval nodeValue4832 x + ((3 : ℝ) * Sparse.eval nodeValue4837 x + ((3 : ℝ) * Sparse.eval nodeValue4845 x + ((3 : ℝ) * Sparse.eval nodeValue4890 x + ((3 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((3 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + 0))))))))))))

noncomputable def reducedSource152 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4070 x + ((1 : ℝ) * Sparse.eval nodeValue4072 x + ((12 : ℝ) * Sparse.eval nodeValue4081 x + ((8 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4094 x + 0))))

noncomputable def reducedSource153 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1354 x + ((1 : ℝ) * Sparse.eval nodeValue1355 x + ((1 : ℝ) * Sparse.eval nodeValue1356 x + ((1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1903 x + ((1 : ℝ) * Sparse.eval nodeValue1916 x + ((1 : ℝ) * Sparse.eval nodeValue1927 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3146 x + ((1 : ℝ) * Sparse.eval nodeValue3147 x + ((1 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3165 x + ((1 : ℝ) * Sparse.eval nodeValue3166 x + ((1 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3193 x + ((1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource154 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2513 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource155 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1028 x + ((1 : ℝ) * Sparse.eval nodeValue1029 x + ((1 : ℝ) * Sparse.eval nodeValue1030 x + ((1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource156 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1028 x + ((1 : ℝ) * Sparse.eval nodeValue2095 x + ((1 : ℝ) * Sparse.eval nodeValue2124 x + ((1 : ℝ) * Sparse.eval nodeValue2252 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource157 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2013 x + ((1 : ℝ) * Sparse.eval nodeValue2014 x + ((1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource158 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource159 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2095 x + ((1 : ℝ) * Sparse.eval nodeValue2096 x + ((1 : ℝ) * Sparse.eval nodeValue2097 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1440 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1148 x + ((1 : ℝ) * Sparse.eval nodeValue1149 x + ((1 : ℝ) * Sparse.eval nodeValue1151 x + ((1 : ℝ) * Sparse.eval nodeValue1156 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1441 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4139 x + ((1 : ℝ) * Sparse.eval nodeValue4140 x + ((1 : ℝ) * Sparse.eval nodeValue4141 x + ((1 : ℝ) * Sparse.eval nodeValue4145 x + ((1 : ℝ) * Sparse.eval nodeValue4172 x + ((1 : ℝ) * Sparse.eval nodeValue4513 x + ((1 : ℝ) * Sparse.eval nodeValue4514 x + ((1 : ℝ) * Sparse.eval nodeValue4515 x + ((1 : ℝ) * Sparse.eval nodeValue4518 x + ((1 : ℝ) * Sparse.eval nodeValue4521 x + ((1 : ℝ) * Sparse.eval nodeValue4522 x + ((1 : ℝ) * Sparse.eval nodeValue4524 x + ((1 : ℝ) * Sparse.eval nodeValue4541 x + ((1 : ℝ) * Sparse.eval nodeValue4581 x + ((1 : ℝ) * Sparse.eval nodeValue4583 x + ((1 : ℝ) * Sparse.eval nodeValue4586 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((3 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4622 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource1442 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue567 x + ((1 : ℝ) * Sparse.eval nodeValue568 x + ((1 : ℝ) * Sparse.eval nodeValue569 x + ((1 : ℝ) * Sparse.eval nodeValue573 x + ((1 : ℝ) * Sparse.eval nodeValue600 x + ((1 : ℝ) * Sparse.eval nodeValue1097 x + ((1 : ℝ) * Sparse.eval nodeValue1098 x + ((1 : ℝ) * Sparse.eval nodeValue1099 x + ((1 : ℝ) * Sparse.eval nodeValue1102 x + ((1 : ℝ) * Sparse.eval nodeValue1105 x + ((1 : ℝ) * Sparse.eval nodeValue1106 x + ((1 : ℝ) * Sparse.eval nodeValue1108 x + ((1 : ℝ) * Sparse.eval nodeValue1126 x + ((1 : ℝ) * Sparse.eval nodeValue1200 x + ((1 : ℝ) * Sparse.eval nodeValue1202 x + ((1 : ℝ) * Sparse.eval nodeValue1205 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((3 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1299 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource1443 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1229 x + ((1 : ℝ) * Sparse.eval nodeValue2504 x + ((1 : ℝ) * Sparse.eval nodeValue2550 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1444 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1183 x + ((1 : ℝ) * Sparse.eval nodeValue1188 x + ((2 : ℝ) * Sparse.eval nodeValue1189 x + ((1 : ℝ) * Sparse.eval nodeValue1286 x + ((1 : ℝ) * Sparse.eval nodeValue2684 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1445 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1185 x + ((1 : ℝ) * Sparse.eval nodeValue2400 x + ((1 : ℝ) * Sparse.eval nodeValue2535 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0))))))

noncomputable def reducedSource1446 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1188 x + ((1 : ℝ) * Sparse.eval nodeValue2403 x + ((1 : ℝ) * Sparse.eval nodeValue2536 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2684 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1447 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1184 x + ((1 : ℝ) * Sparse.eval nodeValue2399 x + ((1 : ℝ) * Sparse.eval nodeValue2534 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1448 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1200 x + ((2 : ℝ) * Sparse.eval nodeValue1201 x + ((2 : ℝ) * Sparse.eval nodeValue1228 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))

noncomputable def reducedSource1449 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1198 x + ((2 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue2701 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1450 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1200 x + ((2 : ℝ) * Sparse.eval nodeValue2461 x + ((2 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))

noncomputable def reducedSource1451 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1197 x + ((2 : ℝ) * Sparse.eval nodeValue2458 x + ((1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2700 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1452 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1052 x + ((2 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue1060 x + ((1 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1453 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue2031 x + ((1 : ℝ) * Sparse.eval nodeValue2129 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1454 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1053 x + ((1 : ℝ) * Sparse.eval nodeValue2030 x + ((1 : ℝ) * Sparse.eval nodeValue2128 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1455 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue990 x + ((1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue1052 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1456 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue1922 x + ((1 : ℝ) * Sparse.eval nodeValue2118 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1457 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue987 x + ((1 : ℝ) * Sparse.eval nodeValue1921 x + ((1 : ℝ) * Sparse.eval nodeValue2117 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2215 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1458 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1023 x + ((2 : ℝ) * Sparse.eval nodeValue2091 x + ((2 : ℝ) * Sparse.eval nodeValue2234 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))

noncomputable def reducedSource1459 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1018 x + ((1 : ℝ) * Sparse.eval nodeValue1023 x + ((2 : ℝ) * Sparse.eval nodeValue1034 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))

noncomputable def reducedSource1460 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1018 x + ((2 : ℝ) * Sparse.eval nodeValue2086 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

noncomputable def reducedSource1461 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1017 x + ((2 : ℝ) * Sparse.eval nodeValue2085 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1462 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1045 x + ((1 : ℝ) * Sparse.eval nodeValue2024 x + ((1 : ℝ) * Sparse.eval nodeValue2111 x + ((1 : ℝ) * Sparse.eval nodeValue2246 x + ((1 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1463 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1032 x + ((1 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue1045 x + ((1 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1464 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue2017 x + ((1 : ℝ) * Sparse.eval nodeValue2102 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1465 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4152 x + ((1 : ℝ) * Sparse.eval nodeValue4157 x + ((2 : ℝ) * Sparse.eval nodeValue4158 x + ((1 : ℝ) * Sparse.eval nodeValue4182 x + ((1 : ℝ) * Sparse.eval nodeValue4331 x + ((2 : ℝ) * Sparse.eval nodeValue4332 x + ((1 : ℝ) * Sparse.eval nodeValue4351 x + ((1 : ℝ) * Sparse.eval nodeValue4366 x + ((1 : ℝ) * Sparse.eval nodeValue4371 x + ((2 : ℝ) * Sparse.eval nodeValue4372 x + ((2 : ℝ) * Sparse.eval nodeValue4439 x + ((2 : ℝ) * Sparse.eval nodeValue4442 x + ((2 : ℝ) * Sparse.eval nodeValue4444 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + 0))))))))))))))))))))

noncomputable def reducedSource1466 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1510 x + ((2 : ℝ) * Sparse.eval nodeValue1522 x + ((1 : ℝ) * Sparse.eval nodeValue1524 x + ((1 : ℝ) * Sparse.eval nodeValue1528 x + ((2 : ℝ) * Sparse.eval nodeValue1678 x + ((1 : ℝ) * Sparse.eval nodeValue1680 x + ((1 : ℝ) * Sparse.eval nodeValue1684 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((1 : ℝ) * Sparse.eval nodeValue1711 x + ((2 : ℝ) * Sparse.eval nodeValue1713 x + ((2 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1726 x + ((2 : ℝ) * Sparse.eval nodeValue1734 x + ((2 : ℝ) * Sparse.eval nodeValue1736 x + ((2 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue1742 x + ((2 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((2 : ℝ) * Sparse.eval nodeValue2277 x + 0))))))))))))))))))))

noncomputable def reducedSource1467 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue610 x + ((1 : ℝ) * Sparse.eval nodeValue929 x + ((3 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1081 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource1468 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue944 x + ((1 : ℝ) * Sparse.eval nodeValue949 x + ((2 : ℝ) * Sparse.eval nodeValue950 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1469 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4104 x + ((1 : ℝ) * Sparse.eval nodeValue4105 x + ((2 : ℝ) * Sparse.eval nodeValue4106 x + ((1 : ℝ) * Sparse.eval nodeValue4126 x + ((1 : ℝ) * Sparse.eval nodeValue4290 x + ((2 : ℝ) * Sparse.eval nodeValue4291 x + ((1 : ℝ) * Sparse.eval nodeValue4307 x + ((1 : ℝ) * Sparse.eval nodeValue4351 x + ((1 : ℝ) * Sparse.eval nodeValue4352 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4451 x + ((2 : ℝ) * Sparse.eval nodeValue4452 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((2 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4489 x + ((2 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + 0))))))))))))))))))))

noncomputable def reducedSource1470 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue786 x + ((1 : ℝ) * Sparse.eval nodeValue810 x + ((2 : ℝ) * Sparse.eval nodeValue811 x + ((1 : ℝ) * Sparse.eval nodeValue827 x + ((1 : ℝ) * Sparse.eval nodeValue980 x + ((2 : ℝ) * Sparse.eval nodeValue981 x + ((1 : ℝ) * Sparse.eval nodeValue990 x + ((2 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue1023 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((2 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((2 : ℝ) * Sparse.eval nodeValue1045 x + ((2 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1060 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((2 : ℝ) * Sparse.eval nodeValue1087 x + ((1 : ℝ) * Sparse.eval nodeValue1216 x + ((2 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + 0))))))))))))))))))))

noncomputable def reducedSource1471 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4150 x + ((1 : ℝ) * Sparse.eval nodeValue4153 x + ((1 : ℝ) * Sparse.eval nodeValue4155 x + ((1 : ℝ) * Sparse.eval nodeValue4158 x + ((1 : ℝ) * Sparse.eval nodeValue4175 x + ((1 : ℝ) * Sparse.eval nodeValue4327 x + ((1 : ℝ) * Sparse.eval nodeValue4329 x + ((1 : ℝ) * Sparse.eval nodeValue4332 x + ((1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4364 x + ((1 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4369 x + ((1 : ℝ) * Sparse.eval nodeValue4372 x + ((1 : ℝ) * Sparse.eval nodeValue4438 x + ((1 : ℝ) * Sparse.eval nodeValue4440 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((3 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + 0)))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1472 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue625 x + ((1 : ℝ) * Sparse.eval nodeValue626 x + ((1 : ℝ) * Sparse.eval nodeValue627 x + ((1 : ℝ) * Sparse.eval nodeValue632 x + ((1 : ℝ) * Sparse.eval nodeValue644 x + ((1 : ℝ) * Sparse.eval nodeValue1316 x + ((1 : ℝ) * Sparse.eval nodeValue1317 x + ((1 : ℝ) * Sparse.eval nodeValue1318 x + ((1 : ℝ) * Sparse.eval nodeValue1322 x + ((1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue1328 x + ((1 : ℝ) * Sparse.eval nodeValue1331 x + ((1 : ℝ) * Sparse.eval nodeValue1339 x + ((1 : ℝ) * Sparse.eval nodeValue1386 x + ((1 : ℝ) * Sparse.eval nodeValue1388 x + ((1 : ℝ) * Sparse.eval nodeValue1391 x + ((1 : ℝ) * Sparse.eval nodeValue1409 x + ((1 : ℝ) * Sparse.eval nodeValue1410 x + ((3 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue1413 x + ((1 : ℝ) * Sparse.eval nodeValue1420 x + ((1 : ℝ) * Sparse.eval nodeValue1446 x + ((1 : ℝ) * Sparse.eval nodeValue1447 x + ((1 : ℝ) * Sparse.eval nodeValue3184 x + ((1 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((1 : ℝ) * Sparse.eval nodeValue3228 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource1473 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1504 x + ((1 : ℝ) * Sparse.eval nodeValue1514 x + ((1 : ℝ) * Sparse.eval nodeValue1515 x + ((1 : ℝ) * Sparse.eval nodeValue1517 x + ((1 : ℝ) * Sparse.eval nodeValue1522 x + ((1 : ℝ) * Sparse.eval nodeValue1670 x + ((1 : ℝ) * Sparse.eval nodeValue1671 x + ((1 : ℝ) * Sparse.eval nodeValue1673 x + ((1 : ℝ) * Sparse.eval nodeValue1678 x + ((1 : ℝ) * Sparse.eval nodeValue1703 x + ((1 : ℝ) * Sparse.eval nodeValue1705 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((1 : ℝ) * Sparse.eval nodeValue1720 x + ((1 : ℝ) * Sparse.eval nodeValue1721 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((3 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1726 x + ((1 : ℝ) * Sparse.eval nodeValue1734 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue1753 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource1474 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue578 x + ((1 : ℝ) * Sparse.eval nodeValue581 x + ((1 : ℝ) * Sparse.eval nodeValue583 x + ((1 : ℝ) * Sparse.eval nodeValue586 x + ((1 : ℝ) * Sparse.eval nodeValue603 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1475 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue603 x + ((1 : ℝ) * Sparse.eval nodeValue922 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1081 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1476 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue942 x + ((1 : ℝ) * Sparse.eval nodeValue945 x + ((1 : ℝ) * Sparse.eval nodeValue947 x + ((1 : ℝ) * Sparse.eval nodeValue950 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1477 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4100 x + ((1 : ℝ) * Sparse.eval nodeValue4101 x + ((1 : ℝ) * Sparse.eval nodeValue4102 x + ((1 : ℝ) * Sparse.eval nodeValue4107 x + ((1 : ℝ) * Sparse.eval nodeValue4119 x + ((1 : ℝ) * Sparse.eval nodeValue4287 x + ((1 : ℝ) * Sparse.eval nodeValue4288 x + ((1 : ℝ) * Sparse.eval nodeValue4292 x + ((1 : ℝ) * Sparse.eval nodeValue4301 x + ((1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4355 x + ((1 : ℝ) * Sparse.eval nodeValue4399 x + ((1 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1478 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4249 x + ((1 : ℝ) * Sparse.eval nodeValue4264 x + ((1 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4267 x + ((1 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4397 x + ((1 : ℝ) * Sparse.eval nodeValue4399 x + ((1 : ℝ) * Sparse.eval nodeValue4407 x + ((1 : ℝ) * Sparse.eval nodeValue4436 x + ((1 : ℝ) * Sparse.eval nodeValue4438 x + ((1 : ℝ) * Sparse.eval nodeValue4439 x + ((1 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4453 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4471 x + ((1 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4590 x + ((1 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1479 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue807 x + ((1 : ℝ) * Sparse.eval nodeValue810 x + ((1 : ℝ) * Sparse.eval nodeValue824 x + ((1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue978 x + ((1 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue1018 x + ((1 : ℝ) * Sparse.eval nodeValue1020 x + ((1 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue1057 x + ((1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1082 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1266 x + ((1 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1480 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue1358 x + ((1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1368 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue1383 x + ((1 : ℝ) * Sparse.eval nodeValue1384 x + ((1 : ℝ) * Sparse.eval nodeValue1386 x + ((1 : ℝ) * Sparse.eval nodeValue1393 x + ((1 : ℝ) * Sparse.eval nodeValue1395 x + ((1 : ℝ) * Sparse.eval nodeValue1396 x + ((1 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1407 x + ((1 : ℝ) * Sparse.eval nodeValue1410 x + ((2 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue1412 x + ((1 : ℝ) * Sparse.eval nodeValue1414 x + ((1 : ℝ) * Sparse.eval nodeValue1443 x + ((1 : ℝ) * Sparse.eval nodeValue1447 x + ((1 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue1468 x + ((1 : ℝ) * Sparse.eval nodeValue1475 x + ((1 : ℝ) * Sparse.eval nodeValue1480 x + ((1 : ℝ) * Sparse.eval nodeValue1482 x + ((1 : ℝ) * Sparse.eval nodeValue1483 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1481 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue2016 x + ((1 : ℝ) * Sparse.eval nodeValue2101 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1482 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue730 x + ((1 : ℝ) * Sparse.eval nodeValue733 x + ((1 : ℝ) * Sparse.eval nodeValue734 x + ((1 : ℝ) * Sparse.eval nodeValue738 x + ((1 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue1645 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1483 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4149 x + ((1 : ℝ) * Sparse.eval nodeValue4151 x + ((2 : ℝ) * Sparse.eval nodeValue4154 x + ((1 : ℝ) * Sparse.eval nodeValue4172 x + ((1 : ℝ) * Sparse.eval nodeValue4326 x + ((2 : ℝ) * Sparse.eval nodeValue4328 x + ((1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4363 x + ((1 : ℝ) * Sparse.eval nodeValue4365 x + ((2 : ℝ) * Sparse.eval nodeValue4368 x + ((1 : ℝ) * Sparse.eval nodeValue4455 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((2 : ℝ) * Sparse.eval nodeValue4460 x + ((2 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4894 x + 0))))))))))))))))))))

noncomputable def reducedSource1484 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue629 x + ((1 : ℝ) * Sparse.eval nodeValue630 x + ((2 : ℝ) * Sparse.eval nodeValue631 x + ((1 : ℝ) * Sparse.eval nodeValue646 x + ((1 : ℝ) * Sparse.eval nodeValue1319 x + ((1 : ℝ) * Sparse.eval nodeValue1320 x + ((2 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue1329 x + ((2 : ℝ) * Sparse.eval nodeValue1330 x + ((1 : ℝ) * Sparse.eval nodeValue1341 x + ((1 : ℝ) * Sparse.eval nodeValue1405 x + ((2 : ℝ) * Sparse.eval nodeValue1406 x + ((2 : ℝ) * Sparse.eval nodeValue1414 x + ((2 : ℝ) * Sparse.eval nodeValue1416 x + ((2 : ℝ) * Sparse.eval nodeValue1419 x + ((1 : ℝ) * Sparse.eval nodeValue1441 x + ((2 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue3185 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource1485 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1501 x + ((1 : ℝ) * Sparse.eval nodeValue1505 x + ((1 : ℝ) * Sparse.eval nodeValue1507 x + ((2 : ℝ) * Sparse.eval nodeValue1511 x + ((1 : ℝ) * Sparse.eval nodeValue1663 x + ((1 : ℝ) * Sparse.eval nodeValue1664 x + ((2 : ℝ) * Sparse.eval nodeValue1667 x + ((1 : ℝ) * Sparse.eval nodeValue1697 x + ((1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1704 x + ((2 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((2 : ℝ) * Sparse.eval nodeValue1712 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((2 : ℝ) * Sparse.eval nodeValue1725 x + ((2 : ℝ) * Sparse.eval nodeValue1727 x + ((2 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2264 x + 0))))))))))))))))))))

noncomputable def reducedSource1486 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue577 x + ((1 : ℝ) * Sparse.eval nodeValue579 x + ((2 : ℝ) * Sparse.eval nodeValue582 x + ((1 : ℝ) * Sparse.eval nodeValue600 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1487 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue600 x + ((1 : ℝ) * Sparse.eval nodeValue919 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((2 : ℝ) * Sparse.eval nodeValue1082 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1488 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue941 x + ((1 : ℝ) * Sparse.eval nodeValue943 x + ((2 : ℝ) * Sparse.eval nodeValue946 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((1 : ℝ) * Sparse.eval nodeValue2106 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1489 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue577 x + ((1 : ℝ) * Sparse.eval nodeValue941 x + ((1 : ℝ) * Sparse.eval nodeValue1038 x + ((3 : ℝ) * Sparse.eval nodeValue1040 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource1490 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4098 x + ((1 : ℝ) * Sparse.eval nodeValue4099 x + ((2 : ℝ) * Sparse.eval nodeValue4102 x + ((1 : ℝ) * Sparse.eval nodeValue4115 x + ((1 : ℝ) * Sparse.eval nodeValue4286 x + ((2 : ℝ) * Sparse.eval nodeValue4288 x + ((1 : ℝ) * Sparse.eval nodeValue4298 x + ((1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4343 x + ((2 : ℝ) * Sparse.eval nodeValue4349 x + ((2 : ℝ) * Sparse.eval nodeValue4396 x + ((2 : ℝ) * Sparse.eval nodeValue4398 x + ((2 : ℝ) * Sparse.eval nodeValue4404 x + ((2 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + 0))))))))))))))))))))

noncomputable def reducedSource1491 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue535 x + ((1 : ℝ) * Sparse.eval nodeValue536 x + ((2 : ℝ) * Sparse.eval nodeValue539 x + ((1 : ℝ) * Sparse.eval nodeValue552 x + ((1 : ℝ) * Sparse.eval nodeValue864 x + ((2 : ℝ) * Sparse.eval nodeValue866 x + ((1 : ℝ) * Sparse.eval nodeValue876 x + ((1 : ℝ) * Sparse.eval nodeValue919 x + ((1 : ℝ) * Sparse.eval nodeValue921 x + ((2 : ℝ) * Sparse.eval nodeValue927 x + ((2 : ℝ) * Sparse.eval nodeValue977 x + ((2 : ℝ) * Sparse.eval nodeValue979 x + ((2 : ℝ) * Sparse.eval nodeValue985 x + ((2 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1039 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((1 : ℝ) * Sparse.eval nodeValue2594 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + 0))))))))))))))))))))

noncomputable def reducedSource1492 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4248 x + ((1 : ℝ) * Sparse.eval nodeValue4251 x + ((1 : ℝ) * Sparse.eval nodeValue4255 x + ((2 : ℝ) * Sparse.eval nodeValue4264 x + ((1 : ℝ) * Sparse.eval nodeValue4395 x + ((2 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4406 x + ((2 : ℝ) * Sparse.eval nodeValue4435 x + ((1 : ℝ) * Sparse.eval nodeValue4438 x + ((2 : ℝ) * Sparse.eval nodeValue4450 x + ((2 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4470 x + ((1 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4589 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((2 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + 0))))))))))))))))))))

noncomputable def reducedSource1493 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue1360 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((2 : ℝ) * Sparse.eval nodeValue1371 x + ((1 : ℝ) * Sparse.eval nodeValue1386 x + ((2 : ℝ) * Sparse.eval nodeValue1387 x + ((2 : ℝ) * Sparse.eval nodeValue1396 x + ((1 : ℝ) * Sparse.eval nodeValue1398 x + ((2 : ℝ) * Sparse.eval nodeValue1411 x + ((2 : ℝ) * Sparse.eval nodeValue1412 x + ((1 : ℝ) * Sparse.eval nodeValue1414 x + ((2 : ℝ) * Sparse.eval nodeValue1415 x + ((2 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue1451 x + ((1 : ℝ) * Sparse.eval nodeValue1470 x + ((1 : ℝ) * Sparse.eval nodeValue1477 x + ((1 : ℝ) * Sparse.eval nodeValue1478 x + ((2 : ℝ) * Sparse.eval nodeValue1483 x + 0))))))))))))))))))))

noncomputable def reducedSource1494 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1033 x + ((1 : ℝ) * Sparse.eval nodeValue2015 x + ((1 : ℝ) * Sparse.eval nodeValue2099 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1495 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue981 x + ((1 : ℝ) * Sparse.eval nodeValue1913 x + ((1 : ℝ) * Sparse.eval nodeValue2078 x + ((1 : ℝ) * Sparse.eval nodeValue2192 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1496 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue978 x + ((1 : ℝ) * Sparse.eval nodeValue981 x + ((1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue1032 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1497 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue978 x + ((1 : ℝ) * Sparse.eval nodeValue1909 x + ((1 : ℝ) * Sparse.eval nodeValue2076 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1498 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue1912 x + ((1 : ℝ) * Sparse.eval nodeValue2077 x + ((2 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

noncomputable def reducedSource1499 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue1003 x + ((1 : ℝ) * Sparse.eval nodeValue1034 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))

noncomputable def reducedSource1500 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue1908 x + ((1 : ℝ) * Sparse.eval nodeValue2075 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1501 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue865 x + ((1 : ℝ) * Sparse.eval nodeValue866 x + ((1 : ℝ) * Sparse.eval nodeValue869 x + ((1 : ℝ) * Sparse.eval nodeValue878 x + ((1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue1908 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1502 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue699 x + ((1 : ℝ) * Sparse.eval nodeValue700 x + ((1 : ℝ) * Sparse.eval nodeValue703 x + ((1 : ℝ) * Sparse.eval nodeValue712 x + ((1 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue1597 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

noncomputable def reducedSource1503 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue976 x + ((1 : ℝ) * Sparse.eval nodeValue1907 x + ((1 : ℝ) * Sparse.eval nodeValue2074 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1504 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1076 x + ((2 : ℝ) * Sparse.eval nodeValue2049 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2282 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1505 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4176 x + ((1 : ℝ) * Sparse.eval nodeValue4184 x + ((1 : ℝ) * Sparse.eval nodeValue4185 x + ((1 : ℝ) * Sparse.eval nodeValue4188 x + ((2 : ℝ) * Sparse.eval nodeValue4345 x + ((2 : ℝ) * Sparse.eval nodeValue4353 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((2 : ℝ) * Sparse.eval nodeValue4357 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4464 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4478 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + 0))))))))))))))))))))

noncomputable def reducedSource1506 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1512 x + ((1 : ℝ) * Sparse.eval nodeValue1525 x + ((1 : ℝ) * Sparse.eval nodeValue1526 x + ((1 : ℝ) * Sparse.eval nodeValue1530 x + ((2 : ℝ) * Sparse.eval nodeValue1668 x + ((2 : ℝ) * Sparse.eval nodeValue1681 x + ((2 : ℝ) * Sparse.eval nodeValue1682 x + ((2 : ℝ) * Sparse.eval nodeValue1686 x + ((2 : ℝ) * Sparse.eval nodeValue1708 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((2 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + 0))))))))))))))))))))

noncomputable def reducedSource1507 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4276 x + ((1 : ℝ) * Sparse.eval nodeValue4279 x + ((1 : ℝ) * Sparse.eval nodeValue4283 x + ((2 : ℝ) * Sparse.eval nodeValue4400 x + ((2 : ℝ) * Sparse.eval nodeValue4424 x + ((2 : ℝ) * Sparse.eval nodeValue4425 x + ((2 : ℝ) * Sparse.eval nodeValue4427 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((2 : ℝ) * Sparse.eval nodeValue4462 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4500 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4504 x + ((1 : ℝ) * Sparse.eval nodeValue4506 x + ((2 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + 0))))))))))))))))))))

noncomputable def reducedSource1508 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4173 x + ((1 : ℝ) * Sparse.eval nodeValue4178 x + ((1 : ℝ) * Sparse.eval nodeValue4180 x + ((1 : ℝ) * Sparse.eval nodeValue4188 x + ((2 : ℝ) * Sparse.eval nodeValue4342 x + ((2 : ℝ) * Sparse.eval nodeValue4347 x + ((2 : ℝ) * Sparse.eval nodeValue4349 x + ((2 : ℝ) * Sparse.eval nodeValue4357 x + ((2 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4476 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((2 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + 0))))))))))))))))))))

noncomputable def reducedSource1509 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1508 x + ((1 : ℝ) * Sparse.eval nodeValue1519 x + ((1 : ℝ) * Sparse.eval nodeValue1520 x + ((1 : ℝ) * Sparse.eval nodeValue1526 x + ((2 : ℝ) * Sparse.eval nodeValue1665 x + ((2 : ℝ) * Sparse.eval nodeValue1675 x + ((2 : ℝ) * Sparse.eval nodeValue1676 x + ((2 : ℝ) * Sparse.eval nodeValue1682 x + ((2 : ℝ) * Sparse.eval nodeValue1708 x + ((2 : ℝ) * Sparse.eval nodeValue1709 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((2 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1755 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + 0))))))))))))))))))))

noncomputable def reducedSource1510 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4119 x + ((1 : ℝ) * Sparse.eval nodeValue4121 x + ((1 : ℝ) * Sparse.eval nodeValue4122 x + ((1 : ℝ) * Sparse.eval nodeValue4133 x + ((2 : ℝ) * Sparse.eval nodeValue4301 x + ((2 : ℝ) * Sparse.eval nodeValue4303 x + ((2 : ℝ) * Sparse.eval nodeValue4304 x + ((2 : ℝ) * Sparse.eval nodeValue4314 x + ((2 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4428 x + ((1 : ℝ) * Sparse.eval nodeValue4431 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + 0))))))))))))))))))))

noncomputable def reducedSource1511 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4270 x + ((1 : ℝ) * Sparse.eval nodeValue4273 x + ((1 : ℝ) * Sparse.eval nodeValue4283 x + ((2 : ℝ) * Sparse.eval nodeValue4397 x + ((2 : ℝ) * Sparse.eval nodeValue4419 x + ((2 : ℝ) * Sparse.eval nodeValue4420 x + ((2 : ℝ) * Sparse.eval nodeValue4424 x + ((2 : ℝ) * Sparse.eval nodeValue4453 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4491 x + ((1 : ℝ) * Sparse.eval nodeValue4492 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4500 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + 0))))))))))))))))))))

noncomputable def reducedSource1512 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1075 x + ((2 : ℝ) * Sparse.eval nodeValue2048 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1513 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((2 : ℝ) * Sparse.eval nodeValue4175 x + ((1 : ℝ) * Sparse.eval nodeValue4183 x + ((2 : ℝ) * Sparse.eval nodeValue4186 x + ((2 : ℝ) * Sparse.eval nodeValue4344 x + ((2 : ℝ) * Sparse.eval nodeValue4352 x + ((4 : ℝ) * Sparse.eval nodeValue4355 x + ((4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((2 : ℝ) * Sparse.eval nodeValue4467 x + ((2 : ℝ) * Sparse.eval nodeValue4497 x + ((2 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4838 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + 0)))))))))))))

noncomputable def reducedSource1514 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4172 x + ((1 : ℝ) * Sparse.eval nodeValue4177 x + ((1 : ℝ) * Sparse.eval nodeValue4180 x + ((1 : ℝ) * Sparse.eval nodeValue4185 x + ((2 : ℝ) * Sparse.eval nodeValue4341 x + ((2 : ℝ) * Sparse.eval nodeValue4346 x + ((2 : ℝ) * Sparse.eval nodeValue4349 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + 0))))))))))))))))))))

noncomputable def reducedSource1515 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1074 x + ((2 : ℝ) * Sparse.eval nodeValue2047 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1516 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4170 x + ((1 : ℝ) * Sparse.eval nodeValue4174 x + ((2 : ℝ) * Sparse.eval nodeValue4179 x + ((2 : ℝ) * Sparse.eval nodeValue4340 x + ((2 : ℝ) * Sparse.eval nodeValue4343 x + ((4 : ℝ) * Sparse.eval nodeValue4348 x + ((2 : ℝ) * Sparse.eval nodeValue4494 x + ((4 : ℝ) * Sparse.eval nodeValue4496 x + ((2 : ℝ) * Sparse.eval nodeValue4500 x + ((2 : ℝ) * Sparse.eval nodeValue4501 x + ((2 : ℝ) * Sparse.eval nodeValue4510 x + ((2 : ℝ) * Sparse.eval nodeValue4832 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + 0)))))))))))))

noncomputable def reducedSource1517 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue651 x + ((1 : ℝ) * Sparse.eval nodeValue652 x + ((2 : ℝ) * Sparse.eval nodeValue653 x + ((2 : ℝ) * Sparse.eval nodeValue1345 x + ((2 : ℝ) * Sparse.eval nodeValue1346 x + ((4 : ℝ) * Sparse.eval nodeValue1347 x + ((2 : ℝ) * Sparse.eval nodeValue1435 x + ((2 : ℝ) * Sparse.eval nodeValue1436 x + ((4 : ℝ) * Sparse.eval nodeValue1451 x + ((2 : ℝ) * Sparse.eval nodeValue1452 x + ((2 : ℝ) * Sparse.eval nodeValue1454 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((2 : ℝ) * Sparse.eval nodeValue3082 x + ((2 : ℝ) * Sparse.eval nodeValue3114 x + 0)))))))))))))

noncomputable def reducedSource1518 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1503 x + ((1 : ℝ) * Sparse.eval nodeValue1509 x + ((2 : ℝ) * Sparse.eval nodeValue1513 x + ((2 : ℝ) * Sparse.eval nodeValue1662 x + ((2 : ℝ) * Sparse.eval nodeValue1666 x + ((4 : ℝ) * Sparse.eval nodeValue1669 x + ((2 : ℝ) * Sparse.eval nodeValue1700 x + ((4 : ℝ) * Sparse.eval nodeValue1710 x + ((2 : ℝ) * Sparse.eval nodeValue1716 x + ((2 : ℝ) * Sparse.eval nodeValue1730 x + ((2 : ℝ) * Sparse.eval nodeValue1741 x + ((2 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2268 x + 0)))))))))))))

noncomputable def reducedSource1519 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue598 x + ((1 : ℝ) * Sparse.eval nodeValue602 x + ((2 : ℝ) * Sparse.eval nodeValue607 x + ((1 : ℝ) * Sparse.eval nodeValue1080 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1520 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue598 x + ((1 : ℝ) * Sparse.eval nodeValue918 x + ((1 : ℝ) * Sparse.eval nodeValue1078 x + ((3 : ℝ) * Sparse.eval nodeValue1080 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource1521 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1252 x + ((1 : ℝ) * Sparse.eval nodeValue1255 x + ((2 : ℝ) * Sparse.eval nodeValue1270 x + ((2 : ℝ) * Sparse.eval nodeValue1272 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((2 : ℝ) * Sparse.eval nodeValue1306 x + ((2 : ℝ) * Sparse.eval nodeValue1398 x + ((2 : ℝ) * Sparse.eval nodeValue1414 x + ((4 : ℝ) * Sparse.eval nodeValue1415 x + ((4 : ℝ) * Sparse.eval nodeValue1427 x + ((2 : ℝ) * Sparse.eval nodeValue1448 x + ((2 : ℝ) * Sparse.eval nodeValue1449 x + ((2 : ℝ) * Sparse.eval nodeValue1478 x + ((2 : ℝ) * Sparse.eval nodeValue1484 x + 0)))))))))))))

noncomputable def reducedSource1522 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1006 x + ((1 : ℝ) * Sparse.eval nodeValue1948 x + ((1 : ℝ) * Sparse.eval nodeValue2001 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2221 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1523 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1001 x + ((1 : ℝ) * Sparse.eval nodeValue1946 x + ((1 : ℝ) * Sparse.eval nodeValue1998 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1524 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1008 x + ((1 : ℝ) * Sparse.eval nodeValue1949 x + ((1 : ℝ) * Sparse.eval nodeValue2002 x + ((2 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1525 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue996 x + ((2 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1008 x + ((1 : ℝ) * Sparse.eval nodeValue1071 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1526 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1947 x + ((1 : ℝ) * Sparse.eval nodeValue2000 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1527 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue1004 x + ((2 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1528 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1945 x + ((1 : ℝ) * Sparse.eval nodeValue1997 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1529 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue876 x + ((1 : ℝ) * Sparse.eval nodeValue881 x + ((1 : ℝ) * Sparse.eval nodeValue883 x + ((1 : ℝ) * Sparse.eval nodeValue891 x + ((1 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1945 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1530 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue999 x + ((1 : ℝ) * Sparse.eval nodeValue1944 x + ((1 : ℝ) * Sparse.eval nodeValue1996 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1531 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue786 x + ((2 : ℝ) * Sparse.eval nodeValue1638 x + ((2 : ℝ) * Sparse.eval nodeValue1699 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1532 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue786 x + ((2 : ℝ) * Sparse.eval nodeValue805 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1533 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue550 x + ((2 : ℝ) * Sparse.eval nodeValue803 x + ((1 : ℝ) * Sparse.eval nodeValue822 x + ((2 : ℝ) * Sparse.eval nodeValue850 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

noncomputable def reducedSource1534 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue783 x + ((2 : ℝ) * Sparse.eval nodeValue1636 x + ((1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1535 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue537 x + ((1 : ℝ) * Sparse.eval nodeValue732 x + ((2 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue805 x + ((1 : ℝ) * Sparse.eval nodeValue810 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1536 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4068 x + ((1 : ℝ) * Sparse.eval nodeValue4100 x + ((1 : ℝ) * Sparse.eval nodeValue4105 x + ((2 : ℝ) * Sparse.eval nodeValue4107 x + ((1 : ℝ) * Sparse.eval nodeValue4125 x + ((1 : ℝ) * Sparse.eval nodeValue4199 x + ((2 : ℝ) * Sparse.eval nodeValue4201 x + ((1 : ℝ) * Sparse.eval nodeValue4216 x + ((1 : ℝ) * Sparse.eval nodeValue4232 x + ((1 : ℝ) * Sparse.eval nodeValue4237 x + ((2 : ℝ) * Sparse.eval nodeValue4239 x + ((2 : ℝ) * Sparse.eval nodeValue4249 x + ((2 : ℝ) * Sparse.eval nodeValue4253 x + ((2 : ℝ) * Sparse.eval nodeValue4256 x + ((1 : ℝ) * Sparse.eval nodeValue4263 x + ((4 : ℝ) * Sparse.eval nodeValue4267 x + ((1 : ℝ) * Sparse.eval nodeValue4417 x + ((1 : ℝ) * Sparse.eval nodeValue4489 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + 0)))))))))))))))))))

noncomputable def reducedSource1537 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue662 x + ((1 : ℝ) * Sparse.eval nodeValue681 x + ((2 : ℝ) * Sparse.eval nodeValue682 x + ((1 : ℝ) * Sparse.eval nodeValue687 x + ((1 : ℝ) * Sparse.eval nodeValue760 x + ((2 : ℝ) * Sparse.eval nodeValue761 x + ((1 : ℝ) * Sparse.eval nodeValue766 x + ((1 : ℝ) * Sparse.eval nodeValue798 x + ((2 : ℝ) * Sparse.eval nodeValue803 x + ((1 : ℝ) * Sparse.eval nodeValue805 x + ((1 : ℝ) * Sparse.eval nodeValue840 x + ((2 : ℝ) * Sparse.eval nodeValue841 x + ((2 : ℝ) * Sparse.eval nodeValue847 x + ((2 : ℝ) * Sparse.eval nodeValue848 x + ((4 : ℝ) * Sparse.eval nodeValue850 x + ((1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue1073 x + ((2 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue1081 x + ((1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))))))))))))))))

noncomputable def reducedSource1538 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue732 x + ((1 : ℝ) * Sparse.eval nodeValue737 x + ((2 : ℝ) * Sparse.eval nodeValue739 x + ((1 : ℝ) * Sparse.eval nodeValue810 x + ((1 : ℝ) * Sparse.eval nodeValue1648 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1539 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4069 x + ((1 : ℝ) * Sparse.eval nodeValue4113 x + ((1 : ℝ) * Sparse.eval nodeValue4118 x + ((2 : ℝ) * Sparse.eval nodeValue4119 x + ((1 : ℝ) * Sparse.eval nodeValue4126 x + ((1 : ℝ) * Sparse.eval nodeValue4209 x + ((2 : ℝ) * Sparse.eval nodeValue4210 x + ((1 : ℝ) * Sparse.eval nodeValue4217 x + ((2 : ℝ) * Sparse.eval nodeValue4249 x + ((1 : ℝ) * Sparse.eval nodeValue4252 x + ((2 : ℝ) * Sparse.eval nodeValue4264 x + ((2 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4267 x + ((4 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4275 x + ((2 : ℝ) * Sparse.eval nodeValue4283 x + ((1 : ℝ) * Sparse.eval nodeValue4399 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + 0)))))))))))))))))))

noncomputable def reducedSource1540 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4057 x + ((1 : ℝ) * Sparse.eval nodeValue4058 x + ((2 : ℝ) * Sparse.eval nodeValue4059 x + ((2 : ℝ) * Sparse.eval nodeValue4063 x + ((2 : ℝ) * Sparse.eval nodeValue4064 x + ((4 : ℝ) * Sparse.eval nodeValue4065 x + ((2 : ℝ) * Sparse.eval nodeValue4068 x + ((6 : ℝ) * Sparse.eval nodeValue4069 x + ((2 : ℝ) * Sparse.eval nodeValue4070 x + ((2 : ℝ) * Sparse.eval nodeValue4071 x + ((2 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4083 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))

noncomputable def reducedSource1541 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1700 x + ((1 : ℝ) * Sparse.eval nodeValue3057 x + ((3 : ℝ) * Sparse.eval nodeValue3072 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1542 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1700 x + ((3 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1543 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue597 x + ((1 : ℝ) * Sparse.eval nodeValue1038 x + ((1 : ℝ) * Sparse.eval nodeValue1056 x + ((3 : ℝ) * Sparse.eval nodeValue1079 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource1544 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1698 x + ((3 : ℝ) * Sparse.eval nodeValue3286 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1545 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1699 x + ((3 : ℝ) * Sparse.eval nodeValue1706 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1546 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1316 x + ((1 : ℝ) * Sparse.eval nodeValue1319 x + ((1 : ℝ) * Sparse.eval nodeValue1366 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource1547 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1699 x + ((3 : ℝ) * Sparse.eval nodeValue3239 x + ((1 : ℝ) * Sparse.eval nodeValue3244 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1548 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1256 x + ((1 : ℝ) * Sparse.eval nodeValue2628 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((3 : ℝ) * Sparse.eval nodeValue2747 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0))))

noncomputable def reducedSource1549 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1644 x + ((1 : ℝ) * Sparse.eval nodeValue3057 x + ((3 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1550 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1126 x + ((1 : ℝ) * Sparse.eval nodeValue1127 x + ((2 : ℝ) * Sparse.eval nodeValue1130 x + ((1 : ℝ) * Sparse.eval nodeValue1233 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1551 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue637 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((3 : ℝ) * Sparse.eval nodeValue1260 x + ((1 : ℝ) * Sparse.eval nodeValue1293 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1552 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1636 x + ((1 : ℝ) * Sparse.eval nodeValue1638 x + ((1 : ℝ) * Sparse.eval nodeValue1644 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1553 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1593 x + ((1 : ℝ) * Sparse.eval nodeValue1595 x + ((2 : ℝ) * Sparse.eval nodeValue1600 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1554 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((2 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((1 : ℝ) * Sparse.eval nodeValue3307 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1555 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1600 x + ((1 : ℝ) * Sparse.eval nodeValue3239 x + ((1 : ℝ) * Sparse.eval nodeValue3286 x + ((2 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1556 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1706 x + ((2 : ℝ) * Sparse.eval nodeValue3289 x + ((2 : ℝ) * Sparse.eval nodeValue3292 x + ((1 : ℝ) * Sparse.eval nodeValue3307 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1557 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1648 x + ((1 : ℝ) * Sparse.eval nodeValue3072 x + ((1 : ℝ) * Sparse.eval nodeValue3286 x + ((2 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

noncomputable def reducedSource1558 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1636 x + ((1 : ℝ) * Sparse.eval nodeValue1639 x + ((1 : ℝ) * Sparse.eval nodeValue1641 x + ((1 : ℝ) * Sparse.eval nodeValue1648 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue3303 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))))

noncomputable def reducedSource1559 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4164 x + ((3 : ℝ) * Sparse.eval nodeValue4165 x + ((1 : ℝ) * Sparse.eval nodeValue4182 x + ((3 : ℝ) * Sparse.eval nodeValue4537 x + ((1 : ℝ) * Sparse.eval nodeValue4550 x + ((1 : ℝ) * Sparse.eval nodeValue4569 x + ((3 : ℝ) * Sparse.eval nodeValue4570 x + ((3 : ℝ) * Sparse.eval nodeValue4618 x + ((6 : ℝ) * Sparse.eval nodeValue4619 x + ((3 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue5166 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((3 : ℝ) * Sparse.eval nodeValue5306 x + 0))))))))))))

noncomputable def reducedSource1560 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue592 x + ((3 : ℝ) * Sparse.eval nodeValue593 x + ((1 : ℝ) * Sparse.eval nodeValue610 x + ((3 : ℝ) * Sparse.eval nodeValue1122 x + ((1 : ℝ) * Sparse.eval nodeValue1135 x + ((1 : ℝ) * Sparse.eval nodeValue1187 x + ((3 : ℝ) * Sparse.eval nodeValue1188 x + ((3 : ℝ) * Sparse.eval nodeValue1293 x + ((6 : ℝ) * Sparse.eval nodeValue1294 x + ((3 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue2953 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + ((3 : ℝ) * Sparse.eval nodeValue3120 x + 0))))))))))))

noncomputable def reducedSource1561 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4169 x + ((1 : ℝ) * Sparse.eval nodeValue4170 x + ((3 : ℝ) * Sparse.eval nodeValue4173 x + ((1 : ℝ) * Sparse.eval nodeValue4540 x + ((3 : ℝ) * Sparse.eval nodeValue4542 x + ((3 : ℝ) * Sparse.eval nodeValue4599 x + ((3 : ℝ) * Sparse.eval nodeValue4600 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((6 : ℝ) * Sparse.eval nodeValue4603 x + ((3 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((3 : ℝ) * Sparse.eval nodeValue5290 x + 0))))))))))))

noncomputable def reducedSource1562 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue597 x + ((1 : ℝ) * Sparse.eval nodeValue598 x + ((3 : ℝ) * Sparse.eval nodeValue601 x + ((1 : ℝ) * Sparse.eval nodeValue1125 x + ((3 : ℝ) * Sparse.eval nodeValue1127 x + ((3 : ℝ) * Sparse.eval nodeValue1233 x + ((3 : ℝ) * Sparse.eval nodeValue1234 x + ((6 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1265 x + ((3 : ℝ) * Sparse.eval nodeValue1266 x + ((1 : ℝ) * Sparse.eval nodeValue2957 x + ((3 : ℝ) * Sparse.eval nodeValue3099 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + 0))))))))))))

noncomputable def reducedSource1563 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1502 x + ((1 : ℝ) * Sparse.eval nodeValue1503 x + ((3 : ℝ) * Sparse.eval nodeValue1508 x + ((1 : ℝ) * Sparse.eval nodeValue2688 x + ((3 : ℝ) * Sparse.eval nodeValue2702 x + ((3 : ℝ) * Sparse.eval nodeValue3257 x + ((3 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((6 : ℝ) * Sparse.eval nodeValue3294 x + ((3 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((1 : ℝ) * Sparse.eval nodeValue3563 x + ((3 : ℝ) * Sparse.eval nodeValue3581 x + 0))))))))))))

noncomputable def reducedSource1564 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue637 x + ((3 : ℝ) * Sparse.eval nodeValue640 x + ((1 : ℝ) * Sparse.eval nodeValue651 x + ((1 : ℝ) * Sparse.eval nodeValue1293 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource1565 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1034 x + ((3 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue1081 x + ((3 : ℝ) * Sparse.eval nodeValue1228 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((1 : ℝ) * Sparse.eval nodeValue1256 x + ((3 : ℝ) * Sparse.eval nodeValue1260 x + ((3 : ℝ) * Sparse.eval nodeValue1286 x + ((6 : ℝ) * Sparse.eval nodeValue1291 x + ((3 : ℝ) * Sparse.eval nodeValue1299 x + ((1 : ℝ) * Sparse.eval nodeValue1405 x + ((1 : ℝ) * Sparse.eval nodeValue1435 x + ((3 : ℝ) * Sparse.eval nodeValue1441 x + 0))))))))))))

noncomputable def reducedSource1566 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1644 x + ((3 : ℝ) * Sparse.eval nodeValue1648 x + ((1 : ℝ) * Sparse.eval nodeValue1726 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

noncomputable def reducedSource1567 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4171 x + ((2 : ℝ) * Sparse.eval nodeValue4172 x + ((2 : ℝ) * Sparse.eval nodeValue4175 x + ((2 : ℝ) * Sparse.eval nodeValue4541 x + ((2 : ℝ) * Sparse.eval nodeValue4544 x + ((2 : ℝ) * Sparse.eval nodeValue4601 x + ((4 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((2 : ℝ) * Sparse.eval nodeValue4622 x + ((2 : ℝ) * Sparse.eval nodeValue4623 x + ((4 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1568 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue599 x + ((2 : ℝ) * Sparse.eval nodeValue600 x + ((2 : ℝ) * Sparse.eval nodeValue603 x + ((2 : ℝ) * Sparse.eval nodeValue1126 x + ((2 : ℝ) * Sparse.eval nodeValue1129 x + ((2 : ℝ) * Sparse.eval nodeValue1235 x + ((4 : ℝ) * Sparse.eval nodeValue1236 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1299 x + ((2 : ℝ) * Sparse.eval nodeValue1300 x + ((4 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue2958 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3122 x + 0)))))))))))))

noncomputable def reducedSource1569 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4456 x + ((4 : ℝ) * Sparse.eval nodeValue4495 x + ((4 : ℝ) * Sparse.eval nodeValue4497 x + ((4 : ℝ) * Sparse.eval nodeValue4599 x + ((4 : ℝ) * Sparse.eval nodeValue4601 x + ((4 : ℝ) * Sparse.eval nodeValue4616 x + ((4 : ℝ) * Sparse.eval nodeValue4618 x + ((4 : ℝ) * Sparse.eval nodeValue4622 x + 0)))))))

noncomputable def reducedSource1570 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1228 x + ((1 : ℝ) * Sparse.eval nodeValue2503 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

noncomputable def reducedSource1571 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4149 x + ((3 : ℝ) * Sparse.eval nodeValue4150 x + ((1 : ℝ) * Sparse.eval nodeValue4169 x + ((3 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4550 x + ((3 : ℝ) * Sparse.eval nodeValue4589 x + ((6 : ℝ) * Sparse.eval nodeValue4590 x + ((3 : ℝ) * Sparse.eval nodeValue4599 x + ((3 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4618 x + ((1 : ℝ) * Sparse.eval nodeValue5100 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + 0))))))))))))

noncomputable def reducedSource1572 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue577 x + ((3 : ℝ) * Sparse.eval nodeValue578 x + ((1 : ℝ) * Sparse.eval nodeValue597 x + ((1 : ℝ) * Sparse.eval nodeValue1161 x + ((3 : ℝ) * Sparse.eval nodeValue1162 x + ((3 : ℝ) * Sparse.eval nodeValue1212 x + ((6 : ℝ) * Sparse.eval nodeValue1213 x + ((3 : ℝ) * Sparse.eval nodeValue1233 x + ((3 : ℝ) * Sparse.eval nodeValue1266 x + ((1 : ℝ) * Sparse.eval nodeValue1298 x + ((1 : ℝ) * Sparse.eval nodeValue2999 x + ((3 : ℝ) * Sparse.eval nodeValue3087 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + 0))))))))))))

noncomputable def reducedSource1573 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1501 x + ((1 : ℝ) * Sparse.eval nodeValue1502 x + ((3 : ℝ) * Sparse.eval nodeValue1504 x + ((3 : ℝ) * Sparse.eval nodeValue3263 x + ((1 : ℝ) * Sparse.eval nodeValue3269 x + ((3 : ℝ) * Sparse.eval nodeValue3288 x + ((3 : ℝ) * Sparse.eval nodeValue3289 x + ((6 : ℝ) * Sparse.eval nodeValue3290 x + ((3 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((1 : ℝ) * Sparse.eval nodeValue3469 x + ((3 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + 0))))))))))))

noncomputable def reducedSource1574 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue625 x + ((1 : ℝ) * Sparse.eval nodeValue629 x + ((1 : ℝ) * Sparse.eval nodeValue637 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource1575 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4139 x + ((1 : ℝ) * Sparse.eval nodeValue4143 x + ((1 : ℝ) * Sparse.eval nodeValue4171 x + ((3 : ℝ) * Sparse.eval nodeValue4513 x + ((1 : ℝ) * Sparse.eval nodeValue4516 x + ((3 : ℝ) * Sparse.eval nodeValue4581 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((6 : ℝ) * Sparse.eval nodeValue4602 x + ((3 : ℝ) * Sparse.eval nodeValue4606 x + ((3 : ℝ) * Sparse.eval nodeValue4622 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + 0))))))))))))

noncomputable def reducedSource1576 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue567 x + ((1 : ℝ) * Sparse.eval nodeValue571 x + ((1 : ℝ) * Sparse.eval nodeValue599 x + ((3 : ℝ) * Sparse.eval nodeValue1097 x + ((1 : ℝ) * Sparse.eval nodeValue1100 x + ((3 : ℝ) * Sparse.eval nodeValue1200 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((6 : ℝ) * Sparse.eval nodeValue1236 x + ((3 : ℝ) * Sparse.eval nodeValue1240 x + ((3 : ℝ) * Sparse.eval nodeValue1299 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((1 : ℝ) * Sparse.eval nodeValue3076 x + ((3 : ℝ) * Sparse.eval nodeValue3100 x + 0))))))))))))

noncomputable def reducedSource1577 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1183 x + ((1 : ℝ) * Sparse.eval nodeValue2398 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2684 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1578 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1187 x + ((1 : ℝ) * Sparse.eval nodeValue2402 x + ((4 : ℝ) * Sparse.eval nodeValue2671 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0)))

noncomputable def reducedSource1579 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1100 x + ((1 : ℝ) * Sparse.eval nodeValue1187 x + ((1 : ℝ) * Sparse.eval nodeValue2402 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0)))

noncomputable def reducedSource1580 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1052 x + ((1 : ℝ) * Sparse.eval nodeValue2127 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((2 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1581 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1032 x + ((1 : ℝ) * Sparse.eval nodeValue2098 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1582 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1034 x + ((1 : ℝ) * Sparse.eval nodeValue2100 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((3 : ℝ) * Sparse.eval nodeValue2241 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))

noncomputable def reducedSource1583 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue732 x + ((1 : ℝ) * Sparse.eval nodeValue736 x + ((1 : ℝ) * Sparse.eval nodeValue805 x + ((1 : ℝ) * Sparse.eval nodeValue1644 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1584 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4150 x + ((2 : ℝ) * Sparse.eval nodeValue4152 x + ((1 : ℝ) * Sparse.eval nodeValue4171 x + ((2 : ℝ) * Sparse.eval nodeValue4364 x + ((2 : ℝ) * Sparse.eval nodeValue4366 x + ((2 : ℝ) * Sparse.eval nodeValue4438 x + ((4 : ℝ) * Sparse.eval nodeValue4439 x + ((2 : ℝ) * Sparse.eval nodeValue4456 x + ((4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((2 : ℝ) * Sparse.eval nodeValue4497 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4887 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + 0)))))))))))))

noncomputable def reducedSource1585 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1504 x + ((1 : ℝ) * Sparse.eval nodeValue1506 x + ((2 : ℝ) * Sparse.eval nodeValue1510 x + ((2 : ℝ) * Sparse.eval nodeValue1703 x + ((2 : ℝ) * Sparse.eval nodeValue1705 x + ((2 : ℝ) * Sparse.eval nodeValue1706 x + ((2 : ℝ) * Sparse.eval nodeValue1711 x + ((4 : ℝ) * Sparse.eval nodeValue1713 x + ((4 : ℝ) * Sparse.eval nodeValue1724 x + ((2 : ℝ) * Sparse.eval nodeValue1726 x + ((2 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((2 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2263 x + 0)))))))))))))

noncomputable def reducedSource1586 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue599 x + ((3 : ℝ) * Sparse.eval nodeValue1039 x + ((2 : ℝ) * Sparse.eval nodeValue1081 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))

noncomputable def reducedSource1587 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4098 x + ((2 : ℝ) * Sparse.eval nodeValue4100 x + ((1 : ℝ) * Sparse.eval nodeValue4113 x + ((2 : ℝ) * Sparse.eval nodeValue4341 x + ((2 : ℝ) * Sparse.eval nodeValue4344 x + ((4 : ℝ) * Sparse.eval nodeValue4396 x + ((2 : ℝ) * Sparse.eval nodeValue4399 x + ((2 : ℝ) * Sparse.eval nodeValue4417 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + 0)))))))))))))

noncomputable def reducedSource1588 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue535 x + ((2 : ℝ) * Sparse.eval nodeValue537 x + ((1 : ℝ) * Sparse.eval nodeValue550 x + ((2 : ℝ) * Sparse.eval nodeValue919 x + ((2 : ℝ) * Sparse.eval nodeValue922 x + ((4 : ℝ) * Sparse.eval nodeValue977 x + ((2 : ℝ) * Sparse.eval nodeValue980 x + ((2 : ℝ) * Sparse.eval nodeValue998 x + ((2 : ℝ) * Sparse.eval nodeValue1040 x + ((4 : ℝ) * Sparse.eval nodeValue1041 x + ((2 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2593 x + ((2 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + 0)))))))))))))

noncomputable def reducedSource1589 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4249 x + ((1 : ℝ) * Sparse.eval nodeValue4252 x + ((2 : ℝ) * Sparse.eval nodeValue4263 x + ((4 : ℝ) * Sparse.eval nodeValue4449 x + ((2 : ℝ) * Sparse.eval nodeValue4451 x + ((2 : ℝ) * Sparse.eval nodeValue4455 x + ((4 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4469 x + ((2 : ℝ) * Sparse.eval nodeValue4473 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((2 : ℝ) * Sparse.eval nodeValue4497 x + ((2 : ℝ) * Sparse.eval nodeValue4599 x + ((2 : ℝ) * Sparse.eval nodeValue4601 x + ((1 : ℝ) * Sparse.eval nodeValue4622 x + 0)))))))))))))

noncomputable def reducedSource1590 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1070 x + ((1 : ℝ) * Sparse.eval nodeValue2043 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1591 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1071 x + ((1 : ℝ) * Sparse.eval nodeValue2044 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((2 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1592 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue2046 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1593 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4169 x + ((1 : ℝ) * Sparse.eval nodeValue4172 x + ((1 : ℝ) * Sparse.eval nodeValue4173 x + ((2 : ℝ) * Sparse.eval nodeValue4176 x + ((1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4342 x + ((2 : ℝ) * Sparse.eval nodeValue4345 x + ((1 : ℝ) * Sparse.eval nodeValue4455 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4473 x + ((1 : ℝ) * Sparse.eval nodeValue4474 x + ((2 : ℝ) * Sparse.eval nodeValue4475 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((2 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + 0))))))))))))))))))))

noncomputable def reducedSource1594 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1502 x + ((1 : ℝ) * Sparse.eval nodeValue1507 x + ((1 : ℝ) * Sparse.eval nodeValue1508 x + ((2 : ℝ) * Sparse.eval nodeValue1512 x + ((1 : ℝ) * Sparse.eval nodeValue1664 x + ((1 : ℝ) * Sparse.eval nodeValue1665 x + ((2 : ℝ) * Sparse.eval nodeValue1668 x + ((1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1699 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((2 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((2 : ℝ) * Sparse.eval nodeValue1715 x + ((2 : ℝ) * Sparse.eval nodeValue1727 x + ((2 : ℝ) * Sparse.eval nodeValue1728 x + ((2 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2265 x + 0))))))))))))))))))))

noncomputable def reducedSource1595 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4171 x + ((3 : ℝ) * Sparse.eval nodeValue4175 x + ((1 : ℝ) * Sparse.eval nodeValue4182 x + ((3 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4351 x + ((3 : ℝ) * Sparse.eval nodeValue4456 x + ((6 : ℝ) * Sparse.eval nodeValue4458 x + ((3 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + ((3 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((3 : ℝ) * Sparse.eval nodeValue4893 x + 0))))))))))))

noncomputable def reducedSource1596 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue995 x + ((1 : ℝ) * Sparse.eval nodeValue1940 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue2219 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

noncomputable def reducedSource1597 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue996 x + ((1 : ℝ) * Sparse.eval nodeValue1941 x + ((2 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2225 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))

noncomputable def reducedSource1598 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4079 x + ((4 : ℝ) * Sparse.eval nodeValue4143 x + ((1 : ℝ) * Sparse.eval nodeValue4164 x + ((4 : ℝ) * Sparse.eval nodeValue4306 x + ((12 : ℝ) * Sparse.eval nodeValue4399 x + ((4 : ℝ) * Sparse.eval nodeValue4451 x + ((4 : ℝ) * Sparse.eval nodeValue4833 x + 0))))))

noncomputable def reducedSource1599 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4068 x + ((3 : ℝ) * Sparse.eval nodeValue4100 x + ((1 : ℝ) * Sparse.eval nodeValue4104 x + ((1 : ℝ) * Sparse.eval nodeValue4117 x + ((3 : ℝ) * Sparse.eval nodeValue4232 x + ((1 : ℝ) * Sparse.eval nodeValue4236 x + ((6 : ℝ) * Sparse.eval nodeValue4249 x + ((3 : ℝ) * Sparse.eval nodeValue4252 x + ((3 : ℝ) * Sparse.eval nodeValue4263 x + ((3 : ℝ) * Sparse.eval nodeValue4267 x + ((1 : ℝ) * Sparse.eval nodeValue4451 x + ((3 : ℝ) * Sparse.eval nodeValue4456 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + 0))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end


