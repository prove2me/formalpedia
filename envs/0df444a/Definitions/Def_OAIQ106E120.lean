-- Prove2me | Definitions.Def_OAIQ106E120
-- name    : OAIQ106E120
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T22:53:42.802414+00:00
-- url     : https://prove2.me/theorems/abd31c37-6ca2-4634-9bfc-4a427e1ea94d
-- title:
--   Definitions bundle OAIQ106E120 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 905 declarations of OpenAI's Lean: 905 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1167`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1169`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow117`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1170`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1171`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1172`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1173`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1174`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1175`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1176`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1177`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1178`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1179`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow118`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1180`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1181`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1182`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1183`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1184`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1185`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1186`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1187`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1188`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1189`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow119`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1190`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1191`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1192`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1193`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1194`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1195`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1196`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1197`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1198`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1199`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow12`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow120`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1200`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1201`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1202` and 865 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSources_Arithmetic0`, `MutuallyUnbiased_MixedSources_Arithmetic1`, `MutuallyUnbiased_MixedSources_Arithmetic10`, `MutuallyUnbiased_MixedSources_Arithmetic100`, `MutuallyUnbiased_MixedSources_Arithmetic101`, `MutuallyUnbiased_MixedSources_Arithmetic102`, `MutuallyUnbiased_MixedSources_Arithmetic103`, `MutuallyUnbiased_MixedSources_Arithmetic104`, `MutuallyUnbiased_MixedSources_Arithmetic105`, `MutuallyUnbiased_MixedSources_Arithmetic106`, `MutuallyUnbiased_MixedSources_Arithmetic107`, `MutuallyUnbiased_MixedSources_Arithmetic108`, `MutuallyUnbiased_MixedSources_Arithmetic109`, `MutuallyUnbiased_MixedSources_Arithmetic11`, `MutuallyUnbiased_MixedSources_Arithmetic110`, `MutuallyUnbiased_MixedSources_Arithmetic111`, `MutuallyUnbiased_MixedSources_Arithmetic112`, `MutuallyUnbiased_MixedSources_Arithmetic113`, `MutuallyUnbiased_MixedSources_Arithmetic114`, `MutuallyUnbiased_MixedSources_Arithmetic115`, `MutuallyUnbiased_MixedSources_Arithmetic116`, `MutuallyUnbiased_MixedSources_Arithmetic117`, `MutuallyUnbiased_MixedSources_Arithmetic118`, `MutuallyUnbiased_MixedSources_Arithmetic119`, `MutuallyUnbiased_MixedSources_Arithmetic12`, `MutuallyUnbiased_MixedSources_Arithmetic120`, `MutuallyUnbiased_MixedSources_Arithmetic121`, `MutuallyUnbiased_MixedSources_Arithmetic122`, `MutuallyUnbiased_MixedSources_Arithmetic123`, `MutuallyUnbiased_MixedSources_Arithmetic132`, `MutuallyUnbiased_MixedSources_Arithmetic7`, `MutuallyUnbiased_MixedSources_Arithmetic72`, `MutuallyUnbiased_MixedSources_Arithmetic73`, `MutuallyUnbiased_MixedSources_Arithmetic74`, `MutuallyUnbiased_MixedSources_Arithmetic75`, `MutuallyUnbiased_MixedSources_Arithmetic76`, `MutuallyUnbiased_MixedSources_Arithmetic77`, `MutuallyUnbiased_MixedSources_Arithmetic78`, `MutuallyUnbiased_MixedSources_Arithmetic79`, `MutuallyUnbiased_MixedSources_Arithmetic8`, `MutuallyUnbiased_MixedSources_Arithmetic80`, `MutuallyUnbiased_MixedSources_Arithmetic81`, `MutuallyUnbiased_MixedSources_Arithmetic82`, `MutuallyUnbiased_MixedSources_Arithmetic83`, `MutuallyUnbiased_MixedSources_Arithmetic84`, `MutuallyUnbiased_MixedSources_Arithmetic85`, `MutuallyUnbiased_MixedSources_Arithmetic86`, `MutuallyUnbiased_MixedSources_Arithmetic87`, `MutuallyUnbiased_MixedSources_Arithmetic88`, `MutuallyUnbiased_MixedSources_Arithmetic89`, `MutuallyUnbiased_MixedSources_Arithmetic9`, `MutuallyUnbiased_MixedSources_Arithmetic90`, `MutuallyUnbiased_MixedSources_Arithmetic91`, `MutuallyUnbiased_MixedSources_Arithmetic92`, `MutuallyUnbiased_MixedSources_Arithmetic93`, `MutuallyUnbiased_MixedSources_Arithmetic94`, `MutuallyUnbiased_MixedSources_Arithmetic95`, `MutuallyUnbiased_MixedSources_Arithmetic96`, `MutuallyUnbiased_MixedSources_Arithmetic97`, `MutuallyUnbiased_MixedSources_Arithmetic98`, `MutuallyUnbiased_MixedSources_Arithmetic99`, `MutuallyUnbiased_MixedTargets_OriginalBlock0`, `MutuallyUnbiased_MixedTargets_ReductionMergeData32`.
--
--   **Imports.** It imports the bundle `OAIQ106E043` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E131`; the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound11_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow12 : Integer.Sparse Master := [(Sum.inl 0, 379), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, -240), (Sum.inl 4, 160), (Sum.inl 1, -140), (Sum.inr 3077, -4320), (Sum.inr 3622, -4320), (Sum.inr 3625, -4320), (Sum.inr 3801, -4320), (Sum.inr 3809, -8640), (Sum.inr 3812, -4320), (Sum.inr 3813, -8640), (Sum.inr 3901, -4320), (Sum.inr 3909, -4320), (Sum.inr 3910, -4320), (Sum.inr 4010, -4320), (Sum.inr 4025, -4320)]

def numericRow13 : Integer.Sparse Master := [(Sum.inl 0, -55), (Sum.inl 12, 40), (Sum.inl 1, 15), (Sum.inr 3077, 1080), (Sum.inr 3801, 1080), (Sum.inr 3809, 2160), (Sum.inr 4010, 1080), (Sum.inr 4025, 1080)]

def numericRow14 : Integer.Sparse Master := [(Sum.inl 0, 79), (Sum.inl 12, -40), (Sum.inl 1, 105), (Sum.inr 2243, -720), (Sum.inr 2244, -1440), (Sum.inr 2262, -1440), (Sum.inr 3800, -1440), (Sum.inr 3805, -1440), (Sum.inr 3901, -1440), (Sum.inr 3902, -1440), (Sum.inr 3903, -2880)]

def numericRow15 : Integer.Sparse Master := [(Sum.inl 0, 469), (Sum.inl 4, 560), (Sum.inl 1, -525), (Sum.inr 2764, -4320), (Sum.inr 2765, -2160), (Sum.inr 2782, -2160), (Sum.inr 3581, -4320), (Sum.inr 3582, -2160), (Sum.inr 3583, -2160), (Sum.inr 3632, -2160), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3903, -4320), (Sum.inr 3907, -2160), (Sum.inr 3910, -4320), (Sum.inr 3913, -4320), (Sum.inr 3983, -8640), (Sum.inr 4010, -4320)]

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

def numericRow16 : Integer.Sparse Master := [(Sum.inl 0, -67), (Sum.inl 4, -80), (Sum.inl 1, 75), (Sum.inr 2764, 1080), (Sum.inr 2765, 540), (Sum.inr 2782, 540), (Sum.inr 3876, 1080), (Sum.inr 3907, 540), (Sum.inr 3910, 1080), (Sum.inr 3913, 540), (Sum.inr 3983, 1080)]

def numericRow17 : Integer.Sparse Master := [(Sum.inl 0, 91), (Sum.inl 4, 80), (Sum.inl 1, 45), (Sum.inr 2739, -1440), (Sum.inr 2740, -720), (Sum.inr 2743, -720), (Sum.inr 3534, -1440), (Sum.inr 3548, -720), (Sum.inr 3623, -720), (Sum.inr 3958, -1440), (Sum.inr 3961, -1440), (Sum.inr 3963, -720), (Sum.inr 3974, -1440), (Sum.inr 4010, -1440)]

def numericRow18 : Integer.Sparse Master := [(Sum.inl 0, 1115), (Sum.inl 2, -10), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, -240), (Sum.inl 1, 875), (Sum.inr 2721, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2739, -4320), (Sum.inr 3532, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3544, -4320), (Sum.inr 3622, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3845, -8640), (Sum.inr 3902, -4320), (Sum.inr 3903, -4320), (Sum.inr 3957, -8640), (Sum.inr 3958, -8640), (Sum.inr 3961, -8640), (Sum.inr 3974, -8640), (Sum.inr 4010, -4320), (Sum.inr 4046, -8640), (Sum.inr 4047, -4320)]

def numericRow19 : Integer.Sparse Master := [(Sum.inl 0, -161), (Sum.inl 4, 80), (Sum.inl 1, -135), (Sum.inr 2721, 1080), (Sum.inr 2722, 1080), (Sum.inr 2723, 1080), (Sum.inr 2739, 1080), (Sum.inr 3838, 1080), (Sum.inr 3845, 1080), (Sum.inr 3902, 1080), (Sum.inr 3957, 1080), (Sum.inr 3958, 1080), (Sum.inr 3961, 1080), (Sum.inr 3974, 1080), (Sum.inr 4010, 1080)]

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

def numericRow160 : Integer.Sparse Master := [(Sum.inr 1042, 1), (Sum.inr 2021, 1), (Sum.inr 2108, 1), (Sum.inr 2253, 1), (Sum.inr 2262, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

def numericRow161 : Integer.Sparse Master := [(Sum.inr 2124, 1), (Sum.inr 2125, 1), (Sum.inr 2126, 1), (Sum.inr 2133, 1), (Sum.inr 2253, 1), (Sum.inr 2513, 1), (Sum.inr 4084, -1)]

def numericRow162 : Integer.Sparse Master := [(Sum.inr 1030, 1), (Sum.inr 2014, 1), (Sum.inr 2097, 1), (Sum.inr 2126, 1), (Sum.inr 2253, 2), (Sum.inr 4084, -1)]

def numericRow163 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 2, -50), (Sum.inl 3, -400), (Sum.inl 13, -240), (Sum.inl 12, -160), (Sum.inl 4, -80), (Sum.inl 1, 70), (Sum.inr 793, 4320), (Sum.inr 794, 4320), (Sum.inr 796, 4320), (Sum.inr 808, 4320), (Sum.inr 825, 4320), (Sum.inr 1902, 4320), (Sum.inr 1904, 4320), (Sum.inr 1910, 4320), (Sum.inr 1923, 4320), (Sum.inr 2034, 4320), (Sum.inr 2035, 4320), (Sum.inr 2039, 4320), (Sum.inr 2055, 4320), (Sum.inr 2089, 4320), (Sum.inr 2090, 4320), (Sum.inr 2094, 4320), (Sum.inr 2108, 4320), (Sum.inr 2196, 4320), (Sum.inr 2197, 4320), (Sum.inr 2207, 4320), (Sum.inr 2217, 4320), (Sum.inr 2250, 4320), (Sum.inr 2251, 4320), (Sum.inr 2259, 4320), (Sum.inr 2274, 4320), (Sum.inr 3803, 4320), (Sum.inr 3813, 4320), (Sum.inr 3814, 4320)]

def numericRow164 : Integer.Sparse Master := [(Sum.inr 3222, 1), (Sum.inr 3803, 1), (Sum.inr 3809, 2), (Sum.inr 3814, 2), (Sum.inr 4092, -1)]

def numericRow165 : Integer.Sparse Master := [(Sum.inr 1463, 1), (Sum.inr 1465, 2), (Sum.inr 1466, 2), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

def numericRow166 : Integer.Sparse Master := [(Sum.inr 1463, 1), (Sum.inr 3170, 2), (Sum.inr 3196, 2), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

def numericRow167 : Integer.Sparse Master := [(Sum.inr 2474, 2), (Sum.inr 3217, 2), (Sum.inr 3222, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

def numericRow168 : Integer.Sparse Master := [(Sum.inr 1466, 1), (Sum.inr 3174, 1), (Sum.inr 3180, 1), (Sum.inr 3198, 1), (Sum.inr 3217, 1), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

def numericRow169 : Integer.Sparse Master := [(Sum.inr 2497, 1), (Sum.inr 2716, 1), (Sum.inr 3196, 1), (Sum.inr 3198, 1), (Sum.inr 3222, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

def numericRow170 : Integer.Sparse Master := [(Sum.inr 1465, 1), (Sum.inr 2474, 1), (Sum.inr 2486, 1), (Sum.inr 2497, 1), (Sum.inr 2716, 1), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

def numericRow171 : Integer.Sparse Master := [(Sum.inr 2233, 1), (Sum.inr 3567, 3), (Sum.inr 3619, 1), (Sum.inr 4083, -1)]

def numericRow172 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 1015, 1), (Sum.inr 1021, 3), (Sum.inr 2233, 1), (Sum.inr 4083, -1)]

def numericRow173 : Integer.Sparse Master := [(Sum.inr 1021, 1), (Sum.inr 2089, 2), (Sum.inr 2233, 1), (Sum.inr 2243, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

def numericRow174 : Integer.Sparse Master := [(Sum.inr 2083, 1), (Sum.inr 2084, 1), (Sum.inr 2089, 2), (Sum.inr 2233, 1), (Sum.inr 3567, 1), (Sum.inr 4083, -1)]

def numericRow175 : Integer.Sparse Master := [(Sum.inr 1015, 1), (Sum.inr 2084, 3), (Sum.inr 2233, 2), (Sum.inr 4083, -1)]

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

def numericRow1600 : Integer.Sparse Master := [(Sum.inr 4056, 1), (Sum.inr 4057, 4), (Sum.inr 4063, 4), (Sum.inr 4068, 4), (Sum.inr 4069, 12), (Sum.inr 4079, 1), (Sum.inr 4083, 4)]

def numericRow1601 : Integer.Sparse Master := [(Sum.inr 940, 1), (Sum.inr 1820, 1), (Sum.inr 1971, 2), (Sum.inr 2063, 1), (Sum.inr 2065, 1), (Sum.inr 4085, -1)]

def numericRow1602 : Integer.Sparse Master := [(Sum.inr 2220, 2), (Sum.inr 2222, 1), (Sum.inr 2230, 1), (Sum.inr 2282, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

def numericRow1603 : Integer.Sparse Master := [(Sum.inr 931, 1), (Sum.inr 1813, 1), (Sum.inr 1965, 1), (Sum.inr 2026, 1), (Sum.inr 2037, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

def numericRow1604 : Integer.Sparse Master := [(Sum.inr 914, 1), (Sum.inr 1797, 1), (Sum.inr 1957, 1), (Sum.inr 1980, 1), (Sum.inr 2026, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

def numericRow1605 : Integer.Sparse Master := [(Sum.inr 949, 1), (Sum.inr 1828, 1), (Sum.inr 1976, 1), (Sum.inr 2092, 2), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

def numericRow1606 : Integer.Sparse Master := [(Sum.inr 2219, 1), (Sum.inr 2220, 2), (Sum.inr 2221, 1), (Sum.inr 2224, 2), (Sum.inr 4081, -1)]

def numericRow1607 : Integer.Sparse Master := [(Sum.inr 925, 1), (Sum.inr 1808, 1), (Sum.inr 1961, 1), (Sum.inr 2035, 1), (Sum.inr 2054, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

def numericRow1608 : Integer.Sparse Master := [(Sum.inr 1137, 1), (Sum.inr 2340, 1), (Sum.inr 2430, 1), (Sum.inr 2486, 1), (Sum.inr 2497, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

def numericRow1609 : Integer.Sparse Master := [(Sum.inr 1948, 1), (Sum.inr 2207, 1), (Sum.inr 3358, 1), (Sum.inr 3437, 1), (Sum.inr 3472, 1), (Sum.inr 3481, 1), (Sum.inr 4081, -1)]

def numericRow1610 : Integer.Sparse Master := [(Sum.inr 1910, 1), (Sum.inr 1916, 1), (Sum.inr 1917, 1), (Sum.inr 1948, 1), (Sum.inr 2207, 1), (Sum.inr 3472, 1), (Sum.inr 4081, -1)]

def numericRow1611 : Integer.Sparse Master := [(Sum.inr 2201, 1), (Sum.inr 2203, 1), (Sum.inr 2207, 1), (Sum.inr 2224, 1), (Sum.inr 2259, 1), (Sum.inr 3481, 1), (Sum.inr 4081, -1)]

def numericRow1612 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 1790, 1), (Sum.inr 1973, 1), (Sum.inr 2009, 1), (Sum.inr 2020, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

def numericRow1613 : Integer.Sparse Master := [(Sum.inr 1116, 1), (Sum.inr 2323, 1), (Sum.inr 2440, 1), (Sum.inr 2471, 2), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

def numericRow1614 : Integer.Sparse Master := [(Sum.inr 1940, 1), (Sum.inr 2201, 1), (Sum.inr 3350, 1), (Sum.inr 3466, 1), (Sum.inr 3481, 2), (Sum.inr 4081, -1)]

def numericRow1615 : Integer.Sparse Master := [(Sum.inr 909, 1), (Sum.inr 1793, 1), (Sum.inr 1976, 1), (Sum.inr 2010, 2), (Sum.inr 2023, 1), (Sum.inr 4083, -1)]

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

def numericRow1616 : Integer.Sparse Master := [(Sum.inr 1903, 1), (Sum.inr 1904, 1), (Sum.inr 1913, 1), (Sum.inr 1925, 1), (Sum.inr 2196, 1), (Sum.inr 3464, 1), (Sum.inr 4080, -1)]

def numericRow1617 : Integer.Sparse Master := [(Sum.inr 954, 1), (Sum.inr 1832, 1), (Sum.inr 1980, 2), (Sum.inr 2113, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

def numericRow1618 : Integer.Sparse Master := [(Sum.inr 945, 1), (Sum.inr 1825, 1), (Sum.inr 1973, 1), (Sum.inr 2090, 1), (Sum.inr 2107, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

def numericRow1619 : Integer.Sparse Master := [(Sum.inr 1121, 1), (Sum.inr 2327, 1), (Sum.inr 2423, 1), (Sum.inr 2443, 1), (Sum.inr 2486, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

def numericRow1620 : Integer.Sparse Master := [(Sum.inr 1946, 1), (Sum.inr 2259, 1), (Sum.inr 3355, 1), (Sum.inr 3434, 1), (Sum.inr 3481, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

def numericRow1621 : Integer.Sparse Master := [(Sum.inr 2259, 2), (Sum.inr 2261, 1), (Sum.inr 2267, 1), (Sum.inr 2287, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

def numericRow1622 : Integer.Sparse Master := [(Sum.inr 1923, 1), (Sum.inr 1927, 1), (Sum.inr 1928, 1), (Sum.inr 1949, 1), (Sum.inr 2217, 1), (Sum.inr 3480, 1), (Sum.inr 4082, -1)]

def numericRow1623 : Integer.Sparse Master := [(Sum.inr 1146, 1), (Sum.inr 2346, 1), (Sum.inr 2435, 2), (Sum.inr 2520, 1), (Sum.inr 2522, 1), (Sum.inr 4084, -1)]

def numericRow1624 : Integer.Sparse Master := [(Sum.inr 1951, 1), (Sum.inr 2267, 1), (Sum.inr 2837, 2), (Sum.inr 2842, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

def numericRow1625 : Integer.Sparse Master := [(Sum.inr 1132, 1), (Sum.inr 2335, 1), (Sum.inr 2426, 1), (Sum.inr 2495, 1), (Sum.inr 2512, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

def numericRow1626 : Integer.Sparse Master := [(Sum.inr 1917, 1), (Sum.inr 3343, 1), (Sum.inr 3368, 1), (Sum.inr 3385, 1), (Sum.inr 3468, 1), (Sum.inr 3472, 1), (Sum.inr 4081, -1)]

def numericRow1627 : Integer.Sparse Master := [(Sum.inr 3466, 1), (Sum.inr 3468, 2), (Sum.inr 3472, 1), (Sum.inr 3481, 2), (Sum.inr 4081, -1)]

def numericRow1628 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 2320, 1), (Sum.inr 2437, 1), (Sum.inr 2470, 1), (Sum.inr 2480, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

def numericRow1629 : Integer.Sparse Master := [(Sum.inr 1907, 1), (Sum.inr 3443, 1), (Sum.inr 3466, 1), (Sum.inr 3468, 2), (Sum.inr 4081, -1)]

def numericRow1630 : Integer.Sparse Master := [(Sum.inr 1317, 1), (Sum.inr 2426, 1), (Sum.inr 2434, 1), (Sum.inr 2519, 1), (Sum.inr 2558, 1), (Sum.inr 2881, 1), (Sum.inr 4092, -1)]

def numericRow1631 : Integer.Sparse Master := [(Sum.inr 1155, 1), (Sum.inr 2352, 1), (Sum.inr 2434, 1), (Sum.inr 2524, 1), (Sum.inr 2558, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

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

def numericRow1632 : Integer.Sparse Master := [(Sum.inr 1337, 1), (Sum.inr 2437, 1), (Sum.inr 2442, 1), (Sum.inr 2485, 1), (Sum.inr 2618, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

def numericRow1633 : Integer.Sparse Master := [(Sum.inr 2047, 1), (Sum.inr 3385, 1), (Sum.inr 3443, 1), (Sum.inr 3468, 1), (Sum.inr 3523, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

def numericRow1634 : Integer.Sparse Master := [(Sum.inr 1998, 1), (Sum.inr 2004, 1), (Sum.inr 2006, 1), (Sum.inr 2049, 1), (Sum.inr 2230, 1), (Sum.inr 3523, 1), (Sum.inr 4081, -1)]

def numericRow1635 : Integer.Sparse Master := [(Sum.inr 3468, 2), (Sum.inr 3519, 1), (Sum.inr 3523, 2), (Sum.inr 3615, 1), (Sum.inr 4081, -1)]

def numericRow1636 : Integer.Sparse Master := [(Sum.inr 2006, 1), (Sum.inr 3343, 1), (Sum.inr 3353, 1), (Sum.inr 3468, 1), (Sum.inr 3523, 1), (Sum.inr 4081, -1)]

def numericRow1637 : Integer.Sparse Master := [(Sum.inr 2118, 1), (Sum.inr 2121, 1), (Sum.inr 2123, 1), (Sum.inr 2129, 1), (Sum.inr 2216, 1), (Sum.inr 2735, 1), (Sum.inr 4080, -1)]

def numericRow1638 : Integer.Sparse Master := [(Sum.inr 1148, 1), (Sum.inr 2347, 1), (Sum.inr 2425, 1), (Sum.inr 2482, 1), (Sum.inr 2553, 1), (Sum.inr 4092, -1)]

def numericRow1639 : Integer.Sparse Master := [(Sum.inr 3432, 1), (Sum.inr 3434, 1), (Sum.inr 3437, 1), (Sum.inr 3481, 1), (Sum.inr 3519, 1), (Sum.inr 4081, -1)]

def numericRow1640 : Integer.Sparse Master := [(Sum.inr 1986, 1), (Sum.inr 1989, 1), (Sum.inr 1996, 1), (Sum.inr 2015, 1), (Sum.inr 2203, 1), (Sum.inr 4081, -1)]

def numericRow1641 : Integer.Sparse Master := [(Sum.inr 1996, 1), (Sum.inr 3368, 1), (Sum.inr 3432, 1), (Sum.inr 3468, 1), (Sum.inr 3519, 1), (Sum.inr 4081, -1)]

def numericRow1642 : Integer.Sparse Master := [(Sum.inr 2203, 1), (Sum.inr 3468, 1), (Sum.inr 3481, 1), (Sum.inr 3530, 1), (Sum.inr 3608, 1), (Sum.inr 4081, -1)]

def numericRow1643 : Integer.Sparse Master := [(Sum.inr 1327, 1), (Sum.inr 2422, 1), (Sum.inr 2429, 1), (Sum.inr 2485, 1), (Sum.inr 2543, 1), (Sum.inr 2924, 1), (Sum.inr 4091, -1)]

def numericRow1644 : Integer.Sparse Master := [(Sum.inr 1150, 1), (Sum.inr 2349, 1), (Sum.inr 2429, 1), (Sum.inr 2543, 2), (Sum.inr 2556, 1), (Sum.inr 4091, -1)]

def numericRow1645 : Integer.Sparse Master := [(Sum.inr 2071, 1), (Sum.inr 2073, 1), (Sum.inr 2077, 1), (Sum.inr 2086, 1), (Sum.inr 2191, 1), (Sum.inr 3558, 1), (Sum.inr 4079, -1)]

def numericRow1646 : Integer.Sparse Master := [(Sum.inr 2454, 1), (Sum.inr 2456, 1), (Sum.inr 2462, 1), (Sum.inr 2491, 1), (Sum.inr 2698, 1), (Sum.inr 3796, 1), (Sum.inr 4090, -1)]

def numericRow1647 : Integer.Sparse Master := [(Sum.inr 1992, 1), (Sum.inr 1994, 1), (Sum.inr 2000, 1), (Sum.inr 2031, 1), (Sum.inr 2216, 1), (Sum.inr 3517, 1), (Sum.inr 4080, -1)]

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

def numericRow1648 : Integer.Sparse Master := [(Sum.inl 0, 53), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 1, 260), (Sum.inr 1136, -2160), (Sum.inr 1140, -540), (Sum.inr 1145, -1080), (Sum.inr 2815, -2160), (Sum.inr 2820, -540), (Sum.inr 3273, -2160), (Sum.inr 3275, -540), (Sum.inr 3277, -1080), (Sum.inr 3310, -1080), (Sum.inr 3588, -2160), (Sum.inr 3596, -540), (Sum.inr 3603, -2160), (Sum.inr 3608, -2160), (Sum.inr 3614, -1080)]

def numericRow1649 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 1, -260), (Sum.inr 1136, 2160), (Sum.inr 1140, 540), (Sum.inr 1145, 1080), (Sum.inr 2815, 2160), (Sum.inr 2820, 540)]

def numericRow1650 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 5, -4), (Sum.inl 6, -1), (Sum.inl 1, -14), (Sum.inr 924, -864), (Sum.inr 928, -216), (Sum.inr 938, -432), (Sum.inr 1043, -432), (Sum.inr 1674, -864), (Sum.inr 1677, -216), (Sum.inr 1693, -432), (Sum.inr 1725, -432), (Sum.inr 2334, -864), (Sum.inr 2344, -216), (Sum.inr 2425, -432), (Sum.inr 2482, -864), (Sum.inr 2726, -216), (Sum.inr 3411, -864), (Sum.inr 3422, -216), (Sum.inr 3449, -432), (Sum.inr 3468, -864), (Sum.inr 3545, -216), (Sum.inr 3607, -864), (Sum.inr 3616, -432), (Sum.inr 3627, -432)]

def numericRow1651 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 5, 4), (Sum.inl 6, 1), (Sum.inl 1, 14), (Sum.inr 924, 864), (Sum.inr 928, 216), (Sum.inr 938, 432), (Sum.inr 1043, 432), (Sum.inr 2334, 864), (Sum.inr 2344, 216), (Sum.inr 2425, 432), (Sum.inr 2482, 864), (Sum.inr 2726, 216)]

def numericRow1652 : Integer.Sparse Master := [(Sum.inl 0, 71), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 1, -40), (Sum.inr 930, -1440), (Sum.inr 934, -720), (Sum.inr 939, -720), (Sum.inr 1046, -720), (Sum.inr 1131, -1440), (Sum.inr 1144, -720), (Sum.inr 1690, -1440), (Sum.inr 1692, -720), (Sum.inr 1694, -720), (Sum.inr 1750, -720), (Sum.inr 2339, -1440), (Sum.inr 2345, -720), (Sum.inr 2429, -1440), (Sum.inr 2434, -1440), (Sum.inr 2485, -1440), (Sum.inr 3264, -1440), (Sum.inr 3276, -720), (Sum.inr 3310, -720), (Sum.inr 3420, -1440), (Sum.inr 3423, -720), (Sum.inr 3455, -1440), (Sum.inr 3457, -1440), (Sum.inr 3481, -1440), (Sum.inr 3607, -1440), (Sum.inr 3613, -1440), (Sum.inr 3614, -720), (Sum.inr 3615, -1440), (Sum.inr 3616, -720), (Sum.inr 3632, -720), (Sum.inr 3634, -720)]

def numericRow1653 : Integer.Sparse Master := [(Sum.inl 0, -71), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 1, 40), (Sum.inr 930, 1440), (Sum.inr 934, 720), (Sum.inr 939, 720), (Sum.inr 1046, 720), (Sum.inr 1131, 1440), (Sum.inr 1144, 720), (Sum.inr 2339, 1440), (Sum.inr 2345, 720), (Sum.inr 2429, 1440), (Sum.inr 2434, 1440), (Sum.inr 2485, 1440)]

def numericRow1654 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 1, 100), (Sum.inr 2025, -4320), (Sum.inr 2062, -2160), (Sum.inr 2112, -2160), (Sum.inr 2224, -4320), (Sum.inr 2230, -2160), (Sum.inr 2287, -2160), (Sum.inr 2482, -4320), (Sum.inr 2485, -4320), (Sum.inr 2519, -2160), (Sum.inr 3468, -4320), (Sum.inr 3481, -4320), (Sum.inr 3486, -2160), (Sum.inr 3608, -2160), (Sum.inr 5128, 8640), (Sum.inr 5139, 17280)]

def numericRow1655 : Integer.Sparse Master := [(Sum.inl 0, 45), (Sum.inl 5, -20), (Sum.inl 2, -5), (Sum.inl 7, -80), (Sum.inl 3, 80), (Sum.inl 12, -80), (Sum.inl 1, 150), (Sum.inr 737, -4320), (Sum.inr 740, -2160), (Sum.inr 743, -2160), (Sum.inr 828, -2160), (Sum.inr 840, -4320), (Sum.inr 842, -2160), (Sum.inr 844, -2160), (Sum.inr 857, -2160), (Sum.inr 1123, -4320), (Sum.inr 1143, -2160), (Sum.inr 1297, -2160), (Sum.inr 1812, -4320), (Sum.inr 1819, -2160), (Sum.inr 1877, -4320), (Sum.inr 1881, -4320), (Sum.inr 1926, -4320), (Sum.inr 1935, -4320), (Sum.inr 1937, -4320), (Sum.inr 1939, -4320), (Sum.inr 1948, -4320), (Sum.inr 2110, -4320), (Sum.inr 2112, -4320), (Sum.inr 2115, -2160), (Sum.inr 2165, -4320), (Sum.inr 2167, -2160), (Sum.inr 2169, -2160), (Sum.inr 2275, -4320), (Sum.inr 2276, -2160), (Sum.inr 2279, -4320), (Sum.inr 2281, -2160), (Sum.inr 2287, -4320), (Sum.inr 2289, -2160), (Sum.inr 2294, -2160), (Sum.inr 2954, -4320), (Sum.inr 3606, -4320), (Sum.inr 3614, -2160), (Sum.inr 3633, -2160), (Sum.inr 3907, -2160)]

def numericRow1656 : Integer.Sparse Master := [(Sum.inl 0, -45), (Sum.inl 5, 20), (Sum.inl 2, 5), (Sum.inl 7, 80), (Sum.inl 3, -80), (Sum.inl 12, 80), (Sum.inl 1, -150), (Sum.inr 737, 4320), (Sum.inr 740, 2160), (Sum.inr 743, 2160), (Sum.inr 828, 2160), (Sum.inr 1123, 4320), (Sum.inr 1143, 2160), (Sum.inr 1297, 2160), (Sum.inr 1812, 4320), (Sum.inr 1819, 2160), (Sum.inr 1877, 4320), (Sum.inr 1881, 4320), (Sum.inr 1926, 4320), (Sum.inr 2110, 4320), (Sum.inr 2112, 4320), (Sum.inr 2115, 2160), (Sum.inr 2279, 2160), (Sum.inr 2281, 2160), (Sum.inr 2954, 4320)]

def numericRow1657 : Integer.Sparse Master := [(Sum.inr 1046, -1), (Sum.inr 1750, -1), (Sum.inr 2025, -2), (Sum.inr 2107, -2), (Sum.inr 2116, -1), (Sum.inr 2224, -2), (Sum.inr 2247, -1), (Sum.inr 2260, -2), (Sum.inr 2288, -1), (Sum.inr 2290, -1), (Sum.inr 2782, -1), (Sum.inr 3583, -1), (Sum.inr 4353, 8), (Sum.inr 4358, 4), (Sum.inr 4362, 4), (Sum.inr 4367, 8), (Sum.inr 4374, 4), (Sum.inr 4464, 4), (Sum.inr 4699, 8), (Sum.inr 4705, 4), (Sum.inr 4772, 8), (Sum.inr 4777, 8), (Sum.inr 4853, 8), (Sum.inr 5173, 8), (Sum.inr 5175, 4), (Sum.inr 5295, 4)]

def numericRow1658 : Integer.Sparse Master := [(Sum.inr 1686, 2), (Sum.inr 1687, 1), (Sum.inr 1695, 1), (Sum.inr 1720, 2), (Sum.inr 1745, 1), (Sum.inr 1748, 1), (Sum.inr 1750, 1), (Sum.inr 2198, 2), (Sum.inr 2223, 2), (Sum.inr 2224, 2), (Sum.inr 2256, 2), (Sum.inr 2259, 2), (Sum.inr 2260, 2), (Sum.inr 2286, 1), (Sum.inr 2288, 1), (Sum.inr 2290, 1), (Sum.inr 2735, 2), (Sum.inr 2761, 1), (Sum.inr 2781, 1), (Sum.inr 2782, 1)]

def numericRow1659 : Integer.Sparse Master := [(Sum.inr 953, 1), (Sum.inr 1831, 1), (Sum.inr 1979, 2), (Sum.inr 2112, 1), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

def numericRow1660 : Integer.Sparse Master := [(Sum.inr 1336, 1), (Sum.inr 1973, 1), (Sum.inr 1979, 1), (Sum.inr 2025, 1), (Sum.inr 2112, 1), (Sum.inr 2952, 1), (Sum.inr 4083, -1)]

def numericRow1661 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 1, -50), (Sum.inr 1074, -2160), (Sum.inr 1650, -2160), (Sum.inr 2025, -4320), (Sum.inr 2047, -4320), (Sum.inr 2062, -4320), (Sum.inr 2079, -4320), (Sum.inr 2109, -2160), (Sum.inr 2224, -4320), (Sum.inr 2230, -4320), (Sum.inr 2261, -2160), (Sum.inr 2519, -2160), (Sum.inr 3486, -2160), (Sum.inr 3615, -2160), (Sum.inr 4486, 17280), (Sum.inr 4492, 8640), (Sum.inr 4504, 8640), (Sum.inr 4808, 17280), (Sum.inr 4824, 17280), (Sum.inr 4829, 17280), (Sum.inr 4840, 17280), (Sum.inr 4844, 8640), (Sum.inr 4853, 17280), (Sum.inr 4872, 8640), (Sum.inr 4881, 8640), (Sum.inr 5139, 17280)]

def numericRow1662 : Integer.Sparse Master := [(Sum.inl 0, -96), (Sum.inl 5, -40), (Sum.inl 6, -30), (Sum.inl 2, 160), (Sum.inl 3, 160), (Sum.inl 13, 160), (Sum.inl 52, 320), (Sum.inl 1, 230), (Sum.inr 1639, 8640), (Sum.inr 1650, 4320), (Sum.inr 1651, 4320), (Sum.inr 1659, 4320), (Sum.inr 2025, 8640), (Sum.inr 2062, 4320), (Sum.inr 2071, 8640), (Sum.inr 2079, 8640), (Sum.inr 2080, 8640), (Sum.inr 2090, 8640), (Sum.inr 2092, 8640), (Sum.inr 2109, 4320), (Sum.inr 2113, 4320), (Sum.inr 2121, 8640), (Sum.inr 2134, 4320), (Sum.inr 2136, 4320), (Sum.inr 2618, 8640)]

def numericRow1663 : Integer.Sparse Master := [(Sum.inr 1159, 1), (Sum.inr 2355, 1), (Sum.inr 2436, 1), (Sum.inr 2482, 1), (Sum.inr 2569, 1), (Sum.inr 2590, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1664 : Integer.Sparse Master := [(Sum.inr 1320, 1), (Sum.inr 2815, 1), (Sum.inr 2847, 1), (Sum.inr 2865, 2), (Sum.inr 2884, 1), (Sum.inr 4091, -1)]

def numericRow1665 : Integer.Sparse Master := [(Sum.inr 1334, 1), (Sum.inr 2797, 1), (Sum.inr 2802, 1), (Sum.inr 2815, 1), (Sum.inr 2865, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

def numericRow1666 : Integer.Sparse Master := [(Sum.inr 2018, 1), (Sum.inr 2074, 1), (Sum.inr 2081, 1), (Sum.inr 2099, 1), (Sum.inr 2203, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

def numericRow1667 : Integer.Sparse Master := [(Sum.inr 2015, 1), (Sum.inr 2018, 1), (Sum.inr 2027, 1), (Sum.inr 2047, 1), (Sum.inr 2261, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

def numericRow1668 : Integer.Sparse Master := [(Sum.inr 1136, -1), (Sum.inr 2339, -1), (Sum.inr 2429, -1), (Sum.inr 2480, -1), (Sum.inr 2485, -1), (Sum.inr 2489, -1), (Sum.inr 2723, -1), (Sum.inr 2924, -1), (Sum.inr 2931, -1), (Sum.inr 2954, -1), (Sum.inr 3077, -1), (Sum.inr 3273, -1), (Sum.inr 3420, -1), (Sum.inr 3455, -1), (Sum.inr 3467, -1), (Sum.inr 3481, -1), (Sum.inr 3482, -1), (Sum.inr 3544, -1), (Sum.inr 3605, -1), (Sum.inr 3606, -1), (Sum.inr 3612, -1), (Sum.inr 3625, -1), (Sum.inr 4327, 4), (Sum.inr 4330, 4), (Sum.inr 4335, 4), (Sum.inr 4347, 4), (Sum.inr 4440, 4), (Sum.inr 4528, 4), (Sum.inr 4535, 4), (Sum.inr 4591, 4), (Sum.inr 4930, 8), (Sum.inr 4935, 4), (Sum.inr 4944, 4), (Sum.inr 5034, 4), (Sum.inr 5065, 4), (Sum.inr 5128, 4), (Sum.inr 5139, 4), (Sum.inr 5252, 4)]

def numericRow1669 : Integer.Sparse Master := [(Sum.inl 0, -304), (Sum.inl 5, -160), (Sum.inl 6, 60), (Sum.inl 2, 180), (Sum.inl 3, 320), (Sum.inl 52, 320), (Sum.inl 1, -680), (Sum.inr 905, 5760), (Sum.inr 908, 5760), (Sum.inr 913, 5760), (Sum.inr 925, 5760), (Sum.inr 1022, 5760), (Sum.inr 1148, 5760), (Sum.inr 1154, 5760), (Sum.inr 1215, 5760), (Sum.inr 2320, 5760), (Sum.inr 2326, 5760), (Sum.inr 2335, 5760), (Sum.inr 2422, 5760), (Sum.inr 2426, 5760), (Sum.inr 2470, 5760), (Sum.inr 2543, 5760), (Sum.inr 2558, 5760), (Sum.inr 2712, 5760)]

def numericRow1670 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1672, 1), (Sum.inr 1676, 1), (Sum.inr 1689, 1), (Sum.inr 1723, 1), (Sum.inr 3260, 1), (Sum.inr 3272, 1), (Sum.inr 3273, 1), (Sum.inr 3291, 1), (Sum.inr 3408, 2), (Sum.inr 3413, 1), (Sum.inr 3419, 1), (Sum.inr 3420, 1), (Sum.inr 3451, 1), (Sum.inr 3455, 1), (Sum.inr 3466, 1), (Sum.inr 3467, 1), (Sum.inr 3481, 1), (Sum.inr 3482, 1), (Sum.inr 3519, 1), (Sum.inr 3523, 1), (Sum.inr 3543, 1), (Sum.inr 3544, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1)]

def numericRow1671 : Integer.Sparse Master := [(Sum.inr 1136, 1), (Sum.inr 2339, 1), (Sum.inr 2429, 1), (Sum.inr 2485, 2), (Sum.inr 4091, -1)]

def numericRow1672 : Integer.Sparse Master := [(Sum.inl 0, 111), (Sum.inl 6, -5), (Sum.inl 2, 20), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 12, 160), (Sum.inl 1, -310), (Sum.inr 702, -4320), (Sum.inr 705, -4320), (Sum.inr 708, -4320), (Sum.inr 720, -4320), (Sum.inr 760, -4320), (Sum.inr 762, -4320), (Sum.inr 764, -4320), (Sum.inr 769, -4320), (Sum.inr 787, -4320), (Sum.inr 847, -4320), (Sum.inr 1105, -4320), (Sum.inr 1109, -4320), (Sum.inr 1128, -4320), (Sum.inr 1239, -4320), (Sum.inr 1762, -4320), (Sum.inr 1767, -4320), (Sum.inr 1778, -4320), (Sum.inr 1847, -4320), (Sum.inr 1849, -4320), (Sum.inr 1851, -4320), (Sum.inr 1854, -4320), (Sum.inr 1861, -4320), (Sum.inr 1867, -4320), (Sum.inr 1887, -4320), (Sum.inr 1889, -4320), (Sum.inr 1891, -4320), (Sum.inr 1898, -4320), (Sum.inr 1940, -4320), (Sum.inr 1964, -4320), (Sum.inr 1970, -4320), (Sum.inr 2023, -4320), (Sum.inr 2025, -8640), (Sum.inr 2028, -4320), (Sum.inr 2058, -4320), (Sum.inr 2062, -4320), (Sum.inr 2182, -4320), (Sum.inr 2184, -4320), (Sum.inr 2186, -4320), (Sum.inr 2214, -4320), (Sum.inr 2215, -4320), (Sum.inr 2216, -4320), (Sum.inr 2224, -8640), (Sum.inr 2226, -4320), (Sum.inr 2230, -4320), (Sum.inr 2245, -4320), (Sum.inr 2247, -4320), (Sum.inr 2277, -4320), (Sum.inr 2290, -4320), (Sum.inr 2924, -4320), (Sum.inr 2931, -4320), (Sum.inr 3605, -4320), (Sum.inr 3612, -4320), (Sum.inr 3613, -4320), (Sum.inr 3632, -4320), (Sum.inr 3906, -4320)]

def numericRow1673 : Integer.Sparse Master := [(Sum.inr 930, -1), (Sum.inr 1046, -1), (Sum.inr 1690, -1), (Sum.inr 1750, -1), (Sum.inr 1812, -1), (Sum.inr 1964, -1), (Sum.inr 2020, -1), (Sum.inr 2025, -2), (Sum.inr 2029, -1), (Sum.inr 2112, -1), (Sum.inr 2165, -1), (Sum.inr 2182, -1), (Sum.inr 2202, -1), (Sum.inr 2224, -2), (Sum.inr 2225, -1), (Sum.inr 2247, -1), (Sum.inr 2287, -1), (Sum.inr 2290, -1), (Sum.inr 2739, -1), (Sum.inr 3534, -1), (Sum.inr 4327, 4), (Sum.inr 4331, 4), (Sum.inr 4333, 4), (Sum.inr 4335, 4), (Sum.inr 4336, 4), (Sum.inr 4353, 4), (Sum.inr 4442, 4), (Sum.inr 4664, 4), (Sum.inr 4670, 4), (Sum.inr 4757, 4), (Sum.inr 4772, 4), (Sum.inr 4777, 4), (Sum.inr 4792, 4), (Sum.inr 5150, 4), (Sum.inr 5151, 4), (Sum.inr 5173, 4), (Sum.inr 5270, 4)]

def numericRow1674 : Integer.Sparse Master := [(Sum.inl 0, -420), (Sum.inl 5, -80), (Sum.inl 6, 60), (Sum.inl 2, -460), (Sum.inl 35, 320), (Sum.inl 3, 320), (Sum.inl 13, 640), (Sum.inl 52, 320), (Sum.inl 1, -580), (Sum.inr 909, 5760), (Sum.inr 911, 5760), (Sum.inr 914, 5760), (Sum.inr 931, 5760), (Sum.inr 1024, 5760), (Sum.inr 1327, 5760), (Sum.inr 1333, 5760), (Sum.inr 2323, 5760), (Sum.inr 2327, 5760), (Sum.inr 2340, 5760), (Sum.inr 2423, 5760), (Sum.inr 2430, 5760), (Sum.inr 2471, 5760), (Sum.inr 2573, 5760), (Sum.inr 2575, 5760), (Sum.inr 2600, 5760), (Sum.inr 2754, 5760)]

def numericRow1675 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1684, 1), (Sum.inr 1685, 1), (Sum.inr 1686, 1), (Sum.inr 1688, 1), (Sum.inr 1689, 1), (Sum.inr 1690, 1), (Sum.inr 1744, 1), (Sum.inr 1750, 1), (Sum.inr 2147, 1), (Sum.inr 2164, 1), (Sum.inr 2165, 1), (Sum.inr 2181, 1), (Sum.inr 2182, 1), (Sum.inr 2198, 1), (Sum.inr 2201, 1), (Sum.inr 2202, 1), (Sum.inr 2223, 1), (Sum.inr 2224, 2), (Sum.inr 2225, 1), (Sum.inr 2287, 1), (Sum.inr 2290, 1), (Sum.inr 2681, 1), (Sum.inr 2700, 1), (Sum.inr 2735, 1), (Sum.inr 2738, 1), (Sum.inr 2739, 1)]

def numericRow1676 : Integer.Sparse Master := [(Sum.inr 913, 1), (Sum.inr 1796, 1), (Sum.inr 1956, 1), (Sum.inr 1979, 1), (Sum.inr 2025, 1), (Sum.inr 2029, 1), (Sum.inr 4083, -1)]

def numericRow1677 : Integer.Sparse Master := [(Sum.inr 1326, 1), (Sum.inr 1956, 1), (Sum.inr 1964, 1), (Sum.inr 2025, 2), (Sum.inr 2923, 1), (Sum.inr 4083, -1)]

def numericRow1678 : Integer.Sparse Master := [(Sum.inr 930, 1), (Sum.inr 1812, 1), (Sum.inr 1964, 1), (Sum.inr 2025, 2), (Sum.inr 4083, -1)]

def numericRow1679 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 1, -50), (Sum.inr 999, -2160), (Sum.inr 1602, -2160), (Sum.inr 1898, -2160), (Sum.inr 1915, -2160), (Sum.inr 1926, -2160), (Sum.inr 1940, -2160), (Sum.inr 1946, -2160), (Sum.inr 1948, -2160), (Sum.inr 1987, -2160), (Sum.inr 1996, -2160), (Sum.inr 2022, -2160), (Sum.inr 2025, -4320), (Sum.inr 2062, -2160), (Sum.inr 2112, -2160), (Sum.inr 2203, -2160), (Sum.inr 2224, -4320), (Sum.inr 2230, -2160), (Sum.inr 2287, -2160), (Sum.inr 2485, -4320), (Sum.inr 3481, -4320), (Sum.inr 3615, -2160), (Sum.inr 4414, 8640), (Sum.inr 4420, 8640), (Sum.inr 4425, 8640), (Sum.inr 4486, 8640), (Sum.inr 4780, 8640), (Sum.inr 4783, 8640), (Sum.inr 4792, 8640), (Sum.inr 4793, 8640), (Sum.inr 4808, 17280), (Sum.inr 4817, 8640), (Sum.inr 4819, 8640), (Sum.inr 4824, 8640), (Sum.inr 4853, 8640), (Sum.inr 5128, 8640)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1680 : Integer.Sparse Master := [(Sum.inr 2390, 1), (Sum.inr 2393, 1), (Sum.inr 2395, 1), (Sum.inr 2404, 1), (Sum.inr 2678, 1), (Sum.inr 3771, 1), (Sum.inr 4088, -1)]

def numericRow1681 : Integer.Sparse Master := [(Sum.inr 1898, 1), (Sum.inr 1901, 1), (Sum.inr 2191, 1), (Sum.inr 3460, 1), (Sum.inr 4079, -1)]

def numericRow1682 : Integer.Sparse Master := [(Sum.inr 2076, 1), (Sum.inr 2080, 1), (Sum.inr 2082, 1), (Sum.inr 2102, 1), (Sum.inr 2206, 1), (Sum.inr 3565, 1), (Sum.inr 4080, -1)]

def numericRow1683 : Integer.Sparse Master := [(Sum.inr 1325, 1), (Sum.inr 2811, 2), (Sum.inr 2820, 1), (Sum.inr 2886, 1), (Sum.inr 2889, 1), (Sum.inr 4092, -1)]

def numericRow1684 : Integer.Sparse Master := [(Sum.inr 1145, -1), (Sum.inr 2345, -1), (Sum.inr 2434, -2), (Sum.inr 2512, -2), (Sum.inr 2743, -1), (Sum.inr 2881, -2), (Sum.inr 2889, -1), (Sum.inr 3054, -1), (Sum.inr 3277, -1), (Sum.inr 3423, -1), (Sum.inr 3457, -2), (Sum.inr 3471, -2), (Sum.inr 3548, -1), (Sum.inr 3624, -2), (Sum.inr 3626, -1), (Sum.inr 3631, -1), (Sum.inr 4367, 8), (Sum.inr 4370, 4), (Sum.inr 4374, 4), (Sum.inr 4476, 4), (Sum.inr 4547, 8), (Sum.inr 4609, 4), (Sum.inr 4944, 8), (Sum.inr 5034, 8), (Sum.inr 5087, 8), (Sum.inr 5139, 8), (Sum.inr 5268, 4)]

def numericRow1685 : Integer.Sparse Master := [(Sum.inr 1720, 2), (Sum.inr 1722, 1), (Sum.inr 1729, 1), (Sum.inr 1748, 1), (Sum.inr 3266, 2), (Sum.inr 3277, 1), (Sum.inr 3302, 1), (Sum.inr 3413, 2), (Sum.inr 3423, 1), (Sum.inr 3451, 2), (Sum.inr 3457, 2), (Sum.inr 3471, 2), (Sum.inr 3472, 2), (Sum.inr 3523, 2), (Sum.inr 3548, 1), (Sum.inr 3549, 1), (Sum.inr 3624, 2), (Sum.inr 3626, 1), (Sum.inr 3631, 1)]

def numericRow1686 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, -10), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 1, 5), (Sum.inr 720, -2160), (Sum.inr 726, -1080), (Sum.inr 729, -1080), (Sum.inr 769, -2160), (Sum.inr 773, -1080), (Sum.inr 774, -1080), (Sum.inr 813, -1080), (Sum.inr 853, -1080), (Sum.inr 1098, -2160), (Sum.inr 1103, -1080), (Sum.inr 1239, -1080), (Sum.inr 1778, -2160), (Sum.inr 1783, -1080), (Sum.inr 1854, -2160), (Sum.inr 1857, -1080), (Sum.inr 1858, -1080), (Sum.inr 1867, -2160), (Sum.inr 1873, -2160), (Sum.inr 1891, -2160), (Sum.inr 1893, -2160), (Sum.inr 1894, -2160), (Sum.inr 1915, -2160), (Sum.inr 1946, -2160), (Sum.inr 2025, -2160), (Sum.inr 2058, -2160), (Sum.inr 2065, -1080), (Sum.inr 2216, -2160), (Sum.inr 2218, -1080), (Sum.inr 2224, -2160), (Sum.inr 2226, -1080), (Sum.inr 2247, -1080), (Sum.inr 2266, -1080), (Sum.inr 2278, -1080), (Sum.inr 2290, -1080), (Sum.inr 2881, -2160), (Sum.inr 2889, -1080), (Sum.inr 3624, -2160), (Sum.inr 3631, -1080), (Sum.inr 3632, -1080), (Sum.inr 3907, -1080)]

def numericRow1687 : Integer.Sparse Master := [(Sum.inr 939, -1), (Sum.inr 1091, -1), (Sum.inr 1694, -1), (Sum.inr 1756, -1), (Sum.inr 1819, -1), (Sum.inr 1970, -2), (Sum.inr 2054, -2), (Sum.inr 2062, -2), (Sum.inr 2169, -1), (Sum.inr 2186, -2), (Sum.inr 2206, -2), (Sum.inr 2230, -2), (Sum.inr 2281, -1), (Sum.inr 2294, -1), (Sum.inr 2743, -1), (Sum.inr 3548, -1), (Sum.inr 4347, 8), (Sum.inr 4358, 4), (Sum.inr 4371, 8), (Sum.inr 4375, 4), (Sum.inr 4478, 4), (Sum.inr 4682, 8), (Sum.inr 4761, 8), (Sum.inr 4817, 8), (Sum.inr 5205, 8), (Sum.inr 5206, 4), (Sum.inr 5276, 4)]

def numericRow1688 : Integer.Sparse Master := [(Sum.inr 1676, 2), (Sum.inr 1694, 1), (Sum.inr 1695, 1), (Sum.inr 1742, 2), (Sum.inr 1743, 1), (Sum.inr 1746, 1), (Sum.inr 1756, 1), (Sum.inr 2153, 2), (Sum.inr 2169, 1), (Sum.inr 2175, 2), (Sum.inr 2186, 2), (Sum.inr 2206, 2), (Sum.inr 2207, 2), (Sum.inr 2230, 2), (Sum.inr 2294, 1), (Sum.inr 2687, 1), (Sum.inr 2706, 2), (Sum.inr 2743, 1), (Sum.inr 2744, 1)]

def numericRow1689 : Integer.Sparse Master := [(Sum.inr 939, 1), (Sum.inr 1819, 1), (Sum.inr 1970, 2), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

def numericRow1690 : Integer.Sparse Master := [(Sum.inr 1315, 1), (Sum.inr 1961, 1), (Sum.inr 1970, 1), (Sum.inr 2062, 2), (Sum.inr 2879, 1), (Sum.inr 4084, -1)]

def numericRow1691 : Integer.Sparse Master := [(Sum.inr 2128, 2), (Sum.inr 2130, 1), (Sum.inr 2137, 1), (Sum.inr 2276, 1), (Sum.inr 2687, 1), (Sum.inr 4082, -1)]

def numericRow1692 : Integer.Sparse Master := [(Sum.inr 2085, 1), (Sum.inr 2087, 1), (Sum.inr 2093, 1), (Sum.inr 2101, 1), (Sum.inr 2242, 1), (Sum.inr 3570, 1), (Sum.inr 4080, -1)]

def numericRow1693 : Integer.Sparse Master := [(Sum.inr 2492, 1), (Sum.inr 2606, 1), (Sum.inr 2608, 1), (Sum.inr 2629, 1), (Sum.inr 2672, 1), (Sum.inr 3811, 1), (Sum.inr 4088, -1)]

def numericRow1694 : Integer.Sparse Master := [(Sum.inr 2030, 1), (Sum.inr 2032, 1), (Sum.inr 2038, 1), (Sum.inr 2048, 1), (Sum.inr 2276, 1), (Sum.inr 3538, 1), (Sum.inr 4082, -1)]

def numericRow1695 : Integer.Sparse Master := [(Sum.inr 2469, 1), (Sum.inr 2609, 1), (Sum.inr 2613, 2), (Sum.inr 2694, 1), (Sum.inr 3799, 1), (Sum.inr 4090, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1696 : Integer.Sparse Master := [(Sum.inr 2008, 1), (Sum.inr 2011, 1), (Sum.inr 2016, 2), (Sum.inr 2242, 1), (Sum.inr 3524, 1), (Sum.inr 4080, -1)]

def numericRow1697 : Integer.Sparse Master := [(Sum.inr 2117, 1), (Sum.inr 2119, 1), (Sum.inr 2122, 1), (Sum.inr 2128, 1), (Sum.inr 2215, 1), (Sum.inr 2681, 1), (Sum.inr 4082, -1)]

def numericRow1698 : Integer.Sparse Master := [(Sum.inr 2070, 1), (Sum.inr 2072, 1), (Sum.inr 2075, 1), (Sum.inr 2085, 1), (Sum.inr 2190, 1), (Sum.inr 3557, 1), (Sum.inr 4080, -1)]

def numericRow1699 : Integer.Sparse Master := [(Sum.inr 2453, 1), (Sum.inr 2455, 1), (Sum.inr 2459, 1), (Sum.inr 2490, 1), (Sum.inr 2697, 1), (Sum.inr 3795, 1), (Sum.inr 4088, -1)]

def numericRow1700 : Integer.Sparse Master := [(Sum.inr 2453, 1), (Sum.inr 2533, 1), (Sum.inr 2536, 1), (Sum.inr 2565, 1), (Sum.inr 2672, 1), (Sum.inr 3795, 1), (Sum.inr 4088, -1)]

def numericRow1701 : Integer.Sparse Master := [(Sum.inr 1991, 1), (Sum.inr 1993, 1), (Sum.inr 1997, 1), (Sum.inr 2030, 1), (Sum.inr 2215, 1), (Sum.inr 3516, 1), (Sum.inr 4082, -1)]

def numericRow1702 : Integer.Sparse Master := [(Sum.inr 1043, -1), (Sum.inr 1297, -1), (Sum.inr 1725, -1), (Sum.inr 2022, -2), (Sum.inr 2106, -2), (Sum.inr 2109, -2), (Sum.inr 2115, -1), (Sum.inr 2203, -2), (Sum.inr 2242, -2), (Sum.inr 2261, -2), (Sum.inr 2276, -1), (Sum.inr 2289, -1), (Sum.inr 2765, -1), (Sum.inr 2783, -2), (Sum.inr 3582, -1), (Sum.inr 4365, 8), (Sum.inr 4370, 4), (Sum.inr 4373, 4), (Sum.inr 4552, 8), (Sum.inr 4560, 4), (Sum.inr 4697, 8), (Sum.inr 4704, 4), (Sum.inr 4771, 8), (Sum.inr 4776, 8), (Sum.inr 5161, 8), (Sum.inr 5175, 4)]

def numericRow1703 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 6, 5), (Sum.inl 2, 80), (Sum.inl 35, -80), (Sum.inl 26, -80), (Sum.inl 1, 60), (Sum.inr 1137, 1440), (Sum.inr 1142, 720), (Sum.inr 1146, 720), (Sum.inr 1320, 1440), (Sum.inr 1325, 720), (Sum.inr 2816, 1440), (Sum.inr 2821, 720), (Sum.inr 2895, 1440), (Sum.inr 2899, 1440), (Sum.inr 2964, 1440), (Sum.inr 2967, 720)]

def numericRow1704 : Integer.Sparse Master := [(Sum.inr 1704, 2), (Sum.inr 1722, 1), (Sum.inr 1725, 1), (Sum.inr 1735, 1), (Sum.inr 2189, 2), (Sum.inr 2200, 2), (Sum.inr 2203, 2), (Sum.inr 2212, 2), (Sum.inr 2239, 2), (Sum.inr 2242, 2), (Sum.inr 2258, 1), (Sum.inr 2261, 2), (Sum.inr 2273, 1), (Sum.inr 2276, 1), (Sum.inr 2289, 1), (Sum.inr 2719, 2), (Sum.inr 2761, 1), (Sum.inr 2765, 1), (Sum.inr 2783, 1)]

def numericRow1705 : Integer.Sparse Master := [(Sum.inr 952, 1), (Sum.inr 1830, 1), (Sum.inr 1978, 2), (Sum.inr 2109, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

def numericRow1706 : Integer.Sparse Master := [(Sum.inr 1157, 1), (Sum.inr 1972, 1), (Sum.inr 1978, 1), (Sum.inr 2022, 1), (Sum.inr 2109, 1), (Sum.inr 2588, 1), (Sum.inr 4084, -1)]

def numericRow1707 : Integer.Sparse Master := [(Sum.inr 943, 1), (Sum.inr 1823, 1), (Sum.inr 1972, 1), (Sum.inr 2106, 1), (Sum.inr 2109, 2), (Sum.inr 4084, -1)]

def numericRow1708 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 5, -20), (Sum.inl 2, 10), (Sum.inl 7, -80), (Sum.inl 3, -160), (Sum.inl 4, -80), (Sum.inl 1, 45), (Sum.inr 733, -4320), (Sum.inr 735, -2160), (Sum.inr 742, -2160), (Sum.inr 799, -4320), (Sum.inr 801, -2160), (Sum.inr 815, -2160), (Sum.inr 826, -2160), (Sum.inr 843, -2160), (Sum.inr 916, -4320), (Sum.inr 937, -2160), (Sum.inr 1037, -2160), (Sum.inr 1633, -4320), (Sum.inr 1647, -2160), (Sum.inr 1683, -2160), (Sum.inr 1807, -4320), (Sum.inr 1818, -2160), (Sum.inr 1875, -4320), (Sum.inr 1880, -4320), (Sum.inr 1905, -4320), (Sum.inr 1917, -4320), (Sum.inr 1924, -4320), (Sum.inr 1938, -4320), (Sum.inr 2047, -4320), (Sum.inr 2065, -2160), (Sum.inr 2079, -4320), (Sum.inr 2107, -4320), (Sum.inr 2116, -2160), (Sum.inr 2151, -4320), (Sum.inr 2168, -2160), (Sum.inr 2218, -2160), (Sum.inr 2260, -4320), (Sum.inr 2266, -2160), (Sum.inr 2278, -2160), (Sum.inr 2288, -2160), (Sum.inr 2590, -4320), (Sum.inr 2765, -2160), (Sum.inr 3564, -4320), (Sum.inr 3582, -2160), (Sum.inr 3614, -2160), (Sum.inr 3913, -2160)]

def numericRow1709 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 5, 20), (Sum.inl 2, -10), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 4, 80), (Sum.inl 1, -45), (Sum.inr 733, 4320), (Sum.inr 735, 2160), (Sum.inr 742, 2160), (Sum.inr 826, 2160), (Sum.inr 916, 4320), (Sum.inr 937, 2160), (Sum.inr 1037, 2160), (Sum.inr 1807, 4320), (Sum.inr 1818, 2160), (Sum.inr 1875, 4320), (Sum.inr 1880, 4320), (Sum.inr 1924, 4320), (Sum.inr 2079, 4320), (Sum.inr 2107, 4320), (Sum.inr 2116, 2160), (Sum.inr 2218, 2160), (Sum.inr 2278, 2160), (Sum.inr 2590, 4320), (Sum.inr 2765, 2160)]

def numericRow1710 : Integer.Sparse Master := [(Sum.inr 1131, -1), (Sum.inr 1242, -1), (Sum.inr 2334, -1), (Sum.inr 2425, -1), (Sum.inr 2479, -1), (Sum.inr 2482, -1), (Sum.inr 2488, -1), (Sum.inr 2553, -1), (Sum.inr 2561, -1), (Sum.inr 2590, -1), (Sum.inr 2722, -1), (Sum.inr 2726, -1), (Sum.inr 3264, -1), (Sum.inr 3300, -1), (Sum.inr 3411, -1), (Sum.inr 3449, -1), (Sum.inr 3459, -1), (Sum.inr 3468, -1), (Sum.inr 3478, -1), (Sum.inr 3514, -1), (Sum.inr 3522, -1), (Sum.inr 3533, -1), (Sum.inr 3545, -1), (Sum.inr 3564, -1), (Sum.inr 4527, 4), (Sum.inr 4528, 4), (Sum.inr 4531, 4), (Sum.inr 4534, 4), (Sum.inr 4535, 4), (Sum.inr 4547, 4), (Sum.inr 4591, 4), (Sum.inr 4934, 4), (Sum.inr 4954, 4), (Sum.inr 4965, 4), (Sum.inr 5041, 4), (Sum.inr 5147, 4)]

def numericRow1711 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3260, 1), (Sum.inr 3262, 1), (Sum.inr 3264, 1), (Sum.inr 3266, 1), (Sum.inr 3268, 1), (Sum.inr 3272, 1), (Sum.inr 3291, 1), (Sum.inr 3300, 1), (Sum.inr 3411, 1), (Sum.inr 3415, 1), (Sum.inr 3449, 1), (Sum.inr 3452, 1), (Sum.inr 3458, 1), (Sum.inr 3459, 1), (Sum.inr 3468, 1), (Sum.inr 3475, 1), (Sum.inr 3478, 1), (Sum.inr 3514, 1), (Sum.inr 3522, 1), (Sum.inr 3530, 1), (Sum.inr 3533, 1), (Sum.inr 3545, 1), (Sum.inr 3564, 1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1712 : Integer.Sparse Master := [(Sum.inr 1119, 1), (Sum.inr 2325, 1), (Sum.inr 2347, 1), (Sum.inr 2355, 1), (Sum.inr 2482, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

def numericRow1713 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 2436, 1), (Sum.inr 2479, 1), (Sum.inr 2482, 2), (Sum.inr 4092, -1)]

def numericRow1714 : Integer.Sparse Master := [(Sum.inr 1131, 1), (Sum.inr 2334, 1), (Sum.inr 2425, 1), (Sum.inr 2482, 1), (Sum.inr 4092, -1)]

def numericRow1715 : Integer.Sparse Master := [(Sum.inl 0, 199), (Sum.inl 5, 40), (Sum.inl 6, 5), (Sum.inl 8, 80), (Sum.inl 1, 60), (Sum.inr 865, -4320), (Sum.inr 867, -4320), (Sum.inr 873, -4320), (Sum.inr 881, -4320), (Sum.inr 900, -4320), (Sum.inr 903, -4320), (Sum.inr 924, -4320), (Sum.inr 982, -4320), (Sum.inr 1043, -4320), (Sum.inr 1553, -4320), (Sum.inr 1555, -4320), (Sum.inr 1559, -4320), (Sum.inr 1569, -4320), (Sum.inr 1588, -4320), (Sum.inr 1591, -4320), (Sum.inr 1617, -4320), (Sum.inr 1674, -4320), (Sum.inr 1725, -4320), (Sum.inr 2295, -4320), (Sum.inr 2300, -4320), (Sum.inr 2306, -4320), (Sum.inr 2317, -4320), (Sum.inr 2334, -4320), (Sum.inr 2371, -4320), (Sum.inr 2385, -4320), (Sum.inr 2425, -4320), (Sum.inr 2449, -4320), (Sum.inr 2480, -4320), (Sum.inr 2482, -4320), (Sum.inr 2489, -4320), (Sum.inr 2512, -4320), (Sum.inr 2556, -4320), (Sum.inr 2561, -4320), (Sum.inr 2723, -4320), (Sum.inr 2726, -4320), (Sum.inr 3315, -4320), (Sum.inr 3318, -4320), (Sum.inr 3325, -4320), (Sum.inr 3335, -4320), (Sum.inr 3353, -4320), (Sum.inr 3399, -4320), (Sum.inr 3411, -4320), (Sum.inr 3432, -4320), (Sum.inr 3449, -4320), (Sum.inr 3467, -4320), (Sum.inr 3468, -4320), (Sum.inr 3471, -4320), (Sum.inr 3482, -4320), (Sum.inr 3521, -4320), (Sum.inr 3522, -4320), (Sum.inr 3544, -4320), (Sum.inr 3545, -4320), (Sum.inr 3607, -4320), (Sum.inr 3608, -4320), (Sum.inr 3627, -4320), (Sum.inr 4047, -4320)]

def numericRow1716 : Integer.Sparse Master := [(Sum.inr 924, -1), (Sum.inr 1043, -1), (Sum.inr 1239, -1), (Sum.inr 1674, -1), (Sum.inr 1725, -1), (Sum.inr 1807, -1), (Sum.inr 1960, -1), (Sum.inr 2019, -1), (Sum.inr 2022, -2), (Sum.inr 2028, -1), (Sum.inr 2109, -1), (Sum.inr 2151, -1), (Sum.inr 2173, -1), (Sum.inr 2190, -1), (Sum.inr 2203, -2), (Sum.inr 2215, -1), (Sum.inr 2226, -1), (Sum.inr 2261, -1), (Sum.inr 2722, -1), (Sum.inr 2740, -2), (Sum.inr 3533, -1), (Sum.inr 4330, 4), (Sum.inr 4334, 4), (Sum.inr 4532, 4), (Sum.inr 4536, 4), (Sum.inr 4552, 4), (Sum.inr 4663, 4), (Sum.inr 4669, 4), (Sum.inr 4756, 4), (Sum.inr 4771, 4), (Sum.inr 4776, 4), (Sum.inr 5140, 4), (Sum.inr 5161, 4)]

def numericRow1717 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 5, -20), (Sum.inl 6, 20), (Sum.inl 2, 130), (Sum.inl 35, 80), (Sum.inl 26, 80), (Sum.inl 1, 140), (Sum.inr 1116, 1080), (Sum.inr 1118, 1080), (Sum.inr 1121, 1080), (Sum.inr 1137, 1080), (Sum.inr 1334, 1080), (Sum.inr 2800, 1080), (Sum.inr 2803, 1080), (Sum.inr 2816, 1080), (Sum.inr 2890, 1080), (Sum.inr 2895, 1080), (Sum.inr 2942, 1080), (Sum.inr 2964, 1080)]

def numericRow1718 : Integer.Sparse Master := [(Sum.inr 1672, 1), (Sum.inr 1674, 1), (Sum.inr 1679, 1), (Sum.inr 1725, 1), (Sum.inr 2140, 1), (Sum.inr 2149, 1), (Sum.inr 2151, 1), (Sum.inr 2155, 1), (Sum.inr 2172, 1), (Sum.inr 2173, 1), (Sum.inr 2176, 1), (Sum.inr 2189, 1), (Sum.inr 2190, 1), (Sum.inr 2200, 1), (Sum.inr 2203, 2), (Sum.inr 2212, 1), (Sum.inr 2215, 1), (Sum.inr 2226, 1), (Sum.inr 2261, 1), (Sum.inr 2670, 1), (Sum.inr 2719, 1), (Sum.inr 2722, 1), (Sum.inr 2740, 1)]

def numericRow1719 : Integer.Sparse Master := [(Sum.inr 912, 1), (Sum.inr 1795, 1), (Sum.inr 1955, 1), (Sum.inr 1978, 1), (Sum.inr 2022, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

def numericRow1720 : Integer.Sparse Master := [(Sum.inr 1147, 1), (Sum.inr 1955, 1), (Sum.inr 1960, 1), (Sum.inr 2022, 2), (Sum.inr 4084, -1)]

def numericRow1721 : Integer.Sparse Master := [(Sum.inr 1789, 1), (Sum.inr 1972, 1), (Sum.inr 2019, 1), (Sum.inr 2022, 2), (Sum.inr 4084, -1)]

def numericRow1722 : Integer.Sparse Master := [(Sum.inr 924, 1), (Sum.inr 1807, 1), (Sum.inr 1960, 1), (Sum.inr 2022, 1), (Sum.inr 4084, -1)]

def numericRow1723 : Integer.Sparse Master := [(Sum.inl 0, 86), (Sum.inl 6, -5), (Sum.inl 2, 20), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 4, 80), (Sum.inl 1, 155), (Sum.inr 699, -4320), (Sum.inr 701, -4320), (Sum.inr 707, -4320), (Sum.inr 715, -4320), (Sum.inr 748, -4320), (Sum.inr 750, -4320), (Sum.inr 753, -4320), (Sum.inr 763, -4320), (Sum.inr 785, -4320), (Sum.inr 804, -4320), (Sum.inr 898, -4320), (Sum.inr 902, -4320), (Sum.inr 921, -4320), (Sum.inr 979, -4320), (Sum.inr 1586, -4320), (Sum.inr 1590, -4320), (Sum.inr 1599, -4320), (Sum.inr 1666, -4320), (Sum.inr 1760, -4320), (Sum.inr 1766, -4320), (Sum.inr 1773, -4320), (Sum.inr 1836, -4320), (Sum.inr 1841, -4320), (Sum.inr 1850, -4320), (Sum.inr 1860, -4320), (Sum.inr 1863, -4320), (Sum.inr 1883, -4320), (Sum.inr 1888, -4320), (Sum.inr 1897, -4320), (Sum.inr 1907, -4320), (Sum.inr 1960, -4320), (Sum.inr 1969, -4320), (Sum.inr 1987, -4320), (Sum.inr 1996, -4320), (Sum.inr 2003, -4320), (Sum.inr 2006, -4320), (Sum.inr 2020, -4320), (Sum.inr 2022, -4320), (Sum.inr 2029, -4320), (Sum.inr 2052, -4320), (Sum.inr 2054, -4320), (Sum.inr 2173, -4320), (Sum.inr 2185, -4320), (Sum.inr 2193, -4320), (Sum.inr 2202, -4320), (Sum.inr 2203, -4320), (Sum.inr 2206, -4320), (Sum.inr 2225, -4320), (Sum.inr 2244, -4320), (Sum.inr 2262, -4320), (Sum.inr 2553, -4320), (Sum.inr 2561, -4320), (Sum.inr 2722, -4320), (Sum.inr 3514, -4320), (Sum.inr 3522, -4320), (Sum.inr 3533, -4320), (Sum.inr 3603, -4320), (Sum.inr 3903, -4320)]

def numericRow1724 : Integer.Sparse Master := [(Sum.inr 2391, 1), (Sum.inr 2535, 1), (Sum.inr 2539, 1), (Sum.inr 2585, 1), (Sum.inr 2686, 1), (Sum.inr 3770, 1), (Sum.inr 4089, -1)]

def numericRow1725 : Integer.Sparse Master := [(Sum.inr 1921, 1), (Sum.inr 1924, 1), (Sum.inr 1928, 1), (Sum.inr 2215, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

def numericRow1726 : Integer.Sparse Master := [(Sum.inr 1924, 1), (Sum.inr 2534, 1), (Sum.inr 2538, 1), (Sum.inr 2584, 1), (Sum.inr 2685, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

def numericRow1727 : Integer.Sparse Master := [(Sum.inr 2379, 1), (Sum.inr 2382, 2), (Sum.inr 2661, 1), (Sum.inr 3757, 1), (Sum.inr 4088, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1728 : Integer.Sparse Master := [(Sum.inr 2541, 1), (Sum.inr 2551, 2), (Sum.inr 2705, 1), (Sum.inr 3757, 1), (Sum.inr 4088, -1)]

def numericRow1729 : Integer.Sparse Master := [(Sum.inr 1897, 1), (Sum.inr 2550, 2), (Sum.inr 2704, 1), (Sum.inr 3459, 1), (Sum.inr 4080, -1)]

def numericRow1730 : Integer.Sparse Master := [(Sum.inr 2075, 1), (Sum.inr 2079, 1), (Sum.inr 2082, 1), (Sum.inr 2101, 1), (Sum.inr 3564, 1), (Sum.inr 4080, -1)]

def numericRow1731 : Integer.Sparse Master := [(Sum.inr 1123, 1), (Sum.inr 1875, 1), (Sum.inr 1880, 1), (Sum.inr 2079, 1), (Sum.inr 2504, 1), (Sum.inr 4080, -1)]

def numericRow1732 : Integer.Sparse Master := [(Sum.inr 916, 1), (Sum.inr 1799, 1), (Sum.inr 1874, 1), (Sum.inr 2018, 1), (Sum.inr 2047, 1), (Sum.inr 4081, -1)]

def numericRow1733 : Integer.Sparse Master := [(Sum.inr 2449, 1), (Sum.inr 2452, 1), (Sum.inr 2477, 1), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

def numericRow1734 : Integer.Sparse Master := [(Sum.inr 924, -2), (Sum.inr 934, -1), (Sum.inr 938, -1), (Sum.inr 1128, -2), (Sum.inr 1143, -1), (Sum.inr 1239, -1), (Sum.inr 1674, -2), (Sum.inr 1692, -1), (Sum.inr 1693, -1), (Sum.inr 1807, -2), (Sum.inr 1818, -1), (Sum.inr 1960, -2), (Sum.inr 1969, -2), (Sum.inr 2022, -2), (Sum.inr 2151, -2), (Sum.inr 2167, -1), (Sum.inr 2168, -1), (Sum.inr 2173, -2), (Sum.inr 2184, -2), (Sum.inr 2185, -2), (Sum.inr 2203, -2), (Sum.inr 2226, -1), (Sum.inr 2509, -2), (Sum.inr 2522, -1), (Sum.inr 2685, -1), (Sum.inr 2704, -2), (Sum.inr 2740, -2), (Sum.inr 4084, 4)]

def numericRow1735 : Integer.Sparse Master := [(Sum.inr 1674, 2), (Sum.inr 1692, 1), (Sum.inr 1693, 1), (Sum.inr 2151, 2), (Sum.inr 2167, 1), (Sum.inr 2168, 1), (Sum.inr 2173, 2), (Sum.inr 2184, 2), (Sum.inr 2185, 2), (Sum.inr 2203, 2), (Sum.inr 2226, 1), (Sum.inr 2685, 1), (Sum.inr 2704, 2), (Sum.inr 2740, 1), (Sum.inr 4084, 1)]

def numericRow1736 : Integer.Sparse Master := [(Sum.inr 2382, 1), (Sum.inr 2385, 1), (Sum.inr 2388, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

def numericRow1737 : Integer.Sparse Master := [(Sum.inr 2385, 1), (Sum.inr 2459, 1), (Sum.inr 2505, 1), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

def numericRow1738 : Integer.Sparse Master := [(Sum.inr 865, -1), (Sum.inr 871, -1), (Sum.inr 873, -1), (Sum.inr 982, -1), (Sum.inr 1105, -1), (Sum.inr 1109, -1), (Sum.inr 1123, -1), (Sum.inr 1202, -1), (Sum.inr 1553, -1), (Sum.inr 1568, -1), (Sum.inr 1569, -1), (Sum.inr 1617, -1), (Sum.inr 1760, -1), (Sum.inr 1766, -1), (Sum.inr 1836, -1), (Sum.inr 1849, -1), (Sum.inr 1850, -1), (Sum.inr 1860, -1), (Sum.inr 1875, -1), (Sum.inr 1880, -1), (Sum.inr 1887, -1), (Sum.inr 1888, -1), (Sum.inr 1897, -1), (Sum.inr 1905, -1), (Sum.inr 1907, -1), (Sum.inr 1937, -1), (Sum.inr 1938, -1), (Sum.inr 1942, -1), (Sum.inr 1987, -1), (Sum.inr 1996, -1), (Sum.inr 2047, -1), (Sum.inr 2052, -1), (Sum.inr 2079, -1), (Sum.inr 2193, -1), (Sum.inr 2399, -1), (Sum.inr 2458, -2), (Sum.inr 2467, -1), (Sum.inr 2504, -2), (Sum.inr 2509, -1), (Sum.inr 2704, -1), (Sum.inr 4080, 4)]

def numericRow1739 : Integer.Sparse Master := [(Sum.inr 882, -2), (Sum.inr 897, -1), (Sum.inr 1012, -1), (Sum.inr 1558, -2), (Sum.inr 1577, -1), (Sum.inr 1627, -1), (Sum.inr 1774, -2), (Sum.inr 1783, -1), (Sum.inr 1840, -2), (Sum.inr 1857, -1), (Sum.inr 1864, -2), (Sum.inr 1873, -2), (Sum.inr 1882, -2), (Sum.inr 1893, -2), (Sum.inr 1915, -2), (Sum.inr 1946, -2), (Sum.inr 1951, -2), (Sum.inr 2003, -2), (Sum.inr 2006, -2), (Sum.inr 2062, -1), (Sum.inr 2230, -1), (Sum.inr 2385, -2), (Sum.inr 2407, -1), (Sum.inr 2519, -1), (Sum.inr 3353, -2), (Sum.inr 3360, -1), (Sum.inr 3486, -1), (Sum.inr 4081, 4)]

def numericRow1740 : Integer.Sparse Master := [(Sum.inr 921, -4), (Sum.inr 928, -1), (Sum.inr 937, -2), (Sum.inr 1666, -4), (Sum.inr 1677, -1), (Sum.inr 1683, -2), (Sum.inr 1804, -4), (Sum.inr 1817, -1), (Sum.inr 1959, -2), (Sum.inr 2052, -4), (Sum.inr 2065, -2), (Sum.inr 2143, -4), (Sum.inr 2159, -1), (Sum.inr 2170, -2), (Sum.inr 2193, -4), (Sum.inr 2218, -2), (Sum.inr 2726, -1), (Sum.inr 3545, -1), (Sum.inr 4085, 4)]

def numericRow1741 : Integer.Sparse Master := [(Sum.inr 1666, 4), (Sum.inr 1677, 1), (Sum.inr 1683, 2), (Sum.inr 2143, 4), (Sum.inr 2159, 1), (Sum.inr 2170, 2), (Sum.inr 2193, 4), (Sum.inr 2218, 2), (Sum.inr 2726, 1), (Sum.inr 4085, 1)]

def numericRow1742 : Integer.Sparse Master := [(Sum.inr 937, 1), (Sum.inr 1804, 2), (Sum.inr 1817, 1), (Sum.inr 2065, 1), (Sum.inr 4085, -1)]

def numericRow1743 : Integer.Sparse Master := [(Sum.inr 864, -1), (Sum.inr 867, -1), (Sum.inr 872, -1), (Sum.inr 898, -1), (Sum.inr 902, -1), (Sum.inr 916, -1), (Sum.inr 979, -1), (Sum.inr 1550, -1), (Sum.inr 1555, -1), (Sum.inr 1562, -1), (Sum.inr 1586, -1), (Sum.inr 1590, -1), (Sum.inr 1599, -1), (Sum.inr 1633, -1), (Sum.inr 1759, -1), (Sum.inr 1765, -1), (Sum.inr 1784, -1), (Sum.inr 1799, -1), (Sum.inr 1833, -1), (Sum.inr 1843, -1), (Sum.inr 1874, -1), (Sum.inr 1884, -1), (Sum.inr 1896, -1), (Sum.inr 1897, -1), (Sum.inr 1907, -1), (Sum.inr 1917, -1), (Sum.inr 1920, -1), (Sum.inr 1924, -1), (Sum.inr 1986, -2), (Sum.inr 1987, -1), (Sum.inr 1996, -1), (Sum.inr 2003, -1), (Sum.inr 2006, -1), (Sum.inr 2018, -2), (Sum.inr 2022, -1), (Sum.inr 2047, -1), (Sum.inr 2079, -1), (Sum.inr 2203, -1), (Sum.inr 2482, -1), (Sum.inr 3468, -1), (Sum.inr 4081, 4)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1744 : Integer.Sparse Master := [(Sum.inr 4064, 4), (Sum.inr 4066, 1), (Sum.inr 4067, 2), (Sum.inr 4070, 2), (Sum.inr 4074, 4), (Sum.inr 4076, 1), (Sum.inr 4077, 2), (Sum.inr 4080, 4), (Sum.inr 4081, 4), (Sum.inr 4082, 2), (Sum.inr 4084, 2), (Sum.inr 4085, 1), (Sum.inr 4092, 1)]

def numericRow1745 : Integer.Sparse Master := [(Sum.inr 2340, 1), (Sum.inr 2816, 1), (Sum.inr 3162, 1), (Sum.inr 3174, 1), (Sum.inr 3198, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

def numericRow1746 : Integer.Sparse Master := [(Sum.inr 2213, 1), (Sum.inr 2215, 1), (Sum.inr 2217, 1), (Sum.inr 2225, 1), (Sum.inr 2274, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

def numericRow1747 : Integer.Sparse Master := [(Sum.inr 910, 1), (Sum.inr 1794, 1), (Sum.inr 1977, 1), (Sum.inr 2012, 1), (Sum.inr 2020, 1), (Sum.inr 2023, 1), (Sum.inr 4083, -1)]

def numericRow1748 : Integer.Sparse Master := [(Sum.inr 2323, 1), (Sum.inr 2800, 1), (Sum.inr 3189, 1), (Sum.inr 3199, 2), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

def numericRow1749 : Integer.Sparse Master := [(Sum.inr 2213, 1), (Sum.inr 2396, 1), (Sum.inr 3476, 1), (Sum.inr 3610, 1), (Sum.inr 3612, 2), (Sum.inr 4082, -1)]

def numericRow1750 : Integer.Sparse Master := [(Sum.inr 3193, 1), (Sum.inr 3648, 1), (Sum.inr 3653, 1), (Sum.inr 3659, 1), (Sum.inr 3762, 2), (Sum.inr 4088, -1)]

def numericRow1751 : Integer.Sparse Master := [(Sum.inr 950, 1), (Sum.inr 1829, 1), (Sum.inr 1977, 1), (Sum.inr 2094, 1), (Sum.inr 2107, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

def numericRow1752 : Integer.Sparse Master := [(Sum.inr 2327, 1), (Sum.inr 2803, 1), (Sum.inr 3133, 1), (Sum.inr 3138, 1), (Sum.inr 3174, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

def numericRow1753 : Integer.Sparse Master := [(Sum.inr 2274, 1), (Sum.inr 2401, 1), (Sum.inr 3536, 1), (Sum.inr 3612, 1), (Sum.inr 3630, 1), (Sum.inr 3631, 1), (Sum.inr 4082, -1)]

def numericRow1754 : Integer.Sparse Master := [(Sum.inr 2274, 2), (Sum.inr 2276, 1), (Sum.inr 2280, 1), (Sum.inr 2288, 1), (Sum.inr 3631, 1), (Sum.inr 4082, -1)]

def numericRow1755 : Integer.Sparse Master := [(Sum.inr 3166, 1), (Sum.inr 3658, 1), (Sum.inr 3660, 1), (Sum.inr 3666, 1), (Sum.inr 3772, 2), (Sum.inr 4089, -1)]

def numericRow1756 : Integer.Sparse Master := [(Sum.inr 2346, 1), (Sum.inr 2821, 1), (Sum.inr 3129, 2), (Sum.inr 3161, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

def numericRow1757 : Integer.Sparse Master := [(Sum.inr 3147, 1), (Sum.inr 3372, 1), (Sum.inr 3473, 1), (Sum.inr 3480, 2), (Sum.inr 3611, 1), (Sum.inr 4082, -1)]

def numericRow1758 : Integer.Sparse Master := [(Sum.inr 1141, 1), (Sum.inr 2343, 1), (Sum.inr 2433, 1), (Sum.inr 2499, 1), (Sum.inr 2512, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

def numericRow1759 : Integer.Sparse Master := [(Sum.inr 2335, 1), (Sum.inr 2811, 1), (Sum.inr 2846, 1), (Sum.inr 2889, 1), (Sum.inr 2979, 1), (Sum.inr 3705, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow176 : Integer.Sparse Master := [(Sum.inl 0, -8), (Sum.inl 2, 35), (Sum.inl 3, 640), (Sum.inl 13, 240), (Sum.inl 12, 320), (Sum.inl 4, 160), (Sum.inl 1, -145), (Sum.inr 776, 1440), (Sum.inr 778, 1440), (Sum.inr 784, 4320), (Sum.inr 2009, 4320), (Sum.inr 2012, 4320), (Sum.inr 2021, 8640), (Sum.inr 2187, 1440), (Sum.inr 2192, 4320), (Sum.inr 2232, 1440), (Sum.inr 2240, 4320), (Sum.inr 3899, 1440), (Sum.inr 3909, 1440)]

def numericRow177 : Integer.Sparse Master := [(Sum.inr 3221, 1), (Sum.inr 3801, 3), (Sum.inr 3899, 1), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

def numericRow178 : Integer.Sparse Master := [(Sum.inr 1464, 3), (Sum.inr 1467, 1), (Sum.inr 1474, 1), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

def numericRow179 : Integer.Sparse Master := [(Sum.inr 1464, 1), (Sum.inr 3172, 1), (Sum.inr 3197, 1), (Sum.inr 3202, 2), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

def numericRow180 : Integer.Sparse Master := [(Sum.inr 2471, 1), (Sum.inr 3199, 1), (Sum.inr 3202, 2), (Sum.inr 3221, 1), (Sum.inr 3801, 1), (Sum.inr 4091, -1)]

def numericRow181 : Integer.Sparse Master := [(Sum.inr 1467, 1), (Sum.inr 3179, 1), (Sum.inr 3199, 3), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

def numericRow182 : Integer.Sparse Master := [(Sum.inr 2707, 1), (Sum.inr 3197, 3), (Sum.inr 3221, 1), (Sum.inr 3899, 1), (Sum.inr 4091, -1)]

def numericRow183 : Integer.Sparse Master := [(Sum.inr 1474, 1), (Sum.inr 2471, 3), (Sum.inr 2707, 1), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

def numericRow184 : Integer.Sparse Master := [(Sum.inl 0, -59), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 13, -320), (Sum.inl 12, -80), (Sum.inl 1, 30), (Sum.inr 1354, 4320), (Sum.inr 1366, 1440), (Sum.inr 3058, 1440), (Sum.inr 3059, 1440), (Sum.inr 3077, 4320), (Sum.inr 3146, 4320), (Sum.inr 3155, 1440), (Sum.inr 3165, 4320), (Sum.inr 3179, 1440), (Sum.inr 3222, 8640)]

def numericRow185 : Integer.Sparse Master := [(Sum.inr 2252, 1), (Sum.inr 2507, 1), (Sum.inr 3576, 1), (Sum.inr 3625, 3), (Sum.inr 4084, -1)]

def numericRow186 : Integer.Sparse Master := [(Sum.inr 1056, 1), (Sum.inr 2131, 1), (Sum.inr 2252, 1), (Sum.inr 2277, 3), (Sum.inr 4084, -1)]

def numericRow187 : Integer.Sparse Master := [(Sum.inr 2104, 1), (Sum.inr 2252, 1), (Sum.inr 2262, 3), (Sum.inr 4084, -1)]

def numericRow188 : Integer.Sparse Master := [(Sum.inl 0, -31), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 13, 160), (Sum.inl 12, 80), (Sum.inl 1, 10), (Sum.inr 2059, 4320), (Sum.inr 2063, 2160), (Sum.inr 2064, 2160), (Sum.inr 2267, 2160), (Sum.inr 2670, 4320), (Sum.inr 2683, 2160), (Sum.inr 2685, 2160), (Sum.inr 2740, 2160), (Sum.inr 3015, 4320), (Sum.inr 3022, 4320), (Sum.inr 3024, 4320), (Sum.inr 3035, 4320), (Sum.inr 3038, 4320), (Sum.inr 3049, 2160), (Sum.inr 3054, 2160), (Sum.inr 3075, 4320), (Sum.inr 3098, 2160), (Sum.inr 3156, 4320), (Sum.inr 3161, 2160)]

def numericRow189 : Integer.Sparse Master := [(Sum.inr 2279, 1), (Sum.inr 2744, 1), (Sum.inr 3541, 2), (Sum.inr 3626, 1), (Sum.inr 3632, 1), (Sum.inr 4084, -1)]

def numericRow190 : Integer.Sparse Master := [(Sum.inr 1238, 2), (Sum.inr 1244, 1), (Sum.inr 1245, 1), (Sum.inr 1296, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

def numericRow191 : Integer.Sparse Master := [(Sum.inr 1296, 1), (Sum.inr 2138, 1), (Sum.inr 2592, 2), (Sum.inr 2744, 1), (Sum.inr 2781, 1), (Sum.inr 4084, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1760 : Integer.Sparse Master := [(Sum.inr 3476, 1), (Sum.inr 3478, 1), (Sum.inr 3480, 1), (Sum.inr 3482, 1), (Sum.inr 3522, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

def numericRow1761 : Integer.Sparse Master := [(Sum.inr 1928, 1), (Sum.inr 2674, 1), (Sum.inr 3348, 1), (Sum.inr 3430, 1), (Sum.inr 3478, 1), (Sum.inr 3480, 1), (Sum.inr 4082, -1)]

def numericRow1762 : Integer.Sparse Master := [(Sum.inr 1117, 1), (Sum.inr 2324, 1), (Sum.inr 2441, 1), (Sum.inr 2473, 1), (Sum.inr 2480, 1), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

def numericRow1763 : Integer.Sparse Master := [(Sum.inr 2320, 1), (Sum.inr 2797, 1), (Sum.inr 2900, 1), (Sum.inr 2931, 1), (Sum.inr 2981, 1), (Sum.inr 3690, 1), (Sum.inr 4091, -1)]

def numericRow1764 : Integer.Sparse Master := [(Sum.inr 1941, 1), (Sum.inr 3476, 2), (Sum.inr 3482, 2), (Sum.inr 4082, -1)]

def numericRow1765 : Integer.Sparse Master := [(Sum.inr 1921, 1), (Sum.inr 2668, 1), (Sum.inr 3345, 1), (Sum.inr 3476, 1), (Sum.inr 3478, 2), (Sum.inr 4082, -1)]

def numericRow1766 : Integer.Sparse Master := [(Sum.inr 1807, 1), (Sum.inr 2427, 1), (Sum.inr 2435, 1), (Sum.inr 2522, 1), (Sum.inr 2560, 1), (Sum.inr 3391, 1), (Sum.inr 4084, -1)]

def numericRow1767 : Integer.Sparse Master := [(Sum.inr 1347, 1), (Sum.inr 2831, 1), (Sum.inr 2902, 1), (Sum.inr 2942, 1), (Sum.inr 2954, 1), (Sum.inr 2964, 1), (Sum.inr 4091, -1)]

def numericRow1768 : Integer.Sparse Master := [(Sum.inr 2584, 1), (Sum.inr 2668, 1), (Sum.inr 2670, 1), (Sum.inr 2674, 1), (Sum.inr 2681, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

def numericRow1769 : Integer.Sparse Master := [(Sum.inr 2670, 1), (Sum.inr 3478, 1), (Sum.inr 3516, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3614, 1), (Sum.inr 4082, -1)]

def numericRow1770 : Integer.Sparse Master := [(Sum.inr 2347, 1), (Sum.inr 2423, 1), (Sum.inr 2431, 1), (Sum.inr 2488, 1), (Sum.inr 2545, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

def numericRow1771 : Integer.Sparse Master := [(Sum.inr 1151, 1), (Sum.inr 2350, 1), (Sum.inr 2431, 1), (Sum.inr 2545, 1), (Sum.inr 2553, 1), (Sum.inr 2557, 1), (Sum.inr 4092, -1)]

def numericRow1772 : Integer.Sparse Master := [(Sum.inr 1330, 1), (Sum.inr 2824, 1), (Sum.inr 2896, 1), (Sum.inr 2916, 1), (Sum.inr 2924, 1), (Sum.inr 2928, 1), (Sum.inr 4091, -1)]

def numericRow1773 : Integer.Sparse Master := [(Sum.inr 2349, 1), (Sum.inr 2890, 1), (Sum.inr 2896, 1), (Sum.inr 2916, 2), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

def numericRow1774 : Integer.Sparse Master := [(Sum.inr 2534, 1), (Sum.inr 3430, 1), (Sum.inr 3433, 1), (Sum.inr 3478, 1), (Sum.inr 3516, 2), (Sum.inr 4082, -1)]

def numericRow1775 : Integer.Sparse Master := [(Sum.inr 2422, 2), (Sum.inr 2432, 1), (Sum.inr 2489, 1), (Sum.inr 3779, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1776 : Integer.Sparse Master := [(Sum.inr 1152, 1), (Sum.inr 2351, 1), (Sum.inr 2432, 1), (Sum.inr 2556, 2), (Sum.inr 4091, -1)]

def numericRow1777 : Integer.Sparse Master := [(Sum.inr 1997, 2), (Sum.inr 2002, 1), (Sum.inr 2044, 1), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

def numericRow1778 : Integer.Sparse Master := [(Sum.inr 3482, 1), (Sum.inr 3522, 2), (Sum.inr 3542, 1), (Sum.inr 3616, 1), (Sum.inr 4082, -1)]

def numericRow1779 : Integer.Sparse Master := [(Sum.inr 2905, 1), (Sum.inr 3680, 1), (Sum.inr 3683, 1), (Sum.inr 3696, 1), (Sum.inr 3796, 1), (Sum.inr 3873, 1), (Sum.inr 4090, -1)]

def numericRow1780 : Integer.Sparse Master := [(Sum.inl 0, 57), (Sum.inl 5, 20), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, 290), (Sum.inr 1138, -1440), (Sum.inr 1143, -720), (Sum.inr 1145, -720), (Sum.inr 1812, -1440), (Sum.inr 1819, -720), (Sum.inr 2112, -720), (Sum.inr 2165, -1440), (Sum.inr 2167, -720), (Sum.inr 2169, -720), (Sum.inr 2287, -720), (Sum.inr 2815, -1440), (Sum.inr 2817, -1440), (Sum.inr 2820, -720), (Sum.inr 2896, -1440), (Sum.inr 2954, -1440), (Sum.inr 3270, -1440), (Sum.inr 3277, -720), (Sum.inr 3311, -720), (Sum.inr 3588, -1440), (Sum.inr 3591, -1440), (Sum.inr 3596, -720), (Sum.inr 3597, -1440), (Sum.inr 3603, -1440), (Sum.inr 3606, -1440), (Sum.inr 3608, -720), (Sum.inr 3614, -1440), (Sum.inr 3633, -720), (Sum.inr 3891, -1440), (Sum.inr 3893, -720), (Sum.inr 3907, -720)]

def numericRow1781 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 5, -20), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, -290), (Sum.inr 1138, 1440), (Sum.inr 1143, 720), (Sum.inr 1145, 720), (Sum.inr 1812, 1440), (Sum.inr 1819, 720), (Sum.inr 2112, 720), (Sum.inr 2815, 1440), (Sum.inr 2817, 1440), (Sum.inr 2820, 720), (Sum.inr 2896, 1440), (Sum.inr 2954, 1440)]

def numericRow1782 : Integer.Sparse Master := [(Sum.inl 0, 15), (Sum.inl 5, 4), (Sum.inl 2, -1), (Sum.inl 7, 16), (Sum.inl 3, 16), (Sum.inl 1, -32), (Sum.inr 932, -432), (Sum.inr 937, -216), (Sum.inr 939, -216), (Sum.inr 1049, -216), (Sum.inr 1681, -432), (Sum.inr 1683, -216), (Sum.inr 1694, -216), (Sum.inr 1738, -216), (Sum.inr 1807, -432), (Sum.inr 1818, -216), (Sum.inr 2109, -216), (Sum.inr 2151, -432), (Sum.inr 2168, -216), (Sum.inr 2261, -216), (Sum.inr 2341, -432), (Sum.inr 2345, -216), (Sum.inr 2431, -432), (Sum.inr 2434, -432), (Sum.inr 2488, -432), (Sum.inr 2590, -432), (Sum.inr 2765, -216), (Sum.inr 3417, -432), (Sum.inr 3423, -216), (Sum.inr 3453, -432), (Sum.inr 3457, -432), (Sum.inr 3478, -432), (Sum.inr 3564, -432), (Sum.inr 3582, -216), (Sum.inr 3613, -432), (Sum.inr 3615, -216), (Sum.inr 3632, -216), (Sum.inr 3892, -432), (Sum.inr 3894, -216), (Sum.inr 3913, -216)]

def numericRow1783 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 5, -4), (Sum.inl 2, 1), (Sum.inl 7, -16), (Sum.inl 3, -16), (Sum.inl 1, 32), (Sum.inr 932, 432), (Sum.inr 937, 216), (Sum.inr 939, 216), (Sum.inr 1049, 216), (Sum.inr 1807, 432), (Sum.inr 1818, 216), (Sum.inr 2109, 216), (Sum.inr 2341, 432), (Sum.inr 2345, 216), (Sum.inr 2431, 432), (Sum.inr 2434, 432), (Sum.inr 2488, 432), (Sum.inr 2590, 432), (Sum.inr 2765, 216)]

def numericRow1784 : Integer.Sparse Master := [(Sum.inl 0, 39), (Sum.inl 5, -40), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 8, -80), (Sum.inl 3, -80), (Sum.inl 1, 50), (Sum.inr 2028, -4320), (Sum.inr 2065, -2160), (Sum.inr 2115, -2160), (Sum.inr 2215, -4320), (Sum.inr 2218, -2160), (Sum.inr 2276, -2160), (Sum.inr 2488, -8640), (Sum.inr 2522, -4320), (Sum.inr 2561, -4320), (Sum.inr 2685, -4320), (Sum.inr 2889, -2160), (Sum.inr 2931, -4320), (Sum.inr 3478, -8640), (Sum.inr 3522, -4320), (Sum.inr 3612, -4320), (Sum.inr 3614, -2160), (Sum.inr 3616, -2160), (Sum.inr 3631, -2160), (Sum.inr 5129, 17280), (Sum.inr 5140, 17280), (Sum.inr 5151, 17280), (Sum.inr 5175, 8640), (Sum.inr 5188, 17280), (Sum.inr 5206, 8640)]

def numericRow1785 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 5, 100), (Sum.inl 2, -55), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, 10), (Sum.inr 2488, 1440), (Sum.inr 2522, 720), (Sum.inr 2867, 1440), (Sum.inr 2888, 720), (Sum.inr 2889, 720), (Sum.inr 2916, 1440), (Sum.inr 2930, 1440), (Sum.inr 2931, 1440), (Sum.inr 2942, 1440), (Sum.inr 2967, 720)]

def numericRow1786 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 5, 10), (Sum.inl 8, 40), (Sum.inl 1, -35), (Sum.inr 1139, -540), (Sum.inr 1144, -540), (Sum.inr 2339, -1080), (Sum.inr 2345, -540), (Sum.inr 2818, -540), (Sum.inr 3274, -540), (Sum.inr 3276, -540), (Sum.inr 3312, -270), (Sum.inr 3420, -1080), (Sum.inr 3423, -540), (Sum.inr 3592, -540), (Sum.inr 3607, -1080), (Sum.inr 3615, -540), (Sum.inr 3616, -540), (Sum.inr 3894, -270), (Sum.inr 3898, -540)]

def numericRow1787 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 5, -10), (Sum.inl 8, -40), (Sum.inl 1, 35), (Sum.inr 1139, 540), (Sum.inr 1144, 540), (Sum.inr 2339, 1080), (Sum.inr 2345, 540), (Sum.inr 2818, 540)]

def numericRow1788 : Integer.Sparse Master := [(Sum.inl 0, 9), (Sum.inl 5, 2), (Sum.inl 8, 8), (Sum.inl 1, 5), (Sum.inr 933, -144), (Sum.inr 938, -144), (Sum.inr 1050, -72), (Sum.inr 1691, -144), (Sum.inr 1693, -144), (Sum.inr 1751, -72), (Sum.inr 2334, -288), (Sum.inr 2342, -144), (Sum.inr 2344, -144), (Sum.inr 2432, -144), (Sum.inr 2489, -144), (Sum.inr 3411, -288), (Sum.inr 3421, -144), (Sum.inr 3422, -144), (Sum.inr 3456, -144), (Sum.inr 3482, -144), (Sum.inr 3607, -288), (Sum.inr 3608, -144), (Sum.inr 3627, -144), (Sum.inr 4042, -144), (Sum.inr 4043, -72)]

def numericRow1789 : Integer.Sparse Master := [(Sum.inl 0, -9), (Sum.inl 5, -2), (Sum.inl 8, -8), (Sum.inl 1, -5), (Sum.inr 933, 144), (Sum.inr 938, 144), (Sum.inr 1050, 72), (Sum.inr 2334, 288), (Sum.inr 2342, 144), (Sum.inr 2344, 144), (Sum.inr 2432, 144), (Sum.inr 2489, 144)]

def numericRow1790 : Integer.Sparse Master := [(Sum.inl 0, 27), (Sum.inl 5, -30), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 8, -40), (Sum.inl 3, -80), (Sum.inl 1, 60), (Sum.inr 2029, -2160), (Sum.inr 2116, -1080), (Sum.inr 2225, -2160), (Sum.inr 2288, -1080), (Sum.inr 2489, -4320), (Sum.inr 2561, -4320), (Sum.inr 2889, -2160), (Sum.inr 2931, -4320), (Sum.inr 3482, -4320), (Sum.inr 3522, -4320), (Sum.inr 3612, -4320), (Sum.inr 3614, -2160), (Sum.inr 3616, -1080), (Sum.inr 3631, -2160), (Sum.inr 5189, 8640)]

def numericRow1791 : Integer.Sparse Master := [(Sum.inr 3482, 2), (Sum.inr 3616, 2), (Sum.inr 4082, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1792 : Integer.Sparse Master := [(Sum.inr 1171, 1), (Sum.inr 2362, 1), (Sum.inr 2529, 1), (Sum.inr 2575, 1), (Sum.inr 2590, 1), (Sum.inr 2600, 1), (Sum.inr 4092, -1)]

def numericRow1793 : Integer.Sparse Master := [(Sum.inr 1812, 1), (Sum.inr 2892, 1), (Sum.inr 2899, 1), (Sum.inr 2930, 2), (Sum.inr 3394, 1), (Sum.inr 4083, -1)]

def numericRow1794 : Integer.Sparse Master := [(Sum.inr 2396, 1), (Sum.inr 2399, 1), (Sum.inr 2401, 1), (Sum.inr 2405, 1), (Sum.inr 2681, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

def numericRow1795 : Integer.Sparse Master := [(Sum.inr 2339, -1), (Sum.inr 2485, -1), (Sum.inr 2815, -1), (Sum.inr 2893, -1), (Sum.inr 2924, -1), (Sum.inr 2931, -1), (Sum.inr 2954, -1), (Sum.inr 3077, -1), (Sum.inr 3420, -1), (Sum.inr 3481, -1), (Sum.inr 3588, -1), (Sum.inr 3599, -1), (Sum.inr 3605, -1), (Sum.inr 3606, -1), (Sum.inr 3612, -1), (Sum.inr 3625, -1), (Sum.inr 3690, -1), (Sum.inr 3694, -1), (Sum.inr 3764, -1), (Sum.inr 3773, -1), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 4332, 4), (Sum.inr 4334, 4), (Sum.inr 4335, 4), (Sum.inr 4357, 4), (Sum.inr 4444, 4), (Sum.inr 4930, 4), (Sum.inr 4933, 4), (Sum.inr 4934, 4), (Sum.inr 4935, 4), (Sum.inr 4951, 4), (Sum.inr 4954, 4), (Sum.inr 5040, 4), (Sum.inr 5067, 4), (Sum.inr 5145, 4), (Sum.inr 5147, 4), (Sum.inr 5164, 4), (Sum.inr 5282, 4)]

def numericRow1796 : Integer.Sparse Master := [(Sum.inl 0, -308), (Sum.inl 5, -240), (Sum.inl 2, 400), (Sum.inl 7, 320), (Sum.inl 8, 320), (Sum.inl 51, -960), (Sum.inl 3, 320), (Sum.inl 1, -620), (Sum.inr 910, 5760), (Sum.inr 912, 5760), (Sum.inr 913, 5760), (Sum.inr 935, 5760), (Sum.inr 1026, 5760), (Sum.inr 2324, 5760), (Sum.inr 2325, 5760), (Sum.inr 2326, 5760), (Sum.inr 2343, 5760), (Sum.inr 2347, 5760), (Sum.inr 2422, 5760), (Sum.inr 2433, 5760), (Sum.inr 2473, 5760), (Sum.inr 2567, 5760), (Sum.inr 2569, 5760), (Sum.inr 2591, 5760), (Sum.inr 2751, 5760)]

def numericRow1797 : Integer.Sparse Master := [(Sum.inr 1678, 1), (Sum.inr 1679, 1), (Sum.inr 1682, 1), (Sum.inr 1689, 1), (Sum.inr 1736, 1), (Sum.inr 3408, 1), (Sum.inr 3414, 1), (Sum.inr 3415, 1), (Sum.inr 3418, 1), (Sum.inr 3419, 1), (Sum.inr 3420, 1), (Sum.inr 3452, 1), (Sum.inr 3454, 1), (Sum.inr 3476, 1), (Sum.inr 3481, 1), (Sum.inr 3530, 1), (Sum.inr 3562, 1), (Sum.inr 3565, 1), (Sum.inr 3580, 1), (Sum.inr 3588, 1), (Sum.inr 3599, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3764, 1), (Sum.inr 3773, 1), (Sum.inr 3961, 1)]

def numericRow1798 : Integer.Sparse Master := [(Sum.inr 2326, 1), (Sum.inr 2802, 1), (Sum.inr 2822, 1), (Sum.inr 2827, 1), (Sum.inr 2931, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

def numericRow1799 : Integer.Sparse Master := [(Sum.inr 1328, 1), (Sum.inr 2822, 1), (Sum.inr 2893, 1), (Sum.inr 2924, 1), (Sum.inr 2925, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

def numericRow1800 : Integer.Sparse Master := [(Sum.inr 1338, 1), (Sum.inr 2827, 1), (Sum.inr 2900, 1), (Sum.inr 2931, 1), (Sum.inr 2954, 1), (Sum.inr 2955, 1), (Sum.inr 4091, -1)]

def numericRow1801 : Integer.Sparse Master := [(Sum.inr 2399, 1), (Sum.inr 3433, 1), (Sum.inr 3522, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

def numericRow1802 : Integer.Sparse Master := [(Sum.inr 2910, 1), (Sum.inr 3346, 1), (Sum.inr 3349, 1), (Sum.inr 3357, 1), (Sum.inr 3479, 1), (Sum.inr 3570, 1), (Sum.inr 4080, -1)]

def numericRow1803 : Integer.Sparse Master := [(Sum.inr 2355, 1), (Sum.inr 2438, 1), (Sum.inr 2443, 1), (Sum.inr 2488, 1), (Sum.inr 2620, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

def numericRow1804 : Integer.Sparse Master := [(Sum.inr 2352, 1), (Sum.inr 2798, 1), (Sum.inr 2803, 1), (Sum.inr 2817, 1), (Sum.inr 2867, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

def numericRow1805 : Integer.Sparse Master := [(Sum.inr 1321, 1), (Sum.inr 2817, 1), (Sum.inr 2848, 1), (Sum.inr 2867, 1), (Sum.inr 2881, 1), (Sum.inr 2885, 1), (Sum.inr 4092, -1)]

def numericRow1806 : Integer.Sparse Master := [(Sum.inr 2538, 1), (Sum.inr 3345, 1), (Sum.inr 3348, 1), (Sum.inr 3354, 1), (Sum.inr 3478, 1), (Sum.inr 3538, 1), (Sum.inr 4082, -1)]

def numericRow1807 : Integer.Sparse Master := [(Sum.inr 2048, 1), (Sum.inr 3386, 1), (Sum.inr 3491, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3542, 1), (Sum.inr 4082, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1808 : Integer.Sparse Master := [(Sum.inr 2799, 1), (Sum.inr 2802, 2), (Sum.inr 2818, 1), (Sum.inr 2868, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

def numericRow1809 : Integer.Sparse Master := [(Sum.inr 1322, 1), (Sum.inr 2818, 1), (Sum.inr 2849, 1), (Sum.inr 2868, 1), (Sum.inr 2884, 2), (Sum.inr 4091, -1)]

def numericRow1810 : Integer.Sparse Master := [(Sum.inr 1819, 1), (Sum.inr 2812, 2), (Sum.inr 2821, 1), (Sum.inr 2888, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

def numericRow1811 : Integer.Sparse Master := [(Sum.inr 2345, -1), (Sum.inr 2519, -1), (Sum.inr 2813, -2), (Sum.inr 2820, -1), (Sum.inr 2881, -2), (Sum.inr 3054, -1), (Sum.inr 3423, -1), (Sum.inr 3486, -1), (Sum.inr 3595, -2), (Sum.inr 3596, -1), (Sum.inr 3624, -2), (Sum.inr 3626, -1), (Sum.inr 3705, -2), (Sum.inr 3767, -2), (Sum.inr 3963, -2), (Sum.inr 4372, 8), (Sum.inr 4373, 4), (Sum.inr 4374, 4), (Sum.inr 4480, 4), (Sum.inr 4944, 8), (Sum.inr 4965, 8), (Sum.inr 5044, 8), (Sum.inr 5090, 8), (Sum.inr 5199, 8), (Sum.inr 5201, 4), (Sum.inr 5300, 4)]

def numericRow1812 : Integer.Sparse Master := [(Sum.inr 1734, 2), (Sum.inr 1735, 1), (Sum.inr 1740, 1), (Sum.inr 1748, 1), (Sum.inr 3413, 2), (Sum.inr 3423, 1), (Sum.inr 3474, 2), (Sum.inr 3475, 2), (Sum.inr 3480, 2), (Sum.inr 3486, 1), (Sum.inr 3578, 2), (Sum.inr 3579, 1), (Sum.inr 3584, 1), (Sum.inr 3595, 2), (Sum.inr 3596, 1), (Sum.inr 3624, 2), (Sum.inr 3626, 1), (Sum.inr 3767, 2), (Sum.inr 3963, 1)]

def numericRow1813 : Integer.Sparse Master := [(Sum.inr 2345, 1), (Sum.inr 2813, 2), (Sum.inr 2820, 1), (Sum.inr 2889, 1), (Sum.inr 4092, -1)]

def numericRow1814 : Integer.Sparse Master := [(Sum.inr 2533, 1), (Sum.inr 3679, 1), (Sum.inr 3681, 1), (Sum.inr 3695, 1), (Sum.inr 3795, 1), (Sum.inr 3832, 1), (Sum.inr 4088, -1)]

def numericRow1815 : Integer.Sparse Master := [(Sum.inr 1246, -1), (Sum.inr 2334, -1), (Sum.inr 2428, -1), (Sum.inr 2434, -1), (Sum.inr 2482, -1), (Sum.inr 2553, -1), (Sum.inr 2561, -1), (Sum.inr 2590, -1), (Sum.inr 2743, -1), (Sum.inr 3301, -1), (Sum.inr 3411, -1), (Sum.inr 3450, -1), (Sum.inr 3457, -1), (Sum.inr 3468, -1), (Sum.inr 3514, -1), (Sum.inr 3522, -1), (Sum.inr 3548, -1), (Sum.inr 3564, -1), (Sum.inr 3689, -1), (Sum.inr 3693, -1), (Sum.inr 3757, -1), (Sum.inr 3770, -1), (Sum.inr 3845, -2), (Sum.inr 4533, 4), (Sum.inr 4534, 4), (Sum.inr 4535, 4), (Sum.inr 4556, 4), (Sum.inr 4934, 4), (Sum.inr 4955, 4), (Sum.inr 4956, 4), (Sum.inr 4959, 4), (Sum.inr 4966, 4), (Sum.inr 5112, 4), (Sum.inr 5139, 4), (Sum.inr 5164, 4)]

def numericRow1816 : Integer.Sparse Master := [(Sum.inl 0, -99), (Sum.inl 5, -80), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 8, 80), (Sum.inl 3, 80), (Sum.inl 1, 130), (Sum.inr 1117, 1080), (Sum.inr 1119, 1080), (Sum.inr 1120, 1080), (Sum.inr 1141, 1080), (Sum.inr 2349, 1080), (Sum.inr 2352, 1080), (Sum.inr 2618, 1080), (Sum.inr 2801, 1080), (Sum.inr 2802, 1080), (Sum.inr 2819, 1080), (Sum.inr 2898, 1080), (Sum.inr 2955, 1080)]

def numericRow1817 : Integer.Sparse Master := [(Sum.inr 3267, 1), (Sum.inr 3268, 1), (Sum.inr 3271, 1), (Sum.inr 3272, 1), (Sum.inr 3301, 1), (Sum.inr 3411, 1), (Sum.inr 3415, 1), (Sum.inr 3450, 1), (Sum.inr 3457, 1), (Sum.inr 3468, 1), (Sum.inr 3508, 1), (Sum.inr 3510, 1), (Sum.inr 3512, 1), (Sum.inr 3514, 1), (Sum.inr 3522, 1), (Sum.inr 3523, 1), (Sum.inr 3548, 1), (Sum.inr 3555, 1), (Sum.inr 3556, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 3757, 1), (Sum.inr 3770, 1), (Sum.inr 3845, 1)]

def numericRow1818 : Integer.Sparse Master := [(Sum.inr 2325, 1), (Sum.inr 2348, 1), (Sum.inr 2352, 1), (Sum.inr 2356, 1), (Sum.inr 2561, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

def numericRow1819 : Integer.Sparse Master := [(Sum.inr 1149, 1), (Sum.inr 2348, 1), (Sum.inr 2428, 1), (Sum.inr 2553, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

def numericRow1820 : Integer.Sparse Master := [(Sum.inr 2524, 1), (Sum.inr 2525, 1), (Sum.inr 2561, 2), (Sum.inr 3689, 1), (Sum.inr 4092, -1)]

def numericRow1821 : Integer.Sparse Master := [(Sum.inr 1160, 1), (Sum.inr 2356, 1), (Sum.inr 2525, 1), (Sum.inr 2561, 1), (Sum.inr 2590, 1), (Sum.inr 2591, 1), (Sum.inr 4092, -1)]

def numericRow1822 : Integer.Sparse Master := [(Sum.inl 0, 199), (Sum.inl 6, -10), (Sum.inl 2, 80), (Sum.inl 7, 80), (Sum.inl 8, 80), (Sum.inl 3, 160), (Sum.inl 4, 80), (Sum.inl 1, 75), (Sum.inr 901, -4320), (Sum.inr 902, -4320), (Sum.inr 903, -4320), (Sum.inr 927, -4320), (Sum.inr 985, -4320), (Sum.inr 1589, -4320), (Sum.inr 1590, -4320), (Sum.inr 1591, -4320), (Sum.inr 1618, -4320), (Sum.inr 1675, -4320), (Sum.inr 1760, -4320), (Sum.inr 1766, -4320), (Sum.inr 1773, -4320), (Sum.inr 1836, -4320), (Sum.inr 1841, -4320), (Sum.inr 1850, -4320), (Sum.inr 2022, -4320), (Sum.inr 2203, -4320), (Sum.inr 2295, -4320), (Sum.inr 2300, -4320), (Sum.inr 2306, -4320), (Sum.inr 2318, -4320), (Sum.inr 2337, -4320), (Sum.inr 2372, -4320), (Sum.inr 2388, -4320), (Sum.inr 2428, -4320), (Sum.inr 2452, -4320), (Sum.inr 2482, -4320), (Sum.inr 2553, -4320), (Sum.inr 2556, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 3315, -4320), (Sum.inr 3318, -4320), (Sum.inr 3325, -4320), (Sum.inr 3336, -4320), (Sum.inr 3354, -4320), (Sum.inr 3400, -4320), (Sum.inr 3412, -4320), (Sum.inr 3433, -4320), (Sum.inr 3450, -4320), (Sum.inr 3468, -4320), (Sum.inr 3514, -4320), (Sum.inr 3521, -4320), (Sum.inr 3533, -4320), (Sum.inr 3544, -4320), (Sum.inr 3603, -4320), (Sum.inr 3607, -4320), (Sum.inr 3690, -4320), (Sum.inr 3694, -4320), (Sum.inr 3705, -4320), (Sum.inr 3764, -4320), (Sum.inr 3767, -4320), (Sum.inr 3773, -4320), (Sum.inr 3903, -4320), (Sum.inr 4047, -4320)]

def numericRow1823 : Integer.Sparse Master := [(Sum.inr 2541, 1), (Sum.inr 3646, 1), (Sum.inr 3757, 2), (Sum.inr 4088, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1824 : Integer.Sparse Master := [(Sum.inr 2456, 1), (Sum.inr 2756, 1), (Sum.inr 3680, 1), (Sum.inr 3776, 1), (Sum.inr 3796, 2), (Sum.inr 4090, -1)]

def numericRow1825 : Integer.Sparse Master := [(Sum.inr 1138, -1), (Sum.inr 2341, -1), (Sum.inr 2431, -1), (Sum.inr 2479, -1), (Sum.inr 2482, -1), (Sum.inr 2515, -1), (Sum.inr 2722, -1), (Sum.inr 3270, -1), (Sum.inr 3417, -1), (Sum.inr 3453, -1), (Sum.inr 3459, -1), (Sum.inr 3468, -1), (Sum.inr 3479, -1), (Sum.inr 3533, -1), (Sum.inr 3693, -1), (Sum.inr 3719, -1), (Sum.inr 3732, -1), (Sum.inr 3770, -1), (Sum.inr 3795, -1), (Sum.inr 3809, -1), (Sum.inr 3811, -1), (Sum.inr 3813, -1), (Sum.inr 4529, 4), (Sum.inr 4534, 4), (Sum.inr 4536, 4), (Sum.inr 4592, 4), (Sum.inr 4664, 4), (Sum.inr 4670, 4), (Sum.inr 4682, 4), (Sum.inr 4853, 4), (Sum.inr 4931, 4), (Sum.inr 4934, 4), (Sum.inr 4954, 4), (Sum.inr 4965, 4), (Sum.inr 5042, 4), (Sum.inr 5074, 4), (Sum.inr 5129, 4), (Sum.inr 5188, 4), (Sum.inr 5260, 4)]

def numericRow1826 : Integer.Sparse Master := [(Sum.inr 2147, 1), (Sum.inr 2149, 1), (Sum.inr 2153, 1), (Sum.inr 2164, 1), (Sum.inr 2259, 1), (Sum.inr 3258, 1), (Sum.inr 3268, 1), (Sum.inr 3270, 1), (Sum.inr 3295, 1), (Sum.inr 3406, 1), (Sum.inr 3415, 1), (Sum.inr 3417, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3459, 1), (Sum.inr 3462, 1), (Sum.inr 3463, 1), (Sum.inr 3468, 1), (Sum.inr 3475, 1), (Sum.inr 3479, 1), (Sum.inr 3516, 1), (Sum.inr 3533, 1), (Sum.inr 3538, 1), (Sum.inr 3540, 1), (Sum.inr 3770, 1), (Sum.inr 3795, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1)]

def numericRow1827 : Integer.Sparse Master := [(Sum.inr 2321, 1), (Sum.inr 2325, 1), (Sum.inr 2327, 1), (Sum.inr 2341, 1), (Sum.inr 2488, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

def numericRow1828 : Integer.Sparse Master := [(Sum.inr 1139, -1), (Sum.inr 2342, -1), (Sum.inr 2432, -1), (Sum.inr 2480, -2), (Sum.inr 2485, -2), (Sum.inr 2723, -2), (Sum.inr 3274, -1), (Sum.inr 3421, -1), (Sum.inr 3456, -1), (Sum.inr 3467, -2), (Sum.inr 3481, -2), (Sum.inr 3544, -2), (Sum.inr 3694, -1), (Sum.inr 3773, -1), (Sum.inr 3779, -1), (Sum.inr 3790, -1), (Sum.inr 3797, -1), (Sum.inr 3815, -1), (Sum.inr 4530, 4), (Sum.inr 4535, 8), (Sum.inr 4593, 4), (Sum.inr 4930, 8), (Sum.inr 4935, 8), (Sum.inr 4944, 8), (Sum.inr 5043, 4), (Sum.inr 5189, 4)]

def numericRow1829 : Integer.Sparse Master := [(Sum.inr 3261, 1), (Sum.inr 3272, 2), (Sum.inr 3274, 1), (Sum.inr 3297, 1), (Sum.inr 3408, 2), (Sum.inr 3413, 2), (Sum.inr 3419, 2), (Sum.inr 3421, 1), (Sum.inr 3456, 1), (Sum.inr 3465, 1), (Sum.inr 3467, 2), (Sum.inr 3481, 2), (Sum.inr 3542, 1), (Sum.inr 3544, 2), (Sum.inr 3773, 1), (Sum.inr 3797, 1), (Sum.inr 3815, 1)]

def numericRow1830 : Integer.Sparse Master := [(Sum.inr 2326, 2), (Sum.inr 2342, 1), (Sum.inr 2489, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

def numericRow1831 : Integer.Sparse Master := [(Sum.inr 1143, -1), (Sum.inr 1807, -2), (Sum.inr 1818, -1), (Sum.inr 2151, -2), (Sum.inr 2167, -1), (Sum.inr 2168, -1), (Sum.inr 2509, -2), (Sum.inr 2672, -2), (Sum.inr 2686, -1), (Sum.inr 2704, -2), (Sum.inr 2740, -2), (Sum.inr 3054, -1), (Sum.inr 3391, -2), (Sum.inr 3397, -1), (Sum.inr 3626, -1), (Sum.inr 4548, 8), (Sum.inr 4560, 4), (Sum.inr 4611, 4), (Sum.inr 4699, 8), (Sum.inr 4705, 4), (Sum.inr 4881, 4), (Sum.inr 4945, 8), (Sum.inr 5035, 8), (Sum.inr 5103, 8), (Sum.inr 5140, 8), (Sum.inr 5276, 4)]

def numericRow1832 : Integer.Sparse Master := [(Sum.inr 2151, 2), (Sum.inr 2167, 1), (Sum.inr 2168, 1), (Sum.inr 2256, 2), (Sum.inr 2258, 1), (Sum.inr 2267, 1), (Sum.inr 2286, 1), (Sum.inr 2652, 2), (Sum.inr 2657, 2), (Sum.inr 2658, 2), (Sum.inr 2670, 2), (Sum.inr 2672, 2), (Sum.inr 2683, 1), (Sum.inr 2686, 1), (Sum.inr 2704, 2), (Sum.inr 2740, 1), (Sum.inr 3024, 2), (Sum.inr 3052, 1), (Sum.inr 3054, 1)]

def numericRow1833 : Integer.Sparse Master := [(Sum.inr 1134, -2), (Sum.inr 1144, -1), (Sum.inr 1145, -1), (Sum.inr 1246, -1), (Sum.inr 2334, -2), (Sum.inr 2337, -2), (Sum.inr 2344, -1), (Sum.inr 2345, -1), (Sum.inr 2428, -2), (Sum.inr 2434, -2), (Sum.inr 2512, -2), (Sum.inr 2519, -1), (Sum.inr 2561, -2), (Sum.inr 2743, -1), (Sum.inr 3265, -2), (Sum.inr 3276, -1), (Sum.inr 3277, -1), (Sum.inr 3301, -1), (Sum.inr 3411, -2), (Sum.inr 3412, -2), (Sum.inr 3422, -1), (Sum.inr 3423, -1), (Sum.inr 3450, -2), (Sum.inr 3457, -2), (Sum.inr 3471, -2), (Sum.inr 3486, -1), (Sum.inr 3522, -2), (Sum.inr 3548, -1), (Sum.inr 4092, 4)]

def numericRow1834 : Integer.Sparse Master := [(Sum.inr 3265, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 3301, 1), (Sum.inr 3411, 2), (Sum.inr 3412, 2), (Sum.inr 3422, 1), (Sum.inr 3423, 1), (Sum.inr 3450, 2), (Sum.inr 3457, 2), (Sum.inr 3471, 2), (Sum.inr 3486, 1), (Sum.inr 3522, 2), (Sum.inr 3548, 1), (Sum.inr 4092, 1)]

def numericRow1835 : Integer.Sparse Master := [(Sum.inr 1106, -1), (Sum.inr 1110, -2), (Sum.inr 1124, -1), (Sum.inr 1205, -1), (Sum.inr 2295, -2), (Sum.inr 2300, -2), (Sum.inr 2316, -1), (Sum.inr 2329, -1), (Sum.inr 2385, -2), (Sum.inr 2424, -1), (Sum.inr 2459, -2), (Sum.inr 2505, -2), (Sum.inr 2541, -1), (Sum.inr 2705, -2), (Sum.inr 3249, -1), (Sum.inr 3252, -2), (Sum.inr 3254, -1), (Sum.inr 3284, -1), (Sum.inr 3315, -2), (Sum.inr 3325, -2), (Sum.inr 3353, -2), (Sum.inr 3398, -1), (Sum.inr 3402, -1), (Sum.inr 3429, -2), (Sum.inr 3440, -1), (Sum.inr 3448, -2), (Sum.inr 3487, -1), (Sum.inr 3498, -2), (Sum.inr 4088, 4)]

def numericRow1836 : Integer.Sparse Master := [(Sum.inr 2379, 1), (Sum.inr 3646, 1), (Sum.inr 3718, 2), (Sum.inr 3757, 1), (Sum.inr 3759, 1), (Sum.inr 4088, -1)]

def numericRow1837 : Integer.Sparse Master := [(Sum.inr 2388, 1), (Sum.inr 3681, 1), (Sum.inr 3702, 1), (Sum.inr 3767, 1), (Sum.inr 4088, -1)]

def numericRow1838 : Integer.Sparse Master := [(Sum.inr 1099, -2), (Sum.inr 1104, -2), (Sum.inr 1193, -1), (Sum.inr 2306, -4), (Sum.inr 2370, -2), (Sum.inr 2400, -4), (Sum.inr 2407, -2), (Sum.inr 2539, -2), (Sum.inr 2686, -2), (Sum.inr 3233, -2), (Sum.inr 3237, -2), (Sum.inr 3248, -1), (Sum.inr 3318, -4), (Sum.inr 3334, -2), (Sum.inr 3344, -4), (Sum.inr 3360, -2), (Sum.inr 3372, -2), (Sum.inr 3397, -2), (Sum.inr 4089, 4)]

def numericRow1839 : Integer.Sparse Master := [(Sum.inr 1049, -1), (Sum.inr 1738, -1), (Sum.inr 2028, -2), (Sum.inr 2106, -2), (Sum.inr 2109, -1), (Sum.inr 2215, -2), (Sum.inr 2242, -2), (Sum.inr 2261, -1), (Sum.inr 2266, -1), (Sum.inr 2278, -1), (Sum.inr 2765, -1), (Sum.inr 3582, -1), (Sum.inr 4368, 8), (Sum.inr 4373, 4), (Sum.inr 4375, 4), (Sum.inr 4687, 8), (Sum.inr 4694, 4), (Sum.inr 4700, 8), (Sum.inr 4704, 4), (Sum.inr 4773, 8), (Sum.inr 4776, 8), (Sum.inr 4867, 8), (Sum.inr 4872, 4), (Sum.inr 5264, 8), (Sum.inr 5297, 4), (Sum.inr 5300, 4)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1840 : Integer.Sparse Master := [(Sum.inl 0, -120), (Sum.inl 5, -40), (Sum.inl 2, 170), (Sum.inl 54, 480), (Sum.inl 1, 290), (Sum.inr 1321, 4320), (Sum.inr 1323, 2160), (Sum.inr 1325, 2160), (Sum.inr 1813, 4320), (Sum.inr 1820, 2160), (Sum.inr 2113, 2160), (Sum.inr 2816, 4320), (Sum.inr 2821, 2160), (Sum.inr 3040, 4320), (Sum.inr 3055, 2160), (Sum.inr 3056, 2160), (Sum.inr 3131, 4320), (Sum.inr 3163, 4320), (Sum.inr 3180, 4320)]

def numericRow1841 : Integer.Sparse Master := [(Sum.inr 1712, 2), (Sum.inr 1735, 1), (Sum.inr 1738, 1), (Sum.inr 1743, 1), (Sum.inr 2162, 2), (Sum.inr 2163, 1), (Sum.inr 2194, 2), (Sum.inr 2212, 2), (Sum.inr 2215, 2), (Sum.inr 2242, 2), (Sum.inr 2249, 2), (Sum.inr 2251, 2), (Sum.inr 2261, 1), (Sum.inr 2273, 1), (Sum.inr 2278, 1), (Sum.inr 2282, 1), (Sum.inr 2729, 2), (Sum.inr 2765, 1), (Sum.inr 2771, 1), (Sum.inr 2774, 1)]

def numericRow1842 : Integer.Sparse Master := [(Sum.inr 1826, 2), (Sum.inr 1830, 1), (Sum.inr 1832, 1), (Sum.inr 2115, 1), (Sum.inr 3056, 1), (Sum.inr 4084, -1)]

def numericRow1843 : Integer.Sparse Master := [(Sum.inr 946, 1), (Sum.inr 1826, 1), (Sum.inr 1974, 1), (Sum.inr 2106, 1), (Sum.inr 2108, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

def numericRow1844 : Integer.Sparse Master := [(Sum.inl 0, 81), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 23, 720), (Sum.inl 12, -240), (Sum.inl 27, 180), (Sum.inl 1, 510), (Sum.inr 738, -12960), (Sum.inr 741, -6480), (Sum.inr 743, -6480), (Sum.inr 819, -12960), (Sum.inr 820, -6480), (Sum.inr 830, -12960), (Sum.inr 844, -6480), (Sum.inr 1799, -12960), (Sum.inr 1814, -12960), (Sum.inr 1817, -6480), (Sum.inr 1819, -6480), (Sum.inr 1878, -12960), (Sum.inr 1881, -12960), (Sum.inr 1919, -12960), (Sum.inr 1920, -12960), (Sum.inr 1928, -25920), (Sum.inr 1939, -12960), (Sum.inr 2101, -25920), (Sum.inr 2103, -12960), (Sum.inr 2110, -12960), (Sum.inr 2112, -6480), (Sum.inr 2115, -6480), (Sum.inr 2157, -12960), (Sum.inr 2159, -6480), (Sum.inr 2169, -6480), (Sum.inr 2275, -12960), (Sum.inr 2276, -6480), (Sum.inr 2279, -12960), (Sum.inr 2287, -6480), (Sum.inr 3732, -12960), (Sum.inr 3811, -12960), (Sum.inr 3886, -12960), (Sum.inr 3893, -6480), (Sum.inr 3907, -6480)]

def numericRow1845 : Integer.Sparse Master := [(Sum.inl 0, -81), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 23, -720), (Sum.inl 12, 240), (Sum.inl 27, -180), (Sum.inl 1, -510), (Sum.inr 738, 12960), (Sum.inr 741, 6480), (Sum.inr 743, 6480), (Sum.inr 830, 6480), (Sum.inr 1799, 12960), (Sum.inr 1814, 12960), (Sum.inr 1817, 6480), (Sum.inr 1819, 6480), (Sum.inr 1878, 12960), (Sum.inr 1881, 12960), (Sum.inr 1928, 12960), (Sum.inr 2101, 12960), (Sum.inr 2103, 6480), (Sum.inr 2110, 12960), (Sum.inr 2112, 6480), (Sum.inr 2276, 6480), (Sum.inr 2279, 6480), (Sum.inr 3732, 12960), (Sum.inr 3886, 6480)]

def numericRow1846 : Integer.Sparse Master := [(Sum.inl 0, -116), (Sum.inl 5, 160), (Sum.inl 2, -80), (Sum.inl 7, 320), (Sum.inl 51, -960), (Sum.inl 3, 320), (Sum.inl 1, -220), (Sum.inr 1640, 17280), (Sum.inr 1652, 8640), (Sum.inr 1653, 8640), (Sum.inr 1660, 8640), (Sum.inr 2028, 17280), (Sum.inr 2065, 8640), (Sum.inr 2072, 17280), (Sum.inr 2081, 17280), (Sum.inr 2082, 17280), (Sum.inr 2093, 17280), (Sum.inr 2094, 17280), (Sum.inr 2114, 8640), (Sum.inr 2116, 8640), (Sum.inr 2122, 17280), (Sum.inr 2137, 8640), (Sum.inr 2138, 8640), (Sum.inr 2620, 17280), (Sum.inr 2643, 8640)]

def numericRow1847 : Integer.Sparse Master := [(Sum.inl 0, -120), (Sum.inl 5, 200), (Sum.inl 2, -130), (Sum.inl 54, 480), (Sum.inl 1, -10), (Sum.inr 1371, 4320), (Sum.inr 1373, 2160), (Sum.inr 1374, 2160), (Sum.inr 2867, 4320), (Sum.inr 2872, 4320), (Sum.inr 2887, 2160), (Sum.inr 2888, 2160), (Sum.inr 2889, 2160), (Sum.inr 3151, 4320), (Sum.inr 3159, 4320), (Sum.inr 3160, 2160), (Sum.inr 3161, 2160), (Sum.inr 3168, 4320), (Sum.inr 3174, 4320)]

def numericRow1848 : Integer.Sparse Master := [(Sum.inr 1050, -1), (Sum.inr 1751, -1), (Sum.inr 2029, -2), (Sum.inr 2107, -4), (Sum.inr 2112, -2), (Sum.inr 2225, -2), (Sum.inr 2260, -4), (Sum.inr 2287, -2), (Sum.inr 2782, -2), (Sum.inr 3583, -2), (Sum.inr 4369, 8), (Sum.inr 4374, 8), (Sum.inr 4701, 8), (Sum.inr 4705, 8), (Sum.inr 4774, 8), (Sum.inr 4777, 16), (Sum.inr 5269, 8), (Sum.inr 5303, 4)]

def numericRow1849 : Integer.Sparse Master := [(Sum.inl 0, -104), (Sum.inl 5, -40), (Sum.inl 2, -80), (Sum.inl 56, 480), (Sum.inl 1, -160), (Sum.inr 1322, 2880), (Sum.inr 1324, 2880), (Sum.inr 2340, 5760), (Sum.inr 2346, 2880), (Sum.inr 3108, 2880), (Sum.inr 3118, 1440), (Sum.inr 3132, 2880), (Sum.inr 3164, 2880)]

def numericRow1850 : Integer.Sparse Master := [(Sum.inr 1721, 2), (Sum.inr 1748, 2), (Sum.inr 1751, 1), (Sum.inr 2199, 2), (Sum.inr 2223, 4), (Sum.inr 2225, 2), (Sum.inr 2257, 2), (Sum.inr 2260, 4), (Sum.inr 2286, 2), (Sum.inr 2287, 2), (Sum.inr 2736, 2), (Sum.inr 2779, 1), (Sum.inr 2782, 2)]

def numericRow1851 : Integer.Sparse Master := [(Sum.inr 1827, 2), (Sum.inr 1831, 2), (Sum.inr 2116, 1), (Sum.inr 3118, 1), (Sum.inr 4083, -1)]

def numericRow1852 : Integer.Sparse Master := [(Sum.inr 947, 1), (Sum.inr 1827, 1), (Sum.inr 1975, 1), (Sum.inr 2107, 2), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

def numericRow1853 : Integer.Sparse Master := [(Sum.inl 0, 81), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 24, 360), (Sum.inl 4, -240), (Sum.inl 27, 90), (Sum.inl 1, -120), (Sum.inr 739, -6480), (Sum.inr 742, -6480), (Sum.inr 831, -3240), (Sum.inr 841, -6480), (Sum.inr 843, -6480), (Sum.inr 858, -3240), (Sum.inr 1815, -6480), (Sum.inr 1818, -6480), (Sum.inr 1879, -6480), (Sum.inr 1880, -12960), (Sum.inr 1929, -6480), (Sum.inr 1936, -6480), (Sum.inr 1938, -12960), (Sum.inr 1949, -6480), (Sum.inr 2107, -12960), (Sum.inr 2109, -6480), (Sum.inr 2166, -6480), (Sum.inr 2168, -6480), (Sum.inr 2260, -12960), (Sum.inr 2261, -6480), (Sum.inr 2266, -6480), (Sum.inr 2278, -6480), (Sum.inr 3790, -6480), (Sum.inr 3815, -6480), (Sum.inr 3894, -3240), (Sum.inr 3913, -6480)]

def numericRow1854 : Integer.Sparse Master := [(Sum.inl 0, -81), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 24, -360), (Sum.inl 4, 240), (Sum.inl 27, -90), (Sum.inl 1, 120), (Sum.inr 739, 6480), (Sum.inr 742, 6480), (Sum.inr 831, 3240), (Sum.inr 1815, 6480), (Sum.inr 1818, 6480), (Sum.inr 1879, 6480), (Sum.inr 1880, 12960), (Sum.inr 1929, 6480), (Sum.inr 2107, 12960), (Sum.inr 2109, 6480), (Sum.inr 2278, 6480), (Sum.inr 3790, 6480)]

def numericRow1855 : Integer.Sparse Master := [(Sum.inl 0, 6), (Sum.inl 5, -5), (Sum.inl 8, -20), (Sum.inl 1, -5), (Sum.inr 1075, -1080), (Sum.inr 1653, -1080), (Sum.inr 2029, -1080), (Sum.inr 2048, -2160), (Sum.inr 2082, -2160), (Sum.inr 2115, -1080), (Sum.inr 2225, -1080), (Sum.inr 2276, -1080), (Sum.inr 2889, -1080), (Sum.inr 3616, -540), (Sum.inr 3631, -1080), (Sum.inr 4487, 4320), (Sum.inr 4506, 2160), (Sum.inr 4825, 4320), (Sum.inr 4842, 4320), (Sum.inr 4856, 8640), (Sum.inr 4884, 4320), (Sum.inr 5189, 4320)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1856 : Integer.Sparse Master := [(Sum.inl 0, -104), (Sum.inl 5, 120), (Sum.inl 2, -60), (Sum.inl 8, 160), (Sum.inl 51, -960), (Sum.inl 1, 100), (Sum.inr 1641, 8640), (Sum.inr 1653, 8640), (Sum.inr 1661, 4320), (Sum.inr 2029, 8640), (Sum.inr 2073, 8640), (Sum.inr 2082, 17280), (Sum.inr 2094, 17280), (Sum.inr 2115, 8640), (Sum.inr 2123, 8640), (Sum.inr 2138, 8640), (Sum.inr 2621, 8640)]

def numericRow1857 : Integer.Sparse Master := [(Sum.inr 1876, 1), (Sum.inr 1880, 1), (Sum.inr 1881, 1), (Sum.inr 2082, 1), (Sum.inr 3448, 1), (Sum.inr 4080, -1)]

def numericRow1858 : Integer.Sparse Master := [(Sum.inr 932, -1), (Sum.inr 1049, -1), (Sum.inr 1681, -1), (Sum.inr 1738, -1), (Sum.inr 1814, -1), (Sum.inr 1966, -1), (Sum.inr 2019, -1), (Sum.inr 2022, -1), (Sum.inr 2028, -1), (Sum.inr 2058, -1), (Sum.inr 2115, -1), (Sum.inr 2157, -1), (Sum.inr 2177, -1), (Sum.inr 2190, -1), (Sum.inr 2203, -1), (Sum.inr 2215, -1), (Sum.inr 2216, -1), (Sum.inr 2266, -1), (Sum.inr 2276, -1), (Sum.inr 2278, -1), (Sum.inr 2722, -1), (Sum.inr 3533, -1), (Sum.inr 4328, 4), (Sum.inr 4334, 4), (Sum.inr 4336, 4), (Sum.inr 4665, 4), (Sum.inr 4667, 4), (Sum.inr 4669, 4), (Sum.inr 4671, 4), (Sum.inr 4687, 4), (Sum.inr 4756, 4), (Sum.inr 4773, 4), (Sum.inr 4776, 4), (Sum.inr 4803, 4), (Sum.inr 4808, 4), (Sum.inr 5232, 4), (Sum.inr 5243, 4), (Sum.inr 5264, 4), (Sum.inr 5266, 4)]

def numericRow1859 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 5, -60), (Sum.inl 2, 155), (Sum.inl 7, 80), (Sum.inl 35, 80), (Sum.inl 3, 80), (Sum.inl 13, 80), (Sum.inl 54, -240), (Sum.inl 1, 125), (Sum.inr 1330, 1440), (Sum.inr 1332, 1440), (Sum.inr 1334, 1440), (Sum.inr 1793, 1440), (Sum.inr 1797, 1440), (Sum.inr 1813, 1440), (Sum.inr 2092, 1440), (Sum.inr 2800, 1440), (Sum.inr 2803, 1440), (Sum.inr 2816, 1440), (Sum.inr 3030, 1440), (Sum.inr 3039, 1440), (Sum.inr 3040, 1440), (Sum.inr 3045, 1440), (Sum.inr 3134, 1440), (Sum.inr 3163, 1440), (Sum.inr 3202, 1440)]

def numericRow1860 : Integer.Sparse Master := [(Sum.inr 1667, 1), (Sum.inr 1679, 1), (Sum.inr 1681, 1), (Sum.inr 1685, 1), (Sum.inr 1738, 1), (Sum.inr 2144, 1), (Sum.inr 2155, 1), (Sum.inr 2157, 1), (Sum.inr 2160, 1), (Sum.inr 2161, 1), (Sum.inr 2162, 1), (Sum.inr 2176, 1), (Sum.inr 2177, 1), (Sum.inr 2190, 1), (Sum.inr 2194, 1), (Sum.inr 2195, 1), (Sum.inr 2203, 1), (Sum.inr 2212, 1), (Sum.inr 2215, 1), (Sum.inr 2216, 1), (Sum.inr 2220, 1), (Sum.inr 2276, 1), (Sum.inr 2278, 1), (Sum.inr 2677, 1), (Sum.inr 2697, 1), (Sum.inr 2722, 1), (Sum.inr 2729, 1), (Sum.inr 2731, 1)]

def numericRow1861 : Integer.Sparse Master := [(Sum.inr 1791, 1), (Sum.inr 1795, 1), (Sum.inr 1797, 1), (Sum.inr 1814, 1), (Sum.inr 2028, 1), (Sum.inr 3379, 1), (Sum.inr 4084, -1)]

def numericRow1862 : Integer.Sparse Master := [(Sum.inr 932, 1), (Sum.inr 1814, 1), (Sum.inr 1966, 1), (Sum.inr 2028, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

def numericRow1863 : Integer.Sparse Master := [(Sum.inr 906, 1), (Sum.inr 1791, 1), (Sum.inr 1974, 1), (Sum.inr 2019, 1), (Sum.inr 2021, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

def numericRow1864 : Integer.Sparse Master := [(Sum.inl 0, 198), (Sum.inl 5, 60), (Sum.inl 2, 30), (Sum.inl 7, 240), (Sum.inl 3, 960), (Sum.inl 23, -720), (Sum.inl 12, 720), (Sum.inl 27, -180), (Sum.inl 1, -120), (Sum.inr 703, -12960), (Sum.inr 706, -12960), (Sum.inr 708, -12960), (Sum.inr 724, -12960), (Sum.inr 754, -12960), (Sum.inr 755, -12960), (Sum.inr 758, -12960), (Sum.inr 764, -12960), (Sum.inr 789, -12960), (Sum.inr 823, -12960), (Sum.inr 1763, -12960), (Sum.inr 1765, -12960), (Sum.inr 1767, -12960), (Sum.inr 1781, -12960), (Sum.inr 1784, -12960), (Sum.inr 1804, -12960), (Sum.inr 1842, -12960), (Sum.inr 1843, -12960), (Sum.inr 1846, -12960), (Sum.inr 1851, -12960), (Sum.inr 1861, -12960), (Sum.inr 1870, -12960), (Sum.inr 1884, -12960), (Sum.inr 1886, -12960), (Sum.inr 1889, -12960), (Sum.inr 1900, -12960), (Sum.inr 1921, -12960), (Sum.inr 1966, -12960), (Sum.inr 1970, -12960), (Sum.inr 2016, -12960), (Sum.inr 2018, -25920), (Sum.inr 2023, -12960), (Sum.inr 2025, -12960), (Sum.inr 2028, -12960), (Sum.inr 2048, -12960), (Sum.inr 2058, -12960), (Sum.inr 2075, -12960), (Sum.inr 2082, -12960), (Sum.inr 2106, -12960), (Sum.inr 2143, -12960), (Sum.inr 2177, -12960), (Sum.inr 2186, -12960), (Sum.inr 2214, -12960), (Sum.inr 2215, -12960), (Sum.inr 2216, -12960), (Sum.inr 2224, -12960), (Sum.inr 2242, -12960), (Sum.inr 2245, -12960), (Sum.inr 2277, -12960), (Sum.inr 3693, -12960), (Sum.inr 3719, -12960), (Sum.inr 3770, -12960), (Sum.inr 3795, -12960), (Sum.inr 3850, -25920), (Sum.inr 3891, -12960), (Sum.inr 3906, -12960)]

def numericRow1865 : Integer.Sparse Master := [(Sum.inr 933, -1), (Sum.inr 1050, -1), (Sum.inr 1691, -1), (Sum.inr 1751, -1), (Sum.inr 1815, -1), (Sum.inr 1967, -1), (Sum.inr 2020, -2), (Sum.inr 2025, -2), (Sum.inr 2029, -1), (Sum.inr 2116, -1), (Sum.inr 2166, -1), (Sum.inr 2183, -1), (Sum.inr 2202, -2), (Sum.inr 2224, -2), (Sum.inr 2225, -1), (Sum.inr 2288, -1), (Sum.inr 2739, -2), (Sum.inr 3534, -2), (Sum.inr 4335, 8), (Sum.inr 4666, 4), (Sum.inr 4670, 8), (Sum.inr 4757, 8), (Sum.inr 4774, 4), (Sum.inr 4777, 8), (Sum.inr 5236, 4), (Sum.inr 5269, 4)]

def numericRow1866 : Integer.Sparse Master := [(Sum.inl 0, -196), (Sum.inl 5, -160), (Sum.inl 2, -160), (Sum.inl 8, 160), (Sum.inl 56, -480), (Sum.inl 1, -220), (Sum.inr 1333, 4320), (Sum.inr 2323, 4320), (Sum.inr 2327, 4320), (Sum.inr 2340, 4320), (Sum.inr 3108, 2160), (Sum.inr 3115, 2160), (Sum.inr 3135, 2160), (Sum.inr 3164, 2160)]

def numericRow1867 : Integer.Sparse Master := [(Sum.inr 1689, 2), (Sum.inr 1691, 1), (Sum.inr 1751, 1), (Sum.inr 2148, 1), (Sum.inr 2164, 2), (Sum.inr 2166, 1), (Sum.inr 2181, 2), (Sum.inr 2183, 1), (Sum.inr 2199, 1), (Sum.inr 2202, 2), (Sum.inr 2223, 2), (Sum.inr 2224, 2), (Sum.inr 2225, 1), (Sum.inr 2288, 1), (Sum.inr 2682, 1), (Sum.inr 2736, 1), (Sum.inr 2739, 2)]

def numericRow1868 : Integer.Sparse Master := [(Sum.inr 1792, 1), (Sum.inr 1796, 2), (Sum.inr 1815, 1), (Sum.inr 2029, 1), (Sum.inr 3380, 1), (Sum.inr 4083, -1)]

def numericRow1869 : Integer.Sparse Master := [(Sum.inr 933, 1), (Sum.inr 1815, 1), (Sum.inr 1967, 1), (Sum.inr 2029, 1), (Sum.inr 4083, -1)]

def numericRow1870 : Integer.Sparse Master := [(Sum.inr 1792, 1), (Sum.inr 1975, 1), (Sum.inr 2020, 2), (Sum.inr 2029, 1), (Sum.inr 4083, -1)]

def numericRow1871 : Integer.Sparse Master := [(Sum.inl 0, 216), (Sum.inl 5, 30), (Sum.inl 2, 75), (Sum.inl 8, 120), (Sum.inl 3, 240), (Sum.inl 24, -360), (Sum.inl 4, 240), (Sum.inl 27, -90), (Sum.inl 1, -165), (Sum.inr 704, -6480), (Sum.inr 707, -12960), (Sum.inr 725, -6480), (Sum.inr 761, -6480), (Sum.inr 763, -12960), (Sum.inr 771, -6480), (Sum.inr 790, -6480), (Sum.inr 848, -6480), (Sum.inr 1764, -6480), (Sum.inr 1766, -12960), (Sum.inr 1782, -6480), (Sum.inr 1848, -6480), (Sum.inr 1850, -12960), (Sum.inr 1855, -6480), (Sum.inr 1860, -12960), (Sum.inr 1871, -6480), (Sum.inr 1888, -12960), (Sum.inr 1892, -6480), (Sum.inr 1901, -6480), (Sum.inr 1941, -6480), (Sum.inr 1967, -6480), (Sum.inr 1969, -12960), (Sum.inr 2020, -12960), (Sum.inr 2022, -12960), (Sum.inr 2029, -6480), (Sum.inr 2054, -12960), (Sum.inr 2183, -6480), (Sum.inr 2185, -12960), (Sum.inr 2202, -12960), (Sum.inr 2203, -12960), (Sum.inr 2206, -12960), (Sum.inr 2225, -6480), (Sum.inr 2244, -12960), (Sum.inr 2262, -12960), (Sum.inr 3694, -6480), (Sum.inr 3773, -6480), (Sum.inr 3779, -6480), (Sum.inr 3797, -6480), (Sum.inr 3898, -6480), (Sum.inr 3903, -12960)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1872 : Integer.Sparse Master := [(Sum.inl 0, 6), (Sum.inl 5, -5), (Sum.inl 8, -20), (Sum.inl 1, -5), (Sum.inr 1000, -1080), (Sum.inr 1605, -1080), (Sum.inr 1901, -540), (Sum.inr 1929, -540), (Sum.inr 1941, -540), (Sum.inr 1949, -540), (Sum.inr 1990, -1080), (Sum.inr 1997, -1080), (Sum.inr 2028, -1080), (Sum.inr 2029, -540), (Sum.inr 2116, -540), (Sum.inr 2215, -1080), (Sum.inr 2225, -540), (Sum.inr 2288, -540), (Sum.inr 2489, -540), (Sum.inr 2931, -1080), (Sum.inr 3482, -540), (Sum.inr 3612, -1080), (Sum.inr 3616, -540), (Sum.inr 4427, 2160), (Sum.inr 4487, 2160), (Sum.inr 4785, 2160), (Sum.inr 4795, 4320), (Sum.inr 4821, 4320), (Sum.inr 4825, 2160), (Sum.inr 4856, 4320)]

def numericRow1873 : Integer.Sparse Master := [(Sum.inr 937, -1), (Sum.inr 1094, -1), (Sum.inr 1683, -1), (Sum.inr 1741, -1), (Sum.inr 1804, -2), (Sum.inr 1817, -1), (Sum.inr 2052, -2), (Sum.inr 2065, -2), (Sum.inr 2143, -2), (Sum.inr 2159, -1), (Sum.inr 2193, -2), (Sum.inr 2218, -2), (Sum.inr 2281, -1), (Sum.inr 2294, -1), (Sum.inr 2726, -1), (Sum.inr 3545, -1), (Sum.inr 4348, 8), (Sum.inr 4362, 4), (Sum.inr 4683, 8), (Sum.inr 4694, 4), (Sum.inr 4702, 8), (Sum.inr 4762, 8), (Sum.inr 4836, 8), (Sum.inr 4844, 4), (Sum.inr 5222, 8), (Sum.inr 5235, 4), (Sum.inr 5268, 4)]

def numericRow1874 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 5, -40), (Sum.inl 2, -550), (Sum.inl 35, -160), (Sum.inl 13, -160), (Sum.inl 1, -20), (Sum.inr 1347, 2880), (Sum.inr 1348, 1440), (Sum.inr 1828, 2880), (Sum.inr 1832, 1440), (Sum.inr 2136, 1440), (Sum.inr 2716, 2880), (Sum.inr 2734, 1440), (Sum.inr 3031, 2880), (Sum.inr 3033, 2880), (Sum.inr 3046, 1440), (Sum.inr 3062, 2880)]

def numericRow1875 : Integer.Sparse Master := [(Sum.inr 1669, 2), (Sum.inr 1683, 1), (Sum.inr 1687, 1), (Sum.inr 1741, 1), (Sum.inr 2143, 2), (Sum.inr 2146, 2), (Sum.inr 2159, 1), (Sum.inr 2163, 1), (Sum.inr 2171, 2), (Sum.inr 2180, 2), (Sum.inr 2193, 2), (Sum.inr 2197, 2), (Sum.inr 2218, 2), (Sum.inr 2222, 1), (Sum.inr 2281, 1), (Sum.inr 2664, 2), (Sum.inr 2680, 1), (Sum.inr 2726, 1), (Sum.inr 2734, 1)]

def numericRow1876 : Integer.Sparse Master := [(Sum.inr 1809, 2), (Sum.inr 1817, 1), (Sum.inr 1820, 1), (Sum.inr 2065, 1), (Sum.inr 3396, 1), (Sum.inr 4085, -1)]

def numericRow1877 : Integer.Sparse Master := [(Sum.inr 927, -2), (Sum.inr 938, -1), (Sum.inr 939, -1), (Sum.inr 1675, -2), (Sum.inr 1693, -1), (Sum.inr 1694, -1), (Sum.inr 1810, -2), (Sum.inr 1818, -1), (Sum.inr 1819, -1), (Sum.inr 1963, -2), (Sum.inr 1969, -2), (Sum.inr 1970, -2), (Sum.inr 2054, -2), (Sum.inr 2062, -1), (Sum.inr 2152, -2), (Sum.inr 2168, -1), (Sum.inr 2169, -1), (Sum.inr 2174, -2), (Sum.inr 2185, -2), (Sum.inr 2186, -2), (Sum.inr 2206, -2), (Sum.inr 2230, -1), (Sum.inr 2686, -1), (Sum.inr 2705, -2), (Sum.inr 2743, -1), (Sum.inr 3397, -1), (Sum.inr 3498, -2), (Sum.inr 3548, -1), (Sum.inr 4084, 4)]

def numericRow1878 : Integer.Sparse Master := [(Sum.inr 1675, 2), (Sum.inr 1693, 1), (Sum.inr 1694, 1), (Sum.inr 2152, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2174, 2), (Sum.inr 2185, 2), (Sum.inr 2186, 2), (Sum.inr 2206, 2), (Sum.inr 2230, 1), (Sum.inr 2686, 1), (Sum.inr 2705, 2), (Sum.inr 2743, 1), (Sum.inr 4084, 1)]

def numericRow1879 : Integer.Sparse Master := [(Sum.inr 1810, 2), (Sum.inr 1818, 1), (Sum.inr 1819, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

def numericRow1880 : Integer.Sparse Master := [(Sum.inr 866, -1), (Sum.inr 873, -1), (Sum.inr 874, -1), (Sum.inr 985, -1), (Sum.inr 1554, -1), (Sum.inr 1569, -1), (Sum.inr 1570, -1), (Sum.inr 1618, -1), (Sum.inr 1761, -1), (Sum.inr 1766, -1), (Sum.inr 1767, -1), (Sum.inr 1837, -1), (Sum.inr 1850, -1), (Sum.inr 1851, -1), (Sum.inr 1860, -1), (Sum.inr 1861, -1), (Sum.inr 1876, -1), (Sum.inr 1880, -1), (Sum.inr 1881, -1), (Sum.inr 1888, -1), (Sum.inr 1889, -1), (Sum.inr 1906, -1), (Sum.inr 1909, -2), (Sum.inr 1915, -1), (Sum.inr 1938, -1), (Sum.inr 1939, -1), (Sum.inr 1946, -1), (Sum.inr 1990, -1), (Sum.inr 1997, -1), (Sum.inr 2048, -1), (Sum.inr 2054, -1), (Sum.inr 2082, -1), (Sum.inr 2206, -1), (Sum.inr 2400, -1), (Sum.inr 2459, -1), (Sum.inr 2505, -1), (Sum.inr 2512, -1), (Sum.inr 3344, -1), (Sum.inr 3429, -1), (Sum.inr 3448, -1), (Sum.inr 3471, -1), (Sum.inr 4080, 4)]

def numericRow1881 : Integer.Sparse Master := [(Sum.inr 876, -1), (Sum.inr 881, -1), (Sum.inr 891, -1), (Sum.inr 1000, -1), (Sum.inr 1552, -1), (Sum.inr 1559, -1), (Sum.inr 1565, -1), (Sum.inr 1605, -1), (Sum.inr 1769, -1), (Sum.inr 1773, -1), (Sum.inr 1781, -1), (Sum.inr 1835, -1), (Sum.inr 1841, -1), (Sum.inr 1846, -1), (Sum.inr 1863, -1), (Sum.inr 1870, -1), (Sum.inr 1883, -1), (Sum.inr 1886, -1), (Sum.inr 1900, -1), (Sum.inr 1901, -1), (Sum.inr 1917, -1), (Sum.inr 1921, -1), (Sum.inr 1924, -1), (Sum.inr 1928, -2), (Sum.inr 1929, -1), (Sum.inr 1941, -1), (Sum.inr 1949, -1), (Sum.inr 1990, -1), (Sum.inr 1997, -1), (Sum.inr 2028, -1), (Sum.inr 2029, -1), (Sum.inr 2215, -1), (Sum.inr 2225, -1), (Sum.inr 2388, -1), (Sum.inr 2452, -1), (Sum.inr 2488, -1), (Sum.inr 2489, -1), (Sum.inr 3354, -1), (Sum.inr 3433, -1), (Sum.inr 3478, -1), (Sum.inr 3482, -1), (Sum.inr 4082, 4)]

def numericRow1882 : Integer.Sparse Master := [(Sum.inr 4065, 2), (Sum.inr 4067, 2), (Sum.inr 4071, 1), (Sum.inr 4074, 4), (Sum.inr 4075, 2), (Sum.inr 4076, 2), (Sum.inr 4078, 2), (Sum.inr 4080, 4), (Sum.inr 4081, 2), (Sum.inr 4082, 2), (Sum.inr 4084, 2), (Sum.inr 4088, 2), (Sum.inr 4089, 1), (Sum.inr 4092, 2)]

def numericRow1883 : Integer.Sparse Master := [(Sum.inr 923, 1), (Sum.inr 1806, 1), (Sum.inr 2021, 1), (Sum.inr 2034, 1), (Sum.inr 2051, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

def numericRow1884 : Integer.Sparse Master := [(Sum.inr 2440, 1), (Sum.inr 3062, 1), (Sum.inr 3189, 1), (Sum.inr 3202, 2), (Sum.inr 3789, 1), (Sum.inr 4091, -1)]

def numericRow1885 : Integer.Sparse Master := [(Sum.inr 1803, 1), (Sum.inr 2033, 1), (Sum.inr 2051, 1), (Sum.inr 2054, 2), (Sum.inr 4084, -1)]

def numericRow1886 : Integer.Sparse Master := [(Sum.inr 2895, 1), (Sum.inr 3164, 2), (Sum.inr 3172, 1), (Sum.inr 3197, 1), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

def numericRow1887 : Integer.Sparse Master := [(Sum.inr 2430, 1), (Sum.inr 3162, 1), (Sum.inr 3163, 1), (Sum.inr 3170, 1), (Sum.inr 3196, 1), (Sum.inr 3782, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1888 : Integer.Sparse Master := [(Sum.inr 2443, 1), (Sum.inr 3033, 1), (Sum.inr 3136, 1), (Sum.inr 3138, 1), (Sum.inr 3180, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

def numericRow1889 : Integer.Sparse Master := [(Sum.inr 942, 1), (Sum.inr 1822, 1), (Sum.inr 2088, 1), (Sum.inr 2105, 1), (Sum.inr 2107, 2), (Sum.inr 4083, -1)]

def numericRow1890 : Integer.Sparse Master := [(Sum.inr 2890, 1), (Sum.inr 3135, 2), (Sum.inr 3137, 1), (Sum.inr 3172, 1), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

def numericRow1891 : Integer.Sparse Master := [(Sum.inr 944, 1), (Sum.inr 1824, 1), (Sum.inr 2089, 2), (Sum.inr 2105, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

def numericRow1892 : Integer.Sparse Master := [(Sum.inr 2423, 1), (Sum.inr 3133, 1), (Sum.inr 3134, 1), (Sum.inr 3136, 1), (Sum.inr 3170, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

def numericRow1893 : Integer.Sparse Master := [(Sum.inr 2899, 1), (Sum.inr 3128, 1), (Sum.inr 3132, 2), (Sum.inr 3158, 1), (Sum.inr 3394, 1), (Sum.inr 4083, -1)]

def numericRow1894 : Integer.Sparse Master := [(Sum.inr 2435, 1), (Sum.inr 3127, 1), (Sum.inr 3129, 1), (Sum.inr 3131, 1), (Sum.inr 3156, 1), (Sum.inr 3391, 1), (Sum.inr 4084, -1)]

def numericRow1895 : Integer.Sparse Master := [(Sum.inr 1130, 1), (Sum.inr 2333, 1), (Sum.inr 2481, 1), (Sum.inr 2494, 1), (Sum.inr 2508, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

def numericRow1896 : Integer.Sparse Master := [(Sum.inr 2437, 1), (Sum.inr 2900, 1), (Sum.inr 2902, 1), (Sum.inr 2954, 1), (Sum.inr 2984, 1), (Sum.inr 3787, 1), (Sum.inr 4091, -1)]

def numericRow1897 : Integer.Sparse Master := [(Sum.inr 1127, 1), (Sum.inr 2493, 1), (Sum.inr 2508, 1), (Sum.inr 2512, 2), (Sum.inr 4092, -1)]

def numericRow1898 : Integer.Sparse Master := [(Sum.inr 2847, 1), (Sum.inr 2849, 2), (Sum.inr 2884, 1), (Sum.inr 2976, 1), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

def numericRow1899 : Integer.Sparse Master := [(Sum.inr 2426, 1), (Sum.inr 2846, 1), (Sum.inr 2848, 1), (Sum.inr 2881, 1), (Sum.inr 2974, 1), (Sum.inr 3781, 1), (Sum.inr 4092, -1)]

def numericRow1900 : Integer.Sparse Master := [(Sum.inr 1960, 1), (Sum.inr 2427, 2), (Sum.inr 2509, 1), (Sum.inr 3493, 1), (Sum.inr 4084, -1)]

def numericRow1901 : Integer.Sparse Master := [(Sum.inr 2426, 1), (Sum.inr 2428, 1), (Sum.inr 2433, 1), (Sum.inr 2512, 1), (Sum.inr 3781, 1), (Sum.inr 4092, -1)]

def numericRow1902 : Integer.Sparse Master := [(Sum.inr 2430, 1), (Sum.inr 2431, 1), (Sum.inr 2433, 1), (Sum.inr 2515, 1), (Sum.inr 2557, 1), (Sum.inr 3782, 1), (Sum.inr 4092, -1)]

def numericRow1903 : Integer.Sparse Master := [(Sum.inr 1335, 1), (Sum.inr 2826, 1), (Sum.inr 2924, 1), (Sum.inr 2933, 1), (Sum.inr 2951, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1904 : Integer.Sparse Master := [(Sum.inl 0, 106), (Sum.inl 6, 5), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, 530), (Sum.inr 1135, -1080), (Sum.inr 1136, -1080), (Sum.inr 1138, -2160), (Sum.inr 2814, -1080), (Sum.inr 2815, -1080), (Sum.inr 2817, -2160), (Sum.inr 2896, -2160), (Sum.inr 2954, -2160), (Sum.inr 3269, -1080), (Sum.inr 3270, -2160), (Sum.inr 3273, -1080), (Sum.inr 3308, -1080), (Sum.inr 3585, -1080), (Sum.inr 3588, -1080), (Sum.inr 3591, -2160), (Sum.inr 3597, -2160), (Sum.inr 3603, -3240), (Sum.inr 3606, -2160), (Sum.inr 3608, -2160), (Sum.inr 3614, -2160), (Sum.inr 3623, -1080), (Sum.inr 3891, -1080), (Sum.inr 3895, -1080), (Sum.inr 3902, -1080)]

def numericRow1905 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 6, -5), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, -530), (Sum.inr 1135, 1080), (Sum.inr 1136, 1080), (Sum.inr 1138, 2160), (Sum.inr 2814, 1080), (Sum.inr 2815, 1080), (Sum.inr 2817, 2160), (Sum.inr 2896, 2160), (Sum.inr 2954, 2160)]

def numericRow1906 : Integer.Sparse Master := [(Sum.inl 0, 38), (Sum.inl 6, 1), (Sum.inl 2, 1), (Sum.inl 7, -16), (Sum.inl 3, -16), (Sum.inl 1, -26), (Sum.inr 919, -432), (Sum.inr 921, -432), (Sum.inr 927, -864), (Sum.inr 1040, -432), (Sum.inr 1664, -432), (Sum.inr 1666, -432), (Sum.inr 1675, -864), (Sum.inr 1707, -432), (Sum.inr 1960, -432), (Sum.inr 1969, -432), (Sum.inr 2022, -864), (Sum.inr 2173, -432), (Sum.inr 2185, -432), (Sum.inr 2203, -864), (Sum.inr 2330, -432), (Sum.inr 2337, -864), (Sum.inr 2428, -864), (Sum.inr 2479, -432), (Sum.inr 2553, -864), (Sum.inr 2561, -864), (Sum.inr 2722, -864), (Sum.inr 3404, -432), (Sum.inr 3412, -864), (Sum.inr 3450, -864), (Sum.inr 3459, -432), (Sum.inr 3514, -864), (Sum.inr 3522, -864), (Sum.inr 3533, -864), (Sum.inr 3602, -432), (Sum.inr 3607, -864), (Sum.inr 3622, -432), (Sum.inr 3896, -432), (Sum.inr 3898, -432), (Sum.inr 3903, -864)]

def numericRow1907 : Integer.Sparse Master := [(Sum.inl 0, -38), (Sum.inl 6, -1), (Sum.inl 2, -1), (Sum.inl 7, 16), (Sum.inl 3, 16), (Sum.inl 1, 26), (Sum.inr 919, 432), (Sum.inr 921, 432), (Sum.inr 927, 864), (Sum.inr 1040, 432), (Sum.inr 1960, 432), (Sum.inr 1969, 432), (Sum.inr 2022, 864), (Sum.inr 2330, 432), (Sum.inr 2337, 864), (Sum.inr 2428, 864), (Sum.inr 2479, 432), (Sum.inr 2553, 864), (Sum.inr 2561, 864), (Sum.inr 2722, 864)]

def numericRow1908 : Integer.Sparse Master := [(Sum.inl 0, 133), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 8, -80), (Sum.inl 1, -160), (Sum.inr 1129, -1080), (Sum.inr 1131, -1080), (Sum.inr 1134, -1080), (Sum.inr 1139, -1080), (Sum.inr 2429, -1080), (Sum.inr 2434, -1080), (Sum.inr 2485, -1080), (Sum.inr 2809, -1080), (Sum.inr 2813, -1080), (Sum.inr 2818, -1080), (Sum.inr 2893, -1080), (Sum.inr 2931, -1080), (Sum.inr 3263, -1080), (Sum.inr 3264, -1080), (Sum.inr 3265, -1080), (Sum.inr 3274, -1080), (Sum.inr 3309, -1080), (Sum.inr 3455, -1080), (Sum.inr 3457, -1080), (Sum.inr 3481, -1080), (Sum.inr 3587, -1080), (Sum.inr 3592, -1080), (Sum.inr 3595, -1080), (Sum.inr 3599, -1080), (Sum.inr 3602, -1080), (Sum.inr 3607, -3240), (Sum.inr 3612, -1080), (Sum.inr 3613, -1080), (Sum.inr 3615, -1080), (Sum.inr 3616, -1080), (Sum.inr 3627, -1080), (Sum.inr 3892, -1080), (Sum.inr 3896, -1080), (Sum.inr 3903, -1080)]

def numericRow1909 : Integer.Sparse Master := [(Sum.inl 0, -133), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 8, 80), (Sum.inl 1, 160), (Sum.inr 1129, 1080), (Sum.inr 1131, 1080), (Sum.inr 1134, 1080), (Sum.inr 1139, 1080), (Sum.inr 2429, 1080), (Sum.inr 2434, 1080), (Sum.inr 2485, 1080), (Sum.inr 2809, 1080), (Sum.inr 2813, 1080), (Sum.inr 2818, 1080), (Sum.inr 2893, 1080), (Sum.inr 2931, 1080)]

def numericRow1910 : Integer.Sparse Master := [(Sum.inl 0, 181), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 8, -80), (Sum.inl 1, 80), (Sum.inr 922, -1440), (Sum.inr 924, -1440), (Sum.inr 927, -1440), (Sum.inr 933, -1440), (Sum.inr 1041, -1440), (Sum.inr 1673, -1440), (Sum.inr 1674, -1440), (Sum.inr 1675, -1440), (Sum.inr 1691, -1440), (Sum.inr 1724, -1440), (Sum.inr 2332, -1440), (Sum.inr 2334, -1440), (Sum.inr 2337, -1440), (Sum.inr 2342, -1440), (Sum.inr 2425, -1440), (Sum.inr 2428, -1440), (Sum.inr 2432, -1440), (Sum.inr 2480, -1440), (Sum.inr 2482, -1440), (Sum.inr 2556, -1440), (Sum.inr 2561, -1440), (Sum.inr 2723, -1440), (Sum.inr 3410, -1440), (Sum.inr 3411, -1440), (Sum.inr 3412, -1440), (Sum.inr 3421, -1440), (Sum.inr 3449, -1440), (Sum.inr 3450, -1440), (Sum.inr 3456, -1440), (Sum.inr 3467, -1440), (Sum.inr 3468, -1440), (Sum.inr 3521, -1440), (Sum.inr 3522, -1440), (Sum.inr 3544, -1440), (Sum.inr 3602, -1440), (Sum.inr 3603, -1440), (Sum.inr 3607, -2880), (Sum.inr 3608, -1440), (Sum.inr 3616, -1440), (Sum.inr 3622, -1440), (Sum.inr 3627, -1440), (Sum.inr 4042, -1440), (Sum.inr 4045, -1440), (Sum.inr 4047, -1440)]

def numericRow1911 : Integer.Sparse Master := [(Sum.inl 0, -181), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 8, 80), (Sum.inl 1, -80), (Sum.inr 922, 1440), (Sum.inr 924, 1440), (Sum.inr 927, 1440), (Sum.inr 933, 1440), (Sum.inr 1041, 1440), (Sum.inr 2332, 1440), (Sum.inr 2334, 1440), (Sum.inr 2337, 1440), (Sum.inr 2342, 1440), (Sum.inr 2425, 1440), (Sum.inr 2428, 1440), (Sum.inr 2432, 1440), (Sum.inr 2480, 1440), (Sum.inr 2482, 1440), (Sum.inr 2556, 1440), (Sum.inr 2561, 1440), (Sum.inr 2723, 1440)]

def numericRow1912 : Integer.Sparse Master := [(Sum.inr 2485, -1), (Sum.inr 2924, -1), (Sum.inr 2931, -1), (Sum.inr 3077, -1), (Sum.inr 3481, -1), (Sum.inr 3605, -1), (Sum.inr 3612, -1), (Sum.inr 3625, -1), (Sum.inr 3787, -1), (Sum.inr 3790, -1), (Sum.inr 3804, -1), (Sum.inr 3815, -1), (Sum.inr 3857, -1), (Sum.inr 3876, -1), (Sum.inr 3983, -2), (Sum.inr 4345, 4), (Sum.inr 4347, 4), (Sum.inr 4348, 4), (Sum.inr 4357, 4), (Sum.inr 4459, 4), (Sum.inr 4942, 4), (Sum.inr 4944, 4), (Sum.inr 4945, 4), (Sum.inr 4951, 4), (Sum.inr 5034, 4), (Sum.inr 5035, 4), (Sum.inr 5040, 4), (Sum.inr 5074, 4), (Sum.inr 5138, 4), (Sum.inr 5139, 4), (Sum.inr 5140, 4), (Sum.inr 5160, 4), (Sum.inr 5161, 4), (Sum.inr 5164, 4), (Sum.inr 5260, 4), (Sum.inr 5289, 4)]

def numericRow1913 : Integer.Sparse Master := [(Sum.inr 1668, 1), (Sum.inr 1669, 1), (Sum.inr 1676, 1), (Sum.inr 1682, 1), (Sum.inr 1714, 1), (Sum.inr 2652, 1), (Sum.inr 2658, 1), (Sum.inr 2670, 1), (Sum.inr 2719, 1), (Sum.inr 3407, 1), (Sum.inr 3413, 1), (Sum.inr 3418, 1), (Sum.inr 3451, 1), (Sum.inr 3454, 1), (Sum.inr 3463, 1), (Sum.inr 3481, 1), (Sum.inr 3517, 1), (Sum.inr 3523, 1), (Sum.inr 3540, 1), (Sum.inr 3558, 1), (Sum.inr 3565, 1), (Sum.inr 3572, 1), (Sum.inr 3605, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3804, 1), (Sum.inr 3815, 1), (Sum.inr 3857, 1), (Sum.inr 3983, 1)]

def numericRow1914 : Integer.Sparse Master := [(Sum.inl 0, 143), (Sum.inl 6, 5), (Sum.inl 2, -50), (Sum.inl 7, -80), (Sum.inl 3, -160), (Sum.inl 1, -110), (Sum.inr 1126, -1440), (Sum.inr 1128, -1440), (Sum.inr 1134, -2880), (Sum.inr 1964, -1440), (Sum.inr 1970, -1440), (Sum.inr 2025, -2880), (Sum.inr 2182, -1440), (Sum.inr 2184, -1440), (Sum.inr 2186, -1440), (Sum.inr 2224, -2880), (Sum.inr 2807, -1440), (Sum.inr 2813, -2880), (Sum.inr 2893, -2880), (Sum.inr 2924, -2880), (Sum.inr 2931, -2880), (Sum.inr 3256, -1440), (Sum.inr 3265, -2880), (Sum.inr 3308, -1440), (Sum.inr 3590, -1440), (Sum.inr 3595, -2880), (Sum.inr 3599, -2880), (Sum.inr 3602, -1440), (Sum.inr 3605, -2880), (Sum.inr 3607, -2880), (Sum.inr 3612, -2880), (Sum.inr 3613, -1440), (Sum.inr 3632, -2880), (Sum.inr 3891, -1440), (Sum.inr 3897, -1440), (Sum.inr 3906, -2880)]

def numericRow1915 : Integer.Sparse Master := [(Sum.inl 0, -143), (Sum.inl 6, -5), (Sum.inl 2, 50), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 1, 110), (Sum.inr 1126, 1440), (Sum.inr 1128, 1440), (Sum.inr 1134, 2880), (Sum.inr 1964, 1440), (Sum.inr 1970, 1440), (Sum.inr 2025, 2880), (Sum.inr 2807, 1440), (Sum.inr 2813, 2880), (Sum.inr 2893, 2880), (Sum.inr 2924, 2880), (Sum.inr 2931, 2880)]

def numericRow1916 : Integer.Sparse Master := [(Sum.inl 0, 143), (Sum.inl 6, 5), (Sum.inl 2, -50), (Sum.inl 7, -80), (Sum.inl 3, -160), (Sum.inl 1, -110), (Sum.inr 929, -1440), (Sum.inr 930, -1440), (Sum.inr 932, -2880), (Sum.inr 1044, -1440), (Sum.inr 1680, -1440), (Sum.inr 1681, -2880), (Sum.inr 1690, -1440), (Sum.inr 1737, -1440), (Sum.inr 2338, -1440), (Sum.inr 2339, -1440), (Sum.inr 2341, -2880), (Sum.inr 2429, -1440), (Sum.inr 2431, -2880), (Sum.inr 2483, -1440), (Sum.inr 2589, -1440), (Sum.inr 2590, -2880), (Sum.inr 2764, -1440), (Sum.inr 3416, -1440), (Sum.inr 3417, -2880), (Sum.inr 3420, -1440), (Sum.inr 3453, -2880), (Sum.inr 3455, -1440), (Sum.inr 3477, -1440), (Sum.inr 3563, -1440), (Sum.inr 3564, -2880), (Sum.inr 3581, -1440), (Sum.inr 3613, -2880), (Sum.inr 3614, -2880), (Sum.inr 3615, -2880), (Sum.inr 3632, -2880), (Sum.inr 3896, -1440), (Sum.inr 3898, -1440), (Sum.inr 4010, -1440)]

def numericRow1917 : Integer.Sparse Master := [(Sum.inl 0, -143), (Sum.inl 6, -5), (Sum.inl 2, 50), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 1, 110), (Sum.inr 929, 1440), (Sum.inr 930, 1440), (Sum.inr 932, 2880), (Sum.inr 1044, 1440), (Sum.inr 2338, 1440), (Sum.inr 2339, 1440), (Sum.inr 2341, 2880), (Sum.inr 2429, 1440), (Sum.inr 2431, 2880), (Sum.inr 2483, 1440), (Sum.inr 2589, 1440), (Sum.inr 2590, 2880), (Sum.inr 2764, 1440)]

def numericRow1918 : Integer.Sparse Master := [(Sum.inl 0, 132), (Sum.inl 6, -15), (Sum.inl 2, 55), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 3, 80), (Sum.inl 1, 150), (Sum.inr 2023, -4320), (Sum.inr 2058, -8640), (Sum.inr 2110, -4320), (Sum.inr 2214, -4320), (Sum.inr 2216, -8640), (Sum.inr 2275, -4320), (Sum.inr 2479, -4320), (Sum.inr 2483, -4320), (Sum.inr 2509, -4320), (Sum.inr 2515, -8640), (Sum.inr 2556, -4320), (Sum.inr 2704, -4320), (Sum.inr 2881, -8640), (Sum.inr 2924, -8640), (Sum.inr 2954, -8640), (Sum.inr 3459, -4320), (Sum.inr 3477, -4320), (Sum.inr 3479, -8640), (Sum.inr 3521, -4320), (Sum.inr 3603, -4320), (Sum.inr 3605, -8640), (Sum.inr 3606, -8640), (Sum.inr 3607, -8640), (Sum.inr 3624, -8640), (Sum.inr 5138, 34560), (Sum.inr 5150, 17280), (Sum.inr 5173, 34560), (Sum.inr 5187, 17280), (Sum.inr 5205, 17280)]

def numericRow1919 : Integer.Sparse Master := [(Sum.inr 1156, 1), (Sum.inr 2353, 1), (Sum.inr 2553, 1), (Sum.inr 2566, 1), (Sum.inr 2587, 1), (Sum.inr 2590, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow192 : Integer.Sparse Master := [(Sum.inr 2513, 2), (Sum.inr 2520, 1), (Sum.inr 2522, 1), (Sum.inr 2744, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

def numericRow193 : Integer.Sparse Master := [(Sum.inr 1238, 1), (Sum.inr 2133, 1), (Sum.inr 2513, 1), (Sum.inr 2555, 1), (Sum.inr 2738, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

def numericRow194 : Integer.Sparse Master := [(Sum.inr 2555, 1), (Sum.inr 2559, 1), (Sum.inr 2560, 1), (Sum.inr 2592, 1), (Sum.inr 2744, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def numericRow195 : Integer.Sparse Master := [(Sum.inr 1245, 1), (Sum.inr 2522, 1), (Sum.inr 2560, 2), (Sum.inr 2740, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

def numericRow196 : Integer.Sparse Master := [(Sum.inr 2133, 2), (Sum.inr 2136, 1), (Sum.inr 2138, 1), (Sum.inr 2279, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

def numericRow197 : Integer.Sparse Master := [(Sum.inr 1244, 1), (Sum.inr 2136, 1), (Sum.inr 2520, 1), (Sum.inr 2559, 2), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

def numericRow198 : Integer.Sparse Master := [(Sum.inl 0, -26), (Sum.inl 2, 5), (Sum.inl 3, 160), (Sum.inl 13, 80), (Sum.inl 12, 160), (Sum.inl 1, -85), (Sum.inr 1006, 4320), (Sum.inr 1010, 2160), (Sum.inr 1011, 2160), (Sum.inr 1084, 2160), (Sum.inr 2405, 4320), (Sum.inr 2408, 2160), (Sum.inr 2409, 2160), (Sum.inr 2463, 4320), (Sum.inr 2465, 4320), (Sum.inr 2466, 4320), (Sum.inr 2513, 4320), (Sum.inr 2732, 4320), (Sum.inr 2734, 2160), (Sum.inr 2735, 4320), (Sum.inr 2737, 2160), (Sum.inr 2781, 2160), (Sum.inr 3573, 4320), (Sum.inr 3583, 2160), (Sum.inr 3584, 2160)]

def numericRow200 : Integer.Sparse Master := [(Sum.inr 2773, 2), (Sum.inr 2774, 1), (Sum.inr 2777, 1), (Sum.inr 2782, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

def numericRow201 : Integer.Sparse Master := [(Sum.inr 1282, 1), (Sum.inr 1422, 2), (Sum.inr 1424, 1), (Sum.inr 1436, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1920 : Integer.Sparse Master := [(Sum.inr 2895, 1), (Sum.inr 2896, 1), (Sum.inr 2898, 1), (Sum.inr 2928, 2), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

def numericRow1921 : Integer.Sparse Master := [(Sum.inr 1158, 1), (Sum.inr 2354, 1), (Sum.inr 2556, 1), (Sum.inr 2567, 2), (Sum.inr 2589, 1), (Sum.inr 4091, -1)]

def numericRow1922 : Integer.Sparse Master := [(Sum.inr 2847, 1), (Sum.inr 2893, 1), (Sum.inr 2898, 1), (Sum.inr 2925, 2), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

def numericRow1923 : Integer.Sparse Master := [(Sum.inr 2922, 1), (Sum.inr 3748, 1), (Sum.inr 3751, 1), (Sum.inr 3758, 1), (Sum.inr 3866, 1), (Sum.inr 3973, 1), (Sum.inr 4087, -1)]

def numericRow1924 : Integer.Sparse Master := [(Sum.inr 2429, -1), (Sum.inr 2485, -1), (Sum.inr 2893, -1), (Sum.inr 2896, -1), (Sum.inr 2924, -1), (Sum.inr 2931, -1), (Sum.inr 2954, -1), (Sum.inr 3077, -1), (Sum.inr 3455, -1), (Sum.inr 3481, -1), (Sum.inr 3597, -1), (Sum.inr 3599, -1), (Sum.inr 3605, -1), (Sum.inr 3606, -1), (Sum.inr 3612, -1), (Sum.inr 3625, -1), (Sum.inr 3779, -1), (Sum.inr 3797, -1), (Sum.inr 3838, -1), (Sum.inr 3843, -1), (Sum.inr 3974, -2), (Sum.inr 4327, 4), (Sum.inr 4328, 4), (Sum.inr 4332, 4), (Sum.inr 4345, 4), (Sum.inr 4439, 4), (Sum.inr 4930, 4), (Sum.inr 4931, 4), (Sum.inr 4933, 4), (Sum.inr 4942, 4), (Sum.inr 5128, 4), (Sum.inr 5129, 4), (Sum.inr 5138, 4), (Sum.inr 5144, 4), (Sum.inr 5145, 4), (Sum.inr 5160, 4), (Sum.inr 5251, 4), (Sum.inr 5281, 4)]

def numericRow1925 : Integer.Sparse Master := [(Sum.inl 0, -386), (Sum.inl 9, 200), (Sum.inl 58, -10), (Sum.inl 5, -400), (Sum.inl 6, -10), (Sum.inl 68, -600), (Sum.inl 2, 850), (Sum.inl 69, 480), (Sum.inl 70, 160), (Sum.inl 71, 320), (Sum.inl 7, 960), (Sum.inl 35, 320), (Sum.inl 8, 1280), (Sum.inl 124, -960), (Sum.inl 125, -480), (Sum.inl 126, -960), (Sum.inl 51, -960), (Sum.inl 3, 2720), (Sum.inl 13, 160), (Sum.inl 52, 320), (Sum.inl 23, -480), (Sum.inl 24, -960), (Sum.inl 12, 480), (Sum.inl 56, -480), (Sum.inl 26, 320), (Sum.inl 4, 1120), (Sum.inl 27, 240), (Sum.inl 1, -1420), (Sum.inl 30, -480), (Sum.inl 31, -480), (Sum.inr 905, 8640), (Sum.inr 906, 8640), (Sum.inr 910, 8640), (Sum.inr 923, 8640), (Sum.inr 1021, 8640), (Sum.inr 2320, 8640), (Sum.inr 2321, 8640), (Sum.inr 2324, 8640), (Sum.inr 2333, 8640), (Sum.inr 2543, 8640), (Sum.inr 2545, 8640), (Sum.inr 2557, 8640), (Sum.inr 2566, 8640), (Sum.inr 2567, 8640), (Sum.inr 2587, 8640), (Sum.inr 2710, 8640), (Sum.inr 2750, 8640)]

def numericRow1926 : Integer.Sparse Master := [(Sum.inr 1667, 1), (Sum.inr 1668, 1), (Sum.inr 1670, 1), (Sum.inr 1678, 1), (Sum.inr 1713, 1), (Sum.inr 3406, 1), (Sum.inr 3407, 1), (Sum.inr 3408, 1), (Sum.inr 3414, 1), (Sum.inr 3455, 1), (Sum.inr 3481, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3519, 1), (Sum.inr 3539, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3562, 1), (Sum.inr 3571, 1), (Sum.inr 3597, 1), (Sum.inr 3599, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3797, 1), (Sum.inr 3843, 1), (Sum.inr 3974, 1)]

def numericRow1927 : Integer.Sparse Master := [(Sum.inr 2422, 1), (Sum.inr 2822, 1), (Sum.inr 2824, 1), (Sum.inr 2826, 1), (Sum.inr 2924, 1), (Sum.inr 3779, 1), (Sum.inr 4091, -1)]

def numericRow1928 : Integer.Sparse Master := [(Sum.inr 1169, 1), (Sum.inr 2361, 1), (Sum.inr 2573, 3), (Sum.inr 2589, 1), (Sum.inr 4091, -1)]

def numericRow1929 : Integer.Sparse Master := [(Sum.inr 1964, 1), (Sum.inr 2892, 2), (Sum.inr 2923, 2), (Sum.inr 3496, 1), (Sum.inr 4083, -1)]

def numericRow1930 : Integer.Sparse Master := [(Sum.inr 2800, 1), (Sum.inr 2801, 2), (Sum.inr 2814, 1), (Sum.inr 2864, 1), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

def numericRow1931 : Integer.Sparse Master := [(Sum.inr 2797, 1), (Sum.inr 2799, 1), (Sum.inr 2801, 1), (Sum.inr 2809, 1), (Sum.inr 2862, 1), (Sum.inr 3690, 1), (Sum.inr 4091, -1)]

def numericRow1932 : Integer.Sparse Master := [(Sum.inr 2524, 1), (Sum.inr 2798, 2), (Sum.inr 2807, 1), (Sum.inr 2861, 1), (Sum.inr 3689, 1), (Sum.inr 4092, -1)]

def numericRow1933 : Integer.Sparse Master := [(Sum.inr 2031, 2), (Sum.inr 2036, 1), (Sum.inr 2046, 1), (Sum.inr 2275, 1), (Sum.inr 3537, 1), (Sum.inr 4080, -1)]

def numericRow1934 : Integer.Sparse Master := [(Sum.inr 2810, 1), (Sum.inr 2816, 1), (Sum.inr 2817, 1), (Sum.inr 2819, 1), (Sum.inr 2885, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

def numericRow1935 : Integer.Sparse Master := [(Sum.inr 2809, -1), (Sum.inr 2815, -1), (Sum.inr 2818, -2), (Sum.inr 2880, -1), (Sum.inr 2884, -2), (Sum.inr 3053, -1), (Sum.inr 3587, -1), (Sum.inr 3588, -1), (Sum.inr 3592, -2), (Sum.inr 3617, -1), (Sum.inr 3619, -1), (Sum.inr 3621, -2), (Sum.inr 3945, -1), (Sum.inr 3952, -1), (Sum.inr 3958, -2), (Sum.inr 3961, -2), (Sum.inr 4364, 4), (Sum.inr 4365, 4), (Sum.inr 4369, 8), (Sum.inr 4474, 4), (Sum.inr 5041, 4), (Sum.inr 5043, 8), (Sum.inr 5085, 4), (Sum.inr 5147, 8), (Sum.inr 5185, 8), (Sum.inr 5189, 8), (Sum.inr 5266, 8)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1936 : Integer.Sparse Master := [(Sum.inr 1703, 1), (Sum.inr 1704, 1), (Sum.inr 1709, 1), (Sum.inr 1721, 2), (Sum.inr 3458, 1), (Sum.inr 3461, 1), (Sum.inr 3465, 2), (Sum.inr 3529, 2), (Sum.inr 3530, 2), (Sum.inr 3535, 2), (Sum.inr 3542, 2), (Sum.inr 3587, 1), (Sum.inr 3588, 1), (Sum.inr 3592, 2), (Sum.inr 3617, 1), (Sum.inr 3619, 1), (Sum.inr 3621, 2), (Sum.inr 3952, 1), (Sum.inr 3961, 2)]

def numericRow1937 : Integer.Sparse Master := [(Sum.inr 2434, -1), (Sum.inr 2519, -1), (Sum.inr 2807, -1), (Sum.inr 2813, -1), (Sum.inr 2817, -1), (Sum.inr 2881, -1), (Sum.inr 2889, -1), (Sum.inr 3054, -1), (Sum.inr 3457, -1), (Sum.inr 3486, -1), (Sum.inr 3590, -1), (Sum.inr 3591, -1), (Sum.inr 3595, -1), (Sum.inr 3624, -1), (Sum.inr 3626, -1), (Sum.inr 3631, -1), (Sum.inr 3781, -1), (Sum.inr 3794, -1), (Sum.inr 3845, -2), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 4366, 4), (Sum.inr 4367, 4), (Sum.inr 4368, 4), (Sum.inr 4372, 4), (Sum.inr 4475, 4), (Sum.inr 5034, 4), (Sum.inr 5042, 4), (Sum.inr 5044, 4), (Sum.inr 5086, 4), (Sum.inr 5139, 4), (Sum.inr 5187, 4), (Sum.inr 5188, 4), (Sum.inr 5197, 4), (Sum.inr 5198, 4), (Sum.inr 5199, 4), (Sum.inr 5267, 4), (Sum.inr 5299, 4)]

def numericRow1938 : Integer.Sparse Master := [(Sum.inr 1711, 1), (Sum.inr 1712, 1), (Sum.inr 1715, 1), (Sum.inr 1720, 1), (Sum.inr 1734, 1), (Sum.inr 3451, 1), (Sum.inr 3457, 1), (Sum.inr 3462, 1), (Sum.inr 3464, 1), (Sum.inr 3474, 1), (Sum.inr 3486, 1), (Sum.inr 3523, 1), (Sum.inr 3537, 1), (Sum.inr 3538, 1), (Sum.inr 3541, 1), (Sum.inr 3569, 1), (Sum.inr 3570, 1), (Sum.inr 3573, 1), (Sum.inr 3578, 1), (Sum.inr 3590, 1), (Sum.inr 3591, 1), (Sum.inr 3595, 1), (Sum.inr 3624, 1), (Sum.inr 3626, 1), (Sum.inr 3631, 1), (Sum.inr 3794, 1), (Sum.inr 3845, 1), (Sum.inr 3958, 1)]

def numericRow1939 : Integer.Sparse Master := [(Sum.inr 1970, 1), (Sum.inr 2806, 1), (Sum.inr 2812, 2), (Sum.inr 2879, 1), (Sum.inr 3498, 1), (Sum.inr 4084, -1)]

def numericRow1940 : Integer.Sparse Master := [(Sum.inr 2607, 1), (Sum.inr 3067, 1), (Sum.inr 3751, 1), (Sum.inr 3866, 2), (Sum.inr 3867, 1), (Sum.inr 4087, -1)]

def numericRow1941 : Integer.Sparse Master := [(Sum.inr 1294, -1), (Sum.inr 2482, -1), (Sum.inr 2553, -1), (Sum.inr 2561, -1), (Sum.inr 2590, -1), (Sum.inr 2765, -1), (Sum.inr 2782, -1), (Sum.inr 3305, -1), (Sum.inr 3468, -1), (Sum.inr 3514, -1), (Sum.inr 3522, -1), (Sum.inr 3564, -1), (Sum.inr 3582, -1), (Sum.inr 3583, -1), (Sum.inr 3732, -1), (Sum.inr 3786, -1), (Sum.inr 3799, -1), (Sum.inr 3811, -1), (Sum.inr 3850, -2), (Sum.inr 3857, -1), (Sum.inr 3876, -1), (Sum.inr 4545, 4), (Sum.inr 4547, 4), (Sum.inr 4548, 4), (Sum.inr 4556, 4), (Sum.inr 4963, 4), (Sum.inr 4965, 4), (Sum.inr 4966, 4), (Sum.inr 4976, 4), (Sum.inr 5041, 4), (Sum.inr 5112, 4), (Sum.inr 5116, 4), (Sum.inr 5144, 4), (Sum.inr 5147, 4), (Sum.inr 5151, 4), (Sum.inr 5160, 4), (Sum.inr 5164, 4), (Sum.inr 5173, 4)]

def numericRow1942 : Integer.Sparse Master := [(Sum.inr 2655, 1), (Sum.inr 2657, 1), (Sum.inr 2659, 1), (Sum.inr 2681, 1), (Sum.inr 2735, 1), (Sum.inr 3259, 1), (Sum.inr 3266, 1), (Sum.inr 3271, 1), (Sum.inr 3305, 1), (Sum.inr 3458, 1), (Sum.inr 3468, 1), (Sum.inr 3475, 1), (Sum.inr 3514, 1), (Sum.inr 3522, 1), (Sum.inr 3530, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3556, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 3582, 1), (Sum.inr 3583, 1), (Sum.inr 3799, 1), (Sum.inr 3811, 1), (Sum.inr 3850, 1), (Sum.inr 3876, 1)]

def numericRow1943 : Integer.Sparse Master := [(Sum.inr 2353, 1), (Sum.inr 2355, 1), (Sum.inr 2356, 1), (Sum.inr 2362, 1), (Sum.inr 2590, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

def numericRow1944 : Integer.Sparse Master := [(Sum.inl 0, 152), (Sum.inl 5, -40), (Sum.inl 6, -5), (Sum.inl 2, 65), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, -30), (Sum.inr 915, -4320), (Sum.inr 916, -4320), (Sum.inr 917, -4320), (Sum.inr 932, -4320), (Sum.inr 1035, -4320), (Sum.inr 1632, -4320), (Sum.inr 1633, -4320), (Sum.inr 1634, -4320), (Sum.inr 1645, -4320), (Sum.inr 1681, -4320), (Sum.inr 1875, -4320), (Sum.inr 1880, -4320), (Sum.inr 1905, -4320), (Sum.inr 1917, -4320), (Sum.inr 1924, -4320), (Sum.inr 1938, -4320), (Sum.inr 2109, -4320), (Sum.inr 2261, -4320), (Sum.inr 2328, -4320), (Sum.inr 2329, -4320), (Sum.inr 2341, -4320), (Sum.inr 2424, -4320), (Sum.inr 2431, -4320), (Sum.inr 2477, -4320), (Sum.inr 2536, -4320), (Sum.inr 2539, -4320), (Sum.inr 2589, -4320), (Sum.inr 2590, -8640), (Sum.inr 2672, -4320), (Sum.inr 2764, -4320), (Sum.inr 2765, -4320), (Sum.inr 3370, -4320), (Sum.inr 3372, -4320), (Sum.inr 3391, -4320), (Sum.inr 3401, -4320), (Sum.inr 3402, -4320), (Sum.inr 3417, -4320), (Sum.inr 3440, -4320), (Sum.inr 3444, -4320), (Sum.inr 3453, -4320), (Sum.inr 3563, -4320), (Sum.inr 3564, -8640), (Sum.inr 3581, -4320), (Sum.inr 3582, -4320), (Sum.inr 3613, -4320), (Sum.inr 3614, -4320), (Sum.inr 3787, -4320), (Sum.inr 3790, -4320), (Sum.inr 3804, -4320), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3815, -4320), (Sum.inr 3913, -4320), (Sum.inr 4010, -4320)]

def numericRow1945 : Integer.Sparse Master := [(Sum.inr 1240, -1), (Sum.inr 2429, -1), (Sum.inr 2432, -2), (Sum.inr 2556, -2), (Sum.inr 2589, -1), (Sum.inr 2723, -2), (Sum.inr 3299, -1), (Sum.inr 3455, -1), (Sum.inr 3456, -2), (Sum.inr 3521, -2), (Sum.inr 3544, -2), (Sum.inr 3563, -1), (Sum.inr 3721, -1), (Sum.inr 3836, -1), (Sum.inr 3838, -2), (Sum.inr 3843, -2), (Sum.inr 4527, 4), (Sum.inr 4530, 8), (Sum.inr 4542, 4), (Sum.inr 4956, 4), (Sum.inr 4958, 8), (Sum.inr 4964, 4), (Sum.inr 5128, 8), (Sum.inr 5145, 8)]

def numericRow1946 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3257, 1), (Sum.inr 3261, 2), (Sum.inr 3299, 1), (Sum.inr 3455, 1), (Sum.inr 3456, 2), (Sum.inr 3510, 1), (Sum.inr 3511, 2), (Sum.inr 3519, 2), (Sum.inr 3521, 2), (Sum.inr 3544, 2), (Sum.inr 3554, 1), (Sum.inr 3562, 2), (Sum.inr 3563, 1), (Sum.inr 3836, 1), (Sum.inr 3843, 2)]

def numericRow1947 : Integer.Sparse Master := [(Sum.inr 2349, 1), (Sum.inr 2351, 2), (Sum.inr 2354, 1), (Sum.inr 2556, 1), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

def numericRow1948 : Integer.Sparse Master := [(Sum.inl 0, 322), (Sum.inl 6, 5), (Sum.inl 2, -45), (Sum.inl 7, -80), (Sum.inl 3, -240), (Sum.inl 4, -160), (Sum.inr 900, -4320), (Sum.inr 901, -8640), (Sum.inr 922, -4320), (Sum.inr 980, -4320), (Sum.inr 1588, -4320), (Sum.inr 1589, -8640), (Sum.inr 1616, -4320), (Sum.inr 1673, -4320), (Sum.inr 2317, -4320), (Sum.inr 2318, -8640), (Sum.inr 2332, -4320), (Sum.inr 2371, -4320), (Sum.inr 2372, -8640), (Sum.inr 2383, -4320), (Sum.inr 2482, -8640), (Sum.inr 2553, -8640), (Sum.inr 2561, -8640), (Sum.inr 2721, -4320), (Sum.inr 2723, -8640), (Sum.inr 3335, -4320), (Sum.inr 3336, -8640), (Sum.inr 3352, -4320), (Sum.inr 3399, -4320), (Sum.inr 3400, -8640), (Sum.inr 3410, -4320), (Sum.inr 3468, -8640), (Sum.inr 3514, -8640), (Sum.inr 3522, -8640), (Sum.inr 3532, -4320), (Sum.inr 3544, -8640), (Sum.inr 3602, -4320), (Sum.inr 3607, -8640), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 4046, -4320), (Sum.inr 4047, -8640)]

def numericRow1949 : Integer.Sparse Master := [(Sum.inr 1236, -1), (Sum.inr 2425, -1), (Sum.inr 2428, -1), (Sum.inr 2431, -1), (Sum.inr 2482, -1), (Sum.inr 2561, -1), (Sum.inr 2590, -1), (Sum.inr 2722, -1), (Sum.inr 2739, -1), (Sum.inr 3293, -1), (Sum.inr 3449, -1), (Sum.inr 3450, -1), (Sum.inr 3453, -1), (Sum.inr 3468, -1), (Sum.inr 3522, -1), (Sum.inr 3533, -1), (Sum.inr 3534, -1), (Sum.inr 3564, -1), (Sum.inr 3719, -1), (Sum.inr 3795, -1), (Sum.inr 3837, -2), (Sum.inr 3838, -1), (Sum.inr 3843, -1), (Sum.inr 4528, 4), (Sum.inr 4529, 4), (Sum.inr 4533, 4), (Sum.inr 4545, 4), (Sum.inr 4954, 4), (Sum.inr 4955, 4), (Sum.inr 4957, 4), (Sum.inr 4963, 4), (Sum.inr 5129, 4), (Sum.inr 5138, 4), (Sum.inr 5144, 4), (Sum.inr 5160, 4)]

def numericRow1950 : Integer.Sparse Master := [(Sum.inr 3258, 1), (Sum.inr 3259, 1), (Sum.inr 3260, 1), (Sum.inr 3267, 1), (Sum.inr 3293, 1), (Sum.inr 3449, 1), (Sum.inr 3450, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3468, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3522, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3553, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3564, 1), (Sum.inr 3795, 1), (Sum.inr 3837, 1), (Sum.inr 3838, 1)]

def numericRow1951 : Integer.Sparse Master := [(Sum.inr 2347, 1), (Sum.inr 2348, 1), (Sum.inr 2350, 1), (Sum.inr 2353, 1), (Sum.inr 2553, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1952 : Integer.Sparse Master := [(Sum.inl 0, 182), (Sum.inl 6, 10), (Sum.inl 2, -145), (Sum.inl 8, -160), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 315), (Sum.inr 898, -4320), (Sum.inr 899, -4320), (Sum.inr 901, -4320), (Sum.inr 919, -4320), (Sum.inr 977, -4320), (Sum.inr 1586, -4320), (Sum.inr 1587, -4320), (Sum.inr 1589, -4320), (Sum.inr 1597, -4320), (Sum.inr 1664, -4320), (Sum.inr 1860, -4320), (Sum.inr 1863, -4320), (Sum.inr 1883, -4320), (Sum.inr 1888, -4320), (Sum.inr 1897, -4320), (Sum.inr 1907, -4320), (Sum.inr 2022, -4320), (Sum.inr 2203, -4320), (Sum.inr 2316, -4320), (Sum.inr 2318, -4320), (Sum.inr 2330, -4320), (Sum.inr 2370, -4320), (Sum.inr 2372, -4320), (Sum.inr 2382, -4320), (Sum.inr 2541, -4320), (Sum.inr 2553, -8640), (Sum.inr 2556, -4320), (Sum.inr 2561, -4320), (Sum.inr 2694, -4320), (Sum.inr 2721, -4320), (Sum.inr 2722, -4320), (Sum.inr 3334, -4320), (Sum.inr 3336, -4320), (Sum.inr 3340, -4320), (Sum.inr 3398, -4320), (Sum.inr 3400, -4320), (Sum.inr 3404, -4320), (Sum.inr 3487, -4320), (Sum.inr 3493, -4320), (Sum.inr 3514, -8640), (Sum.inr 3521, -4320), (Sum.inr 3522, -4320), (Sum.inr 3532, -4320), (Sum.inr 3533, -4320), (Sum.inr 3602, -4320), (Sum.inr 3603, -4320), (Sum.inr 3779, -4320), (Sum.inr 3781, -4320), (Sum.inr 3794, -4320), (Sum.inr 3797, -4320), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 3903, -4320), (Sum.inr 4046, -4320)]

def numericRow1953 : Integer.Sparse Master := [(Sum.inr 1129, -1), (Sum.inr 2332, -1), (Sum.inr 2480, -2), (Sum.inr 2483, -1), (Sum.inr 2485, -1), (Sum.inr 2489, -1), (Sum.inr 2721, -1), (Sum.inr 2723, -1), (Sum.inr 3263, -1), (Sum.inr 3410, -1), (Sum.inr 3467, -2), (Sum.inr 3477, -1), (Sum.inr 3481, -1), (Sum.inr 3482, -1), (Sum.inr 3532, -1), (Sum.inr 3544, -1), (Sum.inr 3690, -1), (Sum.inr 3764, -1), (Sum.inr 3787, -1), (Sum.inr 3800, -1), (Sum.inr 3804, -1), (Sum.inr 3805, -1), (Sum.inr 4528, 4), (Sum.inr 4530, 4), (Sum.inr 4533, 4), (Sum.inr 4590, 4), (Sum.inr 4930, 4), (Sum.inr 4933, 4), (Sum.inr 5034, 4), (Sum.inr 5043, 4), (Sum.inr 5044, 4), (Sum.inr 5065, 4), (Sum.inr 5067, 4), (Sum.inr 5185, 4)]

def numericRow1954 : Integer.Sparse Master := [(Sum.inr 3260, 1), (Sum.inr 3261, 1), (Sum.inr 3263, 1), (Sum.inr 3267, 1), (Sum.inr 3290, 1), (Sum.inr 3408, 1), (Sum.inr 3410, 1), (Sum.inr 3414, 1), (Sum.inr 3451, 1), (Sum.inr 3465, 1), (Sum.inr 3466, 1), (Sum.inr 3467, 2), (Sum.inr 3474, 1), (Sum.inr 3476, 1), (Sum.inr 3477, 1), (Sum.inr 3481, 1), (Sum.inr 3482, 1), (Sum.inr 3529, 1), (Sum.inr 3532, 1), (Sum.inr 3544, 1), (Sum.inr 3764, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1)]

def numericRow1955 : Integer.Sparse Master := [(Sum.inr 1875, 1), (Sum.inr 1876, 1), (Sum.inr 1878, 1), (Sum.inr 2075, 1), (Sum.inr 3444, 1), (Sum.inr 4080, -1)]

def numericRow1956 : Integer.Sparse Master := [(Sum.inr 1126, -1), (Sum.inr 2330, -1), (Sum.inr 2482, -2), (Sum.inr 2488, -2), (Sum.inr 2508, -1), (Sum.inr 2722, -2), (Sum.inr 3256, -1), (Sum.inr 3404, -1), (Sum.inr 3460, -1), (Sum.inr 3468, -2), (Sum.inr 3478, -2), (Sum.inr 3533, -2), (Sum.inr 3689, -1), (Sum.inr 3757, -1), (Sum.inr 3786, -1), (Sum.inr 3799, -1), (Sum.inr 3800, -1), (Sum.inr 3805, -1), (Sum.inr 4527, 4), (Sum.inr 4529, 8), (Sum.inr 4589, 4), (Sum.inr 4931, 8), (Sum.inr 5041, 4), (Sum.inr 5042, 8), (Sum.inr 5074, 8), (Sum.inr 5184, 4)]

def numericRow1957 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3256, 1), (Sum.inr 3258, 2), (Sum.inr 3288, 1), (Sum.inr 3404, 1), (Sum.inr 3406, 2), (Sum.inr 3458, 1), (Sum.inr 3460, 1), (Sum.inr 3462, 2), (Sum.inr 3463, 2), (Sum.inr 3468, 2), (Sum.inr 3478, 2), (Sum.inr 3524, 1), (Sum.inr 3533, 2), (Sum.inr 3757, 1), (Sum.inr 3799, 1), (Sum.inr 3800, 1)]

def numericRow1958 : Integer.Sparse Master := [(Sum.inr 1128, -1), (Sum.inr 1960, -1), (Sum.inr 1969, -1), (Sum.inr 2173, -1), (Sum.inr 2184, -1), (Sum.inr 2185, -1), (Sum.inr 2509, -2), (Sum.inr 2522, -2), (Sum.inr 2685, -2), (Sum.inr 2694, -1), (Sum.inr 2704, -2), (Sum.inr 2705, -1), (Sum.inr 2740, -4), (Sum.inr 3077, -1), (Sum.inr 3493, -1), (Sum.inr 3498, -1), (Sum.inr 3625, -1), (Sum.inr 4540, 4), (Sum.inr 4548, 8), (Sum.inr 4600, 4), (Sum.inr 4945, 8), (Sum.inr 5035, 8), (Sum.inr 5097, 4), (Sum.inr 5103, 8), (Sum.inr 5270, 4)]

def numericRow1959 : Integer.Sparse Master := [(Sum.inr 2173, 1), (Sum.inr 2184, 1), (Sum.inr 2185, 1), (Sum.inr 2652, 2), (Sum.inr 2657, 2), (Sum.inr 2658, 2), (Sum.inr 2685, 2), (Sum.inr 2688, 1), (Sum.inr 2694, 1), (Sum.inr 2702, 1), (Sum.inr 2704, 2), (Sum.inr 2705, 1), (Sum.inr 2740, 2), (Sum.inr 3024, 2), (Sum.inr 3058, 1), (Sum.inr 3075, 1), (Sum.inr 3077, 1)]

def numericRow1960 : Integer.Sparse Master := [(Sum.inr 1044, -1), (Sum.inr 1737, -1), (Sum.inr 2023, -1), (Sum.inr 2105, -1), (Sum.inr 2107, -2), (Sum.inr 2214, -1), (Sum.inr 2241, -1), (Sum.inr 2245, -2), (Sum.inr 2260, -2), (Sum.inr 2277, -2), (Sum.inr 2764, -1), (Sum.inr 3581, -1), (Sum.inr 4366, 4), (Sum.inr 4371, 4), (Sum.inr 4372, 8), (Sum.inr 4698, 4), (Sum.inr 4702, 4), (Sum.inr 4703, 8), (Sum.inr 4765, 4), (Sum.inr 4775, 8), (Sum.inr 4808, 8), (Sum.inr 4852, 8), (Sum.inr 4856, 8), (Sum.inr 5263, 4), (Sum.inr 5279, 4), (Sum.inr 5299, 8)]

def numericRow1961 : Integer.Sparse Master := [(Sum.inr 1711, 1), (Sum.inr 1734, 2), (Sum.inr 1737, 1), (Sum.inr 1742, 1), (Sum.inr 2179, 1), (Sum.inr 2180, 1), (Sum.inr 2211, 2), (Sum.inr 2214, 1), (Sum.inr 2220, 2), (Sum.inr 2241, 1), (Sum.inr 2248, 1), (Sum.inr 2250, 2), (Sum.inr 2260, 2), (Sum.inr 2272, 2), (Sum.inr 2274, 2), (Sum.inr 2277, 2), (Sum.inr 2728, 1), (Sum.inr 2748, 1), (Sum.inr 2764, 1), (Sum.inr 2773, 2)]

def numericRow1962 : Integer.Sparse Master := [(Sum.inr 1824, 1), (Sum.inr 1828, 1), (Sum.inr 1829, 2), (Sum.inr 2110, 1), (Sum.inr 3079, 1), (Sum.inr 4083, -1)]

def numericRow1963 : Integer.Sparse Master := [(Sum.inl 0, 270), (Sum.inl 5, 60), (Sum.inl 2, 30), (Sum.inl 7, 240), (Sum.inl 3, -480), (Sum.inl 23, -720), (Sum.inl 12, -720), (Sum.inl 27, -180), (Sum.inl 1, 960), (Sum.inr 736, -12960), (Sum.inr 737, -12960), (Sum.inr 738, -25920), (Sum.inr 818, -12960), (Sum.inr 819, -25920), (Sum.inr 827, -25920), (Sum.inr 840, -12960), (Sum.inr 1811, -12960), (Sum.inr 1812, -12960), (Sum.inr 1814, -25920), (Sum.inr 1877, -12960), (Sum.inr 1878, -25920), (Sum.inr 1919, -25920), (Sum.inr 1925, -25920), (Sum.inr 1935, -12960), (Sum.inr 2100, -25920), (Sum.inr 2101, -51840), (Sum.inr 2110, -38880), (Sum.inr 2112, -25920), (Sum.inr 2115, -25920), (Sum.inr 2156, -12960), (Sum.inr 2157, -25920), (Sum.inr 2165, -12960), (Sum.inr 2275, -38880), (Sum.inr 2276, -25920), (Sum.inr 2279, -51840), (Sum.inr 2287, -25920), (Sum.inr 3789, -12960), (Sum.inr 3810, -12960), (Sum.inr 3885, -25920), (Sum.inr 3891, -12960), (Sum.inr 3907, -25920)]

def numericRow1964 : Integer.Sparse Master := [(Sum.inl 0, -270), (Sum.inl 5, -60), (Sum.inl 2, -30), (Sum.inl 7, -240), (Sum.inl 3, 480), (Sum.inl 23, 720), (Sum.inl 12, 720), (Sum.inl 27, 180), (Sum.inl 1, -960), (Sum.inr 736, 12960), (Sum.inr 737, 12960), (Sum.inr 738, 25920), (Sum.inr 827, 12960), (Sum.inr 1811, 12960), (Sum.inr 1812, 12960), (Sum.inr 1814, 25920), (Sum.inr 1877, 12960), (Sum.inr 1878, 25920), (Sum.inr 1925, 12960), (Sum.inr 2100, 12960), (Sum.inr 2101, 25920), (Sum.inr 2110, 25920), (Sum.inr 2112, 25920), (Sum.inr 2115, 25920), (Sum.inr 2275, 12960), (Sum.inr 2279, 25920), (Sum.inr 3789, 12960), (Sum.inr 3885, 12960)]

def numericRow1965 : Integer.Sparse Master := [(Sum.inr 1041, -1), (Sum.inr 1724, -1), (Sum.inr 2020, -1), (Sum.inr 2105, -1), (Sum.inr 2107, -2), (Sum.inr 2110, -1), (Sum.inr 2112, -1), (Sum.inr 2116, -1), (Sum.inr 2202, -1), (Sum.inr 2241, -1), (Sum.inr 2244, -1), (Sum.inr 2260, -2), (Sum.inr 2262, -1), (Sum.inr 2275, -1), (Sum.inr 2287, -1), (Sum.inr 2288, -1), (Sum.inr 2764, -1), (Sum.inr 2782, -1), (Sum.inr 3581, -1), (Sum.inr 3583, -1), (Sum.inr 4364, 4), (Sum.inr 4367, 4), (Sum.inr 4369, 4), (Sum.inr 4372, 4), (Sum.inr 4696, 4), (Sum.inr 4699, 4), (Sum.inr 4701, 4), (Sum.inr 4703, 4), (Sum.inr 4772, 4), (Sum.inr 4774, 4), (Sum.inr 4775, 4), (Sum.inr 4851, 4), (Sum.inr 4853, 4), (Sum.inr 4856, 4), (Sum.inr 5255, 4), (Sum.inr 5288, 4), (Sum.inr 5289, 4)]

def numericRow1966 : Integer.Sparse Master := [(Sum.inr 1703, 1), (Sum.inr 1720, 1), (Sum.inr 1721, 1), (Sum.inr 1724, 1), (Sum.inr 1734, 1), (Sum.inr 2198, 1), (Sum.inr 2199, 1), (Sum.inr 2202, 1), (Sum.inr 2211, 1), (Sum.inr 2238, 1), (Sum.inr 2240, 1), (Sum.inr 2241, 1), (Sum.inr 2256, 1), (Sum.inr 2257, 1), (Sum.inr 2259, 1), (Sum.inr 2260, 2), (Sum.inr 2262, 1), (Sum.inr 2272, 1), (Sum.inr 2274, 1), (Sum.inr 2275, 1), (Sum.inr 2287, 1), (Sum.inr 2288, 1), (Sum.inr 2718, 1), (Sum.inr 2760, 1), (Sum.inr 2763, 1), (Sum.inr 2764, 1), (Sum.inr 2782, 1)]

def numericRow1967 : Integer.Sparse Master := [(Sum.inr 1822, 1), (Sum.inr 1825, 1), (Sum.inr 1827, 1), (Sum.inr 1829, 1), (Sum.inr 2107, 1), (Sum.inr 3096, 1), (Sum.inr 4083, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1968 : Integer.Sparse Master := [(Sum.inl 0, 327), (Sum.inl 5, 60), (Sum.inl 2, -30), (Sum.inl 7, 240), (Sum.inl 3, 480), (Sum.inl 24, -720), (Sum.inl 12, 240), (Sum.inl 4, 240), (Sum.inl 27, -180), (Sum.inl 1, -765), (Sum.inr 732, -12960), (Sum.inr 733, -12960), (Sum.inr 734, -12960), (Sum.inr 739, -12960), (Sum.inr 798, -12960), (Sum.inr 799, -12960), (Sum.inr 800, -12960), (Sum.inr 811, -12960), (Sum.inr 824, -12960), (Sum.inr 841, -12960), (Sum.inr 1805, -12960), (Sum.inr 1807, -12960), (Sum.inr 1810, -12960), (Sum.inr 1815, -12960), (Sum.inr 1875, -12960), (Sum.inr 1876, -12960), (Sum.inr 1879, -12960), (Sum.inr 1905, -12960), (Sum.inr 1906, -12960), (Sum.inr 1913, -12960), (Sum.inr 1922, -12960), (Sum.inr 1936, -12960), (Sum.inr 2046, -12960), (Sum.inr 2047, -12960), (Sum.inr 2048, -12960), (Sum.inr 2058, -12960), (Sum.inr 2077, -12960), (Sum.inr 2079, -12960), (Sum.inr 2082, -12960), (Sum.inr 2105, -12960), (Sum.inr 2106, -12960), (Sum.inr 2107, -25920), (Sum.inr 2109, -12960), (Sum.inr 2116, -12960), (Sum.inr 2150, -12960), (Sum.inr 2151, -12960), (Sum.inr 2152, -12960), (Sum.inr 2166, -12960), (Sum.inr 2216, -12960), (Sum.inr 2241, -12960), (Sum.inr 2242, -12960), (Sum.inr 2245, -12960), (Sum.inr 2260, -25920), (Sum.inr 2261, -12960), (Sum.inr 2266, -12960), (Sum.inr 2277, -12960), (Sum.inr 2278, -12960), (Sum.inr 2288, -12960), (Sum.inr 3787, -12960), (Sum.inr 3804, -12960), (Sum.inr 3857, -12960), (Sum.inr 3876, -12960), (Sum.inr 3892, -12960), (Sum.inr 3910, -12960), (Sum.inr 3913, -12960)]

def numericRow1969 : Integer.Sparse Master := [(Sum.inl 0, -327), (Sum.inl 5, -60), (Sum.inl 2, 30), (Sum.inl 7, -240), (Sum.inl 3, -480), (Sum.inl 24, 720), (Sum.inl 12, -240), (Sum.inl 4, -240), (Sum.inl 27, 180), (Sum.inl 1, 765), (Sum.inr 732, 12960), (Sum.inr 733, 12960), (Sum.inr 734, 12960), (Sum.inr 739, 12960), (Sum.inr 824, 12960), (Sum.inr 1805, 12960), (Sum.inr 1807, 12960), (Sum.inr 1810, 12960), (Sum.inr 1815, 12960), (Sum.inr 1875, 12960), (Sum.inr 1876, 12960), (Sum.inr 1879, 12960), (Sum.inr 1922, 12960), (Sum.inr 2077, 12960), (Sum.inr 2079, 12960), (Sum.inr 2082, 12960), (Sum.inr 2105, 12960), (Sum.inr 2106, 12960), (Sum.inr 2107, 25920), (Sum.inr 2109, 12960), (Sum.inr 2116, 12960), (Sum.inr 2216, 12960), (Sum.inr 2277, 12960), (Sum.inr 2278, 12960), (Sum.inr 3787, 12960), (Sum.inr 3876, 12960)]

def numericRow1970 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 8, 80), (Sum.inl 1, -20), (Sum.inr 1035, -4320), (Sum.inr 1073, -4320), (Sum.inr 1645, -4320), (Sum.inr 1648, -4320), (Sum.inr 2016, -4320), (Sum.inr 2020, -4320), (Sum.inr 2046, -4320), (Sum.inr 2054, -4320), (Sum.inr 2075, -4320), (Sum.inr 2077, -4320), (Sum.inr 2101, -8640), (Sum.inr 2106, -4320), (Sum.inr 2107, -4320), (Sum.inr 2110, -4320), (Sum.inr 2202, -4320), (Sum.inr 2206, -4320), (Sum.inr 2242, -4320), (Sum.inr 2260, -4320), (Sum.inr 2275, -4320), (Sum.inr 2881, -4320), (Sum.inr 2884, -4320), (Sum.inr 3607, -4320), (Sum.inr 3621, -4320), (Sum.inr 3624, -4320), (Sum.inr 4449, 17280), (Sum.inr 4453, 17280), (Sum.inr 4462, 17280), (Sum.inr 4799, 17280), (Sum.inr 4806, 17280), (Sum.inr 4849, 17280), (Sum.inr 4851, 17280), (Sum.inr 4852, 17280), (Sum.inr 4861, 17280), (Sum.inr 4867, 17280), (Sum.inr 4870, 17280), (Sum.inr 4879, 17280), (Sum.inr 4880, 17280), (Sum.inr 5185, 17280), (Sum.inr 5199, 17280)]

def numericRow1971 : Integer.Sparse Master := [(Sum.inr 1040, -1), (Sum.inr 1707, -1), (Sum.inr 2019, -1), (Sum.inr 2106, -2), (Sum.inr 2109, -2), (Sum.inr 2115, -2), (Sum.inr 2190, -1), (Sum.inr 2242, -2), (Sum.inr 2244, -1), (Sum.inr 2261, -2), (Sum.inr 2262, -1), (Sum.inr 2276, -2), (Sum.inr 2765, -2), (Sum.inr 3582, -2), (Sum.inr 4363, 4), (Sum.inr 4365, 4), (Sum.inr 4368, 8), (Sum.inr 4695, 4), (Sum.inr 4697, 4), (Sum.inr 4700, 8), (Sum.inr 4771, 4), (Sum.inr 4773, 8), (Sum.inr 4863, 4), (Sum.inr 4867, 8), (Sum.inr 5249, 4), (Sum.inr 5279, 4), (Sum.inr 5282, 4)]

def numericRow1972 : Integer.Sparse Master := [(Sum.inl 0, -113), (Sum.inl 5, 20), (Sum.inl 6, -5), (Sum.inl 2, 120), (Sum.inl 35, 80), (Sum.inl 3, 80), (Sum.inl 54, -240), (Sum.inl 26, 160), (Sum.inl 1, 90), (Sum.inr 1319, 1440), (Sum.inr 1320, 1440), (Sum.inr 1321, 2880), (Sum.inr 2895, 1440), (Sum.inr 2899, 1440), (Sum.inr 3066, 1440), (Sum.inr 3078, 1440), (Sum.inr 3079, 1440), (Sum.inr 3130, 1440), (Sum.inr 3131, 2880), (Sum.inr 3163, 2880), (Sum.inr 3179, 1440), (Sum.inr 3180, 2880)]

def numericRow1973 : Integer.Sparse Master := [(Sum.inr 1697, 1), (Sum.inr 1704, 1), (Sum.inr 1707, 1), (Sum.inr 1712, 2), (Sum.inr 2189, 1), (Sum.inr 2190, 1), (Sum.inr 2194, 2), (Sum.inr 2231, 1), (Sum.inr 2232, 1), (Sum.inr 2239, 1), (Sum.inr 2242, 2), (Sum.inr 2244, 1), (Sum.inr 2249, 2), (Sum.inr 2251, 2), (Sum.inr 2261, 2), (Sum.inr 2276, 2), (Sum.inr 2708, 1), (Sum.inr 2748, 1), (Sum.inr 2751, 1), (Sum.inr 2765, 2)]

def numericRow1974 : Integer.Sparse Master := [(Sum.inr 1821, 1), (Sum.inr 1823, 1), (Sum.inr 1826, 2), (Sum.inr 2106, 1), (Sum.inr 3050, 1), (Sum.inr 4084, -1)]

def numericRow1975 : Integer.Sparse Master := [(Sum.inr 941, 1), (Sum.inr 1821, 1), (Sum.inr 2104, 1), (Sum.inr 2106, 3), (Sum.inr 4084, -1)]

def numericRow1977 : Integer.Sparse Master := [(Sum.inl 0, -192), (Sum.inl 5, -60), (Sum.inl 2, 60), (Sum.inl 7, -240), (Sum.inl 3, -960), (Sum.inl 23, 720), (Sum.inl 12, -480), (Sum.inl 4, -480), (Sum.inl 27, 180), (Sum.inl 1, -60), (Sum.inr 730, 12960), (Sum.inr 731, 12960), (Sum.inr 734, 25920), (Sum.inr 823, 12960), (Sum.inr 1802, 12960), (Sum.inr 1804, 12960), (Sum.inr 1810, 25920), (Sum.inr 1874, 12960), (Sum.inr 1876, 25920), (Sum.inr 1921, 12960), (Sum.inr 2018, 25920), (Sum.inr 2075, 25920), (Sum.inr 2082, 25920), (Sum.inr 2105, 12960), (Sum.inr 2107, 25920), (Sum.inr 2215, 25920), (Sum.inr 2277, 12960), (Sum.inr 3786, 12960), (Sum.inr 3850, 25920)]

def numericRow1979 : Integer.Sparse Master := [(Sum.inr 1877, 1), (Sum.inr 1879, 2), (Sum.inr 2077, 1), (Sum.inr 3446, 1), (Sum.inr 4079, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2112 : Integer.Sparse Master := [(Sum.inr 1534, 4), (Sum.inr 1541, 2), (Sum.inr 4062, -1)]

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

def numericRow117 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 1, -110), (Sum.inr 1723, 4320), (Sum.inr 1744, 4320), (Sum.inr 1745, 4320), (Sum.inr 1749, 2160), (Sum.inr 1750, 4320), (Sum.inr 2201, 4320), (Sum.inr 2224, 8640), (Sum.inr 2259, 8640), (Sum.inr 2262, 4320), (Sum.inr 2287, 4320), (Sum.inr 2738, 4320), (Sum.inr 2781, 4320)]

def numericRow118 : Integer.Sparse Master := [(Sum.inr 2244, 2), (Sum.inr 2247, 1), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

def numericRow119 : Integer.Sparse Master := [(Sum.inr 1027, 1), (Sum.inr 1385, 2), (Sum.inr 1408, 2), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

def numericRow120 : Integer.Sparse Master := [(Sum.inr 1385, 1), (Sum.inr 2009, 1), (Sum.inr 2025, 2), (Sum.inr 2247, 1), (Sum.inr 3075, 1), (Sum.inr 4083, -1)]

def numericRow121 : Integer.Sparse Master := [(Sum.inr 1022, 1), (Sum.inr 2009, 1), (Sum.inr 2090, 2), (Sum.inr 2244, 1), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

def numericRow122 : Integer.Sparse Master := [(Sum.inr 1408, 1), (Sum.inr 2090, 2), (Sum.inr 2112, 1), (Sum.inr 2247, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

def numericRow123 : Integer.Sparse Master := [(Sum.inr 1046, 1), (Sum.inr 2025, 2), (Sum.inr 2112, 1), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

def numericRow124 : Integer.Sparse Master := [(Sum.inr 1022, 2), (Sum.inr 1027, 1), (Sum.inr 1046, 2), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

def numericRow125 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 1080, -60), (Sum.inr 1710, -60), (Sum.inr 2052, -120), (Sum.inr 2193, -120), (Sum.inr 2247, -300), (Sum.inr 2281, -120), (Sum.inr 2290, -300), (Sum.inr 2294, -120), (Sum.inr 3634, -120), (Sum.inr 4494, 480), (Sum.inr 4500, 480), (Sum.inr 4830, 480), (Sum.inr 4836, 960), (Sum.inr 4886, 480), (Sum.inr 4892, 480), (Sum.inr 5252, 480)]

def numericRow126 : Integer.Sparse Master := [(Sum.inl 0, -58), (Sum.inl 2, -285), (Sum.inl 13, -80), (Sum.inl 1, -15), (Sum.inr 1435, 1440), (Sum.inr 1436, 1440), (Sum.inr 2235, 1440), (Sum.inr 2247, 720), (Sum.inr 2255, 1440), (Sum.inr 2707, 1440), (Sum.inr 2712, 1440), (Sum.inr 2716, 2880)]

def numericRow127 : Integer.Sparse Master := [(Sum.inl 0, -10), (Sum.inl 2, -51), (Sum.inl 13, 16), (Sum.inl 1, 3), (Sum.inr 1700, 864), (Sum.inr 1710, 432), (Sum.inr 1716, 864), (Sum.inr 2187, 864), (Sum.inr 2193, 864), (Sum.inr 2197, 1728), (Sum.inr 2235, 864), (Sum.inr 2247, 1728), (Sum.inr 2255, 864), (Sum.inr 2281, 864), (Sum.inr 2712, 864)]

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

def numericRow1167 : Integer.Sparse Master := [(Sum.inl 0, -88), (Sum.inl 6, 110), (Sum.inl 2, 100), (Sum.inl 35, 160), (Sum.inl 1, 30), (Sum.inr 787, 8640), (Sum.inr 813, 4320), (Sum.inr 828, 4320), (Sum.inr 972, 8640), (Sum.inr 982, 8640), (Sum.inr 983, 8640), (Sum.inr 991, 8640), (Sum.inr 1022, 8640), (Sum.inr 1024, 8640), (Sum.inr 1043, 4320), (Sum.inr 1046, 8640), (Sum.inr 1047, 4320), (Sum.inr 1059, 4320), (Sum.inr 1061, 4320), (Sum.inr 1091, 4320), (Sum.inr 1217, 8640)]

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

def numericRow1169 : Integer.Sparse Master := [(Sum.inr 605, -1), (Sum.inr 924, -2), (Sum.inr 1040, -2), (Sum.inr 1043, -2), (Sum.inr 1049, -1), (Sum.inr 1051, -1), (Sum.inr 1518, -1), (Sum.inr 1674, -2), (Sum.inr 1707, -2), (Sum.inr 1725, -2), (Sum.inr 1738, -1), (Sum.inr 1752, -1), (Sum.inr 2022, -2), (Sum.inr 2109, -1), (Sum.inr 2203, -2), (Sum.inr 2261, -1), (Sum.inr 4151, 8), (Sum.inr 4156, 4), (Sum.inr 4160, 4), (Sum.inr 4330, 8), (Sum.inr 4334, 8), (Sum.inr 4365, 8), (Sum.inr 4370, 4), (Sum.inr 4373, 4)]

def numericRow1170 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 5, 20), (Sum.inl 6, -25), (Sum.inl 2, 60), (Sum.inl 1, 70), (Sum.inr 630, 1080), (Sum.inr 633, 540), (Sum.inr 636, 540), (Sum.inr 1118, 1080), (Sum.inr 1142, 540), (Sum.inr 1320, 1080), (Sum.inr 1325, 540), (Sum.inr 1334, 1080)]

def numericRow1171 : Integer.Sparse Master := [(Sum.inr 1505, 2), (Sum.inr 1516, 1), (Sum.inr 1518, 1), (Sum.inr 1523, 1), (Sum.inr 1672, 2), (Sum.inr 1674, 2), (Sum.inr 1679, 2), (Sum.inr 1704, 2), (Sum.inr 1707, 2), (Sum.inr 1722, 1), (Sum.inr 1725, 2), (Sum.inr 1735, 1), (Sum.inr 1738, 1), (Sum.inr 1752, 1), (Sum.inr 2203, 2), (Sum.inr 2261, 1)]

def numericRow1172 : Integer.Sparse Master := [(Sum.inr 579, 2), (Sum.inr 584, 1), (Sum.inr 588, 1), (Sum.inr 605, 1), (Sum.inr 1043, 1), (Sum.inr 4084, -1)]

def numericRow1173 : Integer.Sparse Master := [(Sum.inr 605, 1), (Sum.inr 924, 2), (Sum.inr 1043, 1), (Sum.inr 4084, -1)]

def numericRow1174 : Integer.Sparse Master := [(Sum.inr 943, 2), (Sum.inr 948, 1), (Sum.inr 952, 1), (Sum.inr 1043, 1), (Sum.inr 2109, 1), (Sum.inr 4084, -1)]

def numericRow1175 : Integer.Sparse Master := [(Sum.inr 579, 1), (Sum.inr 943, 1), (Sum.inr 1040, 1), (Sum.inr 1043, 2), (Sum.inr 4084, -1)]

def numericRow1176 : Integer.Sparse Master := [(Sum.inr 908, 1), (Sum.inr 912, 1), (Sum.inr 924, 1), (Sum.inr 1043, 1), (Sum.inr 2022, 1), (Sum.inr 4084, -1)]

def numericRow1177 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 1, 70), (Sum.inr 538, -4320), (Sum.inr 540, -2160), (Sum.inr 547, -2160), (Sum.inr 555, -2160), (Sum.inr 663, -4320), (Sum.inr 665, -2160), (Sum.inr 671, -2160), (Sum.inr 684, -2160), (Sum.inr 865, -4320), (Sum.inr 867, -4320), (Sum.inr 873, -4320), (Sum.inr 881, -4320), (Sum.inr 924, -4320), (Sum.inr 928, -2160), (Sum.inr 938, -2160), (Sum.inr 982, -4320), (Sum.inr 986, -2160), (Sum.inr 1009, -2160), (Sum.inr 1041, -4320), (Sum.inr 1050, -2160), (Sum.inr 1083, -2160), (Sum.inr 1553, -4320), (Sum.inr 1555, -4320), (Sum.inr 1559, -4320), (Sum.inr 1569, -4320), (Sum.inr 1617, -4320), (Sum.inr 1620, -2160), (Sum.inr 1630, -2160), (Sum.inr 1674, -4320), (Sum.inr 1677, -2160), (Sum.inr 1693, -2160), (Sum.inr 1724, -4320), (Sum.inr 1728, -2160), (Sum.inr 1751, -2160), (Sum.inr 2482, -4320), (Sum.inr 2726, -2160), (Sum.inr 3468, -4320), (Sum.inr 3545, -2160), (Sum.inr 3608, -2160), (Sum.inr 3627, -2160)]

def numericRow1178 : Integer.Sparse Master := [(Sum.inl 0, -43), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 1, -70), (Sum.inr 538, 4320), (Sum.inr 540, 2160), (Sum.inr 547, 2160), (Sum.inr 555, 2160), (Sum.inr 865, 4320), (Sum.inr 867, 4320), (Sum.inr 873, 4320), (Sum.inr 881, 4320), (Sum.inr 924, 4320), (Sum.inr 928, 2160), (Sum.inr 938, 2160), (Sum.inr 982, 4320), (Sum.inr 986, 2160), (Sum.inr 1009, 2160), (Sum.inr 1041, 4320), (Sum.inr 1050, 2160), (Sum.inr 1083, 2160), (Sum.inr 2482, 4320), (Sum.inr 2726, 2160)]

def numericRow1179 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 5, 20), (Sum.inl 6, 65), (Sum.inl 2, 60), (Sum.inl 1, -20), (Sum.inr 1217, 1080), (Sum.inr 1242, 540), (Sum.inr 1243, 540), (Sum.inr 1361, 1080), (Sum.inr 1372, 540), (Sum.inr 1373, 540), (Sum.inr 1388, 1080), (Sum.inr 1389, 1080)]

def numericRow1180 : Integer.Sparse Master := [(Sum.inr 1037, 1), (Sum.inr 2018, 2), (Sum.inr 2103, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

def numericRow1181 : Integer.Sparse Master := [(Sum.inr 594, 1), (Sum.inr 916, 2), (Sum.inr 1037, 1), (Sum.inr 1074, 1), (Sum.inr 4081, -1)]

def numericRow1182 : Integer.Sparse Master := [(Sum.inr 1033, 2), (Sum.inr 1037, 1), (Sum.inr 1048, 1), (Sum.inr 1074, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

def numericRow1183 : Integer.Sparse Master := [(Sum.inr 731, 2), (Sum.inr 735, 1), (Sum.inr 741, 1), (Sum.inr 1647, 1), (Sum.inr 4070, -1)]

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

def numericRow1184 : Integer.Sparse Master := [(Sum.inr 983, 1), (Sum.inr 985, 1), (Sum.inr 1005, 1), (Sum.inr 1036, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

def numericRow1185 : Integer.Sparse Master := [(Sum.inr 982, 1), (Sum.inr 1987, 1), (Sum.inr 2079, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

def numericRow1186 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 982, 1), (Sum.inr 985, 1), (Sum.inr 1035, 1), (Sum.inr 4080, -1)]

def numericRow1187 : Integer.Sparse Master := [(Sum.inr 979, 1), (Sum.inr 1986, 1), (Sum.inr 2018, 1), (Sum.inr 2203, 1), (Sum.inr 4081, -1)]

def numericRow1188 : Integer.Sparse Master := [(Sum.inr 864, 1), (Sum.inr 867, 1), (Sum.inr 872, 1), (Sum.inr 979, 1), (Sum.inr 4081, -1)]

def numericRow1189 : Integer.Sparse Master := [(Sum.inr 979, 1), (Sum.inr 984, 1), (Sum.inr 999, 1), (Sum.inr 1033, 1), (Sum.inr 2203, 1), (Sum.inr 4081, -1)]

def numericRow1190 : Integer.Sparse Master := [(Sum.inr 698, 1), (Sum.inr 701, 1), (Sum.inr 706, 1), (Sum.inr 1599, 1), (Sum.inr 4070, -1)]

def numericRow1191 : Integer.Sparse Master := [(Sum.inr 620, -1), (Sum.inr 939, -3), (Sum.inr 1083, -3), (Sum.inr 1539, -1), (Sum.inr 1694, -3), (Sum.inr 1728, -3), (Sum.inr 2062, -3), (Sum.inr 2230, -3), (Sum.inr 2281, -1), (Sum.inr 2294, -1), (Sum.inr 4178, 12), (Sum.inr 4189, 4), (Sum.inr 4347, 24), (Sum.inr 4358, 12), (Sum.inr 4476, 12), (Sum.inr 4481, 4)]

def numericRow1192 : Integer.Sparse Master := [(Sum.inr 1520, 3), (Sum.inr 1539, 1), (Sum.inr 1540, 1), (Sum.inr 1676, 6), (Sum.inr 1694, 3), (Sum.inr 1695, 3), (Sum.inr 1728, 3), (Sum.inr 1729, 3), (Sum.inr 1757, 1), (Sum.inr 2230, 3), (Sum.inr 2294, 1)]

def numericRow1193 : Integer.Sparse Master := [(Sum.inr 925, 2), (Sum.inr 936, 1), (Sum.inr 939, 1), (Sum.inr 1091, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

def numericRow1194 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 1, 10), (Sum.inr 559, -2160), (Sum.inr 564, -720), (Sum.inr 566, -720), (Sum.inr 690, -2160), (Sum.inr 694, -720), (Sum.inr 695, -720), (Sum.inr 887, -4320), (Sum.inr 893, -2160), (Sum.inr 897, -2160), (Sum.inr 1046, -2160), (Sum.inr 1051, -720), (Sum.inr 1087, -2160), (Sum.inr 1094, -720), (Sum.inr 1573, -4320), (Sum.inr 1577, -2160), (Sum.inr 1578, -2160), (Sum.inr 1739, -2160), (Sum.inr 1741, -720), (Sum.inr 1750, -2160), (Sum.inr 1752, -720), (Sum.inr 2519, -2160), (Sum.inr 3486, -2160), (Sum.inr 3633, -720), (Sum.inr 3634, -720)]

def numericRow1195 : Integer.Sparse Master := [(Sum.inr 605, -3), (Sum.inr 615, -1), (Sum.inr 619, -1), (Sum.inr 924, -6), (Sum.inr 934, -3), (Sum.inr 938, -3), (Sum.inr 1043, -3), (Sum.inr 1051, -1), (Sum.inr 1518, -3), (Sum.inr 1537, -1), (Sum.inr 1538, -1), (Sum.inr 1674, -6), (Sum.inr 1692, -3), (Sum.inr 1693, -3), (Sum.inr 1725, -3), (Sum.inr 1752, -1), (Sum.inr 4084, 4)]

def numericRow1196 : Integer.Sparse Master := [(Sum.inr 1518, 3), (Sum.inr 1537, 1), (Sum.inr 1538, 1), (Sum.inr 1674, 6), (Sum.inr 1692, 3), (Sum.inr 1693, 3), (Sum.inr 1725, 3), (Sum.inr 1752, 1), (Sum.inr 4084, 1)]

def numericRow1197 : Integer.Sparse Master := [(Sum.inr 602, -3), (Sum.inr 609, -1), (Sum.inr 618, -1), (Sum.inr 921, -6), (Sum.inr 928, -3), (Sum.inr 937, -3), (Sum.inr 1080, -3), (Sum.inr 1094, -1), (Sum.inr 1509, -3), (Sum.inr 1521, -1), (Sum.inr 1527, -1), (Sum.inr 1666, -6), (Sum.inr 1677, -3), (Sum.inr 1683, -3), (Sum.inr 1710, -3), (Sum.inr 1741, -1), (Sum.inr 4085, 4)]

def numericRow1198 : Integer.Sparse Master := [(Sum.inr 1509, 3), (Sum.inr 1521, 1), (Sum.inr 1527, 1), (Sum.inr 1666, 6), (Sum.inr 1677, 3), (Sum.inr 1683, 3), (Sum.inr 1710, 3), (Sum.inr 1741, 1), (Sum.inr 4085, 1)]

def numericRow1199 : Integer.Sparse Master := [(Sum.inr 602, 3), (Sum.inr 609, 1), (Sum.inr 618, 1), (Sum.inr 4085, -1)]

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

def numericRow1200 : Integer.Sparse Master := [(Sum.inr 602, 1), (Sum.inr 921, 2), (Sum.inr 1080, 1), (Sum.inr 4085, -1)]

def numericRow1201 : Integer.Sparse Master := [(Sum.inr 1010, 1), (Sum.inr 1951, 1), (Sum.inr 2004, 2), (Sum.inr 2222, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

def numericRow1202 : Integer.Sparse Master := [(Sum.inr 1001, 2), (Sum.inr 1010, 1), (Sum.inr 1012, 1), (Sum.inr 1076, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

def numericRow1203 : Integer.Sparse Master := [(Sum.inr 1009, 1), (Sum.inr 2003, 2), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

def numericRow1204 : Integer.Sparse Master := [(Sum.inr 1000, 2), (Sum.inr 1009, 1), (Sum.inr 1075, 1), (Sum.inr 4082, -1)]

def numericRow1205 : Integer.Sparse Master := [(Sum.inr 568, -2), (Sum.inr 574, -1), (Sum.inr 575, -1), (Sum.inr 594, -1), (Sum.inr 867, -2), (Sum.inr 898, -2), (Sum.inr 902, -2), (Sum.inr 916, -2), (Sum.inr 979, -2), (Sum.inr 986, -1), (Sum.inr 999, -2), (Sum.inr 1012, -1), (Sum.inr 1037, -1), (Sum.inr 1074, -1), (Sum.inr 1489, -2), (Sum.inr 1494, -1), (Sum.inr 1495, -1), (Sum.inr 1499, -1), (Sum.inr 1555, -2), (Sum.inr 1586, -2), (Sum.inr 1590, -2), (Sum.inr 1599, -2), (Sum.inr 1602, -2), (Sum.inr 1620, -1), (Sum.inr 1627, -1), (Sum.inr 1633, -2), (Sum.inr 1647, -1), (Sum.inr 1650, -1), (Sum.inr 4081, 4)]

def numericRow1206 : Integer.Sparse Master := [(Sum.inr 1489, 2), (Sum.inr 1494, 1), (Sum.inr 1495, 1), (Sum.inr 1499, 1), (Sum.inr 1555, 2), (Sum.inr 1586, 2), (Sum.inr 1590, 2), (Sum.inr 1599, 2), (Sum.inr 1602, 2), (Sum.inr 1620, 1), (Sum.inr 1627, 1), (Sum.inr 1633, 2), (Sum.inr 1647, 1), (Sum.inr 1650, 1), (Sum.inr 4081, 1)]

def numericRow1207 : Integer.Sparse Master := [(Sum.inr 867, 1), (Sum.inr 898, 1), (Sum.inr 902, 1), (Sum.inr 916, 1), (Sum.inr 4081, -1)]

def numericRow1208 : Integer.Sparse Master := [(Sum.inr 793, 1), (Sum.inr 795, 1), (Sum.inr 796, 1), (Sum.inr 811, 1), (Sum.inr 827, 1), (Sum.inr 1715, 1), (Sum.inr 4069, -1)]

def numericRow1209 : Integer.Sparse Master := [(Sum.inr 825, 2), (Sum.inr 829, 1), (Sum.inr 830, 1), (Sum.inr 858, 1), (Sum.inr 1740, 1), (Sum.inr 4071, -1)]

def numericRow1210 : Integer.Sparse Master := [(Sum.inr 828, 1), (Sum.inr 1610, 2), (Sum.inr 1659, 1), (Sum.inr 1716, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

def numericRow1211 : Integer.Sparse Master := [(Sum.inr 824, 2), (Sum.inr 828, 1), (Sum.inr 831, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

def numericRow1212 : Integer.Sparse Master := [(Sum.inr 826, 1), (Sum.inr 1608, 2), (Sum.inr 1657, 1), (Sum.inr 1738, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

def numericRow1213 : Integer.Sparse Master := [(Sum.inr 555, 1), (Sum.inr 715, 2), (Sum.inr 826, 1), (Sum.inr 4071, -1)]

def numericRow1214 : Integer.Sparse Master := [(Sum.inr 823, 2), (Sum.inr 826, 1), (Sum.inr 830, 1), (Sum.inr 1738, 1), (Sum.inr 4071, -1)]

def numericRow1215 : Integer.Sparse Master := [(Sum.inr 546, 1), (Sum.inr 706, 2), (Sum.inr 741, 1), (Sum.inr 815, 1), (Sum.inr 4070, -1)]

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

def numericRow1216 : Integer.Sparse Master := [(Sum.inr 776, 1), (Sum.inr 778, 1), (Sum.inr 783, 3), (Sum.inr 4068, -1)]

def numericRow1217 : Integer.Sparse Master := [(Sum.inr 787, 1), (Sum.inr 1593, 1), (Sum.inr 1639, 2), (Sum.inr 1700, 1), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

def numericRow1218 : Integer.Sparse Master := [(Sum.inr 542, 1), (Sum.inr 702, 1), (Sum.inr 737, 1), (Sum.inr 787, 2), (Sum.inr 4068, -1)]

def numericRow1219 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 787, 1), (Sum.inr 790, 1), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

def numericRow1220 : Integer.Sparse Master := [(Sum.inr 785, 1), (Sum.inr 1637, 2), (Sum.inr 1707, 1), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

def numericRow1221 : Integer.Sparse Master := [(Sum.inr 538, 1), (Sum.inr 699, 1), (Sum.inr 733, 1), (Sum.inr 785, 1), (Sum.inr 4069, -1)]

def numericRow1222 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 785, 1), (Sum.inr 789, 1), (Sum.inr 1707, 1), (Sum.inr 4069, -1)]

def numericRow1223 : Integer.Sparse Master := [(Sum.inr 536, 1), (Sum.inr 698, 1), (Sum.inr 731, 1), (Sum.inr 804, 1), (Sum.inr 4070, -1)]

def numericRow1224 : Integer.Sparse Master := [(Sum.inr 813, 1), (Sum.inr 1603, 2), (Sum.inr 1651, 1), (Sum.inr 1716, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

def numericRow1225 : Integer.Sparse Master := [(Sum.inr 548, 1), (Sum.inr 708, 2), (Sum.inr 743, 1), (Sum.inr 813, 1), (Sum.inr 4069, -1)]

def numericRow1226 : Integer.Sparse Master := [(Sum.inr 807, 2), (Sum.inr 813, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

def numericRow1227 : Integer.Sparse Master := [(Sum.inr 538, -2), (Sum.inr 545, -1), (Sum.inr 547, -1), (Sum.inr 663, -2), (Sum.inr 683, -1), (Sum.inr 684, -1), (Sum.inr 699, -2), (Sum.inr 705, -2), (Sum.inr 707, -2), (Sum.inr 733, -2), (Sum.inr 740, -1), (Sum.inr 742, -1), (Sum.inr 748, -2), (Sum.inr 762, -2), (Sum.inr 763, -2), (Sum.inr 785, -2), (Sum.inr 791, -1), (Sum.inr 799, -2), (Sum.inr 804, -2), (Sum.inr 842, -1), (Sum.inr 843, -1), (Sum.inr 849, -1), (Sum.inr 999, -2), (Sum.inr 1074, -1), (Sum.inr 1080, -1), (Sum.inr 1602, -2), (Sum.inr 1650, -1), (Sum.inr 1710, -1), (Sum.inr 4069, 4)]

def numericRow1228 : Integer.Sparse Master := [(Sum.inr 663, 2), (Sum.inr 683, 1), (Sum.inr 684, 1), (Sum.inr 748, 2), (Sum.inr 762, 2), (Sum.inr 763, 2), (Sum.inr 799, 2), (Sum.inr 804, 2), (Sum.inr 842, 1), (Sum.inr 843, 1), (Sum.inr 849, 1), (Sum.inr 999, 2), (Sum.inr 1074, 1), (Sum.inr 1080, 1), (Sum.inr 4069, 1)]

def numericRow1229 : Integer.Sparse Master := [(Sum.inr 1602, 2), (Sum.inr 1650, 1), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

def numericRow1230 : Integer.Sparse Master := [(Sum.inr 733, 2), (Sum.inr 740, 1), (Sum.inr 742, 1), (Sum.inr 1650, 1), (Sum.inr 4069, -1)]

def numericRow1231 : Integer.Sparse Master := [(Sum.inr 536, -2), (Sum.inr 540, -1), (Sum.inr 546, -1), (Sum.inr 657, -2), (Sum.inr 665, -1), (Sum.inr 676, -1), (Sum.inr 698, -2), (Sum.inr 701, -2), (Sum.inr 706, -2), (Sum.inr 731, -2), (Sum.inr 735, -1), (Sum.inr 741, -1), (Sum.inr 744, -2), (Sum.inr 750, -2), (Sum.inr 755, -2), (Sum.inr 781, -2), (Sum.inr 785, -2), (Sum.inr 801, -1), (Sum.inr 804, -2), (Sum.inr 815, -1), (Sum.inr 820, -1), (Sum.inr 826, -1), (Sum.inr 979, -2), (Sum.inr 1037, -1), (Sum.inr 1043, -1), (Sum.inr 1599, -2), (Sum.inr 1647, -1), (Sum.inr 1725, -1), (Sum.inr 4070, 4)]

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

def numericRow1232 : Integer.Sparse Master := [(Sum.inr 555, -3), (Sum.inr 564, -1), (Sum.inr 671, -3), (Sum.inr 695, -1), (Sum.inr 715, -6), (Sum.inr 726, -3), (Sum.inr 753, -6), (Sum.inr 774, -3), (Sum.inr 815, -3), (Sum.inr 826, -3), (Sum.inr 832, -1), (Sum.inr 862, -1), (Sum.inr 1012, -3), (Sum.inr 1094, -1), (Sum.inr 1627, -3), (Sum.inr 1741, -1), (Sum.inr 4071, 4)]

def numericRow1233 : Integer.Sparse Master := [(Sum.inr 556, -3), (Sum.inr 566, -1), (Sum.inr 670, -3), (Sum.inr 694, -1), (Sum.inr 716, -6), (Sum.inr 729, -3), (Sum.inr 752, -6), (Sum.inr 773, -3), (Sum.inr 813, -3), (Sum.inr 853, -3), (Sum.inr 860, -2), (Sum.inr 1009, -3), (Sum.inr 1091, -1), (Sum.inr 1630, -3), (Sum.inr 1756, -1), (Sum.inr 4070, 4)]

def numericRow1234 : Integer.Sparse Master := [(Sum.inr 4058, 3), (Sum.inr 4060, 1), (Sum.inr 4061, 1), (Sum.inr 4064, 6), (Sum.inr 4066, 3), (Sum.inr 4067, 3), (Sum.inr 4069, 3), (Sum.inr 4070, 3), (Sum.inr 4071, 1), (Sum.inr 4072, 1), (Sum.inr 4081, 3), (Sum.inr 4084, 1), (Sum.inr 4085, 1)]

def numericRow1235 : Integer.Sparse Master := [(Sum.inr 616, 1), (Sum.inr 935, 2), (Sum.inr 1063, 1), (Sum.inr 1083, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

def numericRow1236 : Integer.Sparse Master := [(Sum.inr 1318, 2), (Sum.inr 1324, 1), (Sum.inr 1325, 1), (Sum.inr 1375, 1), (Sum.inr 2889, 1), (Sum.inr 4092, -1)]

def numericRow1237 : Integer.Sparse Master := [(Sum.inr 1736, 2), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 1751, 1), (Sum.inr 3301, 1), (Sum.inr 4071, -1)]

def numericRow1238 : Integer.Sparse Master := [(Sum.inr 858, 1), (Sum.inr 1626, 2), (Sum.inr 1740, 2), (Sum.inr 1751, 1), (Sum.inr 4071, -1)]

def numericRow1239 : Integer.Sparse Master := [(Sum.inr 830, 1), (Sum.inr 1611, 2), (Sum.inr 1660, 1), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 4071, -1)]

def numericRow1240 : Integer.Sparse Master := [(Sum.inr 586, 1), (Sum.inr 910, 1), (Sum.inr 950, 1), (Sum.inr 1026, 1), (Sum.inr 1041, 1), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

def numericRow1241 : Integer.Sparse Master := [(Sum.inr 1328, 1), (Sum.inr 1333, 1), (Sum.inr 1334, 1), (Sum.inr 1338, 1), (Sum.inr 1391, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

def numericRow1242 : Integer.Sparse Master := [(Sum.inr 1736, 1), (Sum.inr 2397, 1), (Sum.inr 3280, 1), (Sum.inr 3284, 1), (Sum.inr 3301, 2), (Sum.inr 4071, -1)]

def numericRow1243 : Integer.Sparse Master := [(Sum.inr 848, 1), (Sum.inr 1736, 2), (Sum.inr 1751, 2), (Sum.inr 4071, -1)]

def numericRow1244 : Integer.Sparse Master := [(Sum.inr 823, 1), (Sum.inr 1606, 1), (Sum.inr 1655, 1), (Sum.inr 1736, 1), (Sum.inr 1738, 2), (Sum.inr 4071, -1)]

def numericRow1245 : Integer.Sparse Master := [(Sum.inr 1356, 1), (Sum.inr 2856, 1), (Sum.inr 2911, 1), (Sum.inr 2970, 1), (Sum.inr 3025, 2), (Sum.inr 4088, -1)]

def numericRow1246 : Integer.Sparse Master := [(Sum.inr 1133, 2), (Sum.inr 1143, 1), (Sum.inr 1146, 1), (Sum.inr 1245, 1), (Sum.inr 2522, 1), (Sum.inr 4084, -1)]

def numericRow1247 : Integer.Sparse Master := [(Sum.inr 653, 1), (Sum.inr 1171, 2), (Sum.inr 1273, 1), (Sum.inr 1294, 1), (Sum.inr 1306, 1), (Sum.inr 4092, -1)]

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

def numericRow1248 : Integer.Sparse Master := [(Sum.inr 1655, 2), (Sum.inr 1657, 1), (Sum.inr 1660, 1), (Sum.inr 1738, 1), (Sum.inr 2683, 1), (Sum.inr 4071, -1)]

def numericRow1249 : Integer.Sparse Master := [(Sum.inr 1741, 1), (Sum.inr 2683, 3), (Sum.inr 2780, 1), (Sum.inr 3311, 1), (Sum.inr 4071, -1)]

def numericRow1250 : Integer.Sparse Master := [(Sum.inr 1627, 1), (Sum.inr 2397, 2), (Sum.inr 2409, 1), (Sum.inr 2683, 1), (Sum.inr 3301, 1), (Sum.inr 4071, -1)]

def numericRow1251 : Integer.Sparse Master := [(Sum.inr 1738, 1), (Sum.inr 2683, 1), (Sum.inr 3295, 2), (Sum.inr 3301, 1), (Sum.inr 3311, 1), (Sum.inr 4071, -1)]

def numericRow1252 : Integer.Sparse Master := [(Sum.inr 1113, 1), (Sum.inr 1119, 1), (Sum.inr 1121, 1), (Sum.inr 1138, 1), (Sum.inr 1219, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

def numericRow1253 : Integer.Sparse Master := [(Sum.inr 631, 1), (Sum.inr 1138, 1), (Sum.inr 1151, 1), (Sum.inr 1219, 1), (Sum.inr 1236, 1), (Sum.inr 1241, 1), (Sum.inr 4092, -1)]

def numericRow1254 : Integer.Sparse Master := [(Sum.inr 1606, 1), (Sum.inr 1608, 1), (Sum.inr 1611, 1), (Sum.inr 1618, 1), (Sum.inr 1738, 1), (Sum.inr 3295, 1), (Sum.inr 4071, -1)]

def numericRow1255 : Integer.Sparse Master := [(Sum.inr 1114, 1), (Sum.inr 1120, 2), (Sum.inr 1139, 1), (Sum.inr 1220, 1), (Sum.inr 2489, 1), (Sum.inr 4091, -1)]

def numericRow1256 : Integer.Sparse Master := [(Sum.inr 632, 1), (Sum.inr 1139, 1), (Sum.inr 1152, 1), (Sum.inr 1220, 1), (Sum.inr 1240, 2), (Sum.inr 4091, -1)]

def numericRow1257 : Integer.Sparse Master := [(Sum.inr 1618, 2), (Sum.inr 1626, 1), (Sum.inr 1751, 1), (Sum.inr 3297, 1), (Sum.inr 4071, -1)]

def numericRow1258 : Integer.Sparse Master := [(Sum.inr 1751, 1), (Sum.inr 3297, 2), (Sum.inr 3301, 2), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

def numericRow1259 : Integer.Sparse Master := [(Sum.inr 1182, 1), (Sum.inr 2388, 1), (Sum.inr 2533, 1), (Sum.inr 2608, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 4088, -1)]

def numericRow1260 : Integer.Sparse Master := [(Sum.inr 1196, 1), (Sum.inr 2452, 2), (Sum.inr 2609, 1), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

def numericRow1261 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, -1), (Sum.inl 7, -4), (Sum.inl 1, 4), (Sum.inr 613, -54), (Sum.inr 618, -18), (Sum.inr 620, -18), (Sum.inr 1138, -108), (Sum.inr 1143, -54), (Sum.inr 1145, -54), (Sum.inr 1294, -54), (Sum.inr 1297, -18), (Sum.inr 1525, -54), (Sum.inr 1527, -18), (Sum.inr 1539, -18), (Sum.inr 2167, -54), (Sum.inr 2289, -18), (Sum.inr 3270, -108), (Sum.inr 3277, -54), (Sum.inr 3305, -54), (Sum.inr 3308, -54), (Sum.inr 3310, -18), (Sum.inr 3614, -54), (Sum.inr 3633, -18)]

def numericRow1262 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 5, 1), (Sum.inl 7, 4), (Sum.inl 1, -4), (Sum.inr 613, 54), (Sum.inr 618, 18), (Sum.inr 620, 18), (Sum.inr 1138, 108), (Sum.inr 1143, 54), (Sum.inr 1145, 54), (Sum.inr 1294, 54), (Sum.inr 1297, 18)]

def numericRow1263 : Integer.Sparse Master := [(Sum.inl 0, 3), (Sum.inl 5, 10), (Sum.inl 8, 40), (Sum.inl 1, -5), (Sum.inr 1049, -2160), (Sum.inr 1094, -720), (Sum.inr 1246, -2160), (Sum.inr 1738, -2160), (Sum.inr 1741, -720), (Sum.inr 3301, -2160), (Sum.inr 3312, -360), (Sum.inr 4592, 8640), (Sum.inr 4611, 8640), (Sum.inr 4626, 1440)]

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

def numericRow1264 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 5, -5), (Sum.inl 7, 4), (Sum.inl 1, 2), (Sum.inr 1049, 54), (Sum.inr 1094, 18), (Sum.inr 1219, 108), (Sum.inr 1245, 54), (Sum.inr 1246, 54), (Sum.inr 1273, 54), (Sum.inr 1310, 18)]

def numericRow1265 : Integer.Sparse Master := [(Sum.inr 3301, 3), (Sum.inr 3311, 1), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

def numericRow1266 : Integer.Sparse Master := [(Sum.inl 0, 6), (Sum.inl 5, -5), (Sum.inl 8, -20), (Sum.inl 1, -5), (Sum.inr 614, -180), (Sum.inr 619, -120), (Sum.inr 1139, -360), (Sum.inr 1144, -360), (Sum.inr 1536, -180), (Sum.inr 1538, -120), (Sum.inr 3274, -360), (Sum.inr 3276, -360), (Sum.inr 3309, -360), (Sum.inr 3310, -120), (Sum.inr 3616, -180)]

def numericRow1267 : Integer.Sparse Master := [(Sum.inl 0, -6), (Sum.inl 5, 5), (Sum.inl 8, 20), (Sum.inl 1, 5), (Sum.inr 614, 180), (Sum.inr 619, 120), (Sum.inr 1139, 360), (Sum.inr 1144, 360)]

def numericRow1268 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, 5), (Sum.inl 7, 20), (Sum.inl 1, 10), (Sum.inr 1050, -540), (Sum.inr 1246, -1080), (Sum.inr 1751, -540), (Sum.inr 3301, -1080), (Sum.inr 3311, -180), (Sum.inr 4593, 2160)]

def numericRow1269 : Integer.Sparse Master := [(Sum.inl 0, -9), (Sum.inl 5, -50), (Sum.inl 8, 40), (Sum.inl 1, -5), (Sum.inr 1050, 360), (Sum.inr 1220, 720), (Sum.inr 1246, 720)]

def numericRow1270 : Integer.Sparse Master := [(Sum.inr 1751, 3), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

def numericRow1271 : Integer.Sparse Master := [(Sum.inr 1134, -2), (Sum.inr 1144, -1), (Sum.inr 1145, -1), (Sum.inr 1236, -2), (Sum.inr 1242, -1), (Sum.inr 1294, -1), (Sum.inr 2561, -2), (Sum.inr 2743, -1), (Sum.inr 3265, -2), (Sum.inr 3276, -1), (Sum.inr 3277, -1), (Sum.inr 3293, -2), (Sum.inr 3300, -1), (Sum.inr 3305, -1), (Sum.inr 3522, -2), (Sum.inr 3548, -1), (Sum.inr 4158, 8), (Sum.inr 4160, 4), (Sum.inr 4161, 4), (Sum.inr 4188, 4), (Sum.inr 4533, 8), (Sum.inr 4534, 8), (Sum.inr 4535, 8), (Sum.inr 4556, 8), (Sum.inr 4603, 8), (Sum.inr 4609, 4), (Sum.inr 4620, 4)]

def numericRow1272 : Integer.Sparse Master := [(Sum.inl 0, -26), (Sum.inl 5, 40), (Sum.inl 2, -15), (Sum.inl 7, -40), (Sum.inl 8, -40), (Sum.inl 1, 15), (Sum.inr 586, 720), (Sum.inr 588, 360), (Sum.inr 589, 360), (Sum.inr 616, 360), (Sum.inr 1117, 720), (Sum.inr 1119, 720), (Sum.inr 1120, 720), (Sum.inr 1141, 720), (Sum.inr 1262, 720), (Sum.inr 1264, 360), (Sum.inr 1295, 360)]

def numericRow1273 : Integer.Sparse Master := [(Sum.inr 1522, 2), (Sum.inr 1523, 1), (Sum.inr 1526, 1), (Sum.inr 1533, 1), (Sum.inr 3265, 2), (Sum.inr 3267, 2), (Sum.inr 3268, 2), (Sum.inr 3271, 2), (Sum.inr 3272, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 3293, 2), (Sum.inr 3294, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 3522, 2), (Sum.inr 3548, 1)]

def numericRow1274 : Integer.Sparse Master := [(Sum.inr 627, 2), (Sum.inr 635, 1), (Sum.inr 636, 1), (Sum.inr 642, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

def numericRow1275 : Integer.Sparse Master := [(Sum.inr 627, 1), (Sum.inr 1134, 1), (Sum.inr 1149, 1), (Sum.inr 1236, 1), (Sum.inr 1237, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

def numericRow1276 : Integer.Sparse Master := [(Sum.inr 1149, 1), (Sum.inr 1154, 1), (Sum.inr 1155, 1), (Sum.inr 1160, 1), (Sum.inr 1246, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

def numericRow1277 : Integer.Sparse Master := [(Sum.inr 642, 1), (Sum.inr 1160, 2), (Sum.inr 1246, 1), (Sum.inr 1294, 1), (Sum.inr 1295, 1), (Sum.inr 4092, -1)]

def numericRow1278 : Integer.Sparse Master := [(Sum.inl 0, 77), (Sum.inl 6, 10), (Sum.inl 2, -55), (Sum.inl 7, -80), (Sum.inl 8, -80), (Sum.inl 3, -80), (Sum.inl 1, -50), (Sum.inr 573, -4320), (Sum.inr 575, -2160), (Sum.inr 576, -2160), (Sum.inr 608, -2160), (Sum.inr 1102, -4320), (Sum.inr 1103, -2160), (Sum.inr 1104, -2160), (Sum.inr 1108, -4320), (Sum.inr 1109, -4320), (Sum.inr 1110, -4320), (Sum.inr 1134, -4320), (Sum.inr 1236, -4320), (Sum.inr 1239, -2160), (Sum.inr 1240, -4320), (Sum.inr 1242, -2160), (Sum.inr 1493, -4320), (Sum.inr 1495, -2160), (Sum.inr 1496, -2160), (Sum.inr 1519, -2160), (Sum.inr 1849, -4320), (Sum.inr 1858, -2160), (Sum.inr 2226, -2160), (Sum.inr 2889, -2160), (Sum.inr 2931, -4320), (Sum.inr 3236, -4320), (Sum.inr 3237, -2160), (Sum.inr 3251, -4320), (Sum.inr 3252, -4320), (Sum.inr 3265, -4320), (Sum.inr 3293, -4320), (Sum.inr 3299, -4320), (Sum.inr 3300, -2160), (Sum.inr 3308, -2160), (Sum.inr 3309, -2160), (Sum.inr 3612, -4320), (Sum.inr 3627, -2160), (Sum.inr 3631, -2160), (Sum.inr 3632, -2160)]

def numericRow1279 : Integer.Sparse Master := [(Sum.inl 0, -77), (Sum.inl 6, -10), (Sum.inl 2, 55), (Sum.inl 7, 80), (Sum.inl 8, 80), (Sum.inl 3, 80), (Sum.inl 1, 50), (Sum.inr 573, 4320), (Sum.inr 575, 2160), (Sum.inr 576, 2160), (Sum.inr 608, 2160), (Sum.inr 1102, 4320), (Sum.inr 1103, 2160), (Sum.inr 1104, 2160), (Sum.inr 1108, 4320), (Sum.inr 1109, 4320), (Sum.inr 1110, 4320), (Sum.inr 1134, 4320), (Sum.inr 1236, 4320), (Sum.inr 1239, 2160), (Sum.inr 1240, 4320), (Sum.inr 1242, 2160), (Sum.inr 2889, 2160), (Sum.inr 2931, 4320)]

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

def numericRow128 : Integer.Sparse Master := [(Sum.inr 1080, 1), (Sum.inr 2052, 2), (Sum.inr 2290, 1), (Sum.inr 4085, -1)]

def numericRow129 : Integer.Sparse Master := [(Sum.inr 1242, -1), (Sum.inr 2482, -2), (Sum.inr 2722, -2), (Sum.inr 2765, -1), (Sum.inr 3300, -1), (Sum.inr 3468, -2), (Sum.inr 3533, -2), (Sum.inr 3582, -1), (Sum.inr 4591, 8), (Sum.inr 4594, 2), (Sum.inr 4609, 4), (Sum.inr 5147, 8), (Sum.inr 5201, 2)]

def numericRow130 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, 5), (Sum.inl 1, 5), (Sum.inr 1217, 180), (Sum.inr 1221, 45), (Sum.inr 1243, 90), (Sum.inr 2865, 180), (Sum.inr 2886, 45)]

def numericRow131 : Integer.Sparse Master := [(Sum.inr 3291, 4), (Sum.inr 3298, 1), (Sum.inr 3300, 2), (Sum.inr 3302, 2), (Sum.inr 3468, 4), (Sum.inr 3530, 4), (Sum.inr 3533, 4), (Sum.inr 3579, 1), (Sum.inr 3582, 2)]

def numericRow132 : Integer.Sparse Master := [(Sum.inr 2722, 2), (Sum.inr 2726, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

def numericRow133 : Integer.Sparse Master := [(Sum.inr 1215, 2), (Sum.inr 1221, 1), (Sum.inr 1242, 1), (Sum.inr 1264, 1), (Sum.inr 2726, 1), (Sum.inr 4092, -1)]

def numericRow134 : Integer.Sparse Master := [(Sum.inr 1242, 1), (Sum.inr 2482, 2), (Sum.inr 2726, 1), (Sum.inr 4092, -1)]

def numericRow135 : Integer.Sparse Master := [(Sum.inr 1264, 1), (Sum.inr 2569, 2), (Sum.inr 2635, 1), (Sum.inr 2726, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

def numericRow136 : Integer.Sparse Master := [(Sum.inr 1215, 1), (Sum.inr 2482, 1), (Sum.inr 2569, 1), (Sum.inr 2722, 1), (Sum.inr 2726, 1), (Sum.inr 4092, -1)]

def numericRow137 : Integer.Sparse Master := [(Sum.inl 0, 23), (Sum.inl 5, 4), (Sum.inl 6, 1), (Sum.inl 2, -12), (Sum.inl 1, 56), (Sum.inr 982, -1728), (Sum.inr 986, -432), (Sum.inr 1009, -864), (Sum.inr 1043, -864), (Sum.inr 1617, -1728), (Sum.inr 1620, -432), (Sum.inr 1630, -864), (Sum.inr 1725, -864), (Sum.inr 2385, -1728), (Sum.inr 2407, -432), (Sum.inr 2449, -864), (Sum.inr 2482, -1728), (Sum.inr 2723, -1728), (Sum.inr 2743, -864), (Sum.inr 3353, -1728), (Sum.inr 3360, -432), (Sum.inr 3432, -864), (Sum.inr 3468, -1728), (Sum.inr 3544, -1728), (Sum.inr 3548, -864), (Sum.inr 3608, -432), (Sum.inr 3627, -864)]

def numericRow138 : Integer.Sparse Master := [(Sum.inl 0, -91), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 2, 60), (Sum.inl 1, -160), (Sum.inr 982, 8640), (Sum.inr 986, 2160), (Sum.inr 1009, 4320), (Sum.inr 1043, 4320), (Sum.inr 2385, 8640), (Sum.inr 2407, 2160), (Sum.inr 2449, 4320), (Sum.inr 2482, 8640), (Sum.inr 2723, 8640), (Sum.inr 2743, 4320)]

def numericRow139 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 2052, -240), (Sum.inr 2065, -120), (Sum.inr 2193, -240), (Sum.inr 2218, -120), (Sum.inr 2726, -300), (Sum.inr 3545, -300), (Sum.inr 3634, -120), (Sum.inr 5222, 960), (Sum.inr 5235, 240), (Sum.inr 5252, 960), (Sum.inr 5268, 480)]

def numericRow140 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 2, -5), (Sum.inr 2193, 160), (Sum.inr 2218, 80), (Sum.inr 2664, 160), (Sum.inr 2680, 40), (Sum.inr 2712, 160), (Sum.inr 2726, 160), (Sum.inr 2734, 80)]

def numericRow141 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 2, -5), (Sum.inr 2712, 40), (Sum.inr 2726, 10), (Sum.inr 2734, 20), (Sum.inr 3031, 40), (Sum.inr 3046, 10)]

def numericRow142 : Integer.Sparse Master := [(Sum.inr 2052, 2), (Sum.inr 2065, 1), (Sum.inr 3545, 1), (Sum.inr 4085, -1)]

def numericRow143 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, 5), (Sum.inr 3310, -240), (Sum.inr 3313, -30), (Sum.inr 3608, -360)]

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

def numericRow1280 : Integer.Sparse Master := [(Sum.inr 1192, 1), (Sum.inr 2410, 1), (Sum.inr 2538, 2), (Sum.inr 2685, 1), (Sum.inr 2687, 1), (Sum.inr 4082, -1)]

def numericRow1281 : Integer.Sparse Master := [(Sum.inr 1193, 1), (Sum.inr 2539, 2), (Sum.inr 2686, 2), (Sum.inr 4089, -1)]

def numericRow1282 : Integer.Sparse Master := [(Sum.inr 1099, 2), (Sum.inr 1104, 2), (Sum.inr 1193, 1), (Sum.inr 4089, -1)]

def numericRow1283 : Integer.Sparse Master := [(Sum.inr 1204, 1), (Sum.inr 2467, 2), (Sum.inr 2704, 1), (Sum.inr 2706, 1), (Sum.inr 4080, -1)]

def numericRow1284 : Integer.Sparse Master := [(Sum.inr 1205, 1), (Sum.inr 2541, 1), (Sum.inr 2705, 2), (Sum.inr 4088, -1)]

def numericRow1285 : Integer.Sparse Master := [(Sum.inr 1106, 1), (Sum.inr 1110, 2), (Sum.inr 1124, 1), (Sum.inr 1205, 1), (Sum.inr 4088, -1)]

def numericRow1286 : Integer.Sparse Master := [(Sum.inr 1062, 1), (Sum.inr 2038, 2), (Sum.inr 2137, 1), (Sum.inr 2276, 1), (Sum.inr 2280, 1), (Sum.inr 4082, -1)]

def numericRow1287 : Integer.Sparse Master := [(Sum.inr 992, 1), (Sum.inr 1928, 1), (Sum.inr 1993, 1), (Sum.inr 2122, 1), (Sum.inr 2215, 1), (Sum.inr 2217, 1), (Sum.inr 4082, -1)]

def numericRow1288 : Integer.Sparse Master := [(Sum.inr 993, 1), (Sum.inr 1929, 1), (Sum.inr 1994, 1), (Sum.inr 2123, 1), (Sum.inr 2216, 2), (Sum.inr 4080, -1)]

def numericRow1289 : Integer.Sparse Master := [(Sum.inr 1025, 1), (Sum.inr 2011, 1), (Sum.inr 2093, 2), (Sum.inr 2242, 1), (Sum.inr 2246, 1), (Sum.inr 4080, -1)]

def numericRow1290 : Integer.Sparse Master := [(Sum.inr 973, 1), (Sum.inr 1900, 1), (Sum.inr 2072, 2), (Sum.inr 2190, 1), (Sum.inr 2192, 1), (Sum.inr 4080, -1)]

def numericRow1291 : Integer.Sparse Master := [(Sum.inr 1901, 1), (Sum.inr 2073, 2), (Sum.inr 2191, 2), (Sum.inr 4079, -1)]

def numericRow1292 : Integer.Sparse Master := [(Sum.inr 1048, 1), (Sum.inr 2027, 2), (Sum.inr 2114, 1), (Sum.inr 2261, 1), (Sum.inr 2267, 1), (Sum.inr 4081, -1)]

def numericRow1293 : Integer.Sparse Master := [(Sum.inr 613, -1), (Sum.inr 932, -2), (Sum.inr 1040, -2), (Sum.inr 1043, -1), (Sum.inr 1087, -1), (Sum.inr 1525, -1), (Sum.inr 1681, -2), (Sum.inr 1707, -2), (Sum.inr 1725, -1), (Sum.inr 1739, -1), (Sum.inr 2028, -2), (Sum.inr 2115, -1), (Sum.inr 2215, -2), (Sum.inr 2266, -1), (Sum.inr 2276, -1), (Sum.inr 2278, -1), (Sum.inr 4154, 8), (Sum.inr 4160, 4), (Sum.inr 4162, 4), (Sum.inr 4328, 8), (Sum.inr 4334, 8), (Sum.inr 4336, 8), (Sum.inr 4368, 8), (Sum.inr 4373, 4), (Sum.inr 4375, 4), (Sum.inr 4459, 8), (Sum.inr 4464, 4)]

def numericRow1294 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 5, 160), (Sum.inl 2, 140), (Sum.inl 7, -160), (Sum.inl 35, -160), (Sum.inl 1, 110), (Sum.inr 631, 2880), (Sum.inr 634, 1440), (Sum.inr 636, 1440), (Sum.inr 1321, 2880), (Sum.inr 1323, 1440), (Sum.inr 1325, 1440), (Sum.inr 1330, 2880), (Sum.inr 1332, 2880), (Sum.inr 1334, 2880), (Sum.inr 1406, 2880), (Sum.inr 1408, 1440)]

def numericRow1295 : Integer.Sparse Master := [(Sum.inr 1511, 2), (Sum.inr 1523, 1), (Sum.inr 1525, 1), (Sum.inr 1529, 1), (Sum.inr 1667, 2), (Sum.inr 1679, 2), (Sum.inr 1681, 2), (Sum.inr 1685, 2), (Sum.inr 1707, 2), (Sum.inr 1712, 2), (Sum.inr 1714, 2), (Sum.inr 1725, 1), (Sum.inr 1735, 1), (Sum.inr 1739, 1), (Sum.inr 1743, 1), (Sum.inr 1745, 1), (Sum.inr 2215, 2), (Sum.inr 2276, 1), (Sum.inr 2278, 1)]

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

def numericRow1296 : Integer.Sparse Master := [(Sum.inr 582, 2), (Sum.inr 588, 1), (Sum.inr 590, 1), (Sum.inr 613, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

def numericRow1297 : Integer.Sparse Master := [(Sum.inr 613, 1), (Sum.inr 932, 2), (Sum.inr 1049, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

def numericRow1298 : Integer.Sparse Master := [(Sum.inr 946, 2), (Sum.inr 952, 1), (Sum.inr 954, 1), (Sum.inr 1049, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

def numericRow1299 : Integer.Sparse Master := [(Sum.inr 582, 1), (Sum.inr 906, 1), (Sum.inr 946, 1), (Sum.inr 1040, 1), (Sum.inr 1042, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

def numericRow1300 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 5, -10), (Sum.inl 2, -10), (Sum.inl 7, -40), (Sum.inl 3, -80), (Sum.inl 1, 15), (Sum.inr 543, -2160), (Sum.inr 546, -1080), (Sum.inr 548, -1080), (Sum.inr 562, -1080), (Sum.inr 675, -2160), (Sum.inr 676, -1080), (Sum.inr 679, -1080), (Sum.inr 685, -1080), (Sum.inr 869, -2160), (Sum.inr 872, -2160), (Sum.inr 874, -2160), (Sum.inr 891, -2160), (Sum.inr 932, -2160), (Sum.inr 937, -1080), (Sum.inr 939, -1080), (Sum.inr 1035, -2160), (Sum.inr 1037, -1080), (Sum.inr 1044, -2160), (Sum.inr 1046, -1080), (Sum.inr 1075, -1080), (Sum.inr 1087, -1080), (Sum.inr 1561, -2160), (Sum.inr 1562, -2160), (Sum.inr 1565, -2160), (Sum.inr 1570, -2160), (Sum.inr 1645, -2160), (Sum.inr 1647, -1080), (Sum.inr 1653, -1080), (Sum.inr 1681, -2160), (Sum.inr 1683, -1080), (Sum.inr 1694, -1080), (Sum.inr 1737, -2160), (Sum.inr 1739, -1080), (Sum.inr 1750, -1080), (Sum.inr 2488, -2160), (Sum.inr 2765, -1080), (Sum.inr 3478, -2160), (Sum.inr 3582, -1080), (Sum.inr 3614, -1080), (Sum.inr 3632, -1080)]

def numericRow1301 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 5, 10), (Sum.inl 2, 10), (Sum.inl 7, 40), (Sum.inl 3, 80), (Sum.inl 1, -15), (Sum.inr 543, 2160), (Sum.inr 546, 1080), (Sum.inr 548, 1080), (Sum.inr 562, 1080), (Sum.inr 869, 2160), (Sum.inr 872, 2160), (Sum.inr 874, 2160), (Sum.inr 891, 2160), (Sum.inr 932, 2160), (Sum.inr 937, 1080), (Sum.inr 939, 1080), (Sum.inr 1035, 2160), (Sum.inr 1037, 1080), (Sum.inr 1044, 2160), (Sum.inr 1046, 1080), (Sum.inr 1075, 1080), (Sum.inr 1087, 1080), (Sum.inr 2488, 2160), (Sum.inr 2765, 1080)]

def numericRow1302 : Integer.Sparse Master := [(Sum.inr 614, -1), (Sum.inr 933, -2), (Sum.inr 1041, -4), (Sum.inr 1046, -2), (Sum.inr 1536, -1), (Sum.inr 1691, -2), (Sum.inr 1724, -4), (Sum.inr 1750, -2), (Sum.inr 2029, -2), (Sum.inr 2116, -1), (Sum.inr 2225, -2), (Sum.inr 2288, -1), (Sum.inr 4155, 8), (Sum.inr 4161, 8), (Sum.inr 4335, 16), (Sum.inr 4369, 8), (Sum.inr 4374, 8)]

def numericRow1303 : Integer.Sparse Master := [(Sum.inl 0, -12), (Sum.inl 5, 25), (Sum.inl 2, -15), (Sum.inl 8, -20), (Sum.inl 1, -20), (Sum.inr 632, 270), (Sum.inr 635, 270), (Sum.inr 1322, 270), (Sum.inr 1324, 270), (Sum.inr 1333, 540)]

def numericRow1304 : Integer.Sparse Master := [(Sum.inr 1515, 2), (Sum.inr 1533, 2), (Sum.inr 1536, 1), (Sum.inr 1689, 4), (Sum.inr 1691, 2), (Sum.inr 1721, 2), (Sum.inr 1724, 4), (Sum.inr 1748, 2), (Sum.inr 1750, 2), (Sum.inr 2225, 2), (Sum.inr 2288, 1)]

def numericRow1305 : Integer.Sparse Master := [(Sum.inr 583, 2), (Sum.inr 589, 2), (Sum.inr 614, 1), (Sum.inr 1050, 1), (Sum.inr 4083, -1)]

def numericRow1306 : Integer.Sparse Master := [(Sum.inr 614, 1), (Sum.inr 933, 2), (Sum.inr 1050, 1), (Sum.inr 4083, -1)]

def numericRow1307 : Integer.Sparse Master := [(Sum.inr 947, 2), (Sum.inr 953, 2), (Sum.inr 1050, 1), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

def numericRow1308 : Integer.Sparse Master := [(Sum.inr 583, 1), (Sum.inr 947, 1), (Sum.inr 1041, 2), (Sum.inr 1050, 1), (Sum.inr 4083, -1)]

def numericRow1309 : Integer.Sparse Master := [(Sum.inl 0, 18), (Sum.inl 5, -5), (Sum.inl 2, -15), (Sum.inl 8, -20), (Sum.inl 1, -20), (Sum.inr 544, -1080), (Sum.inr 547, -1080), (Sum.inr 563, -540), (Sum.inr 682, -1080), (Sum.inr 684, -1080), (Sum.inr 692, -540), (Sum.inr 870, -1080), (Sum.inr 873, -2160), (Sum.inr 892, -1080), (Sum.inr 933, -1080), (Sum.inr 938, -1080), (Sum.inr 1041, -2160), (Sum.inr 1043, -1080), (Sum.inr 1083, -1080), (Sum.inr 1567, -1080), (Sum.inr 1569, -2160), (Sum.inr 1575, -1080), (Sum.inr 1691, -1080), (Sum.inr 1693, -1080), (Sum.inr 1724, -2160), (Sum.inr 1725, -1080), (Sum.inr 1728, -1080), (Sum.inr 2489, -1080), (Sum.inr 3482, -1080), (Sum.inr 3616, -540), (Sum.inr 3627, -1080)]

def numericRow1310 : Integer.Sparse Master := [(Sum.inl 0, 3), (Sum.inl 5, 10), (Sum.inl 8, 40), (Sum.inl 1, -5), (Sum.inr 790, -720), (Sum.inr 831, -360), (Sum.inr 848, -720), (Sum.inr 858, -360), (Sum.inr 985, -1440), (Sum.inr 1049, -720), (Sum.inr 1050, -720), (Sum.inr 1246, -720), (Sum.inr 1618, -1440), (Sum.inr 1738, -720), (Sum.inr 1751, -720), (Sum.inr 3301, -720), (Sum.inr 3312, -360), (Sum.inr 4412, 2880), (Sum.inr 4444, 5760), (Sum.inr 4480, 2880), (Sum.inr 4593, 2880)]

def numericRow1311 : Integer.Sparse Master := [(Sum.inl 0, -23), (Sum.inl 5, -110), (Sum.inl 7, 80), (Sum.inl 8, -40), (Sum.inl 1, 45), (Sum.inr 790, 2160), (Sum.inr 831, 1080), (Sum.inr 985, 4320), (Sum.inr 993, 2160), (Sum.inr 1026, 4320), (Sum.inr 1049, 2160), (Sum.inr 1050, 2160), (Sum.inr 1063, 2160), (Sum.inr 1220, 2160)]

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

def numericRow1312 : Integer.Sparse Master := [(Sum.inl 0, -27), (Sum.inl 5, -130), (Sum.inl 8, -40), (Sum.inl 1, 5), (Sum.inr 1220, 540), (Sum.inr 1246, 540), (Sum.inr 1363, 540), (Sum.inr 1375, 540), (Sum.inr 1391, 1080)]

def numericRow1313 : Integer.Sparse Master := [(Sum.inr 984, 1), (Sum.inr 1917, 1), (Sum.inr 1989, 1), (Sum.inr 2081, 1), (Sum.inr 2203, 1), (Sum.inr 2207, 1), (Sum.inr 4081, -1)]

def numericRow1314 : Integer.Sparse Master := [(Sum.inr 985, 1), (Sum.inr 1990, 1), (Sum.inr 2082, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

def numericRow1315 : Integer.Sparse Master := [(Sum.inr 866, 1), (Sum.inr 873, 1), (Sum.inr 874, 1), (Sum.inr 985, 1), (Sum.inr 4080, -1)]

def numericRow1316 : Integer.Sparse Master := [(Sum.inr 710, 1), (Sum.inr 715, 1), (Sum.inr 724, 1), (Sum.inr 1618, 1), (Sum.inr 4071, -1)]

def numericRow1317 : Integer.Sparse Master := [(Sum.inr 618, -1), (Sum.inr 937, -3), (Sum.inr 1080, -3), (Sum.inr 1527, -1), (Sum.inr 1683, -3), (Sum.inr 1710, -3), (Sum.inr 2065, -3), (Sum.inr 2218, -3), (Sum.inr 2281, -1), (Sum.inr 2294, -1), (Sum.inr 4179, 12), (Sum.inr 4193, 4), (Sum.inr 4348, 24), (Sum.inr 4362, 12), (Sum.inr 4500, 12), (Sum.inr 4508, 4)]

def numericRow1318 : Integer.Sparse Master := [(Sum.inl 0, -38), (Sum.inl 5, 40), (Sum.inl 2, -200), (Sum.inl 35, 160), (Sum.inl 1, -10), (Sum.inr 653, 1440), (Sum.inr 654, 480), (Sum.inr 1347, 2880), (Sum.inr 1348, 1440), (Sum.inr 1436, 1440), (Sum.inr 1438, 480)]

def numericRow1319 : Integer.Sparse Master := [(Sum.inr 1513, 3), (Sum.inr 1527, 1), (Sum.inr 1531, 1), (Sum.inr 1669, 6), (Sum.inr 1683, 3), (Sum.inr 1687, 3), (Sum.inr 1710, 3), (Sum.inr 1716, 3), (Sum.inr 1747, 1), (Sum.inr 2218, 3), (Sum.inr 2281, 1)]

def numericRow1320 : Integer.Sparse Master := [(Sum.inr 607, 3), (Sum.inr 618, 1), (Sum.inr 621, 1), (Sum.inr 1094, 1), (Sum.inr 4085, -1)]

def numericRow1321 : Integer.Sparse Master := [(Sum.inr 608, -3), (Sum.inr 619, -1), (Sum.inr 620, -1), (Sum.inr 927, -6), (Sum.inr 938, -3), (Sum.inr 939, -3), (Sum.inr 1083, -3), (Sum.inr 1091, -1), (Sum.inr 1519, -3), (Sum.inr 1538, -1), (Sum.inr 1539, -1), (Sum.inr 1675, -6), (Sum.inr 1693, -3), (Sum.inr 1694, -3), (Sum.inr 1728, -3), (Sum.inr 1756, -1), (Sum.inr 4084, 4)]

def numericRow1322 : Integer.Sparse Master := [(Sum.inr 1519, 3), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 1675, 6), (Sum.inr 1693, 3), (Sum.inr 1694, 3), (Sum.inr 1728, 3), (Sum.inr 1756, 1), (Sum.inr 4084, 1)]

def numericRow1323 : Integer.Sparse Master := [(Sum.inr 608, 3), (Sum.inr 619, 1), (Sum.inr 620, 1), (Sum.inr 4084, -1)]

def numericRow1324 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, 4), (Sum.inl 7, 8), (Sum.inl 8, 8), (Sum.inl 1, 3), (Sum.inr 985, -432), (Sum.inr 1012, -216), (Sum.inr 1049, -216), (Sum.inr 1050, -216), (Sum.inr 1094, -72), (Sum.inr 1246, -216), (Sum.inr 1618, -432), (Sum.inr 1627, -216), (Sum.inr 1738, -216), (Sum.inr 1741, -72), (Sum.inr 1751, -216), (Sum.inr 3301, -216), (Sum.inr 3311, -72), (Sum.inr 3312, -72), (Sum.inr 4071, 288)]

def numericRow1325 : Integer.Sparse Master := [(Sum.inr 1012, 1), (Sum.inr 2006, 2), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

def numericRow1326 : Integer.Sparse Master := [(Sum.inr 569, -2), (Sum.inr 576, -2), (Sum.inr 595, -1), (Sum.inr 899, -2), (Sum.inr 903, -4), (Sum.inr 917, -2), (Sum.inr 1000, -4), (Sum.inr 1009, -2), (Sum.inr 1075, -2), (Sum.inr 1490, -2), (Sum.inr 1496, -2), (Sum.inr 1500, -1), (Sum.inr 1587, -2), (Sum.inr 1591, -4), (Sum.inr 1605, -4), (Sum.inr 1630, -2), (Sum.inr 1634, -2), (Sum.inr 1653, -2), (Sum.inr 4082, 4)]

def numericRow1327 : Integer.Sparse Master := [(Sum.inr 569, 2), (Sum.inr 576, 2), (Sum.inr 595, 1), (Sum.inr 4082, -1)]

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

def numericRow1328 : Integer.Sparse Master := [(Sum.inr 562, 1), (Sum.inr 724, 2), (Sum.inr 830, 1), (Sum.inr 858, 1), (Sum.inr 4071, -1)]

def numericRow1329 : Integer.Sparse Master := [(Sum.inr 831, 1), (Sum.inr 1612, 2), (Sum.inr 1661, 1), (Sum.inr 1739, 2), (Sum.inr 4069, -1)]

def numericRow1330 : Integer.Sparse Master := [(Sum.inr 789, 1), (Sum.inr 1594, 1), (Sum.inr 1640, 2), (Sum.inr 1707, 1), (Sum.inr 1709, 1), (Sum.inr 4069, -1)]

def numericRow1331 : Integer.Sparse Master := [(Sum.inr 543, 1), (Sum.inr 703, 1), (Sum.inr 738, 1), (Sum.inr 789, 1), (Sum.inr 811, 1), (Sum.inr 4069, -1)]

def numericRow1332 : Integer.Sparse Master := [(Sum.inr 552, 1), (Sum.inr 710, 1), (Sum.inr 823, 1), (Sum.inr 848, 1), (Sum.inr 4071, -1)]

def numericRow1333 : Integer.Sparse Master := [(Sum.inr 790, 1), (Sum.inr 1641, 2), (Sum.inr 1708, 2), (Sum.inr 4068, -1)]

def numericRow1334 : Integer.Sparse Master := [(Sum.inr 544, 1), (Sum.inr 704, 1), (Sum.inr 739, 1), (Sum.inr 790, 1), (Sum.inr 4068, -1)]

def numericRow1335 : Integer.Sparse Master := [(Sum.inr 539, -2), (Sum.inr 547, -1), (Sum.inr 548, -1), (Sum.inr 664, -2), (Sum.inr 684, -1), (Sum.inr 685, -1), (Sum.inr 700, -2), (Sum.inr 707, -2), (Sum.inr 708, -2), (Sum.inr 734, -2), (Sum.inr 742, -1), (Sum.inr 743, -1), (Sum.inr 749, -2), (Sum.inr 763, -2), (Sum.inr 764, -2), (Sum.inr 800, -2), (Sum.inr 807, -4), (Sum.inr 813, -1), (Sum.inr 843, -1), (Sum.inr 844, -1), (Sum.inr 853, -1), (Sum.inr 1000, -2), (Sum.inr 1075, -1), (Sum.inr 1083, -1), (Sum.inr 1605, -2), (Sum.inr 1653, -1), (Sum.inr 1728, -1), (Sum.inr 4069, 4)]

def numericRow1336 : Integer.Sparse Master := [(Sum.inr 664, 2), (Sum.inr 684, 1), (Sum.inr 685, 1), (Sum.inr 749, 2), (Sum.inr 763, 2), (Sum.inr 764, 2), (Sum.inr 800, 2), (Sum.inr 807, 2), (Sum.inr 843, 1), (Sum.inr 844, 1), (Sum.inr 853, 1), (Sum.inr 1000, 2), (Sum.inr 1075, 1), (Sum.inr 1083, 1), (Sum.inr 4069, 1)]

def numericRow1337 : Integer.Sparse Master := [(Sum.inr 1605, 2), (Sum.inr 1653, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

def numericRow1338 : Integer.Sparse Master := [(Sum.inr 539, 2), (Sum.inr 547, 1), (Sum.inr 548, 1), (Sum.inr 4069, -1)]

def numericRow1339 : Integer.Sparse Master := [(Sum.inr 734, 2), (Sum.inr 742, 1), (Sum.inr 743, 1), (Sum.inr 1653, 1), (Sum.inr 4069, -1)]

def numericRow1340 : Integer.Sparse Master := [(Sum.inr 552, -2), (Sum.inr 555, -1), (Sum.inr 562, -1), (Sum.inr 660, -2), (Sum.inr 671, -1), (Sum.inr 679, -1), (Sum.inr 710, -2), (Sum.inr 715, -2), (Sum.inr 724, -2), (Sum.inr 746, -2), (Sum.inr 753, -2), (Sum.inr 758, -2), (Sum.inr 789, -2), (Sum.inr 790, -2), (Sum.inr 815, -1), (Sum.inr 823, -2), (Sum.inr 826, -1), (Sum.inr 830, -2), (Sum.inr 831, -1), (Sum.inr 848, -2), (Sum.inr 858, -1), (Sum.inr 985, -2), (Sum.inr 1049, -1), (Sum.inr 1050, -1), (Sum.inr 1618, -2), (Sum.inr 1738, -1), (Sum.inr 1751, -1), (Sum.inr 4071, 4)]

def numericRow1341 : Integer.Sparse Master := [(Sum.inr 4059, 3), (Sum.inr 4061, 2), (Sum.inr 4065, 6), (Sum.inr 4067, 6), (Sum.inr 4069, 6), (Sum.inr 4070, 2), (Sum.inr 4082, 3), (Sum.inr 4084, 2)]

def numericRow1342 : Integer.Sparse Master := [(Sum.inr 1716, 1), (Sum.inr 2521, 1), (Sum.inr 3022, 2), (Sum.inr 3049, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

def numericRow1343 : Integer.Sparse Master := [(Sum.inr 1714, 2), (Sum.inr 1716, 1), (Sum.inr 1728, 1), (Sum.inr 1739, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

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

def numericRow1344 : Integer.Sparse Master := [(Sum.inr 604, 1), (Sum.inr 923, 1), (Sum.inr 1042, 1), (Sum.inr 1058, 1), (Sum.inr 1079, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

def numericRow1345 : Integer.Sparse Master := [(Sum.inr 1335, 1), (Sum.inr 1337, 1), (Sum.inr 1338, 1), (Sum.inr 1347, 1), (Sum.inr 1406, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

def numericRow1346 : Integer.Sparse Master := [(Sum.inr 1714, 1), (Sum.inr 2502, 1), (Sum.inr 3285, 1), (Sum.inr 3287, 1), (Sum.inr 3293, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

def numericRow1347 : Integer.Sparse Master := [(Sum.inr 824, 1), (Sum.inr 1607, 1), (Sum.inr 1656, 1), (Sum.inr 1714, 1), (Sum.inr 1737, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

def numericRow1348 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 1714, 1), (Sum.inr 1715, 1), (Sum.inr 1724, 1), (Sum.inr 1737, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

def numericRow1349 : Integer.Sparse Master := [(Sum.inr 807, 1), (Sum.inr 1646, 1), (Sum.inr 1714, 1), (Sum.inr 1724, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

def numericRow1350 : Integer.Sparse Master := [(Sum.inr 601, 1), (Sum.inr 1057, 1), (Sum.inr 1079, 1), (Sum.inr 1083, 2), (Sum.inr 4084, -1)]

def numericRow1351 : Integer.Sparse Master := [(Sum.inr 1316, 1), (Sum.inr 1320, 1), (Sum.inr 1322, 2), (Sum.inr 1370, 1), (Sum.inr 2884, 1), (Sum.inr 4091, -1)]

def numericRow1352 : Integer.Sparse Master := [(Sum.inr 1709, 1), (Sum.inr 3241, 1), (Sum.inr 3245, 1), (Sum.inr 3246, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

def numericRow1353 : Integer.Sparse Master := [(Sum.inr 1707, 1), (Sum.inr 1709, 1), (Sum.inr 1724, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

def numericRow1354 : Integer.Sparse Master := [(Sum.inr 811, 1), (Sum.inr 1601, 1), (Sum.inr 1649, 1), (Sum.inr 1709, 1), (Sum.inr 1715, 1), (Sum.inr 1724, 1), (Sum.inr 4069, -1)]

def numericRow1355 : Integer.Sparse Master := [(Sum.inr 1314, 1), (Sum.inr 1317, 1), (Sum.inr 1318, 1), (Sum.inr 1321, 1), (Sum.inr 1367, 1), (Sum.inr 2881, 1), (Sum.inr 4092, -1)]

def numericRow1356 : Integer.Sparse Master := [(Sum.inr 1715, 1), (Sum.inr 2466, 1), (Sum.inr 3238, 1), (Sum.inr 3240, 1), (Sum.inr 3245, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

def numericRow1357 : Integer.Sparse Master := [(Sum.inr 827, 1), (Sum.inr 1609, 1), (Sum.inr 1658, 1), (Sum.inr 1715, 2), (Sum.inr 1737, 1), (Sum.inr 4069, -1)]

def numericRow1358 : Integer.Sparse Master := [(Sum.inr 578, 1), (Sum.inr 942, 1), (Sum.inr 1039, 1), (Sum.inr 1041, 2), (Sum.inr 4083, -1)]

def numericRow1359 : Integer.Sparse Master := [(Sum.inr 3281, 1), (Sum.inr 3282, 2), (Sum.inr 3299, 2), (Sum.inr 4069, -1)]

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

def numericRow1360 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 784, 2), (Sum.inr 803, 2), (Sum.inr 4069, -1)]

def numericRow1361 : Integer.Sparse Master := [(Sum.inr 803, 1), (Sum.inr 1642, 1), (Sum.inr 1713, 1), (Sum.inr 1724, 2), (Sum.inr 4069, -1)]

def numericRow1362 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 1635, 2), (Sum.inr 1707, 2), (Sum.inr 4069, -1)]

def numericRow1363 : Integer.Sparse Master := [(Sum.inr 580, 1), (Sum.inr 944, 1), (Sum.inr 1021, 2), (Sum.inr 1039, 1), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

def numericRow1364 : Integer.Sparse Master := [(Sum.inr 1327, 1), (Sum.inr 1328, 1), (Sum.inr 1330, 1), (Sum.inr 1335, 1), (Sum.inr 1383, 1), (Sum.inr 2924, 1), (Sum.inr 4091, -1)]

def numericRow1365 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 2457, 1), (Sum.inr 3278, 1), (Sum.inr 3281, 1), (Sum.inr 3293, 2), (Sum.inr 4069, -1)]

def numericRow1366 : Integer.Sparse Master := [(Sum.inr 822, 1), (Sum.inr 1654, 1), (Sum.inr 1713, 2), (Sum.inr 1737, 2), (Sum.inr 4069, -1)]

def numericRow1367 : Integer.Sparse Master := [(Sum.inr 1125, 1), (Sum.inr 1128, 1), (Sum.inr 1133, 2), (Sum.inr 1234, 1), (Sum.inr 2509, 1), (Sum.inr 4084, -1)]

def numericRow1368 : Integer.Sparse Master := [(Sum.inr 651, 1), (Sum.inr 1169, 1), (Sum.inr 1270, 3), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

def numericRow1369 : Integer.Sparse Master := [(Sum.inr 1654, 1), (Sum.inr 1656, 2), (Sum.inr 1658, 1), (Sum.inr 1737, 1), (Sum.inr 2702, 1), (Sum.inr 4069, -1)]

def numericRow1370 : Integer.Sparse Master := [(Sum.inr 1710, 1), (Sum.inr 2702, 2), (Sum.inr 2737, 2), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

def numericRow1371 : Integer.Sparse Master := [(Sum.inr 1602, 1), (Sum.inr 2457, 1), (Sum.inr 2466, 1), (Sum.inr 2502, 1), (Sum.inr 2702, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

def numericRow1372 : Integer.Sparse Master := [(Sum.inr 1737, 1), (Sum.inr 2702, 1), (Sum.inr 3288, 1), (Sum.inr 3293, 2), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

def numericRow1373 : Integer.Sparse Master := [(Sum.inr 1127, 1), (Sum.inr 1132, 1), (Sum.inr 1134, 1), (Sum.inr 1141, 1), (Sum.inr 1237, 1), (Sum.inr 2512, 1), (Sum.inr 4092, -1)]

def numericRow1374 : Integer.Sparse Master := [(Sum.inr 640, 1), (Sum.inr 1158, 1), (Sum.inr 1240, 1), (Sum.inr 1262, 2), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

def numericRow1375 : Integer.Sparse Master := [(Sum.inr 1642, 1), (Sum.inr 1645, 1), (Sum.inr 1646, 1), (Sum.inr 1649, 1), (Sum.inr 1724, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

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

def numericRow1376 : Integer.Sparse Master := [(Sum.inr 1603, 1), (Sum.inr 1605, 1), (Sum.inr 1623, 1), (Sum.inr 1728, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

def numericRow1377 : Integer.Sparse Master := [(Sum.inr 1728, 1), (Sum.inr 3294, 2), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

def numericRow1378 : Integer.Sparse Master := [(Sum.inr 1623, 1), (Sum.inr 3246, 1), (Sum.inr 3282, 1), (Sum.inr 3294, 1), (Sum.inr 3296, 1), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

def numericRow1379 : Integer.Sparse Master := [(Sum.inr 1724, 1), (Sum.inr 3290, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 3299, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

def numericRow1380 : Integer.Sparse Master := [(Sum.inr 1605, 1), (Sum.inr 3240, 1), (Sum.inr 3278, 1), (Sum.inr 3287, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

def numericRow1381 : Integer.Sparse Master := [(Sum.inr 1645, 1), (Sum.inr 3022, 1), (Sum.inr 3285, 1), (Sum.inr 3294, 1), (Sum.inr 3296, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

def numericRow1382 : Integer.Sparse Master := [(Sum.inr 1257, 1), (Sum.inr 2565, 1), (Sum.inr 2629, 1), (Sum.inr 2672, 1), (Sum.inr 2748, 1), (Sum.inr 2760, 1), (Sum.inr 4088, -1)]

def numericRow1383 : Integer.Sparse Master := [(Sum.inr 1130, 1), (Sum.inr 1137, 1), (Sum.inr 1138, 1), (Sum.inr 1141, 1), (Sum.inr 1241, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

def numericRow1384 : Integer.Sparse Master := [(Sum.inr 638, 1), (Sum.inr 1156, 1), (Sum.inr 1236, 1), (Sum.inr 1261, 1), (Sum.inr 1291, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

def numericRow1385 : Integer.Sparse Master := [(Sum.inr 1635, 1), (Sum.inr 1637, 1), (Sum.inr 1640, 1), (Sum.inr 1645, 1), (Sum.inr 1707, 1), (Sum.inr 3296, 1), (Sum.inr 4069, -1)]

def numericRow1386 : Integer.Sparse Master := [(Sum.inr 1607, 1), (Sum.inr 1610, 1), (Sum.inr 1612, 1), (Sum.inr 1623, 1), (Sum.inr 1739, 1), (Sum.inr 3296, 1), (Sum.inr 4069, -1)]

def numericRow1387 : Integer.Sparse Master := [(Sum.inr 1739, 1), (Sum.inr 2737, 1), (Sum.inr 3296, 2), (Sum.inr 3305, 1), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

def numericRow1388 : Integer.Sparse Master := [(Sum.inr 1707, 1), (Sum.inr 3288, 1), (Sum.inr 3296, 2), (Sum.inr 3299, 1), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

def numericRow1389 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 1113, 2), (Sum.inr 1126, 1), (Sum.inr 1212, 1), (Sum.inr 2479, 1), (Sum.inr 4092, -1)]

def numericRow1390 : Integer.Sparse Master := [(Sum.inr 623, 1), (Sum.inr 1126, 1), (Sum.inr 1212, 1), (Sum.inr 1233, 1), (Sum.inr 1236, 2), (Sum.inr 4092, -1)]

def numericRow1391 : Integer.Sparse Master := [(Sum.inr 629, 1), (Sum.inr 1135, 1), (Sum.inr 1216, 3), (Sum.inr 1235, 1), (Sum.inr 4091, -1)]

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

def numericRow1392 : Integer.Sparse Master := [(Sum.inr 1116, 1), (Sum.inr 1117, 2), (Sum.inr 1135, 1), (Sum.inr 1216, 1), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

def numericRow1393 : Integer.Sparse Master := [(Sum.inr 1607, 2), (Sum.inr 1609, 1), (Sum.inr 1616, 1), (Sum.inr 1737, 1), (Sum.inr 3288, 1), (Sum.inr 4069, -1)]

def numericRow1394 : Integer.Sparse Master := [(Sum.inr 1594, 1), (Sum.inr 1597, 2), (Sum.inr 1707, 1), (Sum.inr 3288, 1), (Sum.inr 4069, -1)]

def numericRow1395 : Integer.Sparse Master := [(Sum.inr 1597, 1), (Sum.inr 3238, 1), (Sum.inr 3285, 1), (Sum.inr 3288, 1), (Sum.inr 3290, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

def numericRow1396 : Integer.Sparse Master := [(Sum.inr 1616, 1), (Sum.inr 3241, 1), (Sum.inr 3288, 1), (Sum.inr 3290, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

def numericRow1397 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 1114, 1), (Sum.inr 1117, 1), (Sum.inr 1129, 1), (Sum.inr 1213, 1), (Sum.inr 2480, 1), (Sum.inr 4091, -1)]

def numericRow1398 : Integer.Sparse Master := [(Sum.inr 625, 1), (Sum.inr 1129, 1), (Sum.inr 1213, 2), (Sum.inr 1235, 1), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

def numericRow1399 : Integer.Sparse Master := [(Sum.inr 1597, 1), (Sum.inr 1601, 1), (Sum.inr 1616, 1), (Sum.inr 1724, 1), (Sum.inr 3290, 1), (Sum.inr 4069, -1)]

def numericRow1400 : Integer.Sparse Master := [(Sum.inr 1210, 1), (Sum.inr 2477, 1), (Sum.inr 2613, 1), (Sum.inr 2694, 1), (Sum.inr 2708, 1), (Sum.inr 2718, 1), (Sum.inr 4090, -1)]

def numericRow1401 : Integer.Sparse Master := [(Sum.inr 1180, 1), (Sum.inr 2383, 1), (Sum.inr 2607, 1), (Sum.inr 2662, 2), (Sum.inr 2671, 1), (Sum.inr 4087, -1)]

def numericRow1402 : Integer.Sparse Master := [(Sum.inr 1180, 3), (Sum.inr 1187, 1), (Sum.inr 1256, 1), (Sum.inr 2671, 1), (Sum.inr 4087, -1)]

def numericRow1403 : Integer.Sparse Master := [(Sum.inr 1178, 1), (Sum.inr 2382, 1), (Sum.inr 2606, 1), (Sum.inr 2661, 1), (Sum.inr 2669, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

def numericRow1404 : Integer.Sparse Master := [(Sum.inr 1656, 2), (Sum.inr 1659, 1), (Sum.inr 1661, 1), (Sum.inr 1739, 1), (Sum.inr 2737, 1), (Sum.inr 4069, -1)]

def numericRow1405 : Integer.Sparse Master := [(Sum.inr 1650, 1), (Sum.inr 2502, 2), (Sum.inr 2521, 1), (Sum.inr 2737, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

def numericRow1406 : Integer.Sparse Master := [(Sum.inr 1646, 2), (Sum.inr 1651, 1), (Sum.inr 1653, 1), (Sum.inr 1728, 1), (Sum.inr 3306, 1), (Sum.inr 4069, -1)]

def numericRow1407 : Integer.Sparse Master := [(Sum.inr 1653, 1), (Sum.inr 3049, 1), (Sum.inr 3287, 2), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 4069, -1)]

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

def numericRow1408 : Integer.Sparse Master := [(Sum.inr 1288, 1), (Sum.inr 2585, 2), (Sum.inr 2686, 1), (Sum.inr 2771, 1), (Sum.inr 2779, 1), (Sum.inr 4089, -1)]

def numericRow1409 : Integer.Sparse Master := [(Sum.inl 0, 57), (Sum.inl 6, -5), (Sum.inl 7, 80), (Sum.inl 1, 300), (Sum.inr 610, -1440), (Sum.inr 611, -720), (Sum.inr 613, -1440), (Sum.inr 1135, -1440), (Sum.inr 1136, -1440), (Sum.inr 1138, -2880), (Sum.inr 1293, -1440), (Sum.inr 1294, -1440), (Sum.inr 1524, -1440), (Sum.inr 1525, -1440), (Sum.inr 1535, -720), (Sum.inr 3269, -1440), (Sum.inr 3270, -2880), (Sum.inr 3273, -1440), (Sum.inr 3304, -1440), (Sum.inr 3305, -1440), (Sum.inr 3308, -2880), (Sum.inr 3310, -1440), (Sum.inr 3311, -1440), (Sum.inr 3603, -1440), (Sum.inr 3623, -720)]

def numericRow1410 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 6, 5), (Sum.inl 7, -80), (Sum.inl 1, -300), (Sum.inr 610, 1440), (Sum.inr 611, 720), (Sum.inr 613, 1440), (Sum.inr 1135, 1440), (Sum.inr 1136, 1440), (Sum.inr 1138, 2880), (Sum.inr 1293, 1440), (Sum.inr 1294, 1440)]

def numericRow1411 : Integer.Sparse Master := [(Sum.inl 0, 15), (Sum.inl 6, -1), (Sum.inl 7, 16), (Sum.inl 1, -30), (Sum.inr 600, -432), (Sum.inr 602, -216), (Sum.inr 608, -432), (Sum.inr 1126, -432), (Sum.inr 1128, -432), (Sum.inr 1134, -864), (Sum.inr 1236, -864), (Sum.inr 1239, -432), (Sum.inr 1246, -432), (Sum.inr 1507, -432), (Sum.inr 1509, -216), (Sum.inr 1519, -432), (Sum.inr 2184, -432), (Sum.inr 2226, -432), (Sum.inr 3256, -432), (Sum.inr 3265, -864), (Sum.inr 3293, -864), (Sum.inr 3301, -432), (Sum.inr 3307, -432), (Sum.inr 3309, -432), (Sum.inr 3613, -432), (Sum.inr 3632, -432)]

def numericRow1412 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 6, 1), (Sum.inl 7, -16), (Sum.inl 1, 30), (Sum.inr 600, 432), (Sum.inr 602, 216), (Sum.inr 608, 432), (Sum.inr 1126, 432), (Sum.inr 1128, 432), (Sum.inr 1134, 864), (Sum.inr 1236, 864), (Sum.inr 1239, 432), (Sum.inr 1246, 432)]

def numericRow1413 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 6, 5), (Sum.inl 8, -80), (Sum.inl 1, -40), (Sum.inr 1040, -2160), (Sum.inr 1044, -2160), (Sum.inr 1080, -1080), (Sum.inr 1087, -2160), (Sum.inr 1236, -4320), (Sum.inr 1240, -2160), (Sum.inr 1294, -2160), (Sum.inr 1707, -2160), (Sum.inr 1710, -1080), (Sum.inr 1737, -2160), (Sum.inr 1739, -2160), (Sum.inr 3293, -4320), (Sum.inr 3299, -2160), (Sum.inr 3305, -2160), (Sum.inr 3309, -2160), (Sum.inr 4589, 8640), (Sum.inr 4600, 8640), (Sum.inr 4607, 17280), (Sum.inr 4617, 8640)]

def numericRow1414 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 5, 120), (Sum.inl 6, -25), (Sum.inl 2, -60), (Sum.inl 7, -80), (Sum.inl 1, 30), (Sum.inr 1044, 1440), (Sum.inr 1087, 1440), (Sum.inr 1216, 1440), (Sum.inr 1240, 1440), (Sum.inr 1241, 2880), (Sum.inr 1270, 1440), (Sum.inr 1306, 1440)]

def numericRow1415 : Integer.Sparse Master := [(Sum.inr 1737, 2), (Sum.inr 1739, 2), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

def numericRow1416 : Integer.Sparse Master := [(Sum.inr 3293, 2), (Sum.inr 3305, 1), (Sum.inr 3308, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

def numericRow1417 : Integer.Sparse Master := [(Sum.inl 0, 71), (Sum.inl 6, -5), (Sum.inl 8, 80), (Sum.inl 1, -50), (Sum.inr 603, -1440), (Sum.inr 605, -720), (Sum.inr 608, -720), (Sum.inr 614, -720), (Sum.inr 1129, -1440), (Sum.inr 1131, -1440), (Sum.inr 1134, -1440), (Sum.inr 1139, -1440), (Sum.inr 1240, -1440), (Sum.inr 1242, -720), (Sum.inr 1246, -720), (Sum.inr 1517, -1440), (Sum.inr 1518, -720), (Sum.inr 1519, -720), (Sum.inr 1536, -720), (Sum.inr 3263, -1440), (Sum.inr 3264, -1440), (Sum.inr 3265, -1440), (Sum.inr 3274, -1440), (Sum.inr 3299, -1440), (Sum.inr 3300, -720), (Sum.inr 3301, -720), (Sum.inr 3307, -1440), (Sum.inr 3308, -720), (Sum.inr 3309, -2160), (Sum.inr 3310, -720), (Sum.inr 3312, -720), (Sum.inr 3607, -1440), (Sum.inr 3627, -720)]

def numericRow1418 : Integer.Sparse Master := [(Sum.inl 0, -71), (Sum.inl 6, 5), (Sum.inl 8, -80), (Sum.inl 1, 50), (Sum.inr 603, 1440), (Sum.inr 605, 720), (Sum.inr 608, 720), (Sum.inr 614, 720), (Sum.inr 1129, 1440), (Sum.inr 1131, 1440), (Sum.inr 1134, 1440), (Sum.inr 1139, 1440), (Sum.inr 1240, 1440), (Sum.inr 1242, 720), (Sum.inr 1246, 720)]

def numericRow1419 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 6, 15), (Sum.inl 7, -160), (Sum.inl 8, -80), (Sum.inl 1, 80), (Sum.inr 1041, -8640), (Sum.inr 1083, -4320), (Sum.inr 1236, -8640), (Sum.inr 1240, -8640), (Sum.inr 1294, -4320), (Sum.inr 1724, -8640), (Sum.inr 1728, -4320), (Sum.inr 3293, -8640), (Sum.inr 3299, -8640), (Sum.inr 3305, -4320), (Sum.inr 3308, -4320), (Sum.inr 3309, -2160), (Sum.inr 4590, 17280), (Sum.inr 4603, 34560), (Sum.inr 4620, 8640)]

def numericRow1420 : Integer.Sparse Master := [(Sum.inl 0, 61), (Sum.inl 5, 60), (Sum.inl 6, 5), (Sum.inl 2, -10), (Sum.inl 7, 160), (Sum.inl 3, 160), (Sum.inl 1, 320), (Sum.inr 593, -4320), (Sum.inr 594, -2160), (Sum.inr 595, -2160), (Sum.inr 613, -2160), (Sum.inr 1122, -4320), (Sum.inr 1123, -4320), (Sum.inr 1124, -4320), (Sum.inr 1138, -4320), (Sum.inr 1188, -4320), (Sum.inr 1190, -2160), (Sum.inr 1193, -2160), (Sum.inr 1293, -4320), (Sum.inr 1294, -6480), (Sum.inr 1297, -2160), (Sum.inr 1498, -4320), (Sum.inr 1499, -2160), (Sum.inr 1500, -2160), (Sum.inr 1525, -2160), (Sum.inr 1937, -4320), (Sum.inr 1952, -2160), (Sum.inr 2289, -2160), (Sum.inr 2954, -4320), (Sum.inr 3054, -2160), (Sum.inr 3245, -4320), (Sum.inr 3248, -2160), (Sum.inr 3253, -4320), (Sum.inr 3254, -4320), (Sum.inr 3270, -4320), (Sum.inr 3304, -4320), (Sum.inr 3305, -6480), (Sum.inr 3308, -2160), (Sum.inr 3311, -2160), (Sum.inr 3606, -4320), (Sum.inr 3623, -2160), (Sum.inr 3626, -2160), (Sum.inr 3633, -2160)]

def numericRow1421 : Integer.Sparse Master := [(Sum.inl 0, -61), (Sum.inl 5, -60), (Sum.inl 6, -5), (Sum.inl 2, 10), (Sum.inl 7, -160), (Sum.inl 3, -160), (Sum.inl 1, -320), (Sum.inr 593, 4320), (Sum.inr 594, 2160), (Sum.inr 595, 2160), (Sum.inr 613, 2160), (Sum.inr 1122, 4320), (Sum.inr 1123, 4320), (Sum.inr 1124, 4320), (Sum.inr 1138, 4320), (Sum.inr 1188, 4320), (Sum.inr 1190, 2160), (Sum.inr 1193, 2160), (Sum.inr 1293, 4320), (Sum.inr 1294, 6480), (Sum.inr 1297, 2160), (Sum.inr 2954, 4320), (Sum.inr 3054, 2160)]

def numericRow1422 : Integer.Sparse Master := [(Sum.inr 1236, -2), (Sum.inr 1242, -1), (Sum.inr 1246, -1), (Sum.inr 2590, -2), (Sum.inr 2765, -1), (Sum.inr 2782, -1), (Sum.inr 3293, -2), (Sum.inr 3300, -1), (Sum.inr 3301, -1), (Sum.inr 3564, -2), (Sum.inr 3582, -1), (Sum.inr 3583, -1), (Sum.inr 4176, 8), (Sum.inr 4178, 4), (Sum.inr 4179, 4), (Sum.inr 4188, 4), (Sum.inr 4545, 8), (Sum.inr 4547, 8), (Sum.inr 4548, 8), (Sum.inr 4556, 8), (Sum.inr 4607, 8), (Sum.inr 4609, 4), (Sum.inr 4611, 4), (Sum.inr 4616, 8), (Sum.inr 4617, 4), (Sum.inr 4620, 4)]

def numericRow1423 : Integer.Sparse Master := [(Sum.inl 0, -110), (Sum.inl 5, -40), (Sum.inl 6, 10), (Sum.inl 2, -30), (Sum.inl 7, -160), (Sum.inl 35, -160), (Sum.inl 3, -160), (Sum.inl 1, 230), (Sum.inr 604, 4320), (Sum.inr 606, 2160), (Sum.inr 607, 2160), (Sum.inr 616, 2160), (Sum.inr 1130, 4320), (Sum.inr 1132, 4320), (Sum.inr 1133, 4320), (Sum.inr 1141, 4320), (Sum.inr 1241, 4320), (Sum.inr 1243, 2160), (Sum.inr 1245, 2160), (Sum.inr 1291, 4320), (Sum.inr 1292, 2160), (Sum.inr 1295, 2160)]

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

def numericRow1424 : Integer.Sparse Master := [(Sum.inr 1512, 2), (Sum.inr 1513, 1), (Sum.inr 1520, 1), (Sum.inr 1526, 1), (Sum.inr 2657, 2), (Sum.inr 2683, 1), (Sum.inr 2737, 1), (Sum.inr 3259, 2), (Sum.inr 3266, 2), (Sum.inr 3271, 2), (Sum.inr 3293, 2), (Sum.inr 3296, 2), (Sum.inr 3300, 1), (Sum.inr 3301, 1), (Sum.inr 3302, 1), (Sum.inr 3303, 2), (Sum.inr 3306, 1), (Sum.inr 3564, 2), (Sum.inr 3582, 1), (Sum.inr 3583, 1)]

def numericRow1425 : Integer.Sparse Master := [(Sum.inr 638, 2), (Sum.inr 641, 1), (Sum.inr 642, 1), (Sum.inr 653, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

def numericRow1426 : Integer.Sparse Master := [(Sum.inr 1287, 1), (Sum.inr 2584, 2), (Sum.inr 2685, 1), (Sum.inr 2761, 2), (Sum.inr 4082, -1)]

def numericRow1427 : Integer.Sparse Master := [(Sum.inr 1230, 1), (Sum.inr 2505, 1), (Sum.inr 2551, 1), (Sum.inr 2705, 1), (Sum.inr 2729, 1), (Sum.inr 2736, 1), (Sum.inr 4088, -1)]

def numericRow1428 : Integer.Sparse Master := [(Sum.inr 1129, -1), (Sum.inr 1136, -1), (Sum.inr 1139, -2), (Sum.inr 1235, -1), (Sum.inr 1240, -2), (Sum.inr 1293, -1), (Sum.inr 2556, -1), (Sum.inr 2723, -2), (Sum.inr 3263, -1), (Sum.inr 3273, -1), (Sum.inr 3274, -2), (Sum.inr 3292, -1), (Sum.inr 3299, -2), (Sum.inr 3304, -1), (Sum.inr 3521, -1), (Sum.inr 3544, -2), (Sum.inr 4150, 4), (Sum.inr 4151, 4), (Sum.inr 4155, 8), (Sum.inr 4173, 4), (Sum.inr 4527, 4), (Sum.inr 4530, 8), (Sum.inr 4542, 4), (Sum.inr 4590, 8), (Sum.inr 4591, 8), (Sum.inr 4593, 8), (Sum.inr 4603, 8)]

def numericRow1429 : Integer.Sparse Master := [(Sum.inl 0, -77), (Sum.inl 5, -120), (Sum.inl 6, 15), (Sum.inl 2, 120), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 1, -130), (Sum.inr 578, 1440), (Sum.inr 579, 1440), (Sum.inr 583, 2880), (Sum.inr 601, 1440), (Sum.inr 1111, 1440), (Sum.inr 1114, 2880), (Sum.inr 1127, 1440), (Sum.inr 1213, 2880), (Sum.inr 1215, 2880), (Sum.inr 1220, 2880), (Sum.inr 1237, 2880)]

def numericRow1430 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1505, 1), (Sum.inr 1508, 1), (Sum.inr 1515, 2), (Sum.inr 3255, 1), (Sum.inr 3257, 1), (Sum.inr 3261, 2), (Sum.inr 3263, 1), (Sum.inr 3273, 1), (Sum.inr 3274, 2), (Sum.inr 3290, 2), (Sum.inr 3291, 2), (Sum.inr 3292, 1), (Sum.inr 3294, 2), (Sum.inr 3297, 2), (Sum.inr 3299, 2), (Sum.inr 3304, 1), (Sum.inr 3521, 1), (Sum.inr 3544, 2)]

def numericRow1431 : Integer.Sparse Master := [(Sum.inr 625, 1), (Sum.inr 630, 1), (Sum.inr 632, 2), (Sum.inr 640, 1), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

def numericRow1432 : Integer.Sparse Master := [(Sum.inr 1150, 1), (Sum.inr 1152, 2), (Sum.inr 1158, 1), (Sum.inr 1240, 1), (Sum.inr 2556, 1), (Sum.inr 4091, -1)]

def numericRow1433 : Integer.Sparse Master := [(Sum.inl 0, 256), (Sum.inl 6, 5), (Sum.inl 2, -65), (Sum.inl 7, 80), (Sum.inl 8, -160), (Sum.inl 3, 80), (Sum.inl 1, -370), (Sum.inr 571, -4320), (Sum.inr 572, -4320), (Sum.inr 573, -8640), (Sum.inr 603, -4320), (Sum.inr 1100, -4320), (Sum.inr 1101, -4320), (Sum.inr 1102, -8640), (Sum.inr 1107, -4320), (Sum.inr 1108, -8640), (Sum.inr 1129, -4320), (Sum.inr 1235, -4320), (Sum.inr 1236, -8640), (Sum.inr 1240, -8640), (Sum.inr 1242, -8640), (Sum.inr 1246, -8640), (Sum.inr 1491, -4320), (Sum.inr 1492, -4320), (Sum.inr 1493, -8640), (Sum.inr 1517, -4320), (Sum.inr 2884, -4320), (Sum.inr 3234, -4320), (Sum.inr 3235, -4320), (Sum.inr 3236, -8640), (Sum.inr 3250, -4320), (Sum.inr 3251, -8640), (Sum.inr 3263, -4320), (Sum.inr 3292, -4320), (Sum.inr 3293, -8640), (Sum.inr 3299, -8640), (Sum.inr 3300, -8640), (Sum.inr 3301, -8640), (Sum.inr 3307, -4320), (Sum.inr 3309, -8640), (Sum.inr 3621, -4320), (Sum.inr 3622, -4320), (Sum.inr 3627, -8640)]

def numericRow1434 : Integer.Sparse Master := [(Sum.inl 0, -256), (Sum.inl 6, -5), (Sum.inl 2, 65), (Sum.inl 7, -80), (Sum.inl 8, 160), (Sum.inl 3, -80), (Sum.inl 1, 370), (Sum.inr 571, 4320), (Sum.inr 572, 4320), (Sum.inr 573, 8640), (Sum.inr 603, 4320), (Sum.inr 1100, 4320), (Sum.inr 1101, 4320), (Sum.inr 1102, 8640), (Sum.inr 1107, 4320), (Sum.inr 1108, 8640), (Sum.inr 1129, 4320), (Sum.inr 1235, 4320), (Sum.inr 1236, 8640), (Sum.inr 1240, 8640), (Sum.inr 1242, 8640), (Sum.inr 1246, 8640), (Sum.inr 2884, 4320)]

def numericRow1435 : Integer.Sparse Master := [(Sum.inl 0, -212), (Sum.inl 5, 340), (Sum.inl 6, -95), (Sum.inl 2, -120), (Sum.inl 7, 80), (Sum.inl 35, -80), (Sum.inl 8, 160), (Sum.inl 52, -160), (Sum.inl 1, -105), (Sum.inr 980, 4320), (Sum.inr 1005, 8640), (Sum.inr 1180, 4320), (Sum.inr 1188, 4320), (Sum.inr 1189, 8640), (Sum.inr 1200, 4320), (Sum.inr 1201, 8640), (Sum.inr 1213, 8640), (Sum.inr 1216, 4320), (Sum.inr 1236, 8640), (Sum.inr 1237, 8640), (Sum.inr 1240, 4320), (Sum.inr 1241, 8640), (Sum.inr 1370, 4320)]

def numericRow1436 : Integer.Sparse Master := [(Sum.inr 1126, -1), (Sum.inr 1131, -1), (Sum.inr 1134, -1), (Sum.inr 1138, -1), (Sum.inr 1236, -1), (Sum.inr 1242, -1), (Sum.inr 1246, -1), (Sum.inr 1294, -1), (Sum.inr 2553, -1), (Sum.inr 2722, -1), (Sum.inr 2739, -1), (Sum.inr 3256, -1), (Sum.inr 3264, -1), (Sum.inr 3265, -1), (Sum.inr 3270, -1), (Sum.inr 3293, -1), (Sum.inr 3300, -1), (Sum.inr 3301, -1), (Sum.inr 3305, -1), (Sum.inr 3514, -1), (Sum.inr 3533, -1), (Sum.inr 3534, -1), (Sum.inr 4152, 4), (Sum.inr 4153, 4), (Sum.inr 4154, 4), (Sum.inr 4158, 4), (Sum.inr 4176, 4), (Sum.inr 4528, 4), (Sum.inr 4529, 4), (Sum.inr 4533, 4), (Sum.inr 4545, 4), (Sum.inr 4589, 4), (Sum.inr 4591, 4), (Sum.inr 4592, 4), (Sum.inr 4599, 4), (Sum.inr 4603, 4), (Sum.inr 4607, 8), (Sum.inr 4616, 4)]

def numericRow1437 : Integer.Sparse Master := [(Sum.inl 0, -210), (Sum.inl 5, -200), (Sum.inl 6, 30), (Sum.inl 2, -30), (Sum.inl 7, 320), (Sum.inl 35, 160), (Sum.inl 8, 160), (Sum.inl 3, 160), (Sum.inl 1, 150), (Sum.inr 580, 2880), (Sum.inr 581, 2880), (Sum.inr 582, 2880), (Sum.inr 586, 2880), (Sum.inr 604, 2880), (Sum.inr 1112, 2880), (Sum.inr 1113, 2880), (Sum.inr 1117, 2880), (Sum.inr 1130, 2880), (Sum.inr 1216, 2880), (Sum.inr 1217, 2880), (Sum.inr 1219, 2880), (Sum.inr 1241, 2880), (Sum.inr 1260, 2880), (Sum.inr 1261, 2880), (Sum.inr 1262, 2880), (Sum.inr 1291, 2880)]

def numericRow1438 : Integer.Sparse Master := [(Sum.inr 1510, 1), (Sum.inr 1511, 1), (Sum.inr 1512, 1), (Sum.inr 1514, 1), (Sum.inr 1522, 1), (Sum.inr 3256, 1), (Sum.inr 3258, 1), (Sum.inr 3259, 1), (Sum.inr 3260, 1), (Sum.inr 3264, 1), (Sum.inr 3265, 1), (Sum.inr 3267, 1), (Sum.inr 3270, 1), (Sum.inr 3288, 1), (Sum.inr 3289, 1), (Sum.inr 3291, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 3295, 1), (Sum.inr 3296, 2), (Sum.inr 3300, 1), (Sum.inr 3301, 1), (Sum.inr 3303, 1), (Sum.inr 3305, 1), (Sum.inr 3514, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1)]

def numericRow1439 : Integer.Sparse Master := [(Sum.inr 623, 1), (Sum.inr 626, 1), (Sum.inr 627, 1), (Sum.inr 631, 1), (Sum.inr 638, 1), (Sum.inr 1236, 1), (Sum.inr 4092, -1)]

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

def numericRow144 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 2726, -180), (Sum.inr 3545, -180), (Sum.inr 3634, -120), (Sum.inr 4085, 60)]

def numericRow145 : Integer.Sparse Master := [(Sum.inr 1043, -3), (Sum.inr 1051, -1), (Sum.inr 1239, -3), (Sum.inr 1297, -1), (Sum.inr 1725, -3), (Sum.inr 1752, -1), (Sum.inr 2022, -6), (Sum.inr 2109, -3), (Sum.inr 2203, -6), (Sum.inr 2226, -3), (Sum.inr 2261, -3), (Sum.inr 2289, -1), (Sum.inr 2740, -6), (Sum.inr 2783, -2), (Sum.inr 4084, 4)]

def numericRow146 : Integer.Sparse Master := [(Sum.inr 1725, 3), (Sum.inr 1752, 1), (Sum.inr 2203, 6), (Sum.inr 2226, 3), (Sum.inr 2261, 3), (Sum.inr 2289, 1), (Sum.inr 2740, 3), (Sum.inr 2783, 1), (Sum.inr 4084, 1)]

def numericRow147 : Integer.Sparse Master := [(Sum.inr 1051, 1), (Sum.inr 1239, 3), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

def numericRow148 : Integer.Sparse Master := [(Sum.inr 1239, 1), (Sum.inr 2022, 2), (Sum.inr 2740, 1), (Sum.inr 4084, -1)]

def numericRow149 : Integer.Sparse Master := [(Sum.inr 1043, 1), (Sum.inr 2022, 2), (Sum.inr 2109, 1), (Sum.inr 4084, -1)]

def numericRow150 : Integer.Sparse Master := [(Sum.inr 1297, 1), (Sum.inr 2109, 3), (Sum.inr 2783, 1), (Sum.inr 4084, -1)]

def numericRow151 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 1080, -360), (Sum.inr 1094, -120), (Sum.inr 1710, -360), (Sum.inr 1741, -120), (Sum.inr 2052, -720), (Sum.inr 2065, -360), (Sum.inr 2193, -720), (Sum.inr 2218, -360), (Sum.inr 2247, -360), (Sum.inr 2281, -120), (Sum.inr 2290, -360), (Sum.inr 2294, -120), (Sum.inr 2726, -360), (Sum.inr 3545, -360), (Sum.inr 3634, -120), (Sum.inr 4085, 480)]

def numericRow152 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 1, -5), (Sum.inr 4070, 240), (Sum.inr 4072, 30), (Sum.inr 4081, 360), (Sum.inr 4084, 240)]

def numericRow153 : Integer.Sparse Master := [(Sum.inl 0, -113), (Sum.inl 2, 155), (Sum.inl 3, -80), (Sum.inl 13, 160), (Sum.inl 12, 80), (Sum.inl 1, 80), (Sum.inr 1354, 4320), (Sum.inr 1355, 4320), (Sum.inr 1356, 4320), (Sum.inr 1367, 4320), (Sum.inr 1406, 4320), (Sum.inr 1903, 4320), (Sum.inr 1916, 4320), (Sum.inr 1927, 4320), (Sum.inr 2255, 4320), (Sum.inr 3016, 4320), (Sum.inr 3024, 4320), (Sum.inr 3025, 4320), (Sum.inr 3054, 4320), (Sum.inr 3077, 4320), (Sum.inr 3146, 4320), (Sum.inr 3147, 4320), (Sum.inr 3156, 4320), (Sum.inr 3165, 4320), (Sum.inr 3166, 4320), (Sum.inr 3180, 4320), (Sum.inr 3193, 4320), (Sum.inr 3196, 4320), (Sum.inr 3202, 4320), (Sum.inr 3221, 4320), (Sum.inr 3222, 8640)]

def numericRow154 : Integer.Sparse Master := [(Sum.inr 2253, 1), (Sum.inr 2513, 1), (Sum.inr 3528, 1), (Sum.inr 3577, 1), (Sum.inr 3625, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

def numericRow155 : Integer.Sparse Master := [(Sum.inr 1028, 1), (Sum.inr 1029, 1), (Sum.inr 1030, 1), (Sum.inr 1042, 1), (Sum.inr 1058, 1), (Sum.inr 2253, 1), (Sum.inr 4084, -1)]

def numericRow156 : Integer.Sparse Master := [(Sum.inr 1028, 1), (Sum.inr 2095, 1), (Sum.inr 2124, 1), (Sum.inr 2252, 1), (Sum.inr 2253, 2), (Sum.inr 4084, -1)]

def numericRow157 : Integer.Sparse Master := [(Sum.inr 2013, 1), (Sum.inr 2014, 1), (Sum.inr 2021, 1), (Sum.inr 2034, 1), (Sum.inr 2253, 1), (Sum.inr 3528, 1), (Sum.inr 4084, -1)]

def numericRow158 : Integer.Sparse Master := [(Sum.inr 1058, 1), (Sum.inr 2034, 1), (Sum.inr 2133, 1), (Sum.inr 2253, 1), (Sum.inr 2277, 1), (Sum.inr 2279, 1), (Sum.inr 4084, -1)]

def numericRow159 : Integer.Sparse Master := [(Sum.inr 2095, 1), (Sum.inr 2096, 1), (Sum.inr 2097, 1), (Sum.inr 2108, 1), (Sum.inr 2253, 1), (Sum.inr 3577, 1), (Sum.inr 4084, -1)]

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

def numericRow1440 : Integer.Sparse Master := [(Sum.inr 1148, 1), (Sum.inr 1149, 1), (Sum.inr 1151, 1), (Sum.inr 1156, 1), (Sum.inr 1236, 1), (Sum.inr 2553, 1), (Sum.inr 4092, -1)]

def numericRow1441 : Integer.Sparse Master := [(Sum.inl 0, 152), (Sum.inl 6, -5), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 8, 160), (Sum.inl 3, -80), (Sum.inl 1, -50), (Sum.inr 567, -4320), (Sum.inr 568, -4320), (Sum.inr 569, -4320), (Sum.inr 573, -4320), (Sum.inr 600, -4320), (Sum.inr 1097, -4320), (Sum.inr 1098, -4320), (Sum.inr 1099, -4320), (Sum.inr 1102, -4320), (Sum.inr 1105, -4320), (Sum.inr 1106, -4320), (Sum.inr 1108, -4320), (Sum.inr 1126, -4320), (Sum.inr 1200, -4320), (Sum.inr 1202, -4320), (Sum.inr 1205, -4320), (Sum.inr 1235, -4320), (Sum.inr 1236, -12960), (Sum.inr 1239, -4320), (Sum.inr 1240, -4320), (Sum.inr 1246, -4320), (Sum.inr 1488, -4320), (Sum.inr 1489, -4320), (Sum.inr 1490, -4320), (Sum.inr 1493, -4320), (Sum.inr 1507, -4320), (Sum.inr 1887, -4320), (Sum.inr 1894, -4320), (Sum.inr 1942, -4320), (Sum.inr 2226, -4320), (Sum.inr 2881, -4320), (Sum.inr 2924, -4320), (Sum.inr 3077, -4320), (Sum.inr 3232, -4320), (Sum.inr 3233, -4320), (Sum.inr 3236, -4320), (Sum.inr 3249, -4320), (Sum.inr 3251, -4320), (Sum.inr 3256, -4320), (Sum.inr 3281, -4320), (Sum.inr 3284, -4320), (Sum.inr 3292, -4320), (Sum.inr 3293, -12960), (Sum.inr 3299, -4320), (Sum.inr 3301, -4320), (Sum.inr 3307, -4320), (Sum.inr 3308, -4320), (Sum.inr 3605, -4320), (Sum.inr 3622, -4320), (Sum.inr 3624, -4320), (Sum.inr 3625, -4320), (Sum.inr 3632, -4320)]

def numericRow1442 : Integer.Sparse Master := [(Sum.inl 0, -152), (Sum.inl 6, 5), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 8, -160), (Sum.inl 3, 80), (Sum.inl 1, 50), (Sum.inr 567, 4320), (Sum.inr 568, 4320), (Sum.inr 569, 4320), (Sum.inr 573, 4320), (Sum.inr 600, 4320), (Sum.inr 1097, 4320), (Sum.inr 1098, 4320), (Sum.inr 1099, 4320), (Sum.inr 1102, 4320), (Sum.inr 1105, 4320), (Sum.inr 1106, 4320), (Sum.inr 1108, 4320), (Sum.inr 1126, 4320), (Sum.inr 1200, 4320), (Sum.inr 1202, 4320), (Sum.inr 1205, 4320), (Sum.inr 1235, 4320), (Sum.inr 1236, 12960), (Sum.inr 1239, 4320), (Sum.inr 1240, 4320), (Sum.inr 1246, 4320), (Sum.inr 2881, 4320), (Sum.inr 2924, 4320), (Sum.inr 3077, 4320)]

def numericRow1443 : Integer.Sparse Master := [(Sum.inr 1229, 1), (Sum.inr 2504, 1), (Sum.inr 2550, 1), (Sum.inr 2704, 1), (Sum.inr 2719, 1), (Sum.inr 2735, 1), (Sum.inr 4080, -1)]

def numericRow1444 : Integer.Sparse Master := [(Sum.inr 1183, 1), (Sum.inr 1188, 1), (Sum.inr 1189, 2), (Sum.inr 1286, 1), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

def numericRow1445 : Integer.Sparse Master := [(Sum.inr 1185, 1), (Sum.inr 2400, 1), (Sum.inr 2535, 1), (Sum.inr 2677, 1), (Sum.inr 2682, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

def numericRow1446 : Integer.Sparse Master := [(Sum.inr 1188, 1), (Sum.inr 2536, 1), (Sum.inr 2672, 2), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

def numericRow1447 : Integer.Sparse Master := [(Sum.inr 1184, 1), (Sum.inr 2399, 1), (Sum.inr 2534, 1), (Sum.inr 2670, 1), (Sum.inr 2681, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

def numericRow1448 : Integer.Sparse Master := [(Sum.inr 1200, 1), (Sum.inr 1201, 2), (Sum.inr 1228, 2), (Sum.inr 2703, 1), (Sum.inr 4090, -1)]

def numericRow1449 : Integer.Sparse Master := [(Sum.inr 1198, 1), (Sum.inr 2459, 2), (Sum.inr 2697, 1), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

def numericRow1450 : Integer.Sparse Master := [(Sum.inr 1200, 1), (Sum.inr 2694, 2), (Sum.inr 2703, 1), (Sum.inr 4090, -1)]

def numericRow1451 : Integer.Sparse Master := [(Sum.inr 1197, 1), (Sum.inr 2458, 2), (Sum.inr 2700, 1), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

def numericRow1452 : Integer.Sparse Master := [(Sum.inr 1052, 1), (Sum.inr 1054, 2), (Sum.inr 1060, 1), (Sum.inr 1073, 1), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

def numericRow1453 : Integer.Sparse Master := [(Sum.inr 1054, 1), (Sum.inr 2031, 1), (Sum.inr 2129, 1), (Sum.inr 2216, 1), (Sum.inr 2251, 1), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

def numericRow1454 : Integer.Sparse Master := [(Sum.inr 1053, 1), (Sum.inr 2030, 1), (Sum.inr 2128, 1), (Sum.inr 2215, 1), (Sum.inr 2274, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

def numericRow1455 : Integer.Sparse Master := [(Sum.inr 988, 2), (Sum.inr 990, 1), (Sum.inr 998, 1), (Sum.inr 1052, 1), (Sum.inr 2214, 1), (Sum.inr 4080, -1)]

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

def numericRow1456 : Integer.Sparse Master := [(Sum.inr 988, 1), (Sum.inr 1922, 1), (Sum.inr 2118, 1), (Sum.inr 2195, 1), (Sum.inr 2214, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

def numericRow1457 : Integer.Sparse Master := [(Sum.inr 987, 1), (Sum.inr 1921, 1), (Sum.inr 2117, 1), (Sum.inr 2213, 1), (Sum.inr 2215, 2), (Sum.inr 4082, -1)]

def numericRow1458 : Integer.Sparse Master := [(Sum.inr 1023, 1), (Sum.inr 2091, 2), (Sum.inr 2234, 2), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

def numericRow1459 : Integer.Sparse Master := [(Sum.inr 1018, 2), (Sum.inr 1023, 1), (Sum.inr 1034, 2), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

def numericRow1460 : Integer.Sparse Master := [(Sum.inr 1018, 1), (Sum.inr 2086, 2), (Sum.inr 2191, 1), (Sum.inr 2232, 1), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

def numericRow1461 : Integer.Sparse Master := [(Sum.inr 1017, 1), (Sum.inr 2085, 2), (Sum.inr 2190, 1), (Sum.inr 2240, 1), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

def numericRow1462 : Integer.Sparse Master := [(Sum.inr 1045, 1), (Sum.inr 2024, 1), (Sum.inr 2111, 1), (Sum.inr 2246, 1), (Sum.inr 2254, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

def numericRow1463 : Integer.Sparse Master := [(Sum.inr 1032, 1), (Sum.inr 1035, 1), (Sum.inr 1036, 1), (Sum.inr 1045, 1), (Sum.inr 1073, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

def numericRow1464 : Integer.Sparse Master := [(Sum.inr 1036, 1), (Sum.inr 2017, 1), (Sum.inr 2102, 1), (Sum.inr 2206, 1), (Sum.inr 2251, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

def numericRow1465 : Integer.Sparse Master := [(Sum.inr 610, -1), (Sum.inr 929, -1), (Sum.inr 1039, -1), (Sum.inr 1041, -2), (Sum.inr 1044, -2), (Sum.inr 1524, -1), (Sum.inr 1680, -1), (Sum.inr 1706, -1), (Sum.inr 1724, -2), (Sum.inr 1737, -2), (Sum.inr 2023, -1), (Sum.inr 2110, -1), (Sum.inr 2214, -1), (Sum.inr 2245, -2), (Sum.inr 2275, -1), (Sum.inr 2277, -2), (Sum.inr 4152, 4), (Sum.inr 4157, 4), (Sum.inr 4158, 8), (Sum.inr 4331, 4), (Sum.inr 4332, 8), (Sum.inr 4366, 4), (Sum.inr 4371, 4), (Sum.inr 4372, 8), (Sum.inr 4439, 8), (Sum.inr 4442, 8), (Sum.inr 4444, 8)]

def numericRow1466 : Integer.Sparse Master := [(Sum.inr 1510, 1), (Sum.inr 1522, 2), (Sum.inr 1524, 1), (Sum.inr 1528, 1), (Sum.inr 1678, 2), (Sum.inr 1680, 1), (Sum.inr 1684, 1), (Sum.inr 1706, 1), (Sum.inr 1711, 1), (Sum.inr 1713, 2), (Sum.inr 1724, 2), (Sum.inr 1734, 2), (Sum.inr 1736, 2), (Sum.inr 1737, 2), (Sum.inr 1742, 1), (Sum.inr 1744, 2), (Sum.inr 2214, 1), (Sum.inr 2275, 1), (Sum.inr 2277, 2)]

def numericRow1467 : Integer.Sparse Master := [(Sum.inr 610, 1), (Sum.inr 929, 1), (Sum.inr 1044, 3), (Sum.inr 4083, -1)]

def numericRow1468 : Integer.Sparse Master := [(Sum.inr 944, 1), (Sum.inr 949, 1), (Sum.inr 950, 2), (Sum.inr 1044, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

def numericRow1469 : Integer.Sparse Master := [(Sum.inl 0, 113), (Sum.inl 6, -5), (Sum.inl 2, -50), (Sum.inl 7, 80), (Sum.inl 3, -160), (Sum.inl 1, -230), (Sum.inr 541, -4320), (Sum.inr 542, -4320), (Sum.inr 543, -8640), (Sum.inr 557, -4320), (Sum.inr 674, -4320), (Sum.inr 675, -8640), (Sum.inr 677, -4320), (Sum.inr 681, -4320), (Sum.inr 868, -4320), (Sum.inr 869, -8640), (Sum.inr 885, -4320), (Sum.inr 929, -4320), (Sum.inr 930, -4320), (Sum.inr 932, -8640), (Sum.inr 1034, -4320), (Sum.inr 1035, -8640), (Sum.inr 1044, -8640), (Sum.inr 1046, -8640), (Sum.inr 1049, -8640), (Sum.inr 1073, -4320), (Sum.inr 1087, -8640), (Sum.inr 1561, -8640), (Sum.inr 1563, -4320), (Sum.inr 1566, -4320), (Sum.inr 1644, -4320), (Sum.inr 1645, -8640), (Sum.inr 1648, -4320), (Sum.inr 1680, -4320), (Sum.inr 1681, -8640), (Sum.inr 1690, -4320), (Sum.inr 1737, -8640), (Sum.inr 1738, -8640), (Sum.inr 1739, -8640), (Sum.inr 1750, -8640), (Sum.inr 2483, -4320), (Sum.inr 2764, -4320), (Sum.inr 3477, -4320), (Sum.inr 3581, -4320), (Sum.inr 3613, -4320), (Sum.inr 3632, -8640)]

def numericRow1470 : Integer.Sparse Master := [(Sum.inl 0, -84), (Sum.inl 5, 200), (Sum.inl 6, -40), (Sum.inl 2, -90), (Sum.inl 7, -160), (Sum.inl 35, -160), (Sum.inl 8, -160), (Sum.inl 3, -160), (Sum.inl 1, -30), (Sum.inr 786, 4320), (Sum.inr 811, 8640), (Sum.inr 827, 4320), (Sum.inr 980, 4320), (Sum.inr 981, 8640), (Sum.inr 990, 4320), (Sum.inr 1021, 8640), (Sum.inr 1023, 4320), (Sum.inr 1041, 8640), (Sum.inr 1042, 8640), (Sum.inr 1044, 4320), (Sum.inr 1045, 8640), (Sum.inr 1058, 8640), (Sum.inr 1060, 4320), (Sum.inr 1087, 8640), (Sum.inr 1216, 4320), (Sum.inr 1270, 4320)]

def numericRow1471 : Integer.Sparse Master := [(Sum.inr 603, -1), (Sum.inr 922, -1), (Sum.inr 1039, -1), (Sum.inr 1041, -3), (Sum.inr 1044, -1), (Sum.inr 1046, -1), (Sum.inr 1050, -1), (Sum.inr 1517, -1), (Sum.inr 1673, -1), (Sum.inr 1706, -1), (Sum.inr 1724, -3), (Sum.inr 1737, -1), (Sum.inr 1750, -1), (Sum.inr 1751, -1), (Sum.inr 2020, -1), (Sum.inr 2107, -1), (Sum.inr 2202, -1), (Sum.inr 2244, -1), (Sum.inr 2260, -1), (Sum.inr 2262, -1), (Sum.inr 4150, 4), (Sum.inr 4153, 4), (Sum.inr 4155, 4), (Sum.inr 4158, 4), (Sum.inr 4327, 4), (Sum.inr 4332, 4), (Sum.inr 4364, 4), (Sum.inr 4367, 4), (Sum.inr 4369, 4), (Sum.inr 4372, 4), (Sum.inr 4440, 4), (Sum.inr 4444, 4)]

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

def numericRow1472 : Integer.Sparse Master := [(Sum.inl 0, -392), (Sum.inl 5, -480), (Sum.inl 6, 80), (Sum.inl 2, -160), (Sum.inl 8, 320), (Sum.inl 52, 320), (Sum.inl 1, -360), (Sum.inr 625, 4320), (Sum.inr 626, 4320), (Sum.inr 627, 4320), (Sum.inr 632, 4320), (Sum.inr 1316, 4320), (Sum.inr 1317, 4320), (Sum.inr 1318, 4320), (Sum.inr 1322, 4320), (Sum.inr 1327, 4320), (Sum.inr 1328, 4320), (Sum.inr 1388, 4320), (Sum.inr 1391, 4320)]

def numericRow1473 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1514, 1), (Sum.inr 1515, 1), (Sum.inr 1517, 1), (Sum.inr 1522, 1), (Sum.inr 1670, 1), (Sum.inr 1673, 1), (Sum.inr 1678, 1), (Sum.inr 1703, 1), (Sum.inr 1706, 1), (Sum.inr 1720, 1), (Sum.inr 1721, 1), (Sum.inr 1723, 1), (Sum.inr 1724, 3), (Sum.inr 1734, 1), (Sum.inr 1736, 1), (Sum.inr 1737, 1), (Sum.inr 1750, 1), (Sum.inr 1751, 1), (Sum.inr 2202, 1), (Sum.inr 2260, 1), (Sum.inr 2262, 1)]

def numericRow1474 : Integer.Sparse Master := [(Sum.inr 578, 1), (Sum.inr 581, 1), (Sum.inr 583, 1), (Sum.inr 586, 1), (Sum.inr 603, 1), (Sum.inr 1041, 1), (Sum.inr 4083, -1)]

def numericRow1475 : Integer.Sparse Master := [(Sum.inr 603, 1), (Sum.inr 922, 1), (Sum.inr 1041, 2), (Sum.inr 4083, -1)]

def numericRow1476 : Integer.Sparse Master := [(Sum.inr 942, 1), (Sum.inr 945, 1), (Sum.inr 947, 1), (Sum.inr 950, 1), (Sum.inr 1041, 1), (Sum.inr 2107, 1), (Sum.inr 4083, -1)]

def numericRow1477 : Integer.Sparse Master := [(Sum.inl 0, 142), (Sum.inl 6, -5), (Sum.inl 2, 25), (Sum.inl 8, 80), (Sum.inl 3, 80), (Sum.inl 1, -100), (Sum.inr 537, -4320), (Sum.inr 538, -4320), (Sum.inr 539, -4320), (Sum.inr 544, -4320), (Sum.inr 554, -4320), (Sum.inr 662, -4320), (Sum.inr 663, -4320), (Sum.inr 664, -4320), (Sum.inr 668, -4320), (Sum.inr 682, -4320), (Sum.inr 865, -4320), (Sum.inr 866, -4320), (Sum.inr 870, -4320), (Sum.inr 879, -4320), (Sum.inr 922, -4320), (Sum.inr 924, -4320), (Sum.inr 927, -4320), (Sum.inr 933, -4320), (Sum.inr 980, -4320), (Sum.inr 982, -4320), (Sum.inr 985, -4320), (Sum.inr 1005, -4320), (Sum.inr 1039, -4320), (Sum.inr 1040, -4320), (Sum.inr 1041, -8640), (Sum.inr 1043, -4320), (Sum.inr 1050, -4320), (Sum.inr 1079, -4320), (Sum.inr 1083, -4320), (Sum.inr 1553, -4320), (Sum.inr 1554, -4320), (Sum.inr 1556, -4320), (Sum.inr 1567, -4320), (Sum.inr 1616, -4320), (Sum.inr 1617, -4320), (Sum.inr 1618, -4320), (Sum.inr 1623, -4320), (Sum.inr 1673, -4320), (Sum.inr 1674, -4320), (Sum.inr 1675, -4320), (Sum.inr 1691, -4320), (Sum.inr 1706, -4320), (Sum.inr 1707, -4320), (Sum.inr 1708, -4320), (Sum.inr 1724, -8640), (Sum.inr 1725, -4320), (Sum.inr 1728, -4320), (Sum.inr 1751, -4320), (Sum.inr 2480, -4320), (Sum.inr 2723, -4320), (Sum.inr 3467, -4320), (Sum.inr 3544, -4320), (Sum.inr 3607, -4320), (Sum.inr 3622, -4320), (Sum.inr 3627, -4320)]

def numericRow1478 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 6, 5), (Sum.inl 8, -80), (Sum.inl 1, -40), (Sum.inr 783, -2160), (Sum.inr 803, -2160), (Sum.inr 807, -4320), (Sum.inr 811, -2160), (Sum.inr 824, -2160), (Sum.inr 977, -2160), (Sum.inr 980, -2160), (Sum.inr 1035, -2160), (Sum.inr 1040, -2160), (Sum.inr 1041, -4320), (Sum.inr 1044, -2160), (Sum.inr 1083, -2160), (Sum.inr 1236, -2160), (Sum.inr 1240, -2160), (Sum.inr 1597, -2160), (Sum.inr 1616, -2160), (Sum.inr 1645, -2160), (Sum.inr 1707, -2160), (Sum.inr 1724, -4320), (Sum.inr 1728, -2160), (Sum.inr 1737, -2160), (Sum.inr 3293, -2160), (Sum.inr 3299, -2160), (Sum.inr 3309, -2160), (Sum.inr 4407, 8640), (Sum.inr 4436, 8640), (Sum.inr 4439, 8640), (Sum.inr 4453, 8640), (Sum.inr 4459, 8640), (Sum.inr 4471, 8640), (Sum.inr 4474, 8640), (Sum.inr 4475, 8640), (Sum.inr 4590, 8640), (Sum.inr 4603, 8640)]

def numericRow1479 : Integer.Sparse Master := [(Sum.inl 0, -168), (Sum.inl 5, 440), (Sum.inl 6, -80), (Sum.inl 2, -210), (Sum.inl 7, -480), (Sum.inl 35, -160), (Sum.inl 8, -160), (Sum.inl 3, -160), (Sum.inl 1, 150), (Sum.inr 783, 8640), (Sum.inr 807, 8640), (Sum.inr 824, 8640), (Sum.inr 977, 8640), (Sum.inr 980, 8640), (Sum.inr 988, 8640), (Sum.inr 1018, 8640), (Sum.inr 1021, 8640), (Sum.inr 1035, 8640), (Sum.inr 1036, 8640), (Sum.inr 1040, 8640), (Sum.inr 1041, 17280), (Sum.inr 1042, 8640), (Sum.inr 1044, 8640), (Sum.inr 1054, 8640), (Sum.inr 1057, 8640), (Sum.inr 1058, 8640), (Sum.inr 1083, 8640), (Sum.inr 1213, 8640), (Sum.inr 1262, 8640)]

def numericRow1480 : Integer.Sparse Master := [(Sum.inl 0, -440), (Sum.inl 5, 480), (Sum.inl 6, -160), (Sum.inl 2, -160), (Sum.inl 8, 320), (Sum.inl 52, 320), (Sum.inl 1, 120), (Sum.inr 1213, 4320), (Sum.inr 1236, 4320), (Sum.inr 1237, 4320), (Sum.inr 1240, 4320), (Sum.inr 1358, 4320), (Sum.inr 1367, 4320), (Sum.inr 1368, 4320), (Sum.inr 1370, 4320), (Sum.inr 1383, 4320), (Sum.inr 1384, 4320), (Sum.inr 1406, 4320), (Sum.inr 1407, 4320)]

def numericRow1481 : Integer.Sparse Master := [(Sum.inr 1035, 1), (Sum.inr 2016, 1), (Sum.inr 2101, 1), (Sum.inr 2242, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

def numericRow1482 : Integer.Sparse Master := [(Sum.inr 730, 1), (Sum.inr 733, 1), (Sum.inr 734, 1), (Sum.inr 738, 1), (Sum.inr 1645, 1), (Sum.inr 4069, -1)]

def numericRow1483 : Integer.Sparse Master := [(Sum.inr 600, -1), (Sum.inr 919, -1), (Sum.inr 1040, -2), (Sum.inr 1043, -2), (Sum.inr 1049, -2), (Sum.inr 1079, -1), (Sum.inr 1507, -1), (Sum.inr 1664, -1), (Sum.inr 1707, -2), (Sum.inr 1708, -1), (Sum.inr 1725, -2), (Sum.inr 1738, -2), (Sum.inr 2019, -1), (Sum.inr 2106, -1), (Sum.inr 2190, -1), (Sum.inr 2242, -1), (Sum.inr 2244, -1), (Sum.inr 2262, -1), (Sum.inr 4149, 4), (Sum.inr 4151, 4), (Sum.inr 4154, 8), (Sum.inr 4328, 8), (Sum.inr 4363, 4), (Sum.inr 4365, 4), (Sum.inr 4368, 8), (Sum.inr 4459, 8)]

def numericRow1484 : Integer.Sparse Master := [(Sum.inl 0, -212), (Sum.inl 5, -200), (Sum.inl 6, 50), (Sum.inl 2, 280), (Sum.inl 7, 160), (Sum.inl 35, 160), (Sum.inl 1, 290), (Sum.inr 629, 2160), (Sum.inr 630, 2160), (Sum.inr 631, 4320), (Sum.inr 1319, 2160), (Sum.inr 1320, 2160), (Sum.inr 1321, 4320), (Sum.inr 1330, 4320), (Sum.inr 1406, 4320)]

def numericRow1485 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1505, 1), (Sum.inr 1507, 1), (Sum.inr 1511, 2), (Sum.inr 1664, 1), (Sum.inr 1667, 2), (Sum.inr 1697, 1), (Sum.inr 1704, 1), (Sum.inr 1707, 2), (Sum.inr 1708, 1), (Sum.inr 1712, 2), (Sum.inr 1714, 2), (Sum.inr 1725, 2), (Sum.inr 1738, 2), (Sum.inr 2190, 1), (Sum.inr 2242, 1), (Sum.inr 2244, 1)]

def numericRow1486 : Integer.Sparse Master := [(Sum.inr 577, 1), (Sum.inr 579, 1), (Sum.inr 582, 2), (Sum.inr 600, 1), (Sum.inr 1040, 1), (Sum.inr 4084, -1)]

def numericRow1487 : Integer.Sparse Master := [(Sum.inr 600, 1), (Sum.inr 919, 1), (Sum.inr 1040, 1), (Sum.inr 1079, 1), (Sum.inr 4084, -1)]

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

def numericRow1488 : Integer.Sparse Master := [(Sum.inr 941, 1), (Sum.inr 943, 1), (Sum.inr 946, 2), (Sum.inr 1040, 1), (Sum.inr 2106, 1), (Sum.inr 4084, -1)]

def numericRow1489 : Integer.Sparse Master := [(Sum.inr 577, 1), (Sum.inr 941, 1), (Sum.inr 1040, 3), (Sum.inr 4084, -1)]

def numericRow1490 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 6, -1), (Sum.inl 2, 10), (Sum.inl 7, 16), (Sum.inl 3, 32), (Sum.inl 1, 34), (Sum.inr 535, -864), (Sum.inr 536, -864), (Sum.inr 539, -1728), (Sum.inr 552, -864), (Sum.inr 656, -864), (Sum.inr 657, -864), (Sum.inr 660, -864), (Sum.inr 664, -1728), (Sum.inr 864, -864), (Sum.inr 866, -1728), (Sum.inr 876, -864), (Sum.inr 919, -864), (Sum.inr 921, -864), (Sum.inr 927, -1728), (Sum.inr 977, -1728), (Sum.inr 979, -1728), (Sum.inr 985, -1728), (Sum.inr 1000, -1728), (Sum.inr 1039, -864), (Sum.inr 1041, -1728), (Sum.inr 1079, -864), (Sum.inr 1550, -864), (Sum.inr 1552, -864), (Sum.inr 1554, -1728), (Sum.inr 1597, -1728), (Sum.inr 1599, -1728), (Sum.inr 1605, -1728), (Sum.inr 1618, -1728), (Sum.inr 1664, -864), (Sum.inr 1666, -864), (Sum.inr 1675, -1728), (Sum.inr 1706, -864), (Sum.inr 1708, -864), (Sum.inr 1724, -1728), (Sum.inr 2479, -864), (Sum.inr 2722, -1728), (Sum.inr 3459, -864), (Sum.inr 3533, -1728), (Sum.inr 3603, -864), (Sum.inr 3622, -864)]

def numericRow1491 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 6, 1), (Sum.inl 2, -10), (Sum.inl 7, -16), (Sum.inl 3, -32), (Sum.inl 1, -34), (Sum.inr 535, 864), (Sum.inr 536, 864), (Sum.inr 539, 1728), (Sum.inr 552, 864), (Sum.inr 864, 864), (Sum.inr 866, 1728), (Sum.inr 876, 864), (Sum.inr 919, 864), (Sum.inr 921, 864), (Sum.inr 927, 1728), (Sum.inr 977, 1728), (Sum.inr 979, 1728), (Sum.inr 985, 1728), (Sum.inr 1000, 1728), (Sum.inr 1039, 864), (Sum.inr 1041, 1728), (Sum.inr 1079, 864), (Sum.inr 2479, 864), (Sum.inr 2722, 1728)]

def numericRow1492 : Integer.Sparse Master := [(Sum.inl 0, 3), (Sum.inl 6, 1), (Sum.inl 7, -16), (Sum.inl 1, 12), (Sum.inr 782, -864), (Sum.inr 785, -432), (Sum.inr 789, -432), (Sum.inr 804, -432), (Sum.inr 823, -432), (Sum.inr 977, -864), (Sum.inr 1035, -864), (Sum.inr 1040, -432), (Sum.inr 1041, -864), (Sum.inr 1080, -432), (Sum.inr 1240, -432), (Sum.inr 1597, -864), (Sum.inr 1645, -864), (Sum.inr 1707, -432), (Sum.inr 1710, -432), (Sum.inr 1724, -864), (Sum.inr 3299, -432), (Sum.inr 3308, -432), (Sum.inr 4406, 1728), (Sum.inr 4435, 3456), (Sum.inr 4450, 3456), (Sum.inr 4470, 3456), (Sum.inr 4474, 1728), (Sum.inr 4589, 1728), (Sum.inr 4607, 3456)]

def numericRow1493 : Integer.Sparse Master := [(Sum.inl 0, -212), (Sum.inl 5, 280), (Sum.inl 6, -70), (Sum.inl 2, -320), (Sum.inl 7, 160), (Sum.inl 35, 160), (Sum.inl 1, -190), (Sum.inr 1216, 2160), (Sum.inr 1240, 2160), (Sum.inr 1241, 4320), (Sum.inr 1360, 2160), (Sum.inr 1370, 2160), (Sum.inr 1371, 4320), (Sum.inr 1387, 4320), (Sum.inr 1415, 4320)]

def numericRow1494 : Integer.Sparse Master := [(Sum.inr 1033, 1), (Sum.inr 2015, 1), (Sum.inr 2099, 1), (Sum.inr 2203, 1), (Sum.inr 2259, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

def numericRow1495 : Integer.Sparse Master := [(Sum.inr 981, 1), (Sum.inr 1913, 1), (Sum.inr 2078, 1), (Sum.inr 2192, 1), (Sum.inr 2196, 1), (Sum.inr 2202, 1), (Sum.inr 4080, -1)]

def numericRow1496 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 981, 1), (Sum.inr 998, 1), (Sum.inr 1032, 1), (Sum.inr 2202, 1), (Sum.inr 4080, -1)]

def numericRow1497 : Integer.Sparse Master := [(Sum.inr 1909, 1), (Sum.inr 2076, 1), (Sum.inr 2195, 1), (Sum.inr 2202, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

def numericRow1498 : Integer.Sparse Master := [(Sum.inr 980, 1), (Sum.inr 2077, 1), (Sum.inr 2191, 2), (Sum.inr 4079, -1)]

def numericRow1499 : Integer.Sparse Master := [(Sum.inr 980, 3), (Sum.inr 1034, 1), (Sum.inr 4079, -1)]

def numericRow1500 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 2075, 1), (Sum.inr 2190, 1), (Sum.inr 2202, 1), (Sum.inr 4080, -1)]

def numericRow1501 : Integer.Sparse Master := [(Sum.inr 865, 1), (Sum.inr 866, 1), (Sum.inr 869, 1), (Sum.inr 977, 1), (Sum.inr 4080, -1)]

def numericRow1502 : Integer.Sparse Master := [(Sum.inr 699, 1), (Sum.inr 700, 1), (Sum.inr 703, 1), (Sum.inr 1597, 1), (Sum.inr 4069, -1)]

def numericRow1503 : Integer.Sparse Master := [(Sum.inr 1907, 1), (Sum.inr 2074, 1), (Sum.inr 2201, 1), (Sum.inr 2203, 2), (Sum.inr 4081, -1)]

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

def numericRow1504 : Integer.Sparse Master := [(Sum.inr 1076, 1), (Sum.inr 2049, 2), (Sum.inr 2230, 1), (Sum.inr 2282, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

def numericRow1505 : Integer.Sparse Master := [(Sum.inr 613, -1), (Sum.inr 932, -2), (Sum.inr 1049, -1), (Sum.inr 1079, -2), (Sum.inr 1083, -1), (Sum.inr 1525, -1), (Sum.inr 1681, -2), (Sum.inr 1708, -2), (Sum.inr 1728, -1), (Sum.inr 1738, -1), (Sum.inr 2058, -2), (Sum.inr 2216, -2), (Sum.inr 2266, -1), (Sum.inr 2278, -1), (Sum.inr 2279, -2), (Sum.inr 4176, 8), (Sum.inr 4184, 4), (Sum.inr 4188, 4), (Sum.inr 4345, 8), (Sum.inr 4353, 8), (Sum.inr 4357, 8), (Sum.inr 4459, 8), (Sum.inr 4464, 4), (Sum.inr 4475, 8), (Sum.inr 4478, 4), (Sum.inr 4480, 4)]

def numericRow1506 : Integer.Sparse Master := [(Sum.inr 1512, 2), (Sum.inr 1525, 1), (Sum.inr 1526, 1), (Sum.inr 1530, 1), (Sum.inr 1668, 2), (Sum.inr 1681, 2), (Sum.inr 1682, 2), (Sum.inr 1686, 2), (Sum.inr 1708, 2), (Sum.inr 1714, 2), (Sum.inr 1715, 2), (Sum.inr 1728, 1), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 1745, 1), (Sum.inr 1746, 1), (Sum.inr 2216, 2), (Sum.inr 2278, 1), (Sum.inr 2279, 1)]

def numericRow1507 : Integer.Sparse Master := [(Sum.inl 0, 3), (Sum.inl 6, 1), (Sum.inl 7, -16), (Sum.inl 1, 12), (Sum.inr 811, -864), (Sum.inr 824, -864), (Sum.inr 828, -432), (Sum.inr 831, -432), (Sum.inr 857, -432), (Sum.inr 858, -432), (Sum.inr 1005, -864), (Sum.inr 1044, -864), (Sum.inr 1083, -432), (Sum.inr 1087, -432), (Sum.inr 1294, -432), (Sum.inr 1623, -864), (Sum.inr 1728, -432), (Sum.inr 1737, -864), (Sum.inr 1739, -432), (Sum.inr 3305, -432), (Sum.inr 3308, -432), (Sum.inr 4400, 3456), (Sum.inr 4425, 3456), (Sum.inr 4427, 3456), (Sum.inr 4459, 3456), (Sum.inr 4462, 3456), (Sum.inr 4500, 1728), (Sum.inr 4504, 1728), (Sum.inr 4506, 1728), (Sum.inr 4607, 3456), (Sum.inr 4617, 1728)]

def numericRow1508 : Integer.Sparse Master := [(Sum.inr 608, -1), (Sum.inr 927, -2), (Sum.inr 1079, -2), (Sum.inr 1083, -2), (Sum.inr 1087, -1), (Sum.inr 1091, -1), (Sum.inr 1519, -1), (Sum.inr 1675, -2), (Sum.inr 1708, -2), (Sum.inr 1728, -2), (Sum.inr 1739, -1), (Sum.inr 1756, -1), (Sum.inr 2054, -2), (Sum.inr 2206, -2), (Sum.inr 2266, -1), (Sum.inr 2278, -1), (Sum.inr 4173, 8), (Sum.inr 4178, 4), (Sum.inr 4188, 4), (Sum.inr 4347, 8), (Sum.inr 4357, 8), (Sum.inr 4474, 8), (Sum.inr 4476, 4), (Sum.inr 4480, 4)]

def numericRow1509 : Integer.Sparse Master := [(Sum.inr 1508, 2), (Sum.inr 1519, 1), (Sum.inr 1520, 1), (Sum.inr 1526, 1), (Sum.inr 1675, 2), (Sum.inr 1676, 2), (Sum.inr 1682, 2), (Sum.inr 1708, 2), (Sum.inr 1709, 2), (Sum.inr 1728, 2), (Sum.inr 1729, 1), (Sum.inr 1739, 1), (Sum.inr 1740, 1), (Sum.inr 1756, 1), (Sum.inr 2206, 2), (Sum.inr 2266, 1)]

def numericRow1510 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, 80), (Sum.inr 554, -4320), (Sum.inr 555, -2160), (Sum.inr 556, -2160), (Sum.inr 563, -2160), (Sum.inr 668, -4320), (Sum.inr 670, -2160), (Sum.inr 671, -2160), (Sum.inr 692, -2160), (Sum.inr 879, -4320), (Sum.inr 881, -4320), (Sum.inr 882, -4320), (Sum.inr 892, -4320), (Sum.inr 1005, -4320), (Sum.inr 1009, -2160), (Sum.inr 1012, -2160), (Sum.inr 1041, -4320), (Sum.inr 1043, -2160), (Sum.inr 1050, -2160), (Sum.inr 1079, -4320), (Sum.inr 1080, -2160), (Sum.inr 1083, -2160), (Sum.inr 1556, -4320), (Sum.inr 1558, -4320), (Sum.inr 1559, -4320), (Sum.inr 1575, -4320), (Sum.inr 1623, -4320), (Sum.inr 1627, -2160), (Sum.inr 1630, -2160), (Sum.inr 1708, -4320), (Sum.inr 1710, -2160), (Sum.inr 1724, -4320), (Sum.inr 1725, -2160), (Sum.inr 1728, -2160), (Sum.inr 1751, -2160), (Sum.inr 2512, -4320), (Sum.inr 2743, -2160), (Sum.inr 3471, -4320), (Sum.inr 3548, -2160), (Sum.inr 3623, -2160), (Sum.inr 3627, -2160)]

def numericRow1511 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 6, 5), (Sum.inl 8, -80), (Sum.inl 1, -40), (Sum.inr 807, -8640), (Sum.inr 813, -2160), (Sum.inr 853, -2160), (Sum.inr 1000, -4320), (Sum.inr 1005, -4320), (Sum.inr 1041, -4320), (Sum.inr 1075, -2160), (Sum.inr 1087, -2160), (Sum.inr 1294, -2160), (Sum.inr 1605, -4320), (Sum.inr 1623, -4320), (Sum.inr 1653, -2160), (Sum.inr 1724, -4320), (Sum.inr 1739, -2160), (Sum.inr 3305, -2160), (Sum.inr 3309, -2160), (Sum.inr 4420, 17280), (Sum.inr 4453, 17280), (Sum.inr 4459, 17280), (Sum.inr 4492, 8640), (Sum.inr 4500, 8640), (Sum.inr 4603, 17280), (Sum.inr 4620, 8640)]

def numericRow1512 : Integer.Sparse Master := [(Sum.inr 1075, 1), (Sum.inr 2048, 2), (Sum.inr 2276, 1), (Sum.inr 2288, 1), (Sum.inr 4082, -1)]

def numericRow1513 : Integer.Sparse Master := [(Sum.inr 603, -2), (Sum.inr 611, -1), (Sum.inr 614, -2), (Sum.inr 922, -2), (Sum.inr 930, -2), (Sum.inr 933, -4), (Sum.inr 1041, -4), (Sum.inr 1046, -2), (Sum.inr 1050, -2), (Sum.inr 1517, -2), (Sum.inr 1535, -1), (Sum.inr 1536, -2), (Sum.inr 1673, -2), (Sum.inr 1690, -2), (Sum.inr 1691, -4), (Sum.inr 1724, -4), (Sum.inr 1750, -2), (Sum.inr 1751, -2), (Sum.inr 4083, 4)]

def numericRow1514 : Integer.Sparse Master := [(Sum.inr 600, -2), (Sum.inr 605, -1), (Sum.inr 608, -1), (Sum.inr 613, -1), (Sum.inr 919, -2), (Sum.inr 924, -2), (Sum.inr 927, -2), (Sum.inr 932, -2), (Sum.inr 1040, -2), (Sum.inr 1043, -1), (Sum.inr 1049, -1), (Sum.inr 1079, -2), (Sum.inr 1083, -1), (Sum.inr 1087, -1), (Sum.inr 1507, -2), (Sum.inr 1518, -1), (Sum.inr 1519, -1), (Sum.inr 1525, -1), (Sum.inr 1664, -2), (Sum.inr 1674, -2), (Sum.inr 1675, -2), (Sum.inr 1681, -2), (Sum.inr 1707, -2), (Sum.inr 1708, -2), (Sum.inr 1725, -1), (Sum.inr 1728, -1), (Sum.inr 1738, -1), (Sum.inr 1739, -1), (Sum.inr 4084, 4)]

def numericRow1515 : Integer.Sparse Master := [(Sum.inr 1074, 1), (Sum.inr 2047, 2), (Sum.inr 2261, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

def numericRow1516 : Integer.Sparse Master := [(Sum.inr 602, -1), (Sum.inr 921, -2), (Sum.inr 1080, -4), (Sum.inr 1094, -2), (Sum.inr 1509, -1), (Sum.inr 1666, -2), (Sum.inr 1710, -4), (Sum.inr 1741, -2), (Sum.inr 2052, -2), (Sum.inr 2193, -2), (Sum.inr 2247, -1), (Sum.inr 2290, -1), (Sum.inr 4170, 8), (Sum.inr 4179, 8), (Sum.inr 4348, 16), (Sum.inr 4494, 8), (Sum.inr 4500, 8)]

def numericRow1517 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 5, -40), (Sum.inl 2, -520), (Sum.inl 35, -160), (Sum.inl 1, 10), (Sum.inr 651, 2160), (Sum.inr 653, 2160), (Sum.inr 1347, 4320), (Sum.inr 1435, 2160), (Sum.inr 1436, 2160)]

def numericRow1518 : Integer.Sparse Master := [(Sum.inr 1503, 2), (Sum.inr 1509, 1), (Sum.inr 1513, 2), (Sum.inr 1666, 2), (Sum.inr 1669, 4), (Sum.inr 1700, 2), (Sum.inr 1710, 4), (Sum.inr 1716, 2), (Sum.inr 1741, 2), (Sum.inr 2193, 2), (Sum.inr 2247, 1)]

def numericRow1519 : Integer.Sparse Master := [(Sum.inr 598, 2), (Sum.inr 602, 1), (Sum.inr 607, 2), (Sum.inr 1080, 1), (Sum.inr 4085, -1)]

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

def numericRow1520 : Integer.Sparse Master := [(Sum.inr 598, 1), (Sum.inr 1078, 1), (Sum.inr 1080, 3), (Sum.inr 4085, -1)]

def numericRow1521 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 5, 200), (Sum.inl 6, -60), (Sum.inl 2, 80), (Sum.inl 35, -160), (Sum.inl 1, -50), (Sum.inr 1252, 2160), (Sum.inr 1270, 2160), (Sum.inr 1272, 2160), (Sum.inr 1306, 2160), (Sum.inr 1415, 4320)]

def numericRow1522 : Integer.Sparse Master := [(Sum.inr 1006, 1), (Sum.inr 1948, 1), (Sum.inr 2001, 1), (Sum.inr 2207, 1), (Sum.inr 2221, 1), (Sum.inr 2224, 1), (Sum.inr 4081, -1)]

def numericRow1523 : Integer.Sparse Master := [(Sum.inr 1001, 1), (Sum.inr 1946, 1), (Sum.inr 1998, 1), (Sum.inr 2220, 1), (Sum.inr 2224, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

def numericRow1524 : Integer.Sparse Master := [(Sum.inr 1008, 1), (Sum.inr 1949, 1), (Sum.inr 2002, 1), (Sum.inr 2217, 2), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

def numericRow1525 : Integer.Sparse Master := [(Sum.inr 1000, 2), (Sum.inr 1008, 1), (Sum.inr 1071, 1), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

def numericRow1526 : Integer.Sparse Master := [(Sum.inr 1005, 1), (Sum.inr 2000, 1), (Sum.inr 2206, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

def numericRow1527 : Integer.Sparse Master := [(Sum.inr 998, 1), (Sum.inr 1005, 2), (Sum.inr 1073, 1), (Sum.inr 4080, -1)]

def numericRow1528 : Integer.Sparse Master := [(Sum.inr 1000, 1), (Sum.inr 1997, 1), (Sum.inr 2215, 1), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

def numericRow1529 : Integer.Sparse Master := [(Sum.inr 876, 1), (Sum.inr 881, 1), (Sum.inr 891, 1), (Sum.inr 1000, 1), (Sum.inr 4082, -1)]

def numericRow1530 : Integer.Sparse Master := [(Sum.inr 999, 1), (Sum.inr 1996, 1), (Sum.inr 2203, 1), (Sum.inr 2224, 1), (Sum.inr 4081, -1)]

def numericRow1531 : Integer.Sparse Master := [(Sum.inr 786, 1), (Sum.inr 1638, 2), (Sum.inr 1699, 2), (Sum.inr 1706, 1), (Sum.inr 4068, -1)]

def numericRow1532 : Integer.Sparse Master := [(Sum.inr 783, 2), (Sum.inr 786, 1), (Sum.inr 1706, 1), (Sum.inr 4068, -1)]

def numericRow1533 : Integer.Sparse Master := [(Sum.inr 550, 1), (Sum.inr 803, 2), (Sum.inr 822, 1), (Sum.inr 4069, -1)]

def numericRow1534 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 1636, 2), (Sum.inr 1706, 1), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

def numericRow1535 : Integer.Sparse Master := [(Sum.inr 537, 1), (Sum.inr 732, 1), (Sum.inr 783, 2), (Sum.inr 4068, -1)]

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

def numericRow1536 : Integer.Sparse Master := [(Sum.inr 537, -1), (Sum.inr 542, -1), (Sum.inr 544, -2), (Sum.inr 662, -1), (Sum.inr 681, -1), (Sum.inr 682, -2), (Sum.inr 702, -1), (Sum.inr 704, -2), (Sum.inr 732, -1), (Sum.inr 737, -1), (Sum.inr 739, -2), (Sum.inr 760, -1), (Sum.inr 761, -2), (Sum.inr 783, -2), (Sum.inr 787, -2), (Sum.inr 790, -2), (Sum.inr 798, -1), (Sum.inr 803, -2), (Sum.inr 840, -1), (Sum.inr 841, -2), (Sum.inr 847, -2), (Sum.inr 848, -2), (Sum.inr 998, -1), (Sum.inr 1073, -1), (Sum.inr 1079, -2), (Sum.inr 1600, -1), (Sum.inr 1648, -1), (Sum.inr 1708, -2), (Sum.inr 4068, 4)]

def numericRow1537 : Integer.Sparse Master := [(Sum.inr 662, 1), (Sum.inr 681, 1), (Sum.inr 682, 2), (Sum.inr 760, 1), (Sum.inr 761, 2), (Sum.inr 798, 1), (Sum.inr 803, 2), (Sum.inr 840, 1), (Sum.inr 841, 2), (Sum.inr 847, 2), (Sum.inr 848, 2), (Sum.inr 998, 1), (Sum.inr 1073, 1), (Sum.inr 1079, 2), (Sum.inr 4068, 1)]

def numericRow1538 : Integer.Sparse Master := [(Sum.inr 732, 1), (Sum.inr 737, 1), (Sum.inr 739, 2), (Sum.inr 1648, 1), (Sum.inr 4068, -1)]

def numericRow1539 : Integer.Sparse Master := [(Sum.inr 550, -1), (Sum.inr 554, -2), (Sum.inr 557, -1), (Sum.inr 658, -1), (Sum.inr 668, -2), (Sum.inr 677, -1), (Sum.inr 713, -2), (Sum.inr 719, -1), (Sum.inr 751, -2), (Sum.inr 756, -1), (Sum.inr 783, -2), (Sum.inr 786, -1), (Sum.inr 803, -2), (Sum.inr 807, -4), (Sum.inr 811, -4), (Sum.inr 822, -1), (Sum.inr 824, -4), (Sum.inr 827, -2), (Sum.inr 980, -1), (Sum.inr 1041, -2), (Sum.inr 1044, -1), (Sum.inr 1616, -1), (Sum.inr 1724, -2), (Sum.inr 1737, -1), (Sum.inr 4069, 4)]

def numericRow1540 : Integer.Sparse Master := [(Sum.inr 4057, 2), (Sum.inr 4058, 1), (Sum.inr 4059, 2), (Sum.inr 4063, 2), (Sum.inr 4064, 2), (Sum.inr 4065, 4), (Sum.inr 4068, 2), (Sum.inr 4069, 6), (Sum.inr 4070, 2), (Sum.inr 4071, 2), (Sum.inr 4080, 2), (Sum.inr 4083, 1), (Sum.inr 4084, 2)]

def numericRow1541 : Integer.Sparse Master := [(Sum.inr 1700, 1), (Sum.inr 3057, 1), (Sum.inr 3072, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def numericRow1542 : Integer.Sparse Master := [(Sum.inr 1700, 1), (Sum.inr 1708, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def numericRow1543 : Integer.Sparse Master := [(Sum.inr 597, 1), (Sum.inr 1056, 1), (Sum.inr 1079, 3), (Sum.inr 4084, -1)]

def numericRow1544 : Integer.Sparse Master := [(Sum.inr 3286, 3), (Sum.inr 3292, 1), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def numericRow1545 : Integer.Sparse Master := [(Sum.inr 1699, 1), (Sum.inr 1706, 3), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

def numericRow1546 : Integer.Sparse Master := [(Sum.inr 1316, 3), (Sum.inr 1319, 1), (Sum.inr 1366, 1), (Sum.inr 2880, 1), (Sum.inr 4091, -1)]

def numericRow1547 : Integer.Sparse Master := [(Sum.inr 1699, 1), (Sum.inr 3239, 3), (Sum.inr 3244, 1), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

def numericRow1548 : Integer.Sparse Master := [(Sum.inr 1256, 1), (Sum.inr 2628, 1), (Sum.inr 2671, 1), (Sum.inr 2747, 3), (Sum.inr 4087, -1)]

def numericRow1549 : Integer.Sparse Master := [(Sum.inr 1644, 1), (Sum.inr 3057, 1), (Sum.inr 3289, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def numericRow1550 : Integer.Sparse Master := [(Sum.inr 1126, 1), (Sum.inr 1127, 1), (Sum.inr 1130, 2), (Sum.inr 1233, 1), (Sum.inr 2508, 1), (Sum.inr 4092, -1)]

def numericRow1551 : Integer.Sparse Master := [(Sum.inr 637, 1), (Sum.inr 1235, 1), (Sum.inr 1260, 3), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

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

def numericRow1552 : Integer.Sparse Master := [(Sum.inr 1636, 2), (Sum.inr 1638, 1), (Sum.inr 1644, 1), (Sum.inr 1706, 1), (Sum.inr 3289, 1), (Sum.inr 4068, -1)]

def numericRow1553 : Integer.Sparse Master := [(Sum.inr 1593, 1), (Sum.inr 1600, 2), (Sum.inr 1708, 1), (Sum.inr 3289, 1), (Sum.inr 4068, -1)]

def numericRow1554 : Integer.Sparse Master := [(Sum.inr 1708, 1), (Sum.inr 3289, 1), (Sum.inr 3303, 2), (Sum.inr 3304, 1), (Sum.inr 3307, 1), (Sum.inr 4068, -1)]

def numericRow1555 : Integer.Sparse Master := [(Sum.inr 1600, 1), (Sum.inr 3239, 1), (Sum.inr 3286, 1), (Sum.inr 3289, 2), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

def numericRow1556 : Integer.Sparse Master := [(Sum.inr 1706, 1), (Sum.inr 3289, 2), (Sum.inr 3292, 2), (Sum.inr 3307, 1), (Sum.inr 4068, -1)]

def numericRow1557 : Integer.Sparse Master := [(Sum.inr 1648, 1), (Sum.inr 3072, 1), (Sum.inr 3286, 1), (Sum.inr 3303, 2), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def numericRow1558 : Integer.Sparse Master := [(Sum.inr 1636, 1), (Sum.inr 1639, 1), (Sum.inr 1641, 1), (Sum.inr 1648, 1), (Sum.inr 1708, 1), (Sum.inr 3303, 1), (Sum.inr 4068, -1)]

def numericRow1559 : Integer.Sparse Master := [(Sum.inl 0, 34), (Sum.inl 6, 5), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, 170), (Sum.inr 592, -720), (Sum.inr 593, -2160), (Sum.inr 610, -720), (Sum.inr 1122, -2160), (Sum.inr 1135, -720), (Sum.inr 1187, -720), (Sum.inr 1188, -2160), (Sum.inr 1293, -2160), (Sum.inr 1294, -4320), (Sum.inr 1497, -720), (Sum.inr 1498, -2160), (Sum.inr 1524, -720), (Sum.inr 3053, -720), (Sum.inr 3244, -720), (Sum.inr 3245, -2160), (Sum.inr 3253, -2160), (Sum.inr 3269, -720), (Sum.inr 3304, -2160), (Sum.inr 3305, -4320), (Sum.inr 3308, -2160), (Sum.inr 3619, -720), (Sum.inr 3623, -2160)]

def numericRow1560 : Integer.Sparse Master := [(Sum.inl 0, -34), (Sum.inl 6, -5), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, -170), (Sum.inr 592, 720), (Sum.inr 593, 2160), (Sum.inr 610, 720), (Sum.inr 1122, 2160), (Sum.inr 1135, 720), (Sum.inr 1187, 720), (Sum.inr 1188, 2160), (Sum.inr 1293, 2160), (Sum.inr 1294, 4320), (Sum.inr 3053, 720)]

def numericRow1561 : Integer.Sparse Master := [(Sum.inr 1235, -1), (Sum.inr 1240, -3), (Sum.inr 2589, -1), (Sum.inr 2764, -3), (Sum.inr 3292, -1), (Sum.inr 3299, -3), (Sum.inr 3563, -1), (Sum.inr 3581, -3), (Sum.inr 4169, 4), (Sum.inr 4170, 4), (Sum.inr 4173, 12), (Sum.inr 4540, 4), (Sum.inr 4542, 12), (Sum.inr 4599, 12), (Sum.inr 4600, 12), (Sum.inr 4603, 24)]

def numericRow1562 : Integer.Sparse Master := [(Sum.inl 0, -80), (Sum.inl 5, 40), (Sum.inl 6, -15), (Sum.inl 2, 25), (Sum.inl 7, 240), (Sum.inl 35, 160), (Sum.inl 3, 240), (Sum.inl 1, -100), (Sum.inr 597, 2160), (Sum.inr 598, 2160), (Sum.inr 601, 6480), (Sum.inr 1125, 2160), (Sum.inr 1127, 6480), (Sum.inr 1233, 6480), (Sum.inr 1234, 6480), (Sum.inr 1237, 12960)]

def numericRow1563 : Integer.Sparse Master := [(Sum.inr 1502, 1), (Sum.inr 1503, 1), (Sum.inr 1508, 3), (Sum.inr 2688, 1), (Sum.inr 2702, 3), (Sum.inr 3257, 3), (Sum.inr 3289, 3), (Sum.inr 3292, 1), (Sum.inr 3294, 6), (Sum.inr 3299, 3), (Sum.inr 3563, 1), (Sum.inr 3581, 3)]

def numericRow1564 : Integer.Sparse Master := [(Sum.inr 637, 1), (Sum.inr 640, 3), (Sum.inr 651, 1), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

def numericRow1565 : Integer.Sparse Master := [(Sum.inl 0, -75), (Sum.inl 5, -20), (Sum.inl 6, 25), (Sum.inl 2, 65), (Sum.inl 7, -80), (Sum.inl 35, -80), (Sum.inl 8, -160), (Sum.inl 3, -80), (Sum.inl 52, -160), (Sum.inl 1, 115), (Sum.inr 1034, 1440), (Sum.inr 1073, 4320), (Sum.inr 1228, 4320), (Sum.inr 1235, 1440), (Sum.inr 1256, 1440), (Sum.inr 1260, 4320), (Sum.inr 1286, 4320), (Sum.inr 1291, 8640), (Sum.inr 1435, 1440)]

def numericRow1566 : Integer.Sparse Master := [(Sum.inr 1644, 1), (Sum.inr 1648, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

def numericRow1567 : Integer.Sparse Master := [(Sum.inl 0, 143), (Sum.inl 6, 15), (Sum.inl 7, -80), (Sum.inl 8, -160), (Sum.inl 1, -110), (Sum.inr 599, -1440), (Sum.inr 600, -2880), (Sum.inr 603, -2880), (Sum.inr 1126, -2880), (Sum.inr 1129, -2880), (Sum.inr 1235, -2880), (Sum.inr 1236, -5760), (Sum.inr 1240, -2880), (Sum.inr 1506, -1440), (Sum.inr 1507, -2880), (Sum.inr 1517, -2880), (Sum.inr 3256, -2880), (Sum.inr 3263, -2880), (Sum.inr 3292, -2880), (Sum.inr 3293, -5760), (Sum.inr 3299, -2880), (Sum.inr 3307, -2880), (Sum.inr 3308, -2880), (Sum.inr 3309, -5760), (Sum.inr 3602, -1440), (Sum.inr 3622, -2880)]

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

def numericRow1568 : Integer.Sparse Master := [(Sum.inl 0, -143), (Sum.inl 6, -15), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 1, 110), (Sum.inr 599, 1440), (Sum.inr 600, 2880), (Sum.inr 603, 2880), (Sum.inr 1126, 2880), (Sum.inr 1129, 2880), (Sum.inr 1235, 2880), (Sum.inr 1236, 5760), (Sum.inr 1240, 2880)]

def numericRow1569 : Integer.Sparse Master := [(Sum.inl 0, 37), (Sum.inl 6, -15), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 1, -70), (Sum.inr 1039, -2160), (Sum.inr 1079, -4320), (Sum.inr 1235, -4320), (Sum.inr 1293, -4320), (Sum.inr 1706, -2160), (Sum.inr 1708, -4320), (Sum.inr 3292, -4320), (Sum.inr 3304, -4320), (Sum.inr 3307, -4320), (Sum.inr 4599, 17280), (Sum.inr 4616, 17280)]

def numericRow1570 : Integer.Sparse Master := [(Sum.inr 1228, 1), (Sum.inr 2503, 1), (Sum.inr 2703, 1), (Sum.inr 2718, 2), (Sum.inr 2728, 1), (Sum.inr 4090, -1)]

def numericRow1571 : Integer.Sparse Master := [(Sum.inr 1129, -3), (Sum.inr 1135, -1), (Sum.inr 1240, -3), (Sum.inr 1293, -1), (Sum.inr 2721, -3), (Sum.inr 3263, -3), (Sum.inr 3269, -1), (Sum.inr 3299, -3), (Sum.inr 3304, -1), (Sum.inr 3532, -3), (Sum.inr 4149, 4), (Sum.inr 4150, 12), (Sum.inr 4169, 4), (Sum.inr 4589, 12), (Sum.inr 4590, 24), (Sum.inr 4599, 12)]

def numericRow1572 : Integer.Sparse Master := [(Sum.inl 0, -203), (Sum.inl 9, 320), (Sum.inl 58, -20), (Sum.inl 2, 155), (Sum.inl 69, 480), (Sum.inl 70, 160), (Sum.inl 71, 960), (Sum.inl 3, 1200), (Sum.inl 26, 480), (Sum.inl 4, 480), (Sum.inl 1, -970), (Sum.inr 577, 4320), (Sum.inr 578, 12960), (Sum.inr 597, 4320), (Sum.inr 1212, 12960), (Sum.inr 1213, 25920), (Sum.inr 1233, 12960)]

def numericRow1573 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1502, 1), (Sum.inr 1504, 3), (Sum.inr 3263, 3), (Sum.inr 3269, 1), (Sum.inr 3288, 3), (Sum.inr 3289, 3), (Sum.inr 3290, 6), (Sum.inr 3299, 3), (Sum.inr 3304, 1), (Sum.inr 3532, 3)]

def numericRow1574 : Integer.Sparse Master := [(Sum.inr 625, 3), (Sum.inr 629, 1), (Sum.inr 637, 1), (Sum.inr 1235, 1), (Sum.inr 4091, -1)]

def numericRow1575 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 6, -15), (Sum.inl 2, 55), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 3, 80), (Sum.inl 1, -90), (Sum.inr 567, -4320), (Sum.inr 571, -1440), (Sum.inr 599, -1440), (Sum.inr 1097, -4320), (Sum.inr 1100, -1440), (Sum.inr 1200, -4320), (Sum.inr 1235, -1440), (Sum.inr 1236, -8640), (Sum.inr 1240, -4320), (Sum.inr 1488, -4320), (Sum.inr 1491, -1440), (Sum.inr 1506, -1440), (Sum.inr 2880, -1440), (Sum.inr 3232, -4320), (Sum.inr 3234, -1440), (Sum.inr 3281, -4320), (Sum.inr 3292, -1440), (Sum.inr 3293, -8640), (Sum.inr 3299, -4320), (Sum.inr 3307, -4320), (Sum.inr 3617, -1440), (Sum.inr 3622, -4320)]

def numericRow1576 : Integer.Sparse Master := [(Sum.inl 0, -84), (Sum.inl 6, 15), (Sum.inl 2, -55), (Sum.inl 7, -80), (Sum.inl 8, -160), (Sum.inl 3, -80), (Sum.inl 1, 90), (Sum.inr 567, 4320), (Sum.inr 571, 1440), (Sum.inr 599, 1440), (Sum.inr 1097, 4320), (Sum.inr 1100, 1440), (Sum.inr 1200, 4320), (Sum.inr 1235, 1440), (Sum.inr 1236, 8640), (Sum.inr 1240, 4320), (Sum.inr 2880, 1440)]

def numericRow1577 : Integer.Sparse Master := [(Sum.inr 1183, 1), (Sum.inr 2398, 1), (Sum.inr 2669, 2), (Sum.inr 2676, 1), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

def numericRow1578 : Integer.Sparse Master := [(Sum.inr 1187, 1), (Sum.inr 2671, 4), (Sum.inr 4087, -1)]

def numericRow1579 : Integer.Sparse Master := [(Sum.inr 1100, 4), (Sum.inr 1187, 1), (Sum.inr 4087, -1)]

def numericRow1580 : Integer.Sparse Master := [(Sum.inr 1052, 1), (Sum.inr 2127, 1), (Sum.inr 2214, 1), (Sum.inr 2250, 2), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

def numericRow1581 : Integer.Sparse Master := [(Sum.inr 1032, 1), (Sum.inr 2098, 1), (Sum.inr 2202, 1), (Sum.inr 2240, 1), (Sum.inr 2250, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

def numericRow1582 : Integer.Sparse Master := [(Sum.inr 1034, 1), (Sum.inr 2100, 1), (Sum.inr 2241, 3), (Sum.inr 4079, -1)]

def numericRow1583 : Integer.Sparse Master := [(Sum.inr 732, 3), (Sum.inr 736, 1), (Sum.inr 1644, 1), (Sum.inr 4068, -1)]

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

def numericRow1584 : Integer.Sparse Master := [(Sum.inr 599, -1), (Sum.inr 1039, -2), (Sum.inr 1041, -4), (Sum.inr 1044, -2), (Sum.inr 1506, -1), (Sum.inr 1706, -2), (Sum.inr 1724, -4), (Sum.inr 1737, -2), (Sum.inr 2105, -1), (Sum.inr 2241, -1), (Sum.inr 2243, -4), (Sum.inr 4150, 8), (Sum.inr 4152, 8), (Sum.inr 4364, 8), (Sum.inr 4366, 8), (Sum.inr 4439, 16)]

def numericRow1585 : Integer.Sparse Master := [(Sum.inr 1504, 2), (Sum.inr 1506, 1), (Sum.inr 1510, 2), (Sum.inr 1703, 2), (Sum.inr 1706, 2), (Sum.inr 1711, 2), (Sum.inr 1713, 4), (Sum.inr 1724, 4), (Sum.inr 1737, 2), (Sum.inr 2241, 1), (Sum.inr 2243, 2)]

def numericRow1586 : Integer.Sparse Master := [(Sum.inr 599, 1), (Sum.inr 1039, 3), (Sum.inr 4083, -1)]

def numericRow1587 : Integer.Sparse Master := [(Sum.inl 0, 143), (Sum.inl 6, 15), (Sum.inl 7, -80), (Sum.inl 8, -160), (Sum.inl 1, -110), (Sum.inr 535, -8640), (Sum.inr 537, -8640), (Sum.inr 550, -4320), (Sum.inr 656, -8640), (Sum.inr 658, -4320), (Sum.inr 662, -8640), (Sum.inr 919, -8640), (Sum.inr 922, -8640), (Sum.inr 977, -17280), (Sum.inr 980, -8640), (Sum.inr 998, -8640), (Sum.inr 1040, -8640), (Sum.inr 1041, -17280), (Sum.inr 1079, -8640), (Sum.inr 1597, -17280), (Sum.inr 1600, -8640), (Sum.inr 1616, -8640), (Sum.inr 1664, -8640), (Sum.inr 1673, -8640), (Sum.inr 1707, -8640), (Sum.inr 1708, -8640), (Sum.inr 1724, -17280), (Sum.inr 2721, -8640), (Sum.inr 3532, -8640), (Sum.inr 3602, -4320), (Sum.inr 3622, -8640)]

def numericRow1588 : Integer.Sparse Master := [(Sum.inl 0, -143), (Sum.inl 6, -15), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 1, 110), (Sum.inr 535, 8640), (Sum.inr 537, 8640), (Sum.inr 550, 4320), (Sum.inr 919, 8640), (Sum.inr 922, 8640), (Sum.inr 977, 17280), (Sum.inr 980, 8640), (Sum.inr 998, 8640), (Sum.inr 1040, 8640), (Sum.inr 1041, 17280), (Sum.inr 1079, 8640), (Sum.inr 2721, 8640)]

def numericRow1589 : Integer.Sparse Master := [(Sum.inl 0, 37), (Sum.inl 6, -15), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 1, -70), (Sum.inr 783, -8640), (Sum.inr 786, -4320), (Sum.inr 803, -8640), (Sum.inr 822, -4320), (Sum.inr 1034, -8640), (Sum.inr 1039, -17280), (Sum.inr 1079, -8640), (Sum.inr 1235, -8640), (Sum.inr 1644, -8640), (Sum.inr 1706, -17280), (Sum.inr 1708, -8640), (Sum.inr 3292, -8640), (Sum.inr 3307, -4320), (Sum.inr 4449, 69120), (Sum.inr 4469, 34560), (Sum.inr 4473, 34560), (Sum.inr 4599, 34560)]

def numericRow1590 : Integer.Sparse Master := [(Sum.inr 1070, 1), (Sum.inr 2043, 1), (Sum.inr 2220, 1), (Sum.inr 2224, 1), (Sum.inr 2259, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

def numericRow1591 : Integer.Sparse Master := [(Sum.inr 1071, 1), (Sum.inr 2044, 1), (Sum.inr 2225, 1), (Sum.inr 2274, 2), (Sum.inr 2288, 1), (Sum.inr 4082, -1)]

def numericRow1592 : Integer.Sparse Master := [(Sum.inr 1073, 1), (Sum.inr 2046, 1), (Sum.inr 2260, 2), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

def numericRow1593 : Integer.Sparse Master := [(Sum.inr 600, -1), (Sum.inr 919, -1), (Sum.inr 1040, -1), (Sum.inr 1079, -2), (Sum.inr 1083, -2), (Sum.inr 1087, -2), (Sum.inr 1507, -1), (Sum.inr 1664, -1), (Sum.inr 1707, -1), (Sum.inr 1708, -2), (Sum.inr 1728, -2), (Sum.inr 1739, -2), (Sum.inr 2051, -1), (Sum.inr 2191, -1), (Sum.inr 2244, -1), (Sum.inr 2245, -1), (Sum.inr 2262, -1), (Sum.inr 2277, -1), (Sum.inr 4169, 4), (Sum.inr 4173, 4), (Sum.inr 4176, 8), (Sum.inr 4345, 8), (Sum.inr 4459, 8), (Sum.inr 4473, 4), (Sum.inr 4474, 4), (Sum.inr 4475, 8)]

def numericRow1594 : Integer.Sparse Master := [(Sum.inr 1502, 1), (Sum.inr 1507, 1), (Sum.inr 1508, 1), (Sum.inr 1512, 2), (Sum.inr 1664, 1), (Sum.inr 1668, 2), (Sum.inr 1699, 1), (Sum.inr 1707, 1), (Sum.inr 1708, 2), (Sum.inr 1709, 1), (Sum.inr 1714, 2), (Sum.inr 1715, 2), (Sum.inr 1728, 2), (Sum.inr 1739, 2), (Sum.inr 2191, 1), (Sum.inr 2244, 1), (Sum.inr 2245, 1)]

def numericRow1595 : Integer.Sparse Master := [(Sum.inr 599, -1), (Sum.inr 603, -3), (Sum.inr 610, -1), (Sum.inr 922, -3), (Sum.inr 929, -1), (Sum.inr 1039, -3), (Sum.inr 1041, -6), (Sum.inr 1044, -3), (Sum.inr 1506, -1), (Sum.inr 1517, -3), (Sum.inr 1524, -1), (Sum.inr 1673, -3), (Sum.inr 1680, -1), (Sum.inr 1706, -3), (Sum.inr 1724, -6), (Sum.inr 1737, -3), (Sum.inr 4083, 4)]

def numericRow1596 : Integer.Sparse Master := [(Sum.inr 995, 1), (Sum.inr 1940, 1), (Sum.inr 2201, 1), (Sum.inr 2219, 1), (Sum.inr 2224, 2), (Sum.inr 4081, -1)]

def numericRow1597 : Integer.Sparse Master := [(Sum.inr 1941, 1), (Sum.inr 2213, 2), (Sum.inr 2225, 2), (Sum.inr 4082, -1)]

def numericRow1598 : Integer.Sparse Master := [(Sum.inr 571, -4), (Sum.inr 592, -1), (Sum.inr 980, -12), (Sum.inr 1034, -4), (Sum.inr 1491, -4), (Sum.inr 1497, -1), (Sum.inr 1616, -12), (Sum.inr 1644, -4), (Sum.inr 4079, 4)]

def numericRow1599 : Integer.Sparse Master := [(Sum.inr 537, -3), (Sum.inr 541, -1), (Sum.inr 662, -3), (Sum.inr 674, -1), (Sum.inr 732, -3), (Sum.inr 736, -1), (Sum.inr 783, -6), (Sum.inr 786, -3), (Sum.inr 798, -3), (Sum.inr 803, -6), (Sum.inr 818, -1), (Sum.inr 822, -3), (Sum.inr 1034, -1), (Sum.inr 1039, -3), (Sum.inr 1644, -1), (Sum.inr 1706, -3), (Sum.inr 4068, 4)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock0 : Integer.Sparse (Fin 2886) := [(0, 9272200320), (1, 40990420560), (2, 14963621760), (3, 3008545920), (4, -18417761280), (5, 2070649920), (6, -14963621760), (7, 5917182000), (8, 9478498560), (9, 24964920000), (10, -7016282400), (11, -19285274880), (12, -4532866080), (13, -5679645120), (14, -206942400), (15, -11656704000), (16, -3645895920), (17, 4668639360), (18, 513062400), (19, -8117441760), (20, 26455253760), (21, -19821712320), (22, 13312972800), (23, 2022739200), (24, 11656704000), (25, 1839624000), (26, -265507200), (27, -4668639360), (28, -513062400), (29, -2207548800), (30, -2531729760), (31, -26455253760)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1034 : Integer.Sparse Master := [(Sum.inr 2740, -636663027329925120000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


