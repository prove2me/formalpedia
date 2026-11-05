-- Prove2me | Definitions.Def_OAIQ106E084
-- name    : OAIQ106E084
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:32:56.8795+00:00
-- url     : https://prove2.me/theorems/e9bbdc7e-b5fb-467c-a102-1067ecf7b479
-- title:
--   Definitions bundle OAIQ106E084 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5788 declarations of OpenAI's Lean: 5787 definitions and 1 instance. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.keyChunk0`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk1`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk10`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk11`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk12`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk13`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk14`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk15`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk16`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk17`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk18`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk19`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk2`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk20`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk21`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk22`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk23`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk24`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk25`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk26`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk27`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk28`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk29`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk3`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk30`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk31`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk32`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk33`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk34`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk35`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk36`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk37`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk38`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk39`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk4`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk40`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk41`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk42`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk43`, `OAI.MUB6.Certificate.MixedSemantics.keyChunk44` and 5747 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_MixedTargetBasic`, `MutuallyUnbiased_MixedSemantics_Code`, `MutuallyUnbiased_MixedSemantics_KeyMap`, `MutuallyUnbiased_MixedSemantics_KeyMap0`, `MutuallyUnbiased_MixedSemantics_KeyMap1`, `MutuallyUnbiased_MixedSemantics_KeyMap10`, `MutuallyUnbiased_MixedSemantics_KeyMap11`, `MutuallyUnbiased_MixedSemantics_KeyMap12`, `MutuallyUnbiased_MixedSemantics_KeyMap13`, `MutuallyUnbiased_MixedSemantics_KeyMap14`, `MutuallyUnbiased_MixedSemantics_KeyMap15`, `MutuallyUnbiased_MixedSemantics_KeyMap16`, `MutuallyUnbiased_MixedSemantics_KeyMap17`, `MutuallyUnbiased_MixedSemantics_KeyMap18`, `MutuallyUnbiased_MixedSemantics_KeyMap19`, `MutuallyUnbiased_MixedSemantics_KeyMap2`, `MutuallyUnbiased_MixedSemantics_KeyMap20`, `MutuallyUnbiased_MixedSemantics_KeyMap21`, `MutuallyUnbiased_MixedSemantics_KeyMap22`, `MutuallyUnbiased_MixedSemantics_KeyMap23`, `MutuallyUnbiased_MixedSemantics_KeyMap24`, `MutuallyUnbiased_MixedSemantics_KeyMap25`, `MutuallyUnbiased_MixedSemantics_KeyMap26`, `MutuallyUnbiased_MixedSemantics_KeyMap27`, `MutuallyUnbiased_MixedSemantics_KeyMap28`, `MutuallyUnbiased_MixedSemantics_KeyMap29`, `MutuallyUnbiased_MixedSemantics_KeyMap3`, `MutuallyUnbiased_MixedSemantics_KeyMap30`, `MutuallyUnbiased_MixedSemantics_KeyMap31`, `MutuallyUnbiased_MixedSemantics_KeyMap32`, `MutuallyUnbiased_MixedSemantics_KeyMap33`, `MutuallyUnbiased_MixedSemantics_KeyMap34`, `MutuallyUnbiased_MixedSemantics_KeyMap35`, `MutuallyUnbiased_MixedSemantics_KeyMap36`, `MutuallyUnbiased_MixedSemantics_KeyMap37`, `MutuallyUnbiased_MixedSemantics_KeyMap38`, `MutuallyUnbiased_MixedSemantics_KeyMap39`, `MutuallyUnbiased_MixedSemantics_KeyMap4`, `MutuallyUnbiased_MixedSemantics_KeyMap40`, `MutuallyUnbiased_MixedSemantics_KeyMap41`, `MutuallyUnbiased_MixedSemantics_KeyMap42`, `MutuallyUnbiased_MixedSemantics_KeyMap43`, `MutuallyUnbiased_MixedSemantics_KeyMap44`, `MutuallyUnbiased_MixedSemantics_KeyMap45`, `MutuallyUnbiased_MixedSemantics_KeyMap46`, `MutuallyUnbiased_MixedSemantics_KeyMap47`, `MutuallyUnbiased_MixedSemantics_KeyMap48`, `MutuallyUnbiased_MixedSemantics_KeyMap49`, `MutuallyUnbiased_MixedSemantics_KeyMap5`, `MutuallyUnbiased_MixedSemantics_KeyMap50`, `MutuallyUnbiased_MixedSemantics_KeyMap6`, `MutuallyUnbiased_MixedSemantics_KeyMap7`, `MutuallyUnbiased_MixedSemantics_KeyMap8`, `MutuallyUnbiased_MixedSemantics_KeyMap9`, `MutuallyUnbiased_MixedSemantics_Single0`, `MutuallyUnbiased_MixedSemantics_Single1`, `MutuallyUnbiased_MixedSemantics_Single2`, `MutuallyUnbiased_MixedSemantics_Single3`, `MutuallyUnbiased_MixedSemantics_Single4`, `MutuallyUnbiased_MixedSemantics_Single5`, `MutuallyUnbiased_MixedSemantics_Single6`, `MutuallyUnbiased_MixedSemantics_Single7`, `MutuallyUnbiased_MixedSemantics_SingleGroup0`, `MutuallyUnbiased_MixedSemantics_SingleGroup1`, `MutuallyUnbiased_MixedSemantics_SingleGroup10`, `MutuallyUnbiased_MixedSemantics_SingleGroup11`, `MutuallyUnbiased_MixedSemantics_SingleGroup12`, `MutuallyUnbiased_MixedSemantics_SingleGroup13`, `MutuallyUnbiased_MixedSemantics_SingleGroup14`, `MutuallyUnbiased_MixedSemantics_SingleGroup15`, `MutuallyUnbiased_MixedSemantics_SingleGroup16`, `MutuallyUnbiased_MixedSemantics_SingleGroup17`, `MutuallyUnbiased_MixedSemantics_SingleGroup18`, `MutuallyUnbiased_MixedSemantics_SingleGroup19`, `MutuallyUnbiased_MixedSemantics_SingleGroup2`, `MutuallyUnbiased_MixedSemantics_SingleGroup20`, `MutuallyUnbiased_MixedSemantics_SingleGroup21`, `MutuallyUnbiased_MixedSemantics_SingleGroup22`, `MutuallyUnbiased_MixedSemantics_SingleGroup23`, `MutuallyUnbiased_MixedSemantics_SingleGroup24`, `MutuallyUnbiased_MixedSemantics_SingleGroup25`, `MutuallyUnbiased_MixedSemantics_SingleGroup26`, `MutuallyUnbiased_MixedSemantics_SingleGroup27`, `MutuallyUnbiased_MixedSemantics_SingleGroup28`, `MutuallyUnbiased_MixedSemantics_SingleGroup29`, `MutuallyUnbiased_MixedSemantics_SingleGroup3`, `MutuallyUnbiased_MixedSemantics_SingleGroup30`, `MutuallyUnbiased_MixedSemantics_SingleGroup31`, `MutuallyUnbiased_MixedSemantics_SingleGroup32`, `MutuallyUnbiased_MixedSemantics_SingleGroup4`, `MutuallyUnbiased_MixedSemantics_SingleGroup5`, `MutuallyUnbiased_MixedSemantics_SingleGroup6`, `MutuallyUnbiased_MixedSemantics_SingleGroup7`, `MutuallyUnbiased_MixedSemantics_SingleGroup8`, `MutuallyUnbiased_MixedSemantics_SingleGroup9`, `MutuallyUnbiased_MixedSemantics_SinglePriority`, `MutuallyUnbiased_MixedSemantics_Values0`, `MutuallyUnbiased_MixedSemantics_Values1`, `MutuallyUnbiased_MixedSemantics_Values10`, `MutuallyUnbiased_MixedSemantics_Values11`, `MutuallyUnbiased_MixedSemantics_Values12`, `MutuallyUnbiased_MixedSemantics_Values13`, `MutuallyUnbiased_MixedSemantics_Values14`, `MutuallyUnbiased_MixedSemantics_Values15`, `MutuallyUnbiased_MixedSemantics_Values16`, `MutuallyUnbiased_MixedSemantics_Values17`, `MutuallyUnbiased_MixedSemantics_Values18`, `MutuallyUnbiased_MixedSemantics_Values19`, `MutuallyUnbiased_MixedSemantics_Values2`, `MutuallyUnbiased_MixedSemantics_Values20`, `MutuallyUnbiased_MixedSemantics_Values21`, `MutuallyUnbiased_MixedSemantics_Values22`, `MutuallyUnbiased_MixedSemantics_Values23`, `MutuallyUnbiased_MixedSemantics_Values24`, `MutuallyUnbiased_MixedSemantics_Values25`, `MutuallyUnbiased_MixedSemantics_Values26`, `MutuallyUnbiased_MixedSemantics_Values27`, `MutuallyUnbiased_MixedSemantics_Values28`, `MutuallyUnbiased_MixedSemantics_Values29`, `MutuallyUnbiased_MixedSemantics_Values3`, `MutuallyUnbiased_MixedSemantics_Values30`, `MutuallyUnbiased_MixedSemantics_Values31`, `MutuallyUnbiased_MixedSemantics_Values32`, `MutuallyUnbiased_MixedSemantics_Values33`, `MutuallyUnbiased_MixedSemantics_Values34`, `MutuallyUnbiased_MixedSemantics_Values35`, `MutuallyUnbiased_MixedSemantics_Values36`, `MutuallyUnbiased_MixedSemantics_Values37`, `MutuallyUnbiased_MixedSemantics_Values38`, `MutuallyUnbiased_MixedSemantics_Values39`, `MutuallyUnbiased_MixedSemantics_Values4`, `MutuallyUnbiased_MixedSemantics_Values40`, `MutuallyUnbiased_MixedSemantics_Values41`, `MutuallyUnbiased_MixedSemantics_Values42`, `MutuallyUnbiased_MixedSemantics_Values43`, `MutuallyUnbiased_MixedSemantics_Values44`, `MutuallyUnbiased_MixedSemantics_Values45`, `MutuallyUnbiased_MixedSemantics_Values46`, `MutuallyUnbiased_MixedSemantics_Values47`, `MutuallyUnbiased_MixedSemantics_Values48`, `MutuallyUnbiased_MixedSemantics_Values49`, `MutuallyUnbiased_MixedSemantics_Values5`, `MutuallyUnbiased_MixedSemantics_Values50`, `MutuallyUnbiased_MixedSemantics_Values51`, `MutuallyUnbiased_MixedSemantics_Values52`, `MutuallyUnbiased_MixedSemantics_Values53`, `MutuallyUnbiased_MixedSemantics_Values54`, `MutuallyUnbiased_MixedSemantics_Values55`, `MutuallyUnbiased_MixedSemantics_Values56`, `MutuallyUnbiased_MixedSemantics_Values57`, `MutuallyUnbiased_MixedSemantics_Values58`, `MutuallyUnbiased_MixedSemantics_Values59`, `MutuallyUnbiased_MixedSemantics_Values6`, `MutuallyUnbiased_MixedSemantics_Values60`, `MutuallyUnbiased_MixedSemantics_Values61`, `MutuallyUnbiased_MixedSemantics_Values62`, `MutuallyUnbiased_MixedSemantics_Values63`, `MutuallyUnbiased_MixedSemantics_Values64`, `MutuallyUnbiased_MixedSemantics_Values65`, `MutuallyUnbiased_MixedSemantics_Values66`, `MutuallyUnbiased_MixedSemantics_Values67`, `MutuallyUnbiased_MixedSemantics_Values68`, `MutuallyUnbiased_MixedSemantics_Values69`, `MutuallyUnbiased_MixedSemantics_Values7`, `MutuallyUnbiased_MixedSemantics_Values70`, `MutuallyUnbiased_MixedSemantics_Values71`, `MutuallyUnbiased_MixedSemantics_Values72`, `MutuallyUnbiased_MixedSemantics_Values73`, `MutuallyUnbiased_MixedSemantics_Values74`, `MutuallyUnbiased_MixedSemantics_Values75`, `MutuallyUnbiased_MixedSemantics_Values76`, `MutuallyUnbiased_MixedSemantics_Values77`, `MutuallyUnbiased_MixedSemantics_Values78`, `MutuallyUnbiased_MixedSemantics_Values79`, `MutuallyUnbiased_MixedSemantics_Values8`, `MutuallyUnbiased_MixedSemantics_Values80`, `MutuallyUnbiased_MixedSemantics_Values81`, `MutuallyUnbiased_MixedSemantics_Values82`, `MutuallyUnbiased_MixedSemantics_Values83`, `MutuallyUnbiased_MixedSemantics_Values84`, `MutuallyUnbiased_MixedSemantics_Values85`, `MutuallyUnbiased_MixedSemantics_Values9`, `MutuallyUnbiased_PairSemantics_Values0`, `MutuallyUnbiased_PairSemantics_Values1`, `MutuallyUnbiased_PairSemantics_Values15`, `MutuallyUnbiased_PairSemantics_Values16`, `MutuallyUnbiased_PairSemantics_Values17`, `MutuallyUnbiased_PairSemantics_Values18`, `MutuallyUnbiased_PairSemantics_Values19`, `MutuallyUnbiased_PairSemantics_Values2`, `MutuallyUnbiased_PairSemantics_Values20`, `MutuallyUnbiased_PairSemantics_Values21`.
--
--   **Imports.** It imports the bundle `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E085`, `OAIQ106E124`, `OAIQ106E125`, `OAIQ106E126`, `OAIQ106E127`, `OAIQ106E128` and `OAIQ106E129`; the statements `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e` and `OAI.MUB6.Certificate.PairSemantics.sound1399_e`; the proofs of `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e` and `OAI.MUB6.pair_cross_certificate_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Code
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

instance instInhabitedCode : Inhabited Code := ⟨⟨0, 0, 0, 0, Fin.elim0⟩⟩

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk0 : Array Master := #[Sum.inl 0, Sum.inl 9, Sum.inl 58, Sum.inl 5, Sum.inl 6, Sum.inl 256, Sum.inl 257, Sum.inl 259, Sum.inl 59, Sum.inl 260, Sum.inl 60, Sum.inl 262, Sum.inl 263, Sum.inl 264, Sum.inl 266, Sum.inl 61, Sum.inl 62, Sum.inl 32, Sum.inl 267, Sum.inl 268, Sum.inl 63, Sum.inl 64, Sum.inl 271, Sum.inl 65, Sum.inl 33, Sum.inl 273, Sum.inl 66, Sum.inl 67, Sum.inl 275, Sum.inl 34, Sum.inl 276, Sum.inl 68, Sum.inl 2, Sum.inl 277, Sum.inl 69, Sum.inl 70, Sum.inl 278, Sum.inl 71, Sum.inl 279, Sum.inl 280, Sum.inl 281, Sum.inl 282, Sum.inl 72, Sum.inl 73, Sum.inl 74, Sum.inl 75, Sum.inl 284, Sum.inl 286, Sum.inl 287, Sum.inl 288, Sum.inl 289, Sum.inl 76, Sum.inl 290, Sum.inl 291, Sum.inl 293, Sum.inl 77, Sum.inl 78, Sum.inl 299, Sum.inl 300, Sum.inl 79, Sum.inl 80, Sum.inl 81, Sum.inl 306, Sum.inl 307]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk1 : Array Master := #[Sum.inl 10, Sum.inl 308, Sum.inl 7, Sum.inl 309, Sum.inl 35, Sum.inl 82, Sum.inl 310, Sum.inl 8, Sum.inl 311, Sum.inl 312, Sum.inl 83, Sum.inl 84, Sum.inl 313, Sum.inl 314, Sum.inl 315, Sum.inl 85, Sum.inl 316, Sum.inl 317, Sum.inl 318, Sum.inl 319, Sum.inl 321, Sum.inl 322, Sum.inl 323, Sum.inl 324, Sum.inl 325, Sum.inl 86, Sum.inl 326, Sum.inl 327, Sum.inl 328, Sum.inl 329, Sum.inl 330, Sum.inl 352, Sum.inl 87, Sum.inl 36, Sum.inl 37, Sum.inl 38, Sum.inl 89, Sum.inl 39, Sum.inl 40, Sum.inl 378, Sum.inl 379, Sum.inl 383, Sum.inl 41, Sum.inl 94, Sum.inl 95, Sum.inl 97, Sum.inl 98, Sum.inl 392, Sum.inl 99, Sum.inl 100, Sum.inl 101, Sum.inl 42, Sum.inl 102, Sum.inl 398, Sum.inl 399, Sum.inl 400, Sum.inl 103, Sum.inl 104, Sum.inl 105, Sum.inl 425, Sum.inl 426, Sum.inl 106, Sum.inl 428, Sum.inl 107]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk10 : Array Master := #[Sum.inr 1026, Sum.inr 1027, Sum.inr 1028, Sum.inr 1029, Sum.inr 1030, Sum.inr 1031, Sum.inr 1032, Sum.inr 1033, Sum.inr 1034, Sum.inr 1035, Sum.inr 1036, Sum.inr 1037, Sum.inr 1039, Sum.inr 1040, Sum.inr 1041, Sum.inr 1042, Sum.inr 1043, Sum.inr 1044, Sum.inr 1045, Sum.inr 1046, Sum.inr 1047, Sum.inr 1048, Sum.inr 1049, Sum.inr 1050, Sum.inr 1051, Sum.inr 1052, Sum.inr 1053, Sum.inr 1054, Sum.inr 1055, Sum.inr 1056, Sum.inr 1057, Sum.inr 1058, Sum.inr 1059, Sum.inr 1060, Sum.inr 1061, Sum.inr 1062, Sum.inr 1063, Sum.inr 1064, Sum.inr 1066, Sum.inr 1067, Sum.inr 1068, Sum.inr 1069, Sum.inr 1070, Sum.inr 1071, Sum.inr 1072, Sum.inr 1073, Sum.inr 1074, Sum.inr 1075, Sum.inr 1076, Sum.inr 1077, Sum.inr 1078, Sum.inr 1079, Sum.inr 1080, Sum.inr 1083, Sum.inr 1084, Sum.inr 1087, Sum.inr 1088, Sum.inr 1091, Sum.inr 1092, Sum.inr 1093, Sum.inr 1094, Sum.inr 1097, Sum.inr 1098, Sum.inr 1099]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk11 : Array Master := #[Sum.inr 1100, Sum.inr 1101, Sum.inr 1102, Sum.inr 1103, Sum.inr 1104, Sum.inr 1105, Sum.inr 1106, Sum.inr 1107, Sum.inr 1108, Sum.inr 1109, Sum.inr 1110, Sum.inr 1111, Sum.inr 1112, Sum.inr 1113, Sum.inr 1114, Sum.inr 1115, Sum.inr 1116, Sum.inr 1117, Sum.inr 1118, Sum.inr 1119, Sum.inr 1120, Sum.inr 1121, Sum.inr 1122, Sum.inr 1123, Sum.inr 1124, Sum.inr 1125, Sum.inr 1126, Sum.inr 1127, Sum.inr 1128, Sum.inr 1129, Sum.inr 1130, Sum.inr 1131, Sum.inr 1132, Sum.inr 1133, Sum.inr 1134, Sum.inr 1135, Sum.inr 1136, Sum.inr 1137, Sum.inr 1138, Sum.inr 1139, Sum.inr 1140, Sum.inr 1141, Sum.inr 1142, Sum.inr 1143, Sum.inr 1144, Sum.inr 1145, Sum.inr 1146, Sum.inr 1147, Sum.inr 1148, Sum.inr 1149, Sum.inr 1150, Sum.inr 1151, Sum.inr 1152, Sum.inr 1153, Sum.inr 1154, Sum.inr 1155, Sum.inr 1156, Sum.inr 1157, Sum.inr 1158, Sum.inr 1159, Sum.inr 1160, Sum.inr 1169, Sum.inr 1171, Sum.inr 1174]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk12 : Array Master := #[Sum.inr 1178, Sum.inr 1179, Sum.inr 1180, Sum.inr 1181, Sum.inr 1182, Sum.inr 1183, Sum.inr 1184, Sum.inr 1185, Sum.inr 1186, Sum.inr 1187, Sum.inr 1188, Sum.inr 1189, Sum.inr 1190, Sum.inr 1191, Sum.inr 1192, Sum.inr 1193, Sum.inr 1194, Sum.inr 1195, Sum.inr 1196, Sum.inr 1197, Sum.inr 1198, Sum.inr 1199, Sum.inr 1200, Sum.inr 1201, Sum.inr 1202, Sum.inr 1203, Sum.inr 1204, Sum.inr 1205, Sum.inr 1206, Sum.inr 1208, Sum.inr 1209, Sum.inr 1210, Sum.inr 1211, Sum.inr 1212, Sum.inr 1213, Sum.inr 1214, Sum.inr 1215, Sum.inr 1216, Sum.inr 1217, Sum.inr 1218, Sum.inr 1219, Sum.inr 1220, Sum.inr 1221, Sum.inr 1222, Sum.inr 1224, Sum.inr 1226, Sum.inr 1227, Sum.inr 1228, Sum.inr 1229, Sum.inr 1230, Sum.inr 1231, Sum.inr 1233, Sum.inr 1234, Sum.inr 1235, Sum.inr 1236, Sum.inr 1237, Sum.inr 1238, Sum.inr 1239, Sum.inr 1240, Sum.inr 1241, Sum.inr 1242, Sum.inr 1243, Sum.inr 1244, Sum.inr 1245]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk13 : Array Master := #[Sum.inr 1246, Sum.inr 1247, Sum.inr 1248, Sum.inr 1249, Sum.inr 1250, Sum.inr 1252, Sum.inr 1253, Sum.inr 1256, Sum.inr 1257, Sum.inr 1258, Sum.inr 1259, Sum.inr 1260, Sum.inr 1261, Sum.inr 1262, Sum.inr 1263, Sum.inr 1264, Sum.inr 1268, Sum.inr 1270, Sum.inr 1272, Sum.inr 1273, Sum.inr 1276, Sum.inr 1277, Sum.inr 1278, Sum.inr 1279, Sum.inr 1280, Sum.inr 1282, Sum.inr 1283, Sum.inr 1286, Sum.inr 1287, Sum.inr 1288, Sum.inr 1289, Sum.inr 1291, Sum.inr 1292, Sum.inr 1293, Sum.inr 1294, Sum.inr 1295, Sum.inr 1296, Sum.inr 1297, Sum.inr 1303, Sum.inr 1306, Sum.inr 1309, Sum.inr 1310, Sum.inr 1314, Sum.inr 1315, Sum.inr 1316, Sum.inr 1317, Sum.inr 1318, Sum.inr 1319, Sum.inr 1320, Sum.inr 1321, Sum.inr 1322, Sum.inr 1323, Sum.inr 1324, Sum.inr 1325, Sum.inr 1326, Sum.inr 1327, Sum.inr 1328, Sum.inr 1330, Sum.inr 1332, Sum.inr 1333, Sum.inr 1334, Sum.inr 1335, Sum.inr 1336, Sum.inr 1337]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk14 : Array Master := #[Sum.inr 1338, Sum.inr 1347, Sum.inr 1348, Sum.inr 1354, Sum.inr 1355, Sum.inr 1356, Sum.inr 1357, Sum.inr 1358, Sum.inr 1359, Sum.inr 1360, Sum.inr 1361, Sum.inr 1362, Sum.inr 1363, Sum.inr 1364, Sum.inr 1366, Sum.inr 1367, Sum.inr 1368, Sum.inr 1369, Sum.inr 1370, Sum.inr 1371, Sum.inr 1372, Sum.inr 1373, Sum.inr 1374, Sum.inr 1375, Sum.inr 1378, Sum.inr 1380, Sum.inr 1382, Sum.inr 1383, Sum.inr 1384, Sum.inr 1385, Sum.inr 1387, Sum.inr 1388, Sum.inr 1389, Sum.inr 1390, Sum.inr 1391, Sum.inr 1392, Sum.inr 1394, Sum.inr 1400, Sum.inr 1403, Sum.inr 1404, Sum.inr 1406, Sum.inr 1407, Sum.inr 1408, Sum.inr 1415, Sum.inr 1418, Sum.inr 1421, Sum.inr 1422, Sum.inr 1423, Sum.inr 1424, Sum.inr 1425, Sum.inr 1433, Sum.inr 1435, Sum.inr 1436, Sum.inr 1437, Sum.inr 1438, Sum.inr 1440, Sum.inr 1457, Sum.inr 1458, Sum.inr 1459, Sum.inr 1460, Sum.inr 1461, Sum.inr 1462, Sum.inr 1463, Sum.inr 1464]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk15 : Array Master := #[Sum.inr 1465, Sum.inr 1466, Sum.inr 1467, Sum.inr 1474, Sum.inr 1488, Sum.inr 1489, Sum.inr 1490, Sum.inr 1491, Sum.inr 1492, Sum.inr 1493, Sum.inr 1494, Sum.inr 1495, Sum.inr 1496, Sum.inr 1497, Sum.inr 1498, Sum.inr 1499, Sum.inr 1500, Sum.inr 1501, Sum.inr 1502, Sum.inr 1503, Sum.inr 1504, Sum.inr 1505, Sum.inr 1506, Sum.inr 1507, Sum.inr 1508, Sum.inr 1509, Sum.inr 1510, Sum.inr 1511, Sum.inr 1512, Sum.inr 1513, Sum.inr 1514, Sum.inr 1515, Sum.inr 1516, Sum.inr 1517, Sum.inr 1518, Sum.inr 1519, Sum.inr 1520, Sum.inr 1521, Sum.inr 1522, Sum.inr 1523, Sum.inr 1524, Sum.inr 1525, Sum.inr 1526, Sum.inr 1527, Sum.inr 1528, Sum.inr 1529, Sum.inr 1530, Sum.inr 1531, Sum.inr 1532, Sum.inr 1533, Sum.inr 1534, Sum.inr 1535, Sum.inr 1536, Sum.inr 1537, Sum.inr 1538, Sum.inr 1539, Sum.inr 1540, Sum.inr 1541, Sum.inr 1550, Sum.inr 1552, Sum.inr 1553, Sum.inr 1554, Sum.inr 1555, Sum.inr 1556]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk16 : Array Master := #[Sum.inr 1558, Sum.inr 1559, Sum.inr 1561, Sum.inr 1562, Sum.inr 1563, Sum.inr 1565, Sum.inr 1566, Sum.inr 1567, Sum.inr 1568, Sum.inr 1569, Sum.inr 1570, Sum.inr 1573, Sum.inr 1575, Sum.inr 1577, Sum.inr 1578, Sum.inr 1586, Sum.inr 1587, Sum.inr 1588, Sum.inr 1589, Sum.inr 1590, Sum.inr 1591, Sum.inr 1593, Sum.inr 1594, Sum.inr 1597, Sum.inr 1599, Sum.inr 1600, Sum.inr 1601, Sum.inr 1602, Sum.inr 1603, Sum.inr 1604, Sum.inr 1605, Sum.inr 1606, Sum.inr 1607, Sum.inr 1608, Sum.inr 1609, Sum.inr 1610, Sum.inr 1611, Sum.inr 1612, Sum.inr 1613, Sum.inr 1615, Sum.inr 1616, Sum.inr 1617, Sum.inr 1618, Sum.inr 1619, Sum.inr 1620, Sum.inr 1623, Sum.inr 1624, Sum.inr 1626, Sum.inr 1627, Sum.inr 1628, Sum.inr 1629, Sum.inr 1630, Sum.inr 1632, Sum.inr 1633, Sum.inr 1634, Sum.inr 1635, Sum.inr 1636, Sum.inr 1637, Sum.inr 1638, Sum.inr 1639, Sum.inr 1640, Sum.inr 1641, Sum.inr 1642, Sum.inr 1643]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk17 : Array Master := #[Sum.inr 1644, Sum.inr 1645, Sum.inr 1646, Sum.inr 1647, Sum.inr 1648, Sum.inr 1649, Sum.inr 1650, Sum.inr 1651, Sum.inr 1652, Sum.inr 1653, Sum.inr 1654, Sum.inr 1655, Sum.inr 1656, Sum.inr 1657, Sum.inr 1658, Sum.inr 1659, Sum.inr 1660, Sum.inr 1661, Sum.inr 1664, Sum.inr 1666, Sum.inr 1667, Sum.inr 1668, Sum.inr 1669, Sum.inr 1670, Sum.inr 1672, Sum.inr 1673, Sum.inr 1674, Sum.inr 1675, Sum.inr 1676, Sum.inr 1677, Sum.inr 1678, Sum.inr 1679, Sum.inr 1680, Sum.inr 1681, Sum.inr 1682, Sum.inr 1683, Sum.inr 1684, Sum.inr 1685, Sum.inr 1686, Sum.inr 1687, Sum.inr 1688, Sum.inr 1689, Sum.inr 1690, Sum.inr 1691, Sum.inr 1692, Sum.inr 1693, Sum.inr 1694, Sum.inr 1695, Sum.inr 1697, Sum.inr 1699, Sum.inr 1700, Sum.inr 1703, Sum.inr 1704, Sum.inr 1706, Sum.inr 1707, Sum.inr 1708, Sum.inr 1709, Sum.inr 1710, Sum.inr 1711, Sum.inr 1712, Sum.inr 1713, Sum.inr 1714, Sum.inr 1715, Sum.inr 1716]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk18 : Array Master := #[Sum.inr 1720, Sum.inr 1721, Sum.inr 1722, Sum.inr 1723, Sum.inr 1724, Sum.inr 1725, Sum.inr 1728, Sum.inr 1729, Sum.inr 1734, Sum.inr 1735, Sum.inr 1736, Sum.inr 1737, Sum.inr 1738, Sum.inr 1739, Sum.inr 1740, Sum.inr 1741, Sum.inr 1742, Sum.inr 1743, Sum.inr 1744, Sum.inr 1745, Sum.inr 1746, Sum.inr 1747, Sum.inr 1748, Sum.inr 1749, Sum.inr 1750, Sum.inr 1751, Sum.inr 1752, Sum.inr 1756, Sum.inr 1757, Sum.inr 1759, Sum.inr 1760, Sum.inr 1761, Sum.inr 1762, Sum.inr 1763, Sum.inr 1764, Sum.inr 1765, Sum.inr 1766, Sum.inr 1767, Sum.inr 1769, Sum.inr 1771, Sum.inr 1773, Sum.inr 1774, Sum.inr 1776, Sum.inr 1778, Sum.inr 1781, Sum.inr 1782, Sum.inr 1783, Sum.inr 1784, Sum.inr 1786, Sum.inr 1787, Sum.inr 1789, Sum.inr 1790, Sum.inr 1791, Sum.inr 1792, Sum.inr 1793, Sum.inr 1794, Sum.inr 1795, Sum.inr 1796, Sum.inr 1797, Sum.inr 1798, Sum.inr 1799, Sum.inr 1801, Sum.inr 1802, Sum.inr 1803]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk19 : Array Master := #[Sum.inr 1804, Sum.inr 1805, Sum.inr 1806, Sum.inr 1807, Sum.inr 1808, Sum.inr 1809, Sum.inr 1810, Sum.inr 1811, Sum.inr 1812, Sum.inr 1813, Sum.inr 1814, Sum.inr 1815, Sum.inr 1816, Sum.inr 1817, Sum.inr 1818, Sum.inr 1819, Sum.inr 1820, Sum.inr 1821, Sum.inr 1822, Sum.inr 1823, Sum.inr 1824, Sum.inr 1825, Sum.inr 1826, Sum.inr 1827, Sum.inr 1828, Sum.inr 1829, Sum.inr 1830, Sum.inr 1831, Sum.inr 1832, Sum.inr 1833, Sum.inr 1835, Sum.inr 1836, Sum.inr 1837, Sum.inr 1838, Sum.inr 1840, Sum.inr 1841, Sum.inr 1842, Sum.inr 1843, Sum.inr 1844, Sum.inr 1846, Sum.inr 1847, Sum.inr 1848, Sum.inr 1849, Sum.inr 1850, Sum.inr 1851, Sum.inr 1854, Sum.inr 1855, Sum.inr 1857, Sum.inr 1858, Sum.inr 1860, Sum.inr 1861, Sum.inr 1863, Sum.inr 1864, Sum.inr 1867, Sum.inr 1870, Sum.inr 1871, Sum.inr 1873, Sum.inr 1874, Sum.inr 1875, Sum.inr 1876, Sum.inr 1877, Sum.inr 1878, Sum.inr 1879, Sum.inr 1880]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk2 : Array Master := #[Sum.inl 108, Sum.inl 110, Sum.inl 112, Sum.inl 113, Sum.inl 114, Sum.inl 115, Sum.inl 453, Sum.inl 43, Sum.inl 116, Sum.inl 460, Sum.inl 44, Sum.inl 45, Sum.inl 119, Sum.inl 120, Sum.inl 46, Sum.inl 122, Sum.inl 472, Sum.inl 47, Sum.inl 48, Sum.inl 49, Sum.inl 50, Sum.inl 487, Sum.inl 123, Sum.inl 489, Sum.inl 490, Sum.inl 124, Sum.inl 125, Sum.inl 492, Sum.inl 126, Sum.inl 127, Sum.inl 493, Sum.inl 51, Sum.inl 3, Sum.inl 494, Sum.inl 13, Sum.inl 128, Sum.inl 495, Sum.inl 52, Sum.inl 498, Sum.inl 499, Sum.inl 500, Sum.inl 501, Sum.inl 502, Sum.inl 503, Sum.inl 505, Sum.inl 506, Sum.inl 507, Sum.inl 508, Sum.inl 517, Sum.inl 129, Sum.inl 137, Sum.inl 138, Sum.inl 139, Sum.inl 140, Sum.inl 141, Sum.inl 538, Sum.inl 539, Sum.inl 540, Sum.inl 541, Sum.inl 543, Sum.inl 142, Sum.inl 143, Sum.inl 545, Sum.inl 144]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk20 : Array Master := #[Sum.inr 1881, Sum.inr 1882, Sum.inr 1883, Sum.inr 1884, Sum.inr 1886, Sum.inr 1887, Sum.inr 1888, Sum.inr 1889, Sum.inr 1891, Sum.inr 1892, Sum.inr 1893, Sum.inr 1894, Sum.inr 1896, Sum.inr 1897, Sum.inr 1898, Sum.inr 1900, Sum.inr 1901, Sum.inr 1902, Sum.inr 1903, Sum.inr 1904, Sum.inr 1905, Sum.inr 1906, Sum.inr 1907, Sum.inr 1909, Sum.inr 1910, Sum.inr 1913, Sum.inr 1915, Sum.inr 1916, Sum.inr 1917, Sum.inr 1919, Sum.inr 1920, Sum.inr 1921, Sum.inr 1922, Sum.inr 1923, Sum.inr 1924, Sum.inr 1925, Sum.inr 1926, Sum.inr 1927, Sum.inr 1928, Sum.inr 1929, Sum.inr 1935, Sum.inr 1936, Sum.inr 1937, Sum.inr 1938, Sum.inr 1939, Sum.inr 1940, Sum.inr 1941, Sum.inr 1942, Sum.inr 1946, Sum.inr 1948, Sum.inr 1949, Sum.inr 1951, Sum.inr 1952, Sum.inr 1955, Sum.inr 1956, Sum.inr 1957, Sum.inr 1959, Sum.inr 1960, Sum.inr 1961, Sum.inr 1963, Sum.inr 1964, Sum.inr 1965, Sum.inr 1966, Sum.inr 1967]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk21 : Array Master := #[Sum.inr 1969, Sum.inr 1970, Sum.inr 1971, Sum.inr 1972, Sum.inr 1973, Sum.inr 1974, Sum.inr 1975, Sum.inr 1976, Sum.inr 1977, Sum.inr 1978, Sum.inr 1979, Sum.inr 1980, Sum.inr 1982, Sum.inr 1983, Sum.inr 1986, Sum.inr 1987, Sum.inr 1989, Sum.inr 1990, Sum.inr 1991, Sum.inr 1992, Sum.inr 1993, Sum.inr 1994, Sum.inr 1995, Sum.inr 1996, Sum.inr 1997, Sum.inr 1998, Sum.inr 2000, Sum.inr 2001, Sum.inr 2002, Sum.inr 2003, Sum.inr 2004, Sum.inr 2005, Sum.inr 2006, Sum.inr 2008, Sum.inr 2009, Sum.inr 2010, Sum.inr 2011, Sum.inr 2012, Sum.inr 2013, Sum.inr 2014, Sum.inr 2015, Sum.inr 2016, Sum.inr 2017, Sum.inr 2018, Sum.inr 2019, Sum.inr 2020, Sum.inr 2021, Sum.inr 2022, Sum.inr 2023, Sum.inr 2024, Sum.inr 2025, Sum.inr 2026, Sum.inr 2027, Sum.inr 2028, Sum.inr 2029, Sum.inr 2030, Sum.inr 2031, Sum.inr 2032, Sum.inr 2033, Sum.inr 2034, Sum.inr 2035, Sum.inr 2036, Sum.inr 2037, Sum.inr 2038]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk22 : Array Master := #[Sum.inr 2039, Sum.inr 2040, Sum.inr 2041, Sum.inr 2042, Sum.inr 2043, Sum.inr 2044, Sum.inr 2045, Sum.inr 2046, Sum.inr 2047, Sum.inr 2048, Sum.inr 2049, Sum.inr 2050, Sum.inr 2051, Sum.inr 2052, Sum.inr 2054, Sum.inr 2055, Sum.inr 2058, Sum.inr 2059, Sum.inr 2062, Sum.inr 2063, Sum.inr 2064, Sum.inr 2065, Sum.inr 2067, Sum.inr 2070, Sum.inr 2071, Sum.inr 2072, Sum.inr 2073, Sum.inr 2074, Sum.inr 2075, Sum.inr 2076, Sum.inr 2077, Sum.inr 2078, Sum.inr 2079, Sum.inr 2080, Sum.inr 2081, Sum.inr 2082, Sum.inr 2083, Sum.inr 2084, Sum.inr 2085, Sum.inr 2086, Sum.inr 2087, Sum.inr 2088, Sum.inr 2089, Sum.inr 2090, Sum.inr 2091, Sum.inr 2092, Sum.inr 2093, Sum.inr 2094, Sum.inr 2095, Sum.inr 2096, Sum.inr 2097, Sum.inr 2098, Sum.inr 2099, Sum.inr 2100, Sum.inr 2101, Sum.inr 2102, Sum.inr 2103, Sum.inr 2104, Sum.inr 2105, Sum.inr 2106, Sum.inr 2107, Sum.inr 2108, Sum.inr 2109, Sum.inr 2110]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk23 : Array Master := #[Sum.inr 2111, Sum.inr 2112, Sum.inr 2113, Sum.inr 2114, Sum.inr 2115, Sum.inr 2116, Sum.inr 2117, Sum.inr 2118, Sum.inr 2119, Sum.inr 2121, Sum.inr 2122, Sum.inr 2123, Sum.inr 2124, Sum.inr 2125, Sum.inr 2126, Sum.inr 2127, Sum.inr 2128, Sum.inr 2129, Sum.inr 2130, Sum.inr 2131, Sum.inr 2132, Sum.inr 2133, Sum.inr 2134, Sum.inr 2136, Sum.inr 2137, Sum.inr 2138, Sum.inr 2139, Sum.inr 2140, Sum.inr 2141, Sum.inr 2142, Sum.inr 2143, Sum.inr 2144, Sum.inr 2145, Sum.inr 2146, Sum.inr 2147, Sum.inr 2148, Sum.inr 2149, Sum.inr 2150, Sum.inr 2151, Sum.inr 2152, Sum.inr 2153, Sum.inr 2154, Sum.inr 2155, Sum.inr 2156, Sum.inr 2157, Sum.inr 2158, Sum.inr 2159, Sum.inr 2160, Sum.inr 2161, Sum.inr 2162, Sum.inr 2163, Sum.inr 2164, Sum.inr 2165, Sum.inr 2166, Sum.inr 2167, Sum.inr 2168, Sum.inr 2169, Sum.inr 2170, Sum.inr 2171, Sum.inr 2172, Sum.inr 2173, Sum.inr 2174, Sum.inr 2175, Sum.inr 2176]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk24 : Array Master := #[Sum.inr 2177, Sum.inr 2178, Sum.inr 2179, Sum.inr 2180, Sum.inr 2181, Sum.inr 2182, Sum.inr 2183, Sum.inr 2184, Sum.inr 2185, Sum.inr 2186, Sum.inr 2187, Sum.inr 2189, Sum.inr 2190, Sum.inr 2191, Sum.inr 2192, Sum.inr 2193, Sum.inr 2194, Sum.inr 2195, Sum.inr 2196, Sum.inr 2197, Sum.inr 2198, Sum.inr 2199, Sum.inr 2200, Sum.inr 2201, Sum.inr 2202, Sum.inr 2203, Sum.inr 2206, Sum.inr 2207, Sum.inr 2211, Sum.inr 2212, Sum.inr 2213, Sum.inr 2214, Sum.inr 2215, Sum.inr 2216, Sum.inr 2217, Sum.inr 2218, Sum.inr 2219, Sum.inr 2220, Sum.inr 2221, Sum.inr 2222, Sum.inr 2223, Sum.inr 2224, Sum.inr 2225, Sum.inr 2226, Sum.inr 2230, Sum.inr 2231, Sum.inr 2232, Sum.inr 2233, Sum.inr 2234, Sum.inr 2235, Sum.inr 2238, Sum.inr 2239, Sum.inr 2240, Sum.inr 2241, Sum.inr 2242, Sum.inr 2243, Sum.inr 2244, Sum.inr 2245, Sum.inr 2246, Sum.inr 2247, Sum.inr 2248, Sum.inr 2249, Sum.inr 2250, Sum.inr 2251]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk25 : Array Master := #[Sum.inr 2252, Sum.inr 2253, Sum.inr 2254, Sum.inr 2255, Sum.inr 2256, Sum.inr 2257, Sum.inr 2258, Sum.inr 2259, Sum.inr 2260, Sum.inr 2261, Sum.inr 2262, Sum.inr 2266, Sum.inr 2267, Sum.inr 2272, Sum.inr 2273, Sum.inr 2274, Sum.inr 2275, Sum.inr 2276, Sum.inr 2277, Sum.inr 2278, Sum.inr 2279, Sum.inr 2280, Sum.inr 2281, Sum.inr 2282, Sum.inr 2283, Sum.inr 2284, Sum.inr 2285, Sum.inr 2286, Sum.inr 2287, Sum.inr 2288, Sum.inr 2289, Sum.inr 2290, Sum.inr 2294, Sum.inr 2295, Sum.inr 2300, Sum.inr 2306, Sum.inr 2316, Sum.inr 2317, Sum.inr 2318, Sum.inr 2320, Sum.inr 2321, Sum.inr 2323, Sum.inr 2324, Sum.inr 2325, Sum.inr 2326, Sum.inr 2327, Sum.inr 2328, Sum.inr 2329, Sum.inr 2330, Sum.inr 2332, Sum.inr 2333, Sum.inr 2334, Sum.inr 2335, Sum.inr 2337, Sum.inr 2338, Sum.inr 2339, Sum.inr 2340, Sum.inr 2341, Sum.inr 2342, Sum.inr 2343, Sum.inr 2344, Sum.inr 2345, Sum.inr 2346, Sum.inr 2347]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk26 : Array Master := #[Sum.inr 2348, Sum.inr 2349, Sum.inr 2350, Sum.inr 2351, Sum.inr 2352, Sum.inr 2353, Sum.inr 2354, Sum.inr 2355, Sum.inr 2356, Sum.inr 2361, Sum.inr 2362, Sum.inr 2370, Sum.inr 2371, Sum.inr 2372, Sum.inr 2378, Sum.inr 2379, Sum.inr 2382, Sum.inr 2383, Sum.inr 2384, Sum.inr 2385, Sum.inr 2388, Sum.inr 2389, Sum.inr 2390, Sum.inr 2391, Sum.inr 2392, Sum.inr 2393, Sum.inr 2394, Sum.inr 2395, Sum.inr 2396, Sum.inr 2397, Sum.inr 2398, Sum.inr 2399, Sum.inr 2400, Sum.inr 2401, Sum.inr 2404, Sum.inr 2405, Sum.inr 2407, Sum.inr 2408, Sum.inr 2409, Sum.inr 2410, Sum.inr 2412, Sum.inr 2419, Sum.inr 2422, Sum.inr 2423, Sum.inr 2424, Sum.inr 2425, Sum.inr 2426, Sum.inr 2427, Sum.inr 2428, Sum.inr 2429, Sum.inr 2430, Sum.inr 2431, Sum.inr 2432, Sum.inr 2433, Sum.inr 2434, Sum.inr 2435, Sum.inr 2436, Sum.inr 2437, Sum.inr 2438, Sum.inr 2440, Sum.inr 2441, Sum.inr 2442, Sum.inr 2443, Sum.inr 2449]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk27 : Array Master := #[Sum.inr 2452, Sum.inr 2453, Sum.inr 2454, Sum.inr 2455, Sum.inr 2456, Sum.inr 2457, Sum.inr 2458, Sum.inr 2459, Sum.inr 2460, Sum.inr 2462, Sum.inr 2463, Sum.inr 2465, Sum.inr 2466, Sum.inr 2467, Sum.inr 2469, Sum.inr 2470, Sum.inr 2471, Sum.inr 2472, Sum.inr 2473, Sum.inr 2474, Sum.inr 2475, Sum.inr 2476, Sum.inr 2477, Sum.inr 2478, Sum.inr 2479, Sum.inr 2480, Sum.inr 2481, Sum.inr 2482, Sum.inr 2483, Sum.inr 2484, Sum.inr 2485, Sum.inr 2486, Sum.inr 2488, Sum.inr 2489, Sum.inr 2490, Sum.inr 2491, Sum.inr 2492, Sum.inr 2493, Sum.inr 2494, Sum.inr 2495, Sum.inr 2496, Sum.inr 2497, Sum.inr 2498, Sum.inr 2499, Sum.inr 2500, Sum.inr 2501, Sum.inr 2502, Sum.inr 2503, Sum.inr 2504, Sum.inr 2505, Sum.inr 2506, Sum.inr 2507, Sum.inr 2508, Sum.inr 2509, Sum.inr 2512, Sum.inr 2513, Sum.inr 2515, Sum.inr 2516, Sum.inr 2519, Sum.inr 2520, Sum.inr 2521, Sum.inr 2522, Sum.inr 2524, Sum.inr 2525]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk28 : Array Master := #[Sum.inr 2529, Sum.inr 2533, Sum.inr 2534, Sum.inr 2535, Sum.inr 2536, Sum.inr 2537, Sum.inr 2538, Sum.inr 2539, Sum.inr 2541, Sum.inr 2543, Sum.inr 2544, Sum.inr 2545, Sum.inr 2547, Sum.inr 2549, Sum.inr 2550, Sum.inr 2551, Sum.inr 2553, Sum.inr 2555, Sum.inr 2556, Sum.inr 2557, Sum.inr 2558, Sum.inr 2559, Sum.inr 2560, Sum.inr 2561, Sum.inr 2562, Sum.inr 2564, Sum.inr 2565, Sum.inr 2566, Sum.inr 2567, Sum.inr 2568, Sum.inr 2569, Sum.inr 2571, Sum.inr 2573, Sum.inr 2575, Sum.inr 2577, Sum.inr 2578, Sum.inr 2579, Sum.inr 2580, Sum.inr 2582, Sum.inr 2583, Sum.inr 2584, Sum.inr 2585, Sum.inr 2587, Sum.inr 2588, Sum.inr 2589, Sum.inr 2590, Sum.inr 2591, Sum.inr 2592, Sum.inr 2597, Sum.inr 2600, Sum.inr 2603, Sum.inr 2606, Sum.inr 2607, Sum.inr 2608, Sum.inr 2609, Sum.inr 2610, Sum.inr 2611, Sum.inr 2612, Sum.inr 2613, Sum.inr 2614, Sum.inr 2615, Sum.inr 2616, Sum.inr 2617, Sum.inr 2618]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk29 : Array Master := #[Sum.inr 2619, Sum.inr 2620, Sum.inr 2621, Sum.inr 2622, Sum.inr 2623, Sum.inr 2624, Sum.inr 2625, Sum.inr 2627, Sum.inr 2628, Sum.inr 2629, Sum.inr 2630, Sum.inr 2631, Sum.inr 2632, Sum.inr 2633, Sum.inr 2634, Sum.inr 2635, Sum.inr 2639, Sum.inr 2641, Sum.inr 2643, Sum.inr 2645, Sum.inr 2647, Sum.inr 2649, Sum.inr 2650, Sum.inr 2651, Sum.inr 2652, Sum.inr 2653, Sum.inr 2654, Sum.inr 2655, Sum.inr 2656, Sum.inr 2657, Sum.inr 2658, Sum.inr 2659, Sum.inr 2661, Sum.inr 2662, Sum.inr 2664, Sum.inr 2665, Sum.inr 2668, Sum.inr 2669, Sum.inr 2670, Sum.inr 2671, Sum.inr 2672, Sum.inr 2673, Sum.inr 2674, Sum.inr 2675, Sum.inr 2676, Sum.inr 2677, Sum.inr 2678, Sum.inr 2680, Sum.inr 2681, Sum.inr 2682, Sum.inr 2683, Sum.inr 2684, Sum.inr 2685, Sum.inr 2686, Sum.inr 2687, Sum.inr 2688, Sum.inr 2690, Sum.inr 2694, Sum.inr 2697, Sum.inr 2698, Sum.inr 2700, Sum.inr 2702, Sum.inr 2703, Sum.inr 2704]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk3 : Array Master := #[Sum.inl 145, Sum.inl 146, Sum.inl 546, Sum.inl 14, Sum.inl 15, Sum.inl 16, Sum.inl 17, Sum.inl 18, Sum.inl 640, Sum.inl 643, Sum.inl 177, Sum.inl 19, Sum.inl 20, Sum.inl 702, Sum.inl 190, Sum.inl 191, Sum.inl 709, Sum.inl 53, Sum.inl 21, Sum.inl 22, Sum.inl 194, Sum.inl 195, Sum.inl 721, Sum.inl 196, Sum.inl 723, Sum.inl 197, Sum.inl 23, Sum.inl 54, Sum.inl 199, Sum.inl 726, Sum.inl 24, Sum.inl 727, Sum.inl 55, Sum.inl 12, Sum.inl 728, Sum.inl 201, Sum.inl 735, Sum.inl 736, Sum.inl 737, Sum.inl 738, Sum.inl 739, Sum.inl 203, Sum.inl 745, Sum.inl 204, Sum.inl 751, Sum.inl 753, Sum.inl 205, Sum.inl 207, Sum.inl 208, Sum.inl 209, Sum.inl 760, Sum.inl 764, Sum.inl 216, Sum.inl 217, Sum.inl 783, Sum.inl 784, Sum.inl 794, Sum.inl 796, Sum.inl 226, Sum.inl 56, Sum.inl 25, Sum.inl 228, Sum.inl 11, Sum.inl 26]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk30 : Array Master := #[Sum.inr 2705, Sum.inr 2706, Sum.inr 2707, Sum.inr 2708, Sum.inr 2710, Sum.inr 2712, Sum.inr 2713, Sum.inr 2714, Sum.inr 2716, Sum.inr 2717, Sum.inr 2718, Sum.inr 2719, Sum.inr 2721, Sum.inr 2722, Sum.inr 2723, Sum.inr 2724, Sum.inr 2726, Sum.inr 2727, Sum.inr 2728, Sum.inr 2729, Sum.inr 2730, Sum.inr 2731, Sum.inr 2732, Sum.inr 2734, Sum.inr 2735, Sum.inr 2736, Sum.inr 2737, Sum.inr 2738, Sum.inr 2739, Sum.inr 2740, Sum.inr 2743, Sum.inr 2744, Sum.inr 2745, Sum.inr 2746, Sum.inr 2747, Sum.inr 2748, Sum.inr 2749, Sum.inr 2750, Sum.inr 2751, Sum.inr 2754, Sum.inr 2756, Sum.inr 2757, Sum.inr 2758, Sum.inr 2759, Sum.inr 2760, Sum.inr 2761, Sum.inr 2762, Sum.inr 2763, Sum.inr 2764, Sum.inr 2765, Sum.inr 2769, Sum.inr 2771, Sum.inr 2772, Sum.inr 2773, Sum.inr 2774, Sum.inr 2777, Sum.inr 2779, Sum.inr 2780, Sum.inr 2781, Sum.inr 2782, Sum.inr 2783, Sum.inr 2789, Sum.inr 2796, Sum.inr 2797]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk31 : Array Master := #[Sum.inr 2798, Sum.inr 2799, Sum.inr 2800, Sum.inr 2801, Sum.inr 2802, Sum.inr 2803, Sum.inr 2804, Sum.inr 2806, Sum.inr 2807, Sum.inr 2809, Sum.inr 2810, Sum.inr 2811, Sum.inr 2812, Sum.inr 2813, Sum.inr 2814, Sum.inr 2815, Sum.inr 2816, Sum.inr 2817, Sum.inr 2818, Sum.inr 2819, Sum.inr 2820, Sum.inr 2821, Sum.inr 2822, Sum.inr 2824, Sum.inr 2826, Sum.inr 2827, Sum.inr 2831, Sum.inr 2833, Sum.inr 2834, Sum.inr 2835, Sum.inr 2836, Sum.inr 2837, Sum.inr 2838, Sum.inr 2841, Sum.inr 2842, Sum.inr 2846, Sum.inr 2847, Sum.inr 2848, Sum.inr 2849, Sum.inr 2853, Sum.inr 2856, Sum.inr 2857, Sum.inr 2858, Sum.inr 2859, Sum.inr 2860, Sum.inr 2861, Sum.inr 2862, Sum.inr 2864, Sum.inr 2865, Sum.inr 2867, Sum.inr 2868, Sum.inr 2869, Sum.inr 2870, Sum.inr 2871, Sum.inr 2872, Sum.inr 2873, Sum.inr 2874, Sum.inr 2875, Sum.inr 2876, Sum.inr 2877, Sum.inr 2878, Sum.inr 2879, Sum.inr 2880, Sum.inr 2881]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk32 : Array Master := #[Sum.inr 2882, Sum.inr 2883, Sum.inr 2884, Sum.inr 2885, Sum.inr 2886, Sum.inr 2887, Sum.inr 2888, Sum.inr 2889, Sum.inr 2890, Sum.inr 2892, Sum.inr 2893, Sum.inr 2895, Sum.inr 2896, Sum.inr 2898, Sum.inr 2899, Sum.inr 2900, Sum.inr 2902, Sum.inr 2905, Sum.inr 2906, Sum.inr 2907, Sum.inr 2908, Sum.inr 2909, Sum.inr 2910, Sum.inr 2911, Sum.inr 2912, Sum.inr 2913, Sum.inr 2916, Sum.inr 2918, Sum.inr 2919, Sum.inr 2920, Sum.inr 2921, Sum.inr 2922, Sum.inr 2923, Sum.inr 2924, Sum.inr 2925, Sum.inr 2926, Sum.inr 2928, Sum.inr 2929, Sum.inr 2930, Sum.inr 2931, Sum.inr 2933, Sum.inr 2942, Sum.inr 2945, Sum.inr 2946, Sum.inr 2947, Sum.inr 2949, Sum.inr 2950, Sum.inr 2951, Sum.inr 2952, Sum.inr 2954, Sum.inr 2955, Sum.inr 2956, Sum.inr 2962, Sum.inr 2964, Sum.inr 2967, Sum.inr 2970, Sum.inr 2971, Sum.inr 2972, Sum.inr 2973, Sum.inr 2974, Sum.inr 2975, Sum.inr 2976, Sum.inr 2977, Sum.inr 2978]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk33 : Array Master := #[Sum.inr 2979, Sum.inr 2980, Sum.inr 2981, Sum.inr 2983, Sum.inr 2984, Sum.inr 2985, Sum.inr 2992, Sum.inr 2995, Sum.inr 3007, Sum.inr 3008, Sum.inr 3010, Sum.inr 3011, Sum.inr 3012, Sum.inr 3013, Sum.inr 3014, Sum.inr 3015, Sum.inr 3016, Sum.inr 3017, Sum.inr 3018, Sum.inr 3019, Sum.inr 3022, Sum.inr 3023, Sum.inr 3024, Sum.inr 3025, Sum.inr 3028, Sum.inr 3029, Sum.inr 3030, Sum.inr 3031, Sum.inr 3032, Sum.inr 3033, Sum.inr 3034, Sum.inr 3035, Sum.inr 3036, Sum.inr 3037, Sum.inr 3038, Sum.inr 3039, Sum.inr 3040, Sum.inr 3041, Sum.inr 3042, Sum.inr 3043, Sum.inr 3044, Sum.inr 3045, Sum.inr 3046, Sum.inr 3049, Sum.inr 3050, Sum.inr 3051, Sum.inr 3052, Sum.inr 3053, Sum.inr 3054, Sum.inr 3055, Sum.inr 3056, Sum.inr 3057, Sum.inr 3058, Sum.inr 3059, Sum.inr 3062, Sum.inr 3063, Sum.inr 3064, Sum.inr 3066, Sum.inr 3067, Sum.inr 3068, Sum.inr 3069, Sum.inr 3072, Sum.inr 3073, Sum.inr 3074]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk34 : Array Master := #[Sum.inr 3075, Sum.inr 3077, Sum.inr 3078, Sum.inr 3079, Sum.inr 3083, Sum.inr 3084, Sum.inr 3086, Sum.inr 3091, Sum.inr 3092, Sum.inr 3096, Sum.inr 3097, Sum.inr 3098, Sum.inr 3108, Sum.inr 3115, Sum.inr 3118, Sum.inr 3127, Sum.inr 3128, Sum.inr 3129, Sum.inr 3130, Sum.inr 3131, Sum.inr 3132, Sum.inr 3133, Sum.inr 3134, Sum.inr 3135, Sum.inr 3136, Sum.inr 3137, Sum.inr 3138, Sum.inr 3146, Sum.inr 3147, Sum.inr 3149, Sum.inr 3150, Sum.inr 3151, Sum.inr 3152, Sum.inr 3153, Sum.inr 3154, Sum.inr 3155, Sum.inr 3156, Sum.inr 3157, Sum.inr 3158, Sum.inr 3159, Sum.inr 3160, Sum.inr 3161, Sum.inr 3162, Sum.inr 3163, Sum.inr 3164, Sum.inr 3165, Sum.inr 3166, Sum.inr 3168, Sum.inr 3170, Sum.inr 3172, Sum.inr 3174, Sum.inr 3175, Sum.inr 3176, Sum.inr 3179, Sum.inr 3180, Sum.inr 3189, Sum.inr 3193, Sum.inr 3195, Sum.inr 3196, Sum.inr 3197, Sum.inr 3198, Sum.inr 3199, Sum.inr 3202, Sum.inr 3217]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk35 : Array Master := #[Sum.inr 3221, Sum.inr 3222, Sum.inr 3232, Sum.inr 3233, Sum.inr 3234, Sum.inr 3235, Sum.inr 3236, Sum.inr 3237, Sum.inr 3238, Sum.inr 3239, Sum.inr 3240, Sum.inr 3241, Sum.inr 3242, Sum.inr 3243, Sum.inr 3244, Sum.inr 3245, Sum.inr 3246, Sum.inr 3247, Sum.inr 3248, Sum.inr 3249, Sum.inr 3250, Sum.inr 3251, Sum.inr 3252, Sum.inr 3253, Sum.inr 3254, Sum.inr 3255, Sum.inr 3256, Sum.inr 3257, Sum.inr 3258, Sum.inr 3259, Sum.inr 3260, Sum.inr 3261, Sum.inr 3262, Sum.inr 3263, Sum.inr 3264, Sum.inr 3265, Sum.inr 3266, Sum.inr 3267, Sum.inr 3268, Sum.inr 3269, Sum.inr 3270, Sum.inr 3271, Sum.inr 3272, Sum.inr 3273, Sum.inr 3274, Sum.inr 3275, Sum.inr 3276, Sum.inr 3277, Sum.inr 3278, Sum.inr 3279, Sum.inr 3280, Sum.inr 3281, Sum.inr 3282, Sum.inr 3283, Sum.inr 3284, Sum.inr 3285, Sum.inr 3286, Sum.inr 3287, Sum.inr 3288, Sum.inr 3289, Sum.inr 3290, Sum.inr 3291, Sum.inr 3292, Sum.inr 3293]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk36 : Array Master := #[Sum.inr 3294, Sum.inr 3295, Sum.inr 3296, Sum.inr 3297, Sum.inr 3298, Sum.inr 3299, Sum.inr 3300, Sum.inr 3301, Sum.inr 3302, Sum.inr 3303, Sum.inr 3304, Sum.inr 3305, Sum.inr 3306, Sum.inr 3307, Sum.inr 3308, Sum.inr 3309, Sum.inr 3310, Sum.inr 3311, Sum.inr 3312, Sum.inr 3313, Sum.inr 3315, Sum.inr 3318, Sum.inr 3325, Sum.inr 3334, Sum.inr 3335, Sum.inr 3336, Sum.inr 3337, Sum.inr 3340, Sum.inr 3341, Sum.inr 3342, Sum.inr 3343, Sum.inr 3344, Sum.inr 3345, Sum.inr 3346, Sum.inr 3347, Sum.inr 3348, Sum.inr 3349, Sum.inr 3350, Sum.inr 3352, Sum.inr 3353, Sum.inr 3354, Sum.inr 3355, Sum.inr 3357, Sum.inr 3358, Sum.inr 3360, Sum.inr 3365, Sum.inr 3368, Sum.inr 3370, Sum.inr 3372, Sum.inr 3373, Sum.inr 3374, Sum.inr 3375, Sum.inr 3376, Sum.inr 3377, Sum.inr 3378, Sum.inr 3379, Sum.inr 3380, Sum.inr 3382, Sum.inr 3383, Sum.inr 3384, Sum.inr 3385, Sum.inr 3386, Sum.inr 3387, Sum.inr 3388]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk37 : Array Master := #[Sum.inr 3389, Sum.inr 3390, Sum.inr 3391, Sum.inr 3392, Sum.inr 3393, Sum.inr 3394, Sum.inr 3395, Sum.inr 3396, Sum.inr 3397, Sum.inr 3398, Sum.inr 3399, Sum.inr 3400, Sum.inr 3401, Sum.inr 3402, Sum.inr 3404, Sum.inr 3406, Sum.inr 3407, Sum.inr 3408, Sum.inr 3410, Sum.inr 3411, Sum.inr 3412, Sum.inr 3413, Sum.inr 3414, Sum.inr 3415, Sum.inr 3416, Sum.inr 3417, Sum.inr 3418, Sum.inr 3419, Sum.inr 3420, Sum.inr 3421, Sum.inr 3422, Sum.inr 3423, Sum.inr 3425, Sum.inr 3426, Sum.inr 3429, Sum.inr 3430, Sum.inr 3431, Sum.inr 3432, Sum.inr 3433, Sum.inr 3434, Sum.inr 3436, Sum.inr 3437, Sum.inr 3440, Sum.inr 3441, Sum.inr 3442, Sum.inr 3443, Sum.inr 3444, Sum.inr 3445, Sum.inr 3446, Sum.inr 3447, Sum.inr 3448, Sum.inr 3449, Sum.inr 3450, Sum.inr 3451, Sum.inr 3452, Sum.inr 3453, Sum.inr 3454, Sum.inr 3455, Sum.inr 3456, Sum.inr 3457, Sum.inr 3458, Sum.inr 3459, Sum.inr 3460, Sum.inr 3461]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk38 : Array Master := #[Sum.inr 3462, Sum.inr 3463, Sum.inr 3464, Sum.inr 3465, Sum.inr 3466, Sum.inr 3467, Sum.inr 3468, Sum.inr 3471, Sum.inr 3472, Sum.inr 3473, Sum.inr 3474, Sum.inr 3475, Sum.inr 3476, Sum.inr 3477, Sum.inr 3478, Sum.inr 3479, Sum.inr 3480, Sum.inr 3481, Sum.inr 3482, Sum.inr 3486, Sum.inr 3487, Sum.inr 3488, Sum.inr 3490, Sum.inr 3491, Sum.inr 3493, Sum.inr 3495, Sum.inr 3496, Sum.inr 3497, Sum.inr 3498, Sum.inr 3499, Sum.inr 3500, Sum.inr 3501, Sum.inr 3502, Sum.inr 3503, Sum.inr 3504, Sum.inr 3505, Sum.inr 3506, Sum.inr 3507, Sum.inr 3508, Sum.inr 3509, Sum.inr 3510, Sum.inr 3511, Sum.inr 3512, Sum.inr 3514, Sum.inr 3516, Sum.inr 3517, Sum.inr 3518, Sum.inr 3519, Sum.inr 3521, Sum.inr 3522, Sum.inr 3523, Sum.inr 3524, Sum.inr 3526, Sum.inr 3527, Sum.inr 3528, Sum.inr 3529, Sum.inr 3530, Sum.inr 3532, Sum.inr 3533, Sum.inr 3534, Sum.inr 3535, Sum.inr 3536, Sum.inr 3537, Sum.inr 3538]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk39 : Array Master := #[Sum.inr 3539, Sum.inr 3540, Sum.inr 3541, Sum.inr 3542, Sum.inr 3543, Sum.inr 3544, Sum.inr 3545, Sum.inr 3548, Sum.inr 3549, Sum.inr 3550, Sum.inr 3551, Sum.inr 3552, Sum.inr 3553, Sum.inr 3554, Sum.inr 3555, Sum.inr 3556, Sum.inr 3557, Sum.inr 3558, Sum.inr 3559, Sum.inr 3560, Sum.inr 3561, Sum.inr 3562, Sum.inr 3563, Sum.inr 3564, Sum.inr 3565, Sum.inr 3566, Sum.inr 3567, Sum.inr 3568, Sum.inr 3569, Sum.inr 3570, Sum.inr 3571, Sum.inr 3572, Sum.inr 3573, Sum.inr 3574, Sum.inr 3575, Sum.inr 3576, Sum.inr 3577, Sum.inr 3578, Sum.inr 3579, Sum.inr 3580, Sum.inr 3581, Sum.inr 3582, Sum.inr 3583, Sum.inr 3584, Sum.inr 3585, Sum.inr 3586, Sum.inr 3587, Sum.inr 3588, Sum.inr 3589, Sum.inr 3590, Sum.inr 3591, Sum.inr 3592, Sum.inr 3595, Sum.inr 3596, Sum.inr 3597, Sum.inr 3599, Sum.inr 3600, Sum.inr 3602, Sum.inr 3603, Sum.inr 3605, Sum.inr 3606, Sum.inr 3607, Sum.inr 3608, Sum.inr 3610]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk4 : Array Master := #[Sum.inl 4, Sum.inl 798, Sum.inl 810, Sum.inl 811, Sum.inl 27, Sum.inl 1, Sum.inl 812, Sum.inl 230, Sum.inl 231, Sum.inl 818, Sum.inl 236, Sum.inl 237, Sum.inl 238, Sum.inl 855, Sum.inl 239, Sum.inl 870, Sum.inl 57, Sum.inl 30, Sum.inl 31, Sum.inr 535, Sum.inr 536, Sum.inr 537, Sum.inr 538, Sum.inr 539, Sum.inr 540, Sum.inr 541, Sum.inr 542, Sum.inr 543, Sum.inr 544, Sum.inr 545, Sum.inr 546, Sum.inr 547, Sum.inr 548, Sum.inr 549, Sum.inr 550, Sum.inr 552, Sum.inr 554, Sum.inr 555, Sum.inr 556, Sum.inr 557, Sum.inr 559, Sum.inr 562, Sum.inr 563, Sum.inr 564, Sum.inr 566, Sum.inr 567, Sum.inr 568, Sum.inr 569, Sum.inr 570, Sum.inr 571, Sum.inr 572, Sum.inr 573, Sum.inr 574, Sum.inr 575, Sum.inr 576, Sum.inr 577, Sum.inr 578, Sum.inr 579, Sum.inr 580, Sum.inr 581, Sum.inr 582, Sum.inr 583, Sum.inr 584, Sum.inr 585]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk40 : Array Master := #[Sum.inr 3611, Sum.inr 3612, Sum.inr 3613, Sum.inr 3614, Sum.inr 3615, Sum.inr 3616, Sum.inr 3617, Sum.inr 3619, Sum.inr 3620, Sum.inr 3621, Sum.inr 3622, Sum.inr 3623, Sum.inr 3624, Sum.inr 3625, Sum.inr 3626, Sum.inr 3627, Sum.inr 3630, Sum.inr 3631, Sum.inr 3632, Sum.inr 3633, Sum.inr 3634, Sum.inr 3646, Sum.inr 3648, Sum.inr 3653, Sum.inr 3658, Sum.inr 3659, Sum.inr 3660, Sum.inr 3666, Sum.inr 3668, Sum.inr 3670, Sum.inr 3671, Sum.inr 3672, Sum.inr 3673, Sum.inr 3674, Sum.inr 3675, Sum.inr 3676, Sum.inr 3677, Sum.inr 3678, Sum.inr 3679, Sum.inr 3680, Sum.inr 3681, Sum.inr 3683, Sum.inr 3685, Sum.inr 3686, Sum.inr 3687, Sum.inr 3688, Sum.inr 3689, Sum.inr 3690, Sum.inr 3691, Sum.inr 3692, Sum.inr 3693, Sum.inr 3694, Sum.inr 3695, Sum.inr 3696, Sum.inr 3697, Sum.inr 3698, Sum.inr 3699, Sum.inr 3700, Sum.inr 3701, Sum.inr 3702, Sum.inr 3703, Sum.inr 3705, Sum.inr 3706, Sum.inr 3708]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk41 : Array Master := #[Sum.inr 3709, Sum.inr 3710, Sum.inr 3712, Sum.inr 3713, Sum.inr 3714, Sum.inr 3715, Sum.inr 3716, Sum.inr 3717, Sum.inr 3718, Sum.inr 3719, Sum.inr 3720, Sum.inr 3721, Sum.inr 3722, Sum.inr 3723, Sum.inr 3724, Sum.inr 3725, Sum.inr 3729, Sum.inr 3730, Sum.inr 3731, Sum.inr 3732, Sum.inr 3733, Sum.inr 3743, Sum.inr 3744, Sum.inr 3746, Sum.inr 3748, Sum.inr 3749, Sum.inr 3750, Sum.inr 3751, Sum.inr 3752, Sum.inr 3753, Sum.inr 3754, Sum.inr 3755, Sum.inr 3756, Sum.inr 3757, Sum.inr 3758, Sum.inr 3759, Sum.inr 3760, Sum.inr 3761, Sum.inr 3762, Sum.inr 3763, Sum.inr 3764, Sum.inr 3767, Sum.inr 3768, Sum.inr 3769, Sum.inr 3770, Sum.inr 3771, Sum.inr 3772, Sum.inr 3773, Sum.inr 3776, Sum.inr 3778, Sum.inr 3779, Sum.inr 3780, Sum.inr 3781, Sum.inr 3782, Sum.inr 3783, Sum.inr 3784, Sum.inr 3785, Sum.inr 3786, Sum.inr 3787, Sum.inr 3788, Sum.inr 3789, Sum.inr 3790, Sum.inr 3791, Sum.inr 3792]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk42 : Array Master := #[Sum.inr 3794, Sum.inr 3795, Sum.inr 3796, Sum.inr 3797, Sum.inr 3799, Sum.inr 3800, Sum.inr 3801, Sum.inr 3802, Sum.inr 3803, Sum.inr 3804, Sum.inr 3805, Sum.inr 3809, Sum.inr 3810, Sum.inr 3811, Sum.inr 3812, Sum.inr 3813, Sum.inr 3814, Sum.inr 3815, Sum.inr 3819, Sum.inr 3825, Sum.inr 3826, Sum.inr 3827, Sum.inr 3828, Sum.inr 3832, Sum.inr 3833, Sum.inr 3834, Sum.inr 3835, Sum.inr 3836, Sum.inr 3837, Sum.inr 3838, Sum.inr 3839, Sum.inr 3840, Sum.inr 3841, Sum.inr 3842, Sum.inr 3843, Sum.inr 3845, Sum.inr 3846, Sum.inr 3848, Sum.inr 3849, Sum.inr 3850, Sum.inr 3854, Sum.inr 3857, Sum.inr 3863, Sum.inr 3865, Sum.inr 3866, Sum.inr 3867, Sum.inr 3868, Sum.inr 3869, Sum.inr 3870, Sum.inr 3871, Sum.inr 3872, Sum.inr 3873, Sum.inr 3874, Sum.inr 3875, Sum.inr 3876, Sum.inr 3877, Sum.inr 3878, Sum.inr 3879, Sum.inr 3880, Sum.inr 3881, Sum.inr 3884, Sum.inr 3885, Sum.inr 3886, Sum.inr 3890]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk43 : Array Master := #[Sum.inr 3891, Sum.inr 3892, Sum.inr 3893, Sum.inr 3894, Sum.inr 3895, Sum.inr 3896, Sum.inr 3897, Sum.inr 3898, Sum.inr 3899, Sum.inr 3900, Sum.inr 3901, Sum.inr 3902, Sum.inr 3903, Sum.inr 3906, Sum.inr 3907, Sum.inr 3909, Sum.inr 3910, Sum.inr 3913, Sum.inr 3922, Sum.inr 3927, Sum.inr 3929, Sum.inr 3935, Sum.inr 3942, Sum.inr 3945, Sum.inr 3946, Sum.inr 3947, Sum.inr 3949, Sum.inr 3952, Sum.inr 3954, Sum.inr 3955, Sum.inr 3957, Sum.inr 3958, Sum.inr 3959, Sum.inr 3960, Sum.inr 3961, Sum.inr 3963, Sum.inr 3964, Sum.inr 3972, Sum.inr 3973, Sum.inr 3974, Sum.inr 3978, Sum.inr 3983, Sum.inr 4010, Sum.inr 4022, Sum.inr 4024, Sum.inr 4025, Sum.inr 4041, Sum.inr 4042, Sum.inr 4043, Sum.inr 4045, Sum.inr 4046, Sum.inr 4047, Sum.inr 4056, Sum.inr 4057, Sum.inr 4058, Sum.inr 4059, Sum.inr 4060, Sum.inr 4061, Sum.inr 4062, Sum.inr 4063, Sum.inr 4064, Sum.inr 4065, Sum.inr 4066, Sum.inr 4067]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk44 : Array Master := #[Sum.inr 4068, Sum.inr 4069, Sum.inr 4070, Sum.inr 4071, Sum.inr 4072, Sum.inr 4073, Sum.inr 4074, Sum.inr 4075, Sum.inr 4076, Sum.inr 4077, Sum.inr 4078, Sum.inr 4079, Sum.inr 4080, Sum.inr 4081, Sum.inr 4082, Sum.inr 4083, Sum.inr 4084, Sum.inr 4085, Sum.inr 4086, Sum.inr 4087, Sum.inr 4088, Sum.inr 4089, Sum.inr 4090, Sum.inr 4091, Sum.inr 4092, Sum.inr 4149, Sum.inr 4150, Sum.inr 4151, Sum.inr 4152, Sum.inr 4153, Sum.inr 4154, Sum.inr 4155, Sum.inr 4156, Sum.inr 4157, Sum.inr 4158, Sum.inr 4159, Sum.inr 4160, Sum.inr 4161, Sum.inr 4162, Sum.inr 4163, Sum.inr 4169, Sum.inr 4170, Sum.inr 4173, Sum.inr 4176, Sum.inr 4178, Sum.inr 4179, Sum.inr 4184, Sum.inr 4188, Sum.inr 4189, Sum.inr 4193, Sum.inr 4327, Sum.inr 4328, Sum.inr 4330, Sum.inr 4331, Sum.inr 4332, Sum.inr 4333, Sum.inr 4334, Sum.inr 4335, Sum.inr 4336, Sum.inr 4345, Sum.inr 4347, Sum.inr 4348, Sum.inr 4353, Sum.inr 4357]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk45 : Array Master := #[Sum.inr 4358, Sum.inr 4362, Sum.inr 4363, Sum.inr 4364, Sum.inr 4365, Sum.inr 4366, Sum.inr 4367, Sum.inr 4368, Sum.inr 4369, Sum.inr 4370, Sum.inr 4371, Sum.inr 4372, Sum.inr 4373, Sum.inr 4374, Sum.inr 4375, Sum.inr 4391, Sum.inr 4392, Sum.inr 4400, Sum.inr 4402, Sum.inr 4406, Sum.inr 4407, Sum.inr 4410, Sum.inr 4412, Sum.inr 4414, Sum.inr 4420, Sum.inr 4425, Sum.inr 4427, Sum.inr 4435, Sum.inr 4436, Sum.inr 4437, Sum.inr 4439, Sum.inr 4440, Sum.inr 4441, Sum.inr 4442, Sum.inr 4443, Sum.inr 4444, Sum.inr 4445, Sum.inr 4449, Sum.inr 4450, Sum.inr 4453, Sum.inr 4459, Sum.inr 4462, Sum.inr 4464, Sum.inr 4469, Sum.inr 4470, Sum.inr 4471, Sum.inr 4473, Sum.inr 4474, Sum.inr 4475, Sum.inr 4476, Sum.inr 4478, Sum.inr 4480, Sum.inr 4481, Sum.inr 4486, Sum.inr 4487, Sum.inr 4492, Sum.inr 4494, Sum.inr 4500, Sum.inr 4504, Sum.inr 4506, Sum.inr 4508, Sum.inr 4527, Sum.inr 4528, Sum.inr 4529]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk46 : Array Master := #[Sum.inr 4530, Sum.inr 4531, Sum.inr 4532, Sum.inr 4533, Sum.inr 4534, Sum.inr 4535, Sum.inr 4536, Sum.inr 4540, Sum.inr 4542, Sum.inr 4545, Sum.inr 4547, Sum.inr 4548, Sum.inr 4552, Sum.inr 4556, Sum.inr 4560, Sum.inr 4589, Sum.inr 4590, Sum.inr 4591, Sum.inr 4592, Sum.inr 4593, Sum.inr 4594, Sum.inr 4599, Sum.inr 4600, Sum.inr 4603, Sum.inr 4607, Sum.inr 4609, Sum.inr 4611, Sum.inr 4616, Sum.inr 4617, Sum.inr 4620, Sum.inr 4626, Sum.inr 4663, Sum.inr 4664, Sum.inr 4665, Sum.inr 4666, Sum.inr 4667, Sum.inr 4668, Sum.inr 4669, Sum.inr 4670, Sum.inr 4671, Sum.inr 4675, Sum.inr 4677, Sum.inr 4680, Sum.inr 4682, Sum.inr 4683, Sum.inr 4687, Sum.inr 4690, Sum.inr 4694, Sum.inr 4695, Sum.inr 4696, Sum.inr 4697, Sum.inr 4698, Sum.inr 4699, Sum.inr 4700, Sum.inr 4701, Sum.inr 4702, Sum.inr 4703, Sum.inr 4704, Sum.inr 4705, Sum.inr 4756, Sum.inr 4757, Sum.inr 4761, Sum.inr 4762, Sum.inr 4765]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk47 : Array Master := #[Sum.inr 4768, Sum.inr 4771, Sum.inr 4772, Sum.inr 4773, Sum.inr 4774, Sum.inr 4775, Sum.inr 4776, Sum.inr 4777, Sum.inr 4780, Sum.inr 4783, Sum.inr 4785, Sum.inr 4791, Sum.inr 4792, Sum.inr 4793, Sum.inr 4794, Sum.inr 4795, Sum.inr 4797, Sum.inr 4799, Sum.inr 4803, Sum.inr 4806, Sum.inr 4808, Sum.inr 4812, Sum.inr 4813, Sum.inr 4815, Sum.inr 4816, Sum.inr 4817, Sum.inr 4819, Sum.inr 4821, Sum.inr 4824, Sum.inr 4825, Sum.inr 4829, Sum.inr 4830, Sum.inr 4836, Sum.inr 4840, Sum.inr 4842, Sum.inr 4844, Sum.inr 4848, Sum.inr 4849, Sum.inr 4850, Sum.inr 4851, Sum.inr 4852, Sum.inr 4853, Sum.inr 4854, Sum.inr 4855, Sum.inr 4856, Sum.inr 4861, Sum.inr 4863, Sum.inr 4867, Sum.inr 4870, Sum.inr 4872, Sum.inr 4878, Sum.inr 4879, Sum.inr 4880, Sum.inr 4881, Sum.inr 4884, Sum.inr 4885, Sum.inr 4886, Sum.inr 4891, Sum.inr 4892, Sum.inr 4900, Sum.inr 4930, Sum.inr 4931, Sum.inr 4933, Sum.inr 4934]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk48 : Array Master := #[Sum.inr 4935, Sum.inr 4942, Sum.inr 4944, Sum.inr 4945, Sum.inr 4951, Sum.inr 4954, Sum.inr 4955, Sum.inr 4956, Sum.inr 4957, Sum.inr 4958, Sum.inr 4959, Sum.inr 4963, Sum.inr 4964, Sum.inr 4965, Sum.inr 4966, Sum.inr 4975, Sum.inr 4976, Sum.inr 4992, Sum.inr 4993, Sum.inr 4999, Sum.inr 5004, Sum.inr 5005, Sum.inr 5011, Sum.inr 5034, Sum.inr 5035, Sum.inr 5040, Sum.inr 5041, Sum.inr 5042, Sum.inr 5043, Sum.inr 5044, Sum.inr 5064, Sum.inr 5065, Sum.inr 5066, Sum.inr 5067, Sum.inr 5069, Sum.inr 5071, Sum.inr 5074, Sum.inr 5077, Sum.inr 5082, Sum.inr 5083, Sum.inr 5085, Sum.inr 5086, Sum.inr 5087, Sum.inr 5090, Sum.inr 5091, Sum.inr 5092, Sum.inr 5097, Sum.inr 5103, Sum.inr 5112, Sum.inr 5116, Sum.inr 5128, Sum.inr 5129, Sum.inr 5132, Sum.inr 5138, Sum.inr 5139, Sum.inr 5140, Sum.inr 5144, Sum.inr 5145, Sum.inr 5146, Sum.inr 5147, Sum.inr 5150, Sum.inr 5151, Sum.inr 5160, Sum.inr 5161]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk49 : Array Master := #[Sum.inr 5164, Sum.inr 5173, Sum.inr 5175, Sum.inr 5181, Sum.inr 5183, Sum.inr 5184, Sum.inr 5185, Sum.inr 5187, Sum.inr 5188, Sum.inr 5189, Sum.inr 5197, Sum.inr 5198, Sum.inr 5199, Sum.inr 5201, Sum.inr 5205, Sum.inr 5206, Sum.inr 5215, Sum.inr 5216, Sum.inr 5217, Sum.inr 5219, Sum.inr 5220, Sum.inr 5222, Sum.inr 5223, Sum.inr 5226, Sum.inr 5229, Sum.inr 5230, Sum.inr 5231, Sum.inr 5232, Sum.inr 5233, Sum.inr 5235, Sum.inr 5236, Sum.inr 5243, Sum.inr 5244, Sum.inr 5249, Sum.inr 5251, Sum.inr 5252, Sum.inr 5253, Sum.inr 5254, Sum.inr 5255, Sum.inr 5260, Sum.inr 5262, Sum.inr 5263, Sum.inr 5264, Sum.inr 5265, Sum.inr 5266, Sum.inr 5267, Sum.inr 5268, Sum.inr 5269, Sum.inr 5270, Sum.inr 5276, Sum.inr 5277, Sum.inr 5278, Sum.inr 5279, Sum.inr 5281, Sum.inr 5282, Sum.inr 5286, Sum.inr 5287, Sum.inr 5288, Sum.inr 5289, Sum.inr 5295, Sum.inr 5297, Sum.inr 5299, Sum.inr 5300, Sum.inr 5303]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk5 : Array Master := #[Sum.inr 586, Sum.inr 587, Sum.inr 588, Sum.inr 589, Sum.inr 590, Sum.inr 591, Sum.inr 592, Sum.inr 593, Sum.inr 594, Sum.inr 595, Sum.inr 596, Sum.inr 597, Sum.inr 598, Sum.inr 599, Sum.inr 600, Sum.inr 601, Sum.inr 602, Sum.inr 603, Sum.inr 604, Sum.inr 605, Sum.inr 606, Sum.inr 607, Sum.inr 608, Sum.inr 609, Sum.inr 610, Sum.inr 611, Sum.inr 612, Sum.inr 613, Sum.inr 614, Sum.inr 615, Sum.inr 616, Sum.inr 617, Sum.inr 618, Sum.inr 619, Sum.inr 620, Sum.inr 621, Sum.inr 622, Sum.inr 623, Sum.inr 624, Sum.inr 625, Sum.inr 626, Sum.inr 627, Sum.inr 628, Sum.inr 629, Sum.inr 630, Sum.inr 631, Sum.inr 632, Sum.inr 633, Sum.inr 634, Sum.inr 635, Sum.inr 636, Sum.inr 637, Sum.inr 638, Sum.inr 639, Sum.inr 640, Sum.inr 641, Sum.inr 642, Sum.inr 643, Sum.inr 651, Sum.inr 653, Sum.inr 654, Sum.inr 656, Sum.inr 657, Sum.inr 658]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk50 : Array Master := #[Sum.inr 5311, Sum.inr 5338, Sum.inr 5339, Sum.inr 5340, Sum.inr 5348, Sum.inr 5350, Sum.inr 5353, Sum.inr 5357, Sum.inr 5358, Sum.inr 5359, Sum.inr 5360, Sum.inr 5361, Sum.inr 5362, Sum.inr 5376, Sum.inr 5377, Sum.inr 5379, Sum.inr 5381, Sum.inr 5382, Sum.inr 5385, Sum.inr 5399, Sum.inr 5402, Sum.inr 5407, Sum.inr 5414, Sum.inr 5419, Sum.inr 5420, Sum.inr 5421, Sum.inr 5425, Sum.inr 5426, Sum.inr 5429, Sum.inr 5430, Sum.inr 5436, Sum.inr 5445, Sum.inr 5446, Sum.inr 5461, Sum.inr 5463, Sum.inr 5470, Sum.inr 5480]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk6 : Array Master := #[Sum.inr 660, Sum.inr 662, Sum.inr 663, Sum.inr 664, Sum.inr 665, Sum.inr 668, Sum.inr 670, Sum.inr 671, Sum.inr 674, Sum.inr 675, Sum.inr 676, Sum.inr 677, Sum.inr 679, Sum.inr 681, Sum.inr 682, Sum.inr 683, Sum.inr 684, Sum.inr 685, Sum.inr 686, Sum.inr 690, Sum.inr 692, Sum.inr 694, Sum.inr 695, Sum.inr 698, Sum.inr 699, Sum.inr 700, Sum.inr 701, Sum.inr 702, Sum.inr 703, Sum.inr 704, Sum.inr 705, Sum.inr 706, Sum.inr 707, Sum.inr 708, Sum.inr 710, Sum.inr 713, Sum.inr 715, Sum.inr 716, Sum.inr 719, Sum.inr 720, Sum.inr 724, Sum.inr 725, Sum.inr 726, Sum.inr 729, Sum.inr 730, Sum.inr 731, Sum.inr 732, Sum.inr 733, Sum.inr 734, Sum.inr 735, Sum.inr 736, Sum.inr 737, Sum.inr 738, Sum.inr 739, Sum.inr 740, Sum.inr 741, Sum.inr 742, Sum.inr 743, Sum.inr 744, Sum.inr 746, Sum.inr 748, Sum.inr 749, Sum.inr 750, Sum.inr 751]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk7 : Array Master := #[Sum.inr 752, Sum.inr 753, Sum.inr 754, Sum.inr 755, Sum.inr 756, Sum.inr 758, Sum.inr 760, Sum.inr 761, Sum.inr 762, Sum.inr 763, Sum.inr 764, Sum.inr 765, Sum.inr 769, Sum.inr 771, Sum.inr 773, Sum.inr 774, Sum.inr 776, Sum.inr 778, Sum.inr 780, Sum.inr 781, Sum.inr 782, Sum.inr 783, Sum.inr 784, Sum.inr 785, Sum.inr 786, Sum.inr 787, Sum.inr 789, Sum.inr 790, Sum.inr 791, Sum.inr 793, Sum.inr 794, Sum.inr 795, Sum.inr 796, Sum.inr 797, Sum.inr 798, Sum.inr 799, Sum.inr 800, Sum.inr 801, Sum.inr 803, Sum.inr 804, Sum.inr 807, Sum.inr 808, Sum.inr 811, Sum.inr 813, Sum.inr 814, Sum.inr 815, Sum.inr 818, Sum.inr 819, Sum.inr 820, Sum.inr 822, Sum.inr 823, Sum.inr 824, Sum.inr 825, Sum.inr 826, Sum.inr 827, Sum.inr 828, Sum.inr 829, Sum.inr 830, Sum.inr 831, Sum.inr 832, Sum.inr 840, Sum.inr 841, Sum.inr 842, Sum.inr 843]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk8 : Array Master := #[Sum.inr 844, Sum.inr 845, Sum.inr 847, Sum.inr 848, Sum.inr 849, Sum.inr 853, Sum.inr 857, Sum.inr 858, Sum.inr 860, Sum.inr 862, Sum.inr 864, Sum.inr 865, Sum.inr 866, Sum.inr 867, Sum.inr 868, Sum.inr 869, Sum.inr 870, Sum.inr 871, Sum.inr 872, Sum.inr 873, Sum.inr 874, Sum.inr 876, Sum.inr 879, Sum.inr 881, Sum.inr 882, Sum.inr 885, Sum.inr 887, Sum.inr 891, Sum.inr 892, Sum.inr 893, Sum.inr 897, Sum.inr 898, Sum.inr 899, Sum.inr 900, Sum.inr 901, Sum.inr 902, Sum.inr 903, Sum.inr 905, Sum.inr 906, Sum.inr 908, Sum.inr 909, Sum.inr 910, Sum.inr 911, Sum.inr 912, Sum.inr 913, Sum.inr 914, Sum.inr 915, Sum.inr 916, Sum.inr 917, Sum.inr 919, Sum.inr 921, Sum.inr 922, Sum.inr 923, Sum.inr 924, Sum.inr 925, Sum.inr 927, Sum.inr 928, Sum.inr 929, Sum.inr 930, Sum.inr 931, Sum.inr 932, Sum.inr 933, Sum.inr 934, Sum.inr 935]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyChunk9 : Array Master := #[Sum.inr 936, Sum.inr 937, Sum.inr 938, Sum.inr 939, Sum.inr 940, Sum.inr 941, Sum.inr 942, Sum.inr 943, Sum.inr 944, Sum.inr 945, Sum.inr 946, Sum.inr 947, Sum.inr 948, Sum.inr 949, Sum.inr 950, Sum.inr 951, Sum.inr 952, Sum.inr 953, Sum.inr 954, Sum.inr 972, Sum.inr 973, Sum.inr 975, Sum.inr 977, Sum.inr 979, Sum.inr 980, Sum.inr 981, Sum.inr 982, Sum.inr 983, Sum.inr 984, Sum.inr 985, Sum.inr 986, Sum.inr 987, Sum.inr 988, Sum.inr 989, Sum.inr 990, Sum.inr 991, Sum.inr 992, Sum.inr 993, Sum.inr 994, Sum.inr 995, Sum.inr 997, Sum.inr 998, Sum.inr 999, Sum.inr 1000, Sum.inr 1001, Sum.inr 1002, Sum.inr 1005, Sum.inr 1006, Sum.inr 1008, Sum.inr 1009, Sum.inr 1010, Sum.inr 1011, Sum.inr 1012, Sum.inr 1014, Sum.inr 1015, Sum.inr 1016, Sum.inr 1017, Sum.inr 1018, Sum.inr 1019, Sum.inr 1021, Sum.inr 1022, Sum.inr 1023, Sum.inr 1024, Sum.inr 1025]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_KeyMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def keyMap (i : Fin 3237) : Master :=
  ((#[keyChunk0, keyChunk1, keyChunk2, keyChunk3, keyChunk4, keyChunk5, keyChunk6, keyChunk7, keyChunk8, keyChunk9, keyChunk10, keyChunk11, keyChunk12, keyChunk13, keyChunk14, keyChunk15, keyChunk16, keyChunk17, keyChunk18, keyChunk19, keyChunk20, keyChunk21, keyChunk22, keyChunk23, keyChunk24, keyChunk25, keyChunk26, keyChunk27, keyChunk28, keyChunk29, keyChunk30, keyChunk31, keyChunk32, keyChunk33, keyChunk34, keyChunk35, keyChunk36, keyChunk37, keyChunk38, keyChunk39, keyChunk40, keyChunk41, keyChunk42, keyChunk43, keyChunk44, keyChunk45, keyChunk46, keyChunk47, keyChunk48, keyChunk49, keyChunk50])[i.val / 64]!)[i.val % 64]!

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_MixedTargetBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def masterLess (a b : Master) : Bool :=
  match a, b with
  | .inl i, .inl j => decide (i < j)
  | .inl _, .inr _ => true
  | .inr _, .inl _ => false
  | .inr i, .inr j => decide (i < j)

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value0 : Sparse (Fin 909) := [(0, (1 / 1))]

def value1 : Sparse (Fin 909) := [(58, (1 / 1))]

def value10 : Sparse (Fin 909) := [(1, (-1 / 4)), (2, (-1 / 4))]

def value11 : Sparse (Fin 909) := [(0, (1 / 20)), (1, (-1 / 4))]

def value12 : Sparse (Fin 909) := [(2, (1 / 12)), (6, (1 / 6)), (9, (-1 / 3)), (58, (1 / 12))]

def value13 : Sparse (Fin 909) := [(5, (-1 / 3)), (9, (-2 / 3))]

def value14 : Sparse (Fin 909) := [(2, (1 / 12)), (6, (-1 / 6)), (58, (1 / 12))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue0 : Sparse (Fin 909) := [(0, (11 / 72)), (1, (5 / 24)), (2, (5 / 36))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue1 : Sparse (Fin 909) := [(0, (1 / 6)), (1, (-5 / 24)), (2, (-5 / 24))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue2 : Sparse (Fin 909) := [(0, (1 / 6)), (2, (5 / 6))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue3 : Sparse (Fin 909) := [(0, (1 / 9)), (1, (5 / 24)), (2, (-5 / 72))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue4 : Sparse (Fin 909) := [(0, (11 / 72)), (1, (-5 / 36)), (2, (5 / 72))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue5 : Sparse (Fin 909) := [(0, (5 / 24)), (1, (-5 / 24))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue6 : Sparse (Fin 909) := [(0, (1 / 6)), (1, (5 / 6))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value100 : Sparse (Fin 909) := [(268, (1 / 1))]

def value101 : Sparse (Fin 909) := [(63, (1 / 1))]

def value102 : Sparse (Fin 909) := [(7, (-1 / 3)), (35, (-1 / 3)), (67, (-1 / 3))]

def value103 : Sparse (Fin 909) := [(64, (1 / 1))]

def value104 : Sparse (Fin 909) := [(271, (1 / 1))]

def value105 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (13, (-2 / 3))]

def value106 : Sparse (Fin 909) := [(26, (-1 / 3)), (35, (-1 / 3)), (67, (-1 / 3))]

def value107 : Sparse (Fin 909) := [(3, (-1 / 3)), (13, (-1 / 3)), (34, (-1 / 3))]

def value108 : Sparse (Fin 909) := [(26, (-1 / 3)), (34, (-1 / 3)), (67, (-1 / 3))]

def value109 : Sparse (Fin 909) := [(3, (-1 / 3)), (26, (-1 / 3)), (34, (-1 / 3))]

def value110 : Sparse (Fin 909) := [(65, (1 / 1))]

def value111 : Sparse (Fin 909) := [(33, (1 / 1))]

def value112 : Sparse (Fin 909) := [(273, (1 / 1))]

def value113 : Sparse (Fin 909) := [(35, (-1 / 3)), (67, (-1 / 3)), (276, (-1 / 3))]

def value114 : Sparse (Fin 909) := [(66, (1 / 1))]

def value115 : Sparse (Fin 909) := [(275, (1 / 1))]

def value116 : Sparse (Fin 909) := [(1, (-1 / 8)), (2, (-1 / 24)), (5, (1 / 3)), (6, (-1 / 12)), (9, (1 / 6)), (68, (-1 / 2))]

def value117 : Sparse (Fin 909) := [(1, (-1 / 12)), (2, (-1 / 12)), (5, (1 / 6)), (27, (-1 / 2)), (68, (-1 / 1))]

def value118 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 12)), (2, (1 / 12)), (5, (1 / 6)), (6, (-1 / 24))]

def value119 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 6)), (9, (1 / 12)), (69, (-1 / 3))]

def value120 : Sparse (Fin 909) := [(7, (-1 / 3)), (69, (-1 / 3)), (70, (-1 / 3))]

def value121 : Sparse (Fin 909) := [(35, (-1 / 3)), (70, (-1 / 3)), (278, (-1 / 3))]

def value122 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (1 / 12)), (6, (-1 / 16)), (9, (1 / 6)), (58, (-1 / 48))]

def value123 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 24)), (5, (1 / 12)), (6, (-1 / 48)), (9, (1 / 12)), (71, (-1 / 3))]

def value124 : Sparse (Fin 909) := [(8, (-1 / 3)), (71, (-2 / 3))]

def value125 : Sparse (Fin 909) := [(277, (1 / 1))]

def value126 : Sparse (Fin 909) := [(5, (1 / 12)), (9, (1 / 12)), (69, (-1 / 3)), (71, (-1 / 3))]

def value127 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 12)), (69, (-1 / 3)), (71, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue7 : Sparse (Fin 909) := [(0, (19 / 72)), (1, (5 / 72))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value128 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (-1 / 48)), (9, (1 / 12)), (70, (-1 / 3)), (71, (-1 / 3))]

def value129 : Sparse (Fin 909) := [(2, (1 / 24)), (6, (-1 / 24)), (9, (1 / 12)), (70, (-1 / 3))]

def value130 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 24)), (9, (1 / 12)), (58, (-1 / 48)), (278, (-1 / 3))]

def value131 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (-1 / 6)), (6, (-1 / 24))]

def value132 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 12)), (35, (-1 / 3)), (52, (-1 / 3))]

def value133 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (82, (-1 / 3)), (128, (-1 / 3))]

def value134 : Sparse (Fin 909) := [(81, (1 / 1))]

def value135 : Sparse (Fin 909) := [(306, (1 / 1))]

def value136 : Sparse (Fin 909) := [(307, (1 / 1))]

def value137 : Sparse (Fin 909) := [(11, (-1 / 3)), (35, (-1 / 3)), (276, (-1 / 3))]

def value138 : Sparse (Fin 909) := [(35, (-1 / 3)), (82, (-1 / 3)), (276, (-1 / 3))]

def value139 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (-1 / 6)), (9, (1 / 12))]

def value140 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 12)), (7, (-1 / 3)), (69, (-1 / 3))]

def value141 : Sparse (Fin 909) := [(7, (-1 / 3)), (35, (-1 / 3)), (70, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1088 : Sparse (Fin 909) := [(28, (1 / 1))]

def value1089 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (5 / 144)), (5, (-1 / 12)), (6, (1 / 144)), (35, (1 / 9)), (52, (1 / 9)), (306, (-1 / 3))]

def value1090 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (2 / 9)), (35, (2 / 9)), (67, (1 / 9)), (273, (-1 / 3))]

def value1091 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (52, (2 / 9)), (69, (1 / 9)), (262, (-1 / 3))]

def value1092 : Sparse (Fin 909) := [(1, (-7 / 144)), (2, (-7 / 144)), (5, (-1 / 36)), (123, (-1 / 3))]

def value1093 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (1 / 9)), (26, (2 / 9)), (35, (1 / 9)), (123, (-1 / 3))]

def value1094 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (52, (1 / 9))]

def value1095 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (6, (1 / 144)), (35, (1 / 9)), (52, (1 / 9))]

def value1096 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (-11 / 144)), (2, (1 / 144)), (31, (-1 / 3))]

def value1097 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (2 / 9)), (128, (1 / 9)), (490, (-1 / 3))]

def value1098 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (3, (2 / 9)), (12, (1 / 9)), (13, (1 / 9)), (33, (-1 / 3))]

def value1099 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 48)), (3, (1 / 9))]

def value1100 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (5, (-1 / 18)), (7, (1 / 9)), (8, (2 / 9)), (81, (-1 / 3))]

def value1101 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (5 / 36)), (6, (1 / 72)), (226, (-1 / 3))]

def value1102 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (6, (-1 / 36)), (11, (1 / 9)), (35, (1 / 9))]

def value1103 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (1 / 144)), (6, (1 / 144)), (26, (1 / 9)), (35, (1 / 9))]

def value1104 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 72)), (5, (-1 / 36)), (56, (-1 / 3))]

def value1105 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 144)), (3, (1 / 9)), (13, (1 / 3)), (35, (1 / 9)), (52, (1 / 9))]

def value1106 : Sparse (Fin 909) := [(13, (1 / 9)), (35, (2 / 9)), (52, (2 / 9)), (60, (1 / 3)), (128, (1 / 9))]

def value1107 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (5 / 36)), (2, (1 / 72)), (25, (-1 / 3))]

def value1108 : Sparse (Fin 909) := [(2, (1 / 144)), (5, (1 / 36)), (6, (1 / 144)), (228, (-1 / 3))]

def value1109 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (-1 / 36)), (3, (1 / 9)), (26, (1 / 9))]

def value1110 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (1 / 144)), (2, (1 / 144)), (3, (1 / 9)), (4, (1 / 9))]

def value1111 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (1 / 144)), (3, (2 / 9)), (4, (1 / 9)), (25, (-1 / 3)), (26, (1 / 9))]

def value1112 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-1 / 12)), (3, (2 / 9)), (12, (1 / 3))]

def value1113 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 18)), (7, (1 / 3)), (8, (1 / 9)), (35, (1 / 9))]

def value1114 : Sparse (Fin 909) := [(0, (-1 / 90)), (1, (-1 / 18))]

def value1115 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 24)), (5, (-1 / 36)), (6, (-1 / 144)), (11, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value1116 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (3, (1 / 9)), (4, (1 / 9)), (26, (1 / 9))]

def value1117 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 144)), (4, (1 / 9))]

def value1118 : Sparse (Fin 909) := [(0, (-19 / 720)), (1, (-1 / 144))]

def value1119 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-7 / 72)), (4, (1 / 9))]

def value1120 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (5, (-1 / 36)), (7, (2 / 9)), (35, (1 / 9)), (54, (-1 / 3))]

def value1121 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 36)), (5, (-1 / 18)), (6, (1 / 72)), (11, (1 / 9)), (26, (1 / 9)), (35, (1 / 3))]

def value1122 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 48)), (2, (-1 / 144)), (3, (1 / 9)), (26, (1 / 9))]

def value1123 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (1 / 36)), (3, (1 / 3)), (4, (1 / 9)), (26, (1 / 9))]

def value1124 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (-1 / 36)), (26, (-1 / 9))]

def value1125 : Sparse (Fin 909) := [(7, (1 / 9)), (26, (2 / 9)), (35, (1 / 3)), (67, (1 / 3))]

def value1126 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-1 / 36)), (4, (-1 / 9))]

def value1127 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (35, (2 / 9)), (52, (1 / 9)), (81, (-1 / 3))]

def value1128 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-5 / 144)), (5, (-1 / 18)), (6, (1 / 72)), (26, (1 / 9)), (35, (1 / 9))]

def value1129 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (2, (1 / 36)), (5, (-1 / 18)), (8, (2 / 9)), (56, (-1 / 3))]

def value1130 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (1 / 48)), (2, (1 / 24)), (8, (1 / 6)), (30, (-1 / 2))]

def value1131 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 24)), (2, (1 / 48)), (24, (-1 / 2)), (27, (1 / 4)), (30, (-1 / 2))]

def value1132 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 48)), (5, (-1 / 12)), (8, (1 / 6)), (56, (-1 / 2))]

def value1133 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 12)), (5, (-1 / 6)), (6, (1 / 24)), (201, (-1 / 2)), (818, (-1 / 2))]

def value1134 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 16)), (5, (1 / 12)), (6, (1 / 48)), (8, (1 / 6)), (201, (-1 / 2))]

def value1135 : Sparse (Fin 909) := [(0, (1 / 30)), (1, (-1 / 8)), (2, (1 / 24))]

def value1136 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-1 / 16)), (2, (1 / 32)), (27, (1 / 8)), (31, (-1 / 2)), (51, (-1 / 2))]

def value1137 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-1 / 48)), (5, (-1 / 24)), (6, (1 / 48)), (68, (1 / 8)), (237, (-1 / 2)), (494, (-1 / 2))]

def value1138 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (-1 / 48)), (3, (1 / 6)), (5, (-1 / 24)), (13, (1 / 6)), (52, (1 / 6))]

def value1139 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-1 / 32)), (2, (-1 / 48)), (3, (1 / 6)), (13, (1 / 6))]

def value1140 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (5 / 48)), (5, (-1 / 12)), (6, (1 / 24)), (52, (1 / 3)), (128, (1 / 6))]

def value1141 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 12)), (2, (1 / 32)), (3, (1 / 6)), (4, (1 / 6)), (31, (-1 / 2))]

def value1142 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 12)), (2, (1 / 16)), (3, (1 / 3)), (12, (1 / 6))]

def value1143 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (3, (1 / 6)), (5, (-1 / 24)), (55, (-1 / 2))]

def value1144 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 24)), (5, (-1 / 12)), (6, (-1 / 48)), (9, (-1 / 24)), (52, (1 / 6)), (728, (-1 / 2))]

def value1145 : Sparse (Fin 909) := [(5, (1 / 12)), (9, (-1 / 12))]

def value1146 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-1 / 12)), (2, (1 / 16)), (5, (-1 / 24)), (27, (1 / 8))]

def value1147 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 24)), (27, (1 / 8))]

def value1149 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 12)), (2, (-1 / 16)), (5, (-1 / 24)), (6, (1 / 96))]

def value1150 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 24)), (5, (-1 / 24)), (6, (1 / 96))]

def value1151 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (-1 / 12)), (2, (1 / 48))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1280 : Sparse (Fin 909) := [(0, (-53 / 720)), (1, (1 / 144))]

def value1281 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 24)), (3, (-1 / 9)), (4, (1 / 9)), (12, (1 / 9))]

def value1282 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 36)), (3, (1 / 9)), (13, (1 / 9)), (52, (-1 / 9))]

def value1283 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (2 / 9)), (4, (1 / 9)), (26, (-1 / 9))]

def value1284 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 72)), (2, (-1 / 144))]

def value1285 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (1 / 72)), (3, (2 / 9)), (7, (-1 / 9))]

def value1286 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (5 / 144)), (3, (-1 / 9)), (52, (1 / 9))]

def value1287 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (11 / 96)), (6, (1 / 96)), (13, (1 / 6)), (35, (1 / 6))]

def value1288 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 24)), (5, (-1 / 24)), (6, (1 / 96))]

def value1290 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 12)), (5, (1 / 6)), (6, (-1 / 24))]

def value1291 : Sparse (Fin 909) := [(0, (1 / 240)), (2, (1 / 48))]

def value1292 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 12)), (2, (-1 / 24))]

def value1293 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 8)), (2, (-1 / 12))]

def value1294 : Sparse (Fin 909) := [(0, (-7 / 120)), (1, (-1 / 24))]

def value1295 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (5, (1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (69, (1 / 9))]

def value1296 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (2 / 9)), (7, (1 / 9)), (26, (1 / 9))]

def value1297 : Sparse (Fin 909) := [(7, (-1 / 9)), (35, (2 / 9)), (67, (1 / 9)), (70, (1 / 9))]

def value1298 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (6, (1 / 144)), (8, (1 / 9)), (71, (1 / 9))]

def value1299 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (8, (1 / 9))]

def value1300 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (7, (1 / 9)), (35, (-1 / 9)), (70, (1 / 9))]

def value1301 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (1 / 48)), (3, (-1 / 9)), (7, (1 / 9))]

def value1302 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (7, (-1 / 9)), (8, (1 / 9)), (69, (1 / 9))]

def value1303 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 72)), (5, (-1 / 36)), (123, (-1 / 3)), (124, (-1 / 3))]

def value1304 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 72)), (2, (1 / 144)), (23, (-1 / 3)), (25, (-1 / 3))]

def value1305 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (64, (-1 / 3)), (125, (-1 / 3))]

def value1306 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (3, (2 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 3)), (52, (2 / 9))]

def value1307 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (52, (-1 / 9)), (69, (1 / 9))]

def value1308 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 36)), (52, (1 / 9)), (126, (-1 / 3))]

def value1309 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 18)), (2, (1 / 144)), (3, (1 / 9)), (4, (1 / 9)), (24, (-1 / 3))]

def value1310 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (8, (1 / 9)), (51, (-1 / 3)), (126, (-1 / 3))]

def value1311 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-11 / 144)), (2, (1 / 72)), (3, (2 / 9)), (7, (1 / 9)), (12, (1 / 9))]

def value1312 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 18)), (2, (7 / 144)), (5, (-1 / 18)), (13, (1 / 9)), (52, (2 / 9)), (69, (1 / 9))]

def value1313 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (13, (2 / 9)), (35, (1 / 9)), (52, (1 / 9)), (125, (-1 / 3))]

def value1314 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 24)), (3, (2 / 9)), (12, (2 / 9)), (23, (-1 / 3))]

def value1315 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (51, (-1 / 3)), (124, (-1 / 3))]

def value1316 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (3, (2 / 9)), (4, (1 / 9)), (7, (1 / 9))]

def value1317 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 18)), (7, (1 / 9)), (52, (1 / 9)), (69, (1 / 9))]

def value1318 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (2 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (197, (-1 / 3))]

def value1319 : Sparse (Fin 909) := [(24, (-1 / 3)), (55, (-1 / 3)), (197, (-1 / 3))]

def value1320 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-5 / 144)), (3, (1 / 9)), (6, (1 / 144)), (7, (1 / 9)), (13, (1 / 9)), (35, (2 / 9)), (70, (1 / 9))]

def value1321 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (13, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (196, (-1 / 3))]

def value1322 : Sparse (Fin 909) := [(23, (-1 / 3)), (55, (-1 / 3)), (125, (-1 / 3))]

def value1323 : Sparse (Fin 909) := [(0, (-13 / 60)), (1, (-3 / 4)), (2, (1 / 6))]

def value1324 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (7 / 144)), (5, (-1 / 12)), (6, (1 / 72)), (52, (1 / 9)), (818, (-1 / 3))]

def value1325 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (5, (1 / 18)), (6, (1 / 144)), (228, (-1 / 3)), (726, (-1 / 3))]

def value1326 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (5 / 144)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 72)), (52, (1 / 9))]

def value1327 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 48)), (52, (1 / 9)), (237, (-1 / 3))]

def value1328 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (-1 / 72)), (5, (1 / 36)), (6, (1 / 144)), (9, (-1 / 36))]

def value1329 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (5, (-1 / 36)), (55, (-1 / 3)), (228, (-1 / 3))]

def value1330 : Sparse (Fin 909) := [(253, (1 / 1))]

def value1331 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (27, (1 / 12)), (31, (-1 / 3)), (237, (-1 / 3))]

def value1332 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 36)), (238, (-1 / 3))]

def value1333 : Sparse (Fin 909) := [(0, (-1 / 240)), (2, (5 / 144)), (3, (1 / 9)), (31, (-1 / 3))]

def value1334 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (-1 / 36)), (3, (1 / 9))]

def value1335 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (1 / 48)), (5, (-1 / 36))]

def value1336 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-5 / 144)), (2, (1 / 36)), (3, (2 / 9)), (4, (1 / 9)), (52, (1 / 9))]

def value1337 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 72)), (5, (-1 / 36)), (13, (2 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value1338 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (5, (1 / 18)), (6, (1 / 144)), (201, (-1 / 3)), (796, (-1 / 3))]

def value1339 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (-1 / 24)), (6, (1 / 144)), (237, (-1 / 3))]

def value1340 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (-1 / 18)), (6, (1 / 144)), (52, (1 / 9))]

def value1341 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 16)), (2, (1 / 16)), (5, (-1 / 9)), (6, (1 / 144)), (8, (1 / 9)), (52, (1 / 9))]

def value1342 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (1 / 9)), (309, (-1 / 3))]

def value1343 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 18)), (6, (-1 / 144)), (11, (1 / 9)), (35, (1 / 9)), (728, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1344 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 9)), (2, (-1 / 72)), (27, (1 / 12))]

def value1345 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (5 / 144)), (5, (-1 / 36))]

def value1346 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-7 / 144)), (2, (1 / 72)), (3, (1 / 9)), (12, (1 / 9)), (51, (-1 / 3))]

def value1347 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 18)), (2, (-1 / 144)), (3, (1 / 9)), (26, (1 / 9)), (55, (-1 / 3))]

def value1348 : Sparse (Fin 909) := [(1, (-1 / 144)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3))]

def value1349 : Sparse (Fin 909) := [(0, (-3 / 80)), (1, (-1 / 36)), (2, (1 / 144))]

def value1350 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 12)), (2, (-5 / 72))]

def value1351 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (1 / 36)), (5, (-1 / 18)), (7, (1 / 9)), (8, (1 / 9)), (51, (-1 / 3))]

def value1352 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (1 / 144)), (3, (1 / 9)), (13, (1 / 9)), (56, (-1 / 3))]

def value1353 : Sparse (Fin 909) := [(1, (1 / 144)), (5, (-1 / 18)), (6, (-1 / 144)), (35, (1 / 9)), (82, (1 / 9)), (796, (-1 / 3))]

def value1354 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (5, (-1 / 18)), (71, (1 / 9))]

def value1355 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 48)), (13, (1 / 9)), (26, (1 / 9)), (35, (2 / 9))]

def value1356 : Sparse (Fin 909) := [(2, (1 / 48)), (6, (-1 / 144)), (11, (1 / 9)), (35, (2 / 9)), (70, (1 / 9))]

def value1357 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-7 / 36)), (2, (1 / 72))]

def value1358 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (2 / 9)), (13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (262, (-1 / 3))]

def value1359 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 144)), (2, (-1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (236, (-1 / 3))]

def value1360 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (-1 / 72)), (2, (1 / 72)), (30, (-1 / 3))]

def value1361 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 36)), (2, (5 / 144)), (5, (-1 / 36)), (8, (1 / 9)), (236, (-1 / 3))]

def value1362 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 72)), (2, (1 / 36)), (8, (1 / 9))]

def value1363 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 36)), (5, (-1 / 18)), (6, (1 / 72)), (71, (1 / 9))]

def value1364 : Sparse (Fin 909) := [(3, (2 / 9)), (7, (1 / 9)), (35, (2 / 9)), (52, (1 / 9)), (256, (-1 / 3))]

def value1365 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 18)), (6, (1 / 144)), (26, (1 / 9)), (35, (1 / 9)), (197, (-1 / 3))]

def value1366 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (2, (1 / 36)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (126, (-1 / 3))]

def value1367 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (5 / 144)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (8, (1 / 9)), (71, (1 / 9))]

def value1368 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (27, (1 / 12)), (30, (-1 / 3)), (236, (-1 / 3))]

def value1369 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (5, (-1 / 36)), (56, (-1 / 3)), (197, (-1 / 3))]

def value1370 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (24, (-1 / 3)), (27, (1 / 12)), (126, (-1 / 3))]

def value1371 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 144)), (2, (1 / 24)), (5, (-1 / 18)), (8, (2 / 9)), (71, (1 / 9))]

def value1372 : Sparse (Fin 909) := [(51, (-1 / 3)), (56, (-1 / 3)), (262, (-1 / 3))]

def value1373 : Sparse (Fin 909) := [(2, (-1 / 24)), (6, (-1 / 24)), (723, (-2 / 3))]

def value1374 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (54, (-2 / 3))]

def value1375 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (5 / 72)), (6, (1 / 144)), (196, (-1 / 3)), (226, (-1 / 3))]

def value1376 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (5, (-1 / 36)), (54, (-1 / 3)), (125, (-1 / 3))]

def value1377 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (23, (-1 / 3)), (27, (1 / 12)), (124, (-1 / 3))]

def value1378 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (5 / 144)), (3, (1 / 9)), (5, (-1 / 18)), (7, (2 / 9)), (69, (1 / 9))]

def value1379 : Sparse (Fin 909) := [(2, (-1 / 96)), (5, (1 / 2)), (6, (-3 / 32)), (7, (-1 / 1)), (9, (5 / 24)), (35, (-1 / 2)), (69, (-3 / 2)), (70, (-4 / 3)), (71, (-1 / 1)), (257, (-1 / 3))]

def value1380 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 96)), (2, (-7 / 96)), (3, (-1 / 2)), (5, (7 / 24)), (6, (-1 / 32)), (7, (-1 / 2)), (9, (1 / 24)), (35, (-5 / 6)), (52, (-1 / 1)), (69, (-1 / 1)), (70, (-1 / 2)), (71, (-1 / 2)), (256, (3 / 2)), (257, (-1 / 3)), (495, (-1 / 2))]

def value1381 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-19 / 96)), (2, (-7 / 32)), (5, (7 / 12)), (6, (-5 / 96)), (7, (-1 / 6)), (8, (-1 / 1)), (9, (1 / 6)), (52, (-1 / 3)), (69, (-7 / 6)), (70, (-1 / 6)), (71, (-5 / 2)), (256, (1 / 2)), (495, (-1 / 6))]

def value1382 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 24)), (2, (-5 / 48)), (3, (-1 / 3)), (5, (3 / 8)), (6, (-1 / 32)), (7, (-1 / 1)), (8, (-1 / 3)), (9, (1 / 8)), (35, (-2 / 3)), (52, (-1 / 3)), (69, (-4 / 3)), (70, (-5 / 6)), (71, (-1 / 1)), (256, (1 / 1)), (257, (-1 / 3)), (495, (-1 / 3))]

def value1383 : Sparse (Fin 909) := [(1, (7 / 96)), (2, (5 / 96)), (5, (5 / 24)), (6, (-1 / 48)), (7, (-1 / 6)), (9, (1 / 6)), (26, (-1 / 6)), (35, (-1 / 2)), (69, (-1 / 6)), (70, (-1 / 6)), (71, (-1 / 3)), (259, (1 / 2)), (495, (-1 / 6))]

def value1384 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 6)), (2, (-17 / 96)), (3, (-1 / 6)), (5, (11 / 24)), (6, (-7 / 96)), (8, (-1 / 6)), (9, (1 / 8)), (13, (-1 / 3)), (35, (-1 / 6)), (52, (-2 / 3)), (69, (-1 / 3)), (71, (-1 / 3)), (128, (-1 / 3)), (262, (1 / 2)), (495, (-1 / 3))]

def value1385 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-11 / 96)), (2, (-3 / 32)), (3, (-1 / 3)), (5, (1 / 3)), (6, (-7 / 96)), (7, (-1 / 6)), (9, (1 / 12)), (13, (-2 / 3)), (35, (-4 / 3)), (52, (-4 / 3)), (60, (-5 / 6)), (69, (-1 / 6)), (70, (-1 / 6)), (128, (-2 / 3)), (257, (-1 / 3)), (260, (1 / 2)), (495, (-1 / 2))]

def value1386 : Sparse (Fin 909) := [(1, (1 / 12)), (2, (7 / 48)), (3, (-1 / 6)), (5, (7 / 24)), (6, (-1 / 16)), (7, (-1 / 2)), (26, (-1 / 2)), (35, (-1 / 1)), (54, (3 / 2)), (259, (3 / 2)), (260, (1 / 1)), (495, (-1 / 6))]

def value1387 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 96)), (2, (1 / 96)), (3, (-1 / 1)), (5, (7 / 24)), (6, (-1 / 24)), (7, (-1 / 2)), (13, (-1 / 2)), (35, (-4 / 3)), (52, (-1 / 1)), (60, (-1 / 3))]

def value1388 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-7 / 96)), (2, (-3 / 32)), (3, (-1 / 1)), (5, (1 / 8)), (6, (-1 / 96)), (12, (-1 / 2)), (13, (-11 / 6)), (35, (-1 / 2)), (52, (-1 / 1)), (59, (3 / 2)), (60, (-1 / 3)), (128, (-1 / 2))]

def value1389 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 8)), (2, (-1 / 8)), (3, (-1 / 2)), (4, (-1 / 6)), (5, (7 / 24)), (6, (-1 / 32)), (8, (-1 / 3)), (13, (-1 / 3)), (26, (-1 / 6)), (35, (-1 / 3)), (51, (1 / 2)), (52, (-1 / 2)), (56, (1 / 1)), (59, (1 / 2)), (128, (-1 / 6)), (259, (1 / 2)), (262, (2 / 1)), (495, (-1 / 6))]

def value1390 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-1 / 4)), (2, (-25 / 96)), (3, (-1 / 6)), (5, (2 / 3)), (6, (-1 / 12)), (7, (-1 / 3)), (8, (-2 / 3)), (13, (-1 / 3)), (35, (-1 / 6)), (52, (-2 / 3)), (59, (1 / 2)), (128, (-1 / 6))]

def value1391 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 8)), (2, (-5 / 24)), (3, (-1 / 1)), (5, (5 / 12)), (6, (-1 / 24)), (7, (-2 / 3)), (8, (-1 / 3)), (12, (-1 / 6)), (13, (-2 / 3)), (35, (-7 / 6)), (52, (-1 / 1)), (59, (1 / 2)), (60, (-1 / 3)), (128, (-1 / 6))]

def value1392 : Sparse (Fin 909) := [(1, (3 / 32)), (2, (3 / 32)), (3, (-1 / 2)), (5, (1 / 12)), (6, (-1 / 24)), (7, (-2 / 3)), (13, (-1 / 6)), (26, (-2 / 3)), (34, (-1 / 6)), (35, (-4 / 3)), (67, (-1 / 3)), (69, (-1 / 6)), (70, (-1 / 2)), (124, (1 / 2)), (196, (1 / 2)), (197, (1 / 1)), (257, (-1 / 6)), (266, (1 / 2))]

def value1393 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 24)), (2, (-1 / 48)), (3, (-1 / 3)), (5, (1 / 12)), (13, (-1 / 3)), (33, (1 / 2)), (52, (-1 / 3)), (55, (1 / 1)), (64, (1 / 1)), (125, (1 / 1)), (197, (1 / 2)), (260, (1 / 2)), (263, (-1 / 1))]

def value1394 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (3, (-1 / 6)), (5, (1 / 24)), (7, (-1 / 6)), (13, (-1 / 6)), (23, (1 / 1)), (35, (-1 / 6)), (54, (1 / 1)), (55, (1 / 2)), (63, (1 / 2)), (65, (1 / 2)), (124, (1 / 2)), (125, (3 / 2)), (196, (1 / 1)), (197, (1 / 2)), (264, (1 / 1)), (266, (1 / 2))]

def value1395 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (-1 / 24)), (3, (-5 / 6)), (5, (1 / 12)), (6, (-1 / 96)), (7, (-2 / 3)), (13, (-1 / 2)), (26, (-1 / 3)), (34, (-1 / 6)), (35, (-1 / 1)), (52, (-1 / 3)), (60, (-1 / 6)), (64, (1 / 2)), (67, (-1 / 6)), (69, (-1 / 6)), (70, (-1 / 3)), (125, (1 / 1)), (126, (1 / 2)), (197, (1 / 2)), (257, (-1 / 6)), (260, (1 / 2)), (268, (1 / 2))]

def value1396 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (-1 / 96)), (23, (1 / 2)), (24, (1 / 2)), (27, (-1 / 8)), (51, (1 / 2)), (54, (1 / 2)), (55, (1 / 2)), (56, (1 / 2)), (61, (1 / 2)), (124, (1 / 2)), (125, (1 / 2)), (126, (1 / 2)), (196, (1 / 2)), (197, (1 / 1)), (263, (-1 / 1)), (266, (1 / 2)), (268, (1 / 2))]

def value1397 : Sparse (Fin 909) := [(3, (-1 / 3)), (5, (1 / 12)), (7, (-1 / 3)), (13, (-2 / 3)), (32, (-1 / 6)), (35, (-2 / 3)), (52, (-1 / 3)), (54, (1 / 1)), (60, (-1 / 3)), (62, (1 / 1)), (69, (-1 / 6)), (70, (-1 / 6)), (125, (1 / 1)), (257, (-1 / 6)), (260, (1 / 1)), (264, (3 / 2))]

def value1398 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-7 / 96)), (6, (-1 / 48)), (13, (-1 / 3)), (32, (-1 / 6)), (35, (-1 / 6)), (60, (-1 / 3)), (63, (1 / 2)), (70, (-1 / 6)), (196, (1 / 2)), (257, (-1 / 6)), (264, (1 / 2))]

def value1399 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 96)), (5, (1 / 12)), (6, (-1 / 32)), (7, (-1 / 3)), (9, (1 / 8)), (26, (-1 / 3)), (35, (-1 / 2)), (67, (-1 / 3)), (69, (-1 / 6)), (70, (-1 / 3)), (257, (-1 / 3)), (495, (-1 / 3))]

def value1400 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 48)), (2, (-1 / 96)), (3, (-1 / 3)), (5, (1 / 12)), (13, (-1 / 6)), (34, (-1 / 6)), (52, (-1 / 6)), (60, (-1 / 6)), (64, (1 / 2)), (69, (-1 / 6)), (125, (1 / 2)), (128, (-1 / 3)), (260, (1 / 2)), (495, (-1 / 6))]

def value1401 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 16)), (2, (-1 / 24)), (3, (-5 / 6)), (5, (1 / 12)), (12, (-1 / 3)), (13, (-7 / 6)), (35, (-1 / 3)), (52, (-2 / 3)), (59, (1 / 1)), (61, (1 / 2)), (256, (1 / 2)), (263, (-1 / 1))]

def value1402 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 24)), (2, (-1 / 32)), (3, (-2 / 3)), (12, (-1 / 3)), (13, (-13 / 6)), (32, (-1 / 2)), (35, (-5 / 6)), (52, (-2 / 3)), (54, (1 / 2)), (60, (-5 / 6)), (62, (1 / 1)), (128, (-1 / 3)), (257, (-1 / 6)), (260, (1 / 2)), (264, (1 / 2)), (495, (-1 / 6))]

def value1403 : Sparse (Fin 909) := [(1, (1 / 12)), (2, (1 / 96)), (3, (-1 / 6)), (5, (1 / 12)), (6, (-1 / 32)), (26, (-1 / 6)), (34, (-1 / 6)), (35, (-1 / 6)), (54, (1 / 2)), (67, (-1 / 3)), (257, (-1 / 6)), (259, (1 / 2)), (266, (1 / 2)), (495, (-1 / 6))]

def value1404 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 96)), (2, (-1 / 96)), (3, (-2 / 3)), (4, (-1 / 6)), (5, (1 / 24)), (6, (-1 / 96)), (13, (-1 / 2)), (26, (-1 / 2)), (34, (-1 / 3)), (35, (-2 / 3)), (52, (-1 / 2)), (56, (1 / 2)), (60, (-1 / 3)), (67, (-1 / 6)), (128, (-1 / 6)), (257, (-1 / 6)), (262, (1 / 2)), (268, (1 / 2)), (495, (-1 / 6))]

def value1405 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 24)), (2, (-5 / 96)), (3, (-5 / 6)), (5, (1 / 6)), (6, (-1 / 24)), (13, (-2 / 3)), (26, (-1 / 3)), (34, (-1 / 3)), (35, (-2 / 3)), (52, (-2 / 3)), (60, (-1 / 3)), (128, (-1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1000 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 48)), (3, (1 / 9)), (4, (1 / 9)), (12, (1 / 9))]

def value1001 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (1 / 36)), (3, (2 / 9)), (13, (2 / 9)), (34, (1 / 9)), (52, (1 / 9))]

def value1002 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-1 / 12)), (3, (2 / 9)), (12, (2 / 9))]

def value1003 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (2, (1 / 24)), (3, (2 / 9)), (26, (1 / 9))]

def value1004 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 144)), (5, (-1 / 18)), (6, (1 / 144)), (7, (2 / 9)), (8, (1 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value1005 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-5 / 72)), (25, (-1 / 3)), (31, (-1 / 3))]

def value1006 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-7 / 144)), (3, (1 / 9)), (4, (2 / 9))]

def value1007 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 144)), (2, (1 / 48)), (33, (-1 / 3)), (51, (-1 / 3))]

def value1008 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (2 / 9)), (4, (1 / 9)), (12, (1 / 9))]

def value1009 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (3, (1 / 9)), (4, (-1 / 9))]

def value1010 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 24)), (3, (2 / 9)), (4, (1 / 9)), (12, (1 / 9)), (25, (-1 / 3))]

def value1011 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (13, (1 / 9)), (51, (-1 / 3)), (52, (1 / 9)), (64, (-1 / 3))]

def value1012 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-5 / 144)), (63, (-1 / 3)), (237, (-1 / 3))]

def value1013 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 144)), (2, (1 / 24)), (3, (1 / 9)), (33, (-1 / 3))]

def value1014 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (306, (-1 / 3)), (308, (-1 / 3))]

def value1015 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (1 / 9)), (13, (2 / 9)), (52, (1 / 9))]

def value1016 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (2 / 9)), (4, (1 / 9)), (26, (2 / 9)), (33, (-1 / 3))]

def value1017 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (13, (1 / 9)), (35, (1 / 9)), (55, (-1 / 3)), (63, (-1 / 3))]

def value1018 : Sparse (Fin 909) := [(3, (1 / 3)), (13, (1 / 9)), (26, (2 / 9)), (34, (1 / 3))]

def value1019 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 36)), (52, (1 / 9)), (721, (-1 / 3))]

def value1020 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 144)), (11, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3)), (721, (-1 / 3))]

def value1021 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 18)), (6, (1 / 72)), (68, (1 / 12)), (196, (-1 / 3))]

def value1022 : Sparse (Fin 909) := [(2, (-1 / 18)), (5, (-1 / 36)), (6, (-1 / 18)), (9, (-1 / 36)), (723, (-1 / 3))]

def value1023 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (5 / 144)), (5, (-1 / 36)), (9, (-1 / 36)), (35, (1 / 9)), (70, (1 / 9))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1024 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (68, (1 / 12)), (197, (-1 / 3))]

def value1025 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (13, (1 / 9)), (35, (1 / 9)), (196, (-1 / 3)), (728, (-1 / 3))]

def value1026 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (7, (1 / 9)), (35, (2 / 9)), (70, (1 / 9)), (309, (-1 / 3))]

def value1027 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 18)), (2, (1 / 72)), (23, (-1 / 3)), (27, (1 / 12))]

def value1028 : Sparse (Fin 909) := [(1, (-7 / 144)), (2, (-7 / 144)), (5, (-1 / 36)), (54, (-1 / 3))]

def value1029 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 36)), (5, (1 / 9)), (6, (1 / 72)), (199, (-1 / 3))]

def value1030 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (6, (1 / 144)), (9, (-1 / 9)), (726, (-1 / 3))]

def value1031 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (-1 / 48)), (5, (1 / 36)), (6, (1 / 144)), (7, (1 / 9)), (35, (1 / 9))]

def value1032 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9))]

def value1033 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 144)), (2, (1 / 72)), (24, (-1 / 3)), (27, (1 / 12))]

def value1034 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (199, (-1 / 3)), (726, (-1 / 3))]

def value1035 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (26, (1 / 9)), (54, (-1 / 3)), (228, (-1 / 3))]

def value1036 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (1 / 48)), (3, (2 / 9)), (7, (1 / 9)), (51, (-1 / 3))]

def value1037 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 48)), (5, (-1 / 18)), (7, (-1 / 9)), (8, (1 / 9))]

def value1038 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (7, (1 / 9)), (69, (1 / 3)), (70, (1 / 9)), (71, (2 / 9))]

def value1039 : Sparse (Fin 909) := [(1, (5 / 72)), (2, (1 / 72))]

def value1040 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-7 / 72)), (2, (1 / 144)), (3, (1 / 9)), (12, (1 / 9))]

def value1041 : Sparse (Fin 909) := [(0, (-1 / 360)), (2, (-1 / 72)), (12, (1 / 9)), (13, (2 / 9))]

def value1042 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 72)), (35, (1 / 9)), (52, (1 / 9))]

def value1043 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-7 / 144)), (2, (1 / 144)), (3, (1 / 9))]

def value1044 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 16)), (2, (1 / 72))]

def value1045 : Sparse (Fin 909) := [(0, (1 / 40)), (1, (-5 / 72)), (12, (1 / 9))]

def value1046 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (-1 / 72)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (26, (1 / 9)), (35, (1 / 9))]

def value1047 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-1 / 16)), (2, (1 / 72)), (3, (1 / 9)), (4, (1 / 9))]

def value1048 : Sparse (Fin 909) := [(0, (-1 / 90)), (1, (-1 / 18))]

def value1049 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 48)), (2, (5 / 144)), (3, (2 / 9)), (12, (1 / 9)), (13, (1 / 9)), (52, (1 / 9))]

def value1050 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (7 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9))]

def value1051 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (1 / 36)), (6, (1 / 144)), (9, (-1 / 36)), (68, (1 / 12)), (727, (-1 / 3))]

def value1052 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (5, (-1 / 36)), (27, (1 / 12)), (55, (-1 / 3))]

def value1053 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (12, (1 / 9))]

def value1054 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-1 / 48)), (12, (1 / 9))]

def value1055 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9)), (10, (-1 / 3)), (308, (-1 / 3))]

def value1056 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (3, (2 / 9)), (12, (1 / 9)), (13, (1 / 9)), (51, (-1 / 3))]

def value1057 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 9)), (12, (-1 / 9))]

def value1058 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 3)), (4, (2 / 9)), (12, (1 / 9))]

def value1059 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (23, (-1 / 3)), (24, (-1 / 3))]

def value1060 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (52, (1 / 9)), (69, (1 / 9)), (125, (-1 / 3)), (126, (-1 / 3))]

def value1061 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 36)), (5, (-1 / 36)), (6, (-1 / 144)), (9, (-1 / 36)), (68, (1 / 12)), (728, (-1 / 3))]

def value1062 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 24)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (35, (1 / 9))]

def value1063 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (-5 / 144)), (3, (1 / 9)), (13, (1 / 9))]

def value1064 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (35, (2 / 9)), (82, (1 / 9)), (309, (-1 / 3))]

def value1065 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 144)), (13, (-1 / 9)), (52, (1 / 9))]

def value1066 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 36)), (3, (2 / 9)), (12, (1 / 9)), (13, (4 / 9))]

def value1067 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (26, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (56, (-1 / 3))]

def value1068 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 144)), (35, (1 / 9)), (70, (1 / 9)), (196, (-1 / 3)), (197, (-1 / 3))]

def value1069 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (5, (1 / 36)), (6, (-1 / 36)), (35, (1 / 9)), (82, (1 / 9))]

def value1070 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (6, (1 / 48)), (201, (-1 / 3))]

def value1071 : Sparse (Fin 909) := [(2, (1 / 72)), (5, (-1 / 18)), (6, (1 / 72)), (13, (1 / 9)), (52, (2 / 9)), (82, (1 / 9)), (128, (1 / 3))]

def value1072 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-5 / 144)), (5, (-1 / 36)), (6, (1 / 72)), (13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value1073 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (1 / 9)), (55, (-1 / 3)), (237, (-1 / 3))]

def value1074 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (1 / 9)), (26, (2 / 9)), (35, (1 / 9)), (238, (-1 / 3))]

def value1075 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 36)), (5, (-1 / 18)), (6, (1 / 72)), (35, (-1 / 9))]

def value1076 : Sparse (Fin 909) := [(7, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (67, (2 / 9)), (307, (-1 / 3))]

def value1077 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (8, (1 / 9)), (201, (-1 / 3)), (818, (-1 / 3))]

def value1078 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (3, (1 / 9)), (4, (2 / 9)), (31, (-1 / 3))]

def value1079 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (1 / 36)), (3, (-1 / 9))]

def value1080 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 18)), (35, (1 / 9)), (52, (1 / 3))]

def value1081 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (1 / 144)), (2, (1 / 18)), (3, (1 / 9))]

def value1082 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 48)), (5, (-1 / 9)), (6, (1 / 72)), (7, (1 / 9)), (8, (1 / 9)), (35, (1 / 9))]

def value1083 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-5 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9))]

def value1084 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (8, (1 / 9)), (24, (-1 / 3)), (30, (-1 / 3))]

def value1085 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (71, (1 / 9)), (197, (-1 / 3)), (236, (-1 / 3))]

def value1086 : Sparse (Fin 909) := [(13, (2 / 9)), (35, (2 / 9)), (60, (2 / 9)), (490, (-1 / 3))]

def value1087 : Sparse (Fin 909) := [(13, (1 / 9)), (52, (1 / 9)), (59, (-2 / 3)), (128, (1 / 9))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1152 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-1 / 48))]

def value1153 : Sparse (Fin 909) := [(0, (1 / 30)), (1, (-1 / 8)), (2, (1 / 24))]

def value1154 : Sparse (Fin 909) := [(1, (1 / 72)), (5, (-1 / 36)), (6, (1 / 72)), (259, (-1 / 3)), (721, (-1 / 3))]

def value1155 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (35, (2 / 9)), (52, (1 / 9)), (59, (-1 / 3))]

def value1156 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (-1 / 9)), (128, (1 / 9))]

def value1157 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (2 / 9)), (128, (1 / 9)), (262, (-1 / 3))]

def value1158 : Sparse (Fin 909) := [(13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (60, (2 / 9)), (128, (1 / 9)), (260, (-1 / 3))]

def value1159 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (59, (-1 / 3)), (259, (-1 / 3))]

def value1160 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 36)), (5, (-1 / 9)), (6, (1 / 72)), (9, (-1 / 9)), (818, (-1 / 3))]

def value1161 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 72)), (9, (-1 / 6))]

def value1162 : Sparse (Fin 909) := [(54, (-1 / 3)), (259, (-1 / 3)), (723, (-1 / 3))]

def value1163 : Sparse (Fin 909) := [(54, (-1 / 3)), (721, (-1 / 3)), (723, (-1 / 3))]

def value1164 : Sparse (Fin 909) := [(12, (1 / 9)), (13, (2 / 9)), (59, (-1 / 3)), (199, (-1 / 3))]

def value1165 : Sparse (Fin 909) := [(13, (-1 / 9)), (52, (1 / 9)), (82, (1 / 9)), (128, (2 / 9))]

def value1166 : Sparse (Fin 909) := [(3, (1 / 9)), (13, (1 / 9)), (35, (1 / 9)), (490, (-1 / 3)), (492, (-1 / 3))]

def value1167 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (-1 / 12)), (5, (-1 / 36)), (6, (-1 / 36))]

def value1168 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 48)), (2, (1 / 48)), (6, (1 / 144)), (8, (1 / 9))]

def value1169 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (13, (1 / 9)), (35, (2 / 9)), (82, (1 / 9))]

def value1170 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 36)), (5, (1 / 36)), (6, (1 / 144)), (52, (1 / 9))]

def value1171 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 144)), (5, (-1 / 12)), (6, (1 / 72)), (52, (1 / 9))]

def value1172 : Sparse (Fin 909) := [(56, (-1 / 3)), (228, (-1 / 3)), (796, (-1 / 3))]

def value1173 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (2 / 9)), (13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (201, (-1 / 3))]

def value1174 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (-1 / 144)), (6, (-1 / 144)), (35, (1 / 9))]

def value1175 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (35, (-1 / 9)), (82, (1 / 9))]

def value1176 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (2, (7 / 144)), (5, (-1 / 12)), (6, (1 / 48))]

def value1177 : Sparse (Fin 909) := [(1, (-7 / 144)), (2, (-5 / 144)), (5, (1 / 36)), (6, (1 / 72))]

def value1178 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 72)), (5, (1 / 9)), (6, (1 / 144))]

def value1179 : Sparse (Fin 909) := [(54, (-1 / 3)), (228, (-1 / 3)), (492, (-1 / 3))]

def value1180 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (199, (-1 / 3))]

def value1181 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (13 / 144)), (6, (-1 / 18))]

def value1182 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-5 / 144)), (5, (-1 / 18)), (6, (1 / 144)), (9, (-1 / 18)), (68, (1 / 12))]

def value1183 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 144)), (11, (1 / 9)), (35, (1 / 9)), (226, (-1 / 3)), (723, (-1 / 3))]

def value1184 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 144)), (35, (1 / 9)), (70, (1 / 9)), (196, (-1 / 3)), (723, (-1 / 3))]

def value1185 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 72)), (5, (-1 / 18)), (6, (1 / 48)), (26, (1 / 9)), (35, (2 / 9)), (82, (1 / 9))]

def value1186 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (8, (1 / 9)), (56, (-1 / 3)), (201, (-1 / 3))]

def value1187 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (71, (1 / 9)), (197, (-1 / 3)), (796, (-1 / 3))]

def value1188 : Sparse (Fin 909) := [(25, (-1 / 3)), (123, (-1 / 3)), (226, (-1 / 3))]

def value1189 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (35, (-1 / 9)), (52, (1 / 9))]

def value1190 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (12, (1 / 9)), (33, (-1 / 3)), (54, (-1 / 3))]

def value1191 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (12, (1 / 9))]

def value1192 : Sparse (Fin 909) := [(10, (-1 / 3)), (13, (1 / 9)), (35, (1 / 9)), (82, (1 / 9)), (306, (-1 / 3))]

def value1193 : Sparse (Fin 909) := [(3, (2 / 9)), (12, (1 / 9)), (13, (-1 / 9)), (34, (1 / 9))]

def value1194 : Sparse (Fin 909) := [(10, (-1 / 3)), (13, (1 / 9)), (35, (1 / 9)), (82, (1 / 9)), (307, (-1 / 3))]

def value1195 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 144)), (6, (1 / 144)), (27, (1 / 12)), (68, (1 / 12)), (236, (-1 / 3))]

def value1196 : Sparse (Fin 909) := [(55, (-1 / 3)), (197, (-1 / 3)), (728, (-1 / 3))]

def value1197 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (2, (1 / 16)), (5, (-1 / 36)), (6, (1 / 144))]

def value1198 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 72)), (5, (-1 / 36)), (8, (1 / 9))]

def value1199 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-5 / 72)), (5, (-1 / 36)), (6, (1 / 144))]

def value1200 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-5 / 144)), (3, (1 / 9)), (6, (1 / 144)), (11, (1 / 9)), (26, (2 / 9)), (35, (2 / 9))]

def value1201 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 72)), (2, (1 / 24)), (6, (1 / 144))]

def value1202 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-11 / 144)), (2, (-1 / 48))]

def value1203 : Sparse (Fin 909) := [(1, (5 / 72)), (2, (1 / 72))]

def value1204 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-5 / 144)), (2, (-1 / 72)), (3, (2 / 9)), (4, (1 / 9)), (26, (2 / 9)), (35, (1 / 9))]

def value1205 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 144)), (6, (1 / 144)), (27, (1 / 12)), (68, (1 / 12)), (237, (-1 / 3))]

def value1206 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36))]

def value1207 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 24)), (2, (-1 / 144)), (3, (1 / 9))]

def value1208 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (2 / 9)), (4, (2 / 9)), (26, (1 / 9)), (56, (-1 / 3))]

def value1209 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 36)), (3, (1 / 9)), (13, (1 / 9)), (51, (-1 / 3)), (52, (2 / 9))]

def value1210 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (5 / 144)), (5, (-1 / 18)), (68, (1 / 12)), (238, (-1 / 3))]

def value1211 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (-5 / 72)), (6, (1 / 144)), (26, (1 / 9))]

def value1212 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-5 / 72)), (2, (5 / 144)), (26, (1 / 9))]

def value1213 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 72)), (5, (-1 / 18)), (6, (1 / 144)), (27, (1 / 12)), (238, (-1 / 3))]

def value1214 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (1 / 9)), (26, (-1 / 9)), (35, (1 / 9))]

def value1215 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (3, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (55, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1216 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 144)), (2, (5 / 144)), (5, (-1 / 18)), (6, (1 / 144))]

def value1217 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 48)), (2, (-1 / 48)), (5, (-1 / 36)), (6, (1 / 72))]

def value1218 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 72)), (5, (-1 / 12)), (6, (1 / 48)), (9, (-1 / 36))]

def value1219 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (5 / 144)), (5, (-1 / 18)), (27, (1 / 6)), (68, (1 / 12))]

def value1220 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (-1 / 72)), (5, (-1 / 36))]

def value1221 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (13 / 144)), (2, (-1 / 18))]

def value1222 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 48)), (2, (1 / 48)), (5, (-1 / 18)), (27, (1 / 12))]

def value1223 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (25, (-1 / 3)), (26, (1 / 9)), (54, (-1 / 3))]

def value1224 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 48)), (5, (-1 / 18)), (6, (1 / 72)), (68, (1 / 12))]

def value1225 : Sparse (Fin 909) := [(1, (-1 / 18)), (2, (13 / 144)), (6, (1 / 144))]

def value1226 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (26, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (226, (-1 / 3))]

def value1227 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (5, (1 / 9)), (6, (-1 / 36)), (9, (-1 / 36))]

def value1228 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-5 / 144)), (5, (1 / 36)), (6, (-7 / 144))]

def value1229 : Sparse (Fin 909) := [(2, (1 / 144)), (5, (-1 / 36)), (6, (1 / 144)), (35, (1 / 9)), (82, (1 / 9)), (199, (-1 / 3)), (723, (-1 / 3))]

def value1230 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 72)), (52, (1 / 9)), (228, (-1 / 3)), (728, (-1 / 3))]

def value1231 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-7 / 144)), (3, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value1232 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 72)), (5, (-1 / 18)), (6, (1 / 48)), (7, (1 / 9)), (11, (1 / 9)), (35, (2 / 9))]

def value1233 : Sparse (Fin 909) := [(7, (2 / 9)), (69, (2 / 9)), (70, (2 / 9)), (256, (-1 / 3))]

def value1234 : Sparse (Fin 909) := [(3, (2 / 9)), (7, (2 / 9)), (35, (2 / 9)), (81, (-1 / 3))]

def value1235 : Sparse (Fin 909) := [(3, (2 / 9)), (12, (2 / 9)), (13, (2 / 9)), (33, (-1 / 3))]

def value1236 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (5 / 144)), (5, (-1 / 12)), (6, (1 / 144)), (8, (1 / 9)), (71, (1 / 9)), (308, (-1 / 3))]

def value1237 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (-1 / 48)), (2, (1 / 72)), (27, (1 / 12)), (30, (-1 / 3))]

def value1238 : Sparse (Fin 909) := [(3, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (201, (-1 / 3)), (726, (-1 / 3))]

def value1239 : Sparse (Fin 909) := [(3, (1 / 9)), (4, (1 / 9)), (26, (1 / 9)), (56, (-1 / 3)), (228, (-1 / 3))]

def value1240 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (8, (2 / 9)), (69, (1 / 9)), (71, (5 / 9))]

def value1241 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 144)), (2, (1 / 144))]

def value1242 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-1 / 48))]

def value1243 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 24)), (5, (-1 / 9)), (6, (1 / 144)), (7, (2 / 9)), (8, (2 / 9))]

def value1244 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (-1 / 48)), (2, (1 / 72)), (27, (1 / 12)), (31, (-1 / 3))]

def value1245 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-5 / 72)), (2, (1 / 144)), (4, (1 / 9))]

def value1246 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (5 / 144)), (4, (1 / 9))]

def value1247 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-1 / 18)), (2, (1 / 36)), (31, (-1 / 3))]

def value1248 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (51, (-2 / 3)), (52, (1 / 9))]

def value1249 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 3)), (4, (2 / 9)), (26, (1 / 3))]

def value1250 : Sparse (Fin 909) := [(3, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (55, (-2 / 3))]

def value1251 : Sparse (Fin 909) := [(11, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (228, (-2 / 3))]

def value1252 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (-1 / 144)), (5, (1 / 36))]

def value1253 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 36)), (2, (5 / 144)), (5, (-1 / 36)), (27, (1 / 6))]

def value1254 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3)), (277, (-1 / 3))]

def value1255 : Sparse (Fin 909) := [(3, (1 / 9)), (10, (-1 / 3)), (12, (1 / 9)), (13, (1 / 9)), (55, (-1 / 3))]

def value1256 : Sparse (Fin 909) := [(3, (1 / 9)), (12, (1 / 9)), (13, (1 / 9)), (51, (-1 / 3)), (127, (-1 / 3))]

def value1257 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (2 / 9)), (8, (1 / 9)), (10, (-1 / 3)), (35, (1 / 9))]

def value1258 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (69, (2 / 9)), (70, (1 / 9)), (71, (1 / 9)), (277, (-1 / 3))]

def value1259 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-1 / 12)), (2, (-1 / 144))]

def value1260 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-7 / 144)), (2, (1 / 48))]

def value1261 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 144)), (2, (1 / 24)), (5, (-1 / 36))]

def value1262 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-1 / 24)), (2, (1 / 144))]

def value1263 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-11 / 144)), (2, (1 / 36)), (27, (1 / 12))]

def value1264 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (13 / 144)), (2, (1 / 144))]

def value1265 : Sparse (Fin 909) := [(0, (1 / 240)), (2, (1 / 48))]

def value1266 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (69, (1 / 9)), (124, (-1 / 3)), (126, (-1 / 3))]

def value1267 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 144)), (2, (-1 / 18)), (5, (-1 / 36))]

def value1268 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 24)), (2, (-1 / 18))]

def value1269 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (12, (1 / 9)), (13, (1 / 3)), (54, (-1 / 3))]

def value1270 : Sparse (Fin 909) := [(3, (1 / 9)), (13, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (56, (-1 / 3))]

def value1271 : Sparse (Fin 909) := [(7, (1 / 9)), (35, (1 / 9)), (70, (1 / 9)), (125, (-1 / 3)), (197, (-1 / 3))]

def value1272 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (5 / 72)), (5, (-1 / 18)), (6, (5 / 144))]

def value1273 : Sparse (Fin 909) := [(2, (1 / 144)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (1 / 9)), (82, (1 / 9)), (128, (2 / 9)), (492, (-1 / 3))]

def value1274 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (52, (1 / 9)), (237, (-1 / 3)), (308, (-1 / 3))]

def value1275 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (5, (-1 / 18)), (6, (1 / 144)), (11, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (727, (-1 / 3))]

def value1276 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (4, (1 / 9)), (31, (-1 / 3)), (51, (-1 / 3))]

def value1277 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (2 / 9)), (4, (1 / 9)), (26, (1 / 9)), (55, (-1 / 3))]

def value1278 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (35, (1 / 9)), (52, (2 / 9)), (228, (-1 / 3))]

def value1279 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (8, (1 / 9)), (71, (1 / 9)), (126, (-1 / 3)), (236, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue8 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (-5 / 864)), (2, (-5 / 72)), (5, (25 / 72)), (6, (-5 / 72)), (7, (-5 / 9)), (9, (25 / 108)), (35, (-5 / 18)), (58, (-5 / 864)), (69, (-5 / 6)), (70, (-20 / 27)), (71, (-5 / 9)), (257, (-5 / 27))]

def singlePairValue9 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 288)), (2, (-5 / 288)), (5, (-5 / 54)), (6, (5 / 108)), (9, (-5 / 36)), (58, (5 / 432)), (69, (5 / 54)), (70, (5 / 54)), (71, (5 / 27))]

def singlePairValue10 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 288)), (2, (-35 / 864)), (3, (-5 / 27)), (5, (5 / 18)), (6, (-5 / 144)), (7, (-5 / 9)), (8, (-5 / 27)), (9, (5 / 27)), (35, (-10 / 27)), (52, (-5 / 27)), (58, (-5 / 864)), (69, (-20 / 27)), (70, (-25 / 54)), (71, (-5 / 9)), (256, (5 / 9)), (257, (-5 / 27)), (495, (-5 / 27))]

def singlePairValue11 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (25 / 864)), (2, (65 / 864)), (5, (-5 / 54)), (6, (5 / 144)), (9, (-25 / 216)), (52, (5 / 54)), (58, (5 / 432)), (69, (5 / 27)), (71, (5 / 27)), (495, (5 / 54))]

def singlePairValue12 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 96)), (2, (-5 / 288)), (5, (-5 / 72)), (7, (5 / 27)), (9, (-5 / 54)), (35, (5 / 54)), (69, (5 / 18)), (70, (5 / 18)), (71, (5 / 54)), (257, (5 / 54))]

def singlePairValue13 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 144)), (5, (5 / 54)), (6, (-5 / 108)), (9, (5 / 36)), (58, (-5 / 144))]

def singlePairValue14 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 864)), (2, (-5 / 864)), (5, (-5 / 108)), (6, (5 / 144)), (9, (-5 / 54)), (35, (5 / 27)), (58, (5 / 432)), (69, (5 / 54)), (70, (5 / 54)), (257, (5 / 27)), (495, (5 / 27))]

def singlePairValue15 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 288)), (2, (35 / 864)), (5, (-5 / 72)), (7, (5 / 54)), (8, (5 / 54)), (9, (-5 / 54)), (69, (5 / 27)), (70, (5 / 54)), (71, (5 / 18)), (256, (-5 / 18))]

def singlePairValue16 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 216)), (5, (5 / 108)), (6, (-5 / 108)), (9, (5 / 54)), (58, (-5 / 144)), (495, (-5 / 27))]

def singlePairValue17 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (9, (5 / 36)), (69, (-5 / 27)), (70, (-5 / 27)), (71, (-5 / 27))]

def singlePairValue18 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (5 / 144)), (9, (5 / 36)), (69, (-5 / 27)), (71, (-10 / 27))]

def singlePairValue19 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (9, (5 / 36)), (69, (-5 / 27)), (70, (-5 / 27)), (257, (-5 / 27))]

def singlePairValue20 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (9, (-5 / 18)), (58, (5 / 36))]

def singlePairValue21 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (25 / 864)), (2, (25 / 864)), (3, (-5 / 18)), (5, (-5 / 27)), (6, (5 / 72)), (7, (-5 / 18)), (9, (-95 / 216)), (35, (-25 / 54)), (52, (-5 / 9)), (58, (5 / 216)), (69, (-5 / 9)), (70, (-5 / 18)), (71, (-5 / 18)), (256, (5 / 6)), (257, (-5 / 27)), (495, (-5 / 18))]

def singlePairValue22 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 216)), (2, (5 / 432)), (6, (5 / 96)), (7, (-5 / 18)), (8, (-5 / 9)), (9, (-10 / 27)), (58, (5 / 216)), (69, (-5 / 9)), (70, (-5 / 27)), (71, (-10 / 9))]

def singlePairValue23 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-65 / 864)), (2, (-35 / 864)), (6, (-5 / 864)), (7, (5 / 54)), (9, (5 / 54)), (58, (-5 / 864)), (69, (5 / 27)), (70, (5 / 54)), (71, (5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue24 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 288)), (2, (-35 / 864)), (5, (5 / 216)), (6, (-5 / 288)), (9, (25 / 216)), (52, (5 / 27)), (58, (-5 / 864)), (69, (5 / 27)), (71, (5 / 54)), (256, (-5 / 18)), (495, (5 / 54))]

def singlePairValue25 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (25 / 144)), (58, (5 / 432)), (70, (-5 / 27))]

def singlePairValue26 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 216)), (2, (5 / 144)), (6, (-5 / 432)), (8, (5 / 27)), (9, (5 / 54)), (58, (-5 / 864)), (69, (5 / 54)), (71, (10 / 27))]

def singlePairValue27 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-55 / 864)), (2, (-35 / 864)), (3, (5 / 54)), (5, (5 / 72)), (6, (-5 / 288)), (7, (5 / 54)), (9, (25 / 216)), (35, (5 / 27)), (52, (5 / 54)), (58, (-5 / 864)), (69, (5 / 54)), (70, (5 / 54)), (256, (-5 / 18)), (257, (5 / 54)), (495, (5 / 54))]

def singlePairValue28 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (5, (5 / 108)), (6, (5 / 432)), (58, (5 / 432)), (71, (-5 / 27))]

def singlePairValue29 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (65 / 432)), (5, (-5 / 108)), (9, (-5 / 54)), (35, (-5 / 27)), (70, (-5 / 27)), (257, (-5 / 27))]

def singlePairValue30 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (9, (-5 / 54)), (69, (-5 / 27)), (71, (-5 / 27))]

def singlePairValue31 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (35 / 216)), (2, (5 / 216)), (5, (5 / 54)), (6, (5 / 216)), (58, (5 / 432)), (69, (-5 / 27))]

def singlePairValue32 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-25 / 432)), (6, (5 / 216)), (9, (-5 / 108)), (35, (-5 / 27)), (58, (5 / 432)), (257, (-5 / 27)), (495, (-5 / 27))]

def singlePairValue33 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (5, (-5 / 108)), (7, (-5 / 27)), (9, (-5 / 54)), (69, (-5 / 27)), (70, (-5 / 27))]

def singlePairValue34 : Sparse (Fin 909) := [(0, (7 / 216)), (2, (5 / 216)), (5, (-5 / 108)), (8, (-5 / 27)), (9, (-5 / 54)), (71, (-10 / 27))]

def singlePairValue35 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (5, (-5 / 36)), (6, (-5 / 144)), (9, (-5 / 36)), (58, (-5 / 144))]

def singlePairValue36 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (-5 / 108)), (9, (-5 / 54)), (256, (5 / 9))]

def singlePairValue37 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (6, (-5 / 144)), (58, (-5 / 144)), (495, (5 / 9))]

def singlePairValue38 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (2, (5 / 36)), (9, (5 / 36)), (70, (5 / 9))]

def singlePairValue39 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 144)), (9, (5 / 36)), (71, (5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue168 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (68, (5 / 36)), (124, (-5 / 18)), (196, (-5 / 18)), (197, (-5 / 18)), (266, (-5 / 18))]

def singlePairValue169 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (5 / 144)), (68, (5 / 36)), (125, (-5 / 18)), (126, (-5 / 18)), (197, (-5 / 18)), (268, (-5 / 18))]

def singlePairValue170 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (68, (5 / 36)), (125, (-5 / 9)), (264, (-5 / 9))]

def singlePairValue171 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-25 / 864)), (2, (25 / 864)), (3, (-5 / 18)), (5, (-5 / 54)), (6, (5 / 864)), (7, (-5 / 54)), (9, (-5 / 216)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (26, (-5 / 27)), (27, (5 / 24)), (35, (-5 / 18)), (54, (5 / 18)), (55, (5 / 9)), (68, (25 / 72)), (70, (-5 / 54)), (125, (5 / 9)), (196, (5 / 18)), (197, (5 / 9))]

def singlePairValue172 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (-5 / 864)), (2, (-5 / 288)), (3, (-5 / 27)), (5, (-5 / 54)), (6, (5 / 288)), (9, (-5 / 216)), (13, (-5 / 27)), (27, (5 / 24)), (33, (5 / 18)), (52, (-5 / 27)), (55, (5 / 9)), (64, (5 / 9)), (68, (25 / 72)), (125, (5 / 9)), (197, (5 / 18)), (260, (5 / 18)), (263, (-5 / 9))]

def singlePairValue173 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 864)), (2, (5 / 32)), (5, (5 / 108)), (9, (5 / 216)), (13, (5 / 54)), (35, (5 / 27)), (68, (-5 / 72)), (70, (5 / 54)), (196, (-5 / 18))]

def singlePairValue174 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (85 / 864)), (2, (5 / 54)), (3, (-25 / 54)), (4, (-5 / 27)), (5, (-25 / 216)), (6, (5 / 432)), (7, (-5 / 27)), (9, (-5 / 216)), (13, (-5 / 54)), (24, (5 / 9)), (26, (-5 / 27)), (27, (5 / 24)), (35, (-5 / 18)), (55, (5 / 18)), (56, (5 / 9)), (68, (25 / 72)), (70, (-5 / 54)), (125, (5 / 18)), (197, (10 / 9))]

def singlePairValue175 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-85 / 864)), (2, (-5 / 72)), (3, (5 / 54)), (5, (5 / 108)), (6, (-5 / 864)), (7, (5 / 54)), (9, (5 / 216)), (26, (5 / 54)), (35, (5 / 27)), (68, (-5 / 72)), (70, (5 / 54)), (197, (-5 / 18))]

def singlePairValue176 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-55 / 864)), (2, (-5 / 288)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 54)), (52, (5 / 54)), (64, (-5 / 18)), (68, (-5 / 72)), (125, (-5 / 18)), (260, (-5 / 18))]

def singlePairValue177 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 864)), (2, (35 / 288)), (5, (5 / 216)), (13, (5 / 54)), (27, (-5 / 72)), (35, (5 / 54)), (63, (-5 / 18)), (68, (-5 / 36)), (196, (-5 / 18)), (264, (-5 / 18))]

def singlePairValue178 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-25 / 288)), (2, (-5 / 96)), (27, (-5 / 72)), (55, (-5 / 18)), (68, (-5 / 36)), (125, (-5 / 18)), (197, (-5 / 18))]

def singlePairValue179 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (175 / 864)), (2, (5 / 108)), (3, (-5 / 9)), (5, (-5 / 36)), (6, (5 / 288)), (7, (-5 / 18)), (9, (-5 / 216)), (12, (-5 / 18)), (13, (-10 / 27)), (23, (5 / 6)), (27, (5 / 24)), (35, (-5 / 18)), (54, (5 / 6)), (68, (25 / 72)), (70, (-5 / 54)), (125, (5 / 6)), (196, (5 / 9))]

def singlePairValue180 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 36)), (2, (5 / 216)), (3, (5 / 27)), (5, (5 / 108)), (6, (-5 / 432)), (7, (5 / 27)), (9, (5 / 216)), (13, (5 / 54)), (35, (5 / 27)), (68, (-5 / 72)), (70, (5 / 54)), (125, (-5 / 18))]

def singlePairValue181 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 288)), (2, (-65 / 864)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (54, (-5 / 18)), (62, (-5 / 18)), (68, (-5 / 72)), (260, (-5 / 18)), (264, (-5 / 18))]

def singlePairValue182 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 54)), (2, (-5 / 108)), (5, (5 / 216)), (23, (-5 / 18)), (27, (-5 / 72)), (54, (-5 / 18)), (68, (-5 / 36)), (125, (-5 / 18)), (196, (-5 / 18))]

def singlePairValue183 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 432)), (2, (5 / 432)), (5, (5 / 216)), (24, (-5 / 18)), (27, (-5 / 72)), (56, (-5 / 18)), (68, (-5 / 36)), (197, (-5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue184 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 144)), (5, (5 / 216)), (27, (-5 / 72)), (68, (-5 / 36)), (263, (5 / 9))]

def singlePairValue185 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (2, (5 / 36)), (68, (5 / 36)), (196, (5 / 9))]

def singlePairValue186 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 144)), (68, (5 / 36)), (197, (5 / 9))]

def singlePairValue187 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (68, (5 / 36)), (125, (5 / 9))]

def singlePairValue188 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 144)), (2, (5 / 48)), (68, (5 / 36)), (264, (5 / 9))]

def singlePairValue189 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (65 / 864)), (2, (25 / 288)), (3, (-5 / 18)), (5, (-5 / 36)), (6, (5 / 288)), (9, (-5 / 216)), (13, (-5 / 54)), (26, (-5 / 9)), (27, (5 / 24)), (34, (-5 / 18)), (35, (-5 / 18)), (54, (5 / 6)), (65, (5 / 6)), (67, (-5 / 18)), (68, (25 / 72)), (257, (-5 / 54)), (264, (5 / 9)), (266, (5 / 6))]

def singlePairValue190 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 432)), (2, (-5 / 144)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (26, (5 / 27)), (34, (5 / 54)), (35, (5 / 27)), (67, (5 / 27)), (68, (-5 / 72)), (257, (5 / 54)), (266, (-5 / 18))]

def singlePairValue191 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 108)), (2, (35 / 864)), (3, (-10 / 27)), (5, (-5 / 36)), (6, (5 / 288)), (9, (-5 / 216)), (12, (-5 / 27)), (13, (-5 / 9)), (26, (-5 / 27)), (27, (5 / 24)), (32, (-5 / 54)), (34, (-5 / 27)), (35, (-5 / 18)), (54, (5 / 18)), (55, (5 / 9)), (60, (-5 / 27)), (61, (5 / 9)), (65, (5 / 18)), (67, (-5 / 54)), (68, (25 / 72)), (257, (-5 / 54)), (264, (5 / 18)), (266, (5 / 9)), (268, (5 / 9))]

def singlePairValue192 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 288)), (2, (-5 / 288)), (3, (5 / 54)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 54)), (26, (5 / 54)), (34, (5 / 54)), (35, (5 / 27)), (60, (5 / 54)), (67, (5 / 54)), (68, (-5 / 72)), (257, (5 / 54)), (268, (-5 / 18))]

def singlePairValue193 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-35 / 432)), (2, (-35 / 432)), (5, (5 / 216)), (27, (-5 / 72)), (54, (-5 / 18)), (65, (-5 / 18)), (68, (-5 / 36)), (264, (-5 / 18)), (266, (-5 / 18))]

def singlePairValue194 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 216)), (2, (5 / 36)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 27)), (32, (5 / 54)), (35, (5 / 27)), (60, (5 / 27)), (68, (-5 / 72)), (257, (5 / 54)), (264, (-5 / 18))]

def singlePairValue195 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 432)), (2, (-5 / 216)), (5, (5 / 216)), (27, (-5 / 72)), (55, (-5 / 18)), (61, (-5 / 18)), (68, (-5 / 36)), (266, (-5 / 18)), (268, (-5 / 18))]

def singlePairValue196 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (68, (5 / 36)), (266, (5 / 9))]

def singlePairValue197 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 432)), (68, (5 / 36)), (268, (5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue206 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 216)), (2, (-5 / 144)), (3, (-5 / 54)), (5, (5 / 216)), (6, (-35 / 864)), (7, (-5 / 54)), (9, (-5 / 216)), (26, (-5 / 27)), (35, (-5 / 18)), (58, (5 / 864)), (68, (5 / 72)), (70, (-5 / 54)), (71, (-5 / 54)), (197, (5 / 18))]

def singlePairValue207 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 54)), (6, (-25 / 432)), (7, (-5 / 27)), (9, (-5 / 216)), (13, (-25 / 54)), (35, (-10 / 27)), (52, (-10 / 27)), (58, (5 / 864)), (68, (5 / 72)), (69, (-5 / 54)), (70, (-5 / 54)), (125, (5 / 18))]

def singlePairValue208 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 144)), (2, (-5 / 864)), (3, (-10 / 27)), (5, (-5 / 54)), (6, (-5 / 216)), (9, (-5 / 108)), (12, (-5 / 27)), (13, (-65 / 54)), (32, (-5 / 18)), (35, (-25 / 54)), (52, (-10 / 27)), (54, (5 / 18)), (58, (5 / 864)), (60, (-25 / 54)), (62, (5 / 9)), (68, (5 / 72)), (128, (-5 / 27)), (257, (-5 / 54)), (260, (5 / 18)), (264, (5 / 18)), (495, (-5 / 54))]

def singlePairValue209 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 48)), (2, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 72)), (6, (5 / 432)), (7, (-5 / 18)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-10 / 27)), (23, (5 / 18)), (27, (5 / 72)), (35, (-10 / 27)), (52, (-5 / 27)), (54, (5 / 9)), (68, (5 / 36)), (69, (-5 / 54)), (70, (-5 / 54)), (125, (5 / 18)), (196, (5 / 18))]

def singlePairValue210 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (5 / 108)), (2, (5 / 216)), (5, (35 / 216)), (8, (-5 / 18)), (9, (-5 / 108)), (24, (5 / 18)), (27, (5 / 72)), (56, (5 / 9)), (68, (5 / 36)), (71, (-5 / 27)), (197, (5 / 9))]

def singlePairValue211 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-65 / 864)), (2, (-25 / 864)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 54)), (52, (5 / 27)), (68, (-5 / 72)), (69, (5 / 54)), (125, (-5 / 18))]

def singlePairValue212 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 864)), (2, (5 / 96)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 72)), (6, (-25 / 864)), (9, (-5 / 108)), (13, (-5 / 18)), (26, (-5 / 18)), (34, (-5 / 27)), (35, (-10 / 27)), (52, (-5 / 18)), (56, (5 / 18)), (58, (5 / 864)), (60, (-5 / 27)), (67, (-5 / 54)), (68, (5 / 72)), (128, (-5 / 54)), (257, (-5 / 54)), (262, (5 / 18)), (268, (5 / 18)), (495, (-5 / 54))]

def singlePairValue213 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 864)), (2, (25 / 864)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 216)), (6, (5 / 216)), (9, (-5 / 108)), (12, (-5 / 27)), (13, (-10 / 27)), (26, (-5 / 54)), (27, (5 / 72)), (35, (-5 / 27)), (51, (5 / 9)), (54, (5 / 9)), (55, (5 / 18)), (56, (5 / 9)), (59, (5 / 18)), (61, (5 / 9)), (68, (5 / 36)), (259, (5 / 18)), (262, (5 / 18)), (266, (5 / 18)), (268, (5 / 18))]

def singlePairValue214 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 108)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (26, (5 / 54)), (35, (5 / 54)), (54, (-5 / 18)), (68, (-5 / 72)), (259, (-5 / 18)), (266, (-5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue218 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 432)), (3, (-10 / 27)), (5, (5 / 108)), (12, (-5 / 54)), (13, (-40 / 27)), (32, (-10 / 27)), (35, (-10 / 27)), (52, (-10 / 27)), (60, (-10 / 27)), (62, (5 / 9)), (128, (-5 / 54))]

def singlePairValue220 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (-25 / 432)), (2, (-5 / 72)), (3, (-5 / 27)), (5, (5 / 54)), (6, (-5 / 216)), (7, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 27)), (35, (-5 / 27)), (54, (5 / 18))]

def singlePairValue221 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (85 / 864)), (2, (35 / 864)), (3, (-5 / 18)), (4, (-5 / 54)), (5, (25 / 216)), (6, (-5 / 288)), (8, (-5 / 54)), (13, (-5 / 27)), (26, (-5 / 54)), (35, (-5 / 54)), (52, (-5 / 54)), (56, (5 / 18))]

def singlePairValue222 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 108)), (2, (-25 / 432)), (5, (-5 / 216)), (6, (5 / 216)), (26, (5 / 54)), (35, (5 / 54))]

def singlePairValue223 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (65 / 864)), (2, (5 / 432)), (3, (-20 / 27)), (5, (5 / 72)), (6, (-5 / 432)), (7, (-5 / 54)), (12, (-10 / 27)), (13, (-5 / 6)), (35, (-5 / 18)), (52, (-5 / 27)), (54, (5 / 18))]

def singlePairValue224 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (35 / 864)), (2, (5 / 864)), (3, (5 / 54)), (5, (-5 / 216)), (6, (5 / 288)), (13, (5 / 27)), (35, (5 / 54)), (52, (5 / 54))]

def singlePairValue225 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 216)), (2, (-5 / 216)), (3, (5 / 54)), (6, (5 / 432)), (13, (5 / 18)), (32, (5 / 54)), (35, (5 / 54)), (52, (5 / 54)), (60, (5 / 54)), (62, (-5 / 18))]

def singlePairValue226 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-55 / 864)), (2, (-25 / 864)), (3, (5 / 54)), (5, (-5 / 72)), (7, (5 / 54)), (13, (5 / 54)), (35, (5 / 54)), (54, (-5 / 18))]

def singlePairValue227 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (35 / 432)), (2, (5 / 108)), (5, (-5 / 54)), (8, (5 / 54)), (56, (-5 / 18))]

def singlePairValue228 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (-5 / 54)), (6, (5 / 432)), (12, (5 / 54)), (13, (5 / 9)), (32, (5 / 27)), (60, (5 / 27)), (128, (5 / 54))]

def singlePairValue229 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (5 / 432)), (3, (5 / 54)), (5, (-5 / 108)), (12, (5 / 54)), (13, (5 / 18)), (59, (-5 / 18)), (61, (-5 / 18))]

def singlePairValue231 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 864)), (2, (25 / 864)), (5, (-5 / 108)), (6, (-5 / 864)), (54, (-5 / 18)), (56, (-5 / 18)), (228, (-5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue232 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (-35 / 288)), (2, (-25 / 216)), (3, (-10 / 27)), (5, (-5 / 216)), (6, (5 / 432)), (12, (-5 / 54)), (13, (-10 / 27)), (35, (-5 / 54)), (52, (-5 / 27))]

def singlePairValue233 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (5 / 432)), (2, (185 / 864)), (5, (5 / 216)), (13, (5 / 54)), (35, (5 / 54))]

def singlePairValue234 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 288)), (2, (-5 / 144)), (3, (5 / 54)), (6, (-5 / 864)), (13, (5 / 54)), (52, (5 / 54))]

def singlePairValue235 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 108)), (2, (-5 / 288)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 54)), (13, (5 / 18)), (35, (5 / 54)), (52, (5 / 54))]

def singlePairValue236 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-35 / 432)), (6, (5 / 432)), (13, (-5 / 27)), (52, (-5 / 27))]

def singlePairValue237 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (2, (85 / 432)), (5, (-5 / 108)), (13, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue238 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (35 / 864)), (2, (5 / 288)), (3, (-20 / 27)), (4, (-5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (12, (-10 / 27)), (13, (-25 / 27)), (26, (-5 / 54)), (32, (-5 / 54)), (33, (5 / 18)), (34, (-5 / 54)), (35, (-5 / 27)), (51, (5 / 18)), (52, (-5 / 54)), (54, (5 / 9)), (56, (5 / 18)), (60, (-5 / 54)), (61, (5 / 18)), (62, (5 / 18))]

def singlePairValue239 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (35 / 864)), (2, (5 / 864)), (3, (5 / 27)), (6, (5 / 432)), (13, (5 / 27)), (26, (5 / 54)), (34, (5 / 54)), (35, (5 / 27)), (52, (5 / 54)), (60, (5 / 54))]

def singlePairValue240 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 144)), (2, (25 / 432)), (5, (-5 / 108)), (51, (-5 / 18)), (54, (-5 / 18)), (56, (-5 / 18)), (61, (-5 / 18))]

def singlePairValue242 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-65 / 864)), (2, (-85 / 864)), (3, (-5 / 9)), (5, (-5 / 72)), (6, (5 / 288)), (13, (-5 / 18)), (26, (-5 / 18)), (33, (5 / 6)), (35, (-5 / 54)), (54, (5 / 6)), (62, (5 / 9))]

def singlePairValue243 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (5 / 288)), (2, (5 / 288)), (3, (-5 / 6)), (4, (-10 / 27)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 27)), (13, (-25 / 54)), (26, (-10 / 27)), (35, (-5 / 18)), (54, (5 / 18)), (56, (5 / 9))]

def singlePairValue244 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 48)), (2, (-5 / 72)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (26, (5 / 27)), (35, (5 / 54)), (54, (-5 / 18))]

def singlePairValue245 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (5 / 432)), (2, (25 / 864)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 54)), (26, (5 / 54)), (35, (5 / 54)), (56, (-5 / 18))]

def singlePairValue246 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-5 / 144)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 54)), (33, (-5 / 18)), (54, (-5 / 18)), (62, (-5 / 18))]

def singlePairValue247 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 216)), (6, (5 / 432)), (26, (-5 / 27)), (35, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue248 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (145 / 864)), (2, (5 / 144)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 27)), (13, (5 / 18)), (35, (5 / 54)), (54, (-5 / 18))]

def singlePairValue249 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 27)), (3, (-5 / 27)), (6, (5 / 432)), (13, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue250 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (-5 / 54)), (6, (5 / 432)), (62, (5 / 9))]

def singlePairValue251 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (55 / 432)), (2, (-5 / 432)), (5, (-5 / 108)), (54, (5 / 9))]

def singlePairValue252 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (5 / 216)), (2, (5 / 108)), (5, (-5 / 108)), (56, (5 / 9))]

def singlePairValue253 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-5 / 48)), (2, (-25 / 288)), (3, (-5 / 6)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 18)), (13, (-35 / 27)), (26, (-5 / 18)), (32, (-5 / 27)), (34, (-5 / 9)), (60, (-5 / 18)), (61, (5 / 6))]

def singlePairValue254 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (5 / 216)), (2, (5 / 432)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 27)), (26, (5 / 54)), (34, (5 / 27)), (60, (5 / 54)), (61, (-5 / 18))]

def singlePairValue255 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (-5 / 54)), (6, (5 / 432)), (13, (-5 / 27)), (34, (-5 / 27)), (60, (-5 / 27))]

def singlePairValue256 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 108)), (2, (-5 / 108)), (5, (-5 / 108)), (61, (5 / 9))]

def singlePairValue257 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (5 / 96)), (2, (-5 / 72)), (3, (-5 / 6)), (12, (-5 / 9)), (13, (-85 / 54)), (32, (-5 / 27))]

def singlePairValue258 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 48)), (2, (25 / 144)), (13, (5 / 9)), (32, (5 / 27))]

def singlePairValue259 : Sparse (Fin 909) := [(0, (13 / 432)), (1, (115 / 432)), (2, (5 / 54)), (3, (-10 / 27)), (12, (-5 / 54)), (13, (-10 / 27))]

def singlePairValue260 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (-5 / 864)), (2, (-5 / 216)), (3, (5 / 54)), (13, (5 / 54))]

def singlePairValue261 : Sparse (Fin 909) := [(0, (13 / 432)), (1, (-25 / 864)), (2, (5 / 864)), (3, (5 / 27)), (12, (5 / 54)), (13, (5 / 18))]

def singlePairValue262 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 144)), (2, (25 / 144)), (13, (-5 / 27))]

def singlePairValue263 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-35 / 432)), (2, (-5 / 108)), (3, (5 / 27)), (12, (5 / 27)), (13, (5 / 9)), (32, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue264 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (5 / 72)), (13, (-10 / 27)), (32, (-5 / 27))]

def singlePairValue268 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-55 / 432)), (2, (-5 / 54)), (3, (-5 / 27)), (13, (-5 / 27))]

def singlePairValue269 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 72)), (2, (-5 / 72)), (12, (-5 / 27)), (13, (-10 / 27))]

def singlePairValue270 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (5 / 48)), (13, (5 / 9))]

def singlePairValue271 : Sparse (Fin 909) := [(0, (1 / 36)), (2, (5 / 12)), (32, (5 / 9))]

def singlePairValue273 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-25 / 864)), (2, (5 / 216)), (6, (-5 / 864)), (8, (5 / 54)), (9, (5 / 216)), (68, (-5 / 72)), (71, (5 / 54)), (236, (-5 / 18))]

def singlePairValue274 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (35 / 864)), (2, (5 / 216)), (6, (-5 / 432)), (8, (5 / 27)), (9, (5 / 216)), (68, (-5 / 72)), (71, (5 / 54)), (126, (-5 / 18))]

def singlePairValue275 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-25 / 288)), (2, (5 / 864)), (3, (5 / 54)), (5, (5 / 216)), (7, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (126, (-5 / 18)), (197, (-5 / 18))]

def singlePairValue277 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-25 / 432)), (2, (5 / 432)), (68, (5 / 36)), (126, (5 / 9))]

def singlePairValue278 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 432)), (2, (-5 / 864)), (3, (-5 / 27)), (5, (5 / 216)), (7, (-5 / 27)), (23, (5 / 9)), (24, (5 / 18)), (27, (-5 / 36)), (51, (5 / 18)), (54, (5 / 18)), (55, (5 / 18)), (64, (5 / 18)), (68, (-5 / 36)), (124, (5 / 9)), (125, (5 / 6)), (126, (5 / 9)), (196, (5 / 18)), (197, (5 / 18)), (266, (5 / 18))]

def singlePairValue279 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (2, (5 / 216)), (68, (5 / 36)), (125, (-5 / 9)), (126, (-5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue280 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (5 / 144)), (2, (5 / 72)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 36)), (6, (5 / 288)), (7, (-5 / 54)), (9, (-5 / 216)), (12, (-5 / 54)), (23, (5 / 18)), (25, (5 / 18)), (26, (-5 / 27)), (27, (5 / 24)), (35, (-5 / 54)), (51, (5 / 18)), (54, (5 / 18)), (55, (5 / 18)), (64, (5 / 18)), (68, (25 / 72)), (123, (5 / 18)), (124, (5 / 18)), (125, (5 / 18)), (259, (5 / 18)), (266, (5 / 18)), (487, (-5 / 9))]

def singlePairValue281 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-55 / 864)), (2, (5 / 288)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (51, (-5 / 18)), (68, (-5 / 72)), (123, (-5 / 18)), (124, (-5 / 18)), (259, (-5 / 18))]

def singlePairValue282 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 432)), (2, (5 / 432)), (5, (5 / 216)), (27, (-5 / 72)), (68, (-5 / 36)), (487, (5 / 9))]

def singlePairValue283 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (55 / 864)), (2, (-25 / 432)), (3, (-5 / 18)), (4, (-5 / 54)), (5, (-5 / 72)), (6, (5 / 288)), (7, (-5 / 27)), (8, (-5 / 27)), (9, (-5 / 216)), (24, (5 / 9)), (27, (5 / 36)), (51, (5 / 18)), (52, (-5 / 54)), (68, (25 / 72)), (69, (-5 / 54)), (124, (5 / 18)), (126, (10 / 9))]

def singlePairValue284 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (95 / 864)), (2, (-5 / 288)), (3, (5 / 54)), (6, (-5 / 432)), (7, (5 / 27)), (9, (5 / 216)), (68, (-5 / 72)), (69, (5 / 54)), (124, (-5 / 18))]

def singlePairValue285 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-25 / 432)), (2, (35 / 864)), (3, (5 / 54)), (6, (-5 / 432)), (7, (5 / 54)), (9, (5 / 216)), (52, (5 / 54)), (68, (-5 / 72)), (69, (5 / 54)), (126, (-5 / 18))]

def singlePairValue286 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (25 / 288)), (2, (5 / 864)), (3, (5 / 54)), (5, (5 / 216)), (7, (5 / 54)), (23, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (124, (-5 / 18)), (125, (-5 / 18))]

def singlePairValue287 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (126, (-5 / 9))]

def singlePairValue288 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 144)), (5, (5 / 216)), (27, (-5 / 72)), (55, (-5 / 18)), (64, (-5 / 18)), (68, (-5 / 36)), (125, (-5 / 18)), (266, (-5 / 18))]

def singlePairValue289 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-35 / 432)), (2, (5 / 864)), (5, (5 / 216)), (51, (-5 / 18)), (68, (-5 / 36)), (124, (-5 / 18)), (126, (-5 / 18))]

def singlePairValue290 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (25 / 216)), (2, (5 / 432)), (68, (5 / 36)), (124, (5 / 9))]

def singlePairValue291 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 108)), (2, (5 / 216)), (5, (5 / 108)), (6, (-5 / 108)), (8, (-5 / 27)), (9, (-5 / 216)), (58, (5 / 864)), (68, (5 / 72)), (71, (-5 / 27)), (236, (5 / 18))]

def singlePairValue292 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (-5 / 108)), (2, (-65 / 864)), (3, (-10 / 27)), (6, (-25 / 864)), (7, (-5 / 54)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-10 / 27)), (35, (-5 / 27)), (51, (5 / 18)), (52, (-10 / 27)), (58, (5 / 864)), (68, (5 / 72)), (69, (-5 / 54)), (126, (5 / 18)), (128, (-5 / 54)), (262, (5 / 18)), (495, (-5 / 54))]

def singlePairValue293 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-55 / 864)), (2, (-25 / 432)), (3, (-5 / 27)), (5, (5 / 54)), (6, (5 / 288)), (7, (-5 / 27)), (8, (-5 / 27)), (9, (-5 / 108)), (52, (-5 / 54)), (68, (5 / 36)), (69, (-5 / 54)), (71, (-5 / 54)), (126, (5 / 18)), (236, (5 / 18))]

def singlePairValue294 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 288)), (2, (-5 / 108)), (3, (-5 / 27)), (6, (-35 / 864)), (7, (-5 / 54)), (8, (-5 / 27)), (9, (-5 / 216)), (52, (-5 / 27)), (58, (5 / 864)), (68, (5 / 72)), (69, (-5 / 54)), (71, (-5 / 54)), (126, (5 / 18))]

def singlePairValue295 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 216)), (2, (-5 / 144)), (3, (-25 / 54)), (4, (-5 / 54)), (5, (5 / 108)), (6, (5 / 288)), (7, (-5 / 18)), (9, (-5 / 108)), (24, (5 / 18)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 18)), (52, (-5 / 54)), (68, (5 / 36)), (69, (-5 / 54)), (70, (-5 / 54)), (126, (5 / 18)), (197, (5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue296 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (-5 / 216)), (2, (-25 / 288)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (5 / 216)), (6, (5 / 216)), (7, (-5 / 27)), (8, (-5 / 54)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 54)), (27, (5 / 72)), (33, (5 / 18)), (35, (-5 / 27)), (51, (5 / 18)), (52, (-5 / 27)), (59, (5 / 18)), (68, (5 / 36)), (81, (5 / 18)), (256, (5 / 18)), (486, (-5 / 9))]

def singlePairValue297 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 432)), (2, (-5 / 144)), (3, (-25 / 54)), (6, (5 / 216)), (7, (-5 / 18)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (25, (5 / 18)), (26, (-5 / 54)), (27, (5 / 72)), (35, (-5 / 54)), (51, (5 / 9)), (52, (-5 / 54)), (54, (5 / 9)), (64, (5 / 9)), (68, (5 / 36)), (123, (5 / 18)), (124, (5 / 18)), (125, (5 / 18)), (259, (5 / 18)), (260, (5 / 18))]

def singlePairValue298 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 432)), (2, (-35 / 864)), (3, (-5 / 27)), (5, (-5 / 216)), (6, (5 / 216)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (31, (5 / 18)), (33, (5 / 18)), (51, (5 / 9)), (52, (-5 / 54)), (59, (5 / 18)), (68, (5 / 36)), (123, (5 / 18)), (124, (5 / 18)), (126, (5 / 18)), (259, (5 / 18)), (262, (5 / 18))]

def singlePairValue299 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 48)), (2, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 27)), (6, (-5 / 216)), (12, (-5 / 54)), (13, (-10 / 27)), (52, (-10 / 27)), (128, (-5 / 54))]

def singlePairValue300 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (65 / 864)), (2, (-65 / 432)), (3, (-5 / 9)), (5, (5 / 54)), (7, (-10 / 27)), (8, (-10 / 27)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 54)), (33, (5 / 18)), (35, (-5 / 54)), (51, (5 / 9)), (59, (5 / 18))]

def singlePairValue301 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 864)), (2, (5 / 54)), (3, (-10 / 27)), (5, (25 / 216)), (6, (-5 / 216)), (7, (-5 / 27)), (26, (-5 / 27)), (35, (-5 / 54))]

def singlePairValue302 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (5 / 48)), (2, (-35 / 432)), (3, (-5 / 27)), (5, (5 / 36)), (6, (-5 / 288)), (8, (-5 / 27)), (52, (-5 / 54))]

def singlePairValue303 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 216)), (2, (-5 / 144)), (5, (-5 / 108)), (6, (5 / 216))]

def singlePairValue304 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (5 / 144)), (2, (-5 / 96)), (3, (-5 / 18)), (4, (-5 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (26, (-5 / 27)), (35, (-5 / 27)), (52, (-5 / 27))]

def singlePairValue305 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (-5 / 288)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 288)), (52, (5 / 54))]

def singlePairValue306 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 72)), (2, (55 / 864)), (3, (5 / 18)), (5, (-5 / 72)), (7, (5 / 27)), (26, (5 / 54)), (35, (5 / 54))]

def singlePairValue307 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (25 / 216)), (2, (5 / 72)), (5, (-5 / 54)), (8, (5 / 27))]

def singlePairValue308 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 432)), (2, (5 / 216)), (3, (5 / 27)), (6, (5 / 432)), (12, (5 / 54)), (13, (10 / 27)), (52, (5 / 27)), (128, (5 / 54))]

def singlePairValue309 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 216)), (2, (5 / 108)), (3, (5 / 54)), (5, (-5 / 108)), (12, (5 / 54)), (13, (5 / 54)), (33, (-5 / 18)), (51, (-5 / 18)), (59, (-5 / 18))]

def singlePairValue310 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-25 / 288)), (2, (-5 / 54)), (3, (-10 / 27)), (4, (-5 / 27)), (5, (-5 / 216)), (6, (5 / 432)), (26, (-5 / 27)), (35, (-5 / 54)), (52, (-5 / 27))]

def singlePairValue311 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-55 / 864)), (2, (-65 / 864)), (3, (5 / 54)), (5, (5 / 216)), (26, (5 / 27)), (35, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue312 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (5 / 432)), (2, (35 / 432)), (3, (5 / 27)), (6, (-5 / 864)), (52, (5 / 54))]

def singlePairValue313 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-5 / 108)), (2, (-5 / 432)), (3, (5 / 18)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 54)), (13, (5 / 18)), (26, (5 / 54)), (34, (5 / 27)), (35, (5 / 54)), (60, (5 / 54))]

def singlePairValue314 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 96)), (2, (5 / 144)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (26, (5 / 54)), (35, (5 / 54)), (52, (5 / 54))]

def singlePairValue315 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 72)), (2, (-5 / 144)), (3, (-5 / 27)), (6, (5 / 432)), (52, (-5 / 27))]

def singlePairValue316 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 108)), (2, (-5 / 432)), (3, (-5 / 27)), (5, (-5 / 108)), (26, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue317 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (35 / 288)), (2, (-5 / 288)), (3, (-5 / 54)), (5, (5 / 216)), (6, (5 / 216)), (7, (-5 / 54)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (27, (5 / 72)), (35, (-5 / 27)), (68, (5 / 36)), (69, (-5 / 54)), (70, (-5 / 54)), (124, (5 / 18)), (125, (5 / 18))]

def singlePairValue318 : Sparse (Fin 909) := [(0, (23 / 864)), (2, (-145 / 864)), (3, (-5 / 18)), (5, (5 / 36)), (6, (5 / 216)), (7, (-10 / 27)), (8, (-10 / 27)), (9, (-5 / 108)), (51, (5 / 9)), (68, (5 / 36)), (69, (-5 / 54)), (71, (-5 / 54)), (124, (5 / 18)), (126, (5 / 18))]

def singlePairValue319 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (35 / 432)), (2, (-5 / 108)), (3, (-10 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (13, (-10 / 27)), (35, (-5 / 27)), (52, (-10 / 27))]

def singlePairValue320 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 144)), (2, (5 / 216)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (25 / 216)), (6, (-5 / 288)), (7, (-5 / 27)), (8, (-5 / 54)), (26, (-5 / 27)), (35, (-5 / 54))]

def singlePairValue321 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (85 / 432)), (2, (-25 / 432)), (3, (-5 / 27)), (5, (5 / 36)), (6, (-5 / 288)), (7, (-5 / 54)), (8, (-5 / 27))]

def singlePairValue322 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (65 / 864)), (2, (-25 / 432)), (3, (-35 / 54)), (4, (-5 / 27)), (5, (5 / 108)), (6, (-5 / 864)), (7, (-5 / 27)), (12, (-5 / 27)), (13, (-25 / 54)), (26, (-10 / 27)), (34, (-5 / 27)), (35, (-10 / 27)), (52, (-5 / 27)), (67, (-5 / 54))]

def singlePairValue323 : Sparse (Fin 909) := [(0, (13 / 864)), (1, (65 / 864)), (2, (5 / 216)), (3, (5 / 27)), (5, (-5 / 216)), (6, (5 / 432)), (13, (5 / 27)), (35, (5 / 54)), (52, (5 / 27))]

def singlePairValue324 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 432)), (2, (-5 / 144)), (3, (5 / 27)), (5, (-5 / 108)), (7, (5 / 54)), (13, (5 / 54)), (26, (5 / 27)), (34, (5 / 54)), (35, (5 / 27)), (67, (5 / 54))]

def singlePairValue325 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (5 / 432)), (2, (55 / 864)), (3, (5 / 54)), (5, (-5 / 54)), (7, (5 / 54)), (8, (5 / 54))]

def singlePairValue326 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (35 / 432)), (2, (-65 / 864)), (3, (-10 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (8, (-5 / 54)), (12, (-5 / 27)), (13, (-5 / 27)), (35, (-5 / 54)), (51, (5 / 18)), (52, (-5 / 54))]

def singlePairValue327 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (35 / 288)), (3, (-55 / 54)), (4, (-5 / 27)), (5, (5 / 108)), (6, (-5 / 432)), (7, (-5 / 54)), (13, (-10 / 27)), (26, (-20 / 27)), (34, (-25 / 54)), (35, (-5 / 18)), (52, (-5 / 54)), (64, (5 / 18)), (67, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue40 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (9, (5 / 36)), (69, (5 / 9))]

def singlePairValue41 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 144)), (2, (5 / 48)), (9, (5 / 36)), (257, (5 / 9))]

def singlePairValue42 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (2, (5 / 36)), (9, (5 / 9)), (58, (5 / 36))]

def singlePairValue43 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (35 / 432)), (2, (5 / 27)), (5, (-5 / 36)), (6, (5 / 72)), (7, (-5 / 27)), (35, (-10 / 27)), (82, (-5 / 27)), (199, (5 / 18))]

def singlePairValue44 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (-5 / 48)), (2, (-55 / 432)), (3, (-5 / 54)), (5, (5 / 36)), (6, (-5 / 144)), (8, (-5 / 54)), (13, (-5 / 54)), (35, (-5 / 54)), (52, (-10 / 27)), (82, (-5 / 54)), (128, (-5 / 27)), (201, (5 / 18))]

def singlePairValue45 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (35 / 864)), (2, (-5 / 108)), (5, (-25 / 216)), (6, (-5 / 96)), (35, (5 / 54)), (82, (5 / 54))]

def singlePairValue47 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 432)), (2, (5 / 108)), (5, (5 / 54)), (6, (5 / 216)), (7, (5 / 54)), (35, (5 / 27)), (82, (5 / 54)), (199, (-5 / 18))]

def singlePairValue48 : Sparse (Fin 909) := [(0, (13 / 288)), (2, (-5 / 432)), (5, (55 / 216)), (6, (-5 / 864)), (8, (5 / 54)), (201, (-5 / 18))]

def singlePairValue49 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (6, (25 / 144)), (82, (-5 / 27))]

def singlePairValue50 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 72)), (2, (5 / 48)), (5, (-5 / 36)), (6, (5 / 108)), (52, (5 / 27)), (128, (5 / 54))]

def singlePairValue51 : Sparse (Fin 909) := [(0, (5 / 144)), (2, (5 / 72)), (3, (5 / 54)), (5, (-5 / 36)), (6, (5 / 144)), (13, (5 / 54)), (35, (5 / 54)), (52, (5 / 54)), (82, (5 / 54)), (128, (5 / 54)), (201, (-5 / 18))]

def singlePairValue53 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (-5 / 108)), (5, (5 / 27)), (6, (-5 / 108)), (35, (-5 / 27)), (82, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue328 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 288)), (2, (55 / 864)), (3, (5 / 27)), (5, (-5 / 108)), (7, (5 / 54)), (26, (5 / 27)), (34, (5 / 54)), (35, (5 / 54)), (64, (-5 / 18)), (67, (5 / 54))]

def singlePairValue329 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (25 / 864)), (2, (5 / 108)), (3, (5 / 54)), (5, (-5 / 72)), (7, (5 / 54)), (8, (5 / 54)), (51, (-5 / 18))]

def singlePairValue330 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-5 / 864)), (2, (-55 / 864)), (3, (-5 / 6)), (4, (-5 / 18)), (5, (-5 / 72)), (6, (5 / 288)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-25 / 54)), (33, (5 / 18)), (34, (-5 / 27)), (35, (-5 / 27)), (67, (-5 / 54)), (81, (5 / 18))]

def singlePairValue331 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (25 / 216)), (2, (-25 / 216)), (3, (-10 / 9)), (4, (-5 / 9)), (5, (-5 / 108)), (6, (5 / 288)), (7, (-5 / 18)), (26, (-5 / 9)), (35, (-5 / 27))]

def singlePairValue332 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 54)), (2, (5 / 288)), (3, (5 / 18)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (7, (5 / 54)), (26, (5 / 27)), (35, (5 / 54))]

def singlePairValue333 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (5 / 108)), (2, (25 / 864)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (26, (5 / 54)), (33, (-5 / 18)), (81, (-5 / 18))]

def singlePairValue334 : Sparse (Fin 909) := [(0, (49 / 864)), (1, (-35 / 432)), (2, (-55 / 432)), (3, (-5 / 27)), (6, (5 / 288)), (7, (-5 / 54)), (8, (-5 / 27))]

def singlePairValue335 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (95 / 432)), (2, (-5 / 864)), (3, (5 / 54)), (6, (-5 / 864)), (7, (5 / 54))]

def singlePairValue336 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (-5 / 216)), (2, (5 / 144)), (6, (-5 / 864)), (8, (5 / 54))]

def singlePairValue337 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (65 / 432)), (2, (5 / 864)), (5, (5 / 216)), (6, (-5 / 864)), (7, (5 / 54)), (12, (5 / 54)), (13, (5 / 54)), (35, (5 / 54))]

def singlePairValue338 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (25 / 108)), (5, (5 / 108)), (6, (5 / 432))]

def singlePairValue339 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-35 / 432)), (2, (25 / 432)), (3, (5 / 27)), (6, (-5 / 864)), (7, (5 / 54))]

def singlePairValue340 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 216)), (2, (5 / 108)), (3, (5 / 18)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 54)), (26, (5 / 18)), (34, (5 / 27)), (35, (5 / 54)), (67, (5 / 54))]

def singlePairValue341 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-25 / 216)), (2, (-5 / 72)), (5, (5 / 108)), (6, (5 / 432))]

def singlePairValue342 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 216)), (2, (5 / 432)), (5, (-5 / 108)), (26, (-5 / 27)), (34, (-5 / 27)), (67, (-5 / 27))]

def singlePairValue343 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (35 / 216)), (2, (5 / 432)), (3, (-5 / 27)), (5, (-5 / 108)), (7, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue344 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-5 / 108)), (5, (-5 / 108)), (8, (-5 / 27))]

def singlePairValue345 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 96)), (2, (-95 / 864)), (3, (-25 / 27)), (5, (5 / 108)), (6, (-5 / 864)), (7, (-5 / 54)), (12, (-10 / 27)), (13, (-35 / 54)), (34, (-5 / 54)), (35, (-5 / 54)), (51, (5 / 9)), (52, (-5 / 18)), (54, (5 / 18)), (64, (5 / 18))]

def singlePairValue346 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-35 / 864)), (2, (5 / 96)), (3, (5 / 54)), (5, (-5 / 108)), (7, (5 / 54)), (51, (-5 / 18)), (54, (-5 / 18)), (64, (-5 / 18))]

def singlePairValue347 : Sparse (Fin 909) := [(0, (7 / 288)), (2, (-5 / 54)), (3, (-35 / 54)), (4, (-5 / 27)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 27)), (13, (-5 / 27)), (25, (5 / 18)), (26, (-5 / 27)), (31, (5 / 9)), (33, (5 / 9)), (34, (-5 / 54)), (51, (5 / 9)), (52, (-5 / 54)), (64, (5 / 18)), (123, (5 / 9))]

def singlePairValue348 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 96)), (2, (35 / 864)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (25, (-5 / 18)), (26, (5 / 54)), (64, (-5 / 18)), (123, (-5 / 18))]

def singlePairValue349 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 216)), (2, (5 / 432)), (5, (5 / 216)), (6, (-5 / 864)), (31, (-5 / 18)), (33, (-5 / 18)), (51, (-5 / 18)), (123, (-5 / 18))]

def singlePairValue350 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 144)), (6, (5 / 432)), (123, (5 / 9))]

def singlePairValue351 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (5 / 144)), (2, (-25 / 144)), (3, (-5 / 6)), (4, (-5 / 18)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 18)), (13, (-5 / 27)), (51, (5 / 6)), (52, (-5 / 18))]

def singlePairValue352 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (25 / 864)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (51, (-5 / 18)), (52, (5 / 54))]

def singlePairValue353 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-25 / 432)), (2, (5 / 108)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 54)), (13, (5 / 54)), (51, (-5 / 18)), (52, (5 / 54))]

def singlePairValue354 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 144)), (5, (-5 / 108)), (64, (5 / 9))]

def singlePairValue355 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 144)), (2, (5 / 144)), (5, (-5 / 108)), (51, (5 / 9))]

def singlePairValue356 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (-25 / 864)), (2, (25 / 432)), (3, (-5 / 27)), (5, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 9)), (25, (5 / 18)), (26, (-5 / 54)), (27, (5 / 36)), (33, (5 / 18)), (35, (-5 / 54)), (54, (5 / 9)), (55, (5 / 9)), (63, (5 / 9)), (64, (5 / 18)), (65, (5 / 9)), (68, (5 / 18)), (125, (5 / 18)), (196, (5 / 18)), (264, (5 / 18)), (266, (5 / 18))]

def singlePairValue357 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 96)), (2, (-25 / 864)), (3, (-20 / 27)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 18)), (13, (-5 / 9)), (23, (5 / 18)), (26, (-10 / 27)), (27, (-5 / 72)), (34, (-5 / 27)), (35, (-5 / 18)), (55, (5 / 9)), (63, (5 / 18)), (65, (5 / 18)), (67, (-5 / 54))]

def singlePairValue358 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-35 / 432)), (2, (5 / 864)), (3, (-5 / 9)), (5, (-5 / 72)), (12, (-5 / 27)), (13, (-5 / 18)), (25, (5 / 18)), (26, (-5 / 54)), (27, (5 / 24)), (33, (5 / 6)), (35, (-5 / 54)), (55, (5 / 9)), (63, (5 / 18)), (64, (5 / 9))]

def singlePairValue359 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (145 / 864)), (2, (-25 / 864)), (3, (-25 / 27)), (4, (-10 / 27)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (24, (5 / 18)), (26, (-5 / 9)), (27, (-5 / 72)), (33, (5 / 18)), (34, (-5 / 27)), (35, (-5 / 27)), (55, (5 / 6)), (64, (5 / 18)), (66, (5 / 18)), (67, (-5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue360 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (25 / 288)), (2, (35 / 288)), (3, (-10 / 9)), (4, (-5 / 9)), (5, (-5 / 72)), (12, (-5 / 18)), (13, (-5 / 27)), (26, (-5 / 9)), (27, (5 / 24)), (35, (-5 / 18)), (55, (5 / 6))]

def singlePairValue361 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-25 / 288)), (2, (-5 / 72)), (3, (5 / 27)), (5, (5 / 216)), (12, (5 / 54)), (13, (5 / 54)), (26, (5 / 54)), (27, (-5 / 72)), (35, (5 / 54)), (55, (-5 / 18))]

def singlePairValue362 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (5 / 144)), (2, (-5 / 96)), (3, (5 / 54)), (5, (5 / 216)), (27, (-5 / 72)), (33, (-5 / 18)), (55, (-5 / 18)), (64, (-5 / 18))]

def singlePairValue363 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (5 / 144)), (2, (-5 / 864)), (3, (-35 / 54)), (4, (-5 / 27)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (25, (5 / 9)), (26, (-10 / 27)), (27, (-5 / 72)), (33, (5 / 9)), (34, (-5 / 27)), (35, (-5 / 54)), (55, (5 / 18)), (63, (5 / 9)), (64, (5 / 9)), (65, (5 / 18)), (67, (-5 / 54))]

def singlePairValue364 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (23, (-5 / 18)), (27, (5 / 36)), (55, (-5 / 18)), (63, (-5 / 18)), (65, (-5 / 18))]

def singlePairValue365 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 108)), (2, (-5 / 108)), (5, (5 / 216)), (25, (-5 / 18)), (27, (-5 / 72)), (33, (-5 / 18)), (63, (-5 / 18)), (64, (-5 / 18))]

def singlePairValue366 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (65 / 432)), (27, (5 / 36)), (63, (5 / 9))]

def singlePairValue367 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (5 / 72)), (2, (5 / 432)), (24, (-5 / 18)), (27, (5 / 36)), (55, (-5 / 9)), (66, (-5 / 18))]

def singlePairValue368 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 864)), (3, (5 / 18)), (4, (5 / 27)), (5, (5 / 216)), (26, (5 / 27)), (27, (-5 / 72)), (35, (5 / 54)), (55, (-5 / 18))]

def singlePairValue369 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 144)), (27, (5 / 36)), (55, (5 / 9))]

def singlePairValue370 : Sparse (Fin 909) := [(0, (25 / 432)), (1, (-25 / 432)), (2, (-5 / 108)), (3, (-10 / 27)), (5, (-5 / 216)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (55, (5 / 18))]

def singlePairValue371 : Sparse (Fin 909) := [(0, (35 / 864)), (1, (205 / 864)), (2, (5 / 108)), (3, (-35 / 54)), (4, (-10 / 27)), (5, (-5 / 216)), (26, (-10 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (55, (5 / 18))]

def singlePairValue372 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 216)), (2, (-25 / 432)), (3, (5 / 54)), (27, (-5 / 72)), (55, (-5 / 18))]

def singlePairValue373 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (5 / 96)), (2, (-5 / 108)), (3, (-5 / 18)), (12, (-5 / 27)), (13, (-25 / 54)), (26, (-5 / 27)), (34, (-5 / 27))]

def singlePairValue374 : Sparse (Fin 909) := [(0, (1 / 108)), (1, (5 / 144)), (2, (5 / 144)), (13, (5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue376 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (55 / 216)), (2, (-5 / 288)), (3, (-25 / 54)), (4, (-5 / 27)), (26, (-5 / 27))]

def singlePairValue377 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-35 / 864)), (2, (-5 / 96)), (3, (5 / 54)), (26, (5 / 54))]

def singlePairValue378 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 216)), (2, (-35 / 864)), (3, (5 / 54))]

def singlePairValue379 : Sparse (Fin 909) := [(0, (1 / 24)), (2, (5 / 24))]

def singlePairValue380 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (5 / 48)), (2, (5 / 432)), (3, (-65 / 54)), (4, (-10 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-10 / 27)), (13, (-5 / 9)), (26, (-5 / 9)), (27, (5 / 72)), (33, (5 / 9)), (34, (-10 / 27)), (35, (-5 / 54)), (54, (5 / 18)), (65, (5 / 18)), (67, (-5 / 54))]

def singlePairValue381 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-55 / 864)), (2, (-35 / 864)), (3, (5 / 54)), (5, (5 / 216)), (26, (5 / 54)), (27, (-5 / 72)), (33, (-5 / 18)), (54, (-5 / 18)), (65, (-5 / 18))]

def singlePairValue382 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (155 / 864)), (2, (-35 / 864)), (3, (-10 / 9)), (4, (-5 / 27)), (12, (-5 / 9)), (13, (-35 / 54)), (26, (-5 / 27)), (33, (5 / 9)), (34, (-5 / 27))]

def singlePairValue383 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-5 / 864)), (2, (-5 / 864)), (3, (5 / 27)), (12, (5 / 54)), (13, (5 / 27)), (33, (-5 / 18))]

def singlePairValue384 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (-25 / 288)), (3, (5 / 18)), (12, (5 / 27)), (13, (10 / 27)), (34, (5 / 54))]

def singlePairValue385 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 72)), (2, (5 / 36)), (13, (-10 / 27))]

def singlePairValue386 : Sparse (Fin 909) := [(0, (13 / 864)), (1, (5 / 288)), (2, (-5 / 216)), (3, (5 / 18)), (13, (5 / 54)), (26, (5 / 27)), (34, (5 / 27))]

def singlePairValue387 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 432)), (2, (5 / 108)), (3, (5 / 27)), (4, (5 / 54)), (26, (5 / 54))]

def singlePairValue388 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 144)), (2, (-5 / 108)), (26, (-5 / 27))]

def singlePairValue390 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 54)), (2, (-25 / 432)), (3, (-5 / 27))]

def singlePairValue391 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 54)), (2, (-25 / 432)), (3, (-5 / 27)), (13, (-5 / 27)), (34, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue392 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 144)), (2, (25 / 216)), (3, (-10 / 9)), (4, (-10 / 27)), (5, (-5 / 72)), (13, (-5 / 27)), (26, (-10 / 9)), (27, (5 / 24)), (34, (-20 / 27)), (65, (5 / 18)), (66, (5 / 9)), (67, (-5 / 18))]

def singlePairValue393 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 864)), (2, (-25 / 864)), (3, (5 / 27)), (5, (5 / 216)), (13, (5 / 54)), (26, (5 / 27)), (27, (-5 / 72)), (34, (5 / 27)), (65, (-5 / 18)), (67, (5 / 54))]

def singlePairValue394 : Sparse (Fin 909) := [(0, (1 / 432)), (1, (25 / 96)), (2, (-65 / 864)), (3, (-65 / 54)), (4, (-5 / 9)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-35 / 54)), (33, (5 / 18)), (34, (-5 / 27))]

def singlePairValue395 : Sparse (Fin 909) := [(0, (5 / 864)), (1, (5 / 108)), (2, (-5 / 288)), (3, (5 / 27)), (26, (5 / 54)), (33, (-5 / 18))]

def singlePairValue397 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-55 / 864)), (2, (-25 / 864)), (3, (5 / 27)), (12, (5 / 54)), (13, (5 / 54))]

def singlePairValue398 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 108)), (2, (-5 / 108)), (3, (5 / 54)), (5, (5 / 216)), (12, (5 / 54)), (13, (5 / 54)), (27, (-5 / 72)), (33, (-5 / 18)), (55, (-5 / 18)), (61, (-5 / 18))]

def singlePairValue399 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (35 / 432)), (2, (5 / 216)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (26, (5 / 18)), (27, (-5 / 72)), (34, (5 / 27)), (66, (-5 / 18)), (67, (5 / 54))]

def singlePairValue400 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (5 / 432)), (2, (25 / 864)), (3, (10 / 27)), (4, (5 / 27)), (26, (5 / 18)), (34, (5 / 54))]

def singlePairValue401 : Sparse (Fin 909) := [(0, (7 / 288)), (2, (25 / 864)), (3, (5 / 18)), (4, (5 / 27)), (26, (5 / 27))]

def singlePairValue402 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-25 / 432)), (2, (-5 / 144)), (3, (-5 / 27)), (26, (-5 / 27))]

def singlePairValue403 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (-5 / 216)), (2, (55 / 864)), (3, (5 / 54))]

def singlePairValue404 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-5 / 72)), (2, (-5 / 72))]

def singlePairValue405 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 54)), (2, (-25 / 432)), (3, (-5 / 27))]

def singlePairValue406 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 216)), (3, (-5 / 27)), (26, (-5 / 27)), (34, (-5 / 27))]

def singlePairValue407 : Sparse (Fin 909) := [(0, (1 / 24)), (2, (5 / 24))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue408 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (27, (5 / 36)), (65, (5 / 9))]

def singlePairValue409 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (-25 / 864)), (2, (5 / 108)), (3, (5 / 18)), (4, (5 / 54)), (12, (5 / 54)), (13, (5 / 54)), (26, (5 / 54)), (33, (-5 / 18)), (34, (5 / 54))]

def singlePairValue410 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-35 / 432)), (2, (-5 / 432)), (33, (5 / 9))]

def singlePairValue411 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (5 / 36)), (2, (5 / 288)), (3, (5 / 18)), (12, (5 / 18)), (13, (5 / 27))]

def singlePairValue412 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (35 / 432)), (2, (-5 / 216)), (3, (-5 / 27)), (12, (-5 / 27)), (13, (-5 / 27))]

def singlePairValue413 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 72)), (2, (5 / 108)), (27, (5 / 36)), (66, (5 / 9))]

def singlePairValue414 : Sparse (Fin 909) := [(0, (13 / 432)), (1, (-5 / 216)), (2, (5 / 144)), (3, (-5 / 27)), (4, (-5 / 27)), (26, (-5 / 27))]

def singlePairValue415 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 48)), (2, (-5 / 72)), (26, (5 / 9))]

def singlePairValue416 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (55 / 216)), (2, (5 / 432)), (3, (-5 / 27))]

def singlePairValue421 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 48)), (2, (-5 / 48)), (34, (5 / 9))]

def singlePairValue423 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (5 / 432)), (2, (5 / 144)), (5, (-5 / 108)), (31, (5 / 18)), (51, (5 / 9)), (68, (5 / 18)), (124, (5 / 18)), (126, (5 / 9)), (236, (5 / 18))]

def singlePairValue424 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 432)), (2, (5 / 96)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 72)), (7, (-5 / 27)), (12, (-5 / 54)), (23, (5 / 9)), (24, (5 / 9)), (51, (5 / 18)), (55, (5 / 9)), (68, (5 / 18)), (124, (5 / 18)), (125, (5 / 18)), (126, (5 / 18)), (197, (5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue426 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (35 / 432)), (2, (5 / 96)), (3, (-5 / 27)), (4, (-5 / 54)), (5, (-5 / 54)), (12, (-5 / 54)), (27, (5 / 72)), (31, (5 / 18)), (51, (5 / 9)), (55, (5 / 18)), (68, (5 / 18)), (194, (-5 / 9)), (486, (-5 / 9)), (487, (-5 / 9))]

def singlePairValue427 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-5 / 288)), (2, (25 / 288)), (3, (-5 / 54)), (5, (-5 / 54)), (12, (-5 / 54)), (23, (5 / 9)), (24, (5 / 18)), (25, (5 / 18)), (27, (5 / 72)), (54, (5 / 18)), (55, (5 / 18)), (68, (5 / 18)), (195, (-5 / 9)), (263, (-5 / 9)), (487, (-5 / 9))]

def singlePairValue428 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (5 / 36)), (2, (-25 / 432)), (23, (5 / 9)), (24, (10 / 9)), (27, (-5 / 18)), (30, (5 / 9)), (55, (5 / 9)), (194, (-5 / 9))]

def singlePairValue429 : Sparse (Fin 909) := [(0, (5 / 108)), (2, (-5 / 72)), (3, (-5 / 18)), (5, (5 / 54)), (7, (-5 / 54)), (8, (-5 / 54)), (12, (-5 / 54)), (23, (5 / 18)), (24, (5 / 18)), (27, (-5 / 24)), (55, (5 / 18))]

def singlePairValue430 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (155 / 864)), (2, (-115 / 864)), (3, (-5 / 27)), (4, (-5 / 54)), (5, (5 / 72)), (7, (-5 / 54)), (8, (-5 / 54)), (24, (5 / 18)), (27, (-5 / 18)), (30, (5 / 18)), (31, (5 / 18)), (51, (5 / 18))]

def singlePairValue431 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 36)), (2, (-5 / 48)), (3, (-5 / 9)), (4, (-5 / 27)), (5, (5 / 108)), (7, (-5 / 54)), (8, (-5 / 54)), (12, (-5 / 18)), (23, (5 / 18)), (24, (5 / 18)), (27, (-5 / 36)), (51, (5 / 9)), (55, (5 / 9))]

def singlePairValue432 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 72)), (2, (5 / 288)), (23, (-5 / 18)), (24, (-5 / 18)), (27, (5 / 24)), (55, (-5 / 18))]

def singlePairValue433 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (5 / 216)), (24, (-5 / 18)), (27, (5 / 18)), (30, (-5 / 18))]

def singlePairValue434 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (25 / 432)), (2, (-5 / 432)), (3, (-35 / 54)), (4, (-5 / 54)), (5, (5 / 216)), (12, (-10 / 27)), (13, (-25 / 54)), (27, (-5 / 72)), (33, (5 / 9)), (51, (5 / 18)), (55, (5 / 18)), (59, (5 / 18)), (61, (5 / 18)), (194, (-5 / 9))]

def singlePairValue435 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (2, (5 / 216)), (27, (5 / 36)), (194, (5 / 9))]

def singlePairValue436 : Sparse (Fin 909) := [(0, (19 / 432)), (2, (25 / 432)), (3, (-5 / 18)), (4, (-5 / 27)), (5, (-5 / 108)), (12, (-5 / 54)), (27, (5 / 72)), (31, (5 / 9)), (51, (5 / 9)), (55, (5 / 18))]

def singlePairValue437 : Sparse (Fin 909) := [(0, (35 / 864)), (1, (-5 / 144)), (2, (5 / 864)), (5, (5 / 216)), (31, (-5 / 18)), (51, (-5 / 18))]

def singlePairValue438 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-35 / 432)), (2, (-5 / 432)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (12, (5 / 54)), (27, (-5 / 72)), (51, (-5 / 18)), (55, (-5 / 18))]

def singlePairValue439 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (55 / 432)), (2, (55 / 864)), (3, (-10 / 27)), (5, (-5 / 54)), (7, (-5 / 27)), (12, (-5 / 27)), (23, (5 / 9)), (25, (5 / 18)), (27, (5 / 36)), (54, (5 / 9)), (68, (5 / 18)), (124, (5 / 18)), (125, (5 / 9)), (196, (5 / 18))]

def singlePairValue440 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (5 / 432)), (23, (5 / 9)), (24, (5 / 9)), (55, (10 / 9)), (63, (5 / 9)), (65, (5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue441 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (25 / 864)), (2, (-5 / 144)), (3, (-35 / 54)), (4, (-5 / 54)), (5, (5 / 108)), (7, (-5 / 27)), (12, (-5 / 18)), (13, (-5 / 54)), (23, (5 / 9)), (24, (5 / 18)), (25, (5 / 18)), (26, (-5 / 54)), (27, (-5 / 36)), (35, (-5 / 54)), (54, (5 / 18)), (55, (5 / 18))]

def singlePairValue442 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (155 / 864)), (2, (-5 / 48)), (3, (-5 / 6)), (4, (-10 / 27)), (5, (5 / 108)), (7, (-5 / 18)), (12, (-5 / 54)), (23, (5 / 18)), (24, (5 / 9)), (26, (-5 / 27)), (27, (-5 / 36)), (35, (-5 / 54)), (55, (5 / 18))]

def singlePairValue443 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 432)), (2, (-5 / 288)), (3, (-5 / 9)), (4, (-5 / 54)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 18)), (23, (5 / 9)), (25, (5 / 9)), (26, (-5 / 54)), (27, (-5 / 72)), (33, (5 / 9)), (51, (5 / 18)), (54, (5 / 9)), (55, (5 / 18)), (63, (5 / 18)), (64, (5 / 18)), (65, (5 / 18))]

def singlePairValue444 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-5 / 144)), (2, (5 / 48)), (3, (-5 / 9)), (4, (-5 / 18)), (5, (-5 / 72)), (12, (-5 / 27)), (23, (5 / 18)), (25, (5 / 9)), (26, (-5 / 27)), (27, (5 / 24)), (31, (5 / 18)), (33, (5 / 9)), (54, (5 / 9)), (65, (5 / 18)), (195, (-5 / 9))]

def singlePairValue445 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 36)), (2, (55 / 864)), (3, (-35 / 54)), (5, (-5 / 72)), (7, (-5 / 54)), (12, (-5 / 9)), (23, (5 / 6)), (25, (5 / 6)), (27, (5 / 24)), (54, (5 / 9))]

def singlePairValue446 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (95 / 864)), (2, (-5 / 432)), (3, (5 / 54)), (5, (5 / 216)), (12, (5 / 54)), (23, (-5 / 18)), (25, (-5 / 18)), (27, (-5 / 72)), (54, (-5 / 18))]

def singlePairValue447 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 144)), (5, (5 / 216)), (27, (-5 / 72)), (195, (5 / 9))]

def singlePairValue448 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 432)), (2, (5 / 108)), (3, (-20 / 27)), (4, (-10 / 27)), (5, (-5 / 72)), (7, (-5 / 18)), (12, (-5 / 27)), (23, (5 / 18)), (24, (5 / 9)), (27, (5 / 24))]

def singlePairValue449 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 36)), (2, (-5 / 432)), (3, (5 / 27)), (5, (5 / 216)), (7, (5 / 54)), (12, (5 / 54)), (23, (-5 / 18)), (27, (-5 / 72))]

def singlePairValue450 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (-35 / 288)), (2, (-5 / 432)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (7, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72))]

def singlePairValue451 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 18)), (23, (5 / 9)), (27, (5 / 36))]

def singlePairValue452 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 72)), (24, (5 / 9)), (27, (5 / 36))]

def singlePairValue453 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 54)), (2, (-5 / 48)), (3, (-5 / 27)), (4, (-5 / 27)), (5, (5 / 72)), (8, (-5 / 27)), (24, (5 / 9)), (27, (-5 / 24)), (30, (5 / 18)), (56, (5 / 18))]

def singlePairValue454 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (5 / 216)), (2, (-5 / 96)), (3, (-25 / 54)), (4, (-5 / 54)), (5, (-5 / 216)), (6, (5 / 864)), (12, (-5 / 27)), (13, (-5 / 54)), (31, (5 / 18)), (51, (5 / 18)), (52, (-5 / 54))]

def singlePairValue455 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (65 / 864)), (2, (-5 / 432)), (3, (-35 / 54)), (4, (-5 / 18)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-5 / 18)), (13, (-5 / 18)), (26, (-5 / 54)), (27, (5 / 72)), (35, (-5 / 54)), (51, (5 / 18)), (52, (-5 / 54)), (55, (5 / 18))]

def singlePairValue456 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 432)), (2, (5 / 216)), (3, (-5 / 6)), (4, (-10 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (7, (-5 / 54)), (12, (-5 / 27)), (23, (5 / 18)), (25, (5 / 9)), (26, (-10 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (54, (5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue457 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (35 / 216)), (2, (-5 / 216)), (3, (-35 / 54)), (4, (-10 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (7, (-5 / 54)), (12, (-5 / 27)), (13, (-5 / 54)), (24, (5 / 18)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (56, (5 / 18))]

def singlePairValue458 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (25 / 432)), (3, (-20 / 27)), (4, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-25 / 54)), (13, (-5 / 27)), (23, (5 / 18)), (25, (5 / 9)), (27, (5 / 72)), (31, (5 / 18)), (33, (10 / 9)), (54, (5 / 9)), (62, (5 / 18))]

def singlePairValue459 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (155 / 864)), (2, (-5 / 216)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 18)), (23, (5 / 18)), (25, (5 / 18)), (27, (5 / 72)), (35, (-5 / 54)), (54, (5 / 18))]

def singlePairValue461 : Sparse (Fin 909) := [(0, (-1 / 216)), (1, (95 / 864)), (2, (-25 / 864)), (3, (-10 / 27)), (4, (-5 / 27)), (12, (-5 / 27)), (13, (-5 / 54))]

def singlePairValue462 : Sparse (Fin 909) := [(0, (1 / 108)), (1, (145 / 864)), (2, (-35 / 864)), (3, (-20 / 27)), (4, (-5 / 27)), (12, (-10 / 27)), (13, (-5 / 18))]

def singlePairValue463 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 48)), (3, (-10 / 9)), (4, (-5 / 27)), (12, (-5 / 9)), (13, (-10 / 9)), (32, (-5 / 54))]

def singlePairValue467 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 36)), (2, (5 / 144)), (3, (5 / 18)), (4, (5 / 54)), (12, (5 / 27)), (13, (5 / 54))]

def singlePairValue468 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (25 / 432)), (2, (5 / 216)), (3, (5 / 27)), (13, (5 / 27))]

def singlePairValue470 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (35 / 288)), (2, (-25 / 432)), (3, (-5 / 6)), (4, (-5 / 18)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-10 / 27)), (26, (-5 / 27)), (27, (5 / 72)), (33, (5 / 6)), (81, (5 / 18)), (195, (-5 / 9))]

def singlePairValue471 : Sparse (Fin 909) := [(0, (43 / 864)), (1, (55 / 216)), (2, (5 / 216)), (3, (-10 / 27)), (5, (-5 / 216)), (6, (5 / 864)), (7, (-5 / 27)), (12, (-5 / 27)), (23, (5 / 18)), (27, (5 / 72))]

def singlePairValue472 : Sparse (Fin 909) := [(0, (23 / 432)), (1, (-5 / 216)), (2, (-5 / 96)), (3, (-5 / 18)), (4, (-5 / 27)), (5, (-5 / 216)), (6, (5 / 864)), (7, (-5 / 54)), (8, (-5 / 54)), (24, (5 / 18)), (27, (5 / 72))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue473 : Sparse (Fin 909) := [(0, (41 / 864)), (1, (5 / 48)), (2, (-5 / 54)), (3, (-20 / 27)), (5, (-5 / 216)), (6, (5 / 864)), (7, (-5 / 27)), (12, (-25 / 54)), (23, (5 / 18)), (27, (5 / 72))]

def singlePairValue474 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-5 / 108)), (5, (5 / 216)), (8, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72))]

def singlePairValue475 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-5 / 108)), (2, (5 / 864)), (3, (-10 / 27)), (4, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (25, (5 / 9)), (26, (-5 / 27)), (27, (5 / 72)), (31, (5 / 18)), (33, (5 / 9)), (63, (5 / 18)), (64, (5 / 9)), (123, (5 / 18))]

def singlePairValue476 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (65 / 432)), (2, (-5 / 216)), (3, (-35 / 54)), (4, (-5 / 18)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-5 / 18)), (25, (5 / 9)), (26, (-5 / 54)), (27, (5 / 72)), (31, (5 / 9)), (33, (5 / 6)), (51, (5 / 18)), (55, (5 / 18)), (64, (5 / 18)), (123, (5 / 18))]

def singlePairValue477 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (5 / 288)), (2, (-35 / 864)), (3, (-5 / 18)), (4, (-5 / 54)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-5 / 54)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (51, (5 / 18)), (52, (-5 / 54)), (55, (5 / 18))]

def singlePairValue478 : Sparse (Fin 909) := [(0, (13 / 432)), (2, (25 / 432)), (3, (-10 / 27)), (4, (-5 / 27)), (25, (5 / 18)), (26, (-5 / 27))]

def singlePairValue479 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (85 / 864)), (2, (-25 / 864)), (3, (-25 / 54)), (4, (-5 / 27)), (12, (-5 / 27)), (26, (-5 / 54))]

def singlePairValue480 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 48)), (2, (-35 / 864)), (3, (-20 / 27)), (4, (-5 / 27)), (12, (-10 / 27)), (13, (-10 / 27)), (26, (-5 / 54)), (33, (5 / 9)), (34, (-5 / 54))]

def singlePairValue481 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 48)), (3, (-10 / 9)), (12, (-5 / 9)), (13, (-10 / 9)), (34, (-5 / 27))]

def singlePairValue483 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-35 / 432)), (2, (25 / 432)), (3, (5 / 27)), (12, (5 / 54))]

def singlePairValue484 : Sparse (Fin 909) := [(0, (1 / 432)), (1, (25 / 216)), (2, (-25 / 432)), (3, (-35 / 54)), (4, (-10 / 27)), (12, (-5 / 27)), (25, (5 / 9)), (26, (-5 / 54)), (31, (5 / 9)), (33, (5 / 6))]

def singlePairValue485 : Sparse (Fin 909) := [(0, (1 / 216)), (1, (25 / 216)), (2, (-5 / 108)), (3, (-35 / 54)), (4, (-5 / 18)), (12, (-5 / 27)), (13, (-5 / 54)), (25, (5 / 18)), (26, (-5 / 18)), (31, (5 / 18)), (33, (5 / 18)), (34, (-5 / 54))]

def singlePairValue486 : Sparse (Fin 909) := [(0, (-1 / 864)), (1, (35 / 108)), (2, (-5 / 96)), (3, (-5 / 6)), (4, (-5 / 9)), (12, (-10 / 27)), (25, (5 / 18)), (26, (-5 / 27))]

def singlePairValue487 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (5 / 144)), (3, (5 / 27)), (4, (5 / 54)), (25, (-5 / 18)), (26, (5 / 54))]

def singlePairValue488 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (5 / 48)), (2, (-5 / 96)), (3, (-5 / 18)), (4, (-5 / 27)), (12, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue56 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (2, (5 / 216)), (5, (5 / 54)), (6, (5 / 432)), (201, (5 / 9))]

def singlePairValue58 : Sparse (Fin 909) := [(0, (7 / 288)), (2, (5 / 432)), (3, (-5 / 27)), (5, (5 / 24)), (6, (-5 / 216)), (7, (-5 / 54)), (9, (5 / 72)), (13, (-10 / 27)), (35, (-20 / 27)), (52, (-20 / 27)), (58, (-5 / 864)), (60, (-25 / 54)), (69, (-5 / 54)), (70, (-5 / 54)), (128, (-10 / 27)), (257, (-5 / 27)), (260, (5 / 18)), (495, (-5 / 18))]

def singlePairValue59 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (35 / 432)), (2, (5 / 54)), (5, (-5 / 54)), (9, (-5 / 108)), (52, (5 / 27)), (58, (5 / 432)), (128, (5 / 27)), (495, (5 / 27))]

def singlePairValue60 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 864)), (2, (5 / 864)), (5, (-5 / 72)), (6, (5 / 432)), (7, (5 / 54)), (9, (-5 / 108)), (35, (5 / 27)), (52, (5 / 54)), (60, (5 / 54)), (69, (5 / 54)), (70, (5 / 54)), (257, (5 / 54)), (260, (-5 / 18))]

def singlePairValue61 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-35 / 864)), (2, (-5 / 108)), (3, (-5 / 54)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (9, (-5 / 54)), (35, (-5 / 27)), (52, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 27)), (70, (-5 / 54)), (71, (-5 / 27))]

def singlePairValue62 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 432)), (2, (185 / 864)), (5, (5 / 216)), (35, (5 / 54)), (58, (-5 / 864)), (70, (5 / 54))]

def singlePairValue63 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 216)), (2, (-35 / 432)), (5, (5 / 18)), (6, (-5 / 144)), (8, (-10 / 27)), (9, (-5 / 54)), (52, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 54)), (71, (-10 / 27))]

def singlePairValue64 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-35 / 864)), (2, (-5 / 108)), (5, (-5 / 108)), (6, (5 / 216)), (58, (-5 / 864)), (71, (5 / 54))]

def singlePairValue65 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 216)), (2, (-55 / 432)), (3, (-5 / 9)), (5, (5 / 18)), (6, (-5 / 144)), (7, (-5 / 9)), (9, (-5 / 54)), (35, (-5 / 9)), (52, (-5 / 9)), (58, (5 / 864)), (69, (-5 / 18)), (70, (-5 / 27))]

def singlePairValue66 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 108)), (2, (5 / 48)), (5, (-5 / 54)), (6, (5 / 144)), (52, (5 / 27)), (58, (-5 / 864)), (69, (5 / 54))]

def singlePairValue67 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 864)), (2, (5 / 864)), (3, (5 / 54)), (5, (5 / 216)), (6, (5 / 288)), (9, (5 / 216)), (13, (5 / 54)), (35, (5 / 18)), (52, (5 / 27)), (58, (-5 / 864)), (60, (5 / 27)), (128, (5 / 54)), (257, (5 / 54)), (495, (5 / 54))]

def singlePairValue68 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-25 / 288)), (2, (-25 / 432)), (3, (5 / 54)), (5, (-5 / 108)), (6, (-5 / 864)), (7, (5 / 27)), (9, (5 / 108)), (35, (5 / 27)), (52, (5 / 54)), (69, (5 / 54)), (70, (5 / 54))]

def singlePairValue69 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (5 / 54)), (2, (25 / 432)), (5, (-5 / 54)), (8, (5 / 27)), (9, (5 / 108)), (71, (5 / 27))]

def singlePairValue70 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-25 / 432)), (5, (5 / 54)), (6, (-5 / 108)), (9, (5 / 108)), (58, (5 / 432))]

def singlePairValue71 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (5 / 27)), (5, (-5 / 108)), (9, (-5 / 108)), (35, (-5 / 27)), (70, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue489 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-35 / 864)), (2, (25 / 864)), (3, (5 / 54)), (4, (5 / 54))]

def singlePairValue490 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 27)), (2, (5 / 216)), (3, (5 / 27)), (12, (5 / 27))]

def singlePairValue491 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (-5 / 48)), (2, (5 / 144)), (3, (5 / 27)), (12, (5 / 27)), (33, (-5 / 9))]

def singlePairValue492 : Sparse (Fin 909) := [(0, (1 / 432)), (1, (5 / 36)), (2, (-5 / 144)), (3, (-5 / 9)), (13, (-10 / 27))]

def singlePairValue493 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 288)), (2, (5 / 864)), (3, (5 / 18)), (4, (5 / 27)), (12, (5 / 54)), (26, (5 / 54))]

def singlePairValue494 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (95 / 432)), (2, (-5 / 864)), (3, (5 / 54)), (12, (5 / 54))]

def singlePairValue497 : Sparse (Fin 909) := [(1, (115 / 432)), (2, (-25 / 432)), (3, (-20 / 27)), (4, (-10 / 27)), (12, (-10 / 27)), (13, (-5 / 27)), (25, (5 / 9)), (31, (5 / 9)), (33, (5 / 9))]

def singlePairValue498 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (-25 / 864)), (2, (5 / 432)), (3, (5 / 54)), (4, (5 / 54)), (25, (-5 / 18)), (31, (-5 / 18)), (33, (-5 / 18))]

def singlePairValue499 : Sparse (Fin 909) := [(0, (-17 / 864)), (1, (5 / 12)), (2, (-5 / 96)), (3, (-5 / 6)), (4, (-5 / 9)), (12, (-5 / 9)), (13, (-5 / 27))]

def singlePairValue500 : Sparse (Fin 909) := [(0, (1 / 108)), (1, (25 / 216)), (2, (-5 / 216)), (3, (5 / 27)), (12, (5 / 27)), (25, (-5 / 18))]

def singlePairValue501 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 54)), (2, (5 / 216)), (25, (5 / 9))]

def singlePairValue502 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-25 / 216)), (2, (-5 / 432)), (3, (5 / 27)), (4, (5 / 27)), (12, (5 / 54))]

def singlePairValue503 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-25 / 432)), (2, (5 / 432)), (3, (-5 / 27)), (4, (-5 / 27))]

def singlePairValue504 : Sparse (Fin 909) := [(0, (35 / 432)), (1, (-25 / 144)), (12, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue507 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 12)), (12, (5 / 9))]

def singlePairValue508 : Sparse (Fin 909) := [(0, (13 / 216)), (1, (5 / 216)), (5, (-5 / 72)), (8, (-5 / 18)), (24, (5 / 18)), (27, (5 / 24)), (30, (5 / 9))]

def singlePairValue509 : Sparse (Fin 909) := [(0, (2 / 27)), (1, (5 / 108)), (5, (5 / 216)), (8, (5 / 54)), (27, (-5 / 72)), (30, (-5 / 18))]

def singlePairValue510 : Sparse (Fin 909) := [(0, (13 / 216)), (1, (5 / 216)), (27, (5 / 36)), (30, (5 / 9))]

def singlePairValue511 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (35 / 144)), (2, (-115 / 864)), (3, (-10 / 27)), (4, (-5 / 18)), (5, (-5 / 216)), (6, (5 / 864)), (31, (5 / 9)), (51, (5 / 18)), (52, (-5 / 54))]

def singlePairValue513 : Sparse (Fin 909) := [(1, (10 / 27)), (2, (-5 / 54)), (3, (-10 / 27)), (4, (-10 / 27)), (12, (-5 / 54)), (31, (5 / 9))]

def singlePairValue514 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 216)), (2, (5 / 288)), (3, (5 / 54)), (4, (5 / 54)), (31, (-5 / 18))]

def singlePairValue516 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (31, (5 / 9))]

def singlePairValue517 : Sparse (Fin 909) := [(0, (17 / 288)), (1, (25 / 216)), (2, (-5 / 72)), (5, (-5 / 216)), (6, (5 / 864)), (8, (-5 / 27)), (27, (5 / 72)), (30, (5 / 18))]

def singlePairValue519 : Sparse (Fin 909) := [(0, (1 / 864)), (1, (245 / 864)), (2, (-25 / 432)), (3, (-10 / 27)), (4, (-5 / 18)), (26, (-5 / 54)), (31, (5 / 18))]

def singlePairValue520 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (115 / 432)), (2, (-55 / 864)), (3, (-5 / 54)), (4, (-5 / 27))]

def singlePairValue521 : Sparse (Fin 909) := [(0, (11 / 144)), (1, (-5 / 72)), (2, (5 / 144))]

def singlePairValue522 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 864)), (2, (-5 / 216)), (3, (5 / 27)), (26, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue523 : Sparse (Fin 909) := [(0, (49 / 864)), (1, (-25 / 432)), (2, (-5 / 864)), (3, (5 / 54)), (4, (5 / 27))]

def singlePairValue526 : Sparse (Fin 909) := [(0, (67 / 864)), (1, (-25 / 288)), (4, (5 / 54))]

def singlePairValue527 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (5 / 18))]

def singlePairValue528 : Sparse (Fin 909) := [(0, (23 / 432)), (1, (-5 / 144)), (4, (-5 / 27))]

def singlePairValue530 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (-5 / 48)), (4, (5 / 9))]

def singlePairValue531 : Sparse (Fin 909) := [(0, (79 / 432)), (1, (35 / 144)), (12, (-5 / 54))]

def singlePairValue533 : Sparse (Fin 909) := [(0, (47 / 432)), (1, (35 / 144)), (4, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue72 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 144)), (6, (5 / 432)), (9, (-5 / 108)), (52, (-5 / 27)), (69, (-5 / 27))]

def singlePairValue73 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 144)), (2, (25 / 144)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (35, (-5 / 27)), (60, (-5 / 27)), (257, (-5 / 27))]

def singlePairValue74 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-55 / 864)), (2, (-35 / 864)), (5, (-5 / 216)), (6, (-5 / 432)), (7, (5 / 54)), (9, (5 / 108)), (35, (5 / 54)), (54, (-5 / 18)), (259, (-5 / 18)), (260, (-5 / 18))]

def singlePairValue75 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 432)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (259, (5 / 9))]

def singlePairValue76 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-25 / 432)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (260, (5 / 9))]

def singlePairValue77 : Sparse (Fin 909) := [(0, (41 / 864)), (1, (25 / 864)), (2, (55 / 864)), (3, (-5 / 54)), (5, (5 / 216)), (6, (5 / 864)), (7, (-5 / 27)), (8, (-5 / 54)), (11, (-5 / 54)), (26, (-5 / 54)), (35, (-5 / 18)), (52, (-5 / 54)), (228, (5 / 18))]

def singlePairValue78 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 144)), (2, (-25 / 432)), (5, (-5 / 216)), (6, (-25 / 432)), (11, (5 / 54)), (35, (5 / 54))]

def singlePairValue79 : Sparse (Fin 909) := [(0, (49 / 864)), (1, (-35 / 216)), (2, (-55 / 432)), (3, (-5 / 27)), (5, (5 / 54)), (6, (5 / 864)), (7, (-5 / 54)), (8, (-5 / 27)), (35, (-5 / 27)), (52, (-10 / 27))]

def singlePairValue80 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (5 / 144)), (2, (-5 / 108)), (5, (-5 / 108)), (6, (-5 / 96)), (52, (5 / 54))]

def singlePairValue81 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (25 / 864)), (2, (5 / 216)), (5, (5 / 24)), (7, (5 / 54)), (8, (5 / 54)), (35, (5 / 54))]

def singlePairValue83 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 144)), (2, (-5 / 108)), (5, (-5 / 54)), (6, (5 / 216)), (11, (5 / 54)), (26, (5 / 54)), (35, (5 / 27))]

def singlePairValue87 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (25 / 288)), (2, (5 / 288)), (5, (-5 / 108)), (6, (-5 / 216)), (13, (5 / 54)), (35, (5 / 27)), (52, (5 / 27)), (60, (5 / 27)), (128, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue88 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 72)), (2, (5 / 216)), (5, (5 / 54)), (6, (25 / 216)), (128, (-5 / 27))]

def singlePairValue89 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 216)), (2, (25 / 864)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 432)), (7, (5 / 54)), (11, (5 / 54)), (26, (5 / 54)), (35, (5 / 27)), (228, (-5 / 18))]

def singlePairValue90 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (2, (-5 / 216)), (6, (-5 / 144)), (11, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue91 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 216)), (2, (-55 / 432)), (3, (-5 / 27)), (5, (10 / 27)), (6, (-55 / 864)), (7, (-5 / 54)), (8, (-5 / 27)), (35, (-5 / 27)), (52, (-10 / 27))]

def singlePairValue92 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-35 / 864)), (2, (-5 / 108)), (5, (-25 / 216)), (6, (25 / 864)), (7, (5 / 54)), (35, (5 / 54))]

def singlePairValue93 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (5 / 48)), (2, (5 / 54)), (5, (-5 / 36)), (6, (5 / 216)), (8, (5 / 54)), (52, (5 / 54))]

def singlePairValue94 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 108)), (2, (-5 / 72)), (5, (5 / 108)), (6, (-25 / 432))]

def singlePairValue95 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 216)), (2, (35 / 432)), (3, (5 / 27)), (5, (-5 / 54)), (6, (5 / 288)), (7, (5 / 54)), (35, (5 / 27)), (52, (5 / 27))]

def singlePairValue96 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 216)), (2, (-5 / 108)), (5, (5 / 108)), (6, (-5 / 108)), (52, (-5 / 27))]

def singlePairValue97 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 108)), (6, (-5 / 144)), (35, (-5 / 27)), (52, (-5 / 27)), (60, (-5 / 27))]

def singlePairValue98 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (5, (5 / 27)), (7, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue99 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (5 / 216)), (5, (25 / 108)), (8, (-5 / 27))]

def singlePairValue100 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (5, (-5 / 36)), (6, (25 / 144))]

def singlePairValue101 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 108)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 432)), (12, (5 / 54)), (13, (5 / 18)), (35, (5 / 54)), (52, (5 / 54)), (59, (-5 / 18)), (60, (5 / 54)), (128, (5 / 54))]

def singlePairValue102 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 48)), (6, (-5 / 144)), (13, (-5 / 27)), (60, (-5 / 27)), (128, (-5 / 27))]

def singlePairValue103 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (5 / 36)), (59, (5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue104 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (6, (5 / 36)), (128, (5 / 9))]

def singlePairValue105 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 432)), (5, (-5 / 108)), (6, (5 / 216)), (11, (-5 / 27)), (26, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue106 : Sparse (Fin 909) := [(0, (5 / 144)), (2, (5 / 108)), (5, (-5 / 54)), (6, (5 / 432)), (228, (5 / 9))]

def singlePairValue107 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (-5 / 72)), (6, (-5 / 72)), (11, (5 / 9))]

def singlePairValue108 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 96)), (2, (-65 / 864)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 432)), (35, (5 / 54)), (52, (5 / 27))]

def singlePairValue109 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 432)), (2, (25 / 108)), (5, (-5 / 108)), (35, (-5 / 27))]

def singlePairValue110 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 108)), (2, (-5 / 108)), (6, (5 / 432)), (52, (-5 / 27))]

def singlePairValue111 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-25 / 432)), (2, (-5 / 432)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 432)), (35, (-5 / 27)), (52, (-5 / 27))]

def singlePairValue112 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 72)), (6, (-5 / 144)), (52, (5 / 9))]

def singlePairValue113 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (5 / 36)), (5, (5 / 36)), (35, (5 / 9))]

def singlePairValue114 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 108)), (2, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 27)), (6, (-5 / 288)), (7, (-5 / 9)), (8, (-5 / 27)), (9, (5 / 108)), (26, (-5 / 54)), (35, (-20 / 27)), (52, (-5 / 54)), (67, (-5 / 27)), (69, (-10 / 27)), (70, (-10 / 27)), (71, (-5 / 54)), (257, (-5 / 54))]

def singlePairValue115 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 216)), (2, (35 / 432)), (9, (-5 / 54)), (58, (5 / 432))]

def singlePairValue116 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 864)), (2, (5 / 96)), (5, (-25 / 216)), (6, (5 / 432)), (7, (5 / 27)), (8, (5 / 54)), (9, (-5 / 108)), (35, (5 / 54)), (52, (5 / 54)), (69, (5 / 27)), (70, (5 / 54)), (71, (5 / 54))]

def singlePairValue117 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 96)), (2, (-5 / 216)), (5, (-5 / 72)), (6, (5 / 288)), (7, (5 / 27)), (9, (-5 / 108)), (35, (5 / 18)), (67, (5 / 54)), (69, (5 / 54)), (70, (5 / 27)), (257, (5 / 54))]

def singlePairValue118 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-25 / 288)), (2, (-55 / 864)), (3, (-5 / 27)), (5, (25 / 108)), (6, (-5 / 216)), (7, (-10 / 27)), (8, (-10 / 27)), (9, (-5 / 54)), (35, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 27)), (70, (-5 / 54)), (71, (-5 / 27))]

def singlePairValue119 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-65 / 864)), (2, (-35 / 864)), (5, (-5 / 108)), (6, (35 / 864)), (7, (5 / 54)), (35, (5 / 27)), (58, (-5 / 864)), (70, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue120 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 216)), (2, (-5 / 48)), (5, (5 / 36)), (6, (-5 / 432)), (7, (-5 / 27)), (8, (-5 / 27)), (9, (-5 / 54)), (58, (5 / 864)), (69, (-5 / 54)), (71, (-10 / 27))]

def singlePairValue121 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-35 / 864)), (2, (25 / 432)), (6, (25 / 864)), (8, (5 / 54)), (58, (-5 / 864)), (71, (5 / 54))]

def singlePairValue122 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 864)), (2, (5 / 72)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 216)), (7, (5 / 54)), (9, (5 / 216)), (35, (5 / 27)), (52, (5 / 27)), (58, (-5 / 864)), (69, (5 / 54)), (495, (5 / 54))]

def singlePairValue123 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 108)), (3, (5 / 54)), (6, (-5 / 432)), (7, (5 / 27)), (9, (5 / 108)), (26, (5 / 54)), (35, (10 / 27)), (67, (5 / 27)), (70, (5 / 54)), (257, (5 / 54))]

def singlePairValue124 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 96)), (2, (5 / 216)), (5, (-5 / 54)), (6, (-5 / 432)), (7, (5 / 27)), (8, (5 / 27)), (9, (5 / 108)), (69, (5 / 54)), (71, (5 / 54))]

def singlePairValue125 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (35 / 216)), (2, (5 / 288)), (3, (-5 / 18)), (5, (-5 / 108)), (9, (-5 / 54)), (35, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 18)), (70, (-5 / 27))]

def singlePairValue126 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (55 / 432)), (2, (-5 / 432)), (5, (5 / 54)), (6, (5 / 288)), (7, (5 / 54)), (58, (-5 / 864)), (69, (5 / 54))]

def singlePairValue127 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 54)), (3, (5 / 54)), (5, (-5 / 216)), (6, (-5 / 432)), (9, (5 / 108)), (35, (5 / 54)), (69, (5 / 54)), (70, (5 / 54))]

def singlePairValue128 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 216)), (2, (-5 / 432)), (5, (-5 / 108)), (6, (-5 / 432)), (9, (5 / 108)), (71, (5 / 27))]

def singlePairValue129 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 48)), (2, (5 / 432)), (5, (-5 / 54)), (6, (-5 / 216)), (9, (5 / 108)), (58, (5 / 432))]

def singlePairValue130 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 96)), (2, (5 / 864)), (3, (5 / 54)), (5, (-5 / 216)), (6, (-5 / 432)), (7, (5 / 27)), (8, (5 / 54)), (9, (5 / 108)), (35, (5 / 54)), (81, (-5 / 18)), (256, (-5 / 18))]

def singlePairValue131 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 216)), (5, (-5 / 108)), (6, (5 / 432)), (7, (-5 / 27)), (9, (-5 / 108)), (35, (-5 / 27)), (70, (-5 / 27))]

def singlePairValue132 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 72)), (2, (5 / 432)), (6, (5 / 432)), (8, (-5 / 27)), (9, (-5 / 108)), (71, (-5 / 27))]

def singlePairValue133 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 48)), (2, (5 / 432)), (6, (5 / 432)), (7, (-5 / 27)), (9, (-5 / 108)), (69, (-5 / 27))]

def singlePairValue134 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-25 / 432)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (35, (-5 / 27)), (67, (-5 / 27)), (257, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue139 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 144)), (2, (5 / 144)), (5, (5 / 54)), (8, (5 / 54)), (35, (5 / 27)), (67, (5 / 54))]

def singlePairValue140 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (5, (-5 / 54)), (6, (25 / 216))]

def singlePairValue141 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-25 / 432)), (2, (-205 / 864)), (3, (-5 / 18)), (5, (10 / 27)), (6, (-5 / 144)), (7, (-5 / 9)), (8, (-5 / 9)), (35, (-5 / 27))]

def singlePairValue142 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 96)), (2, (5 / 96)), (3, (5 / 54)), (5, (-25 / 216)), (6, (5 / 288)), (7, (5 / 27)), (8, (5 / 54)), (35, (5 / 54))]

def singlePairValue143 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (5, (5 / 108)), (6, (-5 / 108)), (35, (-5 / 27))]

def singlePairValue144 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (25 / 432)), (2, (5 / 72)), (5, (-5 / 36)), (6, (5 / 288)), (7, (5 / 54)), (8, (5 / 27))]

def singlePairValue145 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (2, (25 / 432)), (3, (5 / 27)), (5, (-5 / 72)), (6, (5 / 432)), (7, (5 / 27)), (26, (5 / 54)), (35, (5 / 18)), (52, (5 / 54)), (67, (5 / 54))]

def singlePairValue146 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 54)), (2, (-5 / 72)), (5, (5 / 54)), (6, (-5 / 108))]

def singlePairValue147 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (5 / 108)), (6, (-5 / 144)), (35, (-5 / 27)), (52, (-5 / 27))]

def singlePairValue148 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (5 / 36)), (7, (-5 / 27)), (35, (-5 / 27)), (67, (-5 / 27))]

def singlePairValue149 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 72)), (5, (5 / 27)), (7, (-5 / 27)), (8, (-5 / 27))]

def singlePairValue150 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-35 / 432)), (2, (-5 / 216)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 72)), (6, (-5 / 288)), (7, (5 / 54)), (26, (5 / 27)), (35, (5 / 27)), (67, (5 / 54)), (81, (-5 / 18))]

def singlePairValue151 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 54)), (2, (-35 / 864)), (3, (5 / 18)), (5, (5 / 108)), (6, (-5 / 288)), (7, (5 / 18)), (35, (5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue152 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (55 / 432)), (2, (5 / 144)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 432)), (7, (-5 / 27)), (35, (-5 / 27))]

def singlePairValue153 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 144)), (2, (5 / 108)), (5, (-5 / 108)), (6, (5 / 432)), (81, (5 / 9))]

def singlePairValue154 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 72)), (6, (-5 / 144)), (35, (5 / 9))]

def singlePairValue155 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-35 / 432)), (6, (-5 / 288)), (7, (5 / 54)), (8, (5 / 27))]

def singlePairValue156 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 36)), (6, (5 / 432)), (7, (-5 / 27))]

def singlePairValue157 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 54)), (6, (5 / 432)), (8, (-5 / 27))]

def singlePairValue158 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 36)), (5, (-5 / 36)), (6, (-5 / 144))]

def singlePairValue159 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (5, (5 / 36)), (67, (5 / 9))]

def singlePairValue160 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 18)), (5, (5 / 36)), (7, (5 / 9))]

def singlePairValue161 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 72)), (5, (5 / 36)), (8, (5 / 9))]

def singlePairValue162 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 18)), (5, (5 / 9)), (6, (5 / 36))]

def singlePairValue163 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 144)), (3, (-5 / 18)), (5, (5 / 54)), (6, (-5 / 144)), (7, (-10 / 27)), (9, (5 / 216)), (13, (-5 / 54)), (26, (-10 / 27)), (34, (-5 / 54)), (35, (-20 / 27)), (67, (-5 / 27)), (68, (-5 / 72)), (69, (-5 / 54)), (70, (-5 / 18)), (124, (5 / 18)), (196, (5 / 18)), (197, (5 / 9)), (257, (-5 / 54)), (266, (5 / 18))]

def singlePairValue164 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 864)), (2, (5 / 864)), (3, (-25 / 54)), (5, (5 / 54)), (6, (-5 / 288)), (7, (-10 / 27)), (9, (5 / 216)), (13, (-5 / 18)), (26, (-5 / 27)), (34, (-5 / 54)), (35, (-5 / 9)), (52, (-5 / 27)), (60, (-5 / 54)), (64, (5 / 18)), (67, (-5 / 54)), (68, (-5 / 72)), (69, (-5 / 54)), (70, (-5 / 27)), (125, (5 / 9)), (126, (5 / 18)), (197, (5 / 18)), (257, (-5 / 54)), (260, (5 / 18)), (268, (5 / 18))]

def singlePairValue165 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 96)), (2, (-5 / 288)), (3, (-5 / 54)), (5, (5 / 108)), (7, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 9)), (27, (-5 / 72)), (35, (-5 / 54)), (54, (5 / 9)), (55, (5 / 18)), (63, (5 / 18)), (65, (5 / 18)), (68, (-5 / 36)), (124, (5 / 18)), (125, (5 / 6)), (196, (5 / 9)), (197, (5 / 18)), (264, (5 / 9)), (266, (5 / 18))]

def singlePairValue166 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 288)), (2, (-5 / 288)), (3, (-5 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (9, (5 / 216)), (13, (-10 / 27)), (32, (-5 / 54)), (35, (-10 / 27)), (52, (-5 / 27)), (54, (5 / 9)), (60, (-5 / 27)), (62, (5 / 9)), (68, (-5 / 72)), (69, (-5 / 54)), (70, (-5 / 54)), (125, (5 / 9)), (257, (-5 / 54)), (260, (5 / 9)), (264, (5 / 6))]

def singlePairValue167 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 432)), (2, (5 / 288)), (5, (5 / 216)), (23, (5 / 18)), (24, (5 / 18)), (27, (-5 / 36)), (51, (5 / 18)), (54, (5 / 18)), (55, (5 / 18)), (56, (5 / 18)), (61, (5 / 18)), (68, (-5 / 36)), (124, (5 / 18)), (125, (5 / 18)), (126, (5 / 18)), (196, (5 / 18)), (197, (5 / 9)), (263, (-5 / 9)), (266, (5 / 18)), (268, (5 / 18))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SinglePriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue420 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 72)), (2, (-5 / 144)), (3, (5 / 9))]

def singlePairValue496 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (25 / 216)), (2, (5 / 432)), (3, (-5 / 27)), (12, (-5 / 27))]

def singlePairValue505 : Sparse (Fin 909) := [(0, (5 / 108)), (1, (5 / 36)), (12, (-5 / 27))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue0 : Sparse Master := [(Sum.inl 0, (11 / 72)), (Sum.inl 2, (5 / 36)), (Sum.inl 1, (5 / 24))]

def nodeValue1 : Sparse Master := [(Sum.inl 0, (1 / 6)), (Sum.inl 2, (-5 / 24)), (Sum.inl 1, (-5 / 24))]

def nodeValue2 : Sparse Master := [(Sum.inl 0, (1 / 6)), (Sum.inl 2, (5 / 6))]

def nodeValue3 : Sparse Master := [(Sum.inl 0, (1 / 9)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (5 / 24))]

def nodeValue4 : Sparse Master := [(Sum.inl 0, (11 / 72)), (Sum.inl 2, (5 / 72)), (Sum.inl 1, (-5 / 36))]

def nodeValue5 : Sparse Master := [(Sum.inl 0, (5 / 24)), (Sum.inl 1, (-5 / 24))]

def nodeValue6 : Sparse Master := [(Sum.inl 0, (1 / 6)), (Sum.inl 1, (5 / 6))]

def nodeValue7 : Sparse Master := [(Sum.inl 0, (19 / 72)), (Sum.inl 1, (5 / 72))]

def nodeValue8 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (25 / 108)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (25 / 72)), (Sum.inl 6, (-5 / 72)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (-5 / 72)), (Sum.inl 69, (-5 / 6)), (Sum.inl 70, (-20 / 27)), (Sum.inl 71, (-5 / 9)), (Sum.inl 7, (-5 / 9)), (Sum.inl 35, (-5 / 18)), (Sum.inl 1, (-5 / 864))]

def nodeValue9 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (-5 / 36)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 108)), (Sum.inl 2, (-5 / 288)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 54)), (Sum.inl 71, (5 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue10 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 9, (5 / 27)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (5 / 18)), (Sum.inl 6, (-5 / 144)), (Sum.inl 256, (5 / 9)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (-35 / 864)), (Sum.inl 69, (-20 / 27)), (Sum.inl 70, (-25 / 54)), (Sum.inl 71, (-5 / 9)), (Sum.inl 7, (-5 / 9)), (Sum.inl 35, (-10 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 495, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-5 / 288))]

def nodeValue11 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-25 / 216)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 144)), (Sum.inl 2, (65 / 864)), (Sum.inl 69, (5 / 27)), (Sum.inl 71, (5 / 27)), (Sum.inl 495, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (25 / 864))]

def nodeValue12 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 72)), (Sum.inl 257, (5 / 54)), (Sum.inl 2, (-5 / 288)), (Sum.inl 69, (5 / 18)), (Sum.inl 70, (5 / 18)), (Sum.inl 71, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 54)), (Sum.inl 1, (-5 / 96))]

def nodeValue13 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 36)), (Sum.inl 58, (-5 / 144)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-5 / 144)), (Sum.inl 1, (-25 / 432))]

def nodeValue14 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 144)), (Sum.inl 257, (5 / 27)), (Sum.inl 2, (-5 / 864)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 495, (5 / 27)), (Sum.inl 1, (5 / 864))]

def nodeValue15 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 72)), (Sum.inl 256, (-5 / 18)), (Sum.inl 2, (35 / 864)), (Sum.inl 69, (5 / 27)), (Sum.inl 70, (5 / 54)), (Sum.inl 71, (5 / 18)), (Sum.inl 7, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (5 / 288))]

def nodeValue16 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 54)), (Sum.inl 58, (-5 / 144)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-5 / 216)), (Sum.inl 495, (-5 / 27))]

def nodeValue17 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 36)), (Sum.inl 2, (-5 / 216)), (Sum.inl 69, (-5 / 27)), (Sum.inl 70, (-5 / 27)), (Sum.inl 71, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue18 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (5 / 36)), (Sum.inl 2, (5 / 144)), (Sum.inl 69, (-5 / 27)), (Sum.inl 71, (-10 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue19 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 36)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (-5 / 72)), (Sum.inl 69, (-5 / 27)), (Sum.inl 70, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue20 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 18)), (Sum.inl 58, (5 / 36)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue21 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (-95 / 216)), (Sum.inl 58, (5 / 216)), (Sum.inl 5, (-5 / 27)), (Sum.inl 6, (5 / 72)), (Sum.inl 256, (5 / 6)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (25 / 864)), (Sum.inl 69, (-5 / 9)), (Sum.inl 70, (-5 / 18)), (Sum.inl 71, (-5 / 18)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-25 / 54)), (Sum.inl 3, (-5 / 18)), (Sum.inl 495, (-5 / 18)), (Sum.inl 52, (-5 / 9)), (Sum.inl 1, (25 / 864))]

def nodeValue22 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 9, (-10 / 27)), (Sum.inl 58, (5 / 216)), (Sum.inl 6, (5 / 96)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (-5 / 9)), (Sum.inl 70, (-5 / 27)), (Sum.inl 71, (-10 / 9)), (Sum.inl 7, (-5 / 18)), (Sum.inl 8, (-5 / 9)), (Sum.inl 1, (-5 / 216))]

def nodeValue23 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 54)), (Sum.inl 58, (-5 / 864)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-35 / 864)), (Sum.inl 69, (5 / 27)), (Sum.inl 70, (5 / 54)), (Sum.inl 71, (5 / 27)), (Sum.inl 7, (5 / 54)), (Sum.inl 1, (-65 / 864))]

def nodeValue24 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (25 / 216)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 288)), (Sum.inl 256, (-5 / 18)), (Sum.inl 2, (-35 / 864)), (Sum.inl 69, (5 / 27)), (Sum.inl 71, (5 / 54)), (Sum.inl 495, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue25 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 58, (5 / 432)), (Sum.inl 2, (25 / 144)), (Sum.inl 70, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue26 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 9, (5 / 54)), (Sum.inl 58, (-5 / 864)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (5 / 144)), (Sum.inl 69, (5 / 54)), (Sum.inl 71, (10 / 27)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue27 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (25 / 216)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (5 / 72)), (Sum.inl 6, (-5 / 288)), (Sum.inl 256, (-5 / 18)), (Sum.inl 257, (5 / 54)), (Sum.inl 2, (-35 / 864)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 495, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-55 / 864))]

def nodeValue28 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 108)), (Sum.inl 71, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue29 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 108)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (65 / 432)), (Sum.inl 70, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue30 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (-5 / 54)), (Sum.inl 2, (-5 / 108)), (Sum.inl 69, (-5 / 27)), (Sum.inl 71, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue31 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (5 / 216)), (Sum.inl 69, (-5 / 27)), (Sum.inl 1, (35 / 216))]

def nodeValue32 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 108)), (Sum.inl 58, (5 / 432)), (Sum.inl 6, (5 / 216)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (-25 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 495, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue33 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (-5 / 144)), (Sum.inl 69, (-5 / 27)), (Sum.inl 70, (-5 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 1, (5 / 48))]

def nodeValue34 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 216)), (Sum.inl 71, (-10 / 27)), (Sum.inl 8, (-5 / 27))]

def nodeValue35 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 36)), (Sum.inl 58, (-5 / 144)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-5 / 144)), (Sum.inl 1, (5 / 48))]

def nodeValue36 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 54)), (Sum.inl 5, (-5 / 108)), (Sum.inl 256, (5 / 9)), (Sum.inl 2, (-5 / 216)), (Sum.inl 1, (-25 / 432))]

def nodeValue37 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 58, (-5 / 144)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-5 / 72)), (Sum.inl 495, (5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue38 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 36)), (Sum.inl 2, (5 / 36)), (Sum.inl 70, (5 / 9)), (Sum.inl 1, (5 / 36))]

def nodeValue39 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 71, (5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue40 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 69, (5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue41 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 36)), (Sum.inl 257, (5 / 9)), (Sum.inl 2, (5 / 48)), (Sum.inl 1, (-5 / 144))]

def nodeValue42 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 9)), (Sum.inl 58, (5 / 36)), (Sum.inl 2, (5 / 36)), (Sum.inl 1, (5 / 36))]

def nodeValue43 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 72)), (Sum.inl 2, (5 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-10 / 27)), (Sum.inl 82, (-5 / 27)), (Sum.inl 199, (5 / 18)), (Sum.inl 1, (35 / 432))]

def nodeValue44 : Sparse Master := [(Sum.inl 0, (7 / 144)), (Sum.inl 5, (5 / 36)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-55 / 432)), (Sum.inl 35, (-5 / 54)), (Sum.inl 82, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 3, (-5 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 128, (-5 / 27)), (Sum.inl 52, (-10 / 27)), (Sum.inl 201, (5 / 18)), (Sum.inl 1, (-5 / 48))]

def nodeValue45 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-25 / 216)), (Sum.inl 6, (-5 / 96)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (5 / 54)), (Sum.inl 82, (5 / 54)), (Sum.inl 1, (35 / 864))]

def nodeValue47 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (5 / 108)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 82, (5 / 54)), (Sum.inl 199, (-5 / 18)), (Sum.inl 1, (-5 / 432))]

def nodeValue48 : Sparse Master := [(Sum.inl 0, (13 / 288)), (Sum.inl 5, (55 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-5 / 432)), (Sum.inl 8, (5 / 54)), (Sum.inl 201, (-5 / 18))]

def nodeValue49 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 6, (25 / 144)), (Sum.inl 82, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue50 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 108)), (Sum.inl 2, (5 / 48)), (Sum.inl 128, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (5 / 72))]

def nodeValue51 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 144)), (Sum.inl 2, (5 / 72)), (Sum.inl 35, (5 / 54)), (Sum.inl 82, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 128, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 201, (-5 / 18))]

def nodeValue53 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (5 / 27)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (-5 / 27)), (Sum.inl 82, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue56 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 216)), (Sum.inl 201, (5 / 9)), (Sum.inl 1, (-5 / 216))]

def nodeValue58 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 9, (5 / 72)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (5 / 24)), (Sum.inl 6, (-5 / 216)), (Sum.inl 257, (-5 / 27)), (Sum.inl 260, (5 / 18)), (Sum.inl 60, (-25 / 54)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-20 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 128, (-10 / 27)), (Sum.inl 495, (-5 / 18)), (Sum.inl 52, (-20 / 27))]

def nodeValue59 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (-5 / 54)), (Sum.inl 2, (5 / 54)), (Sum.inl 128, (5 / 27)), (Sum.inl 495, (5 / 27)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (35 / 432))]

def nodeValue60 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 432)), (Sum.inl 257, (5 / 54)), (Sum.inl 260, (-5 / 18)), (Sum.inl 60, (5 / 54)), (Sum.inl 2, (5 / 864)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (5 / 864))]

def nodeValue61 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-5 / 108)), (Sum.inl 69, (-5 / 27)), (Sum.inl 70, (-5 / 54)), (Sum.inl 71, (-5 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 54)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-35 / 864))]

def nodeValue62 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (185 / 864)), (Sum.inl 70, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue63 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 18)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-35 / 432)), (Sum.inl 69, (-5 / 54)), (Sum.inl 71, (-10 / 27)), (Sum.inl 8, (-10 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue64 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (-5 / 108)), (Sum.inl 71, (5 / 54)), (Sum.inl 1, (-35 / 864))]

def nodeValue65 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 18)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-55 / 432)), (Sum.inl 69, (-5 / 18)), (Sum.inl 70, (-5 / 27)), (Sum.inl 7, (-5 / 9)), (Sum.inl 35, (-5 / 9)), (Sum.inl 3, (-5 / 9)), (Sum.inl 52, (-5 / 9)), (Sum.inl 1, (-5 / 216))]

def nodeValue66 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 144)), (Sum.inl 2, (5 / 48)), (Sum.inl 69, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (5 / 108))]

def nodeValue67 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (5 / 288)), (Sum.inl 257, (5 / 54)), (Sum.inl 60, (5 / 27)), (Sum.inl 2, (5 / 864)), (Sum.inl 35, (5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 128, (5 / 54)), (Sum.inl 495, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (-5 / 864))]

def nodeValue68 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-25 / 432)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-25 / 288))]

def nodeValue69 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 54)), (Sum.inl 2, (25 / 432)), (Sum.inl 71, (5 / 27)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (5 / 54))]

def nodeValue70 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 108)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-25 / 432)), (Sum.inl 1, (-35 / 432))]

def nodeValue71 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 27)), (Sum.inl 70, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue72 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 144)), (Sum.inl 69, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue73 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 257, (-5 / 27)), (Sum.inl 60, (-5 / 27)), (Sum.inl 2, (25 / 144)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (5 / 144))]

def nodeValue74 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 259, (-5 / 18)), (Sum.inl 260, (-5 / 18)), (Sum.inl 2, (-35 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 1, (-55 / 864))]

def nodeValue75 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 259, (5 / 9)), (Sum.inl 2, (-5 / 432)), (Sum.inl 1, (-25 / 432))]

def nodeValue76 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 260, (5 / 9)), (Sum.inl 2, (-25 / 432)), (Sum.inl 1, (-5 / 72))]

def nodeValue77 : Sparse Master := [(Sum.inl 0, (41 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (55 / 864)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 18)), (Sum.inl 8, (-5 / 54)), (Sum.inl 3, (-5 / 54)), (Sum.inl 52, (-5 / 54)), (Sum.inl 228, (5 / 18)), (Sum.inl 11, (-5 / 54)), (Sum.inl 26, (-5 / 54)), (Sum.inl 1, (25 / 864))]

def nodeValue78 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (-25 / 432)), (Sum.inl 2, (-25 / 432)), (Sum.inl 35, (5 / 54)), (Sum.inl 11, (5 / 54)), (Sum.inl 1, (5 / 144))]

def nodeValue79 : Sparse Master := [(Sum.inl 0, (49 / 864)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (-55 / 432)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-10 / 27)), (Sum.inl 1, (-35 / 216))]

def nodeValue80 : Sparse Master := [(Sum.inl 0, (13 / 288)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (-5 / 96)), (Sum.inl 2, (-5 / 108)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (5 / 144))]

def nodeValue81 : Sparse Master := [(Sum.inl 0, (13 / 288)), (Sum.inl 5, (5 / 24)), (Sum.inl 2, (5 / 216)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (25 / 864))]

def nodeValue83 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (5 / 27)), (Sum.inl 11, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (5 / 144))]

def nodeValue87 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (-5 / 216)), (Sum.inl 60, (5 / 27)), (Sum.inl 2, (5 / 288)), (Sum.inl 35, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 128, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (25 / 288))]

def nodeValue88 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (25 / 216)), (Sum.inl 2, (5 / 216)), (Sum.inl 128, (-5 / 27)), (Sum.inl 1, (5 / 72))]

def nodeValue89 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (25 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 228, (-5 / 18)), (Sum.inl 11, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue90 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-5 / 216)), (Sum.inl 35, (-5 / 27)), (Sum.inl 11, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue91 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (10 / 27)), (Sum.inl 6, (-55 / 864)), (Sum.inl 2, (-55 / 432)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-10 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue92 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-25 / 216)), (Sum.inl 6, (25 / 864)), (Sum.inl 2, (-5 / 108)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 1, (-35 / 864))]

def nodeValue93 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (5 / 48))]

def nodeValue94 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-25 / 432)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 108))]

def nodeValue95 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (35 / 432)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 27)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue96 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-5 / 108)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue97 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 6, (-5 / 144)), (Sum.inl 60, (-5 / 27)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (-5 / 27)), (Sum.inl 52, (-5 / 27))]

def nodeValue98 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (5 / 27)), (Sum.inl 2, (-5 / 108)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue99 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 5, (25 / 108)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue100 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (25 / 144)), (Sum.inl 1, (-5 / 72))]

def nodeValue101 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 59, (-5 / 18)), (Sum.inl 60, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 18)), (Sum.inl 128, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue102 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 6, (-5 / 144)), (Sum.inl 60, (-5 / 27)), (Sum.inl 2, (-5 / 48)), (Sum.inl 13, (-5 / 27)), (Sum.inl 128, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue103 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 36)), (Sum.inl 59, (5 / 9)), (Sum.inl 2, (-5 / 216)), (Sum.inl 1, (-25 / 432))]

def nodeValue104 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 6, (5 / 36)), (Sum.inl 2, (-5 / 72)), (Sum.inl 128, (5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue105 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 216)), (Sum.inl 35, (-5 / 27)), (Sum.inl 11, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 432))]

def nodeValue106 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 108)), (Sum.inl 228, (5 / 9))]

def nodeValue107 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 6, (-5 / 72)), (Sum.inl 2, (-5 / 72)), (Sum.inl 11, (5 / 9)), (Sum.inl 1, (-5 / 144))]

def nodeValue108 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-65 / 864)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (-5 / 96))]

def nodeValue109 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (25 / 108)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue110 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 108)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-5 / 108))]

def nodeValue111 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue112 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-5 / 72)), (Sum.inl 52, (5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue113 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (5 / 36)), (Sum.inl 2, (5 / 36)), (Sum.inl 35, (5 / 9)), (Sum.inl 1, (-5 / 144))]

def nodeValue114 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (5 / 27)), (Sum.inl 6, (-5 / 288)), (Sum.inl 257, (-5 / 54)), (Sum.inl 67, (-5 / 27)), (Sum.inl 2, (-25 / 432)), (Sum.inl 69, (-10 / 27)), (Sum.inl 70, (-10 / 27)), (Sum.inl 71, (-5 / 54)), (Sum.inl 7, (-5 / 9)), (Sum.inl 35, (-20 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-10 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 26, (-5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue115 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 432)), (Sum.inl 2, (35 / 432)), (Sum.inl 1, (-5 / 216))]

def nodeValue116 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-25 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 96)), (Sum.inl 69, (5 / 27)), (Sum.inl 70, (5 / 54)), (Sum.inl 71, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-25 / 864))]

def nodeValue117 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 257, (5 / 54)), (Sum.inl 67, (5 / 54)), (Sum.inl 2, (-5 / 216)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 27)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 18)), (Sum.inl 1, (-5 / 96))]

def nodeValue118 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (25 / 108)), (Sum.inl 6, (-5 / 216)), (Sum.inl 2, (-55 / 864)), (Sum.inl 69, (-5 / 27)), (Sum.inl 70, (-5 / 54)), (Sum.inl 71, (-5 / 27)), (Sum.inl 7, (-10 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 8, (-10 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (-25 / 288))]

def nodeValue119 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (35 / 864)), (Sum.inl 2, (-35 / 864)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 1, (-65 / 864))]

def nodeValue120 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 36)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-5 / 48)), (Sum.inl 69, (-5 / 54)), (Sum.inl 71, (-10 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue121 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 58, (-5 / 864)), (Sum.inl 6, (25 / 864)), (Sum.inl 2, (25 / 432)), (Sum.inl 71, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (-35 / 864))]

def nodeValue122 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (5 / 216)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (5 / 72)), (Sum.inl 69, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 495, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (-25 / 864))]

def nodeValue123 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 257, (5 / 54)), (Sum.inl 67, (5 / 27)), (Sum.inl 2, (-5 / 108)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (10 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 72))]

def nodeValue124 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (5 / 216)), (Sum.inl 69, (5 / 54)), (Sum.inl 71, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (-5 / 96))]

def nodeValue125 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (-5 / 54)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 288)), (Sum.inl 69, (-5 / 18)), (Sum.inl 70, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 18)), (Sum.inl 1, (35 / 216))]

def nodeValue126 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (-5 / 432)), (Sum.inl 69, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 1, (55 / 432))]

def nodeValue127 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (5 / 54))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue640 : Sparse Master := [(Sum.inr 640, (1 / 1))]

def nodeValue641 : Sparse Master := [(Sum.inr 641, (1 / 1))]

def nodeValue642 : Sparse Master := [(Sum.inr 642, (1 / 1))]

def nodeValue643 : Sparse Master := [(Sum.inr 643, (1 / 1))]

def nodeValue644 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 9, (-1 / 54)), (Sum.inl 58, (1 / 864)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (-1 / 144)), (Sum.inl 69, (-1 / 54)), (Sum.inl 71, (-2 / 27)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (-1 / 216))]

def nodeValue645 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 58, (-1 / 432)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (-1 / 216)), (Sum.inl 69, (1 / 27)), (Sum.inl 1, (-7 / 216))]

def nodeValue646 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (-1 / 54)), (Sum.inl 58, (1 / 864)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (7 / 864)), (Sum.inl 69, (-1 / 27)), (Sum.inl 70, (-1 / 54)), (Sum.inl 71, (-1 / 27)), (Sum.inl 7, (-1 / 54)), (Sum.inl 1, (13 / 864))]

def nodeValue647 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 58, (-1 / 432)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 108)), (Sum.inl 71, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue648 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 9, (1 / 54)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (1 / 144)), (Sum.inl 69, (1 / 27)), (Sum.inl 70, (1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 1, (-1 / 48))]

def nodeValue649 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 9, (1 / 54)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 216)), (Sum.inl 71, (2 / 27)), (Sum.inl 8, (1 / 27))]

def nodeValue650 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 9, (1 / 36)), (Sum.inl 58, (1 / 144)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (1 / 144)), (Sum.inl 1, (-1 / 48))]

def nodeValue651 : Sparse Master := [(Sum.inr 651, (1 / 1))]

def nodeValue652 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 58, (-1 / 432)), (Sum.inl 2, (-5 / 144)), (Sum.inl 70, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue653 : Sparse Master := [(Sum.inr 653, (1 / 1))]

def nodeValue654 : Sparse Master := [(Sum.inr 654, (1 / 1))]

def nodeValue655 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 9, (-1 / 36)), (Sum.inl 2, (-1 / 36)), (Sum.inl 70, (-1 / 9)), (Sum.inl 1, (-1 / 36))]

def nodeValue656 : Sparse Master := [(Sum.inr 656, (1 / 1))]

def nodeValue657 : Sparse Master := [(Sum.inr 657, (1 / 1))]

def nodeValue658 : Sparse Master := [(Sum.inr 658, (1 / 1))]

def nodeValue660 : Sparse Master := [(Sum.inr 660, (1 / 1))]

def nodeValue662 : Sparse Master := [(Sum.inr 662, (1 / 1))]

def nodeValue663 : Sparse Master := [(Sum.inr 663, (1 / 1))]

def nodeValue664 : Sparse Master := [(Sum.inr 664, (1 / 1))]

def nodeValue665 : Sparse Master := [(Sum.inr 665, (1 / 1))]

def nodeValue666 : Sparse Master := []

def nodeValue668 : Sparse Master := [(Sum.inr 668, (1 / 1))]

def nodeValue670 : Sparse Master := [(Sum.inr 670, (1 / 1))]

def nodeValue671 : Sparse Master := [(Sum.inr 671, (1 / 1))]

def nodeValue674 : Sparse Master := [(Sum.inr 674, (1 / 1))]

def nodeValue675 : Sparse Master := [(Sum.inr 675, (1 / 1))]

def nodeValue676 : Sparse Master := [(Sum.inr 676, (1 / 1))]

def nodeValue677 : Sparse Master := [(Sum.inr 677, (1 / 1))]

def nodeValue679 : Sparse Master := [(Sum.inr 679, (1 / 1))]

def nodeValue681 : Sparse Master := [(Sum.inr 681, (1 / 1))]

def nodeValue682 : Sparse Master := [(Sum.inr 682, (1 / 1))]

def nodeValue683 : Sparse Master := [(Sum.inr 683, (1 / 1))]

def nodeValue684 : Sparse Master := [(Sum.inr 684, (1 / 1))]

def nodeValue685 : Sparse Master := [(Sum.inr 685, (1 / 1))]

def nodeValue686 : Sparse Master := [(Sum.inr 686, (1 / 1))]

def nodeValue687 : Sparse Master := []

def nodeValue688 : Sparse Master := []

def nodeValue689 : Sparse Master := []

def nodeValue690 : Sparse Master := [(Sum.inr 690, (1 / 1))]

def nodeValue691 : Sparse Master := []

def nodeValue692 : Sparse Master := [(Sum.inr 692, (1 / 1))]

def nodeValue693 : Sparse Master := []

def nodeValue694 : Sparse Master := [(Sum.inr 694, (1 / 1))]

def nodeValue695 : Sparse Master := [(Sum.inr 695, (1 / 1))]

def nodeValue696 : Sparse Master := []

def nodeValue697 : Sparse Master := []

def nodeValue698 : Sparse Master := [(Sum.inr 698, (1 / 1))]

def nodeValue699 : Sparse Master := [(Sum.inr 699, (1 / 1))]

def nodeValue700 : Sparse Master := [(Sum.inr 700, (1 / 1))]

def nodeValue701 : Sparse Master := [(Sum.inr 701, (1 / 1))]

def nodeValue702 : Sparse Master := [(Sum.inr 702, (1 / 1))]

def nodeValue703 : Sparse Master := [(Sum.inr 703, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue704 : Sparse Master := [(Sum.inr 704, (1 / 1))]

def nodeValue705 : Sparse Master := [(Sum.inr 705, (1 / 1))]

def nodeValue706 : Sparse Master := [(Sum.inr 706, (1 / 1))]

def nodeValue707 : Sparse Master := [(Sum.inr 707, (1 / 1))]

def nodeValue708 : Sparse Master := [(Sum.inr 708, (1 / 1))]

def nodeValue710 : Sparse Master := [(Sum.inr 710, (1 / 1))]

def nodeValue712 : Sparse Master := []

def nodeValue713 : Sparse Master := [(Sum.inr 713, (1 / 1))]

def nodeValue714 : Sparse Master := []

def nodeValue715 : Sparse Master := [(Sum.inr 715, (1 / 1))]

def nodeValue716 : Sparse Master := [(Sum.inr 716, (1 / 1))]

def nodeValue717 : Sparse Master := []

def nodeValue719 : Sparse Master := [(Sum.inr 719, (1 / 1))]

def nodeValue720 : Sparse Master := [(Sum.inr 720, (1 / 1))]

def nodeValue724 : Sparse Master := [(Sum.inr 724, (1 / 1))]

def nodeValue725 : Sparse Master := [(Sum.inr 725, (1 / 1))]

def nodeValue726 : Sparse Master := [(Sum.inr 726, (1 / 1))]

def nodeValue729 : Sparse Master := [(Sum.inr 729, (1 / 1))]

def nodeValue730 : Sparse Master := [(Sum.inr 730, (1 / 1))]

def nodeValue731 : Sparse Master := [(Sum.inr 731, (1 / 1))]

def nodeValue732 : Sparse Master := [(Sum.inr 732, (1 / 1))]

def nodeValue733 : Sparse Master := [(Sum.inr 733, (1 / 1))]

def nodeValue734 : Sparse Master := [(Sum.inr 734, (1 / 1))]

def nodeValue735 : Sparse Master := [(Sum.inr 735, (1 / 1))]

def nodeValue736 : Sparse Master := [(Sum.inr 736, (1 / 1))]

def nodeValue737 : Sparse Master := [(Sum.inr 737, (1 / 1))]

def nodeValue738 : Sparse Master := [(Sum.inr 738, (1 / 1))]

def nodeValue739 : Sparse Master := [(Sum.inr 739, (1 / 1))]

def nodeValue740 : Sparse Master := [(Sum.inr 740, (1 / 1))]

def nodeValue741 : Sparse Master := [(Sum.inr 741, (1 / 1))]

def nodeValue742 : Sparse Master := [(Sum.inr 742, (1 / 1))]

def nodeValue743 : Sparse Master := [(Sum.inr 743, (1 / 1))]

def nodeValue744 : Sparse Master := [(Sum.inr 744, (1 / 1))]

def nodeValue746 : Sparse Master := [(Sum.inr 746, (1 / 1))]

def nodeValue748 : Sparse Master := [(Sum.inr 748, (1 / 1))]

def nodeValue749 : Sparse Master := [(Sum.inr 749, (1 / 1))]

def nodeValue750 : Sparse Master := [(Sum.inr 750, (1 / 1))]

def nodeValue751 : Sparse Master := [(Sum.inr 751, (1 / 1))]

def nodeValue752 : Sparse Master := [(Sum.inr 752, (1 / 1))]

def nodeValue753 : Sparse Master := [(Sum.inr 753, (1 / 1))]

def nodeValue754 : Sparse Master := [(Sum.inr 754, (1 / 1))]

def nodeValue755 : Sparse Master := [(Sum.inr 755, (1 / 1))]

def nodeValue756 : Sparse Master := [(Sum.inr 756, (1 / 1))]

def nodeValue758 : Sparse Master := [(Sum.inr 758, (1 / 1))]

def nodeValue760 : Sparse Master := [(Sum.inr 760, (1 / 1))]

def nodeValue761 : Sparse Master := [(Sum.inr 761, (1 / 1))]

def nodeValue762 : Sparse Master := [(Sum.inr 762, (1 / 1))]

def nodeValue763 : Sparse Master := [(Sum.inr 763, (1 / 1))]

def nodeValue764 : Sparse Master := [(Sum.inr 764, (1 / 1))]

def nodeValue765 : Sparse Master := [(Sum.inr 765, (1 / 1))]

def nodeValue766 : Sparse Master := []

def nodeValue767 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue768 : Sparse Master := []

def nodeValue769 : Sparse Master := [(Sum.inr 769, (1 / 1))]

def nodeValue770 : Sparse Master := []

def nodeValue771 : Sparse Master := [(Sum.inr 771, (1 / 1))]

def nodeValue773 : Sparse Master := [(Sum.inr 773, (1 / 1))]

def nodeValue774 : Sparse Master := [(Sum.inr 774, (1 / 1))]

def nodeValue776 : Sparse Master := [(Sum.inr 776, (1 / 1))]

def nodeValue778 : Sparse Master := [(Sum.inr 778, (1 / 1))]

def nodeValue780 : Sparse Master := [(Sum.inr 780, (1 / 1))]

def nodeValue781 : Sparse Master := [(Sum.inr 781, (1 / 1))]

def nodeValue782 : Sparse Master := [(Sum.inr 782, (1 / 1))]

def nodeValue783 : Sparse Master := [(Sum.inr 783, (1 / 1))]

def nodeValue784 : Sparse Master := [(Sum.inr 784, (1 / 1))]

def nodeValue785 : Sparse Master := [(Sum.inr 785, (1 / 1))]

def nodeValue786 : Sparse Master := [(Sum.inr 786, (1 / 1))]

def nodeValue787 : Sparse Master := [(Sum.inr 787, (1 / 1))]

def nodeValue789 : Sparse Master := [(Sum.inr 789, (1 / 1))]

def nodeValue790 : Sparse Master := [(Sum.inr 790, (1 / 1))]

def nodeValue791 : Sparse Master := [(Sum.inr 791, (1 / 1))]

def nodeValue793 : Sparse Master := [(Sum.inr 793, (1 / 1))]

def nodeValue794 : Sparse Master := [(Sum.inr 794, (1 / 1))]

def nodeValue795 : Sparse Master := [(Sum.inr 795, (1 / 1))]

def nodeValue796 : Sparse Master := [(Sum.inr 796, (1 / 1))]

def nodeValue797 : Sparse Master := [(Sum.inr 797, (1 / 1))]

def nodeValue798 : Sparse Master := [(Sum.inr 798, (1 / 1))]

def nodeValue799 : Sparse Master := [(Sum.inr 799, (1 / 1))]

def nodeValue800 : Sparse Master := [(Sum.inr 800, (1 / 1))]

def nodeValue801 : Sparse Master := [(Sum.inr 801, (1 / 1))]

def nodeValue803 : Sparse Master := [(Sum.inr 803, (1 / 1))]

def nodeValue804 : Sparse Master := [(Sum.inr 804, (1 / 1))]

def nodeValue805 : Sparse Master := []

def nodeValue806 : Sparse Master := []

def nodeValue807 : Sparse Master := [(Sum.inr 807, (1 / 1))]

def nodeValue808 : Sparse Master := [(Sum.inr 808, (1 / 1))]

def nodeValue809 : Sparse Master := []

def nodeValue810 : Sparse Master := []

def nodeValue811 : Sparse Master := [(Sum.inr 811, (1 / 1))]

def nodeValue812 : Sparse Master := []

def nodeValue813 : Sparse Master := [(Sum.inr 813, (1 / 1))]

def nodeValue814 : Sparse Master := [(Sum.inr 814, (1 / 1))]

def nodeValue815 : Sparse Master := [(Sum.inr 815, (1 / 1))]

def nodeValue816 : Sparse Master := []

def nodeValue817 : Sparse Master := []

def nodeValue818 : Sparse Master := [(Sum.inr 818, (1 / 1))]

def nodeValue819 : Sparse Master := [(Sum.inr 819, (1 / 1))]

def nodeValue820 : Sparse Master := [(Sum.inr 820, (1 / 1))]

def nodeValue822 : Sparse Master := [(Sum.inr 822, (1 / 1))]

def nodeValue823 : Sparse Master := [(Sum.inr 823, (1 / 1))]

def nodeValue824 : Sparse Master := [(Sum.inr 824, (1 / 1))]

def nodeValue825 : Sparse Master := [(Sum.inr 825, (1 / 1))]

def nodeValue826 : Sparse Master := [(Sum.inr 826, (1 / 1))]

def nodeValue827 : Sparse Master := [(Sum.inr 827, (1 / 1))]

def nodeValue828 : Sparse Master := [(Sum.inr 828, (1 / 1))]

def nodeValue829 : Sparse Master := [(Sum.inr 829, (1 / 1))]

def nodeValue830 : Sparse Master := [(Sum.inr 830, (1 / 1))]

def nodeValue831 : Sparse Master := [(Sum.inr 831, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue832 : Sparse Master := [(Sum.inr 832, (1 / 1))]

def nodeValue840 : Sparse Master := [(Sum.inr 840, (1 / 1))]

def nodeValue841 : Sparse Master := [(Sum.inr 841, (1 / 1))]

def nodeValue842 : Sparse Master := [(Sum.inr 842, (1 / 1))]

def nodeValue843 : Sparse Master := [(Sum.inr 843, (1 / 1))]

def nodeValue844 : Sparse Master := [(Sum.inr 844, (1 / 1))]

def nodeValue845 : Sparse Master := [(Sum.inr 845, (1 / 1))]

def nodeValue847 : Sparse Master := [(Sum.inr 847, (1 / 1))]

def nodeValue848 : Sparse Master := [(Sum.inr 848, (1 / 1))]

def nodeValue849 : Sparse Master := [(Sum.inr 849, (1 / 1))]

def nodeValue850 : Sparse Master := []

def nodeValue851 : Sparse Master := []

def nodeValue852 : Sparse Master := []

def nodeValue853 : Sparse Master := [(Sum.inr 853, (1 / 1))]

def nodeValue855 : Sparse Master := []

def nodeValue856 : Sparse Master := []

def nodeValue857 : Sparse Master := [(Sum.inr 857, (1 / 1))]

def nodeValue858 : Sparse Master := [(Sum.inr 858, (1 / 1))]

def nodeValue859 : Sparse Master := []

def nodeValue860 : Sparse Master := [(Sum.inr 860, (1 / 1))]

def nodeValue862 : Sparse Master := [(Sum.inr 862, (1 / 1))]

def nodeValue864 : Sparse Master := [(Sum.inr 864, (1 / 1))]

def nodeValue865 : Sparse Master := [(Sum.inr 865, (1 / 1))]

def nodeValue866 : Sparse Master := [(Sum.inr 866, (1 / 1))]

def nodeValue867 : Sparse Master := [(Sum.inr 867, (1 / 1))]

def nodeValue868 : Sparse Master := [(Sum.inr 868, (1 / 1))]

def nodeValue869 : Sparse Master := [(Sum.inr 869, (1 / 1))]

def nodeValue870 : Sparse Master := [(Sum.inr 870, (1 / 1))]

def nodeValue871 : Sparse Master := [(Sum.inr 871, (1 / 1))]

def nodeValue872 : Sparse Master := [(Sum.inr 872, (1 / 1))]

def nodeValue873 : Sparse Master := [(Sum.inr 873, (1 / 1))]

def nodeValue874 : Sparse Master := [(Sum.inr 874, (1 / 1))]

def nodeValue876 : Sparse Master := [(Sum.inr 876, (1 / 1))]

def nodeValue878 : Sparse Master := []

def nodeValue879 : Sparse Master := [(Sum.inr 879, (1 / 1))]

def nodeValue880 : Sparse Master := []

def nodeValue881 : Sparse Master := [(Sum.inr 881, (1 / 1))]

def nodeValue882 : Sparse Master := [(Sum.inr 882, (1 / 1))]

def nodeValue883 : Sparse Master := []

def nodeValue885 : Sparse Master := [(Sum.inr 885, (1 / 1))]

def nodeValue887 : Sparse Master := [(Sum.inr 887, (1 / 1))]

def nodeValue889 : Sparse Master := []

def nodeValue891 : Sparse Master := [(Sum.inr 891, (1 / 1))]

def nodeValue892 : Sparse Master := [(Sum.inr 892, (1 / 1))]

def nodeValue893 : Sparse Master := [(Sum.inr 893, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue897 : Sparse Master := [(Sum.inr 897, (1 / 1))]

def nodeValue898 : Sparse Master := [(Sum.inr 898, (1 / 1))]

def nodeValue899 : Sparse Master := [(Sum.inr 899, (1 / 1))]

def nodeValue900 : Sparse Master := [(Sum.inr 900, (1 / 1))]

def nodeValue901 : Sparse Master := [(Sum.inr 901, (1 / 1))]

def nodeValue902 : Sparse Master := [(Sum.inr 902, (1 / 1))]

def nodeValue903 : Sparse Master := [(Sum.inr 903, (1 / 1))]

def nodeValue904 : Sparse Master := []

def nodeValue905 : Sparse Master := [(Sum.inr 905, (1 / 1))]

def nodeValue906 : Sparse Master := [(Sum.inr 906, (1 / 1))]

def nodeValue907 : Sparse Master := []

def nodeValue908 : Sparse Master := [(Sum.inr 908, (1 / 1))]

def nodeValue909 : Sparse Master := [(Sum.inr 909, (1 / 1))]

def nodeValue910 : Sparse Master := [(Sum.inr 910, (1 / 1))]

def nodeValue911 : Sparse Master := [(Sum.inr 911, (1 / 1))]

def nodeValue912 : Sparse Master := [(Sum.inr 912, (1 / 1))]

def nodeValue913 : Sparse Master := [(Sum.inr 913, (1 / 1))]

def nodeValue914 : Sparse Master := [(Sum.inr 914, (1 / 1))]

def nodeValue915 : Sparse Master := [(Sum.inr 915, (1 / 1))]

def nodeValue916 : Sparse Master := [(Sum.inr 916, (1 / 1))]

def nodeValue917 : Sparse Master := [(Sum.inr 917, (1 / 1))]

def nodeValue918 : Sparse Master := []

def nodeValue919 : Sparse Master := [(Sum.inr 919, (1 / 1))]

def nodeValue920 : Sparse Master := []

def nodeValue921 : Sparse Master := [(Sum.inr 921, (1 / 1))]

def nodeValue922 : Sparse Master := [(Sum.inr 922, (1 / 1))]

def nodeValue923 : Sparse Master := [(Sum.inr 923, (1 / 1))]

def nodeValue924 : Sparse Master := [(Sum.inr 924, (1 / 1))]

def nodeValue925 : Sparse Master := [(Sum.inr 925, (1 / 1))]

def nodeValue927 : Sparse Master := [(Sum.inr 927, (1 / 1))]

def nodeValue928 : Sparse Master := [(Sum.inr 928, (1 / 1))]

def nodeValue929 : Sparse Master := [(Sum.inr 929, (1 / 1))]

def nodeValue930 : Sparse Master := [(Sum.inr 930, (1 / 1))]

def nodeValue931 : Sparse Master := [(Sum.inr 931, (1 / 1))]

def nodeValue932 : Sparse Master := [(Sum.inr 932, (1 / 1))]

def nodeValue933 : Sparse Master := [(Sum.inr 933, (1 / 1))]

def nodeValue934 : Sparse Master := [(Sum.inr 934, (1 / 1))]

def nodeValue935 : Sparse Master := [(Sum.inr 935, (1 / 1))]

def nodeValue936 : Sparse Master := [(Sum.inr 936, (1 / 1))]

def nodeValue937 : Sparse Master := [(Sum.inr 937, (1 / 1))]

def nodeValue938 : Sparse Master := [(Sum.inr 938, (1 / 1))]

def nodeValue939 : Sparse Master := [(Sum.inr 939, (1 / 1))]

def nodeValue940 : Sparse Master := [(Sum.inr 940, (1 / 1))]

def nodeValue941 : Sparse Master := [(Sum.inr 941, (1 / 1))]

def nodeValue942 : Sparse Master := [(Sum.inr 942, (1 / 1))]

def nodeValue943 : Sparse Master := [(Sum.inr 943, (1 / 1))]

def nodeValue944 : Sparse Master := [(Sum.inr 944, (1 / 1))]

def nodeValue945 : Sparse Master := [(Sum.inr 945, (1 / 1))]

def nodeValue946 : Sparse Master := [(Sum.inr 946, (1 / 1))]

def nodeValue947 : Sparse Master := [(Sum.inr 947, (1 / 1))]

def nodeValue948 : Sparse Master := [(Sum.inr 948, (1 / 1))]

def nodeValue949 : Sparse Master := [(Sum.inr 949, (1 / 1))]

def nodeValue950 : Sparse Master := [(Sum.inr 950, (1 / 1))]

def nodeValue951 : Sparse Master := [(Sum.inr 951, (1 / 1))]

def nodeValue952 : Sparse Master := [(Sum.inr 952, (1 / 1))]

def nodeValue953 : Sparse Master := [(Sum.inr 953, (1 / 1))]

def nodeValue954 : Sparse Master := [(Sum.inr 954, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue971 : Sparse Master := []

def nodeValue972 : Sparse Master := [(Sum.inr 972, (1 / 1))]

def nodeValue973 : Sparse Master := [(Sum.inr 973, (1 / 1))]

def nodeValue974 : Sparse Master := []

def nodeValue975 : Sparse Master := [(Sum.inr 975, (1 / 1))]

def nodeValue976 : Sparse Master := []

def nodeValue977 : Sparse Master := [(Sum.inr 977, (1 / 1))]

def nodeValue978 : Sparse Master := []

def nodeValue979 : Sparse Master := [(Sum.inr 979, (1 / 1))]

def nodeValue980 : Sparse Master := [(Sum.inr 980, (1 / 1))]

def nodeValue981 : Sparse Master := [(Sum.inr 981, (1 / 1))]

def nodeValue982 : Sparse Master := [(Sum.inr 982, (1 / 1))]

def nodeValue983 : Sparse Master := [(Sum.inr 983, (1 / 1))]

def nodeValue984 : Sparse Master := [(Sum.inr 984, (1 / 1))]

def nodeValue985 : Sparse Master := [(Sum.inr 985, (1 / 1))]

def nodeValue986 : Sparse Master := [(Sum.inr 986, (1 / 1))]

def nodeValue987 : Sparse Master := [(Sum.inr 987, (1 / 1))]

def nodeValue988 : Sparse Master := [(Sum.inr 988, (1 / 1))]

def nodeValue989 : Sparse Master := [(Sum.inr 989, (1 / 1))]

def nodeValue990 : Sparse Master := [(Sum.inr 990, (1 / 1))]

def nodeValue991 : Sparse Master := [(Sum.inr 991, (1 / 1))]

def nodeValue992 : Sparse Master := [(Sum.inr 992, (1 / 1))]

def nodeValue993 : Sparse Master := [(Sum.inr 993, (1 / 1))]

def nodeValue994 : Sparse Master := [(Sum.inr 994, (1 / 1))]

def nodeValue995 : Sparse Master := [(Sum.inr 995, (1 / 1))]

def nodeValue996 : Sparse Master := []

def nodeValue997 : Sparse Master := [(Sum.inr 997, (1 / 1))]

def nodeValue998 : Sparse Master := [(Sum.inr 998, (1 / 1))]

def nodeValue999 : Sparse Master := [(Sum.inr 999, (1 / 1))]

def nodeValue1000 : Sparse Master := [(Sum.inr 1000, (1 / 1))]

def nodeValue1001 : Sparse Master := [(Sum.inr 1001, (1 / 1))]

def nodeValue1002 : Sparse Master := [(Sum.inr 1002, (1 / 1))]

def nodeValue1003 : Sparse Master := []

def nodeValue1004 : Sparse Master := []

def nodeValue1005 : Sparse Master := [(Sum.inr 1005, (1 / 1))]

def nodeValue1006 : Sparse Master := [(Sum.inr 1006, (1 / 1))]

def nodeValue1007 : Sparse Master := []

def nodeValue1008 : Sparse Master := [(Sum.inr 1008, (1 / 1))]

def nodeValue1009 : Sparse Master := [(Sum.inr 1009, (1 / 1))]

def nodeValue1010 : Sparse Master := [(Sum.inr 1010, (1 / 1))]

def nodeValue1011 : Sparse Master := [(Sum.inr 1011, (1 / 1))]

def nodeValue1012 : Sparse Master := [(Sum.inr 1012, (1 / 1))]

def nodeValue1013 : Sparse Master := []

def nodeValue1014 : Sparse Master := [(Sum.inr 1014, (1 / 1))]

def nodeValue1015 : Sparse Master := [(Sum.inr 1015, (1 / 1))]

def nodeValue1016 : Sparse Master := [(Sum.inr 1016, (1 / 1))]

def nodeValue1017 : Sparse Master := [(Sum.inr 1017, (1 / 1))]

def nodeValue1018 : Sparse Master := [(Sum.inr 1018, (1 / 1))]

def nodeValue1019 : Sparse Master := [(Sum.inr 1019, (1 / 1))]

def nodeValue1020 : Sparse Master := []

def nodeValue1021 : Sparse Master := [(Sum.inr 1021, (1 / 1))]

def nodeValue1022 : Sparse Master := [(Sum.inr 1022, (1 / 1))]

def nodeValue1023 : Sparse Master := [(Sum.inr 1023, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1024 : Sparse Master := [(Sum.inr 1024, (1 / 1))]

def nodeValue1025 : Sparse Master := [(Sum.inr 1025, (1 / 1))]

def nodeValue1026 : Sparse Master := [(Sum.inr 1026, (1 / 1))]

def nodeValue1027 : Sparse Master := [(Sum.inr 1027, (1 / 1))]

def nodeValue1028 : Sparse Master := [(Sum.inr 1028, (1 / 1))]

def nodeValue1029 : Sparse Master := [(Sum.inr 1029, (1 / 1))]

def nodeValue1030 : Sparse Master := [(Sum.inr 1030, (1 / 1))]

def nodeValue1031 : Sparse Master := [(Sum.inr 1031, (1 / 1))]

def nodeValue1032 : Sparse Master := [(Sum.inr 1032, (1 / 1))]

def nodeValue1033 : Sparse Master := [(Sum.inr 1033, (1 / 1))]

def nodeValue1034 : Sparse Master := [(Sum.inr 1034, (1 / 1))]

def nodeValue1035 : Sparse Master := [(Sum.inr 1035, (1 / 1))]

def nodeValue1036 : Sparse Master := [(Sum.inr 1036, (1 / 1))]

def nodeValue1037 : Sparse Master := [(Sum.inr 1037, (1 / 1))]

def nodeValue1038 : Sparse Master := []

def nodeValue1039 : Sparse Master := [(Sum.inr 1039, (1 / 1))]

def nodeValue1040 : Sparse Master := [(Sum.inr 1040, (1 / 1))]

def nodeValue1041 : Sparse Master := [(Sum.inr 1041, (1 / 1))]

def nodeValue1042 : Sparse Master := [(Sum.inr 1042, (1 / 1))]

def nodeValue1043 : Sparse Master := [(Sum.inr 1043, (1 / 1))]

def nodeValue1044 : Sparse Master := [(Sum.inr 1044, (1 / 1))]

def nodeValue1045 : Sparse Master := [(Sum.inr 1045, (1 / 1))]

def nodeValue1046 : Sparse Master := [(Sum.inr 1046, (1 / 1))]

def nodeValue1047 : Sparse Master := [(Sum.inr 1047, (1 / 1))]

def nodeValue1048 : Sparse Master := [(Sum.inr 1048, (1 / 1))]

def nodeValue1049 : Sparse Master := [(Sum.inr 1049, (1 / 1))]

def nodeValue1050 : Sparse Master := [(Sum.inr 1050, (1 / 1))]

def nodeValue1051 : Sparse Master := [(Sum.inr 1051, (1 / 1))]

def nodeValue1052 : Sparse Master := [(Sum.inr 1052, (1 / 1))]

def nodeValue1053 : Sparse Master := [(Sum.inr 1053, (1 / 1))]

def nodeValue1054 : Sparse Master := [(Sum.inr 1054, (1 / 1))]

def nodeValue1055 : Sparse Master := [(Sum.inr 1055, (1 / 1))]

def nodeValue1056 : Sparse Master := [(Sum.inr 1056, (1 / 1))]

def nodeValue1057 : Sparse Master := [(Sum.inr 1057, (1 / 1))]

def nodeValue1058 : Sparse Master := [(Sum.inr 1058, (1 / 1))]

def nodeValue1059 : Sparse Master := [(Sum.inr 1059, (1 / 1))]

def nodeValue1060 : Sparse Master := [(Sum.inr 1060, (1 / 1))]

def nodeValue1061 : Sparse Master := [(Sum.inr 1061, (1 / 1))]

def nodeValue1062 : Sparse Master := [(Sum.inr 1062, (1 / 1))]

def nodeValue1063 : Sparse Master := [(Sum.inr 1063, (1 / 1))]

def nodeValue1064 : Sparse Master := [(Sum.inr 1064, (1 / 1))]

def nodeValue1066 : Sparse Master := [(Sum.inr 1066, (1 / 1))]

def nodeValue1067 : Sparse Master := [(Sum.inr 1067, (1 / 1))]

def nodeValue1068 : Sparse Master := [(Sum.inr 1068, (1 / 1))]

def nodeValue1069 : Sparse Master := [(Sum.inr 1069, (1 / 1))]

def nodeValue1070 : Sparse Master := [(Sum.inr 1070, (1 / 1))]

def nodeValue1071 : Sparse Master := [(Sum.inr 1071, (1 / 1))]

def nodeValue1072 : Sparse Master := [(Sum.inr 1072, (1 / 1))]

def nodeValue1073 : Sparse Master := [(Sum.inr 1073, (1 / 1))]

def nodeValue1074 : Sparse Master := [(Sum.inr 1074, (1 / 1))]

def nodeValue1075 : Sparse Master := [(Sum.inr 1075, (1 / 1))]

def nodeValue1076 : Sparse Master := [(Sum.inr 1076, (1 / 1))]

def nodeValue1077 : Sparse Master := [(Sum.inr 1077, (1 / 1))]

def nodeValue1078 : Sparse Master := [(Sum.inr 1078, (1 / 1))]

def nodeValue1079 : Sparse Master := [(Sum.inr 1079, (1 / 1))]

def nodeValue1080 : Sparse Master := [(Sum.inr 1080, (1 / 1))]

def nodeValue1081 : Sparse Master := []

def nodeValue1082 : Sparse Master := []

def nodeValue1083 : Sparse Master := [(Sum.inr 1083, (1 / 1))]

def nodeValue1084 : Sparse Master := [(Sum.inr 1084, (1 / 1))]

def nodeValue1085 : Sparse Master := []

def nodeValue1086 : Sparse Master := []

def nodeValue1087 : Sparse Master := [(Sum.inr 1087, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1088 : Sparse Master := [(Sum.inr 1088, (1 / 1))]

def nodeValue1089 : Sparse Master := []

def nodeValue1091 : Sparse Master := [(Sum.inr 1091, (1 / 1))]

def nodeValue1092 : Sparse Master := [(Sum.inr 1092, (1 / 1))]

def nodeValue1093 : Sparse Master := [(Sum.inr 1093, (1 / 1))]

def nodeValue1094 : Sparse Master := [(Sum.inr 1094, (1 / 1))]

def nodeValue1095 : Sparse Master := []

def nodeValue1096 : Sparse Master := []

def nodeValue1097 : Sparse Master := [(Sum.inr 1097, (1 / 1))]

def nodeValue1098 : Sparse Master := [(Sum.inr 1098, (1 / 1))]

def nodeValue1099 : Sparse Master := [(Sum.inr 1099, (1 / 1))]

def nodeValue1100 : Sparse Master := [(Sum.inr 1100, (1 / 1))]

def nodeValue1101 : Sparse Master := [(Sum.inr 1101, (1 / 1))]

def nodeValue1102 : Sparse Master := [(Sum.inr 1102, (1 / 1))]

def nodeValue1103 : Sparse Master := [(Sum.inr 1103, (1 / 1))]

def nodeValue1104 : Sparse Master := [(Sum.inr 1104, (1 / 1))]

def nodeValue1105 : Sparse Master := [(Sum.inr 1105, (1 / 1))]

def nodeValue1106 : Sparse Master := [(Sum.inr 1106, (1 / 1))]

def nodeValue1107 : Sparse Master := [(Sum.inr 1107, (1 / 1))]

def nodeValue1108 : Sparse Master := [(Sum.inr 1108, (1 / 1))]

def nodeValue1109 : Sparse Master := [(Sum.inr 1109, (1 / 1))]

def nodeValue1110 : Sparse Master := [(Sum.inr 1110, (1 / 1))]

def nodeValue1111 : Sparse Master := [(Sum.inr 1111, (1 / 1))]

def nodeValue1112 : Sparse Master := [(Sum.inr 1112, (1 / 1))]

def nodeValue1113 : Sparse Master := [(Sum.inr 1113, (1 / 1))]

def nodeValue1114 : Sparse Master := [(Sum.inr 1114, (1 / 1))]

def nodeValue1115 : Sparse Master := [(Sum.inr 1115, (1 / 1))]

def nodeValue1116 : Sparse Master := [(Sum.inr 1116, (1 / 1))]

def nodeValue1117 : Sparse Master := [(Sum.inr 1117, (1 / 1))]

def nodeValue1118 : Sparse Master := [(Sum.inr 1118, (1 / 1))]

def nodeValue1119 : Sparse Master := [(Sum.inr 1119, (1 / 1))]

def nodeValue1120 : Sparse Master := [(Sum.inr 1120, (1 / 1))]

def nodeValue1121 : Sparse Master := [(Sum.inr 1121, (1 / 1))]

def nodeValue1122 : Sparse Master := [(Sum.inr 1122, (1 / 1))]

def nodeValue1123 : Sparse Master := [(Sum.inr 1123, (1 / 1))]

def nodeValue1124 : Sparse Master := [(Sum.inr 1124, (1 / 1))]

def nodeValue1125 : Sparse Master := [(Sum.inr 1125, (1 / 1))]

def nodeValue1126 : Sparse Master := [(Sum.inr 1126, (1 / 1))]

def nodeValue1127 : Sparse Master := [(Sum.inr 1127, (1 / 1))]

def nodeValue1128 : Sparse Master := [(Sum.inr 1128, (1 / 1))]

def nodeValue1129 : Sparse Master := [(Sum.inr 1129, (1 / 1))]

def nodeValue1130 : Sparse Master := [(Sum.inr 1130, (1 / 1))]

def nodeValue1131 : Sparse Master := [(Sum.inr 1131, (1 / 1))]

def nodeValue1132 : Sparse Master := [(Sum.inr 1132, (1 / 1))]

def nodeValue1133 : Sparse Master := [(Sum.inr 1133, (1 / 1))]

def nodeValue1134 : Sparse Master := [(Sum.inr 1134, (1 / 1))]

def nodeValue1135 : Sparse Master := [(Sum.inr 1135, (1 / 1))]

def nodeValue1136 : Sparse Master := [(Sum.inr 1136, (1 / 1))]

def nodeValue1137 : Sparse Master := [(Sum.inr 1137, (1 / 1))]

def nodeValue1138 : Sparse Master := [(Sum.inr 1138, (1 / 1))]

def nodeValue1139 : Sparse Master := [(Sum.inr 1139, (1 / 1))]

def nodeValue1140 : Sparse Master := [(Sum.inr 1140, (1 / 1))]

def nodeValue1141 : Sparse Master := [(Sum.inr 1141, (1 / 1))]

def nodeValue1142 : Sparse Master := [(Sum.inr 1142, (1 / 1))]

def nodeValue1143 : Sparse Master := [(Sum.inr 1143, (1 / 1))]

def nodeValue1144 : Sparse Master := [(Sum.inr 1144, (1 / 1))]

def nodeValue1145 : Sparse Master := [(Sum.inr 1145, (1 / 1))]

def nodeValue1146 : Sparse Master := [(Sum.inr 1146, (1 / 1))]

def nodeValue1147 : Sparse Master := [(Sum.inr 1147, (1 / 1))]

def nodeValue1148 : Sparse Master := [(Sum.inr 1148, (1 / 1))]

def nodeValue1149 : Sparse Master := [(Sum.inr 1149, (1 / 1))]

def nodeValue1150 : Sparse Master := [(Sum.inr 1150, (1 / 1))]

def nodeValue1151 : Sparse Master := [(Sum.inr 1151, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1152 : Sparse Master := [(Sum.inr 1152, (1 / 1))]

def nodeValue1153 : Sparse Master := [(Sum.inr 1153, (1 / 1))]

def nodeValue1154 : Sparse Master := [(Sum.inr 1154, (1 / 1))]

def nodeValue1155 : Sparse Master := [(Sum.inr 1155, (1 / 1))]

def nodeValue1156 : Sparse Master := [(Sum.inr 1156, (1 / 1))]

def nodeValue1157 : Sparse Master := [(Sum.inr 1157, (1 / 1))]

def nodeValue1158 : Sparse Master := [(Sum.inr 1158, (1 / 1))]

def nodeValue1159 : Sparse Master := [(Sum.inr 1159, (1 / 1))]

def nodeValue1160 : Sparse Master := [(Sum.inr 1160, (1 / 1))]

def nodeValue1161 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 9, (1 / 54)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 288)), (Sum.inl 69, (1 / 18)), (Sum.inl 70, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 18)), (Sum.inl 1, (-7 / 216))]

def nodeValue1162 : Sparse Master := [(Sum.inl 0, (-7 / 1440)), (Sum.inl 9, (1 / 54)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-1 / 36)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (1 / 48)), (Sum.inl 69, (1 / 54)), (Sum.inl 71, (2 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1163 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 58, (1 / 864)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (1 / 432)), (Sum.inl 69, (-1 / 54)), (Sum.inl 7, (-1 / 54)), (Sum.inl 1, (-11 / 432))]

def nodeValue1164 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 9, (1 / 54)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (1 / 216)), (Sum.inl 2, (11 / 864)), (Sum.inl 69, (1 / 27)), (Sum.inl 70, (1 / 54)), (Sum.inl 71, (1 / 27)), (Sum.inl 7, (2 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 8, (2 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue1165 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 58, (1 / 864)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-5 / 432)), (Sum.inl 71, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue1166 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 9, (-1 / 108)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (1 / 432)), (Sum.inl 69, (-1 / 54)), (Sum.inl 70, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-1 / 54))]

def nodeValue1167 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 9, (-1 / 108)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (1 / 432)), (Sum.inl 71, (-1 / 27)), (Sum.inl 1, (-1 / 216))]

def nodeValue1168 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 9, (-1 / 108)), (Sum.inl 58, (-1 / 432)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (1 / 216)), (Sum.inl 2, (-1 / 432)), (Sum.inl 1, (-1 / 48))]

def nodeValue1169 : Sparse Master := [(Sum.inr 1169, (1 / 1))]

def nodeValue1170 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 58, (1 / 864)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-7 / 864)), (Sum.inl 2, (7 / 864)), (Sum.inl 70, (-1 / 54)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 1, (13 / 864))]

def nodeValue1171 : Sparse Master := [(Sum.inr 1171, (1 / 1))]

def nodeValue1172 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 9, (-1 / 108)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (-1 / 216)), (Sum.inl 69, (-1 / 54)), (Sum.inl 71, (-1 / 54)), (Sum.inl 7, (-1 / 27)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (1 / 96))]

def nodeValue1173 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (-1 / 108)), (Sum.inl 58, (-1 / 432)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 108)), (Sum.inl 2, (5 / 432)), (Sum.inl 1, (7 / 432))]

def nodeValue1174 : Sparse Master := [(Sum.inr 1174, (1 / 1))]

def nodeValue1175 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 9, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-1 / 432)), (Sum.inl 69, (1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 1, (-1 / 48))]

def nodeValue1176 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 9, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-1 / 432)), (Sum.inl 71, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 72))]

def nodeValue1177 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 216)), (Sum.inl 70, (1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 1, (-1 / 48))]

def nodeValue1178 : Sparse Master := [(Sum.inr 1178, (1 / 1))]

def nodeValue1179 : Sparse Master := [(Sum.inr 1179, (1 / 1))]

def nodeValue1180 : Sparse Master := [(Sum.inr 1180, (1 / 1))]

def nodeValue1181 : Sparse Master := [(Sum.inr 1181, (1 / 1))]

def nodeValue1182 : Sparse Master := [(Sum.inr 1182, (1 / 1))]

def nodeValue1183 : Sparse Master := [(Sum.inr 1183, (1 / 1))]

def nodeValue1184 : Sparse Master := [(Sum.inr 1184, (1 / 1))]

def nodeValue1185 : Sparse Master := [(Sum.inr 1185, (1 / 1))]

def nodeValue1186 : Sparse Master := [(Sum.inr 1186, (1 / 1))]

def nodeValue1187 : Sparse Master := [(Sum.inr 1187, (1 / 1))]

def nodeValue1188 : Sparse Master := [(Sum.inr 1188, (1 / 1))]

def nodeValue1189 : Sparse Master := [(Sum.inr 1189, (1 / 1))]

def nodeValue1190 : Sparse Master := [(Sum.inr 1190, (1 / 1))]

def nodeValue1191 : Sparse Master := [(Sum.inr 1191, (1 / 1))]

def nodeValue1192 : Sparse Master := [(Sum.inr 1192, (1 / 1))]

def nodeValue1193 : Sparse Master := [(Sum.inr 1193, (1 / 1))]

def nodeValue1194 : Sparse Master := [(Sum.inr 1194, (1 / 1))]

def nodeValue1195 : Sparse Master := [(Sum.inr 1195, (1 / 1))]

def nodeValue1196 : Sparse Master := [(Sum.inr 1196, (1 / 1))]

def nodeValue1197 : Sparse Master := [(Sum.inr 1197, (1 / 1))]

def nodeValue1198 : Sparse Master := [(Sum.inr 1198, (1 / 1))]

def nodeValue1199 : Sparse Master := [(Sum.inr 1199, (1 / 1))]

def nodeValue1200 : Sparse Master := [(Sum.inr 1200, (1 / 1))]

def nodeValue1201 : Sparse Master := [(Sum.inr 1201, (1 / 1))]

def nodeValue1202 : Sparse Master := [(Sum.inr 1202, (1 / 1))]

def nodeValue1203 : Sparse Master := [(Sum.inr 1203, (1 / 1))]

def nodeValue1204 : Sparse Master := [(Sum.inr 1204, (1 / 1))]

def nodeValue1205 : Sparse Master := [(Sum.inr 1205, (1 / 1))]

def nodeValue1206 : Sparse Master := [(Sum.inr 1206, (1 / 1))]

def nodeValue1208 : Sparse Master := [(Sum.inr 1208, (1 / 1))]

def nodeValue1209 : Sparse Master := [(Sum.inr 1209, (1 / 1))]

def nodeValue1210 : Sparse Master := [(Sum.inr 1210, (1 / 1))]

def nodeValue1211 : Sparse Master := [(Sum.inr 1211, (1 / 1))]

def nodeValue1212 : Sparse Master := [(Sum.inr 1212, (1 / 1))]

def nodeValue1213 : Sparse Master := [(Sum.inr 1213, (1 / 1))]

def nodeValue1214 : Sparse Master := [(Sum.inr 1214, (1 / 1))]

def nodeValue1215 : Sparse Master := [(Sum.inr 1215, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1216 : Sparse Master := [(Sum.inr 1216, (1 / 1))]

def nodeValue1217 : Sparse Master := [(Sum.inr 1217, (1 / 1))]

def nodeValue1218 : Sparse Master := [(Sum.inr 1218, (1 / 1))]

def nodeValue1219 : Sparse Master := [(Sum.inr 1219, (1 / 1))]

def nodeValue1220 : Sparse Master := [(Sum.inr 1220, (1 / 1))]

def nodeValue1221 : Sparse Master := [(Sum.inr 1221, (1 / 1))]

def nodeValue1222 : Sparse Master := [(Sum.inr 1222, (1 / 1))]

def nodeValue1224 : Sparse Master := [(Sum.inr 1224, (1 / 1))]

def nodeValue1226 : Sparse Master := [(Sum.inr 1226, (1 / 1))]

def nodeValue1227 : Sparse Master := [(Sum.inr 1227, (1 / 1))]

def nodeValue1228 : Sparse Master := [(Sum.inr 1228, (1 / 1))]

def nodeValue1229 : Sparse Master := [(Sum.inr 1229, (1 / 1))]

def nodeValue1230 : Sparse Master := [(Sum.inr 1230, (1 / 1))]

def nodeValue1231 : Sparse Master := [(Sum.inr 1231, (1 / 1))]

def nodeValue1233 : Sparse Master := [(Sum.inr 1233, (1 / 1))]

def nodeValue1234 : Sparse Master := [(Sum.inr 1234, (1 / 1))]

def nodeValue1235 : Sparse Master := [(Sum.inr 1235, (1 / 1))]

def nodeValue1236 : Sparse Master := [(Sum.inr 1236, (1 / 1))]

def nodeValue1237 : Sparse Master := [(Sum.inr 1237, (1 / 1))]

def nodeValue1238 : Sparse Master := [(Sum.inr 1238, (1 / 1))]

def nodeValue1239 : Sparse Master := [(Sum.inr 1239, (1 / 1))]

def nodeValue1240 : Sparse Master := [(Sum.inr 1240, (1 / 1))]

def nodeValue1241 : Sparse Master := [(Sum.inr 1241, (1 / 1))]

def nodeValue1242 : Sparse Master := [(Sum.inr 1242, (1 / 1))]

def nodeValue1243 : Sparse Master := [(Sum.inr 1243, (1 / 1))]

def nodeValue1244 : Sparse Master := [(Sum.inr 1244, (1 / 1))]

def nodeValue1245 : Sparse Master := [(Sum.inr 1245, (1 / 1))]

def nodeValue1246 : Sparse Master := [(Sum.inr 1246, (1 / 1))]

def nodeValue1247 : Sparse Master := [(Sum.inr 1247, (1 / 1))]

def nodeValue1248 : Sparse Master := [(Sum.inr 1248, (1 / 1))]

def nodeValue1249 : Sparse Master := [(Sum.inr 1249, (1 / 1))]

def nodeValue1250 : Sparse Master := [(Sum.inr 1250, (1 / 1))]

def nodeValue1252 : Sparse Master := [(Sum.inr 1252, (1 / 1))]

def nodeValue1253 : Sparse Master := [(Sum.inr 1253, (1 / 1))]

def nodeValue1255 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (-5 / 144)), (Sum.inl 82, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1256 : Sparse Master := [(Sum.inr 1256, (1 / 1))]

def nodeValue1257 : Sparse Master := [(Sum.inr 1257, (1 / 1))]

def nodeValue1258 : Sparse Master := [(Sum.inr 1258, (1 / 1))]

def nodeValue1259 : Sparse Master := [(Sum.inr 1259, (1 / 1))]

def nodeValue1260 : Sparse Master := [(Sum.inr 1260, (1 / 1))]

def nodeValue1261 : Sparse Master := [(Sum.inr 1261, (1 / 1))]

def nodeValue1262 : Sparse Master := [(Sum.inr 1262, (1 / 1))]

def nodeValue1263 : Sparse Master := [(Sum.inr 1263, (1 / 1))]

def nodeValue1264 : Sparse Master := [(Sum.inr 1264, (1 / 1))]

def nodeValue1265 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 5, (-2 / 27)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (41 / 864)), (Sum.inl 7, (1 / 9)), (Sum.inl 35, (1 / 27)), (Sum.inl 8, (1 / 9)), (Sum.inl 3, (1 / 18)), (Sum.inl 1, (5 / 432))]

def nodeValue1266 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (-1 / 72)), (Sum.inl 7, (-1 / 54)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (-5 / 432))]

def nodeValue1267 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (-1 / 96)), (Sum.inl 7, (-1 / 27)), (Sum.inl 35, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (1 / 96))]

def nodeValue1268 : Sparse Master := [(Sum.inr 1268, (1 / 1))]

def nodeValue1269 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 108)), (Sum.inl 2, (1 / 72)), (Sum.inl 1, (1 / 54))]

def nodeValue1270 : Sparse Master := [(Sum.inr 1270, (1 / 1))]

def nodeValue1271 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (1 / 108)), (Sum.inl 2, (1 / 108)), (Sum.inl 35, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue1272 : Sparse Master := [(Sum.inr 1272, (1 / 1))]

def nodeValue1273 : Sparse Master := [(Sum.inr 1273, (1 / 1))]

def nodeValue1274 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 72))]

def nodeValue1275 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-5 / 144)), (Sum.inl 1, (1 / 72))]

def nodeValue1276 : Sparse Master := [(Sum.inr 1276, (1 / 1))]

def nodeValue1277 : Sparse Master := [(Sum.inr 1277, (1 / 1))]

def nodeValue1278 : Sparse Master := [(Sum.inr 1278, (1 / 1))]

def nodeValue1279 : Sparse Master := [(Sum.inr 1279, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue128 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-5 / 432)), (Sum.inl 71, (5 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue129 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 108)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (-5 / 216)), (Sum.inl 2, (5 / 432)), (Sum.inl 1, (5 / 48))]

def nodeValue130 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (5 / 108)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 256, (-5 / 18)), (Sum.inl 2, (5 / 864)), (Sum.inl 81, (-5 / 18)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (-5 / 96))]

def nodeValue131 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 216)), (Sum.inl 70, (-5 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (5 / 48))]

def nodeValue132 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 432)), (Sum.inl 71, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue133 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (-5 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 1, (5 / 48))]

def nodeValue134 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 257, (-5 / 27)), (Sum.inl 67, (-5 / 27)), (Sum.inl 2, (-25 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue139 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 67, (5 / 54)), (Sum.inl 2, (5 / 144)), (Sum.inl 35, (5 / 27)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (-5 / 144))]

def nodeValue140 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (25 / 216)), (Sum.inl 1, (-5 / 108))]

def nodeValue141 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (10 / 27)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-205 / 864)), (Sum.inl 7, (-5 / 9)), (Sum.inl 35, (-5 / 27)), (Sum.inl 8, (-5 / 9)), (Sum.inl 3, (-5 / 18)), (Sum.inl 1, (-25 / 432))]

def nodeValue142 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (-25 / 216)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (5 / 96)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (-5 / 96))]

def nodeValue143 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue144 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (5 / 72)), (Sum.inl 7, (5 / 54)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (25 / 432))]

def nodeValue145 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 432)), (Sum.inl 67, (5 / 54)), (Sum.inl 2, (25 / 432)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue146 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 108)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 54))]

def nodeValue147 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-5 / 216)), (Sum.inl 35, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue148 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 36)), (Sum.inl 67, (-5 / 27)), (Sum.inl 2, (-5 / 216)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue149 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 27)), (Sum.inl 7, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue150 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 72)), (Sum.inl 6, (-5 / 288)), (Sum.inl 67, (5 / 54)), (Sum.inl 2, (-5 / 216)), (Sum.inl 81, (-5 / 18)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 27)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-35 / 432))]

def nodeValue151 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 288)), (Sum.inl 2, (-35 / 864)), (Sum.inl 7, (5 / 18)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 18)), (Sum.inl 1, (5 / 54))]

def nodeValue152 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 144)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (55 / 432))]

def nodeValue153 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 108)), (Sum.inl 81, (5 / 9)), (Sum.inl 1, (-5 / 144))]

def nodeValue154 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 6, (-5 / 144)), (Sum.inl 2, (-5 / 72)), (Sum.inl 35, (5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue155 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 6, (-5 / 288)), (Sum.inl 7, (5 / 54)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue156 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 6, (5 / 432)), (Sum.inl 7, (-5 / 27)), (Sum.inl 1, (5 / 36))]

def nodeValue157 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 6, (5 / 432)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 54))]

def nodeValue158 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (-5 / 144)), (Sum.inl 1, (5 / 36))]

def nodeValue159 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 36)), (Sum.inl 67, (5 / 9)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue160 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 36)), (Sum.inl 7, (5 / 9)), (Sum.inl 1, (5 / 18))]

def nodeValue161 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 5, (5 / 36)), (Sum.inl 8, (5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue162 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 9)), (Sum.inl 6, (5 / 36)), (Sum.inl 1, (5 / 18))]

def nodeValue163 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 144)), (Sum.inl 257, (-5 / 54)), (Sum.inl 266, (5 / 18)), (Sum.inl 67, (-5 / 27)), (Sum.inl 34, (-5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 18)), (Sum.inl 7, (-10 / 27)), (Sum.inl 35, (-20 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 3, (-5 / 18)), (Sum.inl 13, (-5 / 54)), (Sum.inl 196, (5 / 18)), (Sum.inl 197, (5 / 9)), (Sum.inl 26, (-10 / 27)), (Sum.inl 1, (5 / 144))]

def nodeValue164 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 288)), (Sum.inl 257, (-5 / 54)), (Sum.inl 260, (5 / 18)), (Sum.inl 60, (-5 / 54)), (Sum.inl 268, (5 / 18)), (Sum.inl 64, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 864)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 27)), (Sum.inl 7, (-10 / 27)), (Sum.inl 35, (-5 / 9)), (Sum.inl 125, (5 / 9)), (Sum.inl 126, (5 / 18)), (Sum.inl 3, (-25 / 54)), (Sum.inl 13, (-5 / 18)), (Sum.inl 52, (-5 / 27)), (Sum.inl 197, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 864))]

def nodeValue165 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 264, (5 / 9)), (Sum.inl 266, (5 / 18)), (Sum.inl 63, (5 / 18)), (Sum.inl 65, (5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 288)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 6)), (Sum.inl 3, (-5 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 196, (5 / 9)), (Sum.inl 197, (5 / 18)), (Sum.inl 23, (5 / 9)), (Sum.inl 54, (5 / 9)), (Sum.inl 55, (5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 96))]

def nodeValue166 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 257, (-5 / 54)), (Sum.inl 260, (5 / 9)), (Sum.inl 60, (-5 / 27)), (Sum.inl 264, (5 / 6)), (Sum.inl 62, (5 / 9)), (Sum.inl 32, (-5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 288)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-10 / 27)), (Sum.inl 125, (5 / 9)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 54, (5 / 9)), (Sum.inl 1, (-5 / 288))]

def nodeValue167 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 263, (-5 / 9)), (Sum.inl 266, (5 / 18)), (Sum.inl 61, (5 / 18)), (Sum.inl 268, (5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 288)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 126, (5 / 18)), (Sum.inl 51, (5 / 18)), (Sum.inl 196, (5 / 18)), (Sum.inl 197, (5 / 9)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 56, (5 / 18)), (Sum.inl 27, (-5 / 36)), (Sum.inl 1, (5 / 432))]

def nodeValue168 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 266, (-5 / 18)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 216)), (Sum.inl 124, (-5 / 18)), (Sum.inl 196, (-5 / 18)), (Sum.inl 197, (-5 / 18)), (Sum.inl 1, (-25 / 432))]

def nodeValue169 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 268, (-5 / 18)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 144)), (Sum.inl 125, (-5 / 18)), (Sum.inl 126, (-5 / 18)), (Sum.inl 197, (-5 / 18)), (Sum.inl 1, (5 / 432))]

def nodeValue170 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 264, (-5 / 9)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 72)), (Sum.inl 125, (-5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue171 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 864)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (25 / 864)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 18)), (Sum.inl 125, (5 / 9)), (Sum.inl 3, (-5 / 18)), (Sum.inl 13, (-5 / 54)), (Sum.inl 196, (5 / 18)), (Sum.inl 197, (5 / 9)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 27)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (-25 / 864))]

def nodeValue172 : Sparse Master := [(Sum.inl 0, (5 / 288)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 288)), (Sum.inl 260, (5 / 18)), (Sum.inl 263, (-5 / 9)), (Sum.inl 64, (5 / 9)), (Sum.inl 33, (5 / 18)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (-5 / 288)), (Sum.inl 125, (5 / 9)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 197, (5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (-5 / 864))]

def nodeValue173 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 32)), (Sum.inl 70, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 196, (-5 / 18)), (Sum.inl 1, (-35 / 864))]

def nodeValue174 : Sparse Master := [(Sum.inl 0, (25 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-25 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 3, (-25 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 197, (10 / 9)), (Sum.inl 24, (5 / 9)), (Sum.inl 55, (5 / 18)), (Sum.inl 56, (5 / 9)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (85 / 864))]

def nodeValue175 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 864)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 72)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 197, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-85 / 864))]

def nodeValue176 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 260, (-5 / 18)), (Sum.inl 64, (-5 / 18)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 288)), (Sum.inl 125, (-5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-55 / 864))]

def nodeValue177 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 264, (-5 / 18)), (Sum.inl 63, (-5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (35 / 288)), (Sum.inl 35, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 196, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-25 / 864))]

def nodeValue178 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 96)), (Sum.inl 125, (-5 / 18)), (Sum.inl 197, (-5 / 18)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-25 / 288))]

def nodeValue179 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 288)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (5 / 108)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-5 / 18)), (Sum.inl 125, (5 / 6)), (Sum.inl 3, (-5 / 9)), (Sum.inl 13, (-10 / 27)), (Sum.inl 196, (5 / 9)), (Sum.inl 23, (5 / 6)), (Sum.inl 54, (5 / 6)), (Sum.inl 12, (-5 / 18)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (175 / 864))]

def nodeValue180 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 216)), (Sum.inl 70, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 27)), (Sum.inl 125, (-5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 1, (5 / 36))]

def nodeValue181 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 260, (-5 / 18)), (Sum.inl 264, (-5 / 18)), (Sum.inl 62, (-5 / 18)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-65 / 864)), (Sum.inl 54, (-5 / 18)), (Sum.inl 1, (-25 / 288))]

def nodeValue182 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 108)), (Sum.inl 125, (-5 / 18)), (Sum.inl 196, (-5 / 18)), (Sum.inl 23, (-5 / 18)), (Sum.inl 54, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 54))]

def nodeValue183 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 197, (-5 / 9)), (Sum.inl 24, (-5 / 18)), (Sum.inl 56, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 432))]

def nodeValue184 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 263, (5 / 9)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue185 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 36)), (Sum.inl 196, (5 / 9)), (Sum.inl 1, (5 / 36))]

def nodeValue186 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 197, (5 / 9)), (Sum.inl 1, (-5 / 72))]

def nodeValue187 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 125, (5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue188 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 264, (5 / 9)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 48)), (Sum.inl 1, (-5 / 144))]

def nodeValue189 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 288)), (Sum.inl 257, (-5 / 54)), (Sum.inl 264, (5 / 9)), (Sum.inl 266, (5 / 6)), (Sum.inl 65, (5 / 6)), (Sum.inl 67, (-5 / 18)), (Sum.inl 34, (-5 / 18)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (25 / 288)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-5 / 18)), (Sum.inl 13, (-5 / 54)), (Sum.inl 54, (5 / 6)), (Sum.inl 26, (-5 / 9)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (65 / 864))]

def nodeValue190 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 257, (5 / 54)), (Sum.inl 266, (-5 / 18)), (Sum.inl 67, (5 / 27)), (Sum.inl 34, (5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 144)), (Sum.inl 35, (5 / 27)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (-5 / 432))]

def nodeValue191 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 288)), (Sum.inl 257, (-5 / 54)), (Sum.inl 60, (-5 / 27)), (Sum.inl 264, (5 / 18)), (Sum.inl 266, (5 / 9)), (Sum.inl 61, (5 / 9)), (Sum.inl 32, (-5 / 54)), (Sum.inl 268, (5 / 9)), (Sum.inl 65, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (35 / 864)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 9)), (Sum.inl 54, (5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (5 / 108))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1280 : Sparse Master := [(Sum.inr 1280, (1 / 1))]

def nodeValue1282 : Sparse Master := [(Sum.inr 1282, (1 / 1))]

def nodeValue1283 : Sparse Master := [(Sum.inr 1283, (1 / 1))]

def nodeValue1286 : Sparse Master := [(Sum.inr 1286, (1 / 1))]

def nodeValue1287 : Sparse Master := [(Sum.inr 1287, (1 / 1))]

def nodeValue1288 : Sparse Master := [(Sum.inr 1288, (1 / 1))]

def nodeValue1289 : Sparse Master := [(Sum.inr 1289, (1 / 1))]

def nodeValue1291 : Sparse Master := [(Sum.inr 1291, (1 / 1))]

def nodeValue1292 : Sparse Master := [(Sum.inr 1292, (1 / 1))]

def nodeValue1293 : Sparse Master := [(Sum.inr 1293, (1 / 1))]

def nodeValue1294 : Sparse Master := [(Sum.inr 1294, (1 / 1))]

def nodeValue1295 : Sparse Master := [(Sum.inr 1295, (1 / 1))]

def nodeValue1296 : Sparse Master := [(Sum.inr 1296, (1 / 1))]

def nodeValue1297 : Sparse Master := [(Sum.inr 1297, (1 / 1))]

def nodeValue1298 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (1 / 288)), (Sum.inl 2, (7 / 864)), (Sum.inl 7, (-1 / 18)), (Sum.inl 35, (-1 / 27)), (Sum.inl 3, (-1 / 18)), (Sum.inl 1, (-1 / 54))]

def nodeValue1299 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 6, (1 / 288)), (Sum.inl 7, (-1 / 54)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue1300 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (-1 / 432)), (Sum.inl 7, (1 / 27)), (Sum.inl 1, (-1 / 36))]

def nodeValue1301 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 6, (-1 / 432)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 54))]

def nodeValue1302 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-1 / 144)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-11 / 432))]

def nodeValue1303 : Sparse Master := [(Sum.inr 1303, (1 / 1))]

def nodeValue1304 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (1 / 144)), (Sum.inl 1, (-1 / 36))]

def nodeValue1305 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (-1 / 432)), (Sum.inl 7, (1 / 27)), (Sum.inl 1, (-1 / 36))]

def nodeValue1306 : Sparse Master := [(Sum.inr 1306, (1 / 1))]

def nodeValue1307 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (1 / 144)), (Sum.inl 1, (-1 / 36))]

def nodeValue1308 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (1 / 72)), (Sum.inl 35, (-1 / 9)), (Sum.inl 1, (-1 / 48))]

def nodeValue1309 : Sparse Master := [(Sum.inr 1309, (1 / 1))]

def nodeValue1310 : Sparse Master := [(Sum.inr 1310, (1 / 1))]

def nodeValue1311 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (-1 / 36)), (Sum.inl 7, (-1 / 9)), (Sum.inl 1, (-1 / 18))]

def nodeValue1312 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 5, (-1 / 36)), (Sum.inl 8, (-1 / 9)), (Sum.inl 1, (1 / 72))]

def nodeValue1313 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (-1 / 9)), (Sum.inl 6, (-1 / 36)), (Sum.inl 1, (-1 / 18))]

def nodeValue1314 : Sparse Master := [(Sum.inr 1314, (1 / 1))]

def nodeValue1315 : Sparse Master := [(Sum.inr 1315, (1 / 1))]

def nodeValue1316 : Sparse Master := [(Sum.inr 1316, (1 / 1))]

def nodeValue1317 : Sparse Master := [(Sum.inr 1317, (1 / 1))]

def nodeValue1318 : Sparse Master := [(Sum.inr 1318, (1 / 1))]

def nodeValue1319 : Sparse Master := [(Sum.inr 1319, (1 / 1))]

def nodeValue1320 : Sparse Master := [(Sum.inr 1320, (1 / 1))]

def nodeValue1321 : Sparse Master := [(Sum.inr 1321, (1 / 1))]

def nodeValue1322 : Sparse Master := [(Sum.inr 1322, (1 / 1))]

def nodeValue1323 : Sparse Master := [(Sum.inr 1323, (1 / 1))]

def nodeValue1324 : Sparse Master := [(Sum.inr 1324, (1 / 1))]

def nodeValue1325 : Sparse Master := [(Sum.inr 1325, (1 / 1))]

def nodeValue1326 : Sparse Master := [(Sum.inr 1326, (1 / 1))]

def nodeValue1327 : Sparse Master := [(Sum.inr 1327, (1 / 1))]

def nodeValue1328 : Sparse Master := [(Sum.inr 1328, (1 / 1))]

def nodeValue1329 : Sparse Master := []

def nodeValue1330 : Sparse Master := [(Sum.inr 1330, (1 / 1))]

def nodeValue1331 : Sparse Master := []

def nodeValue1332 : Sparse Master := [(Sum.inr 1332, (1 / 1))]

def nodeValue1333 : Sparse Master := [(Sum.inr 1333, (1 / 1))]

def nodeValue1334 : Sparse Master := [(Sum.inr 1334, (1 / 1))]

def nodeValue1335 : Sparse Master := [(Sum.inr 1335, (1 / 1))]

def nodeValue1336 : Sparse Master := [(Sum.inr 1336, (1 / 1))]

def nodeValue1337 : Sparse Master := [(Sum.inr 1337, (1 / 1))]

def nodeValue1338 : Sparse Master := [(Sum.inr 1338, (1 / 1))]

def nodeValue1339 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 9, (1 / 54)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-1 / 18)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (7 / 432)), (Sum.inl 69, (1 / 54)), (Sum.inl 71, (2 / 27)), (Sum.inl 8, (2 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1340 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 58, (1 / 864)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (-1 / 144)), (Sum.inl 2, (-1 / 48)), (Sum.inl 69, (-1 / 54)), (Sum.inl 52, (-1 / 27)), (Sum.inl 1, (-1 / 108))]

def nodeValue1341 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 9, (1 / 54)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (1 / 108)), (Sum.inl 69, (1 / 27)), (Sum.inl 70, (1 / 54)), (Sum.inl 71, (1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 54)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (7 / 864))]

def nodeValue1342 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 58, (1 / 864)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (1 / 108)), (Sum.inl 71, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue1343 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (-1 / 108)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (-1 / 54)), (Sum.inl 70, (-1 / 54)), (Sum.inl 7, (-1 / 27)), (Sum.inl 35, (-1 / 27)), (Sum.inl 3, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (5 / 288))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1344 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 9, (-1 / 108)), (Sum.inl 5, (1 / 54)), (Sum.inl 2, (-5 / 432)), (Sum.inl 71, (-1 / 27)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (-1 / 54))]

def nodeValue1345 : Sparse Master := []

def nodeValue1346 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 58, (1 / 864)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (-37 / 864)), (Sum.inl 70, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue1347 : Sparse Master := [(Sum.inr 1347, (1 / 1))]

def nodeValue1348 : Sparse Master := [(Sum.inr 1348, (1 / 1))]

def nodeValue1349 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 27)), (Sum.inl 70, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue1354 : Sparse Master := [(Sum.inr 1354, (1 / 1))]

def nodeValue1355 : Sparse Master := [(Sum.inr 1355, (1 / 1))]

def nodeValue1356 : Sparse Master := [(Sum.inr 1356, (1 / 1))]

def nodeValue1357 : Sparse Master := [(Sum.inr 1357, (1 / 1))]

def nodeValue1358 : Sparse Master := [(Sum.inr 1358, (1 / 1))]

def nodeValue1359 : Sparse Master := [(Sum.inr 1359, (1 / 1))]

def nodeValue1360 : Sparse Master := [(Sum.inr 1360, (1 / 1))]

def nodeValue1361 : Sparse Master := [(Sum.inr 1361, (1 / 1))]

def nodeValue1362 : Sparse Master := [(Sum.inr 1362, (1 / 1))]

def nodeValue1363 : Sparse Master := [(Sum.inr 1363, (1 / 1))]

def nodeValue1364 : Sparse Master := [(Sum.inr 1364, (1 / 1))]

def nodeValue1366 : Sparse Master := [(Sum.inr 1366, (1 / 1))]

def nodeValue1367 : Sparse Master := [(Sum.inr 1367, (1 / 1))]

def nodeValue1368 : Sparse Master := [(Sum.inr 1368, (1 / 1))]

def nodeValue1369 : Sparse Master := [(Sum.inr 1369, (1 / 1))]

def nodeValue1370 : Sparse Master := [(Sum.inr 1370, (1 / 1))]

def nodeValue1371 : Sparse Master := [(Sum.inr 1371, (1 / 1))]

def nodeValue1372 : Sparse Master := [(Sum.inr 1372, (1 / 1))]

def nodeValue1373 : Sparse Master := [(Sum.inr 1373, (1 / 1))]

def nodeValue1374 : Sparse Master := [(Sum.inr 1374, (1 / 1))]

def nodeValue1375 : Sparse Master := [(Sum.inr 1375, (1 / 1))]

def nodeValue1378 : Sparse Master := [(Sum.inr 1378, (1 / 1))]

def nodeValue1379 : Sparse Master := []

def nodeValue1380 : Sparse Master := [(Sum.inr 1380, (1 / 1))]

def nodeValue1381 : Sparse Master := []

def nodeValue1382 : Sparse Master := [(Sum.inr 1382, (1 / 1))]

def nodeValue1383 : Sparse Master := [(Sum.inr 1383, (1 / 1))]

def nodeValue1384 : Sparse Master := [(Sum.inr 1384, (1 / 1))]

def nodeValue1385 : Sparse Master := [(Sum.inr 1385, (1 / 1))]

def nodeValue1386 : Sparse Master := []

def nodeValue1387 : Sparse Master := [(Sum.inr 1387, (1 / 1))]

def nodeValue1388 : Sparse Master := [(Sum.inr 1388, (1 / 1))]

def nodeValue1389 : Sparse Master := [(Sum.inr 1389, (1 / 1))]

def nodeValue1390 : Sparse Master := [(Sum.inr 1390, (1 / 1))]

def nodeValue1391 : Sparse Master := [(Sum.inr 1391, (1 / 1))]

def nodeValue1392 : Sparse Master := [(Sum.inr 1392, (1 / 1))]

def nodeValue1393 : Sparse Master := []

def nodeValue1394 : Sparse Master := [(Sum.inr 1394, (1 / 1))]

def nodeValue1395 : Sparse Master := [(Sum.inl 0, (-49 / 4320)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (11 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (2 / 27)), (Sum.inl 1, (7 / 216))]

def nodeValue1396 : Sparse Master := [(Sum.inl 0, (-41 / 4320)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (-11 / 864)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 18)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 54)), (Sum.inl 52, (1 / 54)), (Sum.inl 228, (-1 / 18)), (Sum.inl 11, (1 / 54)), (Sum.inl 26, (1 / 54)), (Sum.inl 1, (-5 / 864))]

def nodeValue1397 : Sparse Master := [(Sum.inl 0, (-13 / 1440)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (1 / 96)), (Sum.inl 2, (1 / 108)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (-1 / 144))]

def nodeValue1398 : Sparse Master := []

def nodeValue1399 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 432)), (Sum.inl 35, (-1 / 54)), (Sum.inl 11, (-1 / 54)), (Sum.inl 1, (-1 / 144))]

def nodeValue1400 : Sparse Master := [(Sum.inr 1400, (1 / 1))]

def nodeValue1401 : Sparse Master := [(Sum.inl 0, (-13 / 1440)), (Sum.inl 5, (-1 / 24)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 1, (-5 / 864))]

def nodeValue1403 : Sparse Master := [(Sum.inr 1403, (1 / 1))]

def nodeValue1404 : Sparse Master := [(Sum.inr 1404, (1 / 1))]

def nodeValue1405 : Sparse Master := []

def nodeValue1406 : Sparse Master := [(Sum.inr 1406, (1 / 1))]

def nodeValue1407 : Sparse Master := [(Sum.inr 1407, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1408 : Sparse Master := [(Sum.inr 1408, (1 / 1))]

def nodeValue1409 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (-2 / 27)), (Sum.inl 6, (11 / 864)), (Sum.inl 2, (11 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (2 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1410 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (-7 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 3, (-1 / 27)), (Sum.inl 52, (-1 / 27)), (Sum.inl 1, (-1 / 216))]

def nodeValue1411 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (-1 / 48))]

def nodeValue1412 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-5 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 3, (-1 / 54)), (Sum.inl 228, (1 / 18)), (Sum.inl 11, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue1413 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (1 / 108)), (Sum.inl 2, (1 / 108)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1414 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (1 / 108)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue1415 : Sparse Master := [(Sum.inr 1415, (1 / 1))]

def nodeValue1416 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (1 / 72)), (Sum.inl 1, (1 / 108))]

def nodeValue1417 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (1 / 216)), (Sum.inl 35, (1 / 27)), (Sum.inl 11, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue1418 : Sparse Master := [(Sum.inr 1418, (1 / 1))]

def nodeValue1419 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 27)), (Sum.inl 2, (1 / 108)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue1420 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 5, (-5 / 108)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (-1 / 216))]

def nodeValue1421 : Sparse Master := [(Sum.inr 1421, (1 / 1))]

def nodeValue1422 : Sparse Master := [(Sum.inr 1422, (1 / 1))]

def nodeValue1423 : Sparse Master := [(Sum.inr 1423, (1 / 1))]

def nodeValue1424 : Sparse Master := [(Sum.inr 1424, (1 / 1))]

def nodeValue1425 : Sparse Master := [(Sum.inr 1425, (1 / 1))]

def nodeValue1427 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (1 / 108)), (Sum.inl 35, (-1 / 27)), (Sum.inl 11, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (-1 / 144))]

def nodeValue1433 : Sparse Master := [(Sum.inr 1433, (1 / 1))]

def nodeValue1435 : Sparse Master := [(Sum.inr 1435, (1 / 1))]

def nodeValue1436 : Sparse Master := [(Sum.inr 1436, (1 / 1))]

def nodeValue1437 : Sparse Master := [(Sum.inr 1437, (1 / 1))]

def nodeValue1438 : Sparse Master := [(Sum.inr 1438, (1 / 1))]

def nodeValue1440 : Sparse Master := [(Sum.inr 1440, (1 / 1))]

def nodeValue1441 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (13 / 864)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 52, (-1 / 27)), (Sum.inl 1, (1 / 96))]

def nodeValue1442 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 432)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue1443 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 108)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (1 / 108))]

def nodeValue1444 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-1 / 108)), (Sum.inl 228, (-1 / 9))]

def nodeValue1445 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (1 / 72)), (Sum.inl 52, (-1 / 9)), (Sum.inl 1, (1 / 72))]

def nodeValue1446 : Sparse Master := []

def nodeValue1447 : Sparse Master := []

def nodeValue1448 : Sparse Master := []

def nodeValue1449 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 216)), (Sum.inl 35, (1 / 27)), (Sum.inl 11, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 432))]

def nodeValue1450 : Sparse Master := []

def nodeValue1451 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (1 / 27)), (Sum.inl 1, (-1 / 432))]

def nodeValue1452 : Sparse Master := []

def nodeValue1453 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (1 / 72)), (Sum.inl 2, (1 / 72)), (Sum.inl 11, (-1 / 9)), (Sum.inl 1, (1 / 144))]

def nodeValue1454 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 36)), (Sum.inl 2, (-1 / 36)), (Sum.inl 35, (-1 / 9)), (Sum.inl 1, (1 / 144))]

def nodeValue1455 : Sparse Master := []

def nodeValue1456 : Sparse Master := []

def nodeValue1457 : Sparse Master := [(Sum.inr 1457, (1 / 1))]

def nodeValue1458 : Sparse Master := [(Sum.inr 1458, (1 / 1))]

def nodeValue1459 : Sparse Master := [(Sum.inr 1459, (1 / 1))]

def nodeValue1460 : Sparse Master := [(Sum.inr 1460, (1 / 1))]

def nodeValue1461 : Sparse Master := [(Sum.inr 1461, (1 / 1))]

def nodeValue1462 : Sparse Master := [(Sum.inr 1462, (1 / 1))]

def nodeValue1463 : Sparse Master := [(Sum.inr 1463, (1 / 1))]

def nodeValue1464 : Sparse Master := [(Sum.inr 1464, (1 / 1))]

def nodeValue1465 : Sparse Master := [(Sum.inr 1465, (1 / 1))]

def nodeValue1466 : Sparse Master := [(Sum.inr 1466, (1 / 1))]

def nodeValue1467 : Sparse Master := [(Sum.inr 1467, (1 / 1))]

def nodeValue1468 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-1 / 144)), (Sum.inl 2, (-1 / 72)), (Sum.inl 35, (-1 / 54)), (Sum.inl 82, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 128, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 201, (1 / 18))]

def nodeValue1470 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (-1 / 108)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 82, (-1 / 54)), (Sum.inl 199, (1 / 18)), (Sum.inl 1, (1 / 432))]

def nodeValue1471 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 27)), (Sum.inl 6, (1 / 108)), (Sum.inl 2, (1 / 108)), (Sum.inl 35, (1 / 27)), (Sum.inl 82, (1 / 27)), (Sum.inl 1, (1 / 144))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1473 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (-1 / 216)), (Sum.inl 201, (-1 / 9)), (Sum.inl 1, (1 / 216))]

def nodeValue1474 : Sparse Master := [(Sum.inr 1474, (1 / 1))]

def nodeValue1475 : Sparse Master := [(Sum.inl 0, (-7 / 720)), (Sum.inl 5, (-1 / 36)), (Sum.inl 6, (1 / 144)), (Sum.inl 2, (11 / 432)), (Sum.inl 35, (1 / 54)), (Sum.inl 82, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 128, (1 / 27)), (Sum.inl 52, (2 / 27)), (Sum.inl 201, (-1 / 18)), (Sum.inl 1, (1 / 48))]

def nodeValue1477 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-1 / 72)), (Sum.inl 2, (-1 / 27)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (2 / 27)), (Sum.inl 82, (1 / 27)), (Sum.inl 199, (-1 / 18)), (Sum.inl 1, (-7 / 432))]

def nodeValue1478 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (1 / 96)), (Sum.inl 2, (1 / 108)), (Sum.inl 35, (-1 / 54)), (Sum.inl 82, (-1 / 54)), (Sum.inl 1, (-7 / 864))]

def nodeValue1479 : Sparse Master := [(Sum.inl 0, (-13 / 1440)), (Sum.inl 5, (-11 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 432)), (Sum.inl 8, (-1 / 54)), (Sum.inl 201, (1 / 18))]

def nodeValue1480 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (-1 / 108)), (Sum.inl 2, (-1 / 48)), (Sum.inl 128, (-1 / 54)), (Sum.inl 52, (-1 / 27)), (Sum.inl 1, (-1 / 72))]

def nodeValue1482 : Sparse Master := []

def nodeValue1483 : Sparse Master := []

def nodeValue1484 : Sparse Master := []

def nodeValue1485 : Sparse Master := []

def nodeValue1486 : Sparse Master := []

def nodeValue1488 : Sparse Master := [(Sum.inr 1488, (1 / 1))]

def nodeValue1489 : Sparse Master := [(Sum.inr 1489, (1 / 1))]

def nodeValue1490 : Sparse Master := [(Sum.inr 1490, (1 / 1))]

def nodeValue1491 : Sparse Master := [(Sum.inr 1491, (1 / 1))]

def nodeValue1492 : Sparse Master := [(Sum.inr 1492, (1 / 1))]

def nodeValue1493 : Sparse Master := [(Sum.inr 1493, (1 / 1))]

def nodeValue1494 : Sparse Master := [(Sum.inr 1494, (1 / 1))]

def nodeValue1495 : Sparse Master := [(Sum.inr 1495, (1 / 1))]

def nodeValue1496 : Sparse Master := [(Sum.inr 1496, (1 / 1))]

def nodeValue1497 : Sparse Master := [(Sum.inr 1497, (1 / 1))]

def nodeValue1498 : Sparse Master := [(Sum.inr 1498, (1 / 1))]

def nodeValue1499 : Sparse Master := [(Sum.inr 1499, (1 / 1))]

def nodeValue1500 : Sparse Master := [(Sum.inr 1500, (1 / 1))]

def nodeValue1501 : Sparse Master := [(Sum.inr 1501, (1 / 1))]

def nodeValue1502 : Sparse Master := [(Sum.inr 1502, (1 / 1))]

def nodeValue1503 : Sparse Master := [(Sum.inr 1503, (1 / 1))]

def nodeValue1504 : Sparse Master := [(Sum.inr 1504, (1 / 1))]

def nodeValue1505 : Sparse Master := [(Sum.inr 1505, (1 / 1))]

def nodeValue1506 : Sparse Master := [(Sum.inr 1506, (1 / 1))]

def nodeValue1507 : Sparse Master := [(Sum.inr 1507, (1 / 1))]

def nodeValue1508 : Sparse Master := [(Sum.inr 1508, (1 / 1))]

def nodeValue1509 : Sparse Master := [(Sum.inr 1509, (1 / 1))]

def nodeValue1510 : Sparse Master := [(Sum.inr 1510, (1 / 1))]

def nodeValue1511 : Sparse Master := [(Sum.inr 1511, (1 / 1))]

def nodeValue1512 : Sparse Master := [(Sum.inr 1512, (1 / 1))]

def nodeValue1513 : Sparse Master := [(Sum.inr 1513, (1 / 1))]

def nodeValue1514 : Sparse Master := [(Sum.inr 1514, (1 / 1))]

def nodeValue1515 : Sparse Master := [(Sum.inr 1515, (1 / 1))]

def nodeValue1516 : Sparse Master := [(Sum.inr 1516, (1 / 1))]

def nodeValue1517 : Sparse Master := [(Sum.inr 1517, (1 / 1))]

def nodeValue1518 : Sparse Master := [(Sum.inr 1518, (1 / 1))]

def nodeValue1519 : Sparse Master := [(Sum.inr 1519, (1 / 1))]

def nodeValue1520 : Sparse Master := [(Sum.inr 1520, (1 / 1))]

def nodeValue1521 : Sparse Master := [(Sum.inr 1521, (1 / 1))]

def nodeValue1522 : Sparse Master := [(Sum.inr 1522, (1 / 1))]

def nodeValue1523 : Sparse Master := [(Sum.inr 1523, (1 / 1))]

def nodeValue1524 : Sparse Master := [(Sum.inr 1524, (1 / 1))]

def nodeValue1525 : Sparse Master := [(Sum.inr 1525, (1 / 1))]

def nodeValue1526 : Sparse Master := [(Sum.inr 1526, (1 / 1))]

def nodeValue1527 : Sparse Master := [(Sum.inr 1527, (1 / 1))]

def nodeValue1528 : Sparse Master := [(Sum.inr 1528, (1 / 1))]

def nodeValue1529 : Sparse Master := [(Sum.inr 1529, (1 / 1))]

def nodeValue1530 : Sparse Master := [(Sum.inr 1530, (1 / 1))]

def nodeValue1531 : Sparse Master := [(Sum.inr 1531, (1 / 1))]

def nodeValue1532 : Sparse Master := [(Sum.inr 1532, (1 / 1))]

def nodeValue1533 : Sparse Master := [(Sum.inr 1533, (1 / 1))]

def nodeValue1534 : Sparse Master := [(Sum.inr 1534, (1 / 1))]

def nodeValue1535 : Sparse Master := [(Sum.inr 1535, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1536 : Sparse Master := [(Sum.inr 1536, (1 / 1))]

def nodeValue1537 : Sparse Master := [(Sum.inr 1537, (1 / 1))]

def nodeValue1538 : Sparse Master := [(Sum.inr 1538, (1 / 1))]

def nodeValue1539 : Sparse Master := [(Sum.inr 1539, (1 / 1))]

def nodeValue1540 : Sparse Master := [(Sum.inr 1540, (1 / 1))]

def nodeValue1541 : Sparse Master := [(Sum.inr 1541, (1 / 1))]

def nodeValue1550 : Sparse Master := [(Sum.inr 1550, (1 / 1))]

def nodeValue1552 : Sparse Master := [(Sum.inr 1552, (1 / 1))]

def nodeValue1553 : Sparse Master := [(Sum.inr 1553, (1 / 1))]

def nodeValue1554 : Sparse Master := [(Sum.inr 1554, (1 / 1))]

def nodeValue1555 : Sparse Master := [(Sum.inr 1555, (1 / 1))]

def nodeValue1556 : Sparse Master := [(Sum.inr 1556, (1 / 1))]

def nodeValue1557 : Sparse Master := []

def nodeValue1558 : Sparse Master := [(Sum.inr 1558, (1 / 1))]

def nodeValue1559 : Sparse Master := [(Sum.inr 1559, (1 / 1))]

def nodeValue1561 : Sparse Master := [(Sum.inr 1561, (1 / 1))]

def nodeValue1562 : Sparse Master := [(Sum.inr 1562, (1 / 1))]

def nodeValue1563 : Sparse Master := [(Sum.inr 1563, (1 / 1))]

def nodeValue1565 : Sparse Master := [(Sum.inr 1565, (1 / 1))]

def nodeValue1566 : Sparse Master := [(Sum.inr 1566, (1 / 1))]

def nodeValue1567 : Sparse Master := [(Sum.inr 1567, (1 / 1))]

def nodeValue1568 : Sparse Master := [(Sum.inr 1568, (1 / 1))]

def nodeValue1569 : Sparse Master := [(Sum.inr 1569, (1 / 1))]

def nodeValue1570 : Sparse Master := [(Sum.inr 1570, (1 / 1))]

def nodeValue1573 : Sparse Master := [(Sum.inr 1573, (1 / 1))]

def nodeValue1574 : Sparse Master := []

def nodeValue1575 : Sparse Master := [(Sum.inr 1575, (1 / 1))]

def nodeValue1576 : Sparse Master := []

def nodeValue1577 : Sparse Master := [(Sum.inr 1577, (1 / 1))]

def nodeValue1578 : Sparse Master := [(Sum.inr 1578, (1 / 1))]

def nodeValue1579 : Sparse Master := []

def nodeValue1586 : Sparse Master := [(Sum.inr 1586, (1 / 1))]

def nodeValue1587 : Sparse Master := [(Sum.inr 1587, (1 / 1))]

def nodeValue1588 : Sparse Master := [(Sum.inr 1588, (1 / 1))]

def nodeValue1589 : Sparse Master := [(Sum.inr 1589, (1 / 1))]

def nodeValue1590 : Sparse Master := [(Sum.inr 1590, (1 / 1))]

def nodeValue1591 : Sparse Master := [(Sum.inr 1591, (1 / 1))]

def nodeValue1592 : Sparse Master := []

def nodeValue1593 : Sparse Master := [(Sum.inr 1593, (1 / 1))]

def nodeValue1594 : Sparse Master := [(Sum.inr 1594, (1 / 1))]

def nodeValue1595 : Sparse Master := []

def nodeValue1596 : Sparse Master := []

def nodeValue1597 : Sparse Master := [(Sum.inr 1597, (1 / 1))]

def nodeValue1598 : Sparse Master := []

def nodeValue1599 : Sparse Master := [(Sum.inr 1599, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1600 : Sparse Master := [(Sum.inr 1600, (1 / 1))]

def nodeValue1601 : Sparse Master := [(Sum.inr 1601, (1 / 1))]

def nodeValue1602 : Sparse Master := [(Sum.inr 1602, (1 / 1))]

def nodeValue1603 : Sparse Master := [(Sum.inr 1603, (1 / 1))]

def nodeValue1604 : Sparse Master := [(Sum.inr 1604, (1 / 1))]

def nodeValue1605 : Sparse Master := [(Sum.inr 1605, (1 / 1))]

def nodeValue1606 : Sparse Master := [(Sum.inr 1606, (1 / 1))]

def nodeValue1607 : Sparse Master := [(Sum.inr 1607, (1 / 1))]

def nodeValue1608 : Sparse Master := [(Sum.inr 1608, (1 / 1))]

def nodeValue1609 : Sparse Master := [(Sum.inr 1609, (1 / 1))]

def nodeValue1610 : Sparse Master := [(Sum.inr 1610, (1 / 1))]

def nodeValue1611 : Sparse Master := [(Sum.inr 1611, (1 / 1))]

def nodeValue1612 : Sparse Master := [(Sum.inr 1612, (1 / 1))]

def nodeValue1613 : Sparse Master := [(Sum.inr 1613, (1 / 1))]

def nodeValue1614 : Sparse Master := []

def nodeValue1615 : Sparse Master := [(Sum.inr 1615, (1 / 1))]

def nodeValue1616 : Sparse Master := [(Sum.inr 1616, (1 / 1))]

def nodeValue1617 : Sparse Master := [(Sum.inr 1617, (1 / 1))]

def nodeValue1618 : Sparse Master := [(Sum.inr 1618, (1 / 1))]

def nodeValue1619 : Sparse Master := [(Sum.inr 1619, (1 / 1))]

def nodeValue1620 : Sparse Master := [(Sum.inr 1620, (1 / 1))]

def nodeValue1623 : Sparse Master := [(Sum.inr 1623, (1 / 1))]

def nodeValue1624 : Sparse Master := [(Sum.inr 1624, (1 / 1))]

def nodeValue1625 : Sparse Master := []

def nodeValue1626 : Sparse Master := [(Sum.inr 1626, (1 / 1))]

def nodeValue1627 : Sparse Master := [(Sum.inr 1627, (1 / 1))]

def nodeValue1628 : Sparse Master := [(Sum.inr 1628, (1 / 1))]

def nodeValue1629 : Sparse Master := [(Sum.inr 1629, (1 / 1))]

def nodeValue1630 : Sparse Master := [(Sum.inr 1630, (1 / 1))]

def nodeValue1632 : Sparse Master := [(Sum.inr 1632, (1 / 1))]

def nodeValue1633 : Sparse Master := [(Sum.inr 1633, (1 / 1))]

def nodeValue1634 : Sparse Master := [(Sum.inr 1634, (1 / 1))]

def nodeValue1635 : Sparse Master := [(Sum.inr 1635, (1 / 1))]

def nodeValue1636 : Sparse Master := [(Sum.inr 1636, (1 / 1))]

def nodeValue1637 : Sparse Master := [(Sum.inr 1637, (1 / 1))]

def nodeValue1638 : Sparse Master := [(Sum.inr 1638, (1 / 1))]

def nodeValue1639 : Sparse Master := [(Sum.inr 1639, (1 / 1))]

def nodeValue1640 : Sparse Master := [(Sum.inr 1640, (1 / 1))]

def nodeValue1641 : Sparse Master := [(Sum.inr 1641, (1 / 1))]

def nodeValue1642 : Sparse Master := [(Sum.inr 1642, (1 / 1))]

def nodeValue1643 : Sparse Master := [(Sum.inr 1643, (1 / 1))]

def nodeValue1644 : Sparse Master := [(Sum.inr 1644, (1 / 1))]

def nodeValue1645 : Sparse Master := [(Sum.inr 1645, (1 / 1))]

def nodeValue1646 : Sparse Master := [(Sum.inr 1646, (1 / 1))]

def nodeValue1647 : Sparse Master := [(Sum.inr 1647, (1 / 1))]

def nodeValue1648 : Sparse Master := [(Sum.inr 1648, (1 / 1))]

def nodeValue1649 : Sparse Master := [(Sum.inr 1649, (1 / 1))]

def nodeValue1650 : Sparse Master := [(Sum.inr 1650, (1 / 1))]

def nodeValue1651 : Sparse Master := [(Sum.inr 1651, (1 / 1))]

def nodeValue1652 : Sparse Master := [(Sum.inr 1652, (1 / 1))]

def nodeValue1653 : Sparse Master := [(Sum.inr 1653, (1 / 1))]

def nodeValue1654 : Sparse Master := [(Sum.inr 1654, (1 / 1))]

def nodeValue1655 : Sparse Master := [(Sum.inr 1655, (1 / 1))]

def nodeValue1656 : Sparse Master := [(Sum.inr 1656, (1 / 1))]

def nodeValue1657 : Sparse Master := [(Sum.inr 1657, (1 / 1))]

def nodeValue1658 : Sparse Master := [(Sum.inr 1658, (1 / 1))]

def nodeValue1659 : Sparse Master := [(Sum.inr 1659, (1 / 1))]

def nodeValue1660 : Sparse Master := [(Sum.inr 1660, (1 / 1))]

def nodeValue1661 : Sparse Master := [(Sum.inr 1661, (1 / 1))]

def nodeValue1662 : Sparse Master := []

def nodeValue1663 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1664 : Sparse Master := [(Sum.inr 1664, (1 / 1))]

def nodeValue1665 : Sparse Master := []

def nodeValue1666 : Sparse Master := [(Sum.inr 1666, (1 / 1))]

def nodeValue1667 : Sparse Master := [(Sum.inr 1667, (1 / 1))]

def nodeValue1668 : Sparse Master := [(Sum.inr 1668, (1 / 1))]

def nodeValue1669 : Sparse Master := [(Sum.inr 1669, (1 / 1))]

def nodeValue1670 : Sparse Master := [(Sum.inr 1670, (1 / 1))]

def nodeValue1671 : Sparse Master := []

def nodeValue1672 : Sparse Master := [(Sum.inr 1672, (1 / 1))]

def nodeValue1673 : Sparse Master := [(Sum.inr 1673, (1 / 1))]

def nodeValue1674 : Sparse Master := [(Sum.inr 1674, (1 / 1))]

def nodeValue1675 : Sparse Master := [(Sum.inr 1675, (1 / 1))]

def nodeValue1676 : Sparse Master := [(Sum.inr 1676, (1 / 1))]

def nodeValue1677 : Sparse Master := [(Sum.inr 1677, (1 / 1))]

def nodeValue1678 : Sparse Master := [(Sum.inr 1678, (1 / 1))]

def nodeValue1679 : Sparse Master := [(Sum.inr 1679, (1 / 1))]

def nodeValue1680 : Sparse Master := [(Sum.inr 1680, (1 / 1))]

def nodeValue1681 : Sparse Master := [(Sum.inr 1681, (1 / 1))]

def nodeValue1682 : Sparse Master := [(Sum.inr 1682, (1 / 1))]

def nodeValue1683 : Sparse Master := [(Sum.inr 1683, (1 / 1))]

def nodeValue1684 : Sparse Master := [(Sum.inr 1684, (1 / 1))]

def nodeValue1685 : Sparse Master := [(Sum.inr 1685, (1 / 1))]

def nodeValue1686 : Sparse Master := [(Sum.inr 1686, (1 / 1))]

def nodeValue1687 : Sparse Master := [(Sum.inr 1687, (1 / 1))]

def nodeValue1688 : Sparse Master := [(Sum.inr 1688, (1 / 1))]

def nodeValue1689 : Sparse Master := [(Sum.inr 1689, (1 / 1))]

def nodeValue1690 : Sparse Master := [(Sum.inr 1690, (1 / 1))]

def nodeValue1691 : Sparse Master := [(Sum.inr 1691, (1 / 1))]

def nodeValue1692 : Sparse Master := [(Sum.inr 1692, (1 / 1))]

def nodeValue1693 : Sparse Master := [(Sum.inr 1693, (1 / 1))]

def nodeValue1694 : Sparse Master := [(Sum.inr 1694, (1 / 1))]

def nodeValue1695 : Sparse Master := [(Sum.inr 1695, (1 / 1))]

def nodeValue1697 : Sparse Master := [(Sum.inr 1697, (1 / 1))]

def nodeValue1698 : Sparse Master := []

def nodeValue1699 : Sparse Master := [(Sum.inr 1699, (1 / 1))]

def nodeValue1700 : Sparse Master := [(Sum.inr 1700, (1 / 1))]

def nodeValue1703 : Sparse Master := [(Sum.inr 1703, (1 / 1))]

def nodeValue1704 : Sparse Master := [(Sum.inr 1704, (1 / 1))]

def nodeValue1705 : Sparse Master := []

def nodeValue1706 : Sparse Master := [(Sum.inr 1706, (1 / 1))]

def nodeValue1707 : Sparse Master := [(Sum.inr 1707, (1 / 1))]

def nodeValue1708 : Sparse Master := [(Sum.inr 1708, (1 / 1))]

def nodeValue1709 : Sparse Master := [(Sum.inr 1709, (1 / 1))]

def nodeValue1710 : Sparse Master := [(Sum.inr 1710, (1 / 1))]

def nodeValue1711 : Sparse Master := [(Sum.inr 1711, (1 / 1))]

def nodeValue1712 : Sparse Master := [(Sum.inr 1712, (1 / 1))]

def nodeValue1713 : Sparse Master := [(Sum.inr 1713, (1 / 1))]

def nodeValue1714 : Sparse Master := [(Sum.inr 1714, (1 / 1))]

def nodeValue1715 : Sparse Master := [(Sum.inr 1715, (1 / 1))]

def nodeValue1716 : Sparse Master := [(Sum.inr 1716, (1 / 1))]

def nodeValue1720 : Sparse Master := [(Sum.inr 1720, (1 / 1))]

def nodeValue1721 : Sparse Master := [(Sum.inr 1721, (1 / 1))]

def nodeValue1722 : Sparse Master := [(Sum.inr 1722, (1 / 1))]

def nodeValue1723 : Sparse Master := [(Sum.inr 1723, (1 / 1))]

def nodeValue1724 : Sparse Master := [(Sum.inr 1724, (1 / 1))]

def nodeValue1725 : Sparse Master := [(Sum.inr 1725, (1 / 1))]

def nodeValue1726 : Sparse Master := []

def nodeValue1727 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1728 : Sparse Master := [(Sum.inr 1728, (1 / 1))]

def nodeValue1729 : Sparse Master := [(Sum.inr 1729, (1 / 1))]

def nodeValue1730 : Sparse Master := []

def nodeValue1734 : Sparse Master := [(Sum.inr 1734, (1 / 1))]

def nodeValue1735 : Sparse Master := [(Sum.inr 1735, (1 / 1))]

def nodeValue1736 : Sparse Master := [(Sum.inr 1736, (1 / 1))]

def nodeValue1737 : Sparse Master := [(Sum.inr 1737, (1 / 1))]

def nodeValue1738 : Sparse Master := [(Sum.inr 1738, (1 / 1))]

def nodeValue1739 : Sparse Master := [(Sum.inr 1739, (1 / 1))]

def nodeValue1740 : Sparse Master := [(Sum.inr 1740, (1 / 1))]

def nodeValue1741 : Sparse Master := [(Sum.inr 1741, (1 / 1))]

def nodeValue1742 : Sparse Master := [(Sum.inr 1742, (1 / 1))]

def nodeValue1743 : Sparse Master := [(Sum.inr 1743, (1 / 1))]

def nodeValue1744 : Sparse Master := [(Sum.inr 1744, (1 / 1))]

def nodeValue1745 : Sparse Master := [(Sum.inr 1745, (1 / 1))]

def nodeValue1746 : Sparse Master := [(Sum.inr 1746, (1 / 1))]

def nodeValue1747 : Sparse Master := [(Sum.inr 1747, (1 / 1))]

def nodeValue1748 : Sparse Master := [(Sum.inr 1748, (1 / 1))]

def nodeValue1749 : Sparse Master := [(Sum.inr 1749, (1 / 1))]

def nodeValue1750 : Sparse Master := [(Sum.inr 1750, (1 / 1))]

def nodeValue1751 : Sparse Master := [(Sum.inr 1751, (1 / 1))]

def nodeValue1752 : Sparse Master := [(Sum.inr 1752, (1 / 1))]

def nodeValue1753 : Sparse Master := []

def nodeValue1754 : Sparse Master := []

def nodeValue1755 : Sparse Master := []

def nodeValue1756 : Sparse Master := [(Sum.inr 1756, (1 / 1))]

def nodeValue1757 : Sparse Master := [(Sum.inr 1757, (1 / 1))]

def nodeValue1758 : Sparse Master := []

def nodeValue1759 : Sparse Master := [(Sum.inr 1759, (1 / 1))]

def nodeValue1760 : Sparse Master := [(Sum.inr 1760, (1 / 1))]

def nodeValue1761 : Sparse Master := [(Sum.inr 1761, (1 / 1))]

def nodeValue1762 : Sparse Master := [(Sum.inr 1762, (1 / 1))]

def nodeValue1763 : Sparse Master := [(Sum.inr 1763, (1 / 1))]

def nodeValue1764 : Sparse Master := [(Sum.inr 1764, (1 / 1))]

def nodeValue1765 : Sparse Master := [(Sum.inr 1765, (1 / 1))]

def nodeValue1766 : Sparse Master := [(Sum.inr 1766, (1 / 1))]

def nodeValue1767 : Sparse Master := [(Sum.inr 1767, (1 / 1))]

def nodeValue1769 : Sparse Master := [(Sum.inr 1769, (1 / 1))]

def nodeValue1771 : Sparse Master := [(Sum.inr 1771, (1 / 1))]

def nodeValue1773 : Sparse Master := [(Sum.inr 1773, (1 / 1))]

def nodeValue1774 : Sparse Master := [(Sum.inr 1774, (1 / 1))]

def nodeValue1776 : Sparse Master := [(Sum.inr 1776, (1 / 1))]

def nodeValue1778 : Sparse Master := [(Sum.inr 1778, (1 / 1))]

def nodeValue1781 : Sparse Master := [(Sum.inr 1781, (1 / 1))]

def nodeValue1782 : Sparse Master := [(Sum.inr 1782, (1 / 1))]

def nodeValue1783 : Sparse Master := [(Sum.inr 1783, (1 / 1))]

def nodeValue1784 : Sparse Master := [(Sum.inr 1784, (1 / 1))]

def nodeValue1786 : Sparse Master := [(Sum.inr 1786, (1 / 1))]

def nodeValue1787 : Sparse Master := [(Sum.inr 1787, (1 / 1))]

def nodeValue1789 : Sparse Master := [(Sum.inr 1789, (1 / 1))]

def nodeValue1790 : Sparse Master := [(Sum.inr 1790, (1 / 1))]

def nodeValue1791 : Sparse Master := [(Sum.inr 1791, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1792 : Sparse Master := [(Sum.inr 1792, (1 / 1))]

def nodeValue1793 : Sparse Master := [(Sum.inr 1793, (1 / 1))]

def nodeValue1794 : Sparse Master := [(Sum.inr 1794, (1 / 1))]

def nodeValue1795 : Sparse Master := [(Sum.inr 1795, (1 / 1))]

def nodeValue1796 : Sparse Master := [(Sum.inr 1796, (1 / 1))]

def nodeValue1797 : Sparse Master := [(Sum.inr 1797, (1 / 1))]

def nodeValue1798 : Sparse Master := [(Sum.inr 1798, (1 / 1))]

def nodeValue1799 : Sparse Master := [(Sum.inr 1799, (1 / 1))]

def nodeValue1801 : Sparse Master := [(Sum.inr 1801, (1 / 1))]

def nodeValue1802 : Sparse Master := [(Sum.inr 1802, (1 / 1))]

def nodeValue1803 : Sparse Master := [(Sum.inr 1803, (1 / 1))]

def nodeValue1804 : Sparse Master := [(Sum.inr 1804, (1 / 1))]

def nodeValue1805 : Sparse Master := [(Sum.inr 1805, (1 / 1))]

def nodeValue1806 : Sparse Master := [(Sum.inr 1806, (1 / 1))]

def nodeValue1807 : Sparse Master := [(Sum.inr 1807, (1 / 1))]

def nodeValue1808 : Sparse Master := [(Sum.inr 1808, (1 / 1))]

def nodeValue1809 : Sparse Master := [(Sum.inr 1809, (1 / 1))]

def nodeValue1810 : Sparse Master := [(Sum.inr 1810, (1 / 1))]

def nodeValue1811 : Sparse Master := [(Sum.inr 1811, (1 / 1))]

def nodeValue1812 : Sparse Master := [(Sum.inr 1812, (1 / 1))]

def nodeValue1813 : Sparse Master := [(Sum.inr 1813, (1 / 1))]

def nodeValue1814 : Sparse Master := [(Sum.inr 1814, (1 / 1))]

def nodeValue1815 : Sparse Master := [(Sum.inr 1815, (1 / 1))]

def nodeValue1816 : Sparse Master := [(Sum.inr 1816, (1 / 1))]

def nodeValue1817 : Sparse Master := [(Sum.inr 1817, (1 / 1))]

def nodeValue1818 : Sparse Master := [(Sum.inr 1818, (1 / 1))]

def nodeValue1819 : Sparse Master := [(Sum.inr 1819, (1 / 1))]

def nodeValue1820 : Sparse Master := [(Sum.inr 1820, (1 / 1))]

def nodeValue1821 : Sparse Master := [(Sum.inr 1821, (1 / 1))]

def nodeValue1822 : Sparse Master := [(Sum.inr 1822, (1 / 1))]

def nodeValue1823 : Sparse Master := [(Sum.inr 1823, (1 / 1))]

def nodeValue1824 : Sparse Master := [(Sum.inr 1824, (1 / 1))]

def nodeValue1825 : Sparse Master := [(Sum.inr 1825, (1 / 1))]

def nodeValue1826 : Sparse Master := [(Sum.inr 1826, (1 / 1))]

def nodeValue1827 : Sparse Master := [(Sum.inr 1827, (1 / 1))]

def nodeValue1828 : Sparse Master := [(Sum.inr 1828, (1 / 1))]

def nodeValue1829 : Sparse Master := [(Sum.inr 1829, (1 / 1))]

def nodeValue1830 : Sparse Master := [(Sum.inr 1830, (1 / 1))]

def nodeValue1831 : Sparse Master := [(Sum.inr 1831, (1 / 1))]

def nodeValue1832 : Sparse Master := [(Sum.inr 1832, (1 / 1))]

def nodeValue1833 : Sparse Master := [(Sum.inr 1833, (1 / 1))]

def nodeValue1835 : Sparse Master := [(Sum.inr 1835, (1 / 1))]

def nodeValue1836 : Sparse Master := [(Sum.inr 1836, (1 / 1))]

def nodeValue1837 : Sparse Master := [(Sum.inr 1837, (1 / 1))]

def nodeValue1838 : Sparse Master := [(Sum.inr 1838, (1 / 1))]

def nodeValue1840 : Sparse Master := [(Sum.inr 1840, (1 / 1))]

def nodeValue1841 : Sparse Master := [(Sum.inr 1841, (1 / 1))]

def nodeValue1842 : Sparse Master := [(Sum.inr 1842, (1 / 1))]

def nodeValue1843 : Sparse Master := [(Sum.inr 1843, (1 / 1))]

def nodeValue1844 : Sparse Master := [(Sum.inr 1844, (1 / 1))]

def nodeValue1846 : Sparse Master := [(Sum.inr 1846, (1 / 1))]

def nodeValue1847 : Sparse Master := [(Sum.inr 1847, (1 / 1))]

def nodeValue1848 : Sparse Master := [(Sum.inr 1848, (1 / 1))]

def nodeValue1849 : Sparse Master := [(Sum.inr 1849, (1 / 1))]

def nodeValue1850 : Sparse Master := [(Sum.inr 1850, (1 / 1))]

def nodeValue1851 : Sparse Master := [(Sum.inr 1851, (1 / 1))]

def nodeValue1854 : Sparse Master := [(Sum.inr 1854, (1 / 1))]

def nodeValue1855 : Sparse Master := [(Sum.inr 1855, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1857 : Sparse Master := [(Sum.inr 1857, (1 / 1))]

def nodeValue1858 : Sparse Master := [(Sum.inr 1858, (1 / 1))]

def nodeValue1860 : Sparse Master := [(Sum.inr 1860, (1 / 1))]

def nodeValue1861 : Sparse Master := [(Sum.inr 1861, (1 / 1))]

def nodeValue1863 : Sparse Master := [(Sum.inr 1863, (1 / 1))]

def nodeValue1864 : Sparse Master := [(Sum.inr 1864, (1 / 1))]

def nodeValue1867 : Sparse Master := [(Sum.inr 1867, (1 / 1))]

def nodeValue1870 : Sparse Master := [(Sum.inr 1870, (1 / 1))]

def nodeValue1871 : Sparse Master := [(Sum.inr 1871, (1 / 1))]

def nodeValue1873 : Sparse Master := [(Sum.inr 1873, (1 / 1))]

def nodeValue1874 : Sparse Master := [(Sum.inr 1874, (1 / 1))]

def nodeValue1875 : Sparse Master := [(Sum.inr 1875, (1 / 1))]

def nodeValue1876 : Sparse Master := [(Sum.inr 1876, (1 / 1))]

def nodeValue1877 : Sparse Master := [(Sum.inr 1877, (1 / 1))]

def nodeValue1878 : Sparse Master := [(Sum.inr 1878, (1 / 1))]

def nodeValue1879 : Sparse Master := [(Sum.inr 1879, (1 / 1))]

def nodeValue1880 : Sparse Master := [(Sum.inr 1880, (1 / 1))]

def nodeValue1881 : Sparse Master := [(Sum.inr 1881, (1 / 1))]

def nodeValue1882 : Sparse Master := [(Sum.inr 1882, (1 / 1))]

def nodeValue1883 : Sparse Master := [(Sum.inr 1883, (1 / 1))]

def nodeValue1884 : Sparse Master := [(Sum.inr 1884, (1 / 1))]

def nodeValue1886 : Sparse Master := [(Sum.inr 1886, (1 / 1))]

def nodeValue1887 : Sparse Master := [(Sum.inr 1887, (1 / 1))]

def nodeValue1888 : Sparse Master := [(Sum.inr 1888, (1 / 1))]

def nodeValue1889 : Sparse Master := [(Sum.inr 1889, (1 / 1))]

def nodeValue1891 : Sparse Master := [(Sum.inr 1891, (1 / 1))]

def nodeValue1892 : Sparse Master := [(Sum.inr 1892, (1 / 1))]

def nodeValue1893 : Sparse Master := [(Sum.inr 1893, (1 / 1))]

def nodeValue1894 : Sparse Master := [(Sum.inr 1894, (1 / 1))]

def nodeValue1896 : Sparse Master := [(Sum.inr 1896, (1 / 1))]

def nodeValue1897 : Sparse Master := [(Sum.inr 1897, (1 / 1))]

def nodeValue1898 : Sparse Master := [(Sum.inr 1898, (1 / 1))]

def nodeValue1900 : Sparse Master := [(Sum.inr 1900, (1 / 1))]

def nodeValue1901 : Sparse Master := [(Sum.inr 1901, (1 / 1))]

def nodeValue1902 : Sparse Master := [(Sum.inr 1902, (1 / 1))]

def nodeValue1903 : Sparse Master := [(Sum.inr 1903, (1 / 1))]

def nodeValue1904 : Sparse Master := [(Sum.inr 1904, (1 / 1))]

def nodeValue1905 : Sparse Master := [(Sum.inr 1905, (1 / 1))]

def nodeValue1906 : Sparse Master := [(Sum.inr 1906, (1 / 1))]

def nodeValue1907 : Sparse Master := [(Sum.inr 1907, (1 / 1))]

def nodeValue1908 : Sparse Master := []

def nodeValue1909 : Sparse Master := [(Sum.inr 1909, (1 / 1))]

def nodeValue1910 : Sparse Master := [(Sum.inr 1910, (1 / 1))]

def nodeValue1911 : Sparse Master := []

def nodeValue1912 : Sparse Master := []

def nodeValue1913 : Sparse Master := [(Sum.inr 1913, (1 / 1))]

def nodeValue1914 : Sparse Master := []

def nodeValue1915 : Sparse Master := [(Sum.inr 1915, (1 / 1))]

def nodeValue1916 : Sparse Master := [(Sum.inr 1916, (1 / 1))]

def nodeValue1917 : Sparse Master := [(Sum.inr 1917, (1 / 1))]

def nodeValue1918 : Sparse Master := []

def nodeValue1919 : Sparse Master := [(Sum.inr 1919, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue192 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 257, (5 / 54)), (Sum.inl 60, (5 / 54)), (Sum.inl 268, (-5 / 18)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 288)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 288))]

def nodeValue193 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 264, (-5 / 18)), (Sum.inl 266, (-5 / 18)), (Sum.inl 65, (-5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-35 / 432)), (Sum.inl 54, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-35 / 432))]

def nodeValue194 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 257, (5 / 54)), (Sum.inl 60, (5 / 27)), (Sum.inl 264, (-5 / 18)), (Sum.inl 32, (5 / 54)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 36)), (Sum.inl 35, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue195 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 266, (-5 / 18)), (Sum.inl 61, (-5 / 18)), (Sum.inl 268, (-5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 216)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 432))]

def nodeValue196 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 266, (5 / 9)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue197 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 268, (5 / 9)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 432))]

def nodeValue206 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 9, (-5 / 216)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-35 / 864)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (-5 / 144)), (Sum.inl 70, (-5 / 54)), (Sum.inl 71, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-5 / 54)), (Sum.inl 197, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue207 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-25 / 432)), (Sum.inl 68, (5 / 72)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-10 / 27)), (Sum.inl 125, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-25 / 54)), (Sum.inl 52, (-10 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue208 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (-5 / 216)), (Sum.inl 257, (-5 / 54)), (Sum.inl 260, (5 / 18)), (Sum.inl 60, (-25 / 54)), (Sum.inl 264, (5 / 18)), (Sum.inl 62, (5 / 9)), (Sum.inl 32, (-5 / 18)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (-5 / 864)), (Sum.inl 35, (-25 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-65 / 54)), (Sum.inl 128, (-5 / 27)), (Sum.inl 495, (-5 / 54)), (Sum.inl 52, (-10 / 27)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue209 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 72)), (Sum.inl 6, (5 / 432)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-25 / 432)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-10 / 27)), (Sum.inl 125, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 196, (5 / 18)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 9)), (Sum.inl 12, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 48))]

def nodeValue210 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (35 / 216)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 216)), (Sum.inl 71, (-5 / 27)), (Sum.inl 8, (-5 / 18)), (Sum.inl 197, (5 / 9)), (Sum.inl 24, (5 / 18)), (Sum.inl 56, (5 / 9)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (5 / 108))]

def nodeValue211 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 9, (5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-25 / 864)), (Sum.inl 69, (5 / 54)), (Sum.inl 125, (-5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (-65 / 864))]

def nodeValue212 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (-25 / 864)), (Sum.inl 257, (-5 / 54)), (Sum.inl 60, (-5 / 27)), (Sum.inl 262, (5 / 18)), (Sum.inl 268, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (5 / 96)), (Sum.inl 35, (-10 / 27)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 18)), (Sum.inl 128, (-5 / 54)), (Sum.inl 495, (-5 / 54)), (Sum.inl 52, (-5 / 18)), (Sum.inl 56, (5 / 18)), (Sum.inl 26, (-5 / 18)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (-25 / 864))]

def nodeValue213 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 216)), (Sum.inl 259, (5 / 18)), (Sum.inl 59, (5 / 18)), (Sum.inl 262, (5 / 18)), (Sum.inl 266, (5 / 18)), (Sum.inl 61, (5 / 9)), (Sum.inl 268, (5 / 18)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (25 / 864)), (Sum.inl 35, (-5 / 27)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 54, (5 / 9)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 27)), (Sum.inl 56, (5 / 9)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (5 / 864))]

def nodeValue214 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 259, (-5 / 18)), (Sum.inl 266, (-5 / 18)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 72))]

def nodeValue218 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 60, (-10 / 27)), (Sum.inl 62, (5 / 9)), (Sum.inl 32, (-10 / 27)), (Sum.inl 2, (-5 / 432)), (Sum.inl 35, (-10 / 27)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-40 / 27)), (Sum.inl 128, (-5 / 54)), (Sum.inl 52, (-10 / 27)), (Sum.inl 12, (-5 / 54))]

def nodeValue220 : Sparse Master := [(Sum.inl 0, (7 / 144)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 216)), (Sum.inl 2, (-5 / 72)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 54, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue221 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (25 / 216)), (Sum.inl 6, (-5 / 288)), (Sum.inl 2, (35 / 864)), (Sum.inl 35, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 3, (-5 / 18)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 56, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (85 / 864))]

def nodeValue222 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (-25 / 432)), (Sum.inl 35, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue223 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (5 / 72)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (5 / 432)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-20 / 27)), (Sum.inl 13, (-5 / 6)), (Sum.inl 52, (-5 / 27)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-10 / 27)), (Sum.inl 1, (65 / 864))]

def nodeValue224 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (5 / 864)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (35 / 864))]

def nodeValue225 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 6, (5 / 432)), (Sum.inl 60, (5 / 54)), (Sum.inl 62, (-5 / 18)), (Sum.inl 32, (5 / 54)), (Sum.inl 2, (-5 / 216)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 18)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (5 / 216))]

def nodeValue226 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 72)), (Sum.inl 2, (-25 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 1, (-55 / 864))]

def nodeValue227 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 5, (-5 / 54)), (Sum.inl 2, (5 / 108)), (Sum.inl 8, (5 / 54)), (Sum.inl 56, (-5 / 18)), (Sum.inl 1, (35 / 432))]

def nodeValue228 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 6, (5 / 432)), (Sum.inl 60, (5 / 27)), (Sum.inl 32, (5 / 27)), (Sum.inl 2, (-5 / 54)), (Sum.inl 13, (5 / 9)), (Sum.inl 128, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-25 / 432))]

def nodeValue229 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 59, (-5 / 18)), (Sum.inl 61, (-5 / 18)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue231 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (25 / 864)), (Sum.inl 54, (-5 / 18)), (Sum.inl 56, (-5 / 18)), (Sum.inl 228, (-5 / 18)), (Sum.inl 1, (-5 / 864))]

def nodeValue232 : Sparse Master := [(Sum.inl 0, (47 / 864)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-25 / 216)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (-35 / 288))]

def nodeValue233 : Sparse Master := [(Sum.inl 0, (13 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (185 / 864)), (Sum.inl 35, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue234 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-5 / 144)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-5 / 288))]

def nodeValue235 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-5 / 288)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 18)), (Sum.inl 52, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue236 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-35 / 432)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue237 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (85 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue238 : Sparse Master := [(Sum.inl 0, (25 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 60, (-5 / 54)), (Sum.inl 61, (5 / 18)), (Sum.inl 62, (5 / 18)), (Sum.inl 32, (-5 / 54)), (Sum.inl 33, (5 / 18)), (Sum.inl 34, (-5 / 54)), (Sum.inl 2, (5 / 288)), (Sum.inl 35, (-5 / 27)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-20 / 27)), (Sum.inl 13, (-25 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 54, (5 / 9)), (Sum.inl 12, (-10 / 27)), (Sum.inl 56, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (35 / 864))]

def nodeValue239 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 60, (5 / 54)), (Sum.inl 34, (5 / 54)), (Sum.inl 2, (5 / 864)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (35 / 864))]

def nodeValue240 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 61, (-5 / 18)), (Sum.inl 2, (25 / 432)), (Sum.inl 51, (-5 / 18)), (Sum.inl 54, (-5 / 18)), (Sum.inl 56, (-5 / 18)), (Sum.inl 1, (5 / 144))]

def nodeValue242 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 62, (5 / 9)), (Sum.inl 33, (5 / 6)), (Sum.inl 2, (-85 / 864)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-5 / 9)), (Sum.inl 13, (-5 / 18)), (Sum.inl 54, (5 / 6)), (Sum.inl 26, (-5 / 18)), (Sum.inl 1, (-65 / 864))]

def nodeValue243 : Sparse Master := [(Sum.inl 0, (11 / 288)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (5 / 288)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-25 / 54)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-5 / 27)), (Sum.inl 56, (5 / 9)), (Sum.inl 26, (-10 / 27)), (Sum.inl 4, (-10 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue244 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-5 / 72)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (-5 / 48))]

def nodeValue245 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (25 / 864)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 56, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue246 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 62, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 1, (-5 / 144))]

def nodeValue247 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 216)), (Sum.inl 35, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue248 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 144)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 18)), (Sum.inl 54, (-5 / 18)), (Sum.inl 12, (5 / 27)), (Sum.inl 1, (145 / 864))]

def nodeValue249 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 6, (5 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (5 / 27))]

def nodeValue250 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 6, (5 / 432)), (Sum.inl 62, (5 / 9)), (Sum.inl 2, (-5 / 54)), (Sum.inl 1, (-25 / 432))]

def nodeValue251 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (-5 / 432)), (Sum.inl 54, (5 / 9)), (Sum.inl 1, (55 / 432))]

def nodeValue252 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 108)), (Sum.inl 56, (5 / 9)), (Sum.inl 1, (5 / 216))]

def nodeValue253 : Sparse Master := [(Sum.inl 0, (1 / 27)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 60, (-5 / 18)), (Sum.inl 61, (5 / 6)), (Sum.inl 32, (-5 / 27)), (Sum.inl 34, (-5 / 9)), (Sum.inl 2, (-25 / 288)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-35 / 27)), (Sum.inl 12, (-5 / 18)), (Sum.inl 26, (-5 / 18)), (Sum.inl 1, (-5 / 48))]

def nodeValue254 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 60, (5 / 54)), (Sum.inl 61, (-5 / 18)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (5 / 216))]

def nodeValue255 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 6, (5 / 432)), (Sum.inl 60, (-5 / 27)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-5 / 54)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1920 : Sparse Master := [(Sum.inr 1920, (1 / 1))]

def nodeValue1921 : Sparse Master := [(Sum.inr 1921, (1 / 1))]

def nodeValue1922 : Sparse Master := [(Sum.inr 1922, (1 / 1))]

def nodeValue1923 : Sparse Master := [(Sum.inr 1923, (1 / 1))]

def nodeValue1924 : Sparse Master := [(Sum.inr 1924, (1 / 1))]

def nodeValue1925 : Sparse Master := [(Sum.inr 1925, (1 / 1))]

def nodeValue1926 : Sparse Master := [(Sum.inr 1926, (1 / 1))]

def nodeValue1927 : Sparse Master := [(Sum.inr 1927, (1 / 1))]

def nodeValue1928 : Sparse Master := [(Sum.inr 1928, (1 / 1))]

def nodeValue1929 : Sparse Master := [(Sum.inr 1929, (1 / 1))]

def nodeValue1935 : Sparse Master := [(Sum.inr 1935, (1 / 1))]

def nodeValue1936 : Sparse Master := [(Sum.inr 1936, (1 / 1))]

def nodeValue1937 : Sparse Master := [(Sum.inr 1937, (1 / 1))]

def nodeValue1938 : Sparse Master := [(Sum.inr 1938, (1 / 1))]

def nodeValue1939 : Sparse Master := [(Sum.inr 1939, (1 / 1))]

def nodeValue1940 : Sparse Master := [(Sum.inr 1940, (1 / 1))]

def nodeValue1941 : Sparse Master := [(Sum.inr 1941, (1 / 1))]

def nodeValue1942 : Sparse Master := [(Sum.inr 1942, (1 / 1))]

def nodeValue1944 : Sparse Master := []

def nodeValue1945 : Sparse Master := []

def nodeValue1946 : Sparse Master := [(Sum.inr 1946, (1 / 1))]

def nodeValue1947 : Sparse Master := []

def nodeValue1948 : Sparse Master := [(Sum.inr 1948, (1 / 1))]

def nodeValue1949 : Sparse Master := [(Sum.inr 1949, (1 / 1))]

def nodeValue1950 : Sparse Master := []

def nodeValue1951 : Sparse Master := [(Sum.inr 1951, (1 / 1))]

def nodeValue1952 : Sparse Master := [(Sum.inr 1952, (1 / 1))]

def nodeValue1953 : Sparse Master := []

def nodeValue1955 : Sparse Master := [(Sum.inr 1955, (1 / 1))]

def nodeValue1956 : Sparse Master := [(Sum.inr 1956, (1 / 1))]

def nodeValue1957 : Sparse Master := [(Sum.inr 1957, (1 / 1))]

def nodeValue1959 : Sparse Master := [(Sum.inr 1959, (1 / 1))]

def nodeValue1960 : Sparse Master := [(Sum.inr 1960, (1 / 1))]

def nodeValue1961 : Sparse Master := [(Sum.inr 1961, (1 / 1))]

def nodeValue1963 : Sparse Master := [(Sum.inr 1963, (1 / 1))]

def nodeValue1964 : Sparse Master := [(Sum.inr 1964, (1 / 1))]

def nodeValue1965 : Sparse Master := [(Sum.inr 1965, (1 / 1))]

def nodeValue1966 : Sparse Master := [(Sum.inr 1966, (1 / 1))]

def nodeValue1967 : Sparse Master := [(Sum.inr 1967, (1 / 1))]

def nodeValue1969 : Sparse Master := [(Sum.inr 1969, (1 / 1))]

def nodeValue1970 : Sparse Master := [(Sum.inr 1970, (1 / 1))]

def nodeValue1971 : Sparse Master := [(Sum.inr 1971, (1 / 1))]

def nodeValue1972 : Sparse Master := [(Sum.inr 1972, (1 / 1))]

def nodeValue1973 : Sparse Master := [(Sum.inr 1973, (1 / 1))]

def nodeValue1974 : Sparse Master := [(Sum.inr 1974, (1 / 1))]

def nodeValue1975 : Sparse Master := [(Sum.inr 1975, (1 / 1))]

def nodeValue1976 : Sparse Master := [(Sum.inr 1976, (1 / 1))]

def nodeValue1977 : Sparse Master := [(Sum.inr 1977, (1 / 1))]

def nodeValue1978 : Sparse Master := [(Sum.inr 1978, (1 / 1))]

def nodeValue1979 : Sparse Master := [(Sum.inr 1979, (1 / 1))]

def nodeValue1980 : Sparse Master := [(Sum.inr 1980, (1 / 1))]

def nodeValue1982 : Sparse Master := [(Sum.inr 1982, (1 / 1))]

def nodeValue1983 : Sparse Master := [(Sum.inr 1983, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1986 : Sparse Master := [(Sum.inr 1986, (1 / 1))]

def nodeValue1987 : Sparse Master := [(Sum.inr 1987, (1 / 1))]

def nodeValue1989 : Sparse Master := [(Sum.inr 1989, (1 / 1))]

def nodeValue1990 : Sparse Master := [(Sum.inr 1990, (1 / 1))]

def nodeValue1991 : Sparse Master := [(Sum.inr 1991, (1 / 1))]

def nodeValue1992 : Sparse Master := [(Sum.inr 1992, (1 / 1))]

def nodeValue1993 : Sparse Master := [(Sum.inr 1993, (1 / 1))]

def nodeValue1994 : Sparse Master := [(Sum.inr 1994, (1 / 1))]

def nodeValue1995 : Sparse Master := [(Sum.inr 1995, (1 / 1))]

def nodeValue1996 : Sparse Master := [(Sum.inr 1996, (1 / 1))]

def nodeValue1997 : Sparse Master := [(Sum.inr 1997, (1 / 1))]

def nodeValue1998 : Sparse Master := [(Sum.inr 1998, (1 / 1))]

def nodeValue2000 : Sparse Master := [(Sum.inr 2000, (1 / 1))]

def nodeValue2001 : Sparse Master := [(Sum.inr 2001, (1 / 1))]

def nodeValue2002 : Sparse Master := [(Sum.inr 2002, (1 / 1))]

def nodeValue2003 : Sparse Master := [(Sum.inr 2003, (1 / 1))]

def nodeValue2004 : Sparse Master := [(Sum.inr 2004, (1 / 1))]

def nodeValue2005 : Sparse Master := [(Sum.inr 2005, (1 / 1))]

def nodeValue2006 : Sparse Master := [(Sum.inr 2006, (1 / 1))]

def nodeValue2008 : Sparse Master := [(Sum.inr 2008, (1 / 1))]

def nodeValue2009 : Sparse Master := [(Sum.inr 2009, (1 / 1))]

def nodeValue2010 : Sparse Master := [(Sum.inr 2010, (1 / 1))]

def nodeValue2011 : Sparse Master := [(Sum.inr 2011, (1 / 1))]

def nodeValue2012 : Sparse Master := [(Sum.inr 2012, (1 / 1))]

def nodeValue2013 : Sparse Master := [(Sum.inr 2013, (1 / 1))]

def nodeValue2014 : Sparse Master := [(Sum.inr 2014, (1 / 1))]

def nodeValue2015 : Sparse Master := [(Sum.inr 2015, (1 / 1))]

def nodeValue2016 : Sparse Master := [(Sum.inr 2016, (1 / 1))]

def nodeValue2017 : Sparse Master := [(Sum.inr 2017, (1 / 1))]

def nodeValue2018 : Sparse Master := [(Sum.inr 2018, (1 / 1))]

def nodeValue2019 : Sparse Master := [(Sum.inr 2019, (1 / 1))]

def nodeValue2020 : Sparse Master := [(Sum.inr 2020, (1 / 1))]

def nodeValue2021 : Sparse Master := [(Sum.inr 2021, (1 / 1))]

def nodeValue2022 : Sparse Master := [(Sum.inr 2022, (1 / 1))]

def nodeValue2023 : Sparse Master := [(Sum.inr 2023, (1 / 1))]

def nodeValue2024 : Sparse Master := [(Sum.inr 2024, (1 / 1))]

def nodeValue2025 : Sparse Master := [(Sum.inr 2025, (1 / 1))]

def nodeValue2026 : Sparse Master := [(Sum.inr 2026, (1 / 1))]

def nodeValue2027 : Sparse Master := [(Sum.inr 2027, (1 / 1))]

def nodeValue2028 : Sparse Master := [(Sum.inr 2028, (1 / 1))]

def nodeValue2029 : Sparse Master := [(Sum.inr 2029, (1 / 1))]

def nodeValue2030 : Sparse Master := [(Sum.inr 2030, (1 / 1))]

def nodeValue2031 : Sparse Master := [(Sum.inr 2031, (1 / 1))]

def nodeValue2032 : Sparse Master := [(Sum.inr 2032, (1 / 1))]

def nodeValue2033 : Sparse Master := [(Sum.inr 2033, (1 / 1))]

def nodeValue2034 : Sparse Master := [(Sum.inr 2034, (1 / 1))]

def nodeValue2035 : Sparse Master := [(Sum.inr 2035, (1 / 1))]

def nodeValue2036 : Sparse Master := [(Sum.inr 2036, (1 / 1))]

def nodeValue2037 : Sparse Master := [(Sum.inr 2037, (1 / 1))]

def nodeValue2038 : Sparse Master := [(Sum.inr 2038, (1 / 1))]

def nodeValue2039 : Sparse Master := [(Sum.inr 2039, (1 / 1))]

def nodeValue2040 : Sparse Master := [(Sum.inr 2040, (1 / 1))]

def nodeValue2041 : Sparse Master := [(Sum.inr 2041, (1 / 1))]

def nodeValue2042 : Sparse Master := [(Sum.inr 2042, (1 / 1))]

def nodeValue2043 : Sparse Master := [(Sum.inr 2043, (1 / 1))]

def nodeValue2044 : Sparse Master := [(Sum.inr 2044, (1 / 1))]

def nodeValue2045 : Sparse Master := [(Sum.inr 2045, (1 / 1))]

def nodeValue2046 : Sparse Master := [(Sum.inr 2046, (1 / 1))]

def nodeValue2047 : Sparse Master := [(Sum.inr 2047, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2048 : Sparse Master := [(Sum.inr 2048, (1 / 1))]

def nodeValue2049 : Sparse Master := [(Sum.inr 2049, (1 / 1))]

def nodeValue2050 : Sparse Master := [(Sum.inr 2050, (1 / 1))]

def nodeValue2051 : Sparse Master := [(Sum.inr 2051, (1 / 1))]

def nodeValue2052 : Sparse Master := [(Sum.inr 2052, (1 / 1))]

def nodeValue2053 : Sparse Master := []

def nodeValue2054 : Sparse Master := [(Sum.inr 2054, (1 / 1))]

def nodeValue2055 : Sparse Master := [(Sum.inr 2055, (1 / 1))]

def nodeValue2056 : Sparse Master := []

def nodeValue2057 : Sparse Master := []

def nodeValue2058 : Sparse Master := [(Sum.inr 2058, (1 / 1))]

def nodeValue2059 : Sparse Master := [(Sum.inr 2059, (1 / 1))]

def nodeValue2060 : Sparse Master := []

def nodeValue2062 : Sparse Master := [(Sum.inr 2062, (1 / 1))]

def nodeValue2063 : Sparse Master := [(Sum.inr 2063, (1 / 1))]

def nodeValue2064 : Sparse Master := [(Sum.inr 2064, (1 / 1))]

def nodeValue2065 : Sparse Master := [(Sum.inr 2065, (1 / 1))]

def nodeValue2066 : Sparse Master := []

def nodeValue2067 : Sparse Master := [(Sum.inr 2067, (1 / 1))]

def nodeValue2070 : Sparse Master := [(Sum.inr 2070, (1 / 1))]

def nodeValue2071 : Sparse Master := [(Sum.inr 2071, (1 / 1))]

def nodeValue2072 : Sparse Master := [(Sum.inr 2072, (1 / 1))]

def nodeValue2073 : Sparse Master := [(Sum.inr 2073, (1 / 1))]

def nodeValue2074 : Sparse Master := [(Sum.inr 2074, (1 / 1))]

def nodeValue2075 : Sparse Master := [(Sum.inr 2075, (1 / 1))]

def nodeValue2076 : Sparse Master := [(Sum.inr 2076, (1 / 1))]

def nodeValue2077 : Sparse Master := [(Sum.inr 2077, (1 / 1))]

def nodeValue2078 : Sparse Master := [(Sum.inr 2078, (1 / 1))]

def nodeValue2079 : Sparse Master := [(Sum.inr 2079, (1 / 1))]

def nodeValue2080 : Sparse Master := [(Sum.inr 2080, (1 / 1))]

def nodeValue2081 : Sparse Master := [(Sum.inr 2081, (1 / 1))]

def nodeValue2082 : Sparse Master := [(Sum.inr 2082, (1 / 1))]

def nodeValue2083 : Sparse Master := [(Sum.inr 2083, (1 / 1))]

def nodeValue2084 : Sparse Master := [(Sum.inr 2084, (1 / 1))]

def nodeValue2085 : Sparse Master := [(Sum.inr 2085, (1 / 1))]

def nodeValue2086 : Sparse Master := [(Sum.inr 2086, (1 / 1))]

def nodeValue2087 : Sparse Master := [(Sum.inr 2087, (1 / 1))]

def nodeValue2088 : Sparse Master := [(Sum.inr 2088, (1 / 1))]

def nodeValue2089 : Sparse Master := [(Sum.inr 2089, (1 / 1))]

def nodeValue2090 : Sparse Master := [(Sum.inr 2090, (1 / 1))]

def nodeValue2091 : Sparse Master := [(Sum.inr 2091, (1 / 1))]

def nodeValue2092 : Sparse Master := [(Sum.inr 2092, (1 / 1))]

def nodeValue2093 : Sparse Master := [(Sum.inr 2093, (1 / 1))]

def nodeValue2094 : Sparse Master := [(Sum.inr 2094, (1 / 1))]

def nodeValue2095 : Sparse Master := [(Sum.inr 2095, (1 / 1))]

def nodeValue2096 : Sparse Master := [(Sum.inr 2096, (1 / 1))]

def nodeValue2097 : Sparse Master := [(Sum.inr 2097, (1 / 1))]

def nodeValue2098 : Sparse Master := [(Sum.inr 2098, (1 / 1))]

def nodeValue2099 : Sparse Master := [(Sum.inr 2099, (1 / 1))]

def nodeValue2100 : Sparse Master := [(Sum.inr 2100, (1 / 1))]

def nodeValue2101 : Sparse Master := [(Sum.inr 2101, (1 / 1))]

def nodeValue2102 : Sparse Master := [(Sum.inr 2102, (1 / 1))]

def nodeValue2103 : Sparse Master := [(Sum.inr 2103, (1 / 1))]

def nodeValue2104 : Sparse Master := [(Sum.inr 2104, (1 / 1))]

def nodeValue2105 : Sparse Master := [(Sum.inr 2105, (1 / 1))]

def nodeValue2106 : Sparse Master := [(Sum.inr 2106, (1 / 1))]

def nodeValue2107 : Sparse Master := [(Sum.inr 2107, (1 / 1))]

def nodeValue2108 : Sparse Master := [(Sum.inr 2108, (1 / 1))]

def nodeValue2109 : Sparse Master := [(Sum.inr 2109, (1 / 1))]

def nodeValue2110 : Sparse Master := [(Sum.inr 2110, (1 / 1))]

def nodeValue2111 : Sparse Master := [(Sum.inr 2111, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2112 : Sparse Master := [(Sum.inr 2112, (1 / 1))]

def nodeValue2113 : Sparse Master := [(Sum.inr 2113, (1 / 1))]

def nodeValue2114 : Sparse Master := [(Sum.inr 2114, (1 / 1))]

def nodeValue2115 : Sparse Master := [(Sum.inr 2115, (1 / 1))]

def nodeValue2116 : Sparse Master := [(Sum.inr 2116, (1 / 1))]

def nodeValue2117 : Sparse Master := [(Sum.inr 2117, (1 / 1))]

def nodeValue2118 : Sparse Master := [(Sum.inr 2118, (1 / 1))]

def nodeValue2119 : Sparse Master := [(Sum.inr 2119, (1 / 1))]

def nodeValue2121 : Sparse Master := [(Sum.inr 2121, (1 / 1))]

def nodeValue2122 : Sparse Master := [(Sum.inr 2122, (1 / 1))]

def nodeValue2123 : Sparse Master := [(Sum.inr 2123, (1 / 1))]

def nodeValue2124 : Sparse Master := [(Sum.inr 2124, (1 / 1))]

def nodeValue2125 : Sparse Master := [(Sum.inr 2125, (1 / 1))]

def nodeValue2126 : Sparse Master := [(Sum.inr 2126, (1 / 1))]

def nodeValue2127 : Sparse Master := [(Sum.inr 2127, (1 / 1))]

def nodeValue2128 : Sparse Master := [(Sum.inr 2128, (1 / 1))]

def nodeValue2129 : Sparse Master := [(Sum.inr 2129, (1 / 1))]

def nodeValue2130 : Sparse Master := [(Sum.inr 2130, (1 / 1))]

def nodeValue2131 : Sparse Master := [(Sum.inr 2131, (1 / 1))]

def nodeValue2132 : Sparse Master := [(Sum.inr 2132, (1 / 1))]

def nodeValue2133 : Sparse Master := [(Sum.inr 2133, (1 / 1))]

def nodeValue2134 : Sparse Master := [(Sum.inr 2134, (1 / 1))]

def nodeValue2136 : Sparse Master := [(Sum.inr 2136, (1 / 1))]

def nodeValue2137 : Sparse Master := [(Sum.inr 2137, (1 / 1))]

def nodeValue2138 : Sparse Master := [(Sum.inr 2138, (1 / 1))]

def nodeValue2139 : Sparse Master := [(Sum.inr 2139, (1 / 1))]

def nodeValue2140 : Sparse Master := [(Sum.inr 2140, (1 / 1))]

def nodeValue2141 : Sparse Master := [(Sum.inr 2141, (1 / 1))]

def nodeValue2142 : Sparse Master := [(Sum.inr 2142, (1 / 1))]

def nodeValue2143 : Sparse Master := [(Sum.inr 2143, (1 / 1))]

def nodeValue2144 : Sparse Master := [(Sum.inr 2144, (1 / 1))]

def nodeValue2145 : Sparse Master := [(Sum.inr 2145, (1 / 1))]

def nodeValue2146 : Sparse Master := [(Sum.inr 2146, (1 / 1))]

def nodeValue2147 : Sparse Master := [(Sum.inr 2147, (1 / 1))]

def nodeValue2148 : Sparse Master := [(Sum.inr 2148, (1 / 1))]

def nodeValue2149 : Sparse Master := [(Sum.inr 2149, (1 / 1))]

def nodeValue2150 : Sparse Master := [(Sum.inr 2150, (1 / 1))]

def nodeValue2151 : Sparse Master := [(Sum.inr 2151, (1 / 1))]

def nodeValue2152 : Sparse Master := [(Sum.inr 2152, (1 / 1))]

def nodeValue2153 : Sparse Master := [(Sum.inr 2153, (1 / 1))]

def nodeValue2154 : Sparse Master := [(Sum.inr 2154, (1 / 1))]

def nodeValue2155 : Sparse Master := [(Sum.inr 2155, (1 / 1))]

def nodeValue2156 : Sparse Master := [(Sum.inr 2156, (1 / 1))]

def nodeValue2157 : Sparse Master := [(Sum.inr 2157, (1 / 1))]

def nodeValue2158 : Sparse Master := [(Sum.inr 2158, (1 / 1))]

def nodeValue2159 : Sparse Master := [(Sum.inr 2159, (1 / 1))]

def nodeValue2160 : Sparse Master := [(Sum.inr 2160, (1 / 1))]

def nodeValue2161 : Sparse Master := [(Sum.inr 2161, (1 / 1))]

def nodeValue2162 : Sparse Master := [(Sum.inr 2162, (1 / 1))]

def nodeValue2163 : Sparse Master := [(Sum.inr 2163, (1 / 1))]

def nodeValue2164 : Sparse Master := [(Sum.inr 2164, (1 / 1))]

def nodeValue2165 : Sparse Master := [(Sum.inr 2165, (1 / 1))]

def nodeValue2166 : Sparse Master := [(Sum.inr 2166, (1 / 1))]

def nodeValue2167 : Sparse Master := [(Sum.inr 2167, (1 / 1))]

def nodeValue2168 : Sparse Master := [(Sum.inr 2168, (1 / 1))]

def nodeValue2169 : Sparse Master := [(Sum.inr 2169, (1 / 1))]

def nodeValue2170 : Sparse Master := [(Sum.inr 2170, (1 / 1))]

def nodeValue2171 : Sparse Master := [(Sum.inr 2171, (1 / 1))]

def nodeValue2172 : Sparse Master := [(Sum.inr 2172, (1 / 1))]

def nodeValue2173 : Sparse Master := [(Sum.inr 2173, (1 / 1))]

def nodeValue2174 : Sparse Master := [(Sum.inr 2174, (1 / 1))]

def nodeValue2175 : Sparse Master := [(Sum.inr 2175, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2176 : Sparse Master := [(Sum.inr 2176, (1 / 1))]

def nodeValue2177 : Sparse Master := [(Sum.inr 2177, (1 / 1))]

def nodeValue2178 : Sparse Master := [(Sum.inr 2178, (1 / 1))]

def nodeValue2179 : Sparse Master := [(Sum.inr 2179, (1 / 1))]

def nodeValue2180 : Sparse Master := [(Sum.inr 2180, (1 / 1))]

def nodeValue2181 : Sparse Master := [(Sum.inr 2181, (1 / 1))]

def nodeValue2182 : Sparse Master := [(Sum.inr 2182, (1 / 1))]

def nodeValue2183 : Sparse Master := [(Sum.inr 2183, (1 / 1))]

def nodeValue2184 : Sparse Master := [(Sum.inr 2184, (1 / 1))]

def nodeValue2185 : Sparse Master := [(Sum.inr 2185, (1 / 1))]

def nodeValue2186 : Sparse Master := [(Sum.inr 2186, (1 / 1))]

def nodeValue2187 : Sparse Master := [(Sum.inr 2187, (1 / 1))]

def nodeValue2189 : Sparse Master := [(Sum.inr 2189, (1 / 1))]

def nodeValue2190 : Sparse Master := [(Sum.inr 2190, (1 / 1))]

def nodeValue2191 : Sparse Master := [(Sum.inr 2191, (1 / 1))]

def nodeValue2192 : Sparse Master := [(Sum.inr 2192, (1 / 1))]

def nodeValue2193 : Sparse Master := [(Sum.inr 2193, (1 / 1))]

def nodeValue2194 : Sparse Master := [(Sum.inr 2194, (1 / 1))]

def nodeValue2195 : Sparse Master := [(Sum.inr 2195, (1 / 1))]

def nodeValue2196 : Sparse Master := [(Sum.inr 2196, (1 / 1))]

def nodeValue2197 : Sparse Master := [(Sum.inr 2197, (1 / 1))]

def nodeValue2198 : Sparse Master := [(Sum.inr 2198, (1 / 1))]

def nodeValue2199 : Sparse Master := [(Sum.inr 2199, (1 / 1))]

def nodeValue2200 : Sparse Master := [(Sum.inr 2200, (1 / 1))]

def nodeValue2201 : Sparse Master := [(Sum.inr 2201, (1 / 1))]

def nodeValue2202 : Sparse Master := [(Sum.inr 2202, (1 / 1))]

def nodeValue2203 : Sparse Master := [(Sum.inr 2203, (1 / 1))]

def nodeValue2204 : Sparse Master := []

def nodeValue2205 : Sparse Master := []

def nodeValue2206 : Sparse Master := [(Sum.inr 2206, (1 / 1))]

def nodeValue2207 : Sparse Master := [(Sum.inr 2207, (1 / 1))]

def nodeValue2208 : Sparse Master := []

def nodeValue2211 : Sparse Master := [(Sum.inr 2211, (1 / 1))]

def nodeValue2212 : Sparse Master := [(Sum.inr 2212, (1 / 1))]

def nodeValue2213 : Sparse Master := [(Sum.inr 2213, (1 / 1))]

def nodeValue2214 : Sparse Master := [(Sum.inr 2214, (1 / 1))]

def nodeValue2215 : Sparse Master := [(Sum.inr 2215, (1 / 1))]

def nodeValue2216 : Sparse Master := [(Sum.inr 2216, (1 / 1))]

def nodeValue2217 : Sparse Master := [(Sum.inr 2217, (1 / 1))]

def nodeValue2218 : Sparse Master := [(Sum.inr 2218, (1 / 1))]

def nodeValue2219 : Sparse Master := [(Sum.inr 2219, (1 / 1))]

def nodeValue2220 : Sparse Master := [(Sum.inr 2220, (1 / 1))]

def nodeValue2221 : Sparse Master := [(Sum.inr 2221, (1 / 1))]

def nodeValue2222 : Sparse Master := [(Sum.inr 2222, (1 / 1))]

def nodeValue2223 : Sparse Master := [(Sum.inr 2223, (1 / 1))]

def nodeValue2224 : Sparse Master := [(Sum.inr 2224, (1 / 1))]

def nodeValue2225 : Sparse Master := [(Sum.inr 2225, (1 / 1))]

def nodeValue2226 : Sparse Master := [(Sum.inr 2226, (1 / 1))]

def nodeValue2227 : Sparse Master := []

def nodeValue2228 : Sparse Master := []

def nodeValue2229 : Sparse Master := []

def nodeValue2230 : Sparse Master := [(Sum.inr 2230, (1 / 1))]

def nodeValue2231 : Sparse Master := [(Sum.inr 2231, (1 / 1))]

def nodeValue2232 : Sparse Master := [(Sum.inr 2232, (1 / 1))]

def nodeValue2233 : Sparse Master := [(Sum.inr 2233, (1 / 1))]

def nodeValue2234 : Sparse Master := [(Sum.inr 2234, (1 / 1))]

def nodeValue2235 : Sparse Master := [(Sum.inr 2235, (1 / 1))]

def nodeValue2238 : Sparse Master := [(Sum.inr 2238, (1 / 1))]

def nodeValue2239 : Sparse Master := [(Sum.inr 2239, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2240 : Sparse Master := [(Sum.inr 2240, (1 / 1))]

def nodeValue2241 : Sparse Master := [(Sum.inr 2241, (1 / 1))]

def nodeValue2242 : Sparse Master := [(Sum.inr 2242, (1 / 1))]

def nodeValue2243 : Sparse Master := [(Sum.inr 2243, (1 / 1))]

def nodeValue2244 : Sparse Master := [(Sum.inr 2244, (1 / 1))]

def nodeValue2245 : Sparse Master := [(Sum.inr 2245, (1 / 1))]

def nodeValue2246 : Sparse Master := [(Sum.inr 2246, (1 / 1))]

def nodeValue2247 : Sparse Master := [(Sum.inr 2247, (1 / 1))]

def nodeValue2248 : Sparse Master := [(Sum.inr 2248, (1 / 1))]

def nodeValue2249 : Sparse Master := [(Sum.inr 2249, (1 / 1))]

def nodeValue2250 : Sparse Master := [(Sum.inr 2250, (1 / 1))]

def nodeValue2251 : Sparse Master := [(Sum.inr 2251, (1 / 1))]

def nodeValue2252 : Sparse Master := [(Sum.inr 2252, (1 / 1))]

def nodeValue2253 : Sparse Master := [(Sum.inr 2253, (1 / 1))]

def nodeValue2254 : Sparse Master := [(Sum.inr 2254, (1 / 1))]

def nodeValue2255 : Sparse Master := [(Sum.inr 2255, (1 / 1))]

def nodeValue2256 : Sparse Master := [(Sum.inr 2256, (1 / 1))]

def nodeValue2257 : Sparse Master := [(Sum.inr 2257, (1 / 1))]

def nodeValue2258 : Sparse Master := [(Sum.inr 2258, (1 / 1))]

def nodeValue2259 : Sparse Master := [(Sum.inr 2259, (1 / 1))]

def nodeValue2260 : Sparse Master := [(Sum.inr 2260, (1 / 1))]

def nodeValue2261 : Sparse Master := [(Sum.inr 2261, (1 / 1))]

def nodeValue2262 : Sparse Master := [(Sum.inr 2262, (1 / 1))]

def nodeValue2263 : Sparse Master := []

def nodeValue2264 : Sparse Master := []

def nodeValue2265 : Sparse Master := []

def nodeValue2266 : Sparse Master := [(Sum.inr 2266, (1 / 1))]

def nodeValue2267 : Sparse Master := [(Sum.inr 2267, (1 / 1))]

def nodeValue2268 : Sparse Master := []

def nodeValue2272 : Sparse Master := [(Sum.inr 2272, (1 / 1))]

def nodeValue2273 : Sparse Master := [(Sum.inr 2273, (1 / 1))]

def nodeValue2274 : Sparse Master := [(Sum.inr 2274, (1 / 1))]

def nodeValue2275 : Sparse Master := [(Sum.inr 2275, (1 / 1))]

def nodeValue2276 : Sparse Master := [(Sum.inr 2276, (1 / 1))]

def nodeValue2277 : Sparse Master := [(Sum.inr 2277, (1 / 1))]

def nodeValue2278 : Sparse Master := [(Sum.inr 2278, (1 / 1))]

def nodeValue2279 : Sparse Master := [(Sum.inr 2279, (1 / 1))]

def nodeValue2280 : Sparse Master := [(Sum.inr 2280, (1 / 1))]

def nodeValue2281 : Sparse Master := [(Sum.inr 2281, (1 / 1))]

def nodeValue2282 : Sparse Master := [(Sum.inr 2282, (1 / 1))]

def nodeValue2283 : Sparse Master := [(Sum.inr 2283, (1 / 1))]

def nodeValue2284 : Sparse Master := [(Sum.inr 2284, (1 / 1))]

def nodeValue2285 : Sparse Master := [(Sum.inr 2285, (1 / 1))]

def nodeValue2286 : Sparse Master := [(Sum.inr 2286, (1 / 1))]

def nodeValue2287 : Sparse Master := [(Sum.inr 2287, (1 / 1))]

def nodeValue2288 : Sparse Master := [(Sum.inr 2288, (1 / 1))]

def nodeValue2289 : Sparse Master := [(Sum.inr 2289, (1 / 1))]

def nodeValue2290 : Sparse Master := [(Sum.inr 2290, (1 / 1))]

def nodeValue2291 : Sparse Master := []

def nodeValue2292 : Sparse Master := []

def nodeValue2293 : Sparse Master := []

def nodeValue2294 : Sparse Master := [(Sum.inr 2294, (1 / 1))]

def nodeValue2295 : Sparse Master := [(Sum.inr 2295, (1 / 1))]

def nodeValue2300 : Sparse Master := [(Sum.inr 2300, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2306 : Sparse Master := [(Sum.inr 2306, (1 / 1))]

def nodeValue2316 : Sparse Master := [(Sum.inr 2316, (1 / 1))]

def nodeValue2317 : Sparse Master := [(Sum.inr 2317, (1 / 1))]

def nodeValue2318 : Sparse Master := [(Sum.inr 2318, (1 / 1))]

def nodeValue2319 : Sparse Master := []

def nodeValue2320 : Sparse Master := [(Sum.inr 2320, (1 / 1))]

def nodeValue2321 : Sparse Master := [(Sum.inr 2321, (1 / 1))]

def nodeValue2322 : Sparse Master := []

def nodeValue2323 : Sparse Master := [(Sum.inr 2323, (1 / 1))]

def nodeValue2324 : Sparse Master := [(Sum.inr 2324, (1 / 1))]

def nodeValue2325 : Sparse Master := [(Sum.inr 2325, (1 / 1))]

def nodeValue2326 : Sparse Master := [(Sum.inr 2326, (1 / 1))]

def nodeValue2327 : Sparse Master := [(Sum.inr 2327, (1 / 1))]

def nodeValue2328 : Sparse Master := [(Sum.inr 2328, (1 / 1))]

def nodeValue2329 : Sparse Master := [(Sum.inr 2329, (1 / 1))]

def nodeValue2330 : Sparse Master := [(Sum.inr 2330, (1 / 1))]

def nodeValue2331 : Sparse Master := []

def nodeValue2332 : Sparse Master := [(Sum.inr 2332, (1 / 1))]

def nodeValue2333 : Sparse Master := [(Sum.inr 2333, (1 / 1))]

def nodeValue2334 : Sparse Master := [(Sum.inr 2334, (1 / 1))]

def nodeValue2335 : Sparse Master := [(Sum.inr 2335, (1 / 1))]

def nodeValue2337 : Sparse Master := [(Sum.inr 2337, (1 / 1))]

def nodeValue2338 : Sparse Master := [(Sum.inr 2338, (1 / 1))]

def nodeValue2339 : Sparse Master := [(Sum.inr 2339, (1 / 1))]

def nodeValue2340 : Sparse Master := [(Sum.inr 2340, (1 / 1))]

def nodeValue2341 : Sparse Master := [(Sum.inr 2341, (1 / 1))]

def nodeValue2342 : Sparse Master := [(Sum.inr 2342, (1 / 1))]

def nodeValue2343 : Sparse Master := [(Sum.inr 2343, (1 / 1))]

def nodeValue2344 : Sparse Master := [(Sum.inr 2344, (1 / 1))]

def nodeValue2345 : Sparse Master := [(Sum.inr 2345, (1 / 1))]

def nodeValue2346 : Sparse Master := [(Sum.inr 2346, (1 / 1))]

def nodeValue2347 : Sparse Master := [(Sum.inr 2347, (1 / 1))]

def nodeValue2348 : Sparse Master := [(Sum.inr 2348, (1 / 1))]

def nodeValue2349 : Sparse Master := [(Sum.inr 2349, (1 / 1))]

def nodeValue2350 : Sparse Master := [(Sum.inr 2350, (1 / 1))]

def nodeValue2351 : Sparse Master := [(Sum.inr 2351, (1 / 1))]

def nodeValue2352 : Sparse Master := [(Sum.inr 2352, (1 / 1))]

def nodeValue2353 : Sparse Master := [(Sum.inr 2353, (1 / 1))]

def nodeValue2354 : Sparse Master := [(Sum.inr 2354, (1 / 1))]

def nodeValue2355 : Sparse Master := [(Sum.inr 2355, (1 / 1))]

def nodeValue2356 : Sparse Master := [(Sum.inr 2356, (1 / 1))]

def nodeValue2357 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 9, (-1 / 216)), (Sum.inl 6, (1 / 432)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (1 / 288)), (Sum.inl 69, (-1 / 54)), (Sum.inl 7, (-1 / 27)), (Sum.inl 124, (1 / 18)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-19 / 864))]

def nodeValue2358 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 9, (-1 / 216)), (Sum.inl 6, (1 / 432)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (-7 / 864)), (Sum.inl 69, (-1 / 54)), (Sum.inl 7, (-1 / 54)), (Sum.inl 126, (1 / 18)), (Sum.inl 3, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue2359 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 5, (-1 / 216)), (Sum.inl 68, (1 / 36)), (Sum.inl 2, (-1 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 124, (1 / 18)), (Sum.inl 125, (1 / 18)), (Sum.inl 3, (-1 / 54)), (Sum.inl 23, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-5 / 288))]

def nodeValue2361 : Sparse Master := [(Sum.inr 2361, (1 / 1))]

def nodeValue2362 : Sparse Master := [(Sum.inr 2362, (1 / 1))]

def nodeValue2363 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (1 / 144)), (Sum.inl 125, (-1 / 9)), (Sum.inl 1, (-1 / 48))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2370 : Sparse Master := [(Sum.inr 2370, (1 / 1))]

def nodeValue2371 : Sparse Master := [(Sum.inr 2371, (1 / 1))]

def nodeValue2372 : Sparse Master := [(Sum.inr 2372, (1 / 1))]

def nodeValue2377 : Sparse Master := []

def nodeValue2378 : Sparse Master := [(Sum.inr 2378, (1 / 1))]

def nodeValue2379 : Sparse Master := [(Sum.inr 2379, (1 / 1))]

def nodeValue2382 : Sparse Master := [(Sum.inr 2382, (1 / 1))]

def nodeValue2383 : Sparse Master := [(Sum.inr 2383, (1 / 1))]

def nodeValue2384 : Sparse Master := [(Sum.inr 2384, (1 / 1))]

def nodeValue2385 : Sparse Master := [(Sum.inr 2385, (1 / 1))]

def nodeValue2388 : Sparse Master := [(Sum.inr 2388, (1 / 1))]

def nodeValue2389 : Sparse Master := [(Sum.inr 2389, (1 / 1))]

def nodeValue2390 : Sparse Master := [(Sum.inr 2390, (1 / 1))]

def nodeValue2391 : Sparse Master := [(Sum.inr 2391, (1 / 1))]

def nodeValue2392 : Sparse Master := [(Sum.inr 2392, (1 / 1))]

def nodeValue2393 : Sparse Master := [(Sum.inr 2393, (1 / 1))]

def nodeValue2394 : Sparse Master := [(Sum.inr 2394, (1 / 1))]

def nodeValue2395 : Sparse Master := [(Sum.inr 2395, (1 / 1))]

def nodeValue2396 : Sparse Master := [(Sum.inr 2396, (1 / 1))]

def nodeValue2397 : Sparse Master := [(Sum.inr 2397, (1 / 1))]

def nodeValue2398 : Sparse Master := [(Sum.inr 2398, (1 / 1))]

def nodeValue2399 : Sparse Master := [(Sum.inr 2399, (1 / 1))]

def nodeValue2400 : Sparse Master := [(Sum.inr 2400, (1 / 1))]

def nodeValue2401 : Sparse Master := [(Sum.inr 2401, (1 / 1))]

def nodeValue2402 : Sparse Master := []

def nodeValue2403 : Sparse Master := []

def nodeValue2404 : Sparse Master := [(Sum.inr 2404, (1 / 1))]

def nodeValue2405 : Sparse Master := [(Sum.inr 2405, (1 / 1))]

def nodeValue2407 : Sparse Master := [(Sum.inr 2407, (1 / 1))]

def nodeValue2408 : Sparse Master := [(Sum.inr 2408, (1 / 1))]

def nodeValue2409 : Sparse Master := [(Sum.inr 2409, (1 / 1))]

def nodeValue2410 : Sparse Master := [(Sum.inr 2410, (1 / 1))]

def nodeValue2411 : Sparse Master := []

def nodeValue2412 : Sparse Master := [(Sum.inr 2412, (1 / 1))]

def nodeValue2419 : Sparse Master := [(Sum.inr 2419, (1 / 1))]

def nodeValue2422 : Sparse Master := [(Sum.inr 2422, (1 / 1))]

def nodeValue2423 : Sparse Master := [(Sum.inr 2423, (1 / 1))]

def nodeValue2424 : Sparse Master := [(Sum.inr 2424, (1 / 1))]

def nodeValue2425 : Sparse Master := [(Sum.inr 2425, (1 / 1))]

def nodeValue2426 : Sparse Master := [(Sum.inr 2426, (1 / 1))]

def nodeValue2427 : Sparse Master := [(Sum.inr 2427, (1 / 1))]

def nodeValue2428 : Sparse Master := [(Sum.inr 2428, (1 / 1))]

def nodeValue2429 : Sparse Master := [(Sum.inr 2429, (1 / 1))]

def nodeValue2430 : Sparse Master := [(Sum.inr 2430, (1 / 1))]

def nodeValue2431 : Sparse Master := [(Sum.inr 2431, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2432 : Sparse Master := [(Sum.inr 2432, (1 / 1))]

def nodeValue2433 : Sparse Master := [(Sum.inr 2433, (1 / 1))]

def nodeValue2434 : Sparse Master := [(Sum.inr 2434, (1 / 1))]

def nodeValue2435 : Sparse Master := [(Sum.inr 2435, (1 / 1))]

def nodeValue2436 : Sparse Master := [(Sum.inr 2436, (1 / 1))]

def nodeValue2437 : Sparse Master := [(Sum.inr 2437, (1 / 1))]

def nodeValue2438 : Sparse Master := [(Sum.inr 2438, (1 / 1))]

def nodeValue2440 : Sparse Master := [(Sum.inr 2440, (1 / 1))]

def nodeValue2441 : Sparse Master := [(Sum.inr 2441, (1 / 1))]

def nodeValue2442 : Sparse Master := [(Sum.inr 2442, (1 / 1))]

def nodeValue2443 : Sparse Master := [(Sum.inr 2443, (1 / 1))]

def nodeValue2449 : Sparse Master := [(Sum.inr 2449, (1 / 1))]

def nodeValue2452 : Sparse Master := [(Sum.inr 2452, (1 / 1))]

def nodeValue2453 : Sparse Master := [(Sum.inr 2453, (1 / 1))]

def nodeValue2454 : Sparse Master := [(Sum.inr 2454, (1 / 1))]

def nodeValue2455 : Sparse Master := [(Sum.inr 2455, (1 / 1))]

def nodeValue2456 : Sparse Master := [(Sum.inr 2456, (1 / 1))]

def nodeValue2457 : Sparse Master := [(Sum.inr 2457, (1 / 1))]

def nodeValue2458 : Sparse Master := [(Sum.inr 2458, (1 / 1))]

def nodeValue2459 : Sparse Master := [(Sum.inr 2459, (1 / 1))]

def nodeValue2460 : Sparse Master := [(Sum.inr 2460, (1 / 1))]

def nodeValue2461 : Sparse Master := []

def nodeValue2462 : Sparse Master := [(Sum.inr 2462, (1 / 1))]

def nodeValue2463 : Sparse Master := [(Sum.inr 2463, (1 / 1))]

def nodeValue2465 : Sparse Master := [(Sum.inr 2465, (1 / 1))]

def nodeValue2466 : Sparse Master := [(Sum.inr 2466, (1 / 1))]

def nodeValue2467 : Sparse Master := [(Sum.inr 2467, (1 / 1))]

def nodeValue2468 : Sparse Master := []

def nodeValue2469 : Sparse Master := [(Sum.inr 2469, (1 / 1))]

def nodeValue2470 : Sparse Master := [(Sum.inr 2470, (1 / 1))]

def nodeValue2471 : Sparse Master := [(Sum.inr 2471, (1 / 1))]

def nodeValue2472 : Sparse Master := [(Sum.inr 2472, (1 / 1))]

def nodeValue2473 : Sparse Master := [(Sum.inr 2473, (1 / 1))]

def nodeValue2474 : Sparse Master := [(Sum.inr 2474, (1 / 1))]

def nodeValue2475 : Sparse Master := [(Sum.inr 2475, (1 / 1))]

def nodeValue2476 : Sparse Master := [(Sum.inr 2476, (1 / 1))]

def nodeValue2477 : Sparse Master := [(Sum.inr 2477, (1 / 1))]

def nodeValue2478 : Sparse Master := [(Sum.inr 2478, (1 / 1))]

def nodeValue2479 : Sparse Master := [(Sum.inr 2479, (1 / 1))]

def nodeValue2480 : Sparse Master := [(Sum.inr 2480, (1 / 1))]

def nodeValue2481 : Sparse Master := [(Sum.inr 2481, (1 / 1))]

def nodeValue2482 : Sparse Master := [(Sum.inr 2482, (1 / 1))]

def nodeValue2483 : Sparse Master := [(Sum.inr 2483, (1 / 1))]

def nodeValue2484 : Sparse Master := [(Sum.inr 2484, (1 / 1))]

def nodeValue2485 : Sparse Master := [(Sum.inr 2485, (1 / 1))]

def nodeValue2486 : Sparse Master := [(Sum.inr 2486, (1 / 1))]

def nodeValue2488 : Sparse Master := [(Sum.inr 2488, (1 / 1))]

def nodeValue2489 : Sparse Master := [(Sum.inr 2489, (1 / 1))]

def nodeValue2490 : Sparse Master := [(Sum.inr 2490, (1 / 1))]

def nodeValue2491 : Sparse Master := [(Sum.inr 2491, (1 / 1))]

def nodeValue2492 : Sparse Master := [(Sum.inr 2492, (1 / 1))]

def nodeValue2493 : Sparse Master := [(Sum.inr 2493, (1 / 1))]

def nodeValue2494 : Sparse Master := [(Sum.inr 2494, (1 / 1))]

def nodeValue2495 : Sparse Master := [(Sum.inr 2495, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2496 : Sparse Master := [(Sum.inr 2496, (1 / 1))]

def nodeValue2497 : Sparse Master := [(Sum.inr 2497, (1 / 1))]

def nodeValue2498 : Sparse Master := [(Sum.inr 2498, (1 / 1))]

def nodeValue2499 : Sparse Master := [(Sum.inr 2499, (1 / 1))]

def nodeValue2500 : Sparse Master := [(Sum.inr 2500, (1 / 1))]

def nodeValue2501 : Sparse Master := [(Sum.inr 2501, (1 / 1))]

def nodeValue2502 : Sparse Master := [(Sum.inr 2502, (1 / 1))]

def nodeValue2503 : Sparse Master := [(Sum.inr 2503, (1 / 1))]

def nodeValue2504 : Sparse Master := [(Sum.inr 2504, (1 / 1))]

def nodeValue2505 : Sparse Master := [(Sum.inr 2505, (1 / 1))]

def nodeValue2506 : Sparse Master := [(Sum.inr 2506, (1 / 1))]

def nodeValue2507 : Sparse Master := [(Sum.inr 2507, (1 / 1))]

def nodeValue2508 : Sparse Master := [(Sum.inr 2508, (1 / 1))]

def nodeValue2509 : Sparse Master := [(Sum.inr 2509, (1 / 1))]

def nodeValue2510 : Sparse Master := []

def nodeValue2511 : Sparse Master := []

def nodeValue2512 : Sparse Master := [(Sum.inr 2512, (1 / 1))]

def nodeValue2513 : Sparse Master := [(Sum.inr 2513, (1 / 1))]

def nodeValue2514 : Sparse Master := []

def nodeValue2515 : Sparse Master := [(Sum.inr 2515, (1 / 1))]

def nodeValue2516 : Sparse Master := [(Sum.inr 2516, (1 / 1))]

def nodeValue2517 : Sparse Master := []

def nodeValue2519 : Sparse Master := [(Sum.inr 2519, (1 / 1))]

def nodeValue2520 : Sparse Master := [(Sum.inr 2520, (1 / 1))]

def nodeValue2521 : Sparse Master := [(Sum.inr 2521, (1 / 1))]

def nodeValue2522 : Sparse Master := [(Sum.inr 2522, (1 / 1))]

def nodeValue2523 : Sparse Master := []

def nodeValue2524 : Sparse Master := [(Sum.inr 2524, (1 / 1))]

def nodeValue2525 : Sparse Master := [(Sum.inr 2525, (1 / 1))]

def nodeValue2526 : Sparse Master := [(Sum.inl 0, (-7 / 1440)), (Sum.inl 9, (1 / 216)), (Sum.inl 58, (-1 / 864)), (Sum.inl 6, (7 / 864)), (Sum.inl 68, (-1 / 72)), (Sum.inl 2, (1 / 108)), (Sum.inl 69, (1 / 54)), (Sum.inl 71, (1 / 54)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 27)), (Sum.inl 126, (-1 / 18)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (-1 / 288))]

def nodeValue2527 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (-1 / 216)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (1 / 288)), (Sum.inl 69, (1 / 54)), (Sum.inl 70, (1 / 54)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 27)), (Sum.inl 124, (-1 / 18)), (Sum.inl 125, (-1 / 18)), (Sum.inl 3, (1 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 23, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-7 / 288))]

def nodeValue2528 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 9, (1 / 216)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (5 / 432)), (Sum.inl 68, (-1 / 72)), (Sum.inl 69, (1 / 54)), (Sum.inl 70, (1 / 54)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (2 / 27)), (Sum.inl 125, (-1 / 18)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 52, (2 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue2529 : Sparse Master := [(Sum.inr 2529, (1 / 1))]

def nodeValue2530 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (-1 / 36)), (Sum.inl 6, (-1 / 216)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (29 / 864)), (Sum.inl 69, (1 / 54)), (Sum.inl 71, (1 / 54)), (Sum.inl 7, (2 / 27)), (Sum.inl 8, (2 / 27)), (Sum.inl 124, (-1 / 18)), (Sum.inl 126, (-1 / 18)), (Sum.inl 51, (-1 / 9)), (Sum.inl 3, (1 / 18))]

def nodeValue2531 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 9, (-1 / 216)), (Sum.inl 6, (1 / 432)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (-1 / 216)), (Sum.inl 71, (-1 / 54)), (Sum.inl 8, (-1 / 27)), (Sum.inl 126, (1 / 18)), (Sum.inl 1, (-7 / 864))]

def nodeValue2532 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 9, (-1 / 216)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (1 / 432)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (-1 / 216)), (Sum.inl 70, (-1 / 54)), (Sum.inl 7, (-1 / 27)), (Sum.inl 35, (-1 / 27)), (Sum.inl 125, (1 / 18)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 1, (-1 / 36))]

def nodeValue2533 : Sparse Master := [(Sum.inr 2533, (1 / 1))]

def nodeValue2534 : Sparse Master := [(Sum.inr 2534, (1 / 1))]

def nodeValue2535 : Sparse Master := [(Sum.inr 2535, (1 / 1))]

def nodeValue2536 : Sparse Master := [(Sum.inr 2536, (1 / 1))]

def nodeValue2537 : Sparse Master := [(Sum.inr 2537, (1 / 1))]

def nodeValue2538 : Sparse Master := [(Sum.inr 2538, (1 / 1))]

def nodeValue2539 : Sparse Master := [(Sum.inr 2539, (1 / 1))]

def nodeValue2540 : Sparse Master := []

def nodeValue2541 : Sparse Master := [(Sum.inr 2541, (1 / 1))]

def nodeValue2542 : Sparse Master := []

def nodeValue2543 : Sparse Master := [(Sum.inr 2543, (1 / 1))]

def nodeValue2544 : Sparse Master := [(Sum.inr 2544, (1 / 1))]

def nodeValue2545 : Sparse Master := [(Sum.inr 2545, (1 / 1))]

def nodeValue2546 : Sparse Master := []

def nodeValue2547 : Sparse Master := [(Sum.inr 2547, (1 / 1))]

def nodeValue2549 : Sparse Master := [(Sum.inr 2549, (1 / 1))]

def nodeValue2550 : Sparse Master := [(Sum.inr 2550, (1 / 1))]

def nodeValue2551 : Sparse Master := [(Sum.inr 2551, (1 / 1))]

def nodeValue2552 : Sparse Master := []

def nodeValue2553 : Sparse Master := [(Sum.inr 2553, (1 / 1))]

def nodeValue2554 : Sparse Master := []

def nodeValue2555 : Sparse Master := [(Sum.inr 2555, (1 / 1))]

def nodeValue2556 : Sparse Master := [(Sum.inr 2556, (1 / 1))]

def nodeValue2557 : Sparse Master := [(Sum.inr 2557, (1 / 1))]

def nodeValue2558 : Sparse Master := [(Sum.inr 2558, (1 / 1))]

def nodeValue2559 : Sparse Master := [(Sum.inr 2559, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue256 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (-5 / 108)), (Sum.inl 61, (5 / 9)), (Sum.inl 2, (-5 / 108)), (Sum.inl 1, (-5 / 108))]

def nodeValue257 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 32, (-5 / 27)), (Sum.inl 2, (-5 / 72)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-85 / 54)), (Sum.inl 12, (-5 / 9)), (Sum.inl 1, (5 / 96))]

def nodeValue258 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 32, (5 / 27)), (Sum.inl 2, (25 / 144)), (Sum.inl 13, (5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue259 : Sparse Master := [(Sum.inl 0, (13 / 432)), (Sum.inl 2, (5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (115 / 432))]

def nodeValue260 : Sparse Master := [(Sum.inl 0, (11 / 288)), (Sum.inl 2, (-5 / 216)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 1, (-5 / 864))]

def nodeValue261 : Sparse Master := [(Sum.inl 0, (13 / 432)), (Sum.inl 2, (5 / 864)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-25 / 864))]

def nodeValue262 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 2, (25 / 144)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue263 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 32, (5 / 54)), (Sum.inl 2, (-5 / 108)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 9)), (Sum.inl 12, (5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue264 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 32, (-5 / 27)), (Sum.inl 2, (5 / 72)), (Sum.inl 13, (-10 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue265 : Sparse Master := []

def nodeValue266 : Sparse Master := []

def nodeValue267 : Sparse Master := []

def nodeValue268 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 2, (-5 / 54)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (-55 / 432))]

def nodeValue269 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 2, (-5 / 72)), (Sum.inl 13, (-10 / 27)), (Sum.inl 12, (-5 / 27)), (Sum.inl 1, (5 / 72))]

def nodeValue270 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 2, (5 / 48)), (Sum.inl 13, (5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue271 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 32, (5 / 9)), (Sum.inl 2, (5 / 12))]

def nodeValue272 : Sparse Master := []

def nodeValue273 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 9, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 216)), (Sum.inl 71, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (-25 / 864)), (Sum.inl 236, (-5 / 18))]

def nodeValue274 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 9, (5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 216)), (Sum.inl 71, (5 / 54)), (Sum.inl 8, (5 / 27)), (Sum.inl 126, (-5 / 18)), (Sum.inl 1, (35 / 864))]

def nodeValue275 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 126, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 197, (-5 / 18)), (Sum.inl 24, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-25 / 288))]

def nodeValue277 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 126, (5 / 9)), (Sum.inl 1, (-25 / 432))]

def nodeValue278 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 266, (5 / 18)), (Sum.inl 64, (5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 864)), (Sum.inl 7, (-5 / 27)), (Sum.inl 124, (5 / 9)), (Sum.inl 125, (5 / 6)), (Sum.inl 126, (5 / 9)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-5 / 27)), (Sum.inl 196, (5 / 18)), (Sum.inl 197, (5 / 18)), (Sum.inl 23, (5 / 9)), (Sum.inl 54, (5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 27, (-5 / 36)), (Sum.inl 1, (-5 / 432))]

def nodeValue279 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 216)), (Sum.inl 125, (-5 / 9)), (Sum.inl 126, (-5 / 9)), (Sum.inl 1, (-5 / 108))]

def nodeValue280 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 36)), (Sum.inl 6, (5 / 288)), (Sum.inl 259, (5 / 18)), (Sum.inl 266, (5 / 18)), (Sum.inl 64, (5 / 18)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (5 / 72)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 487, (-5 / 9)), (Sum.inl 123, (5 / 18)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (5 / 144))]

def nodeValue281 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (5 / 216)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 259, (-5 / 18)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (5 / 288)), (Sum.inl 123, (-5 / 18)), (Sum.inl 124, (-5 / 18)), (Sum.inl 51, (-5 / 18)), (Sum.inl 1, (-55 / 864))]

def nodeValue282 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 487, (5 / 9)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-25 / 432))]

def nodeValue283 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 216)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 68, (25 / 72)), (Sum.inl 2, (-25 / 432)), (Sum.inl 69, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 126, (10 / 9)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-5 / 18)), (Sum.inl 52, (-5 / 54)), (Sum.inl 24, (5 / 9)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (55 / 864))]

def nodeValue284 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 288)), (Sum.inl 69, (5 / 54)), (Sum.inl 7, (5 / 27)), (Sum.inl 124, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (95 / 864))]

def nodeValue285 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 9, (5 / 216)), (Sum.inl 6, (-5 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (35 / 864)), (Sum.inl 69, (5 / 54)), (Sum.inl 7, (5 / 54)), (Sum.inl 126, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (-25 / 432))]

def nodeValue286 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 124, (-5 / 18)), (Sum.inl 125, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 23, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (25 / 288))]

def nodeValue287 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 432)), (Sum.inl 8, (5 / 54)), (Sum.inl 126, (-5 / 9)), (Sum.inl 24, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 432))]

def nodeValue288 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 266, (-5 / 18)), (Sum.inl 64, (-5 / 18)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 125, (-5 / 18)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue289 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (5 / 216)), (Sum.inl 68, (-5 / 36)), (Sum.inl 2, (5 / 864)), (Sum.inl 124, (-5 / 18)), (Sum.inl 126, (-5 / 18)), (Sum.inl 51, (-5 / 18)), (Sum.inl 1, (-35 / 432))]

def nodeValue290 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 124, (5 / 9)), (Sum.inl 1, (25 / 216))]

def nodeValue291 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 9, (-5 / 216)), (Sum.inl 58, (5 / 864)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 108)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (5 / 216)), (Sum.inl 71, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 108)), (Sum.inl 236, (5 / 18))]

def nodeValue292 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 9, (-5 / 108)), (Sum.inl 58, (5 / 864)), (Sum.inl 6, (-25 / 864)), (Sum.inl 262, (5 / 18)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (-65 / 864)), (Sum.inl 69, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 126, (5 / 18)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 128, (-5 / 54)), (Sum.inl 495, (-5 / 54)), (Sum.inl 52, (-10 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue293 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (5 / 288)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-25 / 432)), (Sum.inl 69, (-5 / 54)), (Sum.inl 71, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 8, (-5 / 27)), (Sum.inl 126, (5 / 18)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 1, (-55 / 864)), (Sum.inl 236, (5 / 18))]

def nodeValue294 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 9, (-5 / 216)), (Sum.inl 58, (5 / 864)), (Sum.inl 6, (-35 / 864)), (Sum.inl 68, (5 / 72)), (Sum.inl 2, (-5 / 108)), (Sum.inl 69, (-5 / 54)), (Sum.inl 71, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 8, (-5 / 27)), (Sum.inl 126, (5 / 18)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue295 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (5 / 288)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-5 / 18)), (Sum.inl 126, (5 / 18)), (Sum.inl 3, (-25 / 54)), (Sum.inl 52, (-5 / 54)), (Sum.inl 197, (5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 216))]

def nodeValue296 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (5 / 216)), (Sum.inl 256, (5 / 18)), (Sum.inl 59, (5 / 18)), (Sum.inl 33, (5 / 18)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-25 / 288)), (Sum.inl 81, (5 / 18)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 8, (-5 / 54)), (Sum.inl 486, (-5 / 9)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 52, (-5 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 216))]

def nodeValue297 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 9, (-5 / 108)), (Sum.inl 6, (5 / 216)), (Sum.inl 259, (5 / 18)), (Sum.inl 260, (5 / 18)), (Sum.inl 64, (5 / 9)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 144)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-5 / 54)), (Sum.inl 123, (5 / 18)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-25 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 52, (-5 / 54)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 9)), (Sum.inl 12, (-5 / 54)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 432))]

def nodeValue298 : Sparse Master := [(Sum.inl 0, (5 / 288)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 216)), (Sum.inl 259, (5 / 18)), (Sum.inl 59, (5 / 18)), (Sum.inl 262, (5 / 18)), (Sum.inl 33, (5 / 18)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-35 / 864)), (Sum.inl 123, (5 / 18)), (Sum.inl 124, (5 / 18)), (Sum.inl 126, (5 / 18)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 52, (-5 / 54)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (5 / 432)), (Sum.inl 31, (5 / 18))]

def nodeValue299 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 5, (5 / 27)), (Sum.inl 6, (-5 / 216)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 128, (-5 / 54)), (Sum.inl 52, (-10 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (5 / 48))]

def nodeValue300 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 54)), (Sum.inl 59, (5 / 18)), (Sum.inl 33, (5 / 18)), (Sum.inl 2, (-65 / 432)), (Sum.inl 7, (-10 / 27)), (Sum.inl 35, (-5 / 54)), (Sum.inl 8, (-10 / 27)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-5 / 9)), (Sum.inl 13, (-5 / 54)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 54)), (Sum.inl 1, (65 / 864))]

def nodeValue301 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (25 / 216)), (Sum.inl 6, (-5 / 216)), (Sum.inl 2, (5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 864))]

def nodeValue302 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 36)), (Sum.inl 6, (-5 / 288)), (Sum.inl 2, (-35 / 432)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 1, (5 / 48))]

def nodeValue303 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 216)), (Sum.inl 2, (-5 / 144)), (Sum.inl 1, (-5 / 216))]

def nodeValue304 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-5 / 96)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 18)), (Sum.inl 52, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (5 / 144))]

def nodeValue305 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (-5 / 288)), (Sum.inl 3, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue306 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (-5 / 72)), (Sum.inl 2, (55 / 864)), (Sum.inl 7, (5 / 27)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 72))]

def nodeValue307 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (-5 / 54)), (Sum.inl 2, (5 / 72)), (Sum.inl 8, (5 / 27)), (Sum.inl 1, (25 / 216))]

def nodeValue308 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 216)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (10 / 27)), (Sum.inl 128, (5 / 54)), (Sum.inl 52, (5 / 27)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 432))]

def nodeValue309 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 59, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (5 / 108)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue310 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (-25 / 288))]

def nodeValue311 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (-65 / 864)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (-55 / 864))]

def nodeValue312 : Sparse Master := [(Sum.inl 0, (11 / 288)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (35 / 432)), (Sum.inl 3, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue313 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 60, (5 / 54)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (-5 / 432)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 108))]

def nodeValue314 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 144)), (Sum.inl 35, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-5 / 96))]

def nodeValue315 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 144)), (Sum.inl 3, (-5 / 27)), (Sum.inl 52, (-5 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue316 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (-5 / 432)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 108))]

def nodeValue317 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (5 / 216)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-5 / 288)), (Sum.inl 69, (-5 / 54)), (Sum.inl 70, (-5 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 3, (-5 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 23, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (35 / 288))]

def nodeValue318 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 9, (-5 / 108)), (Sum.inl 5, (5 / 36)), (Sum.inl 6, (5 / 216)), (Sum.inl 68, (5 / 36)), (Sum.inl 2, (-145 / 864)), (Sum.inl 69, (-5 / 54)), (Sum.inl 71, (-5 / 54)), (Sum.inl 7, (-10 / 27)), (Sum.inl 8, (-10 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 126, (5 / 18)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-5 / 18))]

def nodeValue319 : Sparse Master := [(Sum.inl 0, (1 / 72)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 52, (-10 / 27)), (Sum.inl 1, (35 / 432))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2560 : Sparse Master := [(Sum.inr 2560, (1 / 1))]

def nodeValue2561 : Sparse Master := [(Sum.inr 2561, (1 / 1))]

def nodeValue2562 : Sparse Master := [(Sum.inr 2562, (1 / 1))]

def nodeValue2564 : Sparse Master := [(Sum.inr 2564, (1 / 1))]

def nodeValue2565 : Sparse Master := [(Sum.inr 2565, (1 / 1))]

def nodeValue2566 : Sparse Master := [(Sum.inr 2566, (1 / 1))]

def nodeValue2567 : Sparse Master := [(Sum.inr 2567, (1 / 1))]

def nodeValue2568 : Sparse Master := [(Sum.inr 2568, (1 / 1))]

def nodeValue2569 : Sparse Master := [(Sum.inr 2569, (1 / 1))]

def nodeValue2570 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (13 / 864)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (1 / 27)), (Sum.inl 52, (1 / 54)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-7 / 432))]

def nodeValue2571 : Sparse Master := [(Sum.inr 2571, (1 / 1))]

def nodeValue2572 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (1 / 288)), (Sum.inl 3, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue2573 : Sparse Master := [(Sum.inr 2573, (1 / 1))]

def nodeValue2574 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (-1 / 864)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 13, (-1 / 27)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (-7 / 864))]

def nodeValue2575 : Sparse Master := [(Sum.inr 2575, (1 / 1))]

def nodeValue2576 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (-1 / 108)), (Sum.inl 7, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 51, (1 / 18)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-5 / 864))]

def nodeValue2577 : Sparse Master := [(Sum.inr 2577, (1 / 1))]

def nodeValue2578 : Sparse Master := [(Sum.inr 2578, (1 / 1))]

def nodeValue2579 : Sparse Master := [(Sum.inr 2579, (1 / 1))]

def nodeValue2580 : Sparse Master := [(Sum.inr 2580, (1 / 1))]

def nodeValue2582 : Sparse Master := [(Sum.inr 2582, (1 / 1))]

def nodeValue2583 : Sparse Master := [(Sum.inr 2583, (1 / 1))]

def nodeValue2584 : Sparse Master := [(Sum.inr 2584, (1 / 1))]

def nodeValue2585 : Sparse Master := [(Sum.inr 2585, (1 / 1))]

def nodeValue2587 : Sparse Master := [(Sum.inr 2587, (1 / 1))]

def nodeValue2588 : Sparse Master := [(Sum.inr 2588, (1 / 1))]

def nodeValue2589 : Sparse Master := [(Sum.inr 2589, (1 / 1))]

def nodeValue2590 : Sparse Master := [(Sum.inr 2590, (1 / 1))]

def nodeValue2591 : Sparse Master := [(Sum.inr 2591, (1 / 1))]

def nodeValue2592 : Sparse Master := [(Sum.inr 2592, (1 / 1))]

def nodeValue2593 : Sparse Master := [(Sum.inl 0, (-49 / 4320)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (11 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue2594 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-19 / 432))]

def nodeValue2595 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 144)), (Sum.inl 8, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue2596 : Sparse Master := [(Sum.inl 0, (-1 / 270)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (-13 / 432))]

def nodeValue2597 : Sparse Master := [(Sum.inr 2597, (1 / 1))]

def nodeValue2598 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 1, (-5 / 108))]

def nodeValue2599 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-5 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue2600 : Sparse Master := [(Sum.inr 2600, (1 / 1))]

def nodeValue2601 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 72)), (Sum.inl 1, (5 / 216))]

def nodeValue2602 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 6, (-1 / 432)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 13, (1 / 27)), (Sum.inl 1, (-1 / 27))]

def nodeValue2603 : Sparse Master := [(Sum.inr 2603, (1 / 1))]

def nodeValue2604 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 432)), (Sum.inl 7, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-7 / 216))]

def nodeValue2605 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 5, (1 / 108)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 108))]

def nodeValue2606 : Sparse Master := [(Sum.inr 2606, (1 / 1))]

def nodeValue2607 : Sparse Master := [(Sum.inr 2607, (1 / 1))]

def nodeValue2608 : Sparse Master := [(Sum.inr 2608, (1 / 1))]

def nodeValue2609 : Sparse Master := [(Sum.inr 2609, (1 / 1))]

def nodeValue2610 : Sparse Master := [(Sum.inr 2610, (1 / 1))]

def nodeValue2611 : Sparse Master := [(Sum.inr 2611, (1 / 1))]

def nodeValue2612 : Sparse Master := [(Sum.inr 2612, (1 / 1))]

def nodeValue2613 : Sparse Master := [(Sum.inr 2613, (1 / 1))]

def nodeValue2614 : Sparse Master := [(Sum.inr 2614, (1 / 1))]

def nodeValue2615 : Sparse Master := [(Sum.inr 2615, (1 / 1))]

def nodeValue2616 : Sparse Master := [(Sum.inr 2616, (1 / 1))]

def nodeValue2617 : Sparse Master := [(Sum.inr 2617, (1 / 1))]

def nodeValue2618 : Sparse Master := [(Sum.inr 2618, (1 / 1))]

def nodeValue2619 : Sparse Master := [(Sum.inr 2619, (1 / 1))]

def nodeValue2620 : Sparse Master := [(Sum.inr 2620, (1 / 1))]

def nodeValue2621 : Sparse Master := [(Sum.inr 2621, (1 / 1))]

def nodeValue2622 : Sparse Master := [(Sum.inr 2622, (1 / 1))]

def nodeValue2623 : Sparse Master := [(Sum.inr 2623, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2624 : Sparse Master := [(Sum.inr 2624, (1 / 1))]

def nodeValue2625 : Sparse Master := [(Sum.inr 2625, (1 / 1))]

def nodeValue2627 : Sparse Master := [(Sum.inr 2627, (1 / 1))]

def nodeValue2628 : Sparse Master := [(Sum.inr 2628, (1 / 1))]

def nodeValue2629 : Sparse Master := [(Sum.inr 2629, (1 / 1))]

def nodeValue2630 : Sparse Master := [(Sum.inr 2630, (1 / 1))]

def nodeValue2631 : Sparse Master := [(Sum.inr 2631, (1 / 1))]

def nodeValue2632 : Sparse Master := [(Sum.inr 2632, (1 / 1))]

def nodeValue2633 : Sparse Master := [(Sum.inr 2633, (1 / 1))]

def nodeValue2634 : Sparse Master := [(Sum.inr 2634, (1 / 1))]

def nodeValue2635 : Sparse Master := [(Sum.inr 2635, (1 / 1))]

def nodeValue2636 : Sparse Master := [(Sum.inl 0, (-5 / 864)), (Sum.inl 5, (1 / 72)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (5 / 144)), (Sum.inl 51, (-1 / 6)), (Sum.inl 3, (1 / 6)), (Sum.inl 13, (1 / 27)), (Sum.inl 52, (1 / 18)), (Sum.inl 12, (1 / 18)), (Sum.inl 4, (1 / 18)), (Sum.inl 1, (-1 / 144))]

def nodeValue2637 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-5 / 864)), (Sum.inl 51, (1 / 18)), (Sum.inl 3, (-1 / 27)), (Sum.inl 52, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue2638 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 108)), (Sum.inl 51, (1 / 18)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue2639 : Sparse Master := [(Sum.inr 2639, (1 / 1))]

def nodeValue2640 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (1 / 72))]

def nodeValue2641 : Sparse Master := [(Sum.inr 2641, (1 / 1))]

def nodeValue2642 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (7 / 432)), (Sum.inl 13, (1 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue2643 : Sparse Master := [(Sum.inr 2643, (1 / 1))]

def nodeValue2644 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 144)), (Sum.inl 51, (-1 / 9)), (Sum.inl 1, (1 / 144))]

def nodeValue2645 : Sparse Master := [(Sum.inr 2645, (1 / 1))]

def nodeValue2647 : Sparse Master := [(Sum.inr 2647, (1 / 1))]

def nodeValue2649 : Sparse Master := [(Sum.inr 2649, (1 / 1))]

def nodeValue2650 : Sparse Master := [(Sum.inr 2650, (1 / 1))]

def nodeValue2651 : Sparse Master := [(Sum.inr 2651, (1 / 1))]

def nodeValue2652 : Sparse Master := [(Sum.inr 2652, (1 / 1))]

def nodeValue2653 : Sparse Master := [(Sum.inr 2653, (1 / 1))]

def nodeValue2654 : Sparse Master := [(Sum.inr 2654, (1 / 1))]

def nodeValue2655 : Sparse Master := [(Sum.inr 2655, (1 / 1))]

def nodeValue2656 : Sparse Master := [(Sum.inr 2656, (1 / 1))]

def nodeValue2657 : Sparse Master := [(Sum.inr 2657, (1 / 1))]

def nodeValue2658 : Sparse Master := [(Sum.inr 2658, (1 / 1))]

def nodeValue2659 : Sparse Master := [(Sum.inr 2659, (1 / 1))]

def nodeValue2661 : Sparse Master := [(Sum.inr 2661, (1 / 1))]

def nodeValue2662 : Sparse Master := [(Sum.inr 2662, (1 / 1))]

def nodeValue2664 : Sparse Master := [(Sum.inr 2664, (1 / 1))]

def nodeValue2665 : Sparse Master := [(Sum.inr 2665, (1 / 1))]

def nodeValue2668 : Sparse Master := [(Sum.inr 2668, (1 / 1))]

def nodeValue2669 : Sparse Master := [(Sum.inr 2669, (1 / 1))]

def nodeValue2670 : Sparse Master := [(Sum.inr 2670, (1 / 1))]

def nodeValue2671 : Sparse Master := [(Sum.inr 2671, (1 / 1))]

def nodeValue2672 : Sparse Master := [(Sum.inr 2672, (1 / 1))]

def nodeValue2673 : Sparse Master := [(Sum.inr 2673, (1 / 1))]

def nodeValue2674 : Sparse Master := [(Sum.inr 2674, (1 / 1))]

def nodeValue2675 : Sparse Master := [(Sum.inr 2675, (1 / 1))]

def nodeValue2676 : Sparse Master := [(Sum.inr 2676, (1 / 1))]

def nodeValue2677 : Sparse Master := [(Sum.inr 2677, (1 / 1))]

def nodeValue2678 : Sparse Master := [(Sum.inr 2678, (1 / 1))]

def nodeValue2680 : Sparse Master := [(Sum.inr 2680, (1 / 1))]

def nodeValue2681 : Sparse Master := [(Sum.inr 2681, (1 / 1))]

def nodeValue2682 : Sparse Master := [(Sum.inr 2682, (1 / 1))]

def nodeValue2683 : Sparse Master := [(Sum.inr 2683, (1 / 1))]

def nodeValue2684 : Sparse Master := [(Sum.inr 2684, (1 / 1))]

def nodeValue2685 : Sparse Master := [(Sum.inr 2685, (1 / 1))]

def nodeValue2686 : Sparse Master := [(Sum.inr 2686, (1 / 1))]

def nodeValue2687 : Sparse Master := [(Sum.inr 2687, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2688 : Sparse Master := [(Sum.inr 2688, (1 / 1))]

def nodeValue2689 : Sparse Master := []

def nodeValue2690 : Sparse Master := [(Sum.inr 2690, (1 / 1))]

def nodeValue2691 : Sparse Master := []

def nodeValue2693 : Sparse Master := []

def nodeValue2694 : Sparse Master := [(Sum.inr 2694, (1 / 1))]

def nodeValue2695 : Sparse Master := []

def nodeValue2697 : Sparse Master := [(Sum.inr 2697, (1 / 1))]

def nodeValue2698 : Sparse Master := [(Sum.inr 2698, (1 / 1))]

def nodeValue2700 : Sparse Master := [(Sum.inr 2700, (1 / 1))]

def nodeValue2701 : Sparse Master := []

def nodeValue2702 : Sparse Master := [(Sum.inr 2702, (1 / 1))]

def nodeValue2703 : Sparse Master := [(Sum.inr 2703, (1 / 1))]

def nodeValue2704 : Sparse Master := [(Sum.inr 2704, (1 / 1))]

def nodeValue2705 : Sparse Master := [(Sum.inr 2705, (1 / 1))]

def nodeValue2706 : Sparse Master := [(Sum.inr 2706, (1 / 1))]

def nodeValue2707 : Sparse Master := [(Sum.inr 2707, (1 / 1))]

def nodeValue2708 : Sparse Master := [(Sum.inr 2708, (1 / 1))]

def nodeValue2709 : Sparse Master := []

def nodeValue2710 : Sparse Master := [(Sum.inr 2710, (1 / 1))]

def nodeValue2712 : Sparse Master := [(Sum.inr 2712, (1 / 1))]

def nodeValue2713 : Sparse Master := [(Sum.inr 2713, (1 / 1))]

def nodeValue2714 : Sparse Master := [(Sum.inr 2714, (1 / 1))]

def nodeValue2716 : Sparse Master := [(Sum.inr 2716, (1 / 1))]

def nodeValue2717 : Sparse Master := [(Sum.inr 2717, (1 / 1))]

def nodeValue2718 : Sparse Master := [(Sum.inr 2718, (1 / 1))]

def nodeValue2719 : Sparse Master := [(Sum.inr 2719, (1 / 1))]

def nodeValue2720 : Sparse Master := []

def nodeValue2721 : Sparse Master := [(Sum.inr 2721, (1 / 1))]

def nodeValue2722 : Sparse Master := [(Sum.inr 2722, (1 / 1))]

def nodeValue2723 : Sparse Master := [(Sum.inr 2723, (1 / 1))]

def nodeValue2724 : Sparse Master := [(Sum.inr 2724, (1 / 1))]

def nodeValue2726 : Sparse Master := [(Sum.inr 2726, (1 / 1))]

def nodeValue2727 : Sparse Master := [(Sum.inr 2727, (1 / 1))]

def nodeValue2728 : Sparse Master := [(Sum.inr 2728, (1 / 1))]

def nodeValue2729 : Sparse Master := [(Sum.inr 2729, (1 / 1))]

def nodeValue2730 : Sparse Master := [(Sum.inr 2730, (1 / 1))]

def nodeValue2731 : Sparse Master := [(Sum.inr 2731, (1 / 1))]

def nodeValue2732 : Sparse Master := [(Sum.inr 2732, (1 / 1))]

def nodeValue2734 : Sparse Master := [(Sum.inr 2734, (1 / 1))]

def nodeValue2735 : Sparse Master := [(Sum.inr 2735, (1 / 1))]

def nodeValue2736 : Sparse Master := [(Sum.inr 2736, (1 / 1))]

def nodeValue2737 : Sparse Master := [(Sum.inr 2737, (1 / 1))]

def nodeValue2738 : Sparse Master := [(Sum.inr 2738, (1 / 1))]

def nodeValue2739 : Sparse Master := [(Sum.inr 2739, (1 / 1))]

def nodeValue2740 : Sparse Master := [(Sum.inr 2740, (1 / 1))]

def nodeValue2741 : Sparse Master := []

def nodeValue2742 : Sparse Master := []

def nodeValue2743 : Sparse Master := [(Sum.inr 2743, (1 / 1))]

def nodeValue2744 : Sparse Master := [(Sum.inr 2744, (1 / 1))]

def nodeValue2745 : Sparse Master := [(Sum.inr 2745, (1 / 1))]

def nodeValue2746 : Sparse Master := [(Sum.inr 2746, (1 / 1))]

def nodeValue2747 : Sparse Master := [(Sum.inr 2747, (1 / 1))]

def nodeValue2748 : Sparse Master := [(Sum.inr 2748, (1 / 1))]

def nodeValue2749 : Sparse Master := [(Sum.inr 2749, (1 / 1))]

def nodeValue2750 : Sparse Master := [(Sum.inr 2750, (1 / 1))]

def nodeValue2751 : Sparse Master := [(Sum.inr 2751, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2752 : Sparse Master := []

def nodeValue2753 : Sparse Master := [(Sum.inl 0, (-1 / 240)), (Sum.inl 2, (5 / 864)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (11 / 864))]

def nodeValue2754 : Sparse Master := [(Sum.inr 2754, (1 / 1))]

def nodeValue2755 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 2, (-5 / 144)), (Sum.inl 13, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue2756 : Sparse Master := [(Sum.inr 2756, (1 / 1))]

def nodeValue2757 : Sparse Master := [(Sum.inr 2757, (1 / 1))]

def nodeValue2758 : Sparse Master := [(Sum.inr 2758, (1 / 1))]

def nodeValue2759 : Sparse Master := [(Sum.inr 2759, (1 / 1))]

def nodeValue2760 : Sparse Master := [(Sum.inr 2760, (1 / 1))]

def nodeValue2761 : Sparse Master := [(Sum.inr 2761, (1 / 1))]

def nodeValue2762 : Sparse Master := [(Sum.inr 2762, (1 / 1))]

def nodeValue2763 : Sparse Master := [(Sum.inr 2763, (1 / 1))]

def nodeValue2764 : Sparse Master := [(Sum.inr 2764, (1 / 1))]

def nodeValue2765 : Sparse Master := [(Sum.inr 2765, (1 / 1))]

def nodeValue2766 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 2, (-11 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue2767 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 2, (1 / 72)), (Sum.inl 1, (1 / 72))]

def nodeValue2768 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (1 / 54))]

def nodeValue2769 : Sparse Master := [(Sum.inr 2769, (1 / 1))]

def nodeValue2770 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 2, (-1 / 24))]

def nodeValue2771 : Sparse Master := [(Sum.inr 2771, (1 / 1))]

def nodeValue2772 : Sparse Master := [(Sum.inr 2772, (1 / 1))]

def nodeValue2773 : Sparse Master := [(Sum.inr 2773, (1 / 1))]

def nodeValue2774 : Sparse Master := [(Sum.inr 2774, (1 / 1))]

def nodeValue2775 : Sparse Master := [(Sum.inl 0, (-11 / 4320)), (Sum.inl 2, (-1 / 288)), (Sum.inl 3, (-1 / 18)), (Sum.inl 13, (-1 / 27)), (Sum.inl 12, (-1 / 18)), (Sum.inl 1, (-1 / 36))]

def nodeValue2776 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 2, (1 / 216)), (Sum.inl 3, (1 / 27)), (Sum.inl 13, (1 / 27)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-7 / 432))]

def nodeValue2777 : Sparse Master := [(Sum.inr 2777, (1 / 1))]

def nodeValue2778 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 2, (-1 / 48)), (Sum.inl 13, (-1 / 9)), (Sum.inl 1, (-1 / 48))]

def nodeValue2779 : Sparse Master := [(Sum.inr 2779, (1 / 1))]

def nodeValue2780 : Sparse Master := [(Sum.inr 2780, (1 / 1))]

def nodeValue2781 : Sparse Master := [(Sum.inr 2781, (1 / 1))]

def nodeValue2782 : Sparse Master := [(Sum.inr 2782, (1 / 1))]

def nodeValue2783 : Sparse Master := [(Sum.inr 2783, (1 / 1))]

def nodeValue2784 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-11 / 216))]

def nodeValue2785 : Sparse Master := []

def nodeValue2786 : Sparse Master := []

def nodeValue2787 : Sparse Master := []

def nodeValue2788 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (-1 / 9)), (Sum.inl 1, (-1 / 72))]

def nodeValue2789 : Sparse Master := [(Sum.inr 2789, (1 / 1))]

def nodeValue2790 : Sparse Master := []

def nodeValue2796 : Sparse Master := [(Sum.inr 2796, (1 / 1))]

def nodeValue2797 : Sparse Master := [(Sum.inr 2797, (1 / 1))]

def nodeValue2798 : Sparse Master := [(Sum.inr 2798, (1 / 1))]

def nodeValue2799 : Sparse Master := [(Sum.inr 2799, (1 / 1))]

def nodeValue2800 : Sparse Master := [(Sum.inr 2800, (1 / 1))]

def nodeValue2801 : Sparse Master := [(Sum.inr 2801, (1 / 1))]

def nodeValue2802 : Sparse Master := [(Sum.inr 2802, (1 / 1))]

def nodeValue2803 : Sparse Master := [(Sum.inr 2803, (1 / 1))]

def nodeValue2804 : Sparse Master := [(Sum.inr 2804, (1 / 1))]

def nodeValue2806 : Sparse Master := [(Sum.inr 2806, (1 / 1))]

def nodeValue2807 : Sparse Master := [(Sum.inr 2807, (1 / 1))]

def nodeValue2809 : Sparse Master := [(Sum.inr 2809, (1 / 1))]

def nodeValue2810 : Sparse Master := [(Sum.inr 2810, (1 / 1))]

def nodeValue2811 : Sparse Master := [(Sum.inr 2811, (1 / 1))]

def nodeValue2812 : Sparse Master := [(Sum.inr 2812, (1 / 1))]

def nodeValue2813 : Sparse Master := [(Sum.inr 2813, (1 / 1))]

def nodeValue2814 : Sparse Master := [(Sum.inr 2814, (1 / 1))]

def nodeValue2815 : Sparse Master := [(Sum.inr 2815, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2816 : Sparse Master := [(Sum.inr 2816, (1 / 1))]

def nodeValue2817 : Sparse Master := [(Sum.inr 2817, (1 / 1))]

def nodeValue2818 : Sparse Master := [(Sum.inr 2818, (1 / 1))]

def nodeValue2819 : Sparse Master := [(Sum.inr 2819, (1 / 1))]

def nodeValue2820 : Sparse Master := [(Sum.inr 2820, (1 / 1))]

def nodeValue2821 : Sparse Master := [(Sum.inr 2821, (1 / 1))]

def nodeValue2822 : Sparse Master := [(Sum.inr 2822, (1 / 1))]

def nodeValue2823 : Sparse Master := []

def nodeValue2824 : Sparse Master := [(Sum.inr 2824, (1 / 1))]

def nodeValue2826 : Sparse Master := [(Sum.inr 2826, (1 / 1))]

def nodeValue2827 : Sparse Master := [(Sum.inr 2827, (1 / 1))]

def nodeValue2828 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 9, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (-1 / 216)), (Sum.inl 71, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 1, (5 / 864)), (Sum.inl 236, (1 / 18))]

def nodeValue2829 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 68, (1 / 36)), (Sum.inl 2, (-1 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 126, (1 / 18)), (Sum.inl 3, (-1 / 54)), (Sum.inl 197, (1 / 18)), (Sum.inl 24, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (5 / 288))]

def nodeValue2831 : Sparse Master := [(Sum.inr 2831, (1 / 1))]

def nodeValue2832 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (1 / 144)), (Sum.inl 197, (-1 / 9)), (Sum.inl 1, (1 / 72))]

def nodeValue2833 : Sparse Master := [(Sum.inr 2833, (1 / 1))]

def nodeValue2834 : Sparse Master := [(Sum.inr 2834, (1 / 1))]

def nodeValue2835 : Sparse Master := [(Sum.inr 2835, (1 / 1))]

def nodeValue2836 : Sparse Master := [(Sum.inr 2836, (1 / 1))]

def nodeValue2837 : Sparse Master := [(Sum.inr 2837, (1 / 1))]

def nodeValue2838 : Sparse Master := [(Sum.inr 2838, (1 / 1))]

def nodeValue2841 : Sparse Master := [(Sum.inr 2841, (1 / 1))]

def nodeValue2842 : Sparse Master := [(Sum.inr 2842, (1 / 1))]

def nodeValue2846 : Sparse Master := [(Sum.inr 2846, (1 / 1))]

def nodeValue2847 : Sparse Master := [(Sum.inr 2847, (1 / 1))]

def nodeValue2848 : Sparse Master := [(Sum.inr 2848, (1 / 1))]

def nodeValue2849 : Sparse Master := [(Sum.inr 2849, (1 / 1))]

def nodeValue2853 : Sparse Master := [(Sum.inr 2853, (1 / 1))]

def nodeValue2856 : Sparse Master := [(Sum.inr 2856, (1 / 1))]

def nodeValue2857 : Sparse Master := [(Sum.inr 2857, (1 / 1))]

def nodeValue2858 : Sparse Master := [(Sum.inr 2858, (1 / 1))]

def nodeValue2859 : Sparse Master := [(Sum.inr 2859, (1 / 1))]

def nodeValue2860 : Sparse Master := [(Sum.inr 2860, (1 / 1))]

def nodeValue2861 : Sparse Master := [(Sum.inr 2861, (1 / 1))]

def nodeValue2862 : Sparse Master := [(Sum.inr 2862, (1 / 1))]

def nodeValue2864 : Sparse Master := [(Sum.inr 2864, (1 / 1))]

def nodeValue2865 : Sparse Master := [(Sum.inr 2865, (1 / 1))]

def nodeValue2867 : Sparse Master := [(Sum.inr 2867, (1 / 1))]

def nodeValue2868 : Sparse Master := [(Sum.inr 2868, (1 / 1))]

def nodeValue2869 : Sparse Master := [(Sum.inr 2869, (1 / 1))]

def nodeValue2870 : Sparse Master := [(Sum.inr 2870, (1 / 1))]

def nodeValue2871 : Sparse Master := [(Sum.inr 2871, (1 / 1))]

def nodeValue2872 : Sparse Master := [(Sum.inr 2872, (1 / 1))]

def nodeValue2873 : Sparse Master := [(Sum.inr 2873, (1 / 1))]

def nodeValue2874 : Sparse Master := [(Sum.inr 2874, (1 / 1))]

def nodeValue2875 : Sparse Master := [(Sum.inr 2875, (1 / 1))]

def nodeValue2876 : Sparse Master := [(Sum.inr 2876, (1 / 1))]

def nodeValue2877 : Sparse Master := [(Sum.inr 2877, (1 / 1))]

def nodeValue2878 : Sparse Master := [(Sum.inr 2878, (1 / 1))]

def nodeValue2879 : Sparse Master := [(Sum.inr 2879, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2880 : Sparse Master := [(Sum.inr 2880, (1 / 1))]

def nodeValue2881 : Sparse Master := [(Sum.inr 2881, (1 / 1))]

def nodeValue2882 : Sparse Master := [(Sum.inr 2882, (1 / 1))]

def nodeValue2883 : Sparse Master := [(Sum.inr 2883, (1 / 1))]

def nodeValue2884 : Sparse Master := [(Sum.inr 2884, (1 / 1))]

def nodeValue2885 : Sparse Master := [(Sum.inr 2885, (1 / 1))]

def nodeValue2886 : Sparse Master := [(Sum.inr 2886, (1 / 1))]

def nodeValue2887 : Sparse Master := [(Sum.inr 2887, (1 / 1))]

def nodeValue2888 : Sparse Master := [(Sum.inr 2888, (1 / 1))]

def nodeValue2889 : Sparse Master := [(Sum.inr 2889, (1 / 1))]

def nodeValue2890 : Sparse Master := [(Sum.inr 2890, (1 / 1))]

def nodeValue2892 : Sparse Master := [(Sum.inr 2892, (1 / 1))]

def nodeValue2893 : Sparse Master := [(Sum.inr 2893, (1 / 1))]

def nodeValue2894 : Sparse Master := []

def nodeValue2895 : Sparse Master := [(Sum.inr 2895, (1 / 1))]

def nodeValue2896 : Sparse Master := [(Sum.inr 2896, (1 / 1))]

def nodeValue2897 : Sparse Master := []

def nodeValue2898 : Sparse Master := [(Sum.inr 2898, (1 / 1))]

def nodeValue2899 : Sparse Master := [(Sum.inr 2899, (1 / 1))]

def nodeValue2900 : Sparse Master := [(Sum.inr 2900, (1 / 1))]

def nodeValue2901 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 9, (1 / 216)), (Sum.inl 58, (-1 / 864)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (7 / 864)), (Sum.inl 68, (-1 / 72)), (Sum.inl 2, (1 / 144)), (Sum.inl 70, (1 / 54)), (Sum.inl 71, (1 / 54)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 18)), (Sum.inl 3, (1 / 54)), (Sum.inl 197, (-1 / 18)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue2902 : Sparse Master := [(Sum.inr 2902, (1 / 1))]

def nodeValue2903 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (-1 / 288)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (1 / 54)), (Sum.inl 71, (1 / 54)), (Sum.inl 7, (1 / 27)), (Sum.inl 8, (1 / 27)), (Sum.inl 126, (-1 / 18)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (1 / 54)), (Sum.inl 1, (11 / 864)), (Sum.inl 236, (-1 / 18))]

def nodeValue2904 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (-1 / 216)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (1 / 864)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (1 / 72)), (Sum.inl 70, (-1 / 54)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 3, (-1 / 54)), (Sum.inl 197, (1 / 18)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (17 / 864))]

def nodeValue2905 : Sparse Master := [(Sum.inr 2905, (1 / 1))]

def nodeValue2906 : Sparse Master := [(Sum.inr 2906, (1 / 1))]

def nodeValue2907 : Sparse Master := [(Sum.inr 2907, (1 / 1))]

def nodeValue2908 : Sparse Master := [(Sum.inr 2908, (1 / 1))]

def nodeValue2909 : Sparse Master := [(Sum.inr 2909, (1 / 1))]

def nodeValue2910 : Sparse Master := [(Sum.inr 2910, (1 / 1))]

def nodeValue2911 : Sparse Master := [(Sum.inr 2911, (1 / 1))]

def nodeValue2912 : Sparse Master := [(Sum.inr 2912, (1 / 1))]

def nodeValue2913 : Sparse Master := [(Sum.inr 2913, (1 / 1))]

def nodeValue2914 : Sparse Master := []

def nodeValue2916 : Sparse Master := [(Sum.inr 2916, (1 / 1))]

def nodeValue2917 : Sparse Master := []

def nodeValue2918 : Sparse Master := [(Sum.inr 2918, (1 / 1))]

def nodeValue2919 : Sparse Master := [(Sum.inr 2919, (1 / 1))]

def nodeValue2920 : Sparse Master := [(Sum.inr 2920, (1 / 1))]

def nodeValue2921 : Sparse Master := [(Sum.inr 2921, (1 / 1))]

def nodeValue2922 : Sparse Master := [(Sum.inr 2922, (1 / 1))]

def nodeValue2923 : Sparse Master := [(Sum.inr 2923, (1 / 1))]

def nodeValue2924 : Sparse Master := [(Sum.inr 2924, (1 / 1))]

def nodeValue2925 : Sparse Master := [(Sum.inr 2925, (1 / 1))]

def nodeValue2926 : Sparse Master := [(Sum.inr 2926, (1 / 1))]

def nodeValue2927 : Sparse Master := []

def nodeValue2928 : Sparse Master := [(Sum.inr 2928, (1 / 1))]

def nodeValue2929 : Sparse Master := [(Sum.inr 2929, (1 / 1))]

def nodeValue2930 : Sparse Master := [(Sum.inr 2930, (1 / 1))]

def nodeValue2931 : Sparse Master := [(Sum.inr 2931, (1 / 1))]

def nodeValue2933 : Sparse Master := [(Sum.inr 2933, (1 / 1))]

def nodeValue2934 : Sparse Master := []

def nodeValue2936 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 5, (-1 / 36)), (Sum.inl 6, (1 / 288)), (Sum.inl 2, (5 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-17 / 432))]

def nodeValue2937 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (1 / 288)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 54)), (Sum.inl 1, (1 / 144))]

def nodeValue2939 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (1 / 144)), (Sum.inl 1, (1 / 216))]

def nodeValue2940 : Sparse Master := []

def nodeValue2941 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 216)), (Sum.inl 2, (5 / 432)), (Sum.inl 35, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (1 / 108))]

def nodeValue2942 : Sparse Master := [(Sum.inr 2942, (1 / 1))]

def nodeValue2943 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 5, (1 / 54)), (Sum.inl 2, (-11 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 8, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue2945 : Sparse Master := [(Sum.inr 2945, (1 / 1))]

def nodeValue2946 : Sparse Master := [(Sum.inr 2946, (1 / 1))]

def nodeValue2947 : Sparse Master := [(Sum.inr 2947, (1 / 1))]

def nodeValue2949 : Sparse Master := [(Sum.inr 2949, (1 / 1))]

def nodeValue2950 : Sparse Master := [(Sum.inr 2950, (1 / 1))]

def nodeValue2951 : Sparse Master := [(Sum.inr 2951, (1 / 1))]

def nodeValue2952 : Sparse Master := [(Sum.inr 2952, (1 / 1))]

def nodeValue2953 : Sparse Master := []

def nodeValue2954 : Sparse Master := [(Sum.inr 2954, (1 / 1))]

def nodeValue2955 : Sparse Master := [(Sum.inr 2955, (1 / 1))]

def nodeValue2956 : Sparse Master := [(Sum.inr 2956, (1 / 1))]

def nodeValue2957 : Sparse Master := [(Sum.inl 0, (-17 / 4320)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (5 / 216)), (Sum.inl 7, (1 / 18)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (2 / 9)), (Sum.inl 26, (1 / 9)), (Sum.inl 4, (1 / 9)), (Sum.inl 1, (-5 / 216))]

def nodeValue2958 : Sparse Master := [(Sum.inl 0, (-49 / 4320)), (Sum.inl 6, (-1 / 288)), (Sum.inl 2, (11 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue2959 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-5 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 1, (7 / 432))]

def nodeValue2960 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 144)), (Sum.inl 8, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue2961 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 288)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 18)), (Sum.inl 26, (-1 / 27)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (1 / 54))]

def nodeValue2962 : Sparse Master := [(Sum.inr 2962, (1 / 1))]

def nodeValue2963 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (-19 / 432))]

def nodeValue2964 : Sparse Master := [(Sum.inr 2964, (1 / 1))]

def nodeValue2965 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 108)), (Sum.inl 6, (-1 / 432)), (Sum.inl 1, (-5 / 108))]

def nodeValue2966 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 216)), (Sum.inl 35, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 72))]

def nodeValue2967 : Sparse Master := [(Sum.inr 2967, (1 / 1))]

def nodeValue2968 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 432)), (Sum.inl 7, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-7 / 216))]

def nodeValue2969 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 5, (1 / 108)), (Sum.inl 8, (1 / 27)), (Sum.inl 1, (1 / 108))]

def nodeValue2970 : Sparse Master := [(Sum.inr 2970, (1 / 1))]

def nodeValue2971 : Sparse Master := [(Sum.inr 2971, (1 / 1))]

def nodeValue2972 : Sparse Master := [(Sum.inr 2972, (1 / 1))]

def nodeValue2973 : Sparse Master := [(Sum.inr 2973, (1 / 1))]

def nodeValue2974 : Sparse Master := [(Sum.inr 2974, (1 / 1))]

def nodeValue2975 : Sparse Master := [(Sum.inr 2975, (1 / 1))]

def nodeValue2976 : Sparse Master := [(Sum.inr 2976, (1 / 1))]

def nodeValue2977 : Sparse Master := [(Sum.inr 2977, (1 / 1))]

def nodeValue2978 : Sparse Master := [(Sum.inr 2978, (1 / 1))]

def nodeValue2979 : Sparse Master := [(Sum.inr 2979, (1 / 1))]

def nodeValue2980 : Sparse Master := [(Sum.inr 2980, (1 / 1))]

def nodeValue2981 : Sparse Master := [(Sum.inr 2981, (1 / 1))]

def nodeValue2983 : Sparse Master := [(Sum.inr 2983, (1 / 1))]

def nodeValue2984 : Sparse Master := [(Sum.inr 2984, (1 / 1))]

def nodeValue2985 : Sparse Master := [(Sum.inr 2985, (1 / 1))]

def nodeValue2986 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (1 / 96)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 18)), (Sum.inl 52, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-1 / 144))]

def nodeValue2987 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 5, (-1 / 36)), (Sum.inl 6, (1 / 288)), (Sum.inl 2, (7 / 432)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 52, (1 / 54)), (Sum.inl 1, (-1 / 48))]

def nodeValue2988 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (1 / 216)), (Sum.inl 2, (-1 / 54)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 864))]

def nodeValue2990 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (-11 / 864)), (Sum.inl 7, (-1 / 27)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 18)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (1 / 72))]

def nodeValue2991 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (1 / 54)), (Sum.inl 2, (-1 / 72)), (Sum.inl 8, (-1 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue2992 : Sparse Master := [(Sum.inr 2992, (1 / 1))]

def nodeValue2995 : Sparse Master := [(Sum.inr 2995, (1 / 1))]

def nodeValue2996 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (1 / 54)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue2997 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-1 / 144)), (Sum.inl 35, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (1 / 96))]

def nodeValue2998 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-7 / 432)), (Sum.inl 3, (-1 / 27)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue2999 : Sparse Master := []

def nodeValue3000 : Sparse Master := []

def nodeValue3001 : Sparse Master := []

def nodeValue3002 : Sparse Master := []

def nodeValue3003 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (13 / 864)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 26, (-1 / 27)), (Sum.inl 1, (11 / 864))]

def nodeValue3004 : Sparse Master := []

def nodeValue3005 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (1 / 432)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 108))]

def nodeValue3006 : Sparse Master := []

def nodeValue3007 : Sparse Master := [(Sum.inr 3007, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3008 : Sparse Master := [(Sum.inr 3008, (1 / 1))]

def nodeValue3010 : Sparse Master := [(Sum.inr 3010, (1 / 1))]

def nodeValue3011 : Sparse Master := [(Sum.inr 3011, (1 / 1))]

def nodeValue3012 : Sparse Master := [(Sum.inr 3012, (1 / 1))]

def nodeValue3013 : Sparse Master := [(Sum.inr 3013, (1 / 1))]

def nodeValue3014 : Sparse Master := [(Sum.inr 3014, (1 / 1))]

def nodeValue3015 : Sparse Master := [(Sum.inr 3015, (1 / 1))]

def nodeValue3016 : Sparse Master := [(Sum.inr 3016, (1 / 1))]

def nodeValue3017 : Sparse Master := [(Sum.inr 3017, (1 / 1))]

def nodeValue3018 : Sparse Master := [(Sum.inr 3018, (1 / 1))]

def nodeValue3019 : Sparse Master := [(Sum.inr 3019, (1 / 1))]

def nodeValue3022 : Sparse Master := [(Sum.inr 3022, (1 / 1))]

def nodeValue3023 : Sparse Master := [(Sum.inr 3023, (1 / 1))]

def nodeValue3024 : Sparse Master := [(Sum.inr 3024, (1 / 1))]

def nodeValue3025 : Sparse Master := [(Sum.inr 3025, (1 / 1))]

def nodeValue3028 : Sparse Master := [(Sum.inr 3028, (1 / 1))]

def nodeValue3029 : Sparse Master := [(Sum.inr 3029, (1 / 1))]

def nodeValue3030 : Sparse Master := [(Sum.inr 3030, (1 / 1))]

def nodeValue3031 : Sparse Master := [(Sum.inr 3031, (1 / 1))]

def nodeValue3032 : Sparse Master := [(Sum.inr 3032, (1 / 1))]

def nodeValue3033 : Sparse Master := [(Sum.inr 3033, (1 / 1))]

def nodeValue3034 : Sparse Master := [(Sum.inr 3034, (1 / 1))]

def nodeValue3035 : Sparse Master := [(Sum.inr 3035, (1 / 1))]

def nodeValue3036 : Sparse Master := [(Sum.inr 3036, (1 / 1))]

def nodeValue3037 : Sparse Master := [(Sum.inr 3037, (1 / 1))]

def nodeValue3038 : Sparse Master := [(Sum.inr 3038, (1 / 1))]

def nodeValue3039 : Sparse Master := [(Sum.inr 3039, (1 / 1))]

def nodeValue3040 : Sparse Master := [(Sum.inr 3040, (1 / 1))]

def nodeValue3041 : Sparse Master := [(Sum.inr 3041, (1 / 1))]

def nodeValue3042 : Sparse Master := [(Sum.inr 3042, (1 / 1))]

def nodeValue3043 : Sparse Master := [(Sum.inr 3043, (1 / 1))]

def nodeValue3044 : Sparse Master := [(Sum.inr 3044, (1 / 1))]

def nodeValue3045 : Sparse Master := [(Sum.inr 3045, (1 / 1))]

def nodeValue3046 : Sparse Master := [(Sum.inr 3046, (1 / 1))]

def nodeValue3049 : Sparse Master := [(Sum.inr 3049, (1 / 1))]

def nodeValue3050 : Sparse Master := [(Sum.inr 3050, (1 / 1))]

def nodeValue3051 : Sparse Master := [(Sum.inr 3051, (1 / 1))]

def nodeValue3052 : Sparse Master := [(Sum.inr 3052, (1 / 1))]

def nodeValue3053 : Sparse Master := [(Sum.inr 3053, (1 / 1))]

def nodeValue3054 : Sparse Master := [(Sum.inr 3054, (1 / 1))]

def nodeValue3055 : Sparse Master := [(Sum.inr 3055, (1 / 1))]

def nodeValue3056 : Sparse Master := [(Sum.inr 3056, (1 / 1))]

def nodeValue3057 : Sparse Master := [(Sum.inr 3057, (1 / 1))]

def nodeValue3058 : Sparse Master := [(Sum.inr 3058, (1 / 1))]

def nodeValue3059 : Sparse Master := [(Sum.inr 3059, (1 / 1))]

def nodeValue3061 : Sparse Master := []

def nodeValue3062 : Sparse Master := [(Sum.inr 3062, (1 / 1))]

def nodeValue3063 : Sparse Master := [(Sum.inr 3063, (1 / 1))]

def nodeValue3064 : Sparse Master := [(Sum.inr 3064, (1 / 1))]

def nodeValue3065 : Sparse Master := []

def nodeValue3066 : Sparse Master := [(Sum.inr 3066, (1 / 1))]

def nodeValue3067 : Sparse Master := [(Sum.inr 3067, (1 / 1))]

def nodeValue3068 : Sparse Master := [(Sum.inr 3068, (1 / 1))]

def nodeValue3069 : Sparse Master := [(Sum.inr 3069, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3072 : Sparse Master := [(Sum.inr 3072, (1 / 1))]

def nodeValue3073 : Sparse Master := [(Sum.inr 3073, (1 / 1))]

def nodeValue3074 : Sparse Master := [(Sum.inr 3074, (1 / 1))]

def nodeValue3075 : Sparse Master := [(Sum.inr 3075, (1 / 1))]

def nodeValue3076 : Sparse Master := []

def nodeValue3077 : Sparse Master := [(Sum.inr 3077, (1 / 1))]

def nodeValue3078 : Sparse Master := [(Sum.inr 3078, (1 / 1))]

def nodeValue3079 : Sparse Master := [(Sum.inr 3079, (1 / 1))]

def nodeValue3080 : Sparse Master := []

def nodeValue3081 : Sparse Master := [(Sum.inl 0, (-5 / 432)), (Sum.inl 5, (1 / 216)), (Sum.inl 2, (1 / 108)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (1 / 54)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 26, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (5 / 432))]

def nodeValue3082 : Sparse Master := [(Sum.inl 0, (-13 / 1440)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (-37 / 864)), (Sum.inl 35, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue3083 : Sparse Master := [(Sum.inr 3083, (1 / 1))]

def nodeValue3084 : Sparse Master := [(Sum.inr 3084, (1 / 1))]

def nodeValue3085 : Sparse Master := []

def nodeValue3086 : Sparse Master := [(Sum.inr 3086, (1 / 1))]

def nodeValue3087 : Sparse Master := [(Sum.inl 0, (-17 / 4320)), (Sum.inl 2, (1 / 288)), (Sum.inl 3, (5 / 54)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-11 / 216))]

def nodeValue3088 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 2, (7 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue3089 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 2, (1 / 96)), (Sum.inl 3, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue3090 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 2, (-1 / 24))]

def nodeValue3091 : Sparse Master := [(Sum.inr 3091, (1 / 1))]

def nodeValue3092 : Sparse Master := [(Sum.inr 3092, (1 / 1))]

def nodeValue3093 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (-7 / 288)), (Sum.inl 35, (1 / 18)), (Sum.inl 3, (2 / 9)), (Sum.inl 13, (1 / 27)), (Sum.inl 55, (-1 / 6)), (Sum.inl 12, (1 / 18)), (Sum.inl 26, (1 / 9)), (Sum.inl 4, (1 / 9)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (-5 / 288))]

def nodeValue3094 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 72)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 55, (1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (5 / 288))]

def nodeValue3095 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-17 / 432)), (Sum.inl 35, (1 / 27)), (Sum.inl 13, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue3096 : Sparse Master := [(Sum.inr 3096, (1 / 1))]

def nodeValue3097 : Sparse Master := [(Sum.inr 3097, (1 / 1))]

def nodeValue3098 : Sparse Master := [(Sum.inr 3098, (1 / 1))]

def nodeValue3099 : Sparse Master := [(Sum.inl 0, (-7 / 1440)), (Sum.inl 2, (-5 / 864)), (Sum.inl 3, (-1 / 18)), (Sum.inl 26, (-1 / 27)), (Sum.inl 4, (-1 / 27))]

def nodeValue3100 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 2, (-11 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 1, (1 / 216))]

def nodeValue3101 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (1 / 54))]

def nodeValue3102 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 2, (1 / 72)), (Sum.inl 1, (1 / 72))]

def nodeValue3103 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3104 : Sparse Master := []

def nodeValue3105 : Sparse Master := [(Sum.inl 0, (-7 / 864)), (Sum.inl 5, (1 / 216)), (Sum.inl 2, (-1 / 108)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (7 / 54)), (Sum.inl 55, (-1 / 18)), (Sum.inl 26, (2 / 27)), (Sum.inl 4, (2 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-41 / 864))]

def nodeValue3106 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (-1 / 54)), (Sum.inl 55, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (1 / 216))]

def nodeValue3108 : Sparse Master := [(Sum.inr 3108, (1 / 1))]

def nodeValue3109 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 2, (-1 / 108)), (Sum.inl 3, (-1 / 27)), (Sum.inl 26, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (1 / 432))]

def nodeValue3110 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (1 / 54))]

def nodeValue3111 : Sparse Master := []

def nodeValue3112 : Sparse Master := []

def nodeValue3113 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (1 / 108)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue3114 : Sparse Master := []

def nodeValue3115 : Sparse Master := [(Sum.inr 3115, (1 / 1))]

def nodeValue3116 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 5, (-1 / 216)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 18)), (Sum.inl 55, (1 / 18)), (Sum.inl 26, (-1 / 27)), (Sum.inl 4, (-1 / 27)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (1 / 864))]

def nodeValue3117 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (1 / 144)), (Sum.inl 55, (-1 / 9)), (Sum.inl 27, (-1 / 36)), (Sum.inl 1, (1 / 72))]

def nodeValue3118 : Sparse Master := [(Sum.inr 3118, (1 / 1))]

def nodeValue3119 : Sparse Master := [(Sum.inl 0, (-13 / 2160)), (Sum.inl 2, (-1 / 144)), (Sum.inl 3, (1 / 27)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (1 / 216))]

def nodeValue3120 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 1, (-11 / 216))]

def nodeValue3121 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (-1 / 9)), (Sum.inl 1, (-1 / 72))]

def nodeValue3122 : Sparse Master := []

def nodeValue3123 : Sparse Master := []

def nodeValue3124 : Sparse Master := []

def nodeValue3125 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (1 / 72)), (Sum.inl 26, (-1 / 9)), (Sum.inl 1, (1 / 48))]

def nodeValue3126 : Sparse Master := []

def nodeValue3127 : Sparse Master := [(Sum.inr 3127, (1 / 1))]

def nodeValue3128 : Sparse Master := [(Sum.inr 3128, (1 / 1))]

def nodeValue3129 : Sparse Master := [(Sum.inr 3129, (1 / 1))]

def nodeValue3130 : Sparse Master := [(Sum.inr 3130, (1 / 1))]

def nodeValue3131 : Sparse Master := [(Sum.inr 3131, (1 / 1))]

def nodeValue3132 : Sparse Master := [(Sum.inr 3132, (1 / 1))]

def nodeValue3133 : Sparse Master := [(Sum.inr 3133, (1 / 1))]

def nodeValue3134 : Sparse Master := [(Sum.inr 3134, (1 / 1))]

def nodeValue3135 : Sparse Master := [(Sum.inr 3135, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3136 : Sparse Master := [(Sum.inr 3136, (1 / 1))]

def nodeValue3137 : Sparse Master := [(Sum.inr 3137, (1 / 1))]

def nodeValue3138 : Sparse Master := [(Sum.inr 3138, (1 / 1))]

def nodeValue3139 : Sparse Master := [(Sum.inl 0, (-5 / 864)), (Sum.inl 9, (1 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-1 / 432)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-1 / 54)), (Sum.inl 70, (1 / 54)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 18)), (Sum.inl 125, (-1 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 197, (-2 / 9)), (Sum.inl 24, (-1 / 9)), (Sum.inl 55, (-1 / 18)), (Sum.inl 56, (-1 / 9)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (-17 / 864))]

def nodeValue3140 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 9, (1 / 216)), (Sum.inl 5, (1 / 54)), (Sum.inl 6, (-1 / 864)), (Sum.inl 68, (-5 / 72)), (Sum.inl 2, (-5 / 864)), (Sum.inl 70, (1 / 54)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 18)), (Sum.inl 125, (-1 / 9)), (Sum.inl 3, (1 / 18)), (Sum.inl 13, (1 / 54)), (Sum.inl 196, (-1 / 18)), (Sum.inl 197, (-1 / 9)), (Sum.inl 23, (-1 / 18)), (Sum.inl 54, (-1 / 18)), (Sum.inl 55, (-1 / 9)), (Sum.inl 12, (1 / 54)), (Sum.inl 26, (1 / 27)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (5 / 864))]

def nodeValue3141 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (-1 / 216)), (Sum.inl 68, (1 / 36)), (Sum.inl 2, (1 / 108)), (Sum.inl 125, (1 / 18)), (Sum.inl 196, (1 / 18)), (Sum.inl 23, (1 / 18)), (Sum.inl 54, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-1 / 54))]

def nodeValue3142 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 68, (1 / 36)), (Sum.inl 2, (-1 / 432)), (Sum.inl 197, (1 / 9)), (Sum.inl 24, (1 / 18)), (Sum.inl 56, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (1 / 432))]

def nodeValue3143 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (-1 / 216)), (Sum.inl 5, (-1 / 108)), (Sum.inl 68, (1 / 72)), (Sum.inl 2, (-1 / 32)), (Sum.inl 70, (-1 / 54)), (Sum.inl 35, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 196, (1 / 18)), (Sum.inl 1, (7 / 864))]

def nodeValue3144 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 68, (1 / 36)), (Sum.inl 2, (1 / 96)), (Sum.inl 125, (1 / 18)), (Sum.inl 197, (1 / 18)), (Sum.inl 55, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (5 / 288))]

def nodeValue3145 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (-1 / 36)), (Sum.inl 196, (-1 / 9)), (Sum.inl 1, (-1 / 36))]

def nodeValue3146 : Sparse Master := [(Sum.inr 3146, (1 / 1))]

def nodeValue3147 : Sparse Master := [(Sum.inr 3147, (1 / 1))]

def nodeValue3149 : Sparse Master := [(Sum.inr 3149, (1 / 1))]

def nodeValue3150 : Sparse Master := [(Sum.inr 3150, (1 / 1))]

def nodeValue3151 : Sparse Master := [(Sum.inr 3151, (1 / 1))]

def nodeValue3152 : Sparse Master := [(Sum.inr 3152, (1 / 1))]

def nodeValue3153 : Sparse Master := [(Sum.inr 3153, (1 / 1))]

def nodeValue3154 : Sparse Master := [(Sum.inr 3154, (1 / 1))]

def nodeValue3155 : Sparse Master := [(Sum.inr 3155, (1 / 1))]

def nodeValue3156 : Sparse Master := [(Sum.inr 3156, (1 / 1))]

def nodeValue3157 : Sparse Master := [(Sum.inr 3157, (1 / 1))]

def nodeValue3158 : Sparse Master := [(Sum.inr 3158, (1 / 1))]

def nodeValue3159 : Sparse Master := [(Sum.inr 3159, (1 / 1))]

def nodeValue3160 : Sparse Master := [(Sum.inr 3160, (1 / 1))]

def nodeValue3161 : Sparse Master := [(Sum.inr 3161, (1 / 1))]

def nodeValue3162 : Sparse Master := [(Sum.inr 3162, (1 / 1))]

def nodeValue3163 : Sparse Master := [(Sum.inr 3163, (1 / 1))]

def nodeValue3164 : Sparse Master := [(Sum.inr 3164, (1 / 1))]

def nodeValue3165 : Sparse Master := [(Sum.inr 3165, (1 / 1))]

def nodeValue3166 : Sparse Master := [(Sum.inr 3166, (1 / 1))]

def nodeValue3168 : Sparse Master := [(Sum.inr 3168, (1 / 1))]

def nodeValue3170 : Sparse Master := [(Sum.inr 3170, (1 / 1))]

def nodeValue3172 : Sparse Master := [(Sum.inr 3172, (1 / 1))]

def nodeValue3174 : Sparse Master := [(Sum.inr 3174, (1 / 1))]

def nodeValue3175 : Sparse Master := [(Sum.inr 3175, (1 / 1))]

def nodeValue3176 : Sparse Master := [(Sum.inr 3176, (1 / 1))]

def nodeValue3178 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-5 / 864)), (Sum.inl 54, (1 / 18)), (Sum.inl 56, (1 / 18)), (Sum.inl 228, (1 / 18)), (Sum.inl 1, (1 / 864))]

def nodeValue3179 : Sparse Master := [(Sum.inr 3179, (1 / 1))]

def nodeValue3180 : Sparse Master := [(Sum.inr 3180, (1 / 1))]

def nodeValue3184 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (-5 / 864)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 54)), (Sum.inl 56, (1 / 18)), (Sum.inl 26, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (-1 / 432))]

def nodeValue3185 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 72)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 54, (1 / 18)), (Sum.inl 26, (-1 / 27)), (Sum.inl 1, (1 / 48))]

def nodeValue3187 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (1 / 432)), (Sum.inl 54, (-1 / 9)), (Sum.inl 1, (-11 / 432))]

def nodeValue3188 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-1 / 108)), (Sum.inl 56, (-1 / 9)), (Sum.inl 1, (-1 / 216))]

def nodeValue3189 : Sparse Master := [(Sum.inr 3189, (1 / 1))]

def nodeValue3190 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (-1 / 72)), (Sum.inl 6, (-1 / 432)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (5 / 432)), (Sum.inl 69, (1 / 54)), (Sum.inl 70, (1 / 54)), (Sum.inl 7, (1 / 18)), (Sum.inl 35, (2 / 27)), (Sum.inl 125, (-1 / 18)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (2 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 196, (-1 / 18)), (Sum.inl 23, (-1 / 18)), (Sum.inl 54, (-1 / 9)), (Sum.inl 12, (1 / 54)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (1 / 48))]

def nodeValue3191 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 9, (1 / 108)), (Sum.inl 5, (-7 / 216)), (Sum.inl 68, (-1 / 36)), (Sum.inl 2, (-1 / 216)), (Sum.inl 71, (1 / 27)), (Sum.inl 8, (1 / 18)), (Sum.inl 197, (-1 / 9)), (Sum.inl 24, (-1 / 18)), (Sum.inl 56, (-1 / 9)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-1 / 108))]

def nodeValue3193 : Sparse Master := [(Sum.inr 3193, (1 / 1))]

def nodeValue3195 : Sparse Master := [(Sum.inr 3195, (1 / 1))]

def nodeValue3196 : Sparse Master := [(Sum.inr 3196, (1 / 1))]

def nodeValue3197 : Sparse Master := [(Sum.inr 3197, (1 / 1))]

def nodeValue3198 : Sparse Master := [(Sum.inr 3198, (1 / 1))]

def nodeValue3199 : Sparse Master := [(Sum.inr 3199, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue320 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (25 / 216)), (Sum.inl 6, (-5 / 288)), (Sum.inl 2, (5 / 216)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (-5 / 144))]

def nodeValue321 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (5 / 36)), (Sum.inl 6, (-5 / 288)), (Sum.inl 2, (-25 / 432)), (Sum.inl 7, (-5 / 54)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (85 / 432))]

def nodeValue322 : Sparse Master := [(Sum.inl 0, (1 / 48)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 864)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-25 / 432)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-10 / 27)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-25 / 54)), (Sum.inl 52, (-5 / 27)), (Sum.inl 12, (-5 / 27)), (Sum.inl 26, (-10 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (65 / 864))]

def nodeValue323 : Sparse Master := [(Sum.inl 0, (13 / 864)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (5 / 216)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 52, (5 / 27)), (Sum.inl 1, (65 / 864))]

def nodeValue324 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 5, (-5 / 108)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 54)), (Sum.inl 2, (-5 / 144)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 27)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue325 : Sparse Master := [(Sum.inl 0, (11 / 288)), (Sum.inl 5, (-5 / 54)), (Sum.inl 2, (55 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue326 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 54)), (Sum.inl 6, (-5 / 432)), (Sum.inl 2, (-65 / 864)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 1, (35 / 432))]

def nodeValue327 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 432)), (Sum.inl 64, (5 / 18)), (Sum.inl 67, (-5 / 27)), (Sum.inl 34, (-25 / 54)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-55 / 54)), (Sum.inl 13, (-10 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 26, (-20 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (35 / 288))]

def nodeValue328 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 64, (-5 / 18)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 54)), (Sum.inl 2, (55 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue329 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 2, (5 / 108)), (Sum.inl 7, (5 / 54)), (Sum.inl 8, (5 / 54)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (25 / 864))]

def nodeValue330 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 33, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-55 / 864)), (Sum.inl 81, (5 / 18)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-5 / 54)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-25 / 54)), (Sum.inl 4, (-5 / 18)), (Sum.inl 1, (-5 / 864))]

def nodeValue331 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (-25 / 216)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-10 / 9)), (Sum.inl 26, (-5 / 9)), (Sum.inl 4, (-5 / 9)), (Sum.inl 1, (25 / 216))]

def nodeValue332 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 288)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 26, (5 / 27)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-5 / 54))]

def nodeValue333 : Sparse Master := [(Sum.inl 0, (7 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (25 / 864)), (Sum.inl 81, (-5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (5 / 108))]

def nodeValue334 : Sparse Master := [(Sum.inl 0, (49 / 864)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (-55 / 432)), (Sum.inl 7, (-5 / 54)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue335 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (-5 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (95 / 432))]

def nodeValue336 : Sparse Master := [(Sum.inl 0, (47 / 864)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 144)), (Sum.inl 8, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue337 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 864)), (Sum.inl 7, (5 / 54)), (Sum.inl 35, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (65 / 432))]

def nodeValue338 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 1, (25 / 108))]

def nodeValue339 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (25 / 432)), (Sum.inl 7, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 1, (-35 / 432))]

def nodeValue340 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (5 / 108)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 26, (5 / 18)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (5 / 216))]

def nodeValue341 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (5 / 432)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-25 / 216))]

def nodeValue342 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 67, (-5 / 27)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (5 / 432)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue343 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 432)), (Sum.inl 7, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (35 / 216))]

def nodeValue344 : Sparse Master := [(Sum.inl 0, (1 / 18)), (Sum.inl 5, (-5 / 108)), (Sum.inl 8, (-5 / 27)), (Sum.inl 1, (-5 / 108))]

def nodeValue345 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 108)), (Sum.inl 6, (-5 / 864)), (Sum.inl 64, (5 / 18)), (Sum.inl 34, (-5 / 54)), (Sum.inl 2, (-95 / 864)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-25 / 27)), (Sum.inl 13, (-35 / 54)), (Sum.inl 52, (-5 / 18)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-10 / 27)), (Sum.inl 1, (5 / 96))]

def nodeValue346 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 64, (-5 / 18)), (Sum.inl 2, (5 / 96)), (Sum.inl 7, (5 / 54)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 1, (-35 / 864))]

def nodeValue347 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 64, (5 / 18)), (Sum.inl 33, (5 / 9)), (Sum.inl 34, (-5 / 54)), (Sum.inl 2, (-5 / 54)), (Sum.inl 123, (5 / 9)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 31, (5 / 9))]

def nodeValue348 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 64, (-5 / 18)), (Sum.inl 2, (35 / 864)), (Sum.inl 123, (-5 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 25, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-5 / 96))]

def nodeValue349 : Sparse Master := [(Sum.inl 0, (5 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (5 / 432)), (Sum.inl 123, (-5 / 18)), (Sum.inl 51, (-5 / 18)), (Sum.inl 1, (5 / 216)), (Sum.inl 31, (-5 / 18))]

def nodeValue350 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 6, (5 / 432)), (Sum.inl 123, (5 / 9)), (Sum.inl 1, (-5 / 144))]

def nodeValue351 : Sparse Master := [(Sum.inl 0, (25 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 6, (5 / 288)), (Sum.inl 2, (-25 / 144)), (Sum.inl 51, (5 / 6)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-5 / 27)), (Sum.inl 52, (-5 / 18)), (Sum.inl 12, (-5 / 18)), (Sum.inl 4, (-5 / 18)), (Sum.inl 1, (5 / 144))]

def nodeValue352 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (25 / 864)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 52, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue353 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (5 / 216)), (Sum.inl 6, (-5 / 864)), (Sum.inl 2, (5 / 108)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 52, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-25 / 432))]

def nodeValue354 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 64, (5 / 9)), (Sum.inl 1, (-5 / 144))]

def nodeValue355 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (5 / 144)), (Sum.inl 51, (5 / 9)), (Sum.inl 1, (-5 / 144))]

def nodeValue356 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (-5 / 54)), (Sum.inl 264, (5 / 18)), (Sum.inl 266, (5 / 18)), (Sum.inl 63, (5 / 9)), (Sum.inl 64, (5 / 18)), (Sum.inl 65, (5 / 9)), (Sum.inl 33, (5 / 18)), (Sum.inl 68, (5 / 18)), (Sum.inl 2, (25 / 432)), (Sum.inl 35, (-5 / 54)), (Sum.inl 125, (5 / 18)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 196, (5 / 18)), (Sum.inl 23, (5 / 9)), (Sum.inl 54, (5 / 9)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 54)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-25 / 864))]

def nodeValue357 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 63, (5 / 18)), (Sum.inl 65, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-25 / 864)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-20 / 27)), (Sum.inl 13, (-5 / 9)), (Sum.inl 23, (5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 18)), (Sum.inl 26, (-10 / 27)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 96))]

def nodeValue358 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (-5 / 72)), (Sum.inl 63, (5 / 18)), (Sum.inl 64, (5 / 9)), (Sum.inl 33, (5 / 6)), (Sum.inl 2, (5 / 864)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-5 / 9)), (Sum.inl 13, (-5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 27)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (-35 / 432))]

def nodeValue359 : Sparse Master := [(Sum.inl 0, (1 / 48)), (Sum.inl 5, (5 / 216)), (Sum.inl 64, (5 / 18)), (Sum.inl 33, (5 / 18)), (Sum.inl 66, (5 / 18)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-25 / 864)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 27)), (Sum.inl 3, (-25 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 24, (5 / 18)), (Sum.inl 55, (5 / 6)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 9)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (145 / 864))]

def nodeValue360 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 5, (-5 / 72)), (Sum.inl 2, (35 / 288)), (Sum.inl 35, (-5 / 18)), (Sum.inl 3, (-10 / 9)), (Sum.inl 13, (-5 / 27)), (Sum.inl 55, (5 / 6)), (Sum.inl 12, (-5 / 18)), (Sum.inl 26, (-5 / 9)), (Sum.inl 4, (-5 / 9)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (25 / 288))]

def nodeValue361 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (-5 / 72)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 55, (-5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-25 / 288))]

def nodeValue362 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 64, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-5 / 96)), (Sum.inl 3, (5 / 54)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 144))]

def nodeValue363 : Sparse Master := [(Sum.inl 0, (25 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 63, (5 / 9)), (Sum.inl 64, (5 / 9)), (Sum.inl 65, (5 / 18)), (Sum.inl 33, (5 / 9)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-5 / 864)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 23, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 25, (5 / 9)), (Sum.inl 26, (-10 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 144))]

def nodeValue364 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 63, (-5 / 18)), (Sum.inl 65, (-5 / 18)), (Sum.inl 2, (-5 / 216)), (Sum.inl 23, (-5 / 18)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-25 / 432))]

def nodeValue365 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 63, (-5 / 18)), (Sum.inl 64, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-5 / 108)), (Sum.inl 25, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 108))]

def nodeValue366 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 63, (5 / 9)), (Sum.inl 2, (65 / 432)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-5 / 216))]

def nodeValue367 : Sparse Master := [(Sum.inl 0, (7 / 432)), (Sum.inl 66, (-5 / 18)), (Sum.inl 2, (5 / 432)), (Sum.inl 24, (-5 / 18)), (Sum.inl 55, (-5 / 9)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (5 / 72))]

def nodeValue368 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 35, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 55, (-5 / 18)), (Sum.inl 26, (5 / 27)), (Sum.inl 4, (5 / 27)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 864))]

def nodeValue369 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 2, (-5 / 144)), (Sum.inl 55, (5 / 9)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-5 / 72))]

def nodeValue370 : Sparse Master := [(Sum.inl 0, (25 / 432)), (Sum.inl 5, (-5 / 216)), (Sum.inl 2, (-5 / 108)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-25 / 432))]

def nodeValue371 : Sparse Master := [(Sum.inl 0, (35 / 864)), (Sum.inl 5, (-5 / 216)), (Sum.inl 2, (5 / 108)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-35 / 54)), (Sum.inl 55, (5 / 18)), (Sum.inl 26, (-10 / 27)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (205 / 864))]

def nodeValue372 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (5 / 54)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 216))]

def nodeValue373 : Sparse Master := [(Sum.inl 0, (11 / 864)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-5 / 108)), (Sum.inl 3, (-5 / 18)), (Sum.inl 13, (-25 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (5 / 96))]

def nodeValue374 : Sparse Master := [(Sum.inl 0, (1 / 108)), (Sum.inl 2, (5 / 144)), (Sum.inl 13, (5 / 27)), (Sum.inl 1, (5 / 144))]

def nodeValue375 : Sparse Master := []

def nodeValue376 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 2, (-5 / 288)), (Sum.inl 3, (-25 / 54)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (55 / 216))]

def nodeValue377 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 2, (-5 / 96)), (Sum.inl 3, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (-35 / 864))]

def nodeValue378 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 2, (-35 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue379 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 2, (5 / 24))]

def nodeValue380 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 65, (5 / 18)), (Sum.inl 33, (5 / 9)), (Sum.inl 67, (-5 / 54)), (Sum.inl 34, (-10 / 27)), (Sum.inl 2, (5 / 432)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-65 / 54)), (Sum.inl 13, (-5 / 9)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-10 / 27)), (Sum.inl 26, (-5 / 9)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (5 / 48))]

def nodeValue381 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 65, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-35 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 54, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-55 / 864))]

def nodeValue382 : Sparse Master := [(Sum.inl 0, (7 / 432)), (Sum.inl 33, (5 / 9)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-35 / 864)), (Sum.inl 3, (-10 / 9)), (Sum.inl 13, (-35 / 54)), (Sum.inl 12, (-5 / 9)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (155 / 864))]

def nodeValue383 : Sparse Master := [(Sum.inl 0, (1 / 72)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-5 / 864)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-5 / 864))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3202 : Sparse Master := [(Sum.inr 3202, (1 / 1))]

def nodeValue3203 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 5, (-1 / 72)), (Sum.inl 6, (1 / 432)), (Sum.inl 2, (-1 / 432)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 18)), (Sum.inl 3, (4 / 27)), (Sum.inl 13, (1 / 6)), (Sum.inl 52, (1 / 27)), (Sum.inl 54, (-1 / 18)), (Sum.inl 12, (2 / 27)), (Sum.inl 1, (-13 / 864))]

def nodeValue3204 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (1 / 288)), (Sum.inl 2, (-7 / 864)), (Sum.inl 35, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 18)), (Sum.inl 13, (1 / 27)), (Sum.inl 52, (1 / 54)), (Sum.inl 56, (-1 / 18)), (Sum.inl 26, (1 / 54)), (Sum.inl 4, (1 / 54)), (Sum.inl 1, (-17 / 864))]

def nodeValue3205 : Sparse Master := [(Sum.inl 0, (-7 / 720)), (Sum.inl 5, (-1 / 54)), (Sum.inl 6, (1 / 216)), (Sum.inl 2, (1 / 72)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 13, (1 / 54)), (Sum.inl 54, (-1 / 18)), (Sum.inl 26, (1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3206 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (5 / 864)), (Sum.inl 7, (-1 / 54)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 54, (1 / 18)), (Sum.inl 1, (11 / 864))]

def nodeValue3207 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 5, (1 / 54)), (Sum.inl 2, (-1 / 108)), (Sum.inl 8, (-1 / 54)), (Sum.inl 56, (1 / 18)), (Sum.inl 1, (-7 / 432))]

def nodeValue3209 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 432)), (Sum.inl 2, (5 / 216)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (2 / 27)), (Sum.inl 52, (1 / 27)), (Sum.inl 12, (1 / 54)), (Sum.inl 1, (7 / 288))]

def nodeValue3210 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 216)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 288)), (Sum.inl 35, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 18)), (Sum.inl 52, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (1 / 108))]

def nodeValue3211 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 6, (1 / 864)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 52, (-1 / 54)), (Sum.inl 1, (1 / 288))]

def nodeValue3212 : Sparse Master := []

def nodeValue3213 : Sparse Master := []

def nodeValue3214 : Sparse Master := []

def nodeValue3215 : Sparse Master := []

def nodeValue3216 : Sparse Master := []

def nodeValue3217 : Sparse Master := [(Sum.inr 3217, (1 / 1))]

def nodeValue3221 : Sparse Master := [(Sum.inr 3221, (1 / 1))]

def nodeValue3222 : Sparse Master := [(Sum.inr 3222, (1 / 1))]

def nodeValue3223 : Sparse Master := [(Sum.inl 0, (-13 / 2160)), (Sum.inl 2, (-1 / 864)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (5 / 864))]

def nodeValue3224 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 2, (1 / 72)), (Sum.inl 13, (2 / 27)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-1 / 72))]

def nodeValue3225 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (1 / 54)), (Sum.inl 3, (1 / 27)), (Sum.inl 13, (1 / 27)), (Sum.inl 1, (11 / 432))]

def nodeValue3226 : Sparse Master := [(Sum.inl 0, (-13 / 2160)), (Sum.inl 2, (-1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (2 / 27)), (Sum.inl 12, (1 / 54)), (Sum.inl 1, (-23 / 432))]

def nodeValue3227 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 2, (1 / 216)), (Sum.inl 3, (-1 / 54)), (Sum.inl 13, (-1 / 54)), (Sum.inl 1, (1 / 864))]

def nodeValue3228 : Sparse Master := []

def nodeValue3229 : Sparse Master := []

def nodeValue3230 : Sparse Master := []

def nodeValue3231 : Sparse Master := []

def nodeValue3232 : Sparse Master := [(Sum.inr 3232, (1 / 1))]

def nodeValue3233 : Sparse Master := [(Sum.inr 3233, (1 / 1))]

def nodeValue3234 : Sparse Master := [(Sum.inr 3234, (1 / 1))]

def nodeValue3235 : Sparse Master := [(Sum.inr 3235, (1 / 1))]

def nodeValue3236 : Sparse Master := [(Sum.inr 3236, (1 / 1))]

def nodeValue3237 : Sparse Master := [(Sum.inr 3237, (1 / 1))]

def nodeValue3238 : Sparse Master := [(Sum.inr 3238, (1 / 1))]

def nodeValue3239 : Sparse Master := [(Sum.inr 3239, (1 / 1))]

def nodeValue3240 : Sparse Master := [(Sum.inr 3240, (1 / 1))]

def nodeValue3241 : Sparse Master := [(Sum.inr 3241, (1 / 1))]

def nodeValue3242 : Sparse Master := [(Sum.inr 3242, (1 / 1))]

def nodeValue3243 : Sparse Master := [(Sum.inr 3243, (1 / 1))]

def nodeValue3244 : Sparse Master := [(Sum.inr 3244, (1 / 1))]

def nodeValue3245 : Sparse Master := [(Sum.inr 3245, (1 / 1))]

def nodeValue3246 : Sparse Master := [(Sum.inr 3246, (1 / 1))]

def nodeValue3247 : Sparse Master := [(Sum.inr 3247, (1 / 1))]

def nodeValue3248 : Sparse Master := [(Sum.inr 3248, (1 / 1))]

def nodeValue3249 : Sparse Master := [(Sum.inr 3249, (1 / 1))]

def nodeValue3250 : Sparse Master := [(Sum.inr 3250, (1 / 1))]

def nodeValue3251 : Sparse Master := [(Sum.inr 3251, (1 / 1))]

def nodeValue3252 : Sparse Master := [(Sum.inr 3252, (1 / 1))]

def nodeValue3253 : Sparse Master := [(Sum.inr 3253, (1 / 1))]

def nodeValue3254 : Sparse Master := [(Sum.inr 3254, (1 / 1))]

def nodeValue3255 : Sparse Master := [(Sum.inr 3255, (1 / 1))]

def nodeValue3256 : Sparse Master := [(Sum.inr 3256, (1 / 1))]

def nodeValue3257 : Sparse Master := [(Sum.inr 3257, (1 / 1))]

def nodeValue3258 : Sparse Master := [(Sum.inr 3258, (1 / 1))]

def nodeValue3259 : Sparse Master := [(Sum.inr 3259, (1 / 1))]

def nodeValue3260 : Sparse Master := [(Sum.inr 3260, (1 / 1))]

def nodeValue3261 : Sparse Master := [(Sum.inr 3261, (1 / 1))]

def nodeValue3262 : Sparse Master := [(Sum.inr 3262, (1 / 1))]

def nodeValue3263 : Sparse Master := [(Sum.inr 3263, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3264 : Sparse Master := [(Sum.inr 3264, (1 / 1))]

def nodeValue3265 : Sparse Master := [(Sum.inr 3265, (1 / 1))]

def nodeValue3266 : Sparse Master := [(Sum.inr 3266, (1 / 1))]

def nodeValue3267 : Sparse Master := [(Sum.inr 3267, (1 / 1))]

def nodeValue3268 : Sparse Master := [(Sum.inr 3268, (1 / 1))]

def nodeValue3269 : Sparse Master := [(Sum.inr 3269, (1 / 1))]

def nodeValue3270 : Sparse Master := [(Sum.inr 3270, (1 / 1))]

def nodeValue3271 : Sparse Master := [(Sum.inr 3271, (1 / 1))]

def nodeValue3272 : Sparse Master := [(Sum.inr 3272, (1 / 1))]

def nodeValue3273 : Sparse Master := [(Sum.inr 3273, (1 / 1))]

def nodeValue3274 : Sparse Master := [(Sum.inr 3274, (1 / 1))]

def nodeValue3275 : Sparse Master := [(Sum.inr 3275, (1 / 1))]

def nodeValue3276 : Sparse Master := [(Sum.inr 3276, (1 / 1))]

def nodeValue3277 : Sparse Master := [(Sum.inr 3277, (1 / 1))]

def nodeValue3278 : Sparse Master := [(Sum.inr 3278, (1 / 1))]

def nodeValue3279 : Sparse Master := [(Sum.inr 3279, (1 / 1))]

def nodeValue3280 : Sparse Master := [(Sum.inr 3280, (1 / 1))]

def nodeValue3281 : Sparse Master := [(Sum.inr 3281, (1 / 1))]

def nodeValue3282 : Sparse Master := [(Sum.inr 3282, (1 / 1))]

def nodeValue3283 : Sparse Master := [(Sum.inr 3283, (1 / 1))]

def nodeValue3284 : Sparse Master := [(Sum.inr 3284, (1 / 1))]

def nodeValue3285 : Sparse Master := [(Sum.inr 3285, (1 / 1))]

def nodeValue3286 : Sparse Master := [(Sum.inr 3286, (1 / 1))]

def nodeValue3287 : Sparse Master := [(Sum.inr 3287, (1 / 1))]

def nodeValue3288 : Sparse Master := [(Sum.inr 3288, (1 / 1))]

def nodeValue3289 : Sparse Master := [(Sum.inr 3289, (1 / 1))]

def nodeValue3290 : Sparse Master := [(Sum.inr 3290, (1 / 1))]

def nodeValue3291 : Sparse Master := [(Sum.inr 3291, (1 / 1))]

def nodeValue3292 : Sparse Master := [(Sum.inr 3292, (1 / 1))]

def nodeValue3293 : Sparse Master := [(Sum.inr 3293, (1 / 1))]

def nodeValue3294 : Sparse Master := [(Sum.inr 3294, (1 / 1))]

def nodeValue3295 : Sparse Master := [(Sum.inr 3295, (1 / 1))]

def nodeValue3296 : Sparse Master := [(Sum.inr 3296, (1 / 1))]

def nodeValue3297 : Sparse Master := [(Sum.inr 3297, (1 / 1))]

def nodeValue3298 : Sparse Master := [(Sum.inr 3298, (1 / 1))]

def nodeValue3299 : Sparse Master := [(Sum.inr 3299, (1 / 1))]

def nodeValue3300 : Sparse Master := [(Sum.inr 3300, (1 / 1))]

def nodeValue3301 : Sparse Master := [(Sum.inr 3301, (1 / 1))]

def nodeValue3302 : Sparse Master := [(Sum.inr 3302, (1 / 1))]

def nodeValue3303 : Sparse Master := [(Sum.inr 3303, (1 / 1))]

def nodeValue3304 : Sparse Master := [(Sum.inr 3304, (1 / 1))]

def nodeValue3305 : Sparse Master := [(Sum.inr 3305, (1 / 1))]

def nodeValue3306 : Sparse Master := [(Sum.inr 3306, (1 / 1))]

def nodeValue3307 : Sparse Master := [(Sum.inr 3307, (1 / 1))]

def nodeValue3308 : Sparse Master := [(Sum.inr 3308, (1 / 1))]

def nodeValue3309 : Sparse Master := [(Sum.inr 3309, (1 / 1))]

def nodeValue3310 : Sparse Master := [(Sum.inr 3310, (1 / 1))]

def nodeValue3311 : Sparse Master := [(Sum.inr 3311, (1 / 1))]

def nodeValue3312 : Sparse Master := [(Sum.inr 3312, (1 / 1))]

def nodeValue3313 : Sparse Master := [(Sum.inr 3313, (1 / 1))]

def nodeValue3315 : Sparse Master := [(Sum.inr 3315, (1 / 1))]

def nodeValue3318 : Sparse Master := [(Sum.inr 3318, (1 / 1))]

def nodeValue3325 : Sparse Master := [(Sum.inr 3325, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3334 : Sparse Master := [(Sum.inr 3334, (1 / 1))]

def nodeValue3335 : Sparse Master := [(Sum.inr 3335, (1 / 1))]

def nodeValue3336 : Sparse Master := [(Sum.inr 3336, (1 / 1))]

def nodeValue3337 : Sparse Master := [(Sum.inr 3337, (1 / 1))]

def nodeValue3339 : Sparse Master := []

def nodeValue3340 : Sparse Master := [(Sum.inr 3340, (1 / 1))]

def nodeValue3341 : Sparse Master := [(Sum.inr 3341, (1 / 1))]

def nodeValue3342 : Sparse Master := [(Sum.inr 3342, (1 / 1))]

def nodeValue3343 : Sparse Master := [(Sum.inr 3343, (1 / 1))]

def nodeValue3344 : Sparse Master := [(Sum.inr 3344, (1 / 1))]

def nodeValue3345 : Sparse Master := [(Sum.inr 3345, (1 / 1))]

def nodeValue3346 : Sparse Master := [(Sum.inr 3346, (1 / 1))]

def nodeValue3347 : Sparse Master := [(Sum.inr 3347, (1 / 1))]

def nodeValue3348 : Sparse Master := [(Sum.inr 3348, (1 / 1))]

def nodeValue3349 : Sparse Master := [(Sum.inr 3349, (1 / 1))]

def nodeValue3350 : Sparse Master := [(Sum.inr 3350, (1 / 1))]

def nodeValue3351 : Sparse Master := []

def nodeValue3352 : Sparse Master := [(Sum.inr 3352, (1 / 1))]

def nodeValue3353 : Sparse Master := [(Sum.inr 3353, (1 / 1))]

def nodeValue3354 : Sparse Master := [(Sum.inr 3354, (1 / 1))]

def nodeValue3355 : Sparse Master := [(Sum.inr 3355, (1 / 1))]

def nodeValue3357 : Sparse Master := [(Sum.inr 3357, (1 / 1))]

def nodeValue3358 : Sparse Master := [(Sum.inr 3358, (1 / 1))]

def nodeValue3360 : Sparse Master := [(Sum.inr 3360, (1 / 1))]

def nodeValue3365 : Sparse Master := [(Sum.inr 3365, (1 / 1))]

def nodeValue3368 : Sparse Master := [(Sum.inr 3368, (1 / 1))]

def nodeValue3370 : Sparse Master := [(Sum.inr 3370, (1 / 1))]

def nodeValue3372 : Sparse Master := [(Sum.inr 3372, (1 / 1))]

def nodeValue3373 : Sparse Master := [(Sum.inr 3373, (1 / 1))]

def nodeValue3374 : Sparse Master := [(Sum.inr 3374, (1 / 1))]

def nodeValue3375 : Sparse Master := [(Sum.inr 3375, (1 / 1))]

def nodeValue3376 : Sparse Master := [(Sum.inr 3376, (1 / 1))]

def nodeValue3377 : Sparse Master := [(Sum.inr 3377, (1 / 1))]

def nodeValue3378 : Sparse Master := [(Sum.inr 3378, (1 / 1))]

def nodeValue3379 : Sparse Master := [(Sum.inr 3379, (1 / 1))]

def nodeValue3380 : Sparse Master := [(Sum.inr 3380, (1 / 1))]

def nodeValue3382 : Sparse Master := [(Sum.inr 3382, (1 / 1))]

def nodeValue3383 : Sparse Master := [(Sum.inr 3383, (1 / 1))]

def nodeValue3384 : Sparse Master := [(Sum.inr 3384, (1 / 1))]

def nodeValue3385 : Sparse Master := [(Sum.inr 3385, (1 / 1))]

def nodeValue3386 : Sparse Master := [(Sum.inr 3386, (1 / 1))]

def nodeValue3387 : Sparse Master := [(Sum.inr 3387, (1 / 1))]

def nodeValue3388 : Sparse Master := [(Sum.inr 3388, (1 / 1))]

def nodeValue3389 : Sparse Master := [(Sum.inr 3389, (1 / 1))]

def nodeValue3390 : Sparse Master := [(Sum.inr 3390, (1 / 1))]

def nodeValue3391 : Sparse Master := [(Sum.inr 3391, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3392 : Sparse Master := [(Sum.inr 3392, (1 / 1))]

def nodeValue3393 : Sparse Master := [(Sum.inr 3393, (1 / 1))]

def nodeValue3394 : Sparse Master := [(Sum.inr 3394, (1 / 1))]

def nodeValue3395 : Sparse Master := [(Sum.inr 3395, (1 / 1))]

def nodeValue3396 : Sparse Master := [(Sum.inr 3396, (1 / 1))]

def nodeValue3397 : Sparse Master := [(Sum.inr 3397, (1 / 1))]

def nodeValue3398 : Sparse Master := [(Sum.inr 3398, (1 / 1))]

def nodeValue3399 : Sparse Master := [(Sum.inr 3399, (1 / 1))]

def nodeValue3400 : Sparse Master := [(Sum.inr 3400, (1 / 1))]

def nodeValue3401 : Sparse Master := [(Sum.inr 3401, (1 / 1))]

def nodeValue3402 : Sparse Master := [(Sum.inr 3402, (1 / 1))]

def nodeValue3403 : Sparse Master := []

def nodeValue3404 : Sparse Master := [(Sum.inr 3404, (1 / 1))]

def nodeValue3405 : Sparse Master := []

def nodeValue3406 : Sparse Master := [(Sum.inr 3406, (1 / 1))]

def nodeValue3407 : Sparse Master := [(Sum.inr 3407, (1 / 1))]

def nodeValue3408 : Sparse Master := [(Sum.inr 3408, (1 / 1))]

def nodeValue3409 : Sparse Master := []

def nodeValue3410 : Sparse Master := [(Sum.inr 3410, (1 / 1))]

def nodeValue3411 : Sparse Master := [(Sum.inr 3411, (1 / 1))]

def nodeValue3412 : Sparse Master := [(Sum.inr 3412, (1 / 1))]

def nodeValue3413 : Sparse Master := [(Sum.inr 3413, (1 / 1))]

def nodeValue3414 : Sparse Master := [(Sum.inr 3414, (1 / 1))]

def nodeValue3415 : Sparse Master := [(Sum.inr 3415, (1 / 1))]

def nodeValue3416 : Sparse Master := [(Sum.inr 3416, (1 / 1))]

def nodeValue3417 : Sparse Master := [(Sum.inr 3417, (1 / 1))]

def nodeValue3418 : Sparse Master := [(Sum.inr 3418, (1 / 1))]

def nodeValue3419 : Sparse Master := [(Sum.inr 3419, (1 / 1))]

def nodeValue3420 : Sparse Master := [(Sum.inr 3420, (1 / 1))]

def nodeValue3421 : Sparse Master := [(Sum.inr 3421, (1 / 1))]

def nodeValue3422 : Sparse Master := [(Sum.inr 3422, (1 / 1))]

def nodeValue3423 : Sparse Master := [(Sum.inr 3423, (1 / 1))]

def nodeValue3425 : Sparse Master := [(Sum.inr 3425, (1 / 1))]

def nodeValue3426 : Sparse Master := [(Sum.inr 3426, (1 / 1))]

def nodeValue3429 : Sparse Master := [(Sum.inr 3429, (1 / 1))]

def nodeValue3430 : Sparse Master := [(Sum.inr 3430, (1 / 1))]

def nodeValue3431 : Sparse Master := [(Sum.inr 3431, (1 / 1))]

def nodeValue3432 : Sparse Master := [(Sum.inr 3432, (1 / 1))]

def nodeValue3433 : Sparse Master := [(Sum.inr 3433, (1 / 1))]

def nodeValue3434 : Sparse Master := [(Sum.inr 3434, (1 / 1))]

def nodeValue3436 : Sparse Master := [(Sum.inr 3436, (1 / 1))]

def nodeValue3437 : Sparse Master := [(Sum.inr 3437, (1 / 1))]

def nodeValue3439 : Sparse Master := []

def nodeValue3440 : Sparse Master := [(Sum.inr 3440, (1 / 1))]

def nodeValue3441 : Sparse Master := [(Sum.inr 3441, (1 / 1))]

def nodeValue3442 : Sparse Master := [(Sum.inr 3442, (1 / 1))]

def nodeValue3443 : Sparse Master := [(Sum.inr 3443, (1 / 1))]

def nodeValue3444 : Sparse Master := [(Sum.inr 3444, (1 / 1))]

def nodeValue3445 : Sparse Master := [(Sum.inr 3445, (1 / 1))]

def nodeValue3446 : Sparse Master := [(Sum.inr 3446, (1 / 1))]

def nodeValue3447 : Sparse Master := [(Sum.inr 3447, (1 / 1))]

def nodeValue3448 : Sparse Master := [(Sum.inr 3448, (1 / 1))]

def nodeValue3449 : Sparse Master := [(Sum.inr 3449, (1 / 1))]

def nodeValue3450 : Sparse Master := [(Sum.inr 3450, (1 / 1))]

def nodeValue3451 : Sparse Master := [(Sum.inr 3451, (1 / 1))]

def nodeValue3452 : Sparse Master := [(Sum.inr 3452, (1 / 1))]

def nodeValue3453 : Sparse Master := [(Sum.inr 3453, (1 / 1))]

def nodeValue3454 : Sparse Master := [(Sum.inr 3454, (1 / 1))]

def nodeValue3455 : Sparse Master := [(Sum.inr 3455, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3456 : Sparse Master := [(Sum.inr 3456, (1 / 1))]

def nodeValue3457 : Sparse Master := [(Sum.inr 3457, (1 / 1))]

def nodeValue3458 : Sparse Master := [(Sum.inr 3458, (1 / 1))]

def nodeValue3459 : Sparse Master := [(Sum.inr 3459, (1 / 1))]

def nodeValue3460 : Sparse Master := [(Sum.inr 3460, (1 / 1))]

def nodeValue3461 : Sparse Master := [(Sum.inr 3461, (1 / 1))]

def nodeValue3462 : Sparse Master := [(Sum.inr 3462, (1 / 1))]

def nodeValue3463 : Sparse Master := [(Sum.inr 3463, (1 / 1))]

def nodeValue3464 : Sparse Master := [(Sum.inr 3464, (1 / 1))]

def nodeValue3465 : Sparse Master := [(Sum.inr 3465, (1 / 1))]

def nodeValue3466 : Sparse Master := [(Sum.inr 3466, (1 / 1))]

def nodeValue3467 : Sparse Master := [(Sum.inr 3467, (1 / 1))]

def nodeValue3468 : Sparse Master := [(Sum.inr 3468, (1 / 1))]

def nodeValue3469 : Sparse Master := []

def nodeValue3470 : Sparse Master := []

def nodeValue3471 : Sparse Master := [(Sum.inr 3471, (1 / 1))]

def nodeValue3472 : Sparse Master := [(Sum.inr 3472, (1 / 1))]

def nodeValue3473 : Sparse Master := [(Sum.inr 3473, (1 / 1))]

def nodeValue3474 : Sparse Master := [(Sum.inr 3474, (1 / 1))]

def nodeValue3475 : Sparse Master := [(Sum.inr 3475, (1 / 1))]

def nodeValue3476 : Sparse Master := [(Sum.inr 3476, (1 / 1))]

def nodeValue3477 : Sparse Master := [(Sum.inr 3477, (1 / 1))]

def nodeValue3478 : Sparse Master := [(Sum.inr 3478, (1 / 1))]

def nodeValue3479 : Sparse Master := [(Sum.inr 3479, (1 / 1))]

def nodeValue3480 : Sparse Master := [(Sum.inr 3480, (1 / 1))]

def nodeValue3481 : Sparse Master := [(Sum.inr 3481, (1 / 1))]

def nodeValue3482 : Sparse Master := [(Sum.inr 3482, (1 / 1))]

def nodeValue3483 : Sparse Master := []

def nodeValue3484 : Sparse Master := []

def nodeValue3485 : Sparse Master := []

def nodeValue3486 : Sparse Master := [(Sum.inr 3486, (1 / 1))]

def nodeValue3487 : Sparse Master := [(Sum.inr 3487, (1 / 1))]

def nodeValue3488 : Sparse Master := [(Sum.inr 3488, (1 / 1))]

def nodeValue3489 : Sparse Master := []

def nodeValue3490 : Sparse Master := [(Sum.inr 3490, (1 / 1))]

def nodeValue3491 : Sparse Master := [(Sum.inr 3491, (1 / 1))]

def nodeValue3492 : Sparse Master := []

def nodeValue3493 : Sparse Master := [(Sum.inr 3493, (1 / 1))]

def nodeValue3494 : Sparse Master := []

def nodeValue3495 : Sparse Master := [(Sum.inr 3495, (1 / 1))]

def nodeValue3496 : Sparse Master := [(Sum.inr 3496, (1 / 1))]

def nodeValue3497 : Sparse Master := [(Sum.inr 3497, (1 / 1))]

def nodeValue3498 : Sparse Master := [(Sum.inr 3498, (1 / 1))]

def nodeValue3499 : Sparse Master := [(Sum.inr 3499, (1 / 1))]

def nodeValue3500 : Sparse Master := [(Sum.inr 3500, (1 / 1))]

def nodeValue3501 : Sparse Master := [(Sum.inr 3501, (1 / 1))]

def nodeValue3502 : Sparse Master := [(Sum.inr 3502, (1 / 1))]

def nodeValue3503 : Sparse Master := [(Sum.inr 3503, (1 / 1))]

def nodeValue3504 : Sparse Master := [(Sum.inr 3504, (1 / 1))]

def nodeValue3505 : Sparse Master := [(Sum.inr 3505, (1 / 1))]

def nodeValue3506 : Sparse Master := [(Sum.inr 3506, (1 / 1))]

def nodeValue3507 : Sparse Master := [(Sum.inr 3507, (1 / 1))]

def nodeValue3508 : Sparse Master := [(Sum.inr 3508, (1 / 1))]

def nodeValue3509 : Sparse Master := [(Sum.inr 3509, (1 / 1))]

def nodeValue3510 : Sparse Master := [(Sum.inr 3510, (1 / 1))]

def nodeValue3511 : Sparse Master := [(Sum.inr 3511, (1 / 1))]

def nodeValue3512 : Sparse Master := [(Sum.inr 3512, (1 / 1))]

def nodeValue3513 : Sparse Master := []

def nodeValue3514 : Sparse Master := [(Sum.inr 3514, (1 / 1))]

def nodeValue3515 : Sparse Master := []

def nodeValue3516 : Sparse Master := [(Sum.inr 3516, (1 / 1))]

def nodeValue3517 : Sparse Master := [(Sum.inr 3517, (1 / 1))]

def nodeValue3518 : Sparse Master := [(Sum.inr 3518, (1 / 1))]

def nodeValue3519 : Sparse Master := [(Sum.inr 3519, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3520 : Sparse Master := []

def nodeValue3521 : Sparse Master := [(Sum.inr 3521, (1 / 1))]

def nodeValue3522 : Sparse Master := [(Sum.inr 3522, (1 / 1))]

def nodeValue3523 : Sparse Master := [(Sum.inr 3523, (1 / 1))]

def nodeValue3524 : Sparse Master := [(Sum.inr 3524, (1 / 1))]

def nodeValue3525 : Sparse Master := []

def nodeValue3526 : Sparse Master := [(Sum.inr 3526, (1 / 1))]

def nodeValue3527 : Sparse Master := [(Sum.inr 3527, (1 / 1))]

def nodeValue3528 : Sparse Master := [(Sum.inr 3528, (1 / 1))]

def nodeValue3529 : Sparse Master := [(Sum.inr 3529, (1 / 1))]

def nodeValue3530 : Sparse Master := [(Sum.inr 3530, (1 / 1))]

def nodeValue3531 : Sparse Master := []

def nodeValue3532 : Sparse Master := [(Sum.inr 3532, (1 / 1))]

def nodeValue3533 : Sparse Master := [(Sum.inr 3533, (1 / 1))]

def nodeValue3534 : Sparse Master := [(Sum.inr 3534, (1 / 1))]

def nodeValue3535 : Sparse Master := [(Sum.inr 3535, (1 / 1))]

def nodeValue3536 : Sparse Master := [(Sum.inr 3536, (1 / 1))]

def nodeValue3537 : Sparse Master := [(Sum.inr 3537, (1 / 1))]

def nodeValue3538 : Sparse Master := [(Sum.inr 3538, (1 / 1))]

def nodeValue3539 : Sparse Master := [(Sum.inr 3539, (1 / 1))]

def nodeValue3540 : Sparse Master := [(Sum.inr 3540, (1 / 1))]

def nodeValue3541 : Sparse Master := [(Sum.inr 3541, (1 / 1))]

def nodeValue3542 : Sparse Master := [(Sum.inr 3542, (1 / 1))]

def nodeValue3543 : Sparse Master := [(Sum.inr 3543, (1 / 1))]

def nodeValue3544 : Sparse Master := [(Sum.inr 3544, (1 / 1))]

def nodeValue3545 : Sparse Master := [(Sum.inr 3545, (1 / 1))]

def nodeValue3546 : Sparse Master := []

def nodeValue3547 : Sparse Master := []

def nodeValue3548 : Sparse Master := [(Sum.inr 3548, (1 / 1))]

def nodeValue3549 : Sparse Master := [(Sum.inr 3549, (1 / 1))]

def nodeValue3550 : Sparse Master := [(Sum.inr 3550, (1 / 1))]

def nodeValue3551 : Sparse Master := [(Sum.inr 3551, (1 / 1))]

def nodeValue3552 : Sparse Master := [(Sum.inr 3552, (1 / 1))]

def nodeValue3553 : Sparse Master := [(Sum.inr 3553, (1 / 1))]

def nodeValue3554 : Sparse Master := [(Sum.inr 3554, (1 / 1))]

def nodeValue3555 : Sparse Master := [(Sum.inr 3555, (1 / 1))]

def nodeValue3556 : Sparse Master := [(Sum.inr 3556, (1 / 1))]

def nodeValue3557 : Sparse Master := [(Sum.inr 3557, (1 / 1))]

def nodeValue3558 : Sparse Master := [(Sum.inr 3558, (1 / 1))]

def nodeValue3559 : Sparse Master := [(Sum.inr 3559, (1 / 1))]

def nodeValue3560 : Sparse Master := [(Sum.inr 3560, (1 / 1))]

def nodeValue3561 : Sparse Master := [(Sum.inr 3561, (1 / 1))]

def nodeValue3562 : Sparse Master := [(Sum.inr 3562, (1 / 1))]

def nodeValue3563 : Sparse Master := [(Sum.inr 3563, (1 / 1))]

def nodeValue3564 : Sparse Master := [(Sum.inr 3564, (1 / 1))]

def nodeValue3565 : Sparse Master := [(Sum.inr 3565, (1 / 1))]

def nodeValue3566 : Sparse Master := [(Sum.inr 3566, (1 / 1))]

def nodeValue3567 : Sparse Master := [(Sum.inr 3567, (1 / 1))]

def nodeValue3568 : Sparse Master := [(Sum.inr 3568, (1 / 1))]

def nodeValue3569 : Sparse Master := [(Sum.inr 3569, (1 / 1))]

def nodeValue3570 : Sparse Master := [(Sum.inr 3570, (1 / 1))]

def nodeValue3571 : Sparse Master := [(Sum.inr 3571, (1 / 1))]

def nodeValue3572 : Sparse Master := [(Sum.inr 3572, (1 / 1))]

def nodeValue3573 : Sparse Master := [(Sum.inr 3573, (1 / 1))]

def nodeValue3574 : Sparse Master := [(Sum.inr 3574, (1 / 1))]

def nodeValue3575 : Sparse Master := [(Sum.inr 3575, (1 / 1))]

def nodeValue3576 : Sparse Master := [(Sum.inr 3576, (1 / 1))]

def nodeValue3577 : Sparse Master := [(Sum.inr 3577, (1 / 1))]

def nodeValue3578 : Sparse Master := [(Sum.inr 3578, (1 / 1))]

def nodeValue3579 : Sparse Master := [(Sum.inr 3579, (1 / 1))]

def nodeValue3580 : Sparse Master := [(Sum.inr 3580, (1 / 1))]

def nodeValue3581 : Sparse Master := [(Sum.inr 3581, (1 / 1))]

def nodeValue3582 : Sparse Master := [(Sum.inr 3582, (1 / 1))]

def nodeValue3583 : Sparse Master := [(Sum.inr 3583, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3584 : Sparse Master := [(Sum.inr 3584, (1 / 1))]

def nodeValue3585 : Sparse Master := [(Sum.inr 3585, (1 / 1))]

def nodeValue3586 : Sparse Master := [(Sum.inr 3586, (1 / 1))]

def nodeValue3587 : Sparse Master := [(Sum.inr 3587, (1 / 1))]

def nodeValue3588 : Sparse Master := [(Sum.inr 3588, (1 / 1))]

def nodeValue3589 : Sparse Master := [(Sum.inr 3589, (1 / 1))]

def nodeValue3590 : Sparse Master := [(Sum.inr 3590, (1 / 1))]

def nodeValue3591 : Sparse Master := [(Sum.inr 3591, (1 / 1))]

def nodeValue3592 : Sparse Master := [(Sum.inr 3592, (1 / 1))]

def nodeValue3595 : Sparse Master := [(Sum.inr 3595, (1 / 1))]

def nodeValue3596 : Sparse Master := [(Sum.inr 3596, (1 / 1))]

def nodeValue3597 : Sparse Master := [(Sum.inr 3597, (1 / 1))]

def nodeValue3599 : Sparse Master := [(Sum.inr 3599, (1 / 1))]

def nodeValue3600 : Sparse Master := [(Sum.inr 3600, (1 / 1))]

def nodeValue3602 : Sparse Master := [(Sum.inr 3602, (1 / 1))]

def nodeValue3603 : Sparse Master := [(Sum.inr 3603, (1 / 1))]

def nodeValue3605 : Sparse Master := [(Sum.inr 3605, (1 / 1))]

def nodeValue3606 : Sparse Master := [(Sum.inr 3606, (1 / 1))]

def nodeValue3607 : Sparse Master := [(Sum.inr 3607, (1 / 1))]

def nodeValue3608 : Sparse Master := [(Sum.inr 3608, (1 / 1))]

def nodeValue3610 : Sparse Master := [(Sum.inr 3610, (1 / 1))]

def nodeValue3611 : Sparse Master := [(Sum.inr 3611, (1 / 1))]

def nodeValue3612 : Sparse Master := [(Sum.inr 3612, (1 / 1))]

def nodeValue3613 : Sparse Master := [(Sum.inr 3613, (1 / 1))]

def nodeValue3614 : Sparse Master := [(Sum.inr 3614, (1 / 1))]

def nodeValue3615 : Sparse Master := [(Sum.inr 3615, (1 / 1))]

def nodeValue3616 : Sparse Master := [(Sum.inr 3616, (1 / 1))]

def nodeValue3617 : Sparse Master := [(Sum.inr 3617, (1 / 1))]

def nodeValue3618 : Sparse Master := []

def nodeValue3619 : Sparse Master := [(Sum.inr 3619, (1 / 1))]

def nodeValue3620 : Sparse Master := [(Sum.inr 3620, (1 / 1))]

def nodeValue3621 : Sparse Master := [(Sum.inr 3621, (1 / 1))]

def nodeValue3622 : Sparse Master := [(Sum.inr 3622, (1 / 1))]

def nodeValue3623 : Sparse Master := [(Sum.inr 3623, (1 / 1))]

def nodeValue3624 : Sparse Master := [(Sum.inr 3624, (1 / 1))]

def nodeValue3625 : Sparse Master := [(Sum.inr 3625, (1 / 1))]

def nodeValue3626 : Sparse Master := [(Sum.inr 3626, (1 / 1))]

def nodeValue3627 : Sparse Master := [(Sum.inr 3627, (1 / 1))]

def nodeValue3628 : Sparse Master := []

def nodeValue3629 : Sparse Master := []

def nodeValue3630 : Sparse Master := [(Sum.inr 3630, (1 / 1))]

def nodeValue3631 : Sparse Master := [(Sum.inr 3631, (1 / 1))]

def nodeValue3632 : Sparse Master := [(Sum.inr 3632, (1 / 1))]

def nodeValue3633 : Sparse Master := [(Sum.inr 3633, (1 / 1))]

def nodeValue3634 : Sparse Master := [(Sum.inr 3634, (1 / 1))]

def nodeValue3635 : Sparse Master := []

def nodeValue3636 : Sparse Master := []

def nodeValue3646 : Sparse Master := [(Sum.inr 3646, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3648 : Sparse Master := [(Sum.inr 3648, (1 / 1))]

def nodeValue3650 : Sparse Master := []

def nodeValue3653 : Sparse Master := [(Sum.inr 3653, (1 / 1))]

def nodeValue3654 : Sparse Master := []

def nodeValue3658 : Sparse Master := [(Sum.inr 3658, (1 / 1))]

def nodeValue3659 : Sparse Master := [(Sum.inr 3659, (1 / 1))]

def nodeValue3660 : Sparse Master := [(Sum.inr 3660, (1 / 1))]

def nodeValue3666 : Sparse Master := [(Sum.inr 3666, (1 / 1))]

def nodeValue3668 : Sparse Master := [(Sum.inr 3668, (1 / 1))]

def nodeValue3670 : Sparse Master := [(Sum.inr 3670, (1 / 1))]

def nodeValue3671 : Sparse Master := [(Sum.inr 3671, (1 / 1))]

def nodeValue3672 : Sparse Master := [(Sum.inr 3672, (1 / 1))]

def nodeValue3673 : Sparse Master := [(Sum.inr 3673, (1 / 1))]

def nodeValue3674 : Sparse Master := [(Sum.inr 3674, (1 / 1))]

def nodeValue3675 : Sparse Master := [(Sum.inr 3675, (1 / 1))]

def nodeValue3676 : Sparse Master := [(Sum.inr 3676, (1 / 1))]

def nodeValue3677 : Sparse Master := [(Sum.inr 3677, (1 / 1))]

def nodeValue3678 : Sparse Master := [(Sum.inr 3678, (1 / 1))]

def nodeValue3679 : Sparse Master := [(Sum.inr 3679, (1 / 1))]

def nodeValue3680 : Sparse Master := [(Sum.inr 3680, (1 / 1))]

def nodeValue3681 : Sparse Master := [(Sum.inr 3681, (1 / 1))]

def nodeValue3683 : Sparse Master := [(Sum.inr 3683, (1 / 1))]

def nodeValue3685 : Sparse Master := [(Sum.inr 3685, (1 / 1))]

def nodeValue3686 : Sparse Master := [(Sum.inr 3686, (1 / 1))]

def nodeValue3687 : Sparse Master := [(Sum.inr 3687, (1 / 1))]

def nodeValue3688 : Sparse Master := [(Sum.inr 3688, (1 / 1))]

def nodeValue3689 : Sparse Master := [(Sum.inr 3689, (1 / 1))]

def nodeValue3690 : Sparse Master := [(Sum.inr 3690, (1 / 1))]

def nodeValue3691 : Sparse Master := [(Sum.inr 3691, (1 / 1))]

def nodeValue3692 : Sparse Master := [(Sum.inr 3692, (1 / 1))]

def nodeValue3693 : Sparse Master := [(Sum.inr 3693, (1 / 1))]

def nodeValue3694 : Sparse Master := [(Sum.inr 3694, (1 / 1))]

def nodeValue3695 : Sparse Master := [(Sum.inr 3695, (1 / 1))]

def nodeValue3696 : Sparse Master := [(Sum.inr 3696, (1 / 1))]

def nodeValue3697 : Sparse Master := [(Sum.inr 3697, (1 / 1))]

def nodeValue3698 : Sparse Master := [(Sum.inr 3698, (1 / 1))]

def nodeValue3699 : Sparse Master := [(Sum.inr 3699, (1 / 1))]

def nodeValue3700 : Sparse Master := [(Sum.inr 3700, (1 / 1))]

def nodeValue3701 : Sparse Master := [(Sum.inr 3701, (1 / 1))]

def nodeValue3702 : Sparse Master := [(Sum.inr 3702, (1 / 1))]

def nodeValue3703 : Sparse Master := [(Sum.inr 3703, (1 / 1))]

def nodeValue3705 : Sparse Master := [(Sum.inr 3705, (1 / 1))]

def nodeValue3706 : Sparse Master := [(Sum.inr 3706, (1 / 1))]

def nodeValue3707 : Sparse Master := []

def nodeValue3708 : Sparse Master := [(Sum.inr 3708, (1 / 1))]

def nodeValue3709 : Sparse Master := [(Sum.inr 3709, (1 / 1))]

def nodeValue3710 : Sparse Master := [(Sum.inr 3710, (1 / 1))]

def nodeValue3711 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (1 / 72)), (Sum.inl 68, (-1 / 18)), (Sum.inl 2, (-1 / 96)), (Sum.inl 7, (1 / 27)), (Sum.inl 124, (-1 / 18)), (Sum.inl 125, (-1 / 18)), (Sum.inl 126, (-1 / 18)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (2 / 27)), (Sum.inl 197, (-1 / 18)), (Sum.inl 23, (-1 / 9)), (Sum.inl 24, (-1 / 9)), (Sum.inl 55, (-1 / 9)), (Sum.inl 12, (1 / 54)), (Sum.inl 4, (1 / 54)), (Sum.inl 1, (-1 / 432))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3712 : Sparse Master := [(Sum.inr 3712, (1 / 1))]

def nodeValue3713 : Sparse Master := [(Sum.inr 3713, (1 / 1))]

def nodeValue3714 : Sparse Master := [(Sum.inr 3714, (1 / 1))]

def nodeValue3715 : Sparse Master := [(Sum.inr 3715, (1 / 1))]

def nodeValue3716 : Sparse Master := [(Sum.inr 3716, (1 / 1))]

def nodeValue3717 : Sparse Master := [(Sum.inr 3717, (1 / 1))]

def nodeValue3718 : Sparse Master := [(Sum.inr 3718, (1 / 1))]

def nodeValue3719 : Sparse Master := [(Sum.inr 3719, (1 / 1))]

def nodeValue3720 : Sparse Master := [(Sum.inr 3720, (1 / 1))]

def nodeValue3721 : Sparse Master := [(Sum.inr 3721, (1 / 1))]

def nodeValue3722 : Sparse Master := [(Sum.inr 3722, (1 / 1))]

def nodeValue3723 : Sparse Master := [(Sum.inr 3723, (1 / 1))]

def nodeValue3724 : Sparse Master := [(Sum.inr 3724, (1 / 1))]

def nodeValue3725 : Sparse Master := [(Sum.inr 3725, (1 / 1))]

def nodeValue3726 : Sparse Master := [(Sum.inl 0, (-19 / 4320)), (Sum.inl 5, (-1 / 108)), (Sum.inl 2, (1 / 48)), (Sum.inl 7, (1 / 18)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (1 / 6)), (Sum.inl 23, (-1 / 18)), (Sum.inl 24, (-1 / 9)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (2 / 27)), (Sum.inl 27, (1 / 36)), (Sum.inl 1, (-31 / 864))]

def nodeValue3727 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 5, (-1 / 108)), (Sum.inl 2, (1 / 144)), (Sum.inl 7, (1 / 27)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (7 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 23, (-1 / 9)), (Sum.inl 54, (-1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 18)), (Sum.inl 25, (-1 / 18)), (Sum.inl 26, (1 / 54)), (Sum.inl 4, (1 / 54)), (Sum.inl 27, (1 / 36)), (Sum.inl 1, (-5 / 864))]

def nodeValue3728 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 2, (-1 / 288)), (Sum.inl 23, (1 / 18)), (Sum.inl 24, (1 / 18)), (Sum.inl 55, (1 / 18)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (1 / 72))]

def nodeValue3729 : Sparse Master := [(Sum.inr 3729, (1 / 1))]

def nodeValue3730 : Sparse Master := [(Sum.inr 3730, (1 / 1))]

def nodeValue3731 : Sparse Master := [(Sum.inr 3731, (1 / 1))]

def nodeValue3732 : Sparse Master := [(Sum.inr 3732, (1 / 1))]

def nodeValue3733 : Sparse Master := [(Sum.inr 3733, (1 / 1))]

def nodeValue3734 : Sparse Master := [(Sum.inl 0, (-1 / 160)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (-11 / 864)), (Sum.inl 7, (1 / 54)), (Sum.inl 3, (7 / 54)), (Sum.inl 23, (-1 / 6)), (Sum.inl 54, (-1 / 9)), (Sum.inl 12, (1 / 9)), (Sum.inl 25, (-1 / 6)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (-1 / 36))]

def nodeValue3735 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 72)), (Sum.inl 2, (-1 / 108)), (Sum.inl 7, (1 / 18)), (Sum.inl 3, (4 / 27)), (Sum.inl 23, (-1 / 18)), (Sum.inl 24, (-1 / 9)), (Sum.inl 12, (1 / 27)), (Sum.inl 4, (2 / 27)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (-1 / 432))]

def nodeValue3736 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 23, (1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-1 / 36))]

def nodeValue3737 : Sparse Master := [(Sum.inl 0, (-13 / 1440)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 24, (1 / 18)), (Sum.inl 4, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (7 / 288))]

def nodeValue3738 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 432)), (Sum.inl 3, (-1 / 54)), (Sum.inl 23, (1 / 18)), (Sum.inl 54, (1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 25, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-19 / 864))]

def nodeValue3739 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 432)), (Sum.inl 7, (-1 / 54)), (Sum.inl 3, (-1 / 27)), (Sum.inl 23, (1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-1 / 36))]

def nodeValue3740 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 23, (-1 / 9)), (Sum.inl 27, (-1 / 36)), (Sum.inl 1, (-1 / 18))]

def nodeValue3741 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 24, (-1 / 9)), (Sum.inl 27, (-1 / 36)), (Sum.inl 1, (1 / 72))]

def nodeValue3743 : Sparse Master := [(Sum.inr 3743, (1 / 1))]

def nodeValue3744 : Sparse Master := [(Sum.inr 3744, (1 / 1))]

def nodeValue3746 : Sparse Master := [(Sum.inr 3746, (1 / 1))]

def nodeValue3748 : Sparse Master := [(Sum.inr 3748, (1 / 1))]

def nodeValue3749 : Sparse Master := [(Sum.inr 3749, (1 / 1))]

def nodeValue3750 : Sparse Master := [(Sum.inr 3750, (1 / 1))]

def nodeValue3751 : Sparse Master := [(Sum.inr 3751, (1 / 1))]

def nodeValue3752 : Sparse Master := [(Sum.inr 3752, (1 / 1))]

def nodeValue3753 : Sparse Master := [(Sum.inr 3753, (1 / 1))]

def nodeValue3754 : Sparse Master := [(Sum.inr 3754, (1 / 1))]

def nodeValue3755 : Sparse Master := [(Sum.inr 3755, (1 / 1))]

def nodeValue3756 : Sparse Master := [(Sum.inr 3756, (1 / 1))]

def nodeValue3757 : Sparse Master := [(Sum.inr 3757, (1 / 1))]

def nodeValue3758 : Sparse Master := [(Sum.inr 3758, (1 / 1))]

def nodeValue3759 : Sparse Master := [(Sum.inr 3759, (1 / 1))]

def nodeValue3760 : Sparse Master := [(Sum.inr 3760, (1 / 1))]

def nodeValue3761 : Sparse Master := [(Sum.inr 3761, (1 / 1))]

def nodeValue3762 : Sparse Master := [(Sum.inr 3762, (1 / 1))]

def nodeValue3763 : Sparse Master := [(Sum.inr 3763, (1 / 1))]

def nodeValue3764 : Sparse Master := [(Sum.inr 3764, (1 / 1))]

def nodeValue3765 : Sparse Master := []

def nodeValue3766 : Sparse Master := []

def nodeValue3767 : Sparse Master := [(Sum.inr 3767, (1 / 1))]

def nodeValue3768 : Sparse Master := [(Sum.inr 3768, (1 / 1))]

def nodeValue3769 : Sparse Master := [(Sum.inr 3769, (1 / 1))]

def nodeValue3770 : Sparse Master := [(Sum.inr 3770, (1 / 1))]

def nodeValue3771 : Sparse Master := [(Sum.inr 3771, (1 / 1))]

def nodeValue3772 : Sparse Master := [(Sum.inr 3772, (1 / 1))]

def nodeValue3773 : Sparse Master := [(Sum.inr 3773, (1 / 1))]

def nodeValue3774 : Sparse Master := []

def nodeValue3775 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3776 : Sparse Master := [(Sum.inr 3776, (1 / 1))]

def nodeValue3778 : Sparse Master := [(Sum.inr 3778, (1 / 1))]

def nodeValue3779 : Sparse Master := [(Sum.inr 3779, (1 / 1))]

def nodeValue3780 : Sparse Master := [(Sum.inr 3780, (1 / 1))]

def nodeValue3781 : Sparse Master := [(Sum.inr 3781, (1 / 1))]

def nodeValue3782 : Sparse Master := [(Sum.inr 3782, (1 / 1))]

def nodeValue3783 : Sparse Master := [(Sum.inr 3783, (1 / 1))]

def nodeValue3784 : Sparse Master := [(Sum.inr 3784, (1 / 1))]

def nodeValue3785 : Sparse Master := [(Sum.inr 3785, (1 / 1))]

def nodeValue3786 : Sparse Master := [(Sum.inr 3786, (1 / 1))]

def nodeValue3787 : Sparse Master := [(Sum.inr 3787, (1 / 1))]

def nodeValue3788 : Sparse Master := [(Sum.inr 3788, (1 / 1))]

def nodeValue3789 : Sparse Master := [(Sum.inr 3789, (1 / 1))]

def nodeValue3790 : Sparse Master := [(Sum.inr 3790, (1 / 1))]

def nodeValue3791 : Sparse Master := [(Sum.inr 3791, (1 / 1))]

def nodeValue3792 : Sparse Master := [(Sum.inr 3792, (1 / 1))]

def nodeValue3793 : Sparse Master := []

def nodeValue3794 : Sparse Master := [(Sum.inr 3794, (1 / 1))]

def nodeValue3795 : Sparse Master := [(Sum.inr 3795, (1 / 1))]

def nodeValue3796 : Sparse Master := [(Sum.inr 3796, (1 / 1))]

def nodeValue3797 : Sparse Master := [(Sum.inr 3797, (1 / 1))]

def nodeValue3798 : Sparse Master := []

def nodeValue3799 : Sparse Master := [(Sum.inr 3799, (1 / 1))]

def nodeValue3800 : Sparse Master := [(Sum.inr 3800, (1 / 1))]

def nodeValue3801 : Sparse Master := [(Sum.inr 3801, (1 / 1))]

def nodeValue3802 : Sparse Master := [(Sum.inr 3802, (1 / 1))]

def nodeValue3803 : Sparse Master := [(Sum.inr 3803, (1 / 1))]

def nodeValue3804 : Sparse Master := [(Sum.inr 3804, (1 / 1))]

def nodeValue3805 : Sparse Master := [(Sum.inr 3805, (1 / 1))]

def nodeValue3806 : Sparse Master := []

def nodeValue3807 : Sparse Master := []

def nodeValue3808 : Sparse Master := []

def nodeValue3809 : Sparse Master := [(Sum.inr 3809, (1 / 1))]

def nodeValue3810 : Sparse Master := [(Sum.inr 3810, (1 / 1))]

def nodeValue3811 : Sparse Master := [(Sum.inr 3811, (1 / 1))]

def nodeValue3812 : Sparse Master := [(Sum.inr 3812, (1 / 1))]

def nodeValue3813 : Sparse Master := [(Sum.inr 3813, (1 / 1))]

def nodeValue3814 : Sparse Master := [(Sum.inr 3814, (1 / 1))]

def nodeValue3815 : Sparse Master := [(Sum.inr 3815, (1 / 1))]

def nodeValue3816 : Sparse Master := []

def nodeValue3817 : Sparse Master := []

def nodeValue3818 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 5, (-1 / 108)), (Sum.inl 2, (1 / 48)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 51, (-1 / 9)), (Sum.inl 3, (1 / 9)), (Sum.inl 23, (-1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 55, (-1 / 9)), (Sum.inl 12, (1 / 18)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (1 / 36)), (Sum.inl 1, (-1 / 36))]

def nodeValue3819 : Sparse Master := [(Sum.inr 3819, (1 / 1))]

def nodeValue3820 : Sparse Master := [(Sum.inl 0, (-43 / 4320)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (1 / 27)), (Sum.inl 3, (2 / 27)), (Sum.inl 23, (-1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-11 / 216))]

def nodeValue3821 : Sparse Master := [(Sum.inl 0, (-23 / 2160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 96)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (1 / 216))]

def nodeValue3822 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 216)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (1 / 27)), (Sum.inl 13, (1 / 18)), (Sum.inl 23, (-1 / 18)), (Sum.inl 54, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 25, (-1 / 18)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-31 / 864))]

def nodeValue3823 : Sparse Master := [(Sum.inl 0, (-41 / 4320)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 54)), (Sum.inl 7, (1 / 27)), (Sum.inl 3, (4 / 27)), (Sum.inl 23, (-1 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-1 / 48))]

def nodeValue3824 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 5, (-1 / 216)), (Sum.inl 8, (-1 / 54)), (Sum.inl 24, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (1 / 108))]

def nodeValue3825 : Sparse Master := [(Sum.inr 3825, (1 / 1))]

def nodeValue3826 : Sparse Master := [(Sum.inr 3826, (1 / 1))]

def nodeValue3827 : Sparse Master := [(Sum.inr 3827, (1 / 1))]

def nodeValue3828 : Sparse Master := [(Sum.inr 3828, (1 / 1))]

def nodeValue3829 : Sparse Master := [(Sum.inl 0, (-5 / 864)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (7 / 864)), (Sum.inl 35, (1 / 54)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (1 / 18)), (Sum.inl 52, (1 / 54)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 54)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-1 / 288))]

def nodeValue3830 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 432)), (Sum.inl 35, (1 / 54)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (7 / 54)), (Sum.inl 13, (1 / 18)), (Sum.inl 52, (1 / 54)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 18)), (Sum.inl 26, (1 / 54)), (Sum.inl 4, (1 / 18)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-13 / 864))]

def nodeValue3831 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (1 / 432)), (Sum.inl 51, (1 / 18)), (Sum.inl 3, (-1 / 27)), (Sum.inl 55, (1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (7 / 432))]

def nodeValue3832 : Sparse Master := [(Sum.inr 3832, (1 / 1))]

def nodeValue3833 : Sparse Master := [(Sum.inr 3833, (1 / 1))]

def nodeValue3834 : Sparse Master := [(Sum.inr 3834, (1 / 1))]

def nodeValue3835 : Sparse Master := [(Sum.inr 3835, (1 / 1))]

def nodeValue3836 : Sparse Master := [(Sum.inr 3836, (1 / 1))]

def nodeValue3837 : Sparse Master := [(Sum.inr 3837, (1 / 1))]

def nodeValue3838 : Sparse Master := [(Sum.inr 3838, (1 / 1))]

def nodeValue3839 : Sparse Master := [(Sum.inr 3839, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue384 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 34, (5 / 54)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (10 / 27)), (Sum.inl 12, (5 / 27)), (Sum.inl 1, (-25 / 288))]

def nodeValue385 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 2, (5 / 36)), (Sum.inl 13, (-10 / 27)), (Sum.inl 1, (-5 / 72))]

def nodeValue386 : Sparse Master := [(Sum.inl 0, (13 / 864)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (-5 / 216)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 26, (5 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue387 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 2, (5 / 108)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-5 / 432))]

def nodeValue388 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 2, (-5 / 108)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue389 : Sparse Master := []

def nodeValue390 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (-5 / 54))]

def nodeValue391 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 1, (-5 / 54))]

def nodeValue392 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (-5 / 72)), (Sum.inl 65, (5 / 18)), (Sum.inl 66, (5 / 9)), (Sum.inl 67, (-5 / 18)), (Sum.inl 34, (-20 / 27)), (Sum.inl 2, (25 / 216)), (Sum.inl 3, (-10 / 9)), (Sum.inl 13, (-5 / 27)), (Sum.inl 26, (-10 / 9)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (5 / 144))]

def nodeValue393 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 65, (-5 / 18)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (-25 / 864)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 26, (5 / 27)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 864))]

def nodeValue394 : Sparse Master := [(Sum.inl 0, (1 / 432)), (Sum.inl 33, (5 / 18)), (Sum.inl 34, (-5 / 27)), (Sum.inl 2, (-65 / 864)), (Sum.inl 3, (-65 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-35 / 54)), (Sum.inl 4, (-5 / 9)), (Sum.inl 1, (25 / 96))]

def nodeValue395 : Sparse Master := [(Sum.inl 0, (5 / 864)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-5 / 288)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (5 / 108))]

def nodeValue396 : Sparse Master := []

def nodeValue397 : Sparse Master := [(Sum.inl 0, (1 / 48)), (Sum.inl 2, (-25 / 864)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-55 / 864))]

def nodeValue398 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (5 / 216)), (Sum.inl 61, (-5 / 18)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (-5 / 108)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (5 / 54)), (Sum.inl 55, (-5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 108))]

def nodeValue399 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 66, (-5 / 18)), (Sum.inl 67, (5 / 54)), (Sum.inl 34, (5 / 27)), (Sum.inl 2, (5 / 216)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 18)), (Sum.inl 4, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (35 / 432))]

def nodeValue400 : Sparse Master := [(Sum.inl 0, (11 / 864)), (Sum.inl 34, (5 / 54)), (Sum.inl 2, (25 / 864)), (Sum.inl 3, (10 / 27)), (Sum.inl 26, (5 / 18)), (Sum.inl 4, (5 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue401 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 2, (25 / 864)), (Sum.inl 3, (5 / 18)), (Sum.inl 26, (5 / 27)), (Sum.inl 4, (5 / 27))]

def nodeValue402 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 2, (-5 / 144)), (Sum.inl 3, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue403 : Sparse Master := [(Sum.inl 0, (47 / 864)), (Sum.inl 2, (55 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 1, (-5 / 216))]

def nodeValue404 : Sparse Master := [(Sum.inl 0, (1 / 18)), (Sum.inl 2, (-5 / 72)), (Sum.inl 1, (-5 / 72))]

def nodeValue405 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (-5 / 54))]

def nodeValue406 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 34, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue407 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 2, (5 / 24))]

def nodeValue408 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 65, (5 / 9)), (Sum.inl 2, (-5 / 72)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-5 / 72))]

def nodeValue409 : Sparse Master := [(Sum.inl 0, (17 / 864)), (Sum.inl 33, (-5 / 18)), (Sum.inl 34, (5 / 54)), (Sum.inl 2, (5 / 108)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-25 / 864))]

def nodeValue410 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 33, (5 / 9)), (Sum.inl 2, (-5 / 432)), (Sum.inl 1, (-35 / 432))]

def nodeValue411 : Sparse Master := [(Sum.inl 0, (11 / 864)), (Sum.inl 2, (5 / 288)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 27)), (Sum.inl 12, (5 / 18)), (Sum.inl 1, (5 / 36))]

def nodeValue412 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 2, (-5 / 216)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 12, (-5 / 27)), (Sum.inl 1, (35 / 432))]

def nodeValue413 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 66, (5 / 9)), (Sum.inl 2, (5 / 108)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (5 / 72))]

def nodeValue414 : Sparse Master := [(Sum.inl 0, (13 / 432)), (Sum.inl 2, (5 / 144)), (Sum.inl 3, (-5 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue415 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 2, (-5 / 72)), (Sum.inl 26, (5 / 9)), (Sum.inl 1, (-5 / 48))]

def nodeValue416 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (-5 / 27)), (Sum.inl 1, (55 / 216))]

def nodeValue417 : Sparse Master := []

def nodeValue418 : Sparse Master := []

def nodeValue419 : Sparse Master := []

def nodeValue420 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 2, (-5 / 144)), (Sum.inl 3, (5 / 9)), (Sum.inl 1, (5 / 72))]

def nodeValue421 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 34, (5 / 9)), (Sum.inl 2, (-5 / 48)), (Sum.inl 1, (-5 / 48))]

def nodeValue422 : Sparse Master := []

def nodeValue423 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 5, (-5 / 108)), (Sum.inl 68, (5 / 18)), (Sum.inl 2, (5 / 144)), (Sum.inl 124, (5 / 18)), (Sum.inl 126, (5 / 9)), (Sum.inl 51, (5 / 9)), (Sum.inl 1, (5 / 432)), (Sum.inl 236, (5 / 18)), (Sum.inl 31, (5 / 18))]

def nodeValue424 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (-5 / 72)), (Sum.inl 68, (5 / 18)), (Sum.inl 2, (5 / 96)), (Sum.inl 7, (-5 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 18)), (Sum.inl 126, (5 / 18)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 197, (5 / 18)), (Sum.inl 23, (5 / 9)), (Sum.inl 24, (5 / 9)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue426 : Sparse Master := [(Sum.inl 0, (5 / 288)), (Sum.inl 5, (-5 / 54)), (Sum.inl 68, (5 / 18)), (Sum.inl 2, (5 / 96)), (Sum.inl 486, (-5 / 9)), (Sum.inl 487, (-5 / 9)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-5 / 27)), (Sum.inl 194, (-5 / 9)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (35 / 432)), (Sum.inl 31, (5 / 18))]

def nodeValue427 : Sparse Master := [(Sum.inl 0, (1 / 48)), (Sum.inl 5, (-5 / 54)), (Sum.inl 263, (-5 / 9)), (Sum.inl 68, (5 / 18)), (Sum.inl 2, (25 / 288)), (Sum.inl 487, (-5 / 9)), (Sum.inl 3, (-5 / 54)), (Sum.inl 195, (-5 / 9)), (Sum.inl 23, (5 / 9)), (Sum.inl 54, (5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 25, (5 / 18)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 288))]

def nodeValue428 : Sparse Master := [(Sum.inl 0, (7 / 432)), (Sum.inl 2, (-25 / 432)), (Sum.inl 194, (-5 / 9)), (Sum.inl 23, (5 / 9)), (Sum.inl 24, (10 / 9)), (Sum.inl 55, (5 / 9)), (Sum.inl 27, (-5 / 18)), (Sum.inl 1, (5 / 36)), (Sum.inl 30, (5 / 9))]

def nodeValue429 : Sparse Master := [(Sum.inl 0, (5 / 108)), (Sum.inl 5, (5 / 54)), (Sum.inl 2, (-5 / 72)), (Sum.inl 7, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 3, (-5 / 18)), (Sum.inl 23, (5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 27, (-5 / 24))]

def nodeValue430 : Sparse Master := [(Sum.inl 0, (1 / 48)), (Sum.inl 5, (5 / 72)), (Sum.inl 2, (-115 / 864)), (Sum.inl 7, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-5 / 27)), (Sum.inl 24, (5 / 18)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (-5 / 18)), (Sum.inl 1, (155 / 864)), (Sum.inl 30, (5 / 18)), (Sum.inl 31, (5 / 18))]

def nodeValue431 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 108)), (Sum.inl 2, (-5 / 48)), (Sum.inl 7, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-5 / 9)), (Sum.inl 23, (5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 55, (5 / 9)), (Sum.inl 12, (-5 / 18)), (Sum.inl 4, (-5 / 27)), (Sum.inl 27, (-5 / 36)), (Sum.inl 1, (5 / 36))]

def nodeValue432 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 2, (5 / 288)), (Sum.inl 23, (-5 / 18)), (Sum.inl 24, (-5 / 18)), (Sum.inl 55, (-5 / 18)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (-5 / 72))]

def nodeValue433 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 24, (-5 / 18)), (Sum.inl 27, (5 / 18)), (Sum.inl 1, (5 / 216)), (Sum.inl 30, (-5 / 18))]

def nodeValue434 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 59, (5 / 18)), (Sum.inl 61, (5 / 18)), (Sum.inl 33, (5 / 9)), (Sum.inl 2, (-5 / 432)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-25 / 54)), (Sum.inl 194, (-5 / 9)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-10 / 27)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (25 / 432))]

def nodeValue435 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 2, (5 / 216)), (Sum.inl 194, (5 / 9)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-5 / 108))]

def nodeValue436 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-5 / 108)), (Sum.inl 2, (25 / 432)), (Sum.inl 51, (5 / 9)), (Sum.inl 3, (-5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 4, (-5 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 31, (5 / 9))]

def nodeValue437 : Sparse Master := [(Sum.inl 0, (35 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (5 / 864)), (Sum.inl 51, (-5 / 18)), (Sum.inl 1, (-5 / 144)), (Sum.inl 31, (-5 / 18))]

def nodeValue438 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (-5 / 432)), (Sum.inl 51, (-5 / 18)), (Sum.inl 3, (5 / 27)), (Sum.inl 55, (-5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-35 / 432))]

def nodeValue439 : Sparse Master := [(Sum.inl 0, (7 / 288)), (Sum.inl 5, (-5 / 54)), (Sum.inl 68, (5 / 18)), (Sum.inl 2, (55 / 864)), (Sum.inl 7, (-5 / 27)), (Sum.inl 124, (5 / 18)), (Sum.inl 125, (5 / 9)), (Sum.inl 3, (-10 / 27)), (Sum.inl 196, (5 / 18)), (Sum.inl 23, (5 / 9)), (Sum.inl 54, (5 / 9)), (Sum.inl 12, (-5 / 27)), (Sum.inl 25, (5 / 18)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (55 / 432))]

def nodeValue440 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 63, (5 / 9)), (Sum.inl 65, (5 / 9)), (Sum.inl 2, (5 / 432)), (Sum.inl 23, (5 / 9)), (Sum.inl 24, (5 / 9)), (Sum.inl 55, (10 / 9)), (Sum.inl 1, (-5 / 216))]

def nodeValue441 : Sparse Master := [(Sum.inl 0, (11 / 288)), (Sum.inl 5, (5 / 108)), (Sum.inl 2, (-5 / 144)), (Sum.inl 7, (-5 / 27)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 23, (5 / 9)), (Sum.inl 54, (5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 18)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (-5 / 36)), (Sum.inl 1, (25 / 864))]

def nodeValue442 : Sparse Master := [(Sum.inl 0, (19 / 864)), (Sum.inl 5, (5 / 108)), (Sum.inl 2, (-5 / 48)), (Sum.inl 7, (-5 / 18)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-5 / 6)), (Sum.inl 23, (5 / 18)), (Sum.inl 24, (5 / 9)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (-5 / 36)), (Sum.inl 1, (155 / 864))]

def nodeValue443 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (5 / 216)), (Sum.inl 63, (5 / 18)), (Sum.inl 64, (5 / 18)), (Sum.inl 65, (5 / 18)), (Sum.inl 33, (5 / 9)), (Sum.inl 2, (-5 / 288)), (Sum.inl 7, (-5 / 54)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-5 / 9)), (Sum.inl 23, (5 / 9)), (Sum.inl 54, (5 / 9)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 18)), (Sum.inl 25, (5 / 9)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 432))]

def nodeValue444 : Sparse Master := [(Sum.inl 0, (1 / 27)), (Sum.inl 5, (-5 / 72)), (Sum.inl 65, (5 / 18)), (Sum.inl 33, (5 / 9)), (Sum.inl 2, (5 / 48)), (Sum.inl 3, (-5 / 9)), (Sum.inl 195, (-5 / 9)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 9)), (Sum.inl 12, (-5 / 27)), (Sum.inl 25, (5 / 9)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 18)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (-5 / 144)), (Sum.inl 31, (5 / 18))]

def nodeValue445 : Sparse Master := [(Sum.inl 0, (1 / 32)), (Sum.inl 5, (-5 / 72)), (Sum.inl 2, (55 / 864)), (Sum.inl 7, (-5 / 54)), (Sum.inl 3, (-35 / 54)), (Sum.inl 23, (5 / 6)), (Sum.inl 54, (5 / 9)), (Sum.inl 12, (-5 / 9)), (Sum.inl 25, (5 / 6)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (5 / 36))]

def nodeValue446 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (-5 / 432)), (Sum.inl 3, (5 / 54)), (Sum.inl 23, (-5 / 18)), (Sum.inl 54, (-5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 25, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (95 / 864))]

def nodeValue447 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 216)), (Sum.inl 195, (5 / 9)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 144))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3840 : Sparse Master := [(Sum.inr 3840, (1 / 1))]

def nodeValue3841 : Sparse Master := [(Sum.inr 3841, (1 / 1))]

def nodeValue3842 : Sparse Master := [(Sum.inr 3842, (1 / 1))]

def nodeValue3843 : Sparse Master := [(Sum.inr 3843, (1 / 1))]

def nodeValue3844 : Sparse Master := []

def nodeValue3845 : Sparse Master := [(Sum.inr 3845, (1 / 1))]

def nodeValue3846 : Sparse Master := [(Sum.inr 3846, (1 / 1))]

def nodeValue3847 : Sparse Master := [(Sum.inl 0, (-1 / 540)), (Sum.inl 2, (7 / 864)), (Sum.inl 3, (4 / 27)), (Sum.inl 13, (1 / 18)), (Sum.inl 12, (2 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-29 / 864))]

def nodeValue3848 : Sparse Master := [(Sum.inr 3848, (1 / 1))]

def nodeValue3849 : Sparse Master := [(Sum.inr 3849, (1 / 1))]

def nodeValue3850 : Sparse Master := [(Sum.inr 3850, (1 / 1))]

def nodeValue3851 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 2, (1 / 96)), (Sum.inl 3, (1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-1 / 48))]

def nodeValue3852 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 2, (-5 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue3853 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 2, (-1 / 216)), (Sum.inl 3, (-1 / 27)), (Sum.inl 12, (-1 / 27)), (Sum.inl 1, (1 / 27))]

def nodeValue3854 : Sparse Master := [(Sum.inr 3854, (1 / 1))]

def nodeValue3855 : Sparse Master := [(Sum.inl 0, (-1 / 2160)), (Sum.inl 2, (1 / 144)), (Sum.inl 3, (1 / 9)), (Sum.inl 13, (2 / 27)), (Sum.inl 1, (-1 / 36))]

def nodeValue3856 : Sparse Master := [(Sum.inl 0, (-1 / 240)), (Sum.inl 2, (-1 / 216)), (Sum.inl 3, (-1 / 27)), (Sum.inl 13, (-1 / 27)), (Sum.inl 1, (-5 / 432))]

def nodeValue3857 : Sparse Master := [(Sum.inr 3857, (1 / 1))]

def nodeValue3858 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 2, (1 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (-19 / 432))]

def nodeValue3859 : Sparse Master := []

def nodeValue3860 : Sparse Master := []

def nodeValue3861 : Sparse Master := []

def nodeValue3862 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue3863 : Sparse Master := [(Sum.inr 3863, (1 / 1))]

def nodeValue3865 : Sparse Master := [(Sum.inr 3865, (1 / 1))]

def nodeValue3866 : Sparse Master := [(Sum.inr 3866, (1 / 1))]

def nodeValue3867 : Sparse Master := [(Sum.inr 3867, (1 / 1))]

def nodeValue3868 : Sparse Master := [(Sum.inr 3868, (1 / 1))]

def nodeValue3869 : Sparse Master := [(Sum.inr 3869, (1 / 1))]

def nodeValue3870 : Sparse Master := [(Sum.inr 3870, (1 / 1))]

def nodeValue3871 : Sparse Master := [(Sum.inr 3871, (1 / 1))]

def nodeValue3872 : Sparse Master := [(Sum.inr 3872, (1 / 1))]

def nodeValue3873 : Sparse Master := [(Sum.inr 3873, (1 / 1))]

def nodeValue3874 : Sparse Master := [(Sum.inr 3874, (1 / 1))]

def nodeValue3875 : Sparse Master := [(Sum.inr 3875, (1 / 1))]

def nodeValue3876 : Sparse Master := [(Sum.inr 3876, (1 / 1))]

def nodeValue3877 : Sparse Master := [(Sum.inr 3877, (1 / 1))]

def nodeValue3878 : Sparse Master := [(Sum.inr 3878, (1 / 1))]

def nodeValue3879 : Sparse Master := [(Sum.inr 3879, (1 / 1))]

def nodeValue3880 : Sparse Master := [(Sum.inr 3880, (1 / 1))]

def nodeValue3881 : Sparse Master := [(Sum.inr 3881, (1 / 1))]

def nodeValue3882 : Sparse Master := [(Sum.inl 0, (17 / 4320)), (Sum.inl 2, (1 / 96)), (Sum.inl 3, (1 / 6)), (Sum.inl 13, (1 / 27)), (Sum.inl 12, (1 / 9)), (Sum.inl 4, (1 / 9)), (Sum.inl 1, (-1 / 12))]

def nodeValue3883 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 2, (-1 / 144)), (Sum.inl 3, (-1 / 18)), (Sum.inl 13, (-1 / 54)), (Sum.inl 12, (-1 / 27)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (1 / 36))]

def nodeValue3884 : Sparse Master := [(Sum.inr 3884, (1 / 1))]

def nodeValue3885 : Sparse Master := [(Sum.inr 3885, (1 / 1))]

def nodeValue3886 : Sparse Master := [(Sum.inr 3886, (1 / 1))]

def nodeValue3887 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 2, (1 / 432)), (Sum.inl 3, (-1 / 27)), (Sum.inl 12, (-1 / 54)), (Sum.inl 4, (-1 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue3888 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3889 : Sparse Master := [(Sum.inl 0, (-1 / 144)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-5 / 216))]

def nodeValue3890 : Sparse Master := [(Sum.inr 3890, (1 / 1))]

def nodeValue3891 : Sparse Master := [(Sum.inr 3891, (1 / 1))]

def nodeValue3892 : Sparse Master := [(Sum.inr 3892, (1 / 1))]

def nodeValue3893 : Sparse Master := [(Sum.inr 3893, (1 / 1))]

def nodeValue3894 : Sparse Master := [(Sum.inr 3894, (1 / 1))]

def nodeValue3895 : Sparse Master := [(Sum.inr 3895, (1 / 1))]

def nodeValue3896 : Sparse Master := [(Sum.inr 3896, (1 / 1))]

def nodeValue3897 : Sparse Master := [(Sum.inr 3897, (1 / 1))]

def nodeValue3898 : Sparse Master := [(Sum.inr 3898, (1 / 1))]

def nodeValue3899 : Sparse Master := [(Sum.inr 3899, (1 / 1))]

def nodeValue3900 : Sparse Master := [(Sum.inr 3900, (1 / 1))]

def nodeValue3901 : Sparse Master := [(Sum.inr 3901, (1 / 1))]

def nodeValue3902 : Sparse Master := [(Sum.inr 3902, (1 / 1))]

def nodeValue3903 : Sparse Master := [(Sum.inr 3903, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3904 : Sparse Master := []

def nodeValue3905 : Sparse Master := []

def nodeValue3906 : Sparse Master := [(Sum.inr 3906, (1 / 1))]

def nodeValue3907 : Sparse Master := [(Sum.inr 3907, (1 / 1))]

def nodeValue3908 : Sparse Master := []

def nodeValue3909 : Sparse Master := [(Sum.inr 3909, (1 / 1))]

def nodeValue3910 : Sparse Master := [(Sum.inr 3910, (1 / 1))]

def nodeValue3911 : Sparse Master := [(Sum.inl 0, (-7 / 432)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (5 / 144))]

def nodeValue3912 : Sparse Master := [(Sum.inl 0, (-1 / 108)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-1 / 36))]

def nodeValue3913 : Sparse Master := [(Sum.inr 3913, (1 / 1))]

def nodeValue3914 : Sparse Master := []

def nodeValue3915 : Sparse Master := [(Sum.inl 0, (-1 / 108)), (Sum.inl 12, (1 / 27)), (Sum.inl 1, (-1 / 36))]

def nodeValue3916 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 12, (-1 / 9)), (Sum.inl 1, (-1 / 12))]

def nodeValue3917 : Sparse Master := []

def nodeValue3920 : Sparse Master := []

def nodeValue3921 : Sparse Master := []

def nodeValue3922 : Sparse Master := [(Sum.inr 3922, (1 / 1))]

def nodeValue3923 : Sparse Master := []

def nodeValue3925 : Sparse Master := [(Sum.inl 0, (-11 / 2160)), (Sum.inl 5, (-1 / 72)), (Sum.inl 2, (1 / 48)), (Sum.inl 8, (1 / 27)), (Sum.inl 3, (1 / 27)), (Sum.inl 24, (-1 / 9)), (Sum.inl 56, (-1 / 18)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (1 / 24)), (Sum.inl 1, (-1 / 54)), (Sum.inl 30, (-1 / 18))]

def nodeValue3926 : Sparse Master := [(Sum.inl 0, (-7 / 1080)), (Sum.inl 24, (1 / 18)), (Sum.inl 27, (-1 / 18)), (Sum.inl 1, (-1 / 216)), (Sum.inl 30, (1 / 18))]

def nodeValue3927 : Sparse Master := [(Sum.inr 3927, (1 / 1))]

def nodeValue3929 : Sparse Master := [(Sum.inr 3929, (1 / 1))]

def nodeValue3930 : Sparse Master := [(Sum.inl 0, (-13 / 1080)), (Sum.inl 5, (1 / 72)), (Sum.inl 8, (1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 27, (-1 / 24)), (Sum.inl 1, (-1 / 216)), (Sum.inl 30, (-1 / 9))]

def nodeValue3931 : Sparse Master := [(Sum.inl 0, (-2 / 135)), (Sum.inl 5, (-1 / 216)), (Sum.inl 8, (-1 / 54)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (-1 / 108)), (Sum.inl 30, (1 / 18))]

def nodeValue3933 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 5, (-1 / 216)), (Sum.inl 8, (-1 / 54)), (Sum.inl 24, (1 / 18)), (Sum.inl 27, (1 / 72)), (Sum.inl 1, (1 / 108))]

def nodeValue3934 : Sparse Master := [(Sum.inl 0, (-13 / 1080)), (Sum.inl 27, (-1 / 36)), (Sum.inl 1, (-1 / 216)), (Sum.inl 30, (-1 / 9))]

def nodeValue3935 : Sparse Master := [(Sum.inr 3935, (1 / 1))]

def nodeValue3936 : Sparse Master := [(Sum.inl 0, (-1 / 240)), (Sum.inl 5, (-1 / 72)), (Sum.inl 2, (23 / 864)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (1 / 27)), (Sum.inl 24, (-1 / 18)), (Sum.inl 4, (1 / 54)), (Sum.inl 27, (1 / 18)), (Sum.inl 1, (-31 / 864)), (Sum.inl 30, (-1 / 18)), (Sum.inl 31, (-1 / 18))]

def nodeValue3937 : Sparse Master := [(Sum.inl 0, (-1 / 108)), (Sum.inl 5, (-1 / 54)), (Sum.inl 2, (1 / 72)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 18)), (Sum.inl 23, (-1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 27, (1 / 24))]

def nodeValue3938 : Sparse Master := [(Sum.inl 0, (-19 / 2160)), (Sum.inl 5, (1 / 108)), (Sum.inl 2, (-5 / 432)), (Sum.inl 51, (-1 / 9)), (Sum.inl 3, (1 / 18)), (Sum.inl 55, (-1 / 18)), (Sum.inl 12, (1 / 54)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 31, (-1 / 9))]

def nodeValue3939 : Sparse Master := [(Sum.inl 0, (-7 / 864)), (Sum.inl 5, (-1 / 216)), (Sum.inl 2, (-1 / 864)), (Sum.inl 51, (1 / 18)), (Sum.inl 1, (1 / 144)), (Sum.inl 31, (1 / 18))]

def nodeValue3940 : Sparse Master := []

def nodeValue3941 : Sparse Master := []

def nodeValue3942 : Sparse Master := [(Sum.inr 3942, (1 / 1))]

def nodeValue3944 : Sparse Master := []

def nodeValue3945 : Sparse Master := [(Sum.inr 3945, (1 / 1))]

def nodeValue3946 : Sparse Master := [(Sum.inr 3946, (1 / 1))]

def nodeValue3947 : Sparse Master := [(Sum.inr 3947, (1 / 1))]

def nodeValue3949 : Sparse Master := [(Sum.inr 3949, (1 / 1))]

def nodeValue3950 : Sparse Master := []

def nodeValue3951 : Sparse Master := []

def nodeValue3952 : Sparse Master := [(Sum.inr 3952, (1 / 1))]

def nodeValue3953 : Sparse Master := []

def nodeValue3954 : Sparse Master := [(Sum.inr 3954, (1 / 1))]

def nodeValue3955 : Sparse Master := [(Sum.inr 3955, (1 / 1))]

def nodeValue3956 : Sparse Master := []

def nodeValue3957 : Sparse Master := [(Sum.inr 3957, (1 / 1))]

def nodeValue3958 : Sparse Master := [(Sum.inr 3958, (1 / 1))]

def nodeValue3959 : Sparse Master := [(Sum.inr 3959, (1 / 1))]

def nodeValue3960 : Sparse Master := [(Sum.inr 3960, (1 / 1))]

def nodeValue3961 : Sparse Master := [(Sum.inr 3961, (1 / 1))]

def nodeValue3962 : Sparse Master := []

def nodeValue3963 : Sparse Master := [(Sum.inr 3963, (1 / 1))]

def nodeValue3964 : Sparse Master := [(Sum.inr 3964, (1 / 1))]

def nodeValue3965 : Sparse Master := [(Sum.inl 0, (-17 / 1440)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 72)), (Sum.inl 8, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-5 / 216)), (Sum.inl 30, (-1 / 18))]

def nodeValue3966 : Sparse Master := [(Sum.inl 0, (-23 / 4320)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 216)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (7 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 24, (-1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 56, (-1 / 18)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (2 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-7 / 216))]

def nodeValue3967 : Sparse Master := [(Sum.inl 0, (-23 / 2160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 96)), (Sum.inl 7, (1 / 54)), (Sum.inl 8, (1 / 54)), (Sum.inl 3, (1 / 18)), (Sum.inl 24, (-1 / 18)), (Sum.inl 4, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (1 / 216))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue3968 : Sparse Master := []

def nodeValue3969 : Sparse Master := [(Sum.inl 0, (-7 / 2160)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (23 / 864)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (2 / 27)), (Sum.inl 52, (1 / 54)), (Sum.inl 4, (1 / 18)), (Sum.inl 1, (-7 / 144)), (Sum.inl 31, (-1 / 9))]

def nodeValue3970 : Sparse Master := [(Sum.inl 0, (-7 / 720)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (1 / 96)), (Sum.inl 51, (-1 / 18)), (Sum.inl 3, (5 / 54)), (Sum.inl 13, (1 / 54)), (Sum.inl 52, (1 / 54)), (Sum.inl 12, (1 / 27)), (Sum.inl 4, (1 / 54)), (Sum.inl 1, (-1 / 216)), (Sum.inl 31, (-1 / 18))]

def nodeValue3971 : Sparse Master := []

def nodeValue3972 : Sparse Master := [(Sum.inr 3972, (1 / 1))]

def nodeValue3973 : Sparse Master := [(Sum.inr 3973, (1 / 1))]

def nodeValue3974 : Sparse Master := [(Sum.inr 3974, (1 / 1))]

def nodeValue3975 : Sparse Master := []

def nodeValue3976 : Sparse Master := []

def nodeValue3977 : Sparse Master := [(Sum.inl 0, (1 / 1080)), (Sum.inl 2, (5 / 864)), (Sum.inl 3, (2 / 27)), (Sum.inl 13, (1 / 54)), (Sum.inl 12, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-19 / 864))]

def nodeValue3978 : Sparse Master := [(Sum.inr 3978, (1 / 1))]

def nodeValue3979 : Sparse Master := []

def nodeValue3980 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 2, (11 / 864)), (Sum.inl 3, (1 / 54)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-23 / 432))]

def nodeValue3981 : Sparse Master := [(Sum.inl 0, (-11 / 720)), (Sum.inl 2, (-1 / 144)), (Sum.inl 1, (1 / 72))]

def nodeValue3982 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 2, (-5 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (7 / 864))]

def nodeValue3983 : Sparse Master := [(Sum.inr 3983, (1 / 1))]

def nodeValue3984 : Sparse Master := [(Sum.inl 0, (-49 / 4320)), (Sum.inl 2, (1 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 4, (-1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3985 : Sparse Master := []

def nodeValue3986 : Sparse Master := []

def nodeValue3987 : Sparse Master := [(Sum.inl 0, (-1 / 120)), (Sum.inl 2, (-1 / 432)), (Sum.inl 3, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3988 : Sparse Master := []

def nodeValue3989 : Sparse Master := []

def nodeValue3990 : Sparse Master := [(Sum.inl 0, (-7 / 2160)), (Sum.inl 2, (5 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 12, (1 / 27)), (Sum.inl 26, (1 / 54)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-17 / 864))]

def nodeValue3991 : Sparse Master := []

def nodeValue3992 : Sparse Master := [(Sum.inl 0, (-47 / 4320)), (Sum.inl 2, (11 / 864)), (Sum.inl 3, (1 / 54)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-23 / 432))]

def nodeValue3993 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 2, (-1 / 864)), (Sum.inl 3, (-1 / 18)), (Sum.inl 12, (-1 / 54)), (Sum.inl 26, (-1 / 54)), (Sum.inl 4, (-1 / 27)), (Sum.inl 1, (5 / 288))]

def nodeValue3994 : Sparse Master := [(Sum.inl 0, (-1 / 4320)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (2 / 27)), (Sum.inl 26, (1 / 54)), (Sum.inl 4, (1 / 18)), (Sum.inl 1, (-49 / 864)), (Sum.inl 31, (-1 / 18))]

def nodeValue3995 : Sparse Master := [(Sum.inl 0, (-31 / 4320)), (Sum.inl 2, (-1 / 288)), (Sum.inl 3, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (1 / 216)), (Sum.inl 31, (1 / 18))]

def nodeValue3996 : Sparse Master := []

def nodeValue3997 : Sparse Master := [(Sum.inl 0, (-1 / 288)), (Sum.inl 2, (1 / 216)), (Sum.inl 3, (-1 / 27)), (Sum.inl 26, (-1 / 54)), (Sum.inl 1, (-1 / 864))]

def nodeValue3998 : Sparse Master := [(Sum.inl 0, (-49 / 4320)), (Sum.inl 2, (1 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 4, (-1 / 27)), (Sum.inl 1, (5 / 432))]

def nodeValue3999 : Sparse Master := []

def nodeValue4000 : Sparse Master := []

def nodeValue4001 : Sparse Master := []

def nodeValue4002 : Sparse Master := [(Sum.inl 2, (1 / 54)), (Sum.inl 3, (2 / 27)), (Sum.inl 12, (1 / 54)), (Sum.inl 4, (2 / 27)), (Sum.inl 1, (-2 / 27)), (Sum.inl 31, (-1 / 9))]

def nodeValue4003 : Sparse Master := [(Sum.inl 0, (-1 / 135)), (Sum.inl 2, (-5 / 432)), (Sum.inl 3, (-1 / 27)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (7 / 432))]

def nodeValue4004 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 2, (-1 / 216)), (Sum.inl 1, (1 / 144)), (Sum.inl 31, (-1 / 9))]

def nodeValue4005 : Sparse Master := []

def nodeValue4006 : Sparse Master := []

def nodeValue4007 : Sparse Master := []

def nodeValue4008 : Sparse Master := []

def nodeValue4009 : Sparse Master := []

def nodeValue4010 : Sparse Master := [(Sum.inr 4010, (1 / 1))]

def nodeValue4011 : Sparse Master := []

def nodeValue4012 : Sparse Master := [(Sum.inl 0, (-11 / 1440)), (Sum.inl 2, (1 / 864)), (Sum.inl 3, (-1 / 54)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (-19 / 432))]

def nodeValue4013 : Sparse Master := [(Sum.inl 0, (-67 / 4320)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (5 / 288))]

def nodeValue4014 : Sparse Master := [(Sum.inl 0, (-1 / 90)), (Sum.inl 1, (-1 / 18))]

def nodeValue4015 : Sparse Master := [(Sum.inl 0, (-23 / 2160)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue4016 : Sparse Master := []

def nodeValue4017 : Sparse Master := [(Sum.inl 0, (-23 / 2160)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (1 / 144))]

def nodeValue4018 : Sparse Master := []

def nodeValue4019 : Sparse Master := []

def nodeValue4020 : Sparse Master := [(Sum.inl 0, (-7 / 720)), (Sum.inl 4, (-1 / 9)), (Sum.inl 1, (1 / 48))]

def nodeValue4021 : Sparse Master := []

def nodeValue4022 : Sparse Master := [(Sum.inr 4022, (1 / 1))]

def nodeValue4023 : Sparse Master := [(Sum.inl 0, (-37 / 4320)), (Sum.inl 5, (1 / 108)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (1 / 54)), (Sum.inl 35, (1 / 54)), (Sum.inl 3, (1 / 6)), (Sum.inl 23, (-1 / 18)), (Sum.inl 54, (-1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 25, (-1 / 9)), (Sum.inl 26, (2 / 27)), (Sum.inl 4, (2 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (1 / 432))]

def nodeValue4024 : Sparse Master := [(Sum.inr 4024, (1 / 1))]

def nodeValue4025 : Sparse Master := [(Sum.inr 4025, (1 / 1))]

def nodeValue4026 : Sparse Master := [(Sum.inl 0, (1 / 4320)), (Sum.inl 2, (1 / 96)), (Sum.inl 3, (1 / 6)), (Sum.inl 12, (2 / 27)), (Sum.inl 25, (-1 / 18)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 9)), (Sum.inl 1, (-7 / 108))]

def nodeValue4027 : Sparse Master := [(Sum.inl 0, (-1 / 180)), (Sum.inl 2, (-1 / 144)), (Sum.inl 3, (-1 / 27)), (Sum.inl 25, (1 / 18)), (Sum.inl 26, (-1 / 54)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (5 / 432))]

def nodeValue4028 : Sparse Master := [(Sum.inl 0, (-1 / 540)), (Sum.inl 2, (1 / 216)), (Sum.inl 3, (-1 / 27)), (Sum.inl 12, (-1 / 27)), (Sum.inl 25, (1 / 18)), (Sum.inl 1, (-5 / 216))]

def nodeValue4029 : Sparse Master := [(Sum.inl 0, (-17 / 2160)), (Sum.inl 2, (1 / 432)), (Sum.inl 3, (-1 / 27)), (Sum.inl 12, (-1 / 54)), (Sum.inl 4, (-1 / 27)), (Sum.inl 1, (5 / 216))]

def nodeValue4030 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 2, (-1 / 216)), (Sum.inl 25, (-1 / 9)), (Sum.inl 1, (-1 / 54))]

def nodeValue4031 : Sparse Master := [(Sum.inl 0, (-43 / 4320)), (Sum.inl 5, (1 / 216)), (Sum.inl 6, (-1 / 864)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (1 / 27)), (Sum.inl 3, (2 / 27)), (Sum.inl 23, (-1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 27, (-1 / 72)), (Sum.inl 1, (-11 / 216))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4032 : Sparse Master := [(Sum.inl 0, (-13 / 2160)), (Sum.inl 2, (-5 / 432)), (Sum.inl 3, (2 / 27)), (Sum.inl 25, (-1 / 18)), (Sum.inl 26, (1 / 27)), (Sum.inl 4, (1 / 27))]

def nodeValue4033 : Sparse Master := [(Sum.inl 0, (-29 / 4320)), (Sum.inl 2, (1 / 96)), (Sum.inl 3, (1 / 18)), (Sum.inl 12, (1 / 27)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-1 / 48))]

def nodeValue4034 : Sparse Master := []

def nodeValue4035 : Sparse Master := []

def nodeValue4036 : Sparse Master := []

def nodeValue4037 : Sparse Master := []

def nodeValue4038 : Sparse Master := []

def nodeValue4039 : Sparse Master := [(Sum.inl 0, (-7 / 432)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (5 / 144))]

def nodeValue4040 : Sparse Master := []

def nodeValue4041 : Sparse Master := [(Sum.inr 4041, (1 / 1))]

def nodeValue4042 : Sparse Master := [(Sum.inr 4042, (1 / 1))]

def nodeValue4043 : Sparse Master := [(Sum.inr 4043, (1 / 1))]

def nodeValue4044 : Sparse Master := []

def nodeValue4045 : Sparse Master := [(Sum.inr 4045, (1 / 1))]

def nodeValue4046 : Sparse Master := [(Sum.inr 4046, (1 / 1))]

def nodeValue4047 : Sparse Master := [(Sum.inr 4047, (1 / 1))]

def nodeValue4048 : Sparse Master := []

def nodeValue4049 : Sparse Master := []

def nodeValue4050 : Sparse Master := [(Sum.inl 0, (-67 / 4320)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (5 / 288))]

def nodeValue4051 : Sparse Master := [(Sum.inl 0, (-79 / 2160)), (Sum.inl 12, (1 / 54)), (Sum.inl 1, (-7 / 144))]

def nodeValue4052 : Sparse Master := []

def nodeValue4053 : Sparse Master := [(Sum.inl 0, (-47 / 2160)), (Sum.inl 4, (1 / 27)), (Sum.inl 1, (-7 / 144))]

def nodeValue4054 : Sparse Master := []

def nodeValue4055 : Sparse Master := []

def nodeValue4056 : Sparse Master := [(Sum.inr 4056, (1 / 1))]

def nodeValue4057 : Sparse Master := [(Sum.inr 4057, (1 / 1))]

def nodeValue4058 : Sparse Master := [(Sum.inr 4058, (1 / 1))]

def nodeValue4059 : Sparse Master := [(Sum.inr 4059, (1 / 1))]

def nodeValue4060 : Sparse Master := [(Sum.inr 4060, (1 / 1))]

def nodeValue4061 : Sparse Master := [(Sum.inr 4061, (1 / 1))]

def nodeValue4062 : Sparse Master := [(Sum.inr 4062, (1 / 1))]

def nodeValue4063 : Sparse Master := [(Sum.inr 4063, (1 / 1))]

def nodeValue4064 : Sparse Master := [(Sum.inr 4064, (1 / 1))]

def nodeValue4065 : Sparse Master := [(Sum.inr 4065, (1 / 1))]

def nodeValue4066 : Sparse Master := [(Sum.inr 4066, (1 / 1))]

def nodeValue4067 : Sparse Master := [(Sum.inr 4067, (1 / 1))]

def nodeValue4068 : Sparse Master := [(Sum.inr 4068, (1 / 1))]

def nodeValue4069 : Sparse Master := [(Sum.inr 4069, (1 / 1))]

def nodeValue4070 : Sparse Master := [(Sum.inr 4070, (1 / 1))]

def nodeValue4071 : Sparse Master := [(Sum.inr 4071, (1 / 1))]

def nodeValue4072 : Sparse Master := [(Sum.inr 4072, (1 / 1))]

def nodeValue4073 : Sparse Master := [(Sum.inr 4073, (1 / 1))]

def nodeValue4074 : Sparse Master := [(Sum.inr 4074, (1 / 1))]

def nodeValue4075 : Sparse Master := [(Sum.inr 4075, (1 / 1))]

def nodeValue4076 : Sparse Master := [(Sum.inr 4076, (1 / 1))]

def nodeValue4077 : Sparse Master := [(Sum.inr 4077, (1 / 1))]

def nodeValue4078 : Sparse Master := [(Sum.inr 4078, (1 / 1))]

def nodeValue4079 : Sparse Master := [(Sum.inr 4079, (1 / 1))]

def nodeValue4080 : Sparse Master := [(Sum.inr 4080, (1 / 1))]

def nodeValue4081 : Sparse Master := [(Sum.inr 4081, (1 / 1))]

def nodeValue4082 : Sparse Master := [(Sum.inr 4082, (1 / 1))]

def nodeValue4083 : Sparse Master := [(Sum.inr 4083, (1 / 1))]

def nodeValue4084 : Sparse Master := [(Sum.inr 4084, (1 / 1))]

def nodeValue4085 : Sparse Master := [(Sum.inr 4085, (1 / 1))]

def nodeValue4086 : Sparse Master := [(Sum.inr 4086, (1 / 1))]

def nodeValue4087 : Sparse Master := [(Sum.inr 4087, (1 / 1))]

def nodeValue4088 : Sparse Master := [(Sum.inr 4088, (1 / 1))]

def nodeValue4089 : Sparse Master := [(Sum.inr 4089, (1 / 1))]

def nodeValue4090 : Sparse Master := [(Sum.inr 4090, (1 / 1))]

def nodeValue4091 : Sparse Master := [(Sum.inr 4091, (1 / 1))]

def nodeValue4092 : Sparse Master := [(Sum.inr 4092, (1 / 1))]

def nodeValue4093 : Sparse Master := [(Sum.inl 0, (-1 / 24)), (Sum.inl 1, (1 / 24))]

def nodeValue4094 : Sparse Master := [(Sum.inl 0, (-1 / 30)), (Sum.inl 1, (-1 / 6))]

def nodeValue4095 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4096 : Sparse Master := [(Sum.inl 0, (-19 / 360)), (Sum.inl 1, (-1 / 72))]

def nodeValue4097 : Sparse Master := []

def nodeValue4098 : Sparse Master := [(Sum.inr 535, (-1 / 4)), (Sum.inr 656, (-1 / 4))]

def nodeValue4099 : Sparse Master := [(Sum.inr 536, (-1 / 4)), (Sum.inr 657, (-1 / 4))]

def nodeValue4100 : Sparse Master := [(Sum.inr 537, (-1 / 4)), (Sum.inr 662, (-1 / 4))]

def nodeValue4101 : Sparse Master := [(Sum.inr 538, (-1 / 4)), (Sum.inr 663, (-1 / 4))]

def nodeValue4102 : Sparse Master := [(Sum.inr 539, (-1 / 4)), (Sum.inr 664, (-1 / 4))]

def nodeValue4103 : Sparse Master := [(Sum.inr 540, (-1 / 4)), (Sum.inr 665, (-1 / 4))]

def nodeValue4104 : Sparse Master := [(Sum.inr 541, (-1 / 4)), (Sum.inr 674, (-1 / 4))]

def nodeValue4105 : Sparse Master := [(Sum.inr 542, (-1 / 4)), (Sum.inr 681, (-1 / 4))]

def nodeValue4106 : Sparse Master := [(Sum.inr 543, (-1 / 4)), (Sum.inr 675, (-1 / 4))]

def nodeValue4107 : Sparse Master := [(Sum.inr 544, (-1 / 4)), (Sum.inr 682, (-1 / 4))]

def nodeValue4108 : Sparse Master := [(Sum.inr 545, (-1 / 4)), (Sum.inr 683, (-1 / 4))]

def nodeValue4109 : Sparse Master := [(Sum.inr 546, (-1 / 4)), (Sum.inr 676, (-1 / 4))]

def nodeValue4110 : Sparse Master := [(Sum.inr 547, (-1 / 4)), (Sum.inr 684, (-1 / 4))]

def nodeValue4111 : Sparse Master := [(Sum.inr 548, (-1 / 4)), (Sum.inr 685, (-1 / 4))]

def nodeValue4112 : Sparse Master := [(Sum.inr 549, (-1 / 4)), (Sum.inr 686, (-1 / 4))]

def nodeValue4113 : Sparse Master := [(Sum.inr 550, (-1 / 4)), (Sum.inr 658, (-1 / 4))]

def nodeValue4115 : Sparse Master := [(Sum.inr 552, (-1 / 4)), (Sum.inr 660, (-1 / 4))]

def nodeValue4117 : Sparse Master := []

def nodeValue4118 : Sparse Master := []

def nodeValue4119 : Sparse Master := [(Sum.inr 554, (-1 / 4)), (Sum.inr 668, (-1 / 4))]

def nodeValue4120 : Sparse Master := []

def nodeValue4121 : Sparse Master := [(Sum.inr 555, (-1 / 4)), (Sum.inr 671, (-1 / 4))]

def nodeValue4122 : Sparse Master := [(Sum.inr 556, (-1 / 4)), (Sum.inr 670, (-1 / 4))]

def nodeValue4123 : Sparse Master := []

def nodeValue4125 : Sparse Master := []

def nodeValue4126 : Sparse Master := [(Sum.inr 557, (-1 / 4)), (Sum.inr 677, (-1 / 4))]

def nodeValue4127 : Sparse Master := []

def nodeValue4128 : Sparse Master := [(Sum.inr 559, (-1 / 4)), (Sum.inr 690, (-1 / 4))]

def nodeValue4130 : Sparse Master := []

def nodeValue4131 : Sparse Master := []

def nodeValue4132 : Sparse Master := [(Sum.inr 562, (-1 / 4)), (Sum.inr 679, (-1 / 4))]

def nodeValue4133 : Sparse Master := [(Sum.inr 563, (-1 / 4)), (Sum.inr 692, (-1 / 4))]

def nodeValue4134 : Sparse Master := [(Sum.inr 564, (-1 / 4)), (Sum.inr 695, (-1 / 4))]

def nodeValue4136 : Sparse Master := []

def nodeValue4137 : Sparse Master := []

def nodeValue4138 : Sparse Master := [(Sum.inr 566, (-1 / 4)), (Sum.inr 694, (-1 / 4))]

def nodeValue4139 : Sparse Master := [(Sum.inr 567, (-1 / 4)), (Sum.inr 1488, (-1 / 4))]

def nodeValue4140 : Sparse Master := [(Sum.inr 568, (-1 / 4)), (Sum.inr 1489, (-1 / 4))]

def nodeValue4141 : Sparse Master := [(Sum.inr 569, (-1 / 4)), (Sum.inr 1490, (-1 / 4))]

def nodeValue4142 : Sparse Master := [(Sum.inr 570, (-1 / 4)), (Sum.inr 765, (-1 / 4))]

def nodeValue4143 : Sparse Master := [(Sum.inr 571, (-1 / 4)), (Sum.inr 1491, (-1 / 4))]

def nodeValue4144 : Sparse Master := [(Sum.inr 572, (-1 / 4)), (Sum.inr 1492, (-1 / 4))]

def nodeValue4145 : Sparse Master := [(Sum.inr 573, (-1 / 4)), (Sum.inr 1493, (-1 / 4))]

def nodeValue4146 : Sparse Master := [(Sum.inr 574, (-1 / 4)), (Sum.inr 1494, (-1 / 4))]

def nodeValue4147 : Sparse Master := [(Sum.inr 575, (-1 / 4)), (Sum.inr 1495, (-1 / 4))]

def nodeValue4148 : Sparse Master := [(Sum.inr 576, (-1 / 4)), (Sum.inr 1496, (-1 / 4))]

def nodeValue4149 : Sparse Master := [(Sum.inr 4149, (1 / 1))]

def nodeValue4150 : Sparse Master := [(Sum.inr 4150, (1 / 1))]

def nodeValue4151 : Sparse Master := [(Sum.inr 4151, (1 / 1))]

def nodeValue4152 : Sparse Master := [(Sum.inr 4152, (1 / 1))]

def nodeValue4153 : Sparse Master := [(Sum.inr 4153, (1 / 1))]

def nodeValue4154 : Sparse Master := [(Sum.inr 4154, (1 / 1))]

def nodeValue4155 : Sparse Master := [(Sum.inr 4155, (1 / 1))]

def nodeValue4156 : Sparse Master := [(Sum.inr 4156, (1 / 1))]

def nodeValue4157 : Sparse Master := [(Sum.inr 4157, (1 / 1))]

def nodeValue4158 : Sparse Master := [(Sum.inr 4158, (1 / 1))]

def nodeValue4159 : Sparse Master := [(Sum.inr 4159, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4160 : Sparse Master := [(Sum.inr 4160, (1 / 1))]

def nodeValue4161 : Sparse Master := [(Sum.inr 4161, (1 / 1))]

def nodeValue4162 : Sparse Master := [(Sum.inr 4162, (1 / 1))]

def nodeValue4163 : Sparse Master := [(Sum.inr 4163, (1 / 1))]

def nodeValue4164 : Sparse Master := [(Sum.inr 592, (-1 / 4)), (Sum.inr 1497, (-1 / 4))]

def nodeValue4165 : Sparse Master := [(Sum.inr 593, (-1 / 4)), (Sum.inr 1498, (-1 / 4))]

def nodeValue4166 : Sparse Master := [(Sum.inr 594, (-1 / 4)), (Sum.inr 1499, (-1 / 4))]

def nodeValue4167 : Sparse Master := [(Sum.inr 595, (-1 / 4)), (Sum.inr 1500, (-1 / 4))]

def nodeValue4168 : Sparse Master := [(Sum.inr 596, (-1 / 4)), (Sum.inr 845, (-1 / 4))]

def nodeValue4169 : Sparse Master := [(Sum.inr 4169, (1 / 1))]

def nodeValue4170 : Sparse Master := [(Sum.inr 4170, (1 / 1))]

def nodeValue4171 : Sparse Master := [(Sum.inr 599, (-1 / 4)), (Sum.inr 1506, (-1 / 4))]

def nodeValue4172 : Sparse Master := [(Sum.inr 600, (-1 / 4)), (Sum.inr 1507, (-1 / 4))]

def nodeValue4173 : Sparse Master := [(Sum.inr 4173, (1 / 1))]

def nodeValue4174 : Sparse Master := [(Sum.inr 602, (-1 / 4)), (Sum.inr 1509, (-1 / 4))]

def nodeValue4175 : Sparse Master := [(Sum.inr 603, (-1 / 4)), (Sum.inr 1517, (-1 / 4))]

def nodeValue4176 : Sparse Master := [(Sum.inr 4176, (1 / 1))]

def nodeValue4177 : Sparse Master := [(Sum.inr 605, (-1 / 4)), (Sum.inr 1518, (-1 / 4))]

def nodeValue4178 : Sparse Master := [(Sum.inr 4178, (1 / 1))]

def nodeValue4179 : Sparse Master := [(Sum.inr 4179, (1 / 1))]

def nodeValue4180 : Sparse Master := [(Sum.inr 608, (-1 / 4)), (Sum.inr 1519, (-1 / 4))]

def nodeValue4181 : Sparse Master := [(Sum.inr 609, (-1 / 4)), (Sum.inr 1521, (-1 / 4))]

def nodeValue4182 : Sparse Master := [(Sum.inr 610, (-1 / 4)), (Sum.inr 1524, (-1 / 4))]

def nodeValue4183 : Sparse Master := [(Sum.inr 611, (-1 / 4)), (Sum.inr 1535, (-1 / 4))]

def nodeValue4184 : Sparse Master := [(Sum.inr 4184, (1 / 1))]

def nodeValue4185 : Sparse Master := [(Sum.inr 613, (-1 / 4)), (Sum.inr 1525, (-1 / 4))]

def nodeValue4186 : Sparse Master := [(Sum.inr 614, (-1 / 4)), (Sum.inr 1536, (-1 / 4))]

def nodeValue4187 : Sparse Master := [(Sum.inr 615, (-1 / 4)), (Sum.inr 1537, (-1 / 4))]

def nodeValue4188 : Sparse Master := [(Sum.inr 4188, (1 / 1))]

def nodeValue4189 : Sparse Master := [(Sum.inr 4189, (1 / 1))]

def nodeValue4190 : Sparse Master := [(Sum.inr 618, (-1 / 4)), (Sum.inr 1527, (-1 / 4))]

def nodeValue4191 : Sparse Master := [(Sum.inr 619, (-1 / 4)), (Sum.inr 1538, (-1 / 4))]

def nodeValue4192 : Sparse Master := [(Sum.inr 620, (-1 / 4)), (Sum.inr 1539, (-1 / 4))]

def nodeValue4193 : Sparse Master := [(Sum.inr 4193, (1 / 1))]

def nodeValue4194 : Sparse Master := [(Sum.inr 622, (-1 / 4)), (Sum.inr 1541, (-1 / 4))]

def nodeValue4195 : Sparse Master := [(Sum.inr 698, (-1 / 4)), (Sum.inr 744, (-1 / 4))]

def nodeValue4196 : Sparse Master := [(Sum.inr 699, (-1 / 4)), (Sum.inr 748, (-1 / 4))]

def nodeValue4197 : Sparse Master := [(Sum.inr 700, (-1 / 4)), (Sum.inr 749, (-1 / 4))]

def nodeValue4198 : Sparse Master := [(Sum.inr 701, (-1 / 4)), (Sum.inr 750, (-1 / 4))]

def nodeValue4199 : Sparse Master := [(Sum.inr 702, (-1 / 4)), (Sum.inr 760, (-1 / 4))]

def nodeValue4200 : Sparse Master := [(Sum.inr 703, (-1 / 4)), (Sum.inr 754, (-1 / 4))]

def nodeValue4201 : Sparse Master := [(Sum.inr 704, (-1 / 4)), (Sum.inr 761, (-1 / 4))]

def nodeValue4202 : Sparse Master := [(Sum.inr 705, (-1 / 4)), (Sum.inr 762, (-1 / 4))]

def nodeValue4203 : Sparse Master := [(Sum.inr 706, (-1 / 4)), (Sum.inr 755, (-1 / 4))]

def nodeValue4204 : Sparse Master := [(Sum.inr 707, (-1 / 4)), (Sum.inr 763, (-1 / 4))]

def nodeValue4205 : Sparse Master := [(Sum.inr 708, (-1 / 4)), (Sum.inr 764, (-1 / 4))]

def nodeValue4207 : Sparse Master := [(Sum.inr 710, (-1 / 4)), (Sum.inr 746, (-1 / 4))]

def nodeValue4209 : Sparse Master := []

def nodeValue4210 : Sparse Master := [(Sum.inr 713, (-1 / 4)), (Sum.inr 751, (-1 / 4))]

def nodeValue4211 : Sparse Master := []

def nodeValue4212 : Sparse Master := [(Sum.inr 715, (-1 / 4)), (Sum.inr 753, (-1 / 4))]

def nodeValue4213 : Sparse Master := [(Sum.inr 716, (-1 / 4)), (Sum.inr 752, (-1 / 4))]

def nodeValue4214 : Sparse Master := []

def nodeValue4216 : Sparse Master := []

def nodeValue4217 : Sparse Master := [(Sum.inr 719, (-1 / 4)), (Sum.inr 756, (-1 / 4))]

def nodeValue4218 : Sparse Master := []

def nodeValue4219 : Sparse Master := [(Sum.inr 720, (-1 / 4)), (Sum.inr 769, (-1 / 4))]

def nodeValue4221 : Sparse Master := []

def nodeValue4222 : Sparse Master := []

def nodeValue4223 : Sparse Master := [(Sum.inr 724, (-1 / 4)), (Sum.inr 758, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4224 : Sparse Master := [(Sum.inr 725, (-1 / 4)), (Sum.inr 771, (-1 / 4))]

def nodeValue4225 : Sparse Master := [(Sum.inr 726, (-1 / 4)), (Sum.inr 774, (-1 / 4))]

def nodeValue4227 : Sparse Master := []

def nodeValue4228 : Sparse Master := []

def nodeValue4229 : Sparse Master := [(Sum.inr 729, (-1 / 4)), (Sum.inr 773, (-1 / 4))]

def nodeValue4230 : Sparse Master := [(Sum.inr 730, (-1 / 4)), (Sum.inr 780, (-1 / 4))]

def nodeValue4231 : Sparse Master := [(Sum.inr 731, (-1 / 4)), (Sum.inr 781, (-1 / 4))]

def nodeValue4232 : Sparse Master := [(Sum.inr 732, (-1 / 4)), (Sum.inr 798, (-1 / 4))]

def nodeValue4233 : Sparse Master := [(Sum.inr 733, (-1 / 4)), (Sum.inr 799, (-1 / 4))]

def nodeValue4234 : Sparse Master := [(Sum.inr 734, (-1 / 4)), (Sum.inr 800, (-1 / 4))]

def nodeValue4235 : Sparse Master := [(Sum.inr 735, (-1 / 4)), (Sum.inr 801, (-1 / 4))]

def nodeValue4236 : Sparse Master := [(Sum.inr 736, (-1 / 4)), (Sum.inr 818, (-1 / 4))]

def nodeValue4237 : Sparse Master := [(Sum.inr 737, (-1 / 4)), (Sum.inr 840, (-1 / 4))]

def nodeValue4238 : Sparse Master := [(Sum.inr 738, (-1 / 4)), (Sum.inr 819, (-1 / 4))]

def nodeValue4239 : Sparse Master := [(Sum.inr 739, (-1 / 4)), (Sum.inr 841, (-1 / 4))]

def nodeValue4240 : Sparse Master := [(Sum.inr 740, (-1 / 4)), (Sum.inr 842, (-1 / 4))]

def nodeValue4241 : Sparse Master := [(Sum.inr 741, (-1 / 4)), (Sum.inr 820, (-1 / 4))]

def nodeValue4242 : Sparse Master := [(Sum.inr 742, (-1 / 4)), (Sum.inr 843, (-1 / 4))]

def nodeValue4243 : Sparse Master := [(Sum.inr 743, (-1 / 4)), (Sum.inr 844, (-1 / 4))]

def nodeValue4248 : Sparse Master := [(Sum.inr 782, (-1 / 2))]

def nodeValue4249 : Sparse Master := [(Sum.inr 783, (-1 / 4)), (Sum.inr 803, (-1 / 4))]

def nodeValue4251 : Sparse Master := [(Sum.inr 785, (-1 / 4)), (Sum.inr 804, (-1 / 4))]

def nodeValue4252 : Sparse Master := [(Sum.inr 786, (-1 / 4)), (Sum.inr 822, (-1 / 4))]

def nodeValue4253 : Sparse Master := [(Sum.inr 787, (-1 / 4)), (Sum.inr 847, (-1 / 4))]

def nodeValue4255 : Sparse Master := [(Sum.inr 789, (-1 / 4)), (Sum.inr 823, (-1 / 4))]

def nodeValue4256 : Sparse Master := [(Sum.inr 790, (-1 / 4)), (Sum.inr 848, (-1 / 4))]

def nodeValue4257 : Sparse Master := [(Sum.inr 791, (-1 / 4)), (Sum.inr 849, (-1 / 4))]

def nodeValue4263 : Sparse Master := []

def nodeValue4264 : Sparse Master := []

def nodeValue4265 : Sparse Master := [(Sum.inr 807, (-1 / 2))]

def nodeValue4266 : Sparse Master := []

def nodeValue4267 : Sparse Master := []

def nodeValue4268 : Sparse Master := [(Sum.inr 811, (-1 / 4)), (Sum.inr 824, (-1 / 4))]

def nodeValue4269 : Sparse Master := []

def nodeValue4270 : Sparse Master := [(Sum.inr 813, (-1 / 4)), (Sum.inr 853, (-1 / 4))]

def nodeValue4272 : Sparse Master := [(Sum.inr 815, (-1 / 4)), (Sum.inr 826, (-1 / 4))]

def nodeValue4273 : Sparse Master := []

def nodeValue4274 : Sparse Master := []

def nodeValue4275 : Sparse Master := [(Sum.inr 827, (-1 / 2))]

def nodeValue4276 : Sparse Master := [(Sum.inr 828, (-1 / 4)), (Sum.inr 857, (-1 / 4))]

def nodeValue4278 : Sparse Master := [(Sum.inr 830, (-1 / 2))]

def nodeValue4279 : Sparse Master := [(Sum.inr 831, (-1 / 4)), (Sum.inr 858, (-1 / 4))]

def nodeValue4280 : Sparse Master := [(Sum.inr 832, (-1 / 4)), (Sum.inr 862, (-1 / 4))]

def nodeValue4283 : Sparse Master := []

def nodeValue4284 : Sparse Master := []

def nodeValue4285 : Sparse Master := [(Sum.inr 860, (-1 / 2))]

def nodeValue4286 : Sparse Master := [(Sum.inr 864, (-1 / 4)), (Sum.inr 1550, (-1 / 4))]

def nodeValue4287 : Sparse Master := [(Sum.inr 865, (-1 / 4)), (Sum.inr 1553, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4288 : Sparse Master := [(Sum.inr 866, (-1 / 4)), (Sum.inr 1554, (-1 / 4))]

def nodeValue4289 : Sparse Master := [(Sum.inr 867, (-1 / 4)), (Sum.inr 1555, (-1 / 4))]

def nodeValue4290 : Sparse Master := [(Sum.inr 868, (-1 / 4)), (Sum.inr 1566, (-1 / 4))]

def nodeValue4291 : Sparse Master := [(Sum.inr 869, (-1 / 4)), (Sum.inr 1561, (-1 / 4))]

def nodeValue4292 : Sparse Master := [(Sum.inr 870, (-1 / 4)), (Sum.inr 1567, (-1 / 4))]

def nodeValue4293 : Sparse Master := [(Sum.inr 871, (-1 / 4)), (Sum.inr 1568, (-1 / 4))]

def nodeValue4294 : Sparse Master := [(Sum.inr 872, (-1 / 4)), (Sum.inr 1562, (-1 / 4))]

def nodeValue4295 : Sparse Master := [(Sum.inr 873, (-1 / 4)), (Sum.inr 1569, (-1 / 4))]

def nodeValue4296 : Sparse Master := [(Sum.inr 874, (-1 / 4)), (Sum.inr 1570, (-1 / 4))]

def nodeValue4298 : Sparse Master := [(Sum.inr 876, (-1 / 4)), (Sum.inr 1552, (-1 / 4))]

def nodeValue4300 : Sparse Master := []

def nodeValue4301 : Sparse Master := [(Sum.inr 879, (-1 / 4)), (Sum.inr 1556, (-1 / 4))]

def nodeValue4302 : Sparse Master := []

def nodeValue4303 : Sparse Master := [(Sum.inr 881, (-1 / 4)), (Sum.inr 1559, (-1 / 4))]

def nodeValue4304 : Sparse Master := [(Sum.inr 882, (-1 / 4)), (Sum.inr 1558, (-1 / 4))]

def nodeValue4305 : Sparse Master := []

def nodeValue4306 : Sparse Master := []

def nodeValue4307 : Sparse Master := [(Sum.inr 885, (-1 / 4)), (Sum.inr 1563, (-1 / 4))]

def nodeValue4308 : Sparse Master := []

def nodeValue4309 : Sparse Master := [(Sum.inr 887, (-1 / 4)), (Sum.inr 1573, (-1 / 4))]

def nodeValue4311 : Sparse Master := []

def nodeValue4312 : Sparse Master := []

def nodeValue4313 : Sparse Master := [(Sum.inr 891, (-1 / 4)), (Sum.inr 1565, (-1 / 4))]

def nodeValue4314 : Sparse Master := [(Sum.inr 892, (-1 / 4)), (Sum.inr 1575, (-1 / 4))]

def nodeValue4315 : Sparse Master := [(Sum.inr 893, (-1 / 4)), (Sum.inr 1578, (-1 / 4))]

def nodeValue4317 : Sparse Master := []

def nodeValue4318 : Sparse Master := []

def nodeValue4319 : Sparse Master := [(Sum.inr 897, (-1 / 4)), (Sum.inr 1577, (-1 / 4))]

def nodeValue4320 : Sparse Master := [(Sum.inr 898, (-1 / 4)), (Sum.inr 1586, (-1 / 4))]

def nodeValue4321 : Sparse Master := [(Sum.inr 899, (-1 / 4)), (Sum.inr 1587, (-1 / 4))]

def nodeValue4322 : Sparse Master := [(Sum.inr 900, (-1 / 4)), (Sum.inr 1588, (-1 / 4))]

def nodeValue4323 : Sparse Master := [(Sum.inr 901, (-1 / 4)), (Sum.inr 1589, (-1 / 4))]

def nodeValue4324 : Sparse Master := [(Sum.inr 902, (-1 / 4)), (Sum.inr 1590, (-1 / 4))]

def nodeValue4325 : Sparse Master := [(Sum.inr 903, (-1 / 4)), (Sum.inr 1591, (-1 / 4))]

def nodeValue4326 : Sparse Master := []

def nodeValue4327 : Sparse Master := [(Sum.inr 4327, (1 / 1))]

def nodeValue4328 : Sparse Master := [(Sum.inr 4328, (1 / 1))]

def nodeValue4329 : Sparse Master := []

def nodeValue4330 : Sparse Master := [(Sum.inr 4330, (1 / 1))]

def nodeValue4331 : Sparse Master := [(Sum.inr 4331, (1 / 1))]

def nodeValue4332 : Sparse Master := [(Sum.inr 4332, (1 / 1))]

def nodeValue4333 : Sparse Master := [(Sum.inr 4333, (1 / 1))]

def nodeValue4334 : Sparse Master := [(Sum.inr 4334, (1 / 1))]

def nodeValue4335 : Sparse Master := [(Sum.inr 4335, (1 / 1))]

def nodeValue4336 : Sparse Master := [(Sum.inr 4336, (1 / 1))]

def nodeValue4337 : Sparse Master := [(Sum.inr 915, (-1 / 4)), (Sum.inr 1632, (-1 / 4))]

def nodeValue4338 : Sparse Master := [(Sum.inr 916, (-1 / 4)), (Sum.inr 1633, (-1 / 4))]

def nodeValue4339 : Sparse Master := [(Sum.inr 917, (-1 / 4)), (Sum.inr 1634, (-1 / 4))]

def nodeValue4340 : Sparse Master := []

def nodeValue4341 : Sparse Master := [(Sum.inr 919, (-1 / 4)), (Sum.inr 1664, (-1 / 4))]

def nodeValue4342 : Sparse Master := []

def nodeValue4343 : Sparse Master := [(Sum.inr 921, (-1 / 4)), (Sum.inr 1666, (-1 / 4))]

def nodeValue4344 : Sparse Master := [(Sum.inr 922, (-1 / 4)), (Sum.inr 1673, (-1 / 4))]

def nodeValue4345 : Sparse Master := [(Sum.inr 4345, (1 / 1))]

def nodeValue4346 : Sparse Master := [(Sum.inr 924, (-1 / 4)), (Sum.inr 1674, (-1 / 4))]

def nodeValue4347 : Sparse Master := [(Sum.inr 4347, (1 / 1))]

def nodeValue4348 : Sparse Master := [(Sum.inr 4348, (1 / 1))]

def nodeValue4349 : Sparse Master := [(Sum.inr 927, (-1 / 4)), (Sum.inr 1675, (-1 / 4))]

def nodeValue4350 : Sparse Master := [(Sum.inr 928, (-1 / 4)), (Sum.inr 1677, (-1 / 4))]

def nodeValue4351 : Sparse Master := [(Sum.inr 929, (-1 / 4)), (Sum.inr 1680, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4352 : Sparse Master := [(Sum.inr 930, (-1 / 4)), (Sum.inr 1690, (-1 / 4))]

def nodeValue4353 : Sparse Master := [(Sum.inr 4353, (1 / 1))]

def nodeValue4354 : Sparse Master := [(Sum.inr 932, (-1 / 4)), (Sum.inr 1681, (-1 / 4))]

def nodeValue4355 : Sparse Master := [(Sum.inr 933, (-1 / 4)), (Sum.inr 1691, (-1 / 4))]

def nodeValue4356 : Sparse Master := [(Sum.inr 934, (-1 / 4)), (Sum.inr 1692, (-1 / 4))]

def nodeValue4357 : Sparse Master := [(Sum.inr 4357, (1 / 1))]

def nodeValue4358 : Sparse Master := [(Sum.inr 4358, (1 / 1))]

def nodeValue4359 : Sparse Master := [(Sum.inr 937, (-1 / 4)), (Sum.inr 1683, (-1 / 4))]

def nodeValue4360 : Sparse Master := [(Sum.inr 938, (-1 / 4)), (Sum.inr 1693, (-1 / 4))]

def nodeValue4361 : Sparse Master := [(Sum.inr 939, (-1 / 4)), (Sum.inr 1694, (-1 / 4))]

def nodeValue4362 : Sparse Master := [(Sum.inr 4362, (1 / 1))]

def nodeValue4363 : Sparse Master := [(Sum.inr 4363, (1 / 1))]

def nodeValue4364 : Sparse Master := [(Sum.inr 4364, (1 / 1))]

def nodeValue4365 : Sparse Master := [(Sum.inr 4365, (1 / 1))]

def nodeValue4366 : Sparse Master := [(Sum.inr 4366, (1 / 1))]

def nodeValue4367 : Sparse Master := [(Sum.inr 4367, (1 / 1))]

def nodeValue4368 : Sparse Master := [(Sum.inr 4368, (1 / 1))]

def nodeValue4369 : Sparse Master := [(Sum.inr 4369, (1 / 1))]

def nodeValue4370 : Sparse Master := [(Sum.inr 4370, (1 / 1))]

def nodeValue4371 : Sparse Master := [(Sum.inr 4371, (1 / 1))]

def nodeValue4372 : Sparse Master := [(Sum.inr 4372, (1 / 1))]

def nodeValue4373 : Sparse Master := [(Sum.inr 4373, (1 / 1))]

def nodeValue4374 : Sparse Master := [(Sum.inr 4374, (1 / 1))]

def nodeValue4375 : Sparse Master := [(Sum.inr 4375, (1 / 1))]

def nodeValue4390 : Sparse Master := []

def nodeValue4391 : Sparse Master := [(Sum.inr 4391, (1 / 1))]

def nodeValue4392 : Sparse Master := [(Sum.inr 4392, (1 / 1))]

def nodeValue4393 : Sparse Master := []

def nodeValue4395 : Sparse Master := []

def nodeValue4396 : Sparse Master := [(Sum.inr 977, (-1 / 4)), (Sum.inr 1597, (-1 / 4))]

def nodeValue4397 : Sparse Master := []

def nodeValue4398 : Sparse Master := [(Sum.inr 979, (-1 / 4)), (Sum.inr 1599, (-1 / 4))]

def nodeValue4399 : Sparse Master := [(Sum.inr 980, (-1 / 4)), (Sum.inr 1616, (-1 / 4))]

def nodeValue4400 : Sparse Master := [(Sum.inr 4400, (1 / 1))]

def nodeValue4401 : Sparse Master := [(Sum.inr 982, (-1 / 4)), (Sum.inr 1617, (-1 / 4))]

def nodeValue4402 : Sparse Master := [(Sum.inr 4402, (1 / 1))]

def nodeValue4404 : Sparse Master := [(Sum.inr 985, (-1 / 4)), (Sum.inr 1618, (-1 / 4))]

def nodeValue4405 : Sparse Master := [(Sum.inr 986, (-1 / 4)), (Sum.inr 1620, (-1 / 4))]

def nodeValue4406 : Sparse Master := [(Sum.inr 4406, (1 / 1))]

def nodeValue4407 : Sparse Master := [(Sum.inr 4407, (1 / 1))]

def nodeValue4410 : Sparse Master := [(Sum.inr 4410, (1 / 1))]

def nodeValue4412 : Sparse Master := [(Sum.inr 4412, (1 / 1))]

def nodeValue4414 : Sparse Master := [(Sum.inr 4414, (1 / 1))]

def nodeValue4415 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4417 : Sparse Master := [(Sum.inr 998, (-1 / 4)), (Sum.inr 1600, (-1 / 4))]

def nodeValue4418 : Sparse Master := [(Sum.inr 999, (-1 / 4)), (Sum.inr 1602, (-1 / 4))]

def nodeValue4419 : Sparse Master := [(Sum.inr 1000, (-1 / 4)), (Sum.inr 1605, (-1 / 4))]

def nodeValue4420 : Sparse Master := [(Sum.inr 4420, (1 / 1))]

def nodeValue4421 : Sparse Master := [(Sum.inr 1002, (-1 / 2))]

def nodeValue4423 : Sparse Master := []

def nodeValue4424 : Sparse Master := [(Sum.inr 1005, (-1 / 4)), (Sum.inr 1623, (-1 / 4))]

def nodeValue4425 : Sparse Master := [(Sum.inr 4425, (1 / 1))]

def nodeValue4426 : Sparse Master := []

def nodeValue4427 : Sparse Master := [(Sum.inr 4427, (1 / 1))]

def nodeValue4428 : Sparse Master := [(Sum.inr 1009, (-1 / 4)), (Sum.inr 1630, (-1 / 4))]

def nodeValue4431 : Sparse Master := [(Sum.inr 1012, (-1 / 4)), (Sum.inr 1627, (-1 / 4))]

def nodeValue4432 : Sparse Master := []

def nodeValue4435 : Sparse Master := [(Sum.inr 4435, (1 / 1))]

def nodeValue4436 : Sparse Master := [(Sum.inr 4436, (1 / 1))]

def nodeValue4437 : Sparse Master := [(Sum.inr 4437, (1 / 1))]

def nodeValue4438 : Sparse Master := []

def nodeValue4439 : Sparse Master := [(Sum.inr 4439, (1 / 1))]

def nodeValue4440 : Sparse Master := [(Sum.inr 4440, (1 / 1))]

def nodeValue4441 : Sparse Master := [(Sum.inr 4441, (1 / 1))]

def nodeValue4442 : Sparse Master := [(Sum.inr 4442, (1 / 1))]

def nodeValue4443 : Sparse Master := [(Sum.inr 4443, (1 / 1))]

def nodeValue4444 : Sparse Master := [(Sum.inr 4444, (1 / 1))]

def nodeValue4445 : Sparse Master := [(Sum.inr 4445, (1 / 1))]

def nodeValue4449 : Sparse Master := [(Sum.inr 4449, (1 / 1))]

def nodeValue4450 : Sparse Master := [(Sum.inr 4450, (1 / 1))]

def nodeValue4451 : Sparse Master := [(Sum.inr 1034, (-1 / 4)), (Sum.inr 1644, (-1 / 4))]

def nodeValue4452 : Sparse Master := [(Sum.inr 1035, (-1 / 4)), (Sum.inr 1645, (-1 / 4))]

def nodeValue4453 : Sparse Master := [(Sum.inr 4453, (1 / 1))]

def nodeValue4454 : Sparse Master := [(Sum.inr 1037, (-1 / 4)), (Sum.inr 1647, (-1 / 4))]

def nodeValue4455 : Sparse Master := []

def nodeValue4456 : Sparse Master := [(Sum.inr 1039, (-1 / 4)), (Sum.inr 1706, (-1 / 4))]

def nodeValue4457 : Sparse Master := [(Sum.inr 1040, (-1 / 4)), (Sum.inr 1707, (-1 / 4))]

def nodeValue4458 : Sparse Master := [(Sum.inr 1041, (-1 / 4)), (Sum.inr 1724, (-1 / 4))]

def nodeValue4459 : Sparse Master := [(Sum.inr 4459, (1 / 1))]

def nodeValue4460 : Sparse Master := [(Sum.inr 1043, (-1 / 4)), (Sum.inr 1725, (-1 / 4))]

def nodeValue4461 : Sparse Master := [(Sum.inr 1044, (-1 / 4)), (Sum.inr 1737, (-1 / 4))]

def nodeValue4462 : Sparse Master := [(Sum.inr 4462, (1 / 1))]

def nodeValue4463 : Sparse Master := [(Sum.inr 1046, (-1 / 4)), (Sum.inr 1750, (-1 / 4))]

def nodeValue4464 : Sparse Master := [(Sum.inr 4464, (1 / 1))]

def nodeValue4466 : Sparse Master := [(Sum.inr 1049, (-1 / 4)), (Sum.inr 1738, (-1 / 4))]

def nodeValue4467 : Sparse Master := [(Sum.inr 1050, (-1 / 4)), (Sum.inr 1751, (-1 / 4))]

def nodeValue4468 : Sparse Master := [(Sum.inr 1051, (-1 / 4)), (Sum.inr 1752, (-1 / 4))]

def nodeValue4469 : Sparse Master := [(Sum.inr 4469, (1 / 1))]

def nodeValue4470 : Sparse Master := [(Sum.inr 4470, (1 / 1))]

def nodeValue4471 : Sparse Master := [(Sum.inr 4471, (1 / 1))]

def nodeValue4473 : Sparse Master := [(Sum.inr 4473, (1 / 1))]

def nodeValue4474 : Sparse Master := [(Sum.inr 4474, (1 / 1))]

def nodeValue4475 : Sparse Master := [(Sum.inr 4475, (1 / 1))]

def nodeValue4476 : Sparse Master := [(Sum.inr 4476, (1 / 1))]

def nodeValue4478 : Sparse Master := [(Sum.inr 4478, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue448 : Sparse Master := [(Sum.inl 0, (19 / 432)), (Sum.inl 5, (-5 / 72)), (Sum.inl 2, (5 / 108)), (Sum.inl 7, (-5 / 18)), (Sum.inl 3, (-20 / 27)), (Sum.inl 23, (5 / 18)), (Sum.inl 24, (5 / 9)), (Sum.inl 12, (-5 / 27)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (5 / 432))]

def nodeValue449 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (-5 / 432)), (Sum.inl 7, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 23, (-5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 36))]

def nodeValue450 : Sparse Master := [(Sum.inl 0, (13 / 288)), (Sum.inl 5, (5 / 216)), (Sum.inl 2, (-5 / 432)), (Sum.inl 7, (5 / 54)), (Sum.inl 3, (5 / 27)), (Sum.inl 24, (-5 / 18)), (Sum.inl 4, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-35 / 288))]

def nodeValue451 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 23, (5 / 9)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (5 / 18))]

def nodeValue452 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 24, (5 / 9)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (-5 / 72))]

def nodeValue453 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 5, (5 / 72)), (Sum.inl 2, (-5 / 48)), (Sum.inl 8, (-5 / 27)), (Sum.inl 3, (-5 / 27)), (Sum.inl 24, (5 / 9)), (Sum.inl 56, (5 / 18)), (Sum.inl 4, (-5 / 27)), (Sum.inl 27, (-5 / 24)), (Sum.inl 1, (5 / 54)), (Sum.inl 30, (5 / 18))]

def nodeValue454 : Sparse Master := [(Sum.inl 0, (7 / 144)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (-5 / 96)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-25 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 52, (-5 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 4, (-5 / 54)), (Sum.inl 1, (5 / 216)), (Sum.inl 31, (5 / 18))]

def nodeValue455 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (-5 / 432)), (Sum.inl 35, (-5 / 54)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-5 / 18)), (Sum.inl 52, (-5 / 54)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 18)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 18)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (65 / 864))]

def nodeValue456 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (5 / 216)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-5 / 6)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-5 / 27)), (Sum.inl 25, (5 / 9)), (Sum.inl 26, (-10 / 27)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 432))]

def nodeValue457 : Sparse Master := [(Sum.inl 0, (23 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (-5 / 216)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 24, (5 / 18)), (Sum.inl 12, (-5 / 27)), (Sum.inl 56, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-10 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (35 / 216))]

def nodeValue458 : Sparse Master := [(Sum.inl 0, (37 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 62, (5 / 18)), (Sum.inl 33, (10 / 9)), (Sum.inl 3, (-20 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 9)), (Sum.inl 12, (-25 / 54)), (Sum.inl 25, (5 / 9)), (Sum.inl 4, (-5 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (25 / 432)), (Sum.inl 31, (5 / 18))]

def nodeValue459 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (-5 / 216)), (Sum.inl 7, (-5 / 54)), (Sum.inl 35, (-5 / 54)), (Sum.inl 3, (-5 / 27)), (Sum.inl 13, (-5 / 18)), (Sum.inl 23, (5 / 18)), (Sum.inl 54, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 25, (5 / 18)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (155 / 864))]

def nodeValue461 : Sparse Master := [(Sum.inl 0, (-1 / 216)), (Sum.inl 2, (-25 / 864)), (Sum.inl 3, (-10 / 27)), (Sum.inl 13, (-5 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (95 / 864))]

def nodeValue462 : Sparse Master := [(Sum.inl 0, (1 / 108)), (Sum.inl 2, (-35 / 864)), (Sum.inl 3, (-20 / 27)), (Sum.inl 13, (-5 / 18)), (Sum.inl 12, (-10 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (145 / 864))]

def nodeValue463 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 32, (-5 / 54)), (Sum.inl 3, (-10 / 9)), (Sum.inl 13, (-10 / 9)), (Sum.inl 12, (-5 / 9)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (5 / 48))]

def nodeValue464 : Sparse Master := []

def nodeValue465 : Sparse Master := []

def nodeValue466 : Sparse Master := []

def nodeValue467 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 2, (5 / 144)), (Sum.inl 3, (5 / 18)), (Sum.inl 13, (5 / 54)), (Sum.inl 12, (5 / 27)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-5 / 36))]

def nodeValue468 : Sparse Master := [(Sum.inl 0, (1 / 48)), (Sum.inl 2, (5 / 216)), (Sum.inl 3, (5 / 27)), (Sum.inl 13, (5 / 27)), (Sum.inl 1, (25 / 432))]

def nodeValue469 : Sparse Master := []

def nodeValue470 : Sparse Master := [(Sum.inl 0, (7 / 216)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 33, (5 / 6)), (Sum.inl 2, (-25 / 432)), (Sum.inl 81, (5 / 18)), (Sum.inl 3, (-5 / 6)), (Sum.inl 195, (-5 / 9)), (Sum.inl 12, (-10 / 27)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 18)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (35 / 288))]

def nodeValue471 : Sparse Master := [(Sum.inl 0, (43 / 864)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (5 / 216)), (Sum.inl 7, (-5 / 27)), (Sum.inl 3, (-10 / 27)), (Sum.inl 23, (5 / 18)), (Sum.inl 12, (-5 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (55 / 216))]

def nodeValue472 : Sparse Master := [(Sum.inl 0, (23 / 432)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (-5 / 96)), (Sum.inl 7, (-5 / 54)), (Sum.inl 8, (-5 / 54)), (Sum.inl 3, (-5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 4, (-5 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 216))]

def nodeValue473 : Sparse Master := [(Sum.inl 0, (41 / 864)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (-5 / 54)), (Sum.inl 7, (-5 / 27)), (Sum.inl 3, (-20 / 27)), (Sum.inl 23, (5 / 18)), (Sum.inl 12, (-25 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (5 / 48))]

def nodeValue474 : Sparse Master := [(Sum.inl 0, (1 / 18)), (Sum.inl 5, (5 / 216)), (Sum.inl 8, (5 / 54)), (Sum.inl 24, (-5 / 18)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (-5 / 108))]

def nodeValue475 : Sparse Master := [(Sum.inl 0, (1 / 27)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 63, (5 / 18)), (Sum.inl 64, (5 / 9)), (Sum.inl 33, (5 / 9)), (Sum.inl 2, (5 / 864)), (Sum.inl 123, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 25, (5 / 9)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (-5 / 108)), (Sum.inl 31, (5 / 18))]

def nodeValue476 : Sparse Master := [(Sum.inl 0, (25 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 64, (5 / 18)), (Sum.inl 33, (5 / 6)), (Sum.inl 2, (-5 / 216)), (Sum.inl 123, (5 / 18)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-35 / 54)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 18)), (Sum.inl 25, (5 / 9)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 18)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (65 / 432)), (Sum.inl 31, (5 / 9))]

def nodeValue477 : Sparse Master := [(Sum.inl 0, (25 / 864)), (Sum.inl 5, (-5 / 108)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (-35 / 864)), (Sum.inl 35, (-5 / 54)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-5 / 18)), (Sum.inl 52, (-5 / 54)), (Sum.inl 55, (5 / 18)), (Sum.inl 12, (-5 / 54)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 54)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (5 / 288))]

def nodeValue478 : Sparse Master := [(Sum.inl 0, (13 / 432)), (Sum.inl 2, (25 / 432)), (Sum.inl 3, (-10 / 27)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 27))]

def nodeValue479 : Sparse Master := [(Sum.inl 0, (7 / 432)), (Sum.inl 2, (-25 / 864)), (Sum.inl 3, (-25 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (85 / 864))]

def nodeValue480 : Sparse Master := [(Sum.inl 0, (5 / 288)), (Sum.inl 33, (5 / 9)), (Sum.inl 34, (-5 / 54)), (Sum.inl 2, (-35 / 864)), (Sum.inl 3, (-20 / 27)), (Sum.inl 13, (-10 / 27)), (Sum.inl 12, (-10 / 27)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (5 / 48))]

def nodeValue481 : Sparse Master := [(Sum.inl 0, (11 / 432)), (Sum.inl 34, (-5 / 27)), (Sum.inl 3, (-10 / 9)), (Sum.inl 13, (-10 / 9)), (Sum.inl 12, (-5 / 9)), (Sum.inl 1, (5 / 48))]

def nodeValue482 : Sparse Master := []

def nodeValue483 : Sparse Master := [(Sum.inl 0, (1 / 27)), (Sum.inl 2, (25 / 432)), (Sum.inl 3, (5 / 27)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-35 / 432))]

def nodeValue484 : Sparse Master := [(Sum.inl 0, (1 / 432)), (Sum.inl 33, (5 / 6)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-35 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 25, (5 / 9)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-10 / 27)), (Sum.inl 1, (25 / 216)), (Sum.inl 31, (5 / 9))]

def nodeValue485 : Sparse Master := [(Sum.inl 0, (1 / 216)), (Sum.inl 33, (5 / 18)), (Sum.inl 34, (-5 / 54)), (Sum.inl 2, (-5 / 108)), (Sum.inl 3, (-35 / 54)), (Sum.inl 13, (-5 / 54)), (Sum.inl 12, (-5 / 27)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 18)), (Sum.inl 4, (-5 / 18)), (Sum.inl 1, (25 / 216)), (Sum.inl 31, (5 / 18))]

def nodeValue486 : Sparse Master := [(Sum.inl 0, (-1 / 864)), (Sum.inl 2, (-5 / 96)), (Sum.inl 3, (-5 / 6)), (Sum.inl 12, (-10 / 27)), (Sum.inl 25, (5 / 18)), (Sum.inl 26, (-5 / 27)), (Sum.inl 4, (-5 / 9)), (Sum.inl 1, (35 / 108))]

def nodeValue487 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 2, (5 / 144)), (Sum.inl 3, (5 / 27)), (Sum.inl 25, (-5 / 18)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-25 / 432))]

def nodeValue488 : Sparse Master := [(Sum.inl 0, (29 / 864)), (Sum.inl 2, (-5 / 96)), (Sum.inl 3, (-5 / 18)), (Sum.inl 12, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (5 / 48))]

def nodeValue489 : Sparse Master := [(Sum.inl 0, (1 / 18)), (Sum.inl 2, (25 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-35 / 864))]

def nodeValue490 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 2, (5 / 216)), (Sum.inl 3, (5 / 27)), (Sum.inl 12, (5 / 27)), (Sum.inl 1, (-5 / 27))]

def nodeValue491 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 33, (-5 / 9)), (Sum.inl 2, (5 / 144)), (Sum.inl 3, (5 / 27)), (Sum.inl 12, (5 / 27)), (Sum.inl 1, (-5 / 48))]

def nodeValue492 : Sparse Master := [(Sum.inl 0, (1 / 432)), (Sum.inl 2, (-5 / 144)), (Sum.inl 3, (-5 / 9)), (Sum.inl 13, (-10 / 27)), (Sum.inl 1, (5 / 36))]

def nodeValue493 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 2, (5 / 864)), (Sum.inl 3, (5 / 18)), (Sum.inl 12, (5 / 54)), (Sum.inl 26, (5 / 54)), (Sum.inl 4, (5 / 27)), (Sum.inl 1, (-25 / 288))]

def nodeValue494 : Sparse Master := [(Sum.inl 0, (11 / 288)), (Sum.inl 2, (-5 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (95 / 432))]

def nodeValue495 : Sparse Master := []

def nodeValue496 : Sparse Master := [(Sum.inl 0, (5 / 144)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (-5 / 27)), (Sum.inl 12, (-5 / 27)), (Sum.inl 1, (25 / 216))]

def nodeValue497 : Sparse Master := [(Sum.inl 33, (5 / 9)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-20 / 27)), (Sum.inl 13, (-5 / 27)), (Sum.inl 12, (-10 / 27)), (Sum.inl 25, (5 / 9)), (Sum.inl 4, (-10 / 27)), (Sum.inl 1, (115 / 432)), (Sum.inl 31, (5 / 9))]

def nodeValue498 : Sparse Master := [(Sum.inl 0, (11 / 864)), (Sum.inl 33, (-5 / 18)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (5 / 54)), (Sum.inl 25, (-5 / 18)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-25 / 864)), (Sum.inl 31, (-5 / 18))]

def nodeValue499 : Sparse Master := [(Sum.inl 0, (-17 / 864)), (Sum.inl 2, (-5 / 96)), (Sum.inl 3, (-5 / 6)), (Sum.inl 13, (-5 / 27)), (Sum.inl 12, (-5 / 9)), (Sum.inl 4, (-5 / 9)), (Sum.inl 1, (5 / 12))]

def nodeValue500 : Sparse Master := [(Sum.inl 0, (1 / 108)), (Sum.inl 2, (-5 / 216)), (Sum.inl 3, (5 / 27)), (Sum.inl 12, (5 / 27)), (Sum.inl 25, (-5 / 18)), (Sum.inl 1, (25 / 216))]

def nodeValue501 : Sparse Master := [(Sum.inl 0, (5 / 216)), (Sum.inl 2, (5 / 216)), (Sum.inl 25, (5 / 9)), (Sum.inl 1, (5 / 54))]

def nodeValue502 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 2, (-5 / 432)), (Sum.inl 3, (5 / 27)), (Sum.inl 12, (5 / 54)), (Sum.inl 4, (5 / 27)), (Sum.inl 1, (-25 / 216))]

def nodeValue503 : Sparse Master := [(Sum.inl 0, (1 / 24)), (Sum.inl 2, (5 / 432)), (Sum.inl 3, (-5 / 27)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue504 : Sparse Master := [(Sum.inl 0, (35 / 432)), (Sum.inl 12, (5 / 54)), (Sum.inl 1, (-25 / 144))]

def nodeValue505 : Sparse Master := [(Sum.inl 0, (5 / 108)), (Sum.inl 12, (-5 / 27)), (Sum.inl 1, (5 / 36))]

def nodeValue506 : Sparse Master := []

def nodeValue507 : Sparse Master := [(Sum.inl 0, (1 / 36)), (Sum.inl 12, (5 / 9)), (Sum.inl 1, (5 / 12))]

def nodeValue508 : Sparse Master := [(Sum.inl 0, (13 / 216)), (Sum.inl 5, (-5 / 72)), (Sum.inl 8, (-5 / 18)), (Sum.inl 24, (5 / 18)), (Sum.inl 27, (5 / 24)), (Sum.inl 1, (5 / 216)), (Sum.inl 30, (5 / 9))]

def nodeValue509 : Sparse Master := [(Sum.inl 0, (2 / 27)), (Sum.inl 5, (5 / 216)), (Sum.inl 8, (5 / 54)), (Sum.inl 27, (-5 / 72)), (Sum.inl 1, (5 / 108)), (Sum.inl 30, (-5 / 18))]

def nodeValue510 : Sparse Master := [(Sum.inl 0, (13 / 216)), (Sum.inl 27, (5 / 36)), (Sum.inl 1, (5 / 216)), (Sum.inl 30, (5 / 9))]

def nodeValue511 : Sparse Master := [(Sum.inl 0, (7 / 432)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (-115 / 864)), (Sum.inl 51, (5 / 18)), (Sum.inl 3, (-10 / 27)), (Sum.inl 52, (-5 / 54)), (Sum.inl 4, (-5 / 18)), (Sum.inl 1, (35 / 144)), (Sum.inl 31, (5 / 9))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4480 : Sparse Master := [(Sum.inr 4480, (1 / 1))]

def nodeValue4481 : Sparse Master := [(Sum.inr 4481, (1 / 1))]

def nodeValue4486 : Sparse Master := [(Sum.inr 4486, (1 / 1))]

def nodeValue4487 : Sparse Master := [(Sum.inr 4487, (1 / 1))]

def nodeValue4489 : Sparse Master := [(Sum.inr 1073, (-1 / 4)), (Sum.inr 1648, (-1 / 4))]

def nodeValue4490 : Sparse Master := [(Sum.inr 1074, (-1 / 4)), (Sum.inr 1650, (-1 / 4))]

def nodeValue4491 : Sparse Master := [(Sum.inr 1075, (-1 / 4)), (Sum.inr 1653, (-1 / 4))]

def nodeValue4492 : Sparse Master := [(Sum.inr 4492, (1 / 1))]

def nodeValue4493 : Sparse Master := [(Sum.inr 1077, (-1 / 2))]

def nodeValue4494 : Sparse Master := [(Sum.inr 4494, (1 / 1))]

def nodeValue4495 : Sparse Master := [(Sum.inr 1079, (-1 / 4)), (Sum.inr 1708, (-1 / 4))]

def nodeValue4496 : Sparse Master := [(Sum.inr 1080, (-1 / 4)), (Sum.inr 1710, (-1 / 4))]

def nodeValue4497 : Sparse Master := []

def nodeValue4498 : Sparse Master := []

def nodeValue4499 : Sparse Master := [(Sum.inr 1083, (-1 / 4)), (Sum.inr 1728, (-1 / 4))]

def nodeValue4500 : Sparse Master := [(Sum.inr 4500, (1 / 1))]

def nodeValue4501 : Sparse Master := []

def nodeValue4502 : Sparse Master := []

def nodeValue4503 : Sparse Master := [(Sum.inr 1087, (-1 / 4)), (Sum.inr 1739, (-1 / 4))]

def nodeValue4504 : Sparse Master := [(Sum.inr 4504, (1 / 1))]

def nodeValue4505 : Sparse Master := []

def nodeValue4506 : Sparse Master := [(Sum.inr 4506, (1 / 1))]

def nodeValue4507 : Sparse Master := [(Sum.inr 1091, (-1 / 4)), (Sum.inr 1756, (-1 / 4))]

def nodeValue4508 : Sparse Master := [(Sum.inr 4508, (1 / 1))]

def nodeValue4510 : Sparse Master := [(Sum.inr 1094, (-1 / 4)), (Sum.inr 1741, (-1 / 4))]

def nodeValue4511 : Sparse Master := []

def nodeValue4512 : Sparse Master := []

def nodeValue4513 : Sparse Master := [(Sum.inr 1097, (-1 / 4)), (Sum.inr 3232, (-1 / 4))]

def nodeValue4514 : Sparse Master := [(Sum.inr 1098, (-1 / 4)), (Sum.inr 1894, (-1 / 4))]

def nodeValue4515 : Sparse Master := [(Sum.inr 1099, (-1 / 4)), (Sum.inr 3233, (-1 / 4))]

def nodeValue4516 : Sparse Master := [(Sum.inr 1100, (-1 / 4)), (Sum.inr 3234, (-1 / 4))]

def nodeValue4517 : Sparse Master := [(Sum.inr 1101, (-1 / 4)), (Sum.inr 3235, (-1 / 4))]

def nodeValue4518 : Sparse Master := [(Sum.inr 1102, (-1 / 4)), (Sum.inr 3236, (-1 / 4))]

def nodeValue4519 : Sparse Master := [(Sum.inr 1103, (-1 / 4)), (Sum.inr 1858, (-1 / 4))]

def nodeValue4520 : Sparse Master := [(Sum.inr 1104, (-1 / 4)), (Sum.inr 3237, (-1 / 4))]

def nodeValue4521 : Sparse Master := [(Sum.inr 1105, (-1 / 4)), (Sum.inr 1887, (-1 / 4))]

def nodeValue4522 : Sparse Master := [(Sum.inr 1106, (-1 / 4)), (Sum.inr 3249, (-1 / 4))]

def nodeValue4523 : Sparse Master := [(Sum.inr 1107, (-1 / 4)), (Sum.inr 3250, (-1 / 4))]

def nodeValue4524 : Sparse Master := [(Sum.inr 1108, (-1 / 4)), (Sum.inr 3251, (-1 / 4))]

def nodeValue4525 : Sparse Master := [(Sum.inr 1109, (-1 / 4)), (Sum.inr 1849, (-1 / 4))]

def nodeValue4526 : Sparse Master := [(Sum.inr 1110, (-1 / 4)), (Sum.inr 3252, (-1 / 4))]

def nodeValue4527 : Sparse Master := [(Sum.inr 4527, (1 / 1))]

def nodeValue4528 : Sparse Master := [(Sum.inr 4528, (1 / 1))]

def nodeValue4529 : Sparse Master := [(Sum.inr 4529, (1 / 1))]

def nodeValue4530 : Sparse Master := [(Sum.inr 4530, (1 / 1))]

def nodeValue4531 : Sparse Master := [(Sum.inr 4531, (1 / 1))]

def nodeValue4532 : Sparse Master := [(Sum.inr 4532, (1 / 1))]

def nodeValue4533 : Sparse Master := [(Sum.inr 4533, (1 / 1))]

def nodeValue4534 : Sparse Master := [(Sum.inr 4534, (1 / 1))]

def nodeValue4535 : Sparse Master := [(Sum.inr 4535, (1 / 1))]

def nodeValue4536 : Sparse Master := [(Sum.inr 4536, (1 / 1))]

def nodeValue4537 : Sparse Master := [(Sum.inr 1122, (-1 / 4)), (Sum.inr 3253, (-1 / 4))]

def nodeValue4538 : Sparse Master := [(Sum.inr 1123, (-1 / 4)), (Sum.inr 1937, (-1 / 4))]

def nodeValue4539 : Sparse Master := [(Sum.inr 1124, (-1 / 4)), (Sum.inr 3254, (-1 / 4))]

def nodeValue4540 : Sparse Master := [(Sum.inr 4540, (1 / 1))]

def nodeValue4541 : Sparse Master := [(Sum.inr 1126, (-1 / 4)), (Sum.inr 3256, (-1 / 4))]

def nodeValue4542 : Sparse Master := [(Sum.inr 4542, (1 / 1))]

def nodeValue4543 : Sparse Master := [(Sum.inr 1128, (-1 / 4)), (Sum.inr 2184, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4544 : Sparse Master := [(Sum.inr 1129, (-1 / 4)), (Sum.inr 3263, (-1 / 4))]

def nodeValue4545 : Sparse Master := [(Sum.inr 4545, (1 / 1))]

def nodeValue4546 : Sparse Master := [(Sum.inr 1131, (-1 / 4)), (Sum.inr 3264, (-1 / 4))]

def nodeValue4547 : Sparse Master := [(Sum.inr 4547, (1 / 1))]

def nodeValue4548 : Sparse Master := [(Sum.inr 4548, (1 / 1))]

def nodeValue4549 : Sparse Master := [(Sum.inr 1134, (-1 / 4)), (Sum.inr 3265, (-1 / 4))]

def nodeValue4550 : Sparse Master := [(Sum.inr 1135, (-1 / 4)), (Sum.inr 3269, (-1 / 4))]

def nodeValue4551 : Sparse Master := [(Sum.inr 1136, (-1 / 4)), (Sum.inr 3273, (-1 / 4))]

def nodeValue4552 : Sparse Master := [(Sum.inr 4552, (1 / 1))]

def nodeValue4553 : Sparse Master := [(Sum.inr 1138, (-1 / 4)), (Sum.inr 3270, (-1 / 4))]

def nodeValue4554 : Sparse Master := [(Sum.inr 1139, (-1 / 4)), (Sum.inr 3274, (-1 / 4))]

def nodeValue4555 : Sparse Master := [(Sum.inr 1140, (-1 / 4)), (Sum.inr 3275, (-1 / 4))]

def nodeValue4556 : Sparse Master := [(Sum.inr 4556, (1 / 1))]

def nodeValue4557 : Sparse Master := [(Sum.inr 1143, (-1 / 4)), (Sum.inr 2167, (-1 / 4))]

def nodeValue4558 : Sparse Master := [(Sum.inr 1144, (-1 / 4)), (Sum.inr 3276, (-1 / 4))]

def nodeValue4559 : Sparse Master := [(Sum.inr 1145, (-1 / 4)), (Sum.inr 3277, (-1 / 4))]

def nodeValue4560 : Sparse Master := [(Sum.inr 4560, (1 / 1))]

def nodeValue4569 : Sparse Master := [(Sum.inr 1187, (-1 / 4)), (Sum.inr 3244, (-1 / 4))]

def nodeValue4570 : Sparse Master := [(Sum.inr 1188, (-1 / 4)), (Sum.inr 3245, (-1 / 4))]

def nodeValue4572 : Sparse Master := [(Sum.inr 1190, (-1 / 4)), (Sum.inr 1952, (-1 / 4))]

def nodeValue4575 : Sparse Master := [(Sum.inr 1193, (-1 / 4)), (Sum.inr 3248, (-1 / 4))]

def nodeValue4581 : Sparse Master := [(Sum.inr 1200, (-1 / 4)), (Sum.inr 3281, (-1 / 4))]

def nodeValue4583 : Sparse Master := [(Sum.inr 1202, (-1 / 4)), (Sum.inr 1942, (-1 / 4))]

def nodeValue4586 : Sparse Master := [(Sum.inr 1205, (-1 / 4)), (Sum.inr 3284, (-1 / 4))]

def nodeValue4589 : Sparse Master := [(Sum.inr 4589, (1 / 1))]

def nodeValue4590 : Sparse Master := [(Sum.inr 4590, (1 / 1))]

def nodeValue4591 : Sparse Master := [(Sum.inr 4591, (1 / 1))]

def nodeValue4592 : Sparse Master := [(Sum.inr 4592, (1 / 1))]

def nodeValue4593 : Sparse Master := [(Sum.inr 4593, (1 / 1))]

def nodeValue4594 : Sparse Master := [(Sum.inr 4594, (1 / 1))]

def nodeValue4599 : Sparse Master := [(Sum.inr 4599, (1 / 1))]

def nodeValue4600 : Sparse Master := [(Sum.inr 4600, (1 / 1))]

def nodeValue4601 : Sparse Master := [(Sum.inr 1235, (-1 / 4)), (Sum.inr 3292, (-1 / 4))]

def nodeValue4602 : Sparse Master := [(Sum.inr 1236, (-1 / 4)), (Sum.inr 3293, (-1 / 4))]

def nodeValue4603 : Sparse Master := [(Sum.inr 4603, (1 / 1))]

def nodeValue4605 : Sparse Master := [(Sum.inr 1239, (-1 / 4)), (Sum.inr 2226, (-1 / 4))]

def nodeValue4606 : Sparse Master := [(Sum.inr 1240, (-1 / 4)), (Sum.inr 3299, (-1 / 4))]

def nodeValue4607 : Sparse Master := [(Sum.inr 4607, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4608 : Sparse Master := [(Sum.inr 1242, (-1 / 4)), (Sum.inr 3300, (-1 / 4))]

def nodeValue4609 : Sparse Master := [(Sum.inr 4609, (1 / 1))]

def nodeValue4611 : Sparse Master := [(Sum.inr 4611, (1 / 1))]

def nodeValue4612 : Sparse Master := [(Sum.inr 1246, (-1 / 4)), (Sum.inr 3301, (-1 / 4))]

def nodeValue4616 : Sparse Master := [(Sum.inr 4616, (1 / 1))]

def nodeValue4617 : Sparse Master := [(Sum.inr 4617, (1 / 1))]

def nodeValue4618 : Sparse Master := [(Sum.inr 1293, (-1 / 4)), (Sum.inr 3304, (-1 / 4))]

def nodeValue4619 : Sparse Master := [(Sum.inr 1294, (-1 / 4)), (Sum.inr 3305, (-1 / 4))]

def nodeValue4620 : Sparse Master := [(Sum.inr 4620, (1 / 1))]

def nodeValue4621 : Sparse Master := [(Sum.inr 1297, (-1 / 4)), (Sum.inr 2289, (-1 / 4))]

def nodeValue4622 : Sparse Master := [(Sum.inl 0, (37 / 17280)), (Sum.inl 6, (-1 / 1152)), (Sum.inl 7, (1 / 216)), (Sum.inl 8, (1 / 108)), (Sum.inl 1, (-7 / 1728)), (Sum.inr 3307, (-1 / 4))]

def nodeValue4623 : Sparse Master := [(Sum.inl 0, (1 / 576)), (Sum.inl 6, (1 / 1728)), (Sum.inl 7, (-1 / 108)), (Sum.inl 1, (1 / 144)), (Sum.inr 3308, (-1 / 4))]

def nodeValue4624 : Sparse Master := [(Sum.inl 0, (19 / 8640)), (Sum.inl 6, (1 / 1728)), (Sum.inl 8, (-1 / 108)), (Sum.inl 1, (-1 / 216)), (Sum.inr 3309, (-1 / 4))]

def nodeValue4625 : Sparse Master := [(Sum.inl 0, (1 / 576)), (Sum.inl 5, (-1 / 144)), (Sum.inl 6, (-1 / 576)), (Sum.inl 1, (1 / 144)), (Sum.inr 3310, (-1 / 4))]

def nodeValue4626 : Sparse Master := [(Sum.inr 4626, (1 / 1))]

def nodeValue4627 : Sparse Master := [(Sum.inl 0, (1 / 720)), (Sum.inl 5, (1 / 144)), (Sum.inl 7, (1 / 36)), (Sum.inl 1, (1 / 72)), (Sum.inr 3311, (-1 / 4))]

def nodeValue4628 : Sparse Master := [(Sum.inl 0, (1 / 480)), (Sum.inl 5, (1 / 144)), (Sum.inl 8, (1 / 36)), (Sum.inl 1, (-1 / 288)), (Sum.inr 3312, (-1 / 4))]

def nodeValue4629 : Sparse Master := [(Sum.inl 0, (1 / 720)), (Sum.inl 5, (1 / 36)), (Sum.inl 6, (1 / 144)), (Sum.inl 1, (1 / 72)), (Sum.inr 3313, (-1 / 4))]

def nodeValue4630 : Sparse Master := [(Sum.inr 1759, (-1 / 4)), (Sum.inr 1833, (-1 / 4))]

def nodeValue4631 : Sparse Master := [(Sum.inr 1760, (-1 / 4)), (Sum.inr 1836, (-1 / 4))]

def nodeValue4632 : Sparse Master := [(Sum.inr 1761, (-1 / 4)), (Sum.inr 1837, (-1 / 4))]

def nodeValue4633 : Sparse Master := [(Sum.inr 1762, (-1 / 4)), (Sum.inr 1847, (-1 / 4))]

def nodeValue4634 : Sparse Master := [(Sum.inr 1763, (-1 / 4)), (Sum.inr 1842, (-1 / 4))]

def nodeValue4635 : Sparse Master := [(Sum.inr 1764, (-1 / 4)), (Sum.inr 1848, (-1 / 4))]

def nodeValue4636 : Sparse Master := [(Sum.inr 1765, (-1 / 4)), (Sum.inr 1843, (-1 / 4))]

def nodeValue4637 : Sparse Master := [(Sum.inr 1766, (-1 / 4)), (Sum.inr 1850, (-1 / 4))]

def nodeValue4638 : Sparse Master := [(Sum.inr 1767, (-1 / 4)), (Sum.inr 1851, (-1 / 4))]

def nodeValue4640 : Sparse Master := [(Sum.inr 1769, (-1 / 4)), (Sum.inr 1835, (-1 / 4))]

def nodeValue4641 : Sparse Master := []

def nodeValue4642 : Sparse Master := [(Sum.inr 1771, (-1 / 4)), (Sum.inr 1838, (-1 / 4))]

def nodeValue4643 : Sparse Master := []

def nodeValue4644 : Sparse Master := [(Sum.inr 1773, (-1 / 4)), (Sum.inr 1841, (-1 / 4))]

def nodeValue4645 : Sparse Master := [(Sum.inr 1774, (-1 / 4)), (Sum.inr 1840, (-1 / 4))]

def nodeValue4646 : Sparse Master := []

def nodeValue4648 : Sparse Master := [(Sum.inr 1776, (-1 / 4)), (Sum.inr 1844, (-1 / 4))]

def nodeValue4649 : Sparse Master := []

def nodeValue4650 : Sparse Master := [(Sum.inr 1778, (-1 / 4)), (Sum.inr 1854, (-1 / 4))]

def nodeValue4652 : Sparse Master := []

def nodeValue4653 : Sparse Master := [(Sum.inr 1781, (-1 / 4)), (Sum.inr 1846, (-1 / 4))]

def nodeValue4654 : Sparse Master := [(Sum.inr 1782, (-1 / 4)), (Sum.inr 1855, (-1 / 4))]

def nodeValue4655 : Sparse Master := []

def nodeValue4657 : Sparse Master := [(Sum.inr 1783, (-1 / 4)), (Sum.inr 1857, (-1 / 4))]

def nodeValue4658 : Sparse Master := [(Sum.inr 1784, (-1 / 4)), (Sum.inr 1884, (-1 / 4))]

def nodeValue4660 : Sparse Master := [(Sum.inr 1786, (-1 / 4)), (Sum.inr 1982, (-1 / 4))]

def nodeValue4661 : Sparse Master := [(Sum.inr 1787, (-1 / 4)), (Sum.inr 1983, (-1 / 4))]

def nodeValue4663 : Sparse Master := [(Sum.inr 4663, (1 / 1))]

def nodeValue4664 : Sparse Master := [(Sum.inr 4664, (1 / 1))]

def nodeValue4665 : Sparse Master := [(Sum.inr 4665, (1 / 1))]

def nodeValue4666 : Sparse Master := [(Sum.inr 4666, (1 / 1))]

def nodeValue4667 : Sparse Master := [(Sum.inr 4667, (1 / 1))]

def nodeValue4668 : Sparse Master := [(Sum.inr 4668, (1 / 1))]

def nodeValue4669 : Sparse Master := [(Sum.inr 4669, (1 / 1))]

def nodeValue4670 : Sparse Master := [(Sum.inr 4670, (1 / 1))]

def nodeValue4671 : Sparse Master := [(Sum.inr 4671, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4672 : Sparse Master := [(Sum.inr 1798, (-1 / 4)), (Sum.inr 2067, (-1 / 4))]

def nodeValue4673 : Sparse Master := [(Sum.inr 1799, (-1 / 4)), (Sum.inr 1920, (-1 / 4))]

def nodeValue4675 : Sparse Master := [(Sum.inr 4675, (1 / 1))]

def nodeValue4676 : Sparse Master := [(Sum.inr 1802, (-1 / 4)), (Sum.inr 2141, (-1 / 4))]

def nodeValue4677 : Sparse Master := [(Sum.inr 4677, (1 / 1))]

def nodeValue4678 : Sparse Master := [(Sum.inr 1804, (-1 / 4)), (Sum.inr 2143, (-1 / 4))]

def nodeValue4679 : Sparse Master := [(Sum.inr 1805, (-1 / 4)), (Sum.inr 2150, (-1 / 4))]

def nodeValue4680 : Sparse Master := [(Sum.inr 4680, (1 / 1))]

def nodeValue4681 : Sparse Master := [(Sum.inr 1807, (-1 / 4)), (Sum.inr 2151, (-1 / 4))]

def nodeValue4682 : Sparse Master := [(Sum.inr 4682, (1 / 1))]

def nodeValue4683 : Sparse Master := [(Sum.inr 4683, (1 / 1))]

def nodeValue4684 : Sparse Master := [(Sum.inr 1810, (-1 / 4)), (Sum.inr 2152, (-1 / 4))]

def nodeValue4685 : Sparse Master := [(Sum.inr 1811, (-1 / 4)), (Sum.inr 2156, (-1 / 4))]

def nodeValue4686 : Sparse Master := [(Sum.inr 1812, (-1 / 4)), (Sum.inr 2165, (-1 / 4))]

def nodeValue4687 : Sparse Master := [(Sum.inr 4687, (1 / 1))]

def nodeValue4688 : Sparse Master := [(Sum.inr 1814, (-1 / 4)), (Sum.inr 2157, (-1 / 4))]

def nodeValue4689 : Sparse Master := [(Sum.inr 1815, (-1 / 4)), (Sum.inr 2166, (-1 / 4))]

def nodeValue4690 : Sparse Master := [(Sum.inr 4690, (1 / 1))]

def nodeValue4691 : Sparse Master := [(Sum.inr 1817, (-1 / 4)), (Sum.inr 2159, (-1 / 4))]

def nodeValue4692 : Sparse Master := [(Sum.inr 1818, (-1 / 4)), (Sum.inr 2168, (-1 / 4))]

def nodeValue4693 : Sparse Master := [(Sum.inr 1819, (-1 / 4)), (Sum.inr 2169, (-1 / 4))]

def nodeValue4694 : Sparse Master := [(Sum.inr 4694, (1 / 1))]

def nodeValue4695 : Sparse Master := [(Sum.inr 4695, (1 / 1))]

def nodeValue4696 : Sparse Master := [(Sum.inr 4696, (1 / 1))]

def nodeValue4697 : Sparse Master := [(Sum.inr 4697, (1 / 1))]

def nodeValue4698 : Sparse Master := [(Sum.inr 4698, (1 / 1))]

def nodeValue4699 : Sparse Master := [(Sum.inr 4699, (1 / 1))]

def nodeValue4700 : Sparse Master := [(Sum.inr 4700, (1 / 1))]

def nodeValue4701 : Sparse Master := [(Sum.inr 4701, (1 / 1))]

def nodeValue4702 : Sparse Master := [(Sum.inr 4702, (1 / 1))]

def nodeValue4703 : Sparse Master := [(Sum.inr 4703, (1 / 1))]

def nodeValue4704 : Sparse Master := [(Sum.inr 4704, (1 / 1))]

def nodeValue4705 : Sparse Master := [(Sum.inr 4705, (1 / 1))]

def nodeValue4706 : Sparse Master := [(Sum.inr 1860, (-1 / 4)), (Sum.inr 1888, (-1 / 4))]

def nodeValue4707 : Sparse Master := [(Sum.inr 1861, (-1 / 4)), (Sum.inr 1889, (-1 / 4))]

def nodeValue4708 : Sparse Master := []

def nodeValue4709 : Sparse Master := [(Sum.inr 1863, (-1 / 4)), (Sum.inr 1883, (-1 / 4))]

def nodeValue4710 : Sparse Master := [(Sum.inr 1864, (-1 / 4)), (Sum.inr 1882, (-1 / 4))]

def nodeValue4711 : Sparse Master := []

def nodeValue4712 : Sparse Master := []

def nodeValue4713 : Sparse Master := [(Sum.inr 1867, (-1 / 4)), (Sum.inr 1891, (-1 / 4))]

def nodeValue4715 : Sparse Master := []

def nodeValue4716 : Sparse Master := [(Sum.inr 1870, (-1 / 4)), (Sum.inr 1886, (-1 / 4))]

def nodeValue4717 : Sparse Master := [(Sum.inr 1871, (-1 / 4)), (Sum.inr 1892, (-1 / 4))]

def nodeValue4719 : Sparse Master := [(Sum.inr 1873, (-1 / 4)), (Sum.inr 1893, (-1 / 4))]

def nodeValue4720 : Sparse Master := [(Sum.inr 1874, (-1 / 4)), (Sum.inr 1896, (-1 / 4))]

def nodeValue4721 : Sparse Master := [(Sum.inr 1875, (-1 / 4)), (Sum.inr 1905, (-1 / 4))]

def nodeValue4722 : Sparse Master := [(Sum.inr 1876, (-1 / 4)), (Sum.inr 1906, (-1 / 4))]

def nodeValue4723 : Sparse Master := [(Sum.inr 1877, (-1 / 4)), (Sum.inr 1935, (-1 / 4))]

def nodeValue4724 : Sparse Master := [(Sum.inr 1878, (-1 / 4)), (Sum.inr 1919, (-1 / 4))]

def nodeValue4725 : Sparse Master := [(Sum.inr 1879, (-1 / 4)), (Sum.inr 1936, (-1 / 4))]

def nodeValue4726 : Sparse Master := [(Sum.inr 1880, (-1 / 4)), (Sum.inr 1938, (-1 / 4))]

def nodeValue4727 : Sparse Master := [(Sum.inr 1881, (-1 / 4)), (Sum.inr 1939, (-1 / 4))]

def nodeValue4728 : Sparse Master := [(Sum.inr 1897, (-1 / 4)), (Sum.inr 1907, (-1 / 4))]

def nodeValue4729 : Sparse Master := [(Sum.inr 1898, (-1 / 4)), (Sum.inr 1940, (-1 / 4))]

def nodeValue4731 : Sparse Master := [(Sum.inr 1900, (-1 / 4)), (Sum.inr 1921, (-1 / 4))]

def nodeValue4732 : Sparse Master := [(Sum.inr 1901, (-1 / 4)), (Sum.inr 1941, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4736 : Sparse Master := []

def nodeValue4737 : Sparse Master := [(Sum.inr 1909, (-1 / 2))]

def nodeValue4738 : Sparse Master := []

def nodeValue4739 : Sparse Master := []

def nodeValue4740 : Sparse Master := [(Sum.inr 1913, (-1 / 4)), (Sum.inr 1922, (-1 / 4))]

def nodeValue4741 : Sparse Master := []

def nodeValue4742 : Sparse Master := [(Sum.inr 1915, (-1 / 4)), (Sum.inr 1946, (-1 / 4))]

def nodeValue4744 : Sparse Master := [(Sum.inr 1917, (-1 / 4)), (Sum.inr 1924, (-1 / 4))]

def nodeValue4745 : Sparse Master := []

def nodeValue4746 : Sparse Master := [(Sum.inr 1925, (-1 / 2))]

def nodeValue4747 : Sparse Master := [(Sum.inr 1926, (-1 / 4)), (Sum.inr 1948, (-1 / 4))]

def nodeValue4749 : Sparse Master := [(Sum.inr 1928, (-1 / 2))]

def nodeValue4750 : Sparse Master := [(Sum.inr 1929, (-1 / 4)), (Sum.inr 1949, (-1 / 4))]

def nodeValue4752 : Sparse Master := []

def nodeValue4753 : Sparse Master := []

def nodeValue4754 : Sparse Master := [(Sum.inr 1951, (-1 / 2))]

def nodeValue4756 : Sparse Master := [(Sum.inr 4756, (1 / 1))]

def nodeValue4757 : Sparse Master := [(Sum.inr 4757, (1 / 1))]

def nodeValue4759 : Sparse Master := [(Sum.inr 1959, (-1 / 4)), (Sum.inr 2170, (-1 / 4))]

def nodeValue4760 : Sparse Master := [(Sum.inr 1960, (-1 / 4)), (Sum.inr 2173, (-1 / 4))]

def nodeValue4761 : Sparse Master := [(Sum.inr 4761, (1 / 1))]

def nodeValue4762 : Sparse Master := [(Sum.inr 4762, (1 / 1))]

def nodeValue4763 : Sparse Master := [(Sum.inr 1963, (-1 / 4)), (Sum.inr 2174, (-1 / 4))]

def nodeValue4764 : Sparse Master := [(Sum.inr 1964, (-1 / 4)), (Sum.inr 2182, (-1 / 4))]

def nodeValue4765 : Sparse Master := [(Sum.inr 4765, (1 / 1))]

def nodeValue4766 : Sparse Master := [(Sum.inr 1966, (-1 / 4)), (Sum.inr 2177, (-1 / 4))]

def nodeValue4767 : Sparse Master := [(Sum.inr 1967, (-1 / 4)), (Sum.inr 2183, (-1 / 4))]

def nodeValue4768 : Sparse Master := [(Sum.inr 4768, (1 / 1))]

def nodeValue4769 : Sparse Master := [(Sum.inr 1969, (-1 / 4)), (Sum.inr 2185, (-1 / 4))]

def nodeValue4770 : Sparse Master := [(Sum.inr 1970, (-1 / 4)), (Sum.inr 2186, (-1 / 4))]

def nodeValue4771 : Sparse Master := [(Sum.inr 4771, (1 / 1))]

def nodeValue4772 : Sparse Master := [(Sum.inr 4772, (1 / 1))]

def nodeValue4773 : Sparse Master := [(Sum.inr 4773, (1 / 1))]

def nodeValue4774 : Sparse Master := [(Sum.inr 4774, (1 / 1))]

def nodeValue4775 : Sparse Master := [(Sum.inr 4775, (1 / 1))]

def nodeValue4776 : Sparse Master := [(Sum.inr 4776, (1 / 1))]

def nodeValue4777 : Sparse Master := [(Sum.inr 4777, (1 / 1))]

def nodeValue4778 : Sparse Master := [(Sum.inr 1986, (-1 / 2))]

def nodeValue4779 : Sparse Master := [(Sum.inr 1987, (-1 / 4)), (Sum.inr 1996, (-1 / 4))]

def nodeValue4780 : Sparse Master := [(Sum.inr 4780, (1 / 1))]

def nodeValue4782 : Sparse Master := [(Sum.inr 1990, (-1 / 4)), (Sum.inr 1997, (-1 / 4))]

def nodeValue4783 : Sparse Master := [(Sum.inr 4783, (1 / 1))]

def nodeValue4785 : Sparse Master := [(Sum.inr 4785, (1 / 1))]

def nodeValue4787 : Sparse Master := [(Sum.inr 2000, (-1 / 2))]

def nodeValue4788 : Sparse Master := [(Sum.inr 2003, (-1 / 4)), (Sum.inr 2006, (-1 / 4))]

def nodeValue4790 : Sparse Master := []

def nodeValue4791 : Sparse Master := [(Sum.inr 4791, (1 / 1))]

def nodeValue4792 : Sparse Master := [(Sum.inr 4792, (1 / 1))]

def nodeValue4793 : Sparse Master := [(Sum.inr 4793, (1 / 1))]

def nodeValue4794 : Sparse Master := [(Sum.inr 4794, (1 / 1))]

def nodeValue4795 : Sparse Master := [(Sum.inr 4795, (1 / 1))]

def nodeValue4797 : Sparse Master := [(Sum.inr 4797, (1 / 1))]

def nodeValue4798 : Sparse Master := [(Sum.inr 2016, (-1 / 4)), (Sum.inr 2075, (-1 / 4))]

def nodeValue4799 : Sparse Master := [(Sum.inr 4799, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4800 : Sparse Master := [(Sum.inr 2018, (-1 / 2))]

def nodeValue4801 : Sparse Master := [(Sum.inr 2019, (-1 / 4)), (Sum.inr 2190, (-1 / 4))]

def nodeValue4802 : Sparse Master := [(Sum.inr 2020, (-1 / 4)), (Sum.inr 2202, (-1 / 4))]

def nodeValue4803 : Sparse Master := [(Sum.inr 4803, (1 / 1))]

def nodeValue4804 : Sparse Master := [(Sum.inr 2022, (-1 / 4)), (Sum.inr 2203, (-1 / 4))]

def nodeValue4805 : Sparse Master := [(Sum.inr 2023, (-1 / 4)), (Sum.inr 2214, (-1 / 4))]

def nodeValue4806 : Sparse Master := [(Sum.inr 4806, (1 / 1))]

def nodeValue4807 : Sparse Master := [(Sum.inr 2025, (-1 / 4)), (Sum.inr 2224, (-1 / 4))]

def nodeValue4808 : Sparse Master := [(Sum.inr 4808, (1 / 1))]

def nodeValue4810 : Sparse Master := [(Sum.inr 2028, (-1 / 4)), (Sum.inr 2215, (-1 / 4))]

def nodeValue4811 : Sparse Master := [(Sum.inr 2029, (-1 / 4)), (Sum.inr 2225, (-1 / 4))]

def nodeValue4812 : Sparse Master := [(Sum.inr 4812, (1 / 1))]

def nodeValue4813 : Sparse Master := [(Sum.inr 4813, (1 / 1))]

def nodeValue4815 : Sparse Master := [(Sum.inr 4815, (1 / 1))]

def nodeValue4816 : Sparse Master := [(Sum.inr 4816, (1 / 1))]

def nodeValue4817 : Sparse Master := [(Sum.inr 4817, (1 / 1))]

def nodeValue4819 : Sparse Master := [(Sum.inr 4819, (1 / 1))]

def nodeValue4821 : Sparse Master := [(Sum.inr 4821, (1 / 1))]

def nodeValue4824 : Sparse Master := [(Sum.inr 4824, (1 / 1))]

def nodeValue4825 : Sparse Master := [(Sum.inr 4825, (1 / 1))]

def nodeValue4826 : Sparse Master := [(Sum.inr 2046, (-1 / 4)), (Sum.inr 2077, (-1 / 4))]

def nodeValue4827 : Sparse Master := [(Sum.inr 2047, (-1 / 4)), (Sum.inr 2079, (-1 / 4))]

def nodeValue4828 : Sparse Master := [(Sum.inr 2048, (-1 / 4)), (Sum.inr 2082, (-1 / 4))]

def nodeValue4829 : Sparse Master := [(Sum.inr 4829, (1 / 1))]

def nodeValue4830 : Sparse Master := [(Sum.inr 4830, (1 / 1))]

def nodeValue4831 : Sparse Master := [(Sum.inr 2051, (-1 / 4)), (Sum.inr 2191, (-1 / 4))]

def nodeValue4832 : Sparse Master := [(Sum.inr 2052, (-1 / 4)), (Sum.inr 2193, (-1 / 4))]

def nodeValue4833 : Sparse Master := []

def nodeValue4834 : Sparse Master := []

def nodeValue4835 : Sparse Master := [(Sum.inr 2054, (-1 / 4)), (Sum.inr 2206, (-1 / 4))]

def nodeValue4836 : Sparse Master := [(Sum.inr 4836, (1 / 1))]

def nodeValue4837 : Sparse Master := []

def nodeValue4838 : Sparse Master := []

def nodeValue4839 : Sparse Master := [(Sum.inr 2058, (-1 / 4)), (Sum.inr 2216, (-1 / 4))]

def nodeValue4840 : Sparse Master := [(Sum.inr 4840, (1 / 1))]

def nodeValue4841 : Sparse Master := []

def nodeValue4842 : Sparse Master := [(Sum.inr 4842, (1 / 1))]

def nodeValue4843 : Sparse Master := [(Sum.inr 2062, (-1 / 4)), (Sum.inr 2230, (-1 / 4))]

def nodeValue4844 : Sparse Master := [(Sum.inr 4844, (1 / 1))]

def nodeValue4845 : Sparse Master := [(Sum.inr 2065, (-1 / 4)), (Sum.inr 2218, (-1 / 4))]

def nodeValue4846 : Sparse Master := []

def nodeValue4848 : Sparse Master := [(Sum.inr 4848, (1 / 1))]

def nodeValue4849 : Sparse Master := [(Sum.inr 4849, (1 / 1))]

def nodeValue4850 : Sparse Master := [(Sum.inr 4850, (1 / 1))]

def nodeValue4851 : Sparse Master := [(Sum.inr 4851, (1 / 1))]

def nodeValue4852 : Sparse Master := [(Sum.inr 4852, (1 / 1))]

def nodeValue4853 : Sparse Master := [(Sum.inr 4853, (1 / 1))]

def nodeValue4854 : Sparse Master := [(Sum.inr 4854, (1 / 1))]

def nodeValue4855 : Sparse Master := [(Sum.inr 4855, (1 / 1))]

def nodeValue4856 : Sparse Master := [(Sum.inr 4856, (1 / 1))]

def nodeValue4859 : Sparse Master := [(Sum.inr 2100, (-1 / 2))]

def nodeValue4860 : Sparse Master := [(Sum.inr 2101, (-1 / 2))]

def nodeValue4861 : Sparse Master := [(Sum.inr 4861, (1 / 1))]

def nodeValue4862 : Sparse Master := [(Sum.inr 2103, (-1 / 2))]

def nodeValue4863 : Sparse Master := [(Sum.inr 4863, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4864 : Sparse Master := [(Sum.inr 2105, (-1 / 4)), (Sum.inr 2241, (-1 / 4))]

def nodeValue4865 : Sparse Master := [(Sum.inr 2106, (-1 / 4)), (Sum.inr 2242, (-1 / 4))]

def nodeValue4866 : Sparse Master := [(Sum.inr 2107, (-1 / 4)), (Sum.inr 2260, (-1 / 4))]

def nodeValue4867 : Sparse Master := [(Sum.inr 4867, (1 / 1))]

def nodeValue4868 : Sparse Master := [(Sum.inr 2109, (-1 / 4)), (Sum.inr 2261, (-1 / 4))]

def nodeValue4869 : Sparse Master := [(Sum.inr 2110, (-1 / 4)), (Sum.inr 2275, (-1 / 4))]

def nodeValue4870 : Sparse Master := [(Sum.inr 4870, (1 / 1))]

def nodeValue4871 : Sparse Master := [(Sum.inr 2112, (-1 / 4)), (Sum.inr 2287, (-1 / 4))]

def nodeValue4872 : Sparse Master := [(Sum.inr 4872, (1 / 1))]

def nodeValue4874 : Sparse Master := [(Sum.inr 2115, (-1 / 4)), (Sum.inr 2276, (-1 / 4))]

def nodeValue4875 : Sparse Master := [(Sum.inr 2116, (-1 / 4)), (Sum.inr 2288, (-1 / 4))]

def nodeValue4878 : Sparse Master := [(Sum.inr 4878, (1 / 1))]

def nodeValue4879 : Sparse Master := [(Sum.inr 4879, (1 / 1))]

def nodeValue4880 : Sparse Master := [(Sum.inr 4880, (1 / 1))]

def nodeValue4881 : Sparse Master := [(Sum.inr 4881, (1 / 1))]

def nodeValue4884 : Sparse Master := [(Sum.inr 4884, (1 / 1))]

def nodeValue4885 : Sparse Master := [(Sum.inr 4885, (1 / 1))]

def nodeValue4886 : Sparse Master := [(Sum.inr 4886, (1 / 1))]

def nodeValue4887 : Sparse Master := [(Sum.inr 2243, (-1 / 2))]

def nodeValue4888 : Sparse Master := [(Sum.inr 2244, (-1 / 4)), (Sum.inr 2262, (-1 / 4))]

def nodeValue4889 : Sparse Master := [(Sum.inr 2245, (-1 / 4)), (Sum.inr 2277, (-1 / 4))]

def nodeValue4890 : Sparse Master := [(Sum.inr 2247, (-1 / 4)), (Sum.inr 2290, (-1 / 4))]

def nodeValue4891 : Sparse Master := [(Sum.inr 4891, (1 / 1))]

def nodeValue4892 : Sparse Master := [(Sum.inr 4892, (1 / 1))]

def nodeValue4893 : Sparse Master := []

def nodeValue4894 : Sparse Master := []

def nodeValue4895 : Sparse Master := []

def nodeValue4896 : Sparse Master := [(Sum.inr 2266, (-1 / 4)), (Sum.inr 2278, (-1 / 4))]

def nodeValue4897 : Sparse Master := []

def nodeValue4898 : Sparse Master := [(Sum.inr 2279, (-1 / 2))]

def nodeValue4899 : Sparse Master := [(Sum.inr 2281, (-1 / 4)), (Sum.inr 2294, (-1 / 4))]

def nodeValue4900 : Sparse Master := [(Sum.inr 4900, (1 / 1))]

def nodeValue4901 : Sparse Master := []

def nodeValue4902 : Sparse Master := [(Sum.inr 2295, (-1 / 4)), (Sum.inr 3315, (-1 / 4))]

def nodeValue4907 : Sparse Master := [(Sum.inr 2300, (-1 / 4)), (Sum.inr 3325, (-1 / 4))]

def nodeValue4913 : Sparse Master := [(Sum.inr 2306, (-1 / 4)), (Sum.inr 3318, (-1 / 4))]

def nodeValue4915 : Sparse Master := []

def nodeValue4918 : Sparse Master := []

def nodeValue4924 : Sparse Master := []

def nodeValue4926 : Sparse Master := [(Sum.inr 2316, (-1 / 4)), (Sum.inr 3398, (-1 / 4))]

def nodeValue4927 : Sparse Master := [(Sum.inr 2317, (-1 / 4)), (Sum.inr 3399, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4928 : Sparse Master := [(Sum.inr 2318, (-1 / 4)), (Sum.inr 3400, (-1 / 4))]

def nodeValue4929 : Sparse Master := []

def nodeValue4930 : Sparse Master := [(Sum.inr 4930, (1 / 1))]

def nodeValue4931 : Sparse Master := [(Sum.inr 4931, (1 / 1))]

def nodeValue4932 : Sparse Master := []

def nodeValue4933 : Sparse Master := [(Sum.inr 4933, (1 / 1))]

def nodeValue4934 : Sparse Master := [(Sum.inr 4934, (1 / 1))]

def nodeValue4935 : Sparse Master := [(Sum.inr 4935, (1 / 1))]

def nodeValue4936 : Sparse Master := [(Sum.inr 2328, (-1 / 4)), (Sum.inr 3401, (-1 / 4))]

def nodeValue4937 : Sparse Master := [(Sum.inr 2329, (-1 / 4)), (Sum.inr 3402, (-1 / 4))]

def nodeValue4938 : Sparse Master := []

def nodeValue4939 : Sparse Master := [(Sum.inr 2330, (-1 / 4)), (Sum.inr 3404, (-1 / 4))]

def nodeValue4940 : Sparse Master := []

def nodeValue4941 : Sparse Master := [(Sum.inr 2332, (-1 / 4)), (Sum.inr 3410, (-1 / 4))]

def nodeValue4942 : Sparse Master := [(Sum.inr 4942, (1 / 1))]

def nodeValue4943 : Sparse Master := [(Sum.inr 2334, (-1 / 4)), (Sum.inr 3411, (-1 / 4))]

def nodeValue4944 : Sparse Master := [(Sum.inr 4944, (1 / 1))]

def nodeValue4945 : Sparse Master := [(Sum.inr 4945, (1 / 1))]

def nodeValue4946 : Sparse Master := [(Sum.inr 2337, (-1 / 4)), (Sum.inr 3412, (-1 / 4))]

def nodeValue4947 : Sparse Master := [(Sum.inr 2338, (-1 / 4)), (Sum.inr 3416, (-1 / 4))]

def nodeValue4948 : Sparse Master := [(Sum.inr 2339, (-1 / 4)), (Sum.inr 3420, (-1 / 4))]

def nodeValue4949 : Sparse Master := [(Sum.inr 2341, (-1 / 4)), (Sum.inr 3417, (-1 / 4))]

def nodeValue4950 : Sparse Master := [(Sum.inr 2342, (-1 / 4)), (Sum.inr 3421, (-1 / 4))]

def nodeValue4951 : Sparse Master := [(Sum.inr 4951, (1 / 1))]

def nodeValue4952 : Sparse Master := [(Sum.inr 2344, (-1 / 4)), (Sum.inr 3422, (-1 / 4))]

def nodeValue4953 : Sparse Master := [(Sum.inr 2345, (-1 / 4)), (Sum.inr 3423, (-1 / 4))]

def nodeValue4954 : Sparse Master := [(Sum.inr 4954, (1 / 1))]

def nodeValue4955 : Sparse Master := [(Sum.inr 4955, (1 / 1))]

def nodeValue4956 : Sparse Master := [(Sum.inr 4956, (1 / 1))]

def nodeValue4957 : Sparse Master := [(Sum.inr 4957, (1 / 1))]

def nodeValue4958 : Sparse Master := [(Sum.inr 4958, (1 / 1))]

def nodeValue4959 : Sparse Master := [(Sum.inr 4959, (1 / 1))]

def nodeValue4960 : Sparse Master := [(Sum.inr 2412, (-1 / 4)), (Sum.inr 3426, (-1 / 4))]

def nodeValue4961 : Sparse Master := [(Sum.inr 2796, (-1 / 4)), (Sum.inr 3589, (-1 / 4))]

def nodeValue4963 : Sparse Master := [(Sum.inr 4963, (1 / 1))]

def nodeValue4964 : Sparse Master := [(Sum.inr 4964, (1 / 1))]

def nodeValue4965 : Sparse Master := [(Sum.inr 4965, (1 / 1))]

def nodeValue4966 : Sparse Master := [(Sum.inr 4966, (1 / 1))]

def nodeValue4967 : Sparse Master := [(Sum.inr 2814, (-1 / 4)), (Sum.inr 3585, (-1 / 4))]

def nodeValue4968 : Sparse Master := [(Sum.inr 2809, (-1 / 4)), (Sum.inr 3587, (-1 / 4))]

def nodeValue4969 : Sparse Master := [(Sum.inr 2804, (-1 / 4)), (Sum.inr 3586, (-1 / 4))]

def nodeValue4970 : Sparse Master := [(Sum.inr 2815, (-1 / 4)), (Sum.inr 3588, (-1 / 4))]

def nodeValue4971 : Sparse Master := [(Sum.inr 2807, (-1 / 4)), (Sum.inr 3590, (-1 / 4))]

def nodeValue4972 : Sparse Master := [(Sum.inr 2434, (-1 / 4)), (Sum.inr 3457, (-1 / 4))]

def nodeValue4973 : Sparse Master := [(Sum.inr 2817, (-1 / 4)), (Sum.inr 3591, (-1 / 4))]

def nodeValue4974 : Sparse Master := [(Sum.inr 2818, (-1 / 4)), (Sum.inr 3592, (-1 / 4))]

def nodeValue4975 : Sparse Master := [(Sum.inr 4975, (1 / 1))]

def nodeValue4976 : Sparse Master := [(Sum.inr 4976, (1 / 1))]

def nodeValue4977 : Sparse Master := [(Sum.inr 2813, (-1 / 4)), (Sum.inr 3595, (-1 / 4))]

def nodeValue4979 : Sparse Master := [(Sum.inr 2820, (-1 / 4)), (Sum.inr 3596, (-1 / 4))]

def nodeValue4985 : Sparse Master := [(Sum.inr 2370, (-1 / 4)), (Sum.inr 3334, (-1 / 4))]

def nodeValue4986 : Sparse Master := [(Sum.inr 2371, (-1 / 4)), (Sum.inr 3335, (-1 / 4))]

def nodeValue4987 : Sparse Master := [(Sum.inr 2372, (-1 / 4)), (Sum.inr 3336, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4992 : Sparse Master := [(Sum.inr 4992, (1 / 1))]

def nodeValue4993 : Sparse Master := [(Sum.inr 4993, (1 / 1))]

def nodeValue4996 : Sparse Master := [(Sum.inr 2382, (-1 / 4)), (Sum.inr 3340, (-1 / 4))]

def nodeValue4998 : Sparse Master := [(Sum.inr 2383, (-1 / 4)), (Sum.inr 3352, (-1 / 4))]

def nodeValue4999 : Sparse Master := [(Sum.inr 4999, (1 / 1))]

def nodeValue5000 : Sparse Master := [(Sum.inr 2385, (-1 / 4)), (Sum.inr 3353, (-1 / 4))]

def nodeValue5003 : Sparse Master := [(Sum.inr 2388, (-1 / 4)), (Sum.inr 3354, (-1 / 4))]

def nodeValue5004 : Sparse Master := [(Sum.inr 5004, (1 / 1))]

def nodeValue5005 : Sparse Master := [(Sum.inr 5005, (1 / 1))]

def nodeValue5011 : Sparse Master := [(Sum.inr 5011, (1 / 1))]

def nodeValue5013 : Sparse Master := [(Sum.inr 2398, (-1 / 4)), (Sum.inr 3341, (-1 / 4))]

def nodeValue5014 : Sparse Master := [(Sum.inr 2399, (-1 / 4)), (Sum.inr 2467, (-1 / 4))]

def nodeValue5015 : Sparse Master := [(Sum.inr 2400, (-1 / 4)), (Sum.inr 3344, (-1 / 4))]

def nodeValue5017 : Sparse Master := []

def nodeValue5018 : Sparse Master := [(Sum.inr 2404, (-1 / 4)), (Sum.inr 3357, (-1 / 4))]

def nodeValue5021 : Sparse Master := [(Sum.inr 2407, (-1 / 4)), (Sum.inr 3360, (-1 / 4))]

def nodeValue5023 : Sparse Master := [(Sum.inr 2410, (-1 / 2))]

def nodeValue5025 : Sparse Master := []

def nodeValue5029 : Sparse Master := []

def nodeValue5030 : Sparse Master := [(Sum.inr 2419, (-1 / 4)), (Sum.inr 3425, (-1 / 4))]

def nodeValue5032 : Sparse Master := [(Sum.inr 2424, (-1 / 4)), (Sum.inr 3440, (-1 / 4))]

def nodeValue5033 : Sparse Master := [(Sum.inr 2425, (-1 / 4)), (Sum.inr 3449, (-1 / 4))]

def nodeValue5034 : Sparse Master := [(Sum.inr 5034, (1 / 1))]

def nodeValue5035 : Sparse Master := [(Sum.inr 5035, (1 / 1))]

def nodeValue5036 : Sparse Master := [(Sum.inr 2428, (-1 / 4)), (Sum.inr 3450, (-1 / 4))]

def nodeValue5037 : Sparse Master := [(Sum.inr 2429, (-1 / 4)), (Sum.inr 3455, (-1 / 4))]

def nodeValue5038 : Sparse Master := [(Sum.inr 2431, (-1 / 4)), (Sum.inr 3453, (-1 / 4))]

def nodeValue5039 : Sparse Master := [(Sum.inr 2432, (-1 / 4)), (Sum.inr 3456, (-1 / 4))]

def nodeValue5040 : Sparse Master := [(Sum.inr 5040, (1 / 1))]

def nodeValue5041 : Sparse Master := [(Sum.inr 5041, (1 / 1))]

def nodeValue5042 : Sparse Master := [(Sum.inr 5042, (1 / 1))]

def nodeValue5043 : Sparse Master := [(Sum.inr 5043, (1 / 1))]

def nodeValue5044 : Sparse Master := [(Sum.inr 5044, (1 / 1))]

def nodeValue5047 : Sparse Master := [(Sum.inr 2449, (-1 / 4)), (Sum.inr 3432, (-1 / 4))]

def nodeValue5050 : Sparse Master := [(Sum.inr 2452, (-1 / 4)), (Sum.inr 3433, (-1 / 4))]

def nodeValue5055 : Sparse Master := [(Sum.inr 2458, (-1 / 2))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue5056 : Sparse Master := [(Sum.inr 2459, (-1 / 4)), (Sum.inr 3429, (-1 / 4))]

def nodeValue5058 : Sparse Master := []

def nodeValue5059 : Sparse Master := [(Sum.inr 2462, (-1 / 4)), (Sum.inr 3436, (-1 / 4))]

def nodeValue5063 : Sparse Master := []

def nodeValue5064 : Sparse Master := [(Sum.inr 5064, (1 / 1))]

def nodeValue5065 : Sparse Master := [(Sum.inr 5065, (1 / 1))]

def nodeValue5066 : Sparse Master := [(Sum.inr 5066, (1 / 1))]

def nodeValue5067 : Sparse Master := [(Sum.inr 5067, (1 / 1))]

def nodeValue5069 : Sparse Master := [(Sum.inr 5069, (1 / 1))]

def nodeValue5070 : Sparse Master := [(Sum.inr 2477, (-1 / 4)), (Sum.inr 3444, (-1 / 4))]

def nodeValue5071 : Sparse Master := [(Sum.inr 5071, (1 / 1))]

def nodeValue5072 : Sparse Master := [(Sum.inr 2479, (-1 / 4)), (Sum.inr 3459, (-1 / 4))]

def nodeValue5073 : Sparse Master := [(Sum.inr 2480, (-1 / 4)), (Sum.inr 3467, (-1 / 4))]

def nodeValue5074 : Sparse Master := [(Sum.inr 5074, (1 / 1))]

def nodeValue5075 : Sparse Master := [(Sum.inr 2482, (-1 / 4)), (Sum.inr 3468, (-1 / 4))]

def nodeValue5076 : Sparse Master := [(Sum.inr 2483, (-1 / 4)), (Sum.inr 3477, (-1 / 4))]

def nodeValue5077 : Sparse Master := [(Sum.inr 5077, (1 / 1))]

def nodeValue5078 : Sparse Master := [(Sum.inr 2485, (-1 / 4)), (Sum.inr 3481, (-1 / 4))]

def nodeValue5080 : Sparse Master := [(Sum.inr 2488, (-1 / 4)), (Sum.inr 3478, (-1 / 4))]

def nodeValue5081 : Sparse Master := [(Sum.inr 2489, (-1 / 4)), (Sum.inr 3482, (-1 / 4))]

def nodeValue5082 : Sparse Master := [(Sum.inr 5082, (1 / 1))]

def nodeValue5083 : Sparse Master := [(Sum.inr 5083, (1 / 1))]

def nodeValue5085 : Sparse Master := [(Sum.inr 5085, (1 / 1))]

def nodeValue5086 : Sparse Master := [(Sum.inr 5086, (1 / 1))]

def nodeValue5087 : Sparse Master := [(Sum.inr 5087, (1 / 1))]

def nodeValue5090 : Sparse Master := [(Sum.inr 5090, (1 / 1))]

def nodeValue5091 : Sparse Master := [(Sum.inr 5091, (1 / 1))]

def nodeValue5092 : Sparse Master := [(Sum.inr 5092, (1 / 1))]

def nodeValue5093 : Sparse Master := [(Sum.inr 2503, (-1 / 4)), (Sum.inr 3446, (-1 / 4))]

def nodeValue5094 : Sparse Master := [(Sum.inr 2504, (-1 / 2))]

def nodeValue5095 : Sparse Master := [(Sum.inr 2505, (-1 / 4)), (Sum.inr 3448, (-1 / 4))]

def nodeValue5097 : Sparse Master := [(Sum.inr 5097, (1 / 1))]

def nodeValue5098 : Sparse Master := [(Sum.inr 2508, (-1 / 4)), (Sum.inr 3460, (-1 / 4))]

def nodeValue5099 : Sparse Master := [(Sum.inr 2509, (-1 / 4)), (Sum.inr 2704, (-1 / 4))]

def nodeValue5100 : Sparse Master := []

def nodeValue5101 : Sparse Master := []

def nodeValue5102 : Sparse Master := [(Sum.inr 2512, (-1 / 4)), (Sum.inr 3471, (-1 / 4))]

def nodeValue5103 : Sparse Master := [(Sum.inr 5103, (1 / 1))]

def nodeValue5104 : Sparse Master := []

def nodeValue5105 : Sparse Master := [(Sum.inr 2515, (-1 / 4)), (Sum.inr 3479, (-1 / 4))]

def nodeValue5107 : Sparse Master := []

def nodeValue5109 : Sparse Master := [(Sum.inr 2519, (-1 / 4)), (Sum.inr 3486, (-1 / 4))]

def nodeValue5110 : Sparse Master := [(Sum.inr 2522, (-1 / 4)), (Sum.inr 2685, (-1 / 4))]

def nodeValue5111 : Sparse Master := []

def nodeValue5112 : Sparse Master := [(Sum.inr 5112, (1 / 1))]

def nodeValue5113 : Sparse Master := []

def nodeValue5114 : Sparse Master := [(Sum.inr 2896, (-1 / 4)), (Sum.inr 3597, (-1 / 4))]

def nodeValue5115 : Sparse Master := []

def nodeValue5116 : Sparse Master := [(Sum.inr 5116, (1 / 1))]

def nodeValue5117 : Sparse Master := [(Sum.inr 2893, (-1 / 4)), (Sum.inr 3599, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue512 : Sparse Master := []

def nodeValue513 : Sparse Master := [(Sum.inl 2, (-5 / 54)), (Sum.inl 3, (-10 / 27)), (Sum.inl 12, (-5 / 54)), (Sum.inl 4, (-10 / 27)), (Sum.inl 1, (10 / 27)), (Sum.inl 31, (5 / 9))]

def nodeValue514 : Sparse Master := [(Sum.inl 0, (31 / 864)), (Sum.inl 2, (5 / 288)), (Sum.inl 3, (5 / 54)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-5 / 216)), (Sum.inl 31, (-5 / 18))]

def nodeValue515 : Sparse Master := []

def nodeValue516 : Sparse Master := [(Sum.inl 0, (17 / 432)), (Sum.inl 2, (5 / 216)), (Sum.inl 1, (-5 / 144)), (Sum.inl 31, (5 / 9))]

def nodeValue517 : Sparse Master := [(Sum.inl 0, (17 / 288)), (Sum.inl 5, (-5 / 216)), (Sum.inl 6, (5 / 864)), (Sum.inl 2, (-5 / 72)), (Sum.inl 8, (-5 / 27)), (Sum.inl 27, (5 / 72)), (Sum.inl 1, (25 / 216)), (Sum.inl 30, (5 / 18))]

def nodeValue518 : Sparse Master := []

def nodeValue519 : Sparse Master := [(Sum.inl 0, (1 / 864)), (Sum.inl 2, (-25 / 432)), (Sum.inl 3, (-10 / 27)), (Sum.inl 26, (-5 / 54)), (Sum.inl 4, (-5 / 18)), (Sum.inl 1, (245 / 864)), (Sum.inl 31, (5 / 18))]

def nodeValue520 : Sparse Master := [(Sum.inl 0, (47 / 864)), (Sum.inl 2, (-55 / 864)), (Sum.inl 3, (-5 / 54)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (115 / 432))]

def nodeValue521 : Sparse Master := [(Sum.inl 0, (11 / 144)), (Sum.inl 2, (5 / 144)), (Sum.inl 1, (-5 / 72))]

def nodeValue522 : Sparse Master := [(Sum.inl 0, (5 / 288)), (Sum.inl 2, (-5 / 216)), (Sum.inl 3, (5 / 27)), (Sum.inl 26, (5 / 54)), (Sum.inl 1, (5 / 864))]

def nodeValue523 : Sparse Master := [(Sum.inl 0, (49 / 864)), (Sum.inl 2, (-5 / 864)), (Sum.inl 3, (5 / 54)), (Sum.inl 4, (5 / 27)), (Sum.inl 1, (-25 / 432))]

def nodeValue524 : Sparse Master := []

def nodeValue525 : Sparse Master := []

def nodeValue526 : Sparse Master := [(Sum.inl 0, (67 / 864)), (Sum.inl 4, (5 / 54)), (Sum.inl 1, (-25 / 288))]

def nodeValue527 : Sparse Master := [(Sum.inl 0, (1 / 18)), (Sum.inl 1, (5 / 18))]

def nodeValue528 : Sparse Master := [(Sum.inl 0, (23 / 432)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (-5 / 144))]

def nodeValue529 : Sparse Master := []

def nodeValue530 : Sparse Master := [(Sum.inl 0, (7 / 144)), (Sum.inl 4, (5 / 9)), (Sum.inl 1, (-5 / 48))]

def nodeValue531 : Sparse Master := [(Sum.inl 0, (79 / 432)), (Sum.inl 12, (-5 / 54)), (Sum.inl 1, (35 / 144))]

def nodeValue532 : Sparse Master := []

def nodeValue533 : Sparse Master := [(Sum.inl 0, (47 / 432)), (Sum.inl 4, (-5 / 27)), (Sum.inl 1, (35 / 144))]

def nodeValue535 : Sparse Master := [(Sum.inr 535, (1 / 1))]

def nodeValue536 : Sparse Master := [(Sum.inr 536, (1 / 1))]

def nodeValue537 : Sparse Master := [(Sum.inr 537, (1 / 1))]

def nodeValue538 : Sparse Master := [(Sum.inr 538, (1 / 1))]

def nodeValue539 : Sparse Master := [(Sum.inr 539, (1 / 1))]

def nodeValue540 : Sparse Master := [(Sum.inr 540, (1 / 1))]

def nodeValue541 : Sparse Master := [(Sum.inr 541, (1 / 1))]

def nodeValue542 : Sparse Master := [(Sum.inr 542, (1 / 1))]

def nodeValue543 : Sparse Master := [(Sum.inr 543, (1 / 1))]

def nodeValue544 : Sparse Master := [(Sum.inr 544, (1 / 1))]

def nodeValue545 : Sparse Master := [(Sum.inr 545, (1 / 1))]

def nodeValue546 : Sparse Master := [(Sum.inr 546, (1 / 1))]

def nodeValue547 : Sparse Master := [(Sum.inr 547, (1 / 1))]

def nodeValue548 : Sparse Master := [(Sum.inr 548, (1 / 1))]

def nodeValue549 : Sparse Master := [(Sum.inr 549, (1 / 1))]

def nodeValue550 : Sparse Master := [(Sum.inr 550, (1 / 1))]

def nodeValue552 : Sparse Master := [(Sum.inr 552, (1 / 1))]

def nodeValue554 : Sparse Master := [(Sum.inr 554, (1 / 1))]

def nodeValue555 : Sparse Master := [(Sum.inr 555, (1 / 1))]

def nodeValue556 : Sparse Master := [(Sum.inr 556, (1 / 1))]

def nodeValue557 : Sparse Master := [(Sum.inr 557, (1 / 1))]

def nodeValue559 : Sparse Master := [(Sum.inr 559, (1 / 1))]

def nodeValue561 : Sparse Master := []

def nodeValue562 : Sparse Master := [(Sum.inr 562, (1 / 1))]

def nodeValue563 : Sparse Master := [(Sum.inr 563, (1 / 1))]

def nodeValue564 : Sparse Master := [(Sum.inr 564, (1 / 1))]

def nodeValue566 : Sparse Master := [(Sum.inr 566, (1 / 1))]

def nodeValue567 : Sparse Master := [(Sum.inr 567, (1 / 1))]

def nodeValue568 : Sparse Master := [(Sum.inr 568, (1 / 1))]

def nodeValue569 : Sparse Master := [(Sum.inr 569, (1 / 1))]

def nodeValue570 : Sparse Master := [(Sum.inr 570, (1 / 1))]

def nodeValue571 : Sparse Master := [(Sum.inr 571, (1 / 1))]

def nodeValue572 : Sparse Master := [(Sum.inr 572, (1 / 1))]

def nodeValue573 : Sparse Master := [(Sum.inr 573, (1 / 1))]

def nodeValue574 : Sparse Master := [(Sum.inr 574, (1 / 1))]

def nodeValue575 : Sparse Master := [(Sum.inr 575, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue5123 : Sparse Master := [(Sum.inr 2536, (-1 / 4)), (Sum.inr 3370, (-1 / 4))]

def nodeValue5125 : Sparse Master := [(Sum.inr 2539, (-1 / 4)), (Sum.inr 3372, (-1 / 4))]

def nodeValue5126 : Sparse Master := [(Sum.inr 2541, (-1 / 4)), (Sum.inr 3487, (-1 / 4))]

def nodeValue5127 : Sparse Master := []

def nodeValue5128 : Sparse Master := [(Sum.inr 5128, (1 / 1))]

def nodeValue5129 : Sparse Master := [(Sum.inr 5129, (1 / 1))]

def nodeValue5130 : Sparse Master := []

def nodeValue5132 : Sparse Master := [(Sum.inr 5132, (1 / 1))]

def nodeValue5133 : Sparse Master := []

def nodeValue5134 : Sparse Master := [(Sum.inr 2553, (-1 / 4)), (Sum.inr 3514, (-1 / 4))]

def nodeValue5135 : Sparse Master := []

def nodeValue5137 : Sparse Master := [(Sum.inr 2556, (-1 / 4)), (Sum.inr 3521, (-1 / 4))]

def nodeValue5138 : Sparse Master := [(Sum.inr 5138, (1 / 1))]

def nodeValue5139 : Sparse Master := [(Sum.inr 5139, (1 / 1))]

def nodeValue5140 : Sparse Master := [(Sum.inr 5140, (1 / 1))]

def nodeValue5141 : Sparse Master := [(Sum.inr 2561, (-1 / 4)), (Sum.inr 3522, (-1 / 4))]

def nodeValue5142 : Sparse Master := [(Sum.inr 2913, (-1 / 4)), (Sum.inr 3610, (-1 / 4))]

def nodeValue5144 : Sparse Master := [(Sum.inr 5144, (1 / 1))]

def nodeValue5145 : Sparse Master := [(Sum.inr 5145, (1 / 1))]

def nodeValue5146 : Sparse Master := [(Sum.inr 5146, (1 / 1))]

def nodeValue5147 : Sparse Master := [(Sum.inr 5147, (1 / 1))]

def nodeValue5148 : Sparse Master := []

def nodeValue5149 : Sparse Master := [(Sum.inr 2924, (-1 / 4)), (Sum.inr 3605, (-1 / 4))]

def nodeValue5150 : Sparse Master := [(Sum.inr 5150, (1 / 1))]

def nodeValue5151 : Sparse Master := [(Sum.inr 5151, (1 / 1))]

def nodeValue5152 : Sparse Master := [(Sum.inr 2931, (-1 / 4)), (Sum.inr 3612, (-1 / 4))]

def nodeValue5155 : Sparse Master := [(Sum.inr 2908, (-1 / 4)), (Sum.inr 3600, (-1 / 4))]

def nodeValue5156 : Sparse Master := [(Sum.inr 2911, (-1 / 4)), (Sum.inr 3611, (-1 / 4))]

def nodeValue5160 : Sparse Master := [(Sum.inr 5160, (1 / 1))]

def nodeValue5161 : Sparse Master := [(Sum.inr 5161, (1 / 1))]

def nodeValue5162 : Sparse Master := [(Sum.inr 2589, (-1 / 4)), (Sum.inr 3563, (-1 / 4))]

def nodeValue5163 : Sparse Master := [(Sum.inr 2590, (-1 / 4)), (Sum.inr 3564, (-1 / 4))]

def nodeValue5164 : Sparse Master := [(Sum.inr 5164, (1 / 1))]

def nodeValue5166 : Sparse Master := []

def nodeValue5167 : Sparse Master := [(Sum.inl 0, (49 / 17280)), (Sum.inl 6, (1 / 1152)), (Sum.inl 2, (-11 / 1728)), (Sum.inl 7, (-1 / 216)), (Sum.inl 8, (-1 / 108)), (Sum.inl 3, (-1 / 108)), (Sum.inl 1, (-7 / 1728)), (Sum.inr 3602, (-1 / 4))]

def nodeValue5168 : Sparse Master := [(Sum.inl 0, (19 / 8640)), (Sum.inl 6, (-1 / 3456)), (Sum.inl 2, (-1 / 3456)), (Sum.inl 7, (1 / 216)), (Sum.inl 3, (1 / 216)), (Sum.inl 1, (19 / 1728)), (Sum.inr 3603, (-1 / 4))]

def nodeValue5169 : Sparse Master := [(Sum.inl 0, (47 / 17280)), (Sum.inl 6, (-1 / 3456)), (Sum.inl 2, (1 / 576)), (Sum.inl 8, (1 / 216)), (Sum.inl 1, (-1 / 864)), (Sum.inr 3607, (-1 / 4))]

def nodeValue5170 : Sparse Master := [(Sum.inr 2954, (-1 / 4)), (Sum.inr 3606, (-1 / 4))]

def nodeValue5171 : Sparse Master := [(Sum.inl 0, (19 / 8640)), (Sum.inl 5, (1 / 432)), (Sum.inl 6, (1 / 1728)), (Sum.inl 1, (5 / 432)), (Sum.inr 3608, (-1 / 4))]

def nodeValue5172 : Sparse Master := [(Sum.inl 0, (37 / 17280)), (Sum.inl 6, (-1 / 3456)), (Sum.inl 2, (5 / 1728)), (Sum.inl 7, (1 / 216)), (Sum.inl 3, (1 / 108)), (Sum.inl 1, (-7 / 1728)), (Sum.inr 3613, (-1 / 4))]

def nodeValue5173 : Sparse Master := [(Sum.inr 5173, (1 / 1))]

def nodeValue5174 : Sparse Master := [(Sum.inl 0, (19 / 8640)), (Sum.inl 5, (1 / 432)), (Sum.inl 6, (1 / 1728)), (Sum.inl 2, (-1 / 288)), (Sum.inl 1, (-5 / 864)), (Sum.inr 3615, (-1 / 4))]

def nodeValue5175 : Sparse Master := [(Sum.inr 5175, (1 / 1))]

def nodeValue5176 : Sparse Master := [(Sum.inl 0, (1 / 576)), (Sum.inl 5, (-1 / 432)), (Sum.inl 2, (1 / 1728)), (Sum.inl 7, (-1 / 108)), (Sum.inl 3, (-1 / 108)), (Sum.inl 1, (7 / 864)), (Sum.inr 3614, (-1 / 4))]

def nodeValue5177 : Sparse Master := [(Sum.inl 0, (1 / 360)), (Sum.inl 5, (-1 / 432)), (Sum.inl 8, (-1 / 108)), (Sum.inl 1, (-1 / 432)), (Sum.inr 3616, (-1 / 4))]

def nodeValue5181 : Sparse Master := [(Sum.inr 5181, (1 / 1))]

def nodeValue5183 : Sparse Master := [(Sum.inr 5183, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue5184 : Sparse Master := [(Sum.inr 5184, (1 / 1))]

def nodeValue5185 : Sparse Master := [(Sum.inr 5185, (1 / 1))]

def nodeValue5187 : Sparse Master := [(Sum.inr 5187, (1 / 1))]

def nodeValue5188 : Sparse Master := [(Sum.inr 5188, (1 / 1))]

def nodeValue5189 : Sparse Master := [(Sum.inr 5189, (1 / 1))]

def nodeValue5192 : Sparse Master := [(Sum.inr 2853, (-1 / 4)), (Sum.inr 3620, (-1 / 4))]

def nodeValue5193 : Sparse Master := [(Sum.inr 2856, (-1 / 4)), (Sum.inr 3630, (-1 / 4))]

def nodeValue5197 : Sparse Master := [(Sum.inr 5197, (1 / 1))]

def nodeValue5198 : Sparse Master := [(Sum.inr 5198, (1 / 1))]

def nodeValue5199 : Sparse Master := [(Sum.inr 5199, (1 / 1))]

def nodeValue5201 : Sparse Master := [(Sum.inr 5201, (1 / 1))]

def nodeValue5202 : Sparse Master := [(Sum.inr 2880, (-1 / 4)), (Sum.inr 3617, (-1 / 4))]

def nodeValue5203 : Sparse Master := [(Sum.inr 2884, (-1 / 4)), (Sum.inr 3621, (-1 / 4))]

def nodeValue5204 : Sparse Master := [(Sum.inr 2881, (-1 / 4)), (Sum.inr 3624, (-1 / 4))]

def nodeValue5205 : Sparse Master := [(Sum.inr 5205, (1 / 1))]

def nodeValue5206 : Sparse Master := [(Sum.inr 5206, (1 / 1))]

def nodeValue5207 : Sparse Master := [(Sum.inr 2889, (-1 / 4)), (Sum.inr 3631, (-1 / 4))]

def nodeValue5215 : Sparse Master := [(Sum.inr 5215, (1 / 1))]

def nodeValue5216 : Sparse Master := [(Sum.inr 5216, (1 / 1))]

def nodeValue5217 : Sparse Master := [(Sum.inr 5217, (1 / 1))]

def nodeValue5219 : Sparse Master := [(Sum.inr 5219, (1 / 1))]

def nodeValue5220 : Sparse Master := [(Sum.inr 5220, (1 / 1))]

def nodeValue5222 : Sparse Master := [(Sum.inr 5222, (1 / 1))]

def nodeValue5223 : Sparse Master := [(Sum.inr 5223, (1 / 1))]

def nodeValue5226 : Sparse Master := [(Sum.inr 5226, (1 / 1))]

def nodeValue5227 : Sparse Master := [(Sum.inr 2671, (-1 / 4)), (Sum.inr 3390, (-1 / 4))]

def nodeValue5228 : Sparse Master := [(Sum.inr 2672, (-1 / 4)), (Sum.inr 3391, (-1 / 4))]

def nodeValue5229 : Sparse Master := [(Sum.inr 5229, (1 / 1))]

def nodeValue5230 : Sparse Master := [(Sum.inr 5230, (1 / 1))]

def nodeValue5231 : Sparse Master := [(Sum.inr 5231, (1 / 1))]

def nodeValue5232 : Sparse Master := [(Sum.inr 5232, (1 / 1))]

def nodeValue5233 : Sparse Master := [(Sum.inr 5233, (1 / 1))]

def nodeValue5235 : Sparse Master := [(Sum.inr 5235, (1 / 1))]

def nodeValue5236 : Sparse Master := [(Sum.inr 5236, (1 / 1))]

def nodeValue5237 : Sparse Master := [(Sum.inr 2684, (-1 / 4)), (Sum.inr 3394, (-1 / 4))]

def nodeValue5238 : Sparse Master := [(Sum.inr 2686, (-1 / 4)), (Sum.inr 3397, (-1 / 4))]

def nodeValue5239 : Sparse Master := []

def nodeValue5241 : Sparse Master := [(Sum.inr 2694, (-1 / 4)), (Sum.inr 3493, (-1 / 4))]

def nodeValue5242 : Sparse Master := []

def nodeValue5243 : Sparse Master := [(Sum.inr 5243, (1 / 1))]

def nodeValue5244 : Sparse Master := [(Sum.inr 5244, (1 / 1))]

def nodeValue5246 : Sparse Master := []

def nodeValue5247 : Sparse Master := [(Sum.inr 2703, (-1 / 4)), (Sum.inr 3496, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue5248 : Sparse Master := [(Sum.inr 2705, (-1 / 4)), (Sum.inr 3498, (-1 / 4))]

def nodeValue5249 : Sparse Master := [(Sum.inr 5249, (1 / 1))]

def nodeValue5250 : Sparse Master := []

def nodeValue5251 : Sparse Master := [(Sum.inr 5251, (1 / 1))]

def nodeValue5252 : Sparse Master := [(Sum.inr 5252, (1 / 1))]

def nodeValue5253 : Sparse Master := [(Sum.inr 5253, (1 / 1))]

def nodeValue5254 : Sparse Master := [(Sum.inr 5254, (1 / 1))]

def nodeValue5255 : Sparse Master := [(Sum.inr 5255, (1 / 1))]

def nodeValue5256 : Sparse Master := []

def nodeValue5257 : Sparse Master := [(Sum.inr 2721, (-1 / 4)), (Sum.inr 3532, (-1 / 4))]

def nodeValue5258 : Sparse Master := [(Sum.inr 2722, (-1 / 4)), (Sum.inr 3533, (-1 / 4))]

def nodeValue5259 : Sparse Master := [(Sum.inr 2723, (-1 / 4)), (Sum.inr 3544, (-1 / 4))]

def nodeValue5260 : Sparse Master := [(Sum.inr 5260, (1 / 1))]

def nodeValue5261 : Sparse Master := [(Sum.inr 2726, (-1 / 4)), (Sum.inr 3545, (-1 / 4))]

def nodeValue5262 : Sparse Master := [(Sum.inr 5262, (1 / 1))]

def nodeValue5263 : Sparse Master := [(Sum.inr 5263, (1 / 1))]

def nodeValue5264 : Sparse Master := [(Sum.inr 5264, (1 / 1))]

def nodeValue5265 : Sparse Master := [(Sum.inr 5265, (1 / 1))]

def nodeValue5266 : Sparse Master := [(Sum.inr 5266, (1 / 1))]

def nodeValue5267 : Sparse Master := [(Sum.inr 5267, (1 / 1))]

def nodeValue5268 : Sparse Master := [(Sum.inr 5268, (1 / 1))]

def nodeValue5269 : Sparse Master := [(Sum.inr 5269, (1 / 1))]

def nodeValue5270 : Sparse Master := [(Sum.inr 5270, (1 / 1))]

def nodeValue5271 : Sparse Master := [(Sum.inr 2739, (-1 / 4)), (Sum.inr 3534, (-1 / 4))]

def nodeValue5272 : Sparse Master := [(Sum.inr 2740, (-1 / 2))]

def nodeValue5273 : Sparse Master := []

def nodeValue5274 : Sparse Master := []

def nodeValue5275 : Sparse Master := [(Sum.inr 2743, (-1 / 4)), (Sum.inr 3548, (-1 / 4))]

def nodeValue5276 : Sparse Master := [(Sum.inr 5276, (1 / 1))]

def nodeValue5277 : Sparse Master := [(Sum.inr 5277, (1 / 1))]

def nodeValue5278 : Sparse Master := [(Sum.inr 5278, (1 / 1))]

def nodeValue5279 : Sparse Master := [(Sum.inr 5279, (1 / 1))]

def nodeValue5281 : Sparse Master := [(Sum.inr 5281, (1 / 1))]

def nodeValue5282 : Sparse Master := [(Sum.inr 5282, (1 / 1))]

def nodeValue5283 : Sparse Master := []

def nodeValue5284 : Sparse Master := [(Sum.inr 3077, (-1 / 4)), (Sum.inr 3625, (-1 / 4))]

def nodeValue5286 : Sparse Master := [(Sum.inr 5286, (1 / 1))]

def nodeValue5287 : Sparse Master := [(Sum.inr 5287, (1 / 1))]

def nodeValue5288 : Sparse Master := [(Sum.inr 5288, (1 / 1))]

def nodeValue5289 : Sparse Master := [(Sum.inr 5289, (1 / 1))]

def nodeValue5290 : Sparse Master := [(Sum.inr 2764, (-1 / 4)), (Sum.inr 3581, (-1 / 4))]

def nodeValue5291 : Sparse Master := [(Sum.inr 2765, (-1 / 4)), (Sum.inr 3582, (-1 / 4))]

def nodeValue5292 : Sparse Master := [(Sum.inl 0, (47 / 17280)), (Sum.inl 2, (11 / 3456)), (Sum.inl 3, (1 / 216)), (Sum.inl 1, (-1 / 864)), (Sum.inr 3622, (-1 / 4))]

def nodeValue5293 : Sparse Master := [(Sum.inl 0, (1 / 360)), (Sum.inl 2, (-1 / 288)), (Sum.inl 1, (-1 / 288)), (Sum.inr 3627, (-1 / 4))]

def nodeValue5294 : Sparse Master := [(Sum.inl 0, (19 / 8640)), (Sum.inl 2, (-5 / 1728)), (Sum.inl 3, (-1 / 108)), (Sum.inl 1, (-1 / 216)), (Sum.inr 3632, (-1 / 4))]

def nodeValue5295 : Sparse Master := [(Sum.inr 5295, (1 / 1))]

def nodeValue5296 : Sparse Master := [(Sum.inl 0, (1 / 480)), (Sum.inl 2, (1 / 96)), (Sum.inr 3634, (-1 / 4))]

def nodeValue5297 : Sparse Master := [(Sum.inr 5297, (1 / 1))]

def nodeValue5299 : Sparse Master := [(Sum.inr 5299, (1 / 1))]

def nodeValue5300 : Sparse Master := [(Sum.inr 5300, (1 / 1))]

def nodeValue5301 : Sparse Master := [(Sum.inr 3053, (-1 / 4)), (Sum.inr 3619, (-1 / 4))]

def nodeValue5302 : Sparse Master := [(Sum.inr 3054, (-1 / 4)), (Sum.inr 3626, (-1 / 4))]

def nodeValue5303 : Sparse Master := [(Sum.inr 5303, (1 / 1))]

def nodeValue5304 : Sparse Master := [(Sum.inr 2782, (-1 / 4)), (Sum.inr 3583, (-1 / 4))]

def nodeValue5305 : Sparse Master := [(Sum.inr 2783, (-1 / 2))]

def nodeValue5306 : Sparse Master := [(Sum.inl 0, (19 / 8640)), (Sum.inl 2, (1 / 1728)), (Sum.inl 3, (-1 / 108)), (Sum.inl 1, (11 / 864)), (Sum.inr 3623, (-1 / 4))]

def nodeValue5307 : Sparse Master := []

def nodeValue5308 : Sparse Master := []

def nodeValue5309 : Sparse Master := []

def nodeValue5310 : Sparse Master := [(Sum.inl 0, (1 / 576)), (Sum.inl 2, (-1 / 576)), (Sum.inl 3, (1 / 36)), (Sum.inl 1, (1 / 288)), (Sum.inr 3633, (-1 / 4))]

def nodeValue5311 : Sparse Master := [(Sum.inr 5311, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue5312 : Sparse Master := []

def nodeValue5314 : Sparse Master := []

def nodeValue5323 : Sparse Master := []

def nodeValue5327 : Sparse Master := []

def nodeValue5328 : Sparse Master := [(Sum.inr 3659, (-1 / 2))]

def nodeValue5329 : Sparse Master := [(Sum.inr 3660, (-1 / 2))]

def nodeValue5332 : Sparse Master := []

def nodeValue5333 : Sparse Master := [(Sum.inr 3668, (-1 / 4)), (Sum.inr 3677, (-1 / 4))]

def nodeValue5335 : Sparse Master := [(Sum.inr 3670, (-1 / 4)), (Sum.inr 3753, (-1 / 4))]

def nodeValue5336 : Sparse Master := [(Sum.inr 3671, (-1 / 4)), (Sum.inr 3754, (-1 / 4))]

def nodeValue5337 : Sparse Master := [(Sum.inr 3672, (-1 / 4)), (Sum.inr 3756, (-1 / 4))]

def nodeValue5338 : Sparse Master := [(Sum.inr 5338, (1 / 1))]

def nodeValue5339 : Sparse Master := [(Sum.inr 5339, (1 / 1))]

def nodeValue5340 : Sparse Master := [(Sum.inr 5340, (1 / 1))]

def nodeValue5341 : Sparse Master := [(Sum.inr 3678, (-1 / 4)), (Sum.inr 3744, (-1 / 4))]

def nodeValue5344 : Sparse Master := [(Sum.inr 3681, (-1 / 2))]

def nodeValue5345 : Sparse Master := []

def nodeValue5346 : Sparse Master := [(Sum.inr 3683, (-1 / 4)), (Sum.inr 3746, (-1 / 4))]

def nodeValue5348 : Sparse Master := [(Sum.inr 5348, (1 / 1))]

def nodeValue5349 : Sparse Master := [(Sum.inr 3687, (-1 / 4)), (Sum.inr 3749, (-1 / 4))]

def nodeValue5350 : Sparse Master := [(Sum.inr 5350, (1 / 1))]

def nodeValue5351 : Sparse Master := [(Sum.inr 3689, (-1 / 4)), (Sum.inr 3757, (-1 / 4))]

def nodeValue5352 : Sparse Master := [(Sum.inr 3690, (-1 / 4)), (Sum.inr 3764, (-1 / 4))]

def nodeValue5353 : Sparse Master := [(Sum.inr 5353, (1 / 1))]

def nodeValue5354 : Sparse Master := [(Sum.inr 3692, (-1 / 4)), (Sum.inr 3769, (-1 / 4))]

def nodeValue5355 : Sparse Master := [(Sum.inr 3693, (-1 / 4)), (Sum.inr 3770, (-1 / 4))]

def nodeValue5356 : Sparse Master := [(Sum.inr 3694, (-1 / 4)), (Sum.inr 3773, (-1 / 4))]

def nodeValue5357 : Sparse Master := [(Sum.inr 5357, (1 / 1))]

def nodeValue5358 : Sparse Master := [(Sum.inr 5358, (1 / 1))]

def nodeValue5359 : Sparse Master := [(Sum.inr 5359, (1 / 1))]

def nodeValue5360 : Sparse Master := [(Sum.inr 5360, (1 / 1))]

def nodeValue5361 : Sparse Master := [(Sum.inr 5361, (1 / 1))]

def nodeValue5362 : Sparse Master := [(Sum.inr 5362, (1 / 1))]

def nodeValue5363 : Sparse Master := [(Sum.inr 3701, (-1 / 4)), (Sum.inr 3751, (-1 / 4))]

def nodeValue5364 : Sparse Master := [(Sum.inr 3702, (-1 / 2))]

def nodeValue5365 : Sparse Master := [(Sum.inr 3703, (-1 / 4)), (Sum.inr 3758, (-1 / 4))]

def nodeValue5366 : Sparse Master := []

def nodeValue5367 : Sparse Master := []

def nodeValue5368 : Sparse Master := [(Sum.inr 3705, (-1 / 4)), (Sum.inr 3767, (-1 / 4))]

def nodeValue5369 : Sparse Master := []

def nodeValue5370 : Sparse Master := [(Sum.inr 3706, (-1 / 4)), (Sum.inr 3771, (-1 / 4))]

def nodeValue5371 : Sparse Master := []

def nodeValue5372 : Sparse Master := [(Sum.inr 3708, (-1 / 4)), (Sum.inr 3791, (-1 / 4))]

def nodeValue5373 : Sparse Master := [(Sum.inr 3709, (-1 / 4)), (Sum.inr 3792, (-1 / 4))]

def nodeValue5374 : Sparse Master := [(Sum.inr 3713, (-1 / 2))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue5376 : Sparse Master := [(Sum.inr 5376, (1 / 1))]

def nodeValue5377 : Sparse Master := [(Sum.inr 5377, (1 / 1))]

def nodeValue5378 : Sparse Master := [(Sum.inr 3719, (-1 / 4)), (Sum.inr 3795, (-1 / 4))]

def nodeValue5379 : Sparse Master := [(Sum.inr 5379, (1 / 1))]

def nodeValue5380 : Sparse Master := [(Sum.inr 3721, (-1 / 4)), (Sum.inr 3836, (-1 / 4))]

def nodeValue5381 : Sparse Master := [(Sum.inr 5381, (1 / 1))]

def nodeValue5382 : Sparse Master := [(Sum.inr 5382, (1 / 1))]

def nodeValue5383 : Sparse Master := [(Sum.inr 3731, (-1 / 4)), (Sum.inr 3867, (-1 / 4))]

def nodeValue5384 : Sparse Master := [(Sum.inr 3732, (-1 / 4)), (Sum.inr 3811, (-1 / 4))]

def nodeValue5385 : Sparse Master := [(Sum.inr 5385, (1 / 1))]

def nodeValue5386 : Sparse Master := [(Sum.inl 0, (19 / 8640)), (Sum.inl 5, (-1 / 288)), (Sum.inl 2, (1 / 432)), (Sum.inl 7, (-1 / 72)), (Sum.inl 3, (-1 / 27)), (Sum.inl 23, (1 / 72)), (Sum.inl 24, (1 / 36)), (Sum.inl 12, (-1 / 108)), (Sum.inl 4, (-1 / 54)), (Sum.inl 27, (1 / 96)), (Sum.inl 1, (1 / 1728)), (Sum.inr 3890, (-1 / 4))]

def nodeValue5387 : Sparse Master := [(Sum.inl 0, (1 / 576)), (Sum.inl 5, (1 / 864)), (Sum.inl 2, (-1 / 1728)), (Sum.inl 7, (1 / 216)), (Sum.inl 3, (1 / 108)), (Sum.inl 23, (-1 / 72)), (Sum.inl 12, (1 / 216)), (Sum.inl 27, (-1 / 288)), (Sum.inl 1, (1 / 144)), (Sum.inr 3891, (-1 / 4))]

def nodeValue5388 : Sparse Master := [(Sum.inl 0, (13 / 5760)), (Sum.inl 5, (1 / 864)), (Sum.inl 2, (-1 / 1728)), (Sum.inl 7, (1 / 216)), (Sum.inl 3, (1 / 108)), (Sum.inl 24, (-1 / 72)), (Sum.inl 4, (1 / 216)), (Sum.inl 27, (-1 / 288)), (Sum.inl 1, (-7 / 1152)), (Sum.inr 3892, (-1 / 4))]

def nodeValue5389 : Sparse Master := [(Sum.inl 0, (1 / 720)), (Sum.inl 23, (1 / 36)), (Sum.inl 27, (1 / 144)), (Sum.inl 1, (1 / 72)), (Sum.inr 3893, (-1 / 4))]

def nodeValue5390 : Sparse Master := [(Sum.inl 0, (1 / 480)), (Sum.inl 24, (1 / 36)), (Sum.inl 27, (1 / 144)), (Sum.inl 1, (-1 / 288)), (Sum.inr 3894, (-1 / 4))]

def nodeValue5391 : Sparse Master := [(Sum.inr 3776, (-1 / 4)), (Sum.inr 3778, (-1 / 4))]

def nodeValue5392 : Sparse Master := []

def nodeValue5393 : Sparse Master := [(Sum.inr 3779, (-1 / 4)), (Sum.inr 3797, (-1 / 4))]

def nodeValue5394 : Sparse Master := []

def nodeValue5395 : Sparse Master := [(Sum.inr 3781, (-1 / 4)), (Sum.inr 3794, (-1 / 4))]

def nodeValue5396 : Sparse Master := []

def nodeValue5397 : Sparse Master := [(Sum.inr 3782, (-1 / 4)), (Sum.inr 3796, (-1 / 4))]

def nodeValue5398 : Sparse Master := [(Sum.inr 3784, (-1 / 2))]

def nodeValue5399 : Sparse Master := [(Sum.inr 5399, (1 / 1))]

def nodeValue5400 : Sparse Master := [(Sum.inr 3786, (-1 / 4)), (Sum.inr 3799, (-1 / 4))]

def nodeValue5401 : Sparse Master := [(Sum.inr 3787, (-1 / 4)), (Sum.inr 3804, (-1 / 4))]

def nodeValue5402 : Sparse Master := [(Sum.inr 5402, (1 / 1))]

def nodeValue5403 : Sparse Master := [(Sum.inr 3789, (-1 / 4)), (Sum.inr 3810, (-1 / 4))]

def nodeValue5404 : Sparse Master := [(Sum.inr 3790, (-1 / 4)), (Sum.inr 3815, (-1 / 4))]

def nodeValue5405 : Sparse Master := [(Sum.inr 3800, (-1 / 4)), (Sum.inr 3805, (-1 / 4))]

def nodeValue5406 : Sparse Master := [(Sum.inr 3801, (-1 / 4)), (Sum.inr 3812, (-1 / 4))]

def nodeValue5407 : Sparse Master := [(Sum.inr 5407, (1 / 1))]

def nodeValue5408 : Sparse Master := []

def nodeValue5409 : Sparse Master := []

def nodeValue5410 : Sparse Master := []

def nodeValue5411 : Sparse Master := [(Sum.inr 3809, (-1 / 4)), (Sum.inr 3813, (-1 / 4))]

def nodeValue5412 : Sparse Master := [(Sum.inr 3814, (-1 / 2))]

def nodeValue5413 : Sparse Master := []

def nodeValue5414 : Sparse Master := [(Sum.inr 5414, (1 / 1))]

def nodeValue5415 : Sparse Master := [(Sum.inl 0, (43 / 17280)), (Sum.inl 5, (-1 / 864)), (Sum.inl 6, (1 / 3456)), (Sum.inl 2, (1 / 864)), (Sum.inl 7, (-1 / 108)), (Sum.inl 3, (-1 / 54)), (Sum.inl 23, (1 / 72)), (Sum.inl 12, (-1 / 108)), (Sum.inl 27, (1 / 288)), (Sum.inl 1, (11 / 864)), (Sum.inr 3895, (-1 / 4))]

def nodeValue5416 : Sparse Master := [(Sum.inl 0, (23 / 8640)), (Sum.inl 5, (-1 / 864)), (Sum.inl 6, (1 / 3456)), (Sum.inl 2, (-1 / 384)), (Sum.inl 7, (-1 / 216)), (Sum.inl 8, (-1 / 216)), (Sum.inl 3, (-1 / 72)), (Sum.inl 24, (1 / 72)), (Sum.inl 4, (-1 / 108)), (Sum.inl 27, (1 / 288)), (Sum.inl 1, (-1 / 864)), (Sum.inr 3896, (-1 / 4))]

def nodeValue5417 : Sparse Master := [(Sum.inl 0, (41 / 17280)), (Sum.inl 5, (-1 / 864)), (Sum.inl 6, (1 / 3456)), (Sum.inl 2, (-1 / 216)), (Sum.inl 7, (-1 / 108)), (Sum.inl 3, (-1 / 27)), (Sum.inl 23, (1 / 72)), (Sum.inl 12, (-5 / 216)), (Sum.inl 27, (1 / 288)), (Sum.inl 1, (1 / 192)), (Sum.inr 3897, (-1 / 4))]

def nodeValue5418 : Sparse Master := [(Sum.inl 0, (1 / 360)), (Sum.inl 5, (1 / 864)), (Sum.inl 8, (1 / 216)), (Sum.inl 24, (-1 / 72)), (Sum.inl 27, (-1 / 288)), (Sum.inl 1, (-1 / 432)), (Sum.inr 3898, (-1 / 4))]

def nodeValue5419 : Sparse Master := [(Sum.inr 5419, (1 / 1))]

def nodeValue5420 : Sparse Master := [(Sum.inr 5420, (1 / 1))]

def nodeValue5421 : Sparse Master := [(Sum.inr 5421, (1 / 1))]

def nodeValue5422 : Sparse Master := [(Sum.inr 3900, (-1 / 4)), (Sum.inr 3964, (-1 / 4))]

def nodeValue5423 : Sparse Master := [(Sum.inr 3837, (-1 / 2))]

def nodeValue5424 : Sparse Master := [(Sum.inr 3838, (-1 / 4)), (Sum.inr 3843, (-1 / 4))]

def nodeValue5425 : Sparse Master := [(Sum.inr 5425, (1 / 1))]

def nodeValue5426 : Sparse Master := [(Sum.inr 5426, (1 / 1))]

def nodeValue5427 : Sparse Master := []

def nodeValue5428 : Sparse Master := [(Sum.inr 3845, (-1 / 2))]

def nodeValue5429 : Sparse Master := [(Sum.inr 5429, (1 / 1))]

def nodeValue5430 : Sparse Master := [(Sum.inr 5430, (1 / 1))]

def nodeValue5431 : Sparse Master := [(Sum.inr 3849, (-1 / 4)), (Sum.inr 3875, (-1 / 4))]

def nodeValue5432 : Sparse Master := [(Sum.inr 3850, (-1 / 2))]

def nodeValue5433 : Sparse Master := [(Sum.inl 0, (29 / 17280)), (Sum.inl 2, (-1 / 384)), (Sum.inl 3, (-1 / 72)), (Sum.inl 12, (-1 / 108)), (Sum.inl 4, (-1 / 108)), (Sum.inl 1, (1 / 192)), (Sum.inr 3901, (-1 / 4))]

def nodeValue5434 : Sparse Master := [(Sum.inl 0, (1 / 360)), (Sum.inl 2, (5 / 3456)), (Sum.inl 3, (1 / 216)), (Sum.inl 4, (1 / 216)), (Sum.inl 1, (-7 / 3456)), (Sum.inr 3903, (-1 / 4))]

def nodeValue5435 : Sparse Master := [(Sum.inl 0, (1 / 480)), (Sum.inl 2, (1 / 864)), (Sum.inl 3, (1 / 108)), (Sum.inl 12, (1 / 108)), (Sum.inl 1, (-1 / 108)), (Sum.inr 3906, (-1 / 4))]

def nodeValue5436 : Sparse Master := [(Sum.inr 5436, (1 / 1))]

def nodeValue5437 : Sparse Master := [(Sum.inr 3899, (-1 / 2))]

def nodeValue5438 : Sparse Master := [(Sum.inr 3857, (-1 / 4)), (Sum.inr 3876, (-1 / 4))]

def nodeValue5439 : Sparse Master := [(Sum.inl 0, (11 / 5760)), (Sum.inl 2, (-1 / 3456)), (Sum.inl 3, (1 / 216)), (Sum.inl 12, (1 / 216)), (Sum.inl 1, (19 / 1728)), (Sum.inr 3902, (-1 / 4))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue5440 : Sparse Master := []

def nodeValue5441 : Sparse Master := []

def nodeValue5442 : Sparse Master := []

def nodeValue5443 : Sparse Master := [(Sum.inl 0, (1 / 576)), (Sum.inl 2, (1 / 1728)), (Sum.inl 3, (-1 / 108)), (Sum.inl 12, (-1 / 108)), (Sum.inl 1, (5 / 864)), (Sum.inr 3907, (-1 / 4))]

def nodeValue5445 : Sparse Master := [(Sum.inr 5445, (1 / 1))]

def nodeValue5446 : Sparse Master := [(Sum.inr 5446, (1 / 1))]

def nodeValue5447 : Sparse Master := [(Sum.inr 3909, (-1 / 4)), (Sum.inr 4025, (-1 / 4))]

def nodeValue5448 : Sparse Master := [(Sum.inr 3885, (-1 / 2))]

def nodeValue5449 : Sparse Master := [(Sum.inr 3886, (-1 / 2))]

def nodeValue5450 : Sparse Master := [(Sum.inl 0, (17 / 8640)), (Sum.inl 2, (-1 / 1728)), (Sum.inl 3, (1 / 108)), (Sum.inl 12, (1 / 216)), (Sum.inl 4, (1 / 108)), (Sum.inl 1, (-5 / 864)), (Sum.inr 3910, (-1 / 4))]

def nodeValue5451 : Sparse Master := [(Sum.inl 0, (1 / 480)), (Sum.inl 2, (1 / 1728)), (Sum.inl 3, (-1 / 108)), (Sum.inl 4, (-1 / 108)), (Sum.inl 1, (-5 / 1728)), (Sum.inr 3913, (-1 / 4))]

def nodeValue5452 : Sparse Master := [(Sum.inl 0, (7 / 864)), (Sum.inl 12, (1 / 108)), (Sum.inl 1, (-5 / 288))]

def nodeValue5453 : Sparse Master := [(Sum.inl 0, (1 / 216)), (Sum.inl 12, (-1 / 54)), (Sum.inl 1, (1 / 72))]

def nodeValue5454 : Sparse Master := []

def nodeValue5455 : Sparse Master := []

def nodeValue5456 : Sparse Master := [(Sum.inl 0, (1 / 360)), (Sum.inl 12, (1 / 18)), (Sum.inl 1, (1 / 24))]

def nodeValue5457 : Sparse Master := []

def nodeValue5458 : Sparse Master := []

def nodeValue5459 : Sparse Master := []

def nodeValue5460 : Sparse Master := []

def nodeValue5461 : Sparse Master := [(Sum.inr 5461, (1 / 1))]

def nodeValue5462 : Sparse Master := []

def nodeValue5463 : Sparse Master := [(Sum.inr 5463, (1 / 1))]

def nodeValue5464 : Sparse Master := [(Sum.inl 0, (13 / 4320)), (Sum.inl 5, (-1 / 288)), (Sum.inl 8, (-1 / 72)), (Sum.inl 24, (1 / 72)), (Sum.inl 27, (1 / 96)), (Sum.inl 1, (1 / 864)), (Sum.inl 30, (1 / 36)), (Sum.inr 4041, (-1 / 4))]

def nodeValue5465 : Sparse Master := [(Sum.inl 0, (1 / 270)), (Sum.inl 5, (1 / 864)), (Sum.inl 8, (1 / 216)), (Sum.inl 27, (-1 / 288)), (Sum.inl 1, (1 / 432)), (Sum.inl 30, (-1 / 72)), (Sum.inr 4042, (-1 / 4))]

def nodeValue5466 : Sparse Master := [(Sum.inl 0, (13 / 4320)), (Sum.inl 27, (1 / 144)), (Sum.inl 1, (1 / 864)), (Sum.inl 30, (1 / 36)), (Sum.inr 4043, (-1 / 4))]

def nodeValue5467 : Sparse Master := [(Sum.inr 3942, (-1 / 2))]

def nodeValue5468 : Sparse Master := []

def nodeValue5469 : Sparse Master := [(Sum.inr 3945, (-1 / 4)), (Sum.inr 3952, (-1 / 4))]

def nodeValue5470 : Sparse Master := [(Sum.inr 5470, (1 / 1))]

def nodeValue5471 : Sparse Master := []

def nodeValue5472 : Sparse Master := [(Sum.inr 3957, (-1 / 2))]

def nodeValue5473 : Sparse Master := [(Sum.inr 3958, (-1 / 4)), (Sum.inr 3961, (-1 / 4))]

def nodeValue5474 : Sparse Master := []

def nodeValue5475 : Sparse Master := [(Sum.inr 3963, (-1 / 2))]

def nodeValue5476 : Sparse Master := [(Sum.inl 0, (17 / 5760)), (Sum.inl 5, (-1 / 864)), (Sum.inl 6, (1 / 3456)), (Sum.inl 2, (-1 / 288)), (Sum.inl 8, (-1 / 108)), (Sum.inl 27, (1 / 288)), (Sum.inl 1, (5 / 864)), (Sum.inl 30, (1 / 72)), (Sum.inr 4045, (-1 / 4))]

def nodeValue5477 : Sparse Master := []

def nodeValue5478 : Sparse Master := [(Sum.inr 3974, (-1 / 2))]

def nodeValue5479 : Sparse Master := []

def nodeValue5480 : Sparse Master := [(Sum.inr 5480, (1 / 1))]

def nodeValue5481 : Sparse Master := []

def nodeValue5482 : Sparse Master := [(Sum.inl 0, (47 / 17280)), (Sum.inl 2, (-11 / 3456)), (Sum.inl 3, (-1 / 216)), (Sum.inl 4, (-1 / 108)), (Sum.inl 1, (23 / 1728)), (Sum.inr 4046, (-1 / 4))]

def nodeValue5483 : Sparse Master := [(Sum.inl 0, (11 / 2880)), (Sum.inl 2, (1 / 576)), (Sum.inl 1, (-1 / 288)), (Sum.inr 4047, (-1 / 4))]

def nodeValue5484 : Sparse Master := [(Sum.inr 3983, (-1 / 2))]

def nodeValue5485 : Sparse Master := [(Sum.inl 0, (49 / 17280)), (Sum.inl 2, (-1 / 3456)), (Sum.inl 3, (1 / 216)), (Sum.inl 4, (1 / 108)), (Sum.inl 1, (-5 / 1728)), (Sum.inr 4010, (-1 / 4))]

def nodeValue5486 : Sparse Master := []

def nodeValue5487 : Sparse Master := []

def nodeValue5488 : Sparse Master := []

def nodeValue5489 : Sparse Master := []

def nodeValue5490 : Sparse Master := [(Sum.inl 0, (67 / 8640)), (Sum.inl 4, (1 / 108)), (Sum.inl 1, (-5 / 576))]

def nodeValue5491 : Sparse Master := [(Sum.inl 0, (1 / 180)), (Sum.inl 1, (1 / 36))]

def nodeValue5492 : Sparse Master := [(Sum.inl 0, (23 / 4320)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (-1 / 288))]

def nodeValue5493 : Sparse Master := []

def nodeValue5494 : Sparse Master := [(Sum.inl 0, (7 / 1440)), (Sum.inl 4, (1 / 18)), (Sum.inl 1, (-1 / 96))]

def nodeValue5495 : Sparse Master := []

def nodeValue5496 : Sparse Master := []

def nodeValue5497 : Sparse Master := []

def nodeValue5498 : Sparse Master := [(Sum.inl 0, (79 / 4320)), (Sum.inl 12, (-1 / 108)), (Sum.inl 1, (7 / 288))]

def nodeValue5499 : Sparse Master := []

def nodeValue5500 : Sparse Master := [(Sum.inl 0, (47 / 4320)), (Sum.inl 4, (-1 / 54)), (Sum.inl 1, (7 / 288))]

def nodeValue5501 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue576 : Sparse Master := [(Sum.inr 576, (1 / 1))]

def nodeValue577 : Sparse Master := [(Sum.inr 577, (1 / 1))]

def nodeValue578 : Sparse Master := [(Sum.inr 578, (1 / 1))]

def nodeValue579 : Sparse Master := [(Sum.inr 579, (1 / 1))]

def nodeValue580 : Sparse Master := [(Sum.inr 580, (1 / 1))]

def nodeValue581 : Sparse Master := [(Sum.inr 581, (1 / 1))]

def nodeValue582 : Sparse Master := [(Sum.inr 582, (1 / 1))]

def nodeValue583 : Sparse Master := [(Sum.inr 583, (1 / 1))]

def nodeValue584 : Sparse Master := [(Sum.inr 584, (1 / 1))]

def nodeValue585 : Sparse Master := [(Sum.inr 585, (1 / 1))]

def nodeValue586 : Sparse Master := [(Sum.inr 586, (1 / 1))]

def nodeValue587 : Sparse Master := [(Sum.inr 587, (1 / 1))]

def nodeValue588 : Sparse Master := [(Sum.inr 588, (1 / 1))]

def nodeValue589 : Sparse Master := [(Sum.inr 589, (1 / 1))]

def nodeValue590 : Sparse Master := [(Sum.inr 590, (1 / 1))]

def nodeValue591 : Sparse Master := [(Sum.inr 591, (1 / 1))]

def nodeValue592 : Sparse Master := [(Sum.inr 592, (1 / 1))]

def nodeValue593 : Sparse Master := [(Sum.inr 593, (1 / 1))]

def nodeValue594 : Sparse Master := [(Sum.inr 594, (1 / 1))]

def nodeValue595 : Sparse Master := [(Sum.inr 595, (1 / 1))]

def nodeValue596 : Sparse Master := [(Sum.inr 596, (1 / 1))]

def nodeValue597 : Sparse Master := [(Sum.inr 597, (1 / 1))]

def nodeValue598 : Sparse Master := [(Sum.inr 598, (1 / 1))]

def nodeValue599 : Sparse Master := [(Sum.inr 599, (1 / 1))]

def nodeValue600 : Sparse Master := [(Sum.inr 600, (1 / 1))]

def nodeValue601 : Sparse Master := [(Sum.inr 601, (1 / 1))]

def nodeValue602 : Sparse Master := [(Sum.inr 602, (1 / 1))]

def nodeValue603 : Sparse Master := [(Sum.inr 603, (1 / 1))]

def nodeValue604 : Sparse Master := [(Sum.inr 604, (1 / 1))]

def nodeValue605 : Sparse Master := [(Sum.inr 605, (1 / 1))]

def nodeValue606 : Sparse Master := [(Sum.inr 606, (1 / 1))]

def nodeValue607 : Sparse Master := [(Sum.inr 607, (1 / 1))]

def nodeValue608 : Sparse Master := [(Sum.inr 608, (1 / 1))]

def nodeValue609 : Sparse Master := [(Sum.inr 609, (1 / 1))]

def nodeValue610 : Sparse Master := [(Sum.inr 610, (1 / 1))]

def nodeValue611 : Sparse Master := [(Sum.inr 611, (1 / 1))]

def nodeValue612 : Sparse Master := [(Sum.inr 612, (1 / 1))]

def nodeValue613 : Sparse Master := [(Sum.inr 613, (1 / 1))]

def nodeValue614 : Sparse Master := [(Sum.inr 614, (1 / 1))]

def nodeValue615 : Sparse Master := [(Sum.inr 615, (1 / 1))]

def nodeValue616 : Sparse Master := [(Sum.inr 616, (1 / 1))]

def nodeValue617 : Sparse Master := [(Sum.inr 617, (1 / 1))]

def nodeValue618 : Sparse Master := [(Sum.inr 618, (1 / 1))]

def nodeValue619 : Sparse Master := [(Sum.inr 619, (1 / 1))]

def nodeValue620 : Sparse Master := [(Sum.inr 620, (1 / 1))]

def nodeValue621 : Sparse Master := [(Sum.inr 621, (1 / 1))]

def nodeValue622 : Sparse Master := [(Sum.inr 622, (1 / 1))]

def nodeValue623 : Sparse Master := [(Sum.inr 623, (1 / 1))]

def nodeValue624 : Sparse Master := [(Sum.inr 624, (1 / 1))]

def nodeValue625 : Sparse Master := [(Sum.inr 625, (1 / 1))]

def nodeValue626 : Sparse Master := [(Sum.inr 626, (1 / 1))]

def nodeValue627 : Sparse Master := [(Sum.inr 627, (1 / 1))]

def nodeValue628 : Sparse Master := [(Sum.inr 628, (1 / 1))]

def nodeValue629 : Sparse Master := [(Sum.inr 629, (1 / 1))]

def nodeValue630 : Sparse Master := [(Sum.inr 630, (1 / 1))]

def nodeValue631 : Sparse Master := [(Sum.inr 631, (1 / 1))]

def nodeValue632 : Sparse Master := [(Sum.inr 632, (1 / 1))]

def nodeValue633 : Sparse Master := [(Sum.inr 633, (1 / 1))]

def nodeValue634 : Sparse Master := [(Sum.inr 634, (1 / 1))]

def nodeValue635 : Sparse Master := [(Sum.inr 635, (1 / 1))]

def nodeValue636 : Sparse Master := [(Sum.inr 636, (1 / 1))]

def nodeValue637 : Sparse Master := [(Sum.inr 637, (1 / 1))]

def nodeValue638 : Sparse Master := [(Sum.inr 638, (1 / 1))]

def nodeValue639 : Sparse Master := [(Sum.inr 639, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


