-- Prove2me | Definitions.Def_OAIQ106D060
-- name    : OAIQ106D060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:28:08.61055+00:00
-- url     : https://prove2.me/theorems/984b2bbb-f2ca-4f38-8385-f974e51abd98
-- title:
--   Definitions bundle OAIQ106D060 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2063 declarations of OpenAI's Lean: 2063 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw4368`, `OAI.MUB6.Certificate.PairSemantics.raw4369`, `OAI.MUB6.Certificate.PairSemantics.raw4369step0`, `OAI.MUB6.Certificate.PairSemantics.raw4369step1`, `OAI.MUB6.Certificate.PairSemantics.raw436step0`, `OAI.MUB6.Certificate.PairSemantics.raw437`, `OAI.MUB6.Certificate.PairSemantics.raw4370`, `OAI.MUB6.Certificate.PairSemantics.raw4370step0`, `OAI.MUB6.Certificate.PairSemantics.raw4371`, `OAI.MUB6.Certificate.PairSemantics.raw4372`, `OAI.MUB6.Certificate.PairSemantics.raw4372step0`, `OAI.MUB6.Certificate.PairSemantics.raw4373`, `OAI.MUB6.Certificate.PairSemantics.raw4373step0`, `OAI.MUB6.Certificate.PairSemantics.raw4373step1`, `OAI.MUB6.Certificate.PairSemantics.raw4374`, `OAI.MUB6.Certificate.PairSemantics.raw4375`, `OAI.MUB6.Certificate.PairSemantics.raw4376`, `OAI.MUB6.Certificate.PairSemantics.raw4376step0`, `OAI.MUB6.Certificate.PairSemantics.raw4377`, `OAI.MUB6.Certificate.PairSemantics.raw4377step0`, `OAI.MUB6.Certificate.PairSemantics.raw4377step1`, `OAI.MUB6.Certificate.PairSemantics.raw4378`, `OAI.MUB6.Certificate.PairSemantics.raw4379`, `OAI.MUB6.Certificate.PairSemantics.raw4379step0`, `OAI.MUB6.Certificate.PairSemantics.raw437step0`, `OAI.MUB6.Certificate.PairSemantics.raw438`, `OAI.MUB6.Certificate.PairSemantics.raw4380`, `OAI.MUB6.Certificate.PairSemantics.raw4380step0`, `OAI.MUB6.Certificate.PairSemantics.raw4380step1`, `OAI.MUB6.Certificate.PairSemantics.raw4381`, `OAI.MUB6.Certificate.PairSemantics.raw4381step0`, `OAI.MUB6.Certificate.PairSemantics.raw4381step1`, `OAI.MUB6.Certificate.PairSemantics.raw4381step2`, `OAI.MUB6.Certificate.PairSemantics.raw4382`, `OAI.MUB6.Certificate.PairSemantics.raw4382step0`, `OAI.MUB6.Certificate.PairSemantics.raw4382step1`, `OAI.MUB6.Certificate.PairSemantics.raw4383`, `OAI.MUB6.Certificate.PairSemantics.raw4383step0`, `OAI.MUB6.Certificate.PairSemantics.raw4383step1`, `OAI.MUB6.Certificate.PairSemantics.raw4384` and 2023 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical1`, `MutuallyUnbiased_PairSemantics_Canonical13`, `MutuallyUnbiased_PairSemantics_Canonical136`, `MutuallyUnbiased_PairSemantics_Canonical137`, `MutuallyUnbiased_PairSemantics_Canonical138`, `MutuallyUnbiased_PairSemantics_Canonical139`, `MutuallyUnbiased_PairSemantics_Canonical14`, `MutuallyUnbiased_PairSemantics_Canonical140`, `MutuallyUnbiased_PairSemantics_Canonical141`, `MutuallyUnbiased_PairSemantics_Canonical142`, `MutuallyUnbiased_PairSemantics_Canonical143`, `MutuallyUnbiased_PairSemantics_Canonical144`, `MutuallyUnbiased_PairSemantics_Canonical145`, `MutuallyUnbiased_PairSemantics_Canonical146`, `MutuallyUnbiased_PairSemantics_Canonical147`, `MutuallyUnbiased_PairSemantics_Canonical148`, `MutuallyUnbiased_PairSemantics_Canonical149`, `MutuallyUnbiased_PairSemantics_Canonical15`, `MutuallyUnbiased_PairSemantics_Canonical150`, `MutuallyUnbiased_PairSemantics_Canonical151`, `MutuallyUnbiased_PairSemantics_Canonical152`, `MutuallyUnbiased_PairSemantics_Canonical153`, `MutuallyUnbiased_PairSemantics_Canonical154`, `MutuallyUnbiased_PairSemantics_Canonical155`, `MutuallyUnbiased_PairSemantics_Canonical156`, `MutuallyUnbiased_PairSemantics_Canonical157`, `MutuallyUnbiased_PairSemantics_Canonical158`, `MutuallyUnbiased_PairSemantics_Canonical159`, `MutuallyUnbiased_PairSemantics_Canonical16`, `MutuallyUnbiased_PairSemantics_Canonical160`, `MutuallyUnbiased_PairSemantics_Canonical249`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statement `OAI.MUB6.Certificate.PairSemantics.canonical5123`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1266`, `OAI.MUB6.Certificate.MixedSemantics.sound1267`, `OAI.MUB6.Certificate.MixedSemantics.sound1271`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3852`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3982`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4013`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4050`, `OAI.MUB6.Certificate.MixedSemantics.sound4053`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound479`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound514`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1098`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound152`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2190`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2221`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2222`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2360`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2389`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound25`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound488`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound590`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound794`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval116`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval124`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval130`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval173`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval203`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval207`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval231`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval257`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval263`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval323`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval334`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval368`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval477`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval360`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound249`, `OAI.MUB6.Certificate.PairSemantics.boundarySound250`, `OAI.MUB6.Certificate.PairSemantics.boundarySound252`, `OAI.MUB6.Certificate.PairSemantics.boundarySound305`, `OAI.MUB6.Certificate.PairSemantics.boundarySound347`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound56`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75`, `OAI.MUB6.Certificate.PairSemantics.boundarySound83`, `OAI.MUB6.Certificate.PairSemantics.boundarySound97`, `OAI.MUB6.Certificate.PairSemantics.canonical5123`, `OAI.MUB6.Certificate.PairSemantics.sound1141`, `OAI.MUB6.Certificate.PairSemantics.sound117`, `OAI.MUB6.Certificate.PairSemantics.sound1323`, `OAI.MUB6.Certificate.PairSemantics.sound1383`, `OAI.MUB6.Certificate.PairSemantics.sound1391`, `OAI.MUB6.Certificate.PairSemantics.sound1392`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1419`, `OAI.MUB6.Certificate.PairSemantics.sound1423`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1425`, `OAI.MUB6.Certificate.PairSemantics.sound1432`, `OAI.MUB6.Certificate.PairSemantics.sound1434`, `OAI.MUB6.Certificate.PairSemantics.sound1443`, `OAI.MUB6.Certificate.PairSemantics.sound1500`, `OAI.MUB6.Certificate.PairSemantics.sound1520`, `OAI.MUB6.Certificate.PairSemantics.sound1523`, `OAI.MUB6.Certificate.PairSemantics.sound1530`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1535`, `OAI.MUB6.Certificate.PairSemantics.sound1548`, `OAI.MUB6.Certificate.PairSemantics.sound1552`, `OAI.MUB6.Certificate.PairSemantics.sound1563`, `OAI.MUB6.Certificate.PairSemantics.sound1605`, `OAI.MUB6.Certificate.PairSemantics.sound1625`, `OAI.MUB6.Certificate.PairSemantics.sound1631`, `OAI.MUB6.Certificate.PairSemantics.sound1634`, `OAI.MUB6.Certificate.PairSemantics.sound1635`, `OAI.MUB6.Certificate.PairSemantics.sound1643`, `OAI.MUB6.Certificate.PairSemantics.sound1646`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1669`, `OAI.MUB6.Certificate.PairSemantics.sound1682`, `OAI.MUB6.Certificate.PairSemantics.sound1685`, `OAI.MUB6.Certificate.PairSemantics.sound1686`, `OAI.MUB6.Certificate.PairSemantics.sound1718`, `OAI.MUB6.Certificate.PairSemantics.sound1736`, `OAI.MUB6.Certificate.PairSemantics.sound1739`, `OAI.MUB6.Certificate.PairSemantics.sound1768`, `OAI.MUB6.Certificate.PairSemantics.sound1769`, `OAI.MUB6.Certificate.PairSemantics.sound1770`, `OAI.MUB6.Certificate.PairSemantics.sound1774`, `OAI.MUB6.Certificate.PairSemantics.sound1784`, `OAI.MUB6.Certificate.PairSemantics.sound1793`, `OAI.MUB6.Certificate.PairSemantics.sound1800`, `OAI.MUB6.Certificate.PairSemantics.sound1803`, `OAI.MUB6.Certificate.PairSemantics.sound1826`, `OAI.MUB6.Certificate.PairSemantics.sound1828`, `OAI.MUB6.Certificate.PairSemantics.sound1830`, `OAI.MUB6.Certificate.PairSemantics.sound1858`, `OAI.MUB6.Certificate.PairSemantics.sound1860`, `OAI.MUB6.Certificate.PairSemantics.sound1865`, `OAI.MUB6.Certificate.PairSemantics.sound1866`, `OAI.MUB6.Certificate.PairSemantics.sound1867`, `OAI.MUB6.Certificate.PairSemantics.sound1870`, `OAI.MUB6.Certificate.PairSemantics.sound1885`, `OAI.MUB6.Certificate.PairSemantics.sound1890`, `OAI.MUB6.Certificate.PairSemantics.sound1968`, `OAI.MUB6.Certificate.PairSemantics.sound1977`, `OAI.MUB6.Certificate.PairSemantics.sound1978`, `OAI.MUB6.Certificate.PairSemantics.sound1980`, `OAI.MUB6.Certificate.PairSemantics.sound1986`, `OAI.MUB6.Certificate.PairSemantics.sound1987`, `OAI.MUB6.Certificate.PairSemantics.sound2041`, `OAI.MUB6.Certificate.PairSemantics.sound2058`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2113`, `OAI.MUB6.Certificate.PairSemantics.sound2122`, `OAI.MUB6.Certificate.PairSemantics.sound2128`, `OAI.MUB6.Certificate.PairSemantics.sound2132`, `OAI.MUB6.Certificate.PairSemantics.sound2168`, `OAI.MUB6.Certificate.PairSemantics.sound2175`, `OAI.MUB6.Certificate.PairSemantics.sound2177`, `OAI.MUB6.Certificate.PairSemantics.sound2183`, `OAI.MUB6.Certificate.PairSemantics.sound2190`, `OAI.MUB6.Certificate.PairSemantics.sound2192`, `OAI.MUB6.Certificate.PairSemantics.sound2197`, `OAI.MUB6.Certificate.PairSemantics.sound2201`, `OAI.MUB6.Certificate.PairSemantics.sound2202`, `OAI.MUB6.Certificate.PairSemantics.sound2204`, `OAI.MUB6.Certificate.PairSemantics.sound2213`, `OAI.MUB6.Certificate.PairSemantics.sound2216`, `OAI.MUB6.Certificate.PairSemantics.sound2228`, `OAI.MUB6.Certificate.PairSemantics.sound2243`, `OAI.MUB6.Certificate.PairSemantics.sound2244`, `OAI.MUB6.Certificate.PairSemantics.sound2262`, `OAI.MUB6.Certificate.PairSemantics.sound2284`, `OAI.MUB6.Certificate.PairSemantics.sound2285`, `OAI.MUB6.Certificate.PairSemantics.sound2286`, `OAI.MUB6.Certificate.PairSemantics.sound2293`, `OAI.MUB6.Certificate.PairSemantics.sound2294`, `OAI.MUB6.Certificate.PairSemantics.sound2295`, `OAI.MUB6.Certificate.PairSemantics.sound2296`, `OAI.MUB6.Certificate.PairSemantics.sound2298`, `OAI.MUB6.Certificate.PairSemantics.sound2304`, `OAI.MUB6.Certificate.PairSemantics.sound2307`, `OAI.MUB6.Certificate.PairSemantics.sound2312`, `OAI.MUB6.Certificate.PairSemantics.sound2315`, `OAI.MUB6.Certificate.PairSemantics.sound2324`, `OAI.MUB6.Certificate.PairSemantics.sound2325`, `OAI.MUB6.Certificate.PairSemantics.sound2327`, `OAI.MUB6.Certificate.PairSemantics.sound2338`, `OAI.MUB6.Certificate.PairSemantics.sound2349`, `OAI.MUB6.Certificate.PairSemantics.sound2382`, `OAI.MUB6.Certificate.PairSemantics.sound2389`, `OAI.MUB6.Certificate.PairSemantics.sound2414`, `OAI.MUB6.Certificate.PairSemantics.sound2415`, `OAI.MUB6.Certificate.PairSemantics.sound2420`, `OAI.MUB6.Certificate.PairSemantics.sound2433`, `OAI.MUB6.Certificate.PairSemantics.sound2434`, `OAI.MUB6.Certificate.PairSemantics.sound2436`, `OAI.MUB6.Certificate.PairSemantics.sound2440`, `OAI.MUB6.Certificate.PairSemantics.sound2441`, `OAI.MUB6.Certificate.PairSemantics.sound2442`, `OAI.MUB6.Certificate.PairSemantics.sound2443`, `OAI.MUB6.Certificate.PairSemantics.sound2444`, `OAI.MUB6.Certificate.PairSemantics.sound2445`, `OAI.MUB6.Certificate.PairSemantics.sound2455`, `OAI.MUB6.Certificate.PairSemantics.sound2463`, `OAI.MUB6.Certificate.PairSemantics.sound2470`, `OAI.MUB6.Certificate.PairSemantics.sound2472`, `OAI.MUB6.Certificate.PairSemantics.sound2486`, `OAI.MUB6.Certificate.PairSemantics.sound2489`, `OAI.MUB6.Certificate.PairSemantics.sound2491`, `OAI.MUB6.Certificate.PairSemantics.sound2507`, `OAI.MUB6.Certificate.PairSemantics.sound2525`, `OAI.MUB6.Certificate.PairSemantics.sound2533`, `OAI.MUB6.Certificate.PairSemantics.sound2540`, `OAI.MUB6.Certificate.PairSemantics.sound2546`, `OAI.MUB6.Certificate.PairSemantics.sound2548`, `OAI.MUB6.Certificate.PairSemantics.sound2557`, `OAI.MUB6.Certificate.PairSemantics.sound2558`, `OAI.MUB6.Certificate.PairSemantics.sound2559`, `OAI.MUB6.Certificate.PairSemantics.sound2573`, `OAI.MUB6.Certificate.PairSemantics.sound2579`, `OAI.MUB6.Certificate.PairSemantics.sound2604`, `OAI.MUB6.Certificate.PairSemantics.sound2606`, `OAI.MUB6.Certificate.PairSemantics.sound2619`, `OAI.MUB6.Certificate.PairSemantics.sound2626`, `OAI.MUB6.Certificate.PairSemantics.sound2627`, `OAI.MUB6.Certificate.PairSemantics.sound2657`, `OAI.MUB6.Certificate.PairSemantics.sound2666`, `OAI.MUB6.Certificate.PairSemantics.sound2671`, `OAI.MUB6.Certificate.PairSemantics.sound2693`, `OAI.MUB6.Certificate.PairSemantics.sound2709`, `OAI.MUB6.Certificate.PairSemantics.sound2710`, `OAI.MUB6.Certificate.PairSemantics.sound2717`, `OAI.MUB6.Certificate.PairSemantics.sound2732`, `OAI.MUB6.Certificate.PairSemantics.sound2733`, `OAI.MUB6.Certificate.PairSemantics.sound2765`, `OAI.MUB6.Certificate.PairSemantics.sound2793`, `OAI.MUB6.Certificate.PairSemantics.sound2836`, `OAI.MUB6.Certificate.PairSemantics.sound2845`, `OAI.MUB6.Certificate.PairSemantics.sound2863`, `OAI.MUB6.Certificate.PairSemantics.sound2879`, `OAI.MUB6.Certificate.PairSemantics.sound2882`, `OAI.MUB6.Certificate.PairSemantics.sound2884`, `OAI.MUB6.Certificate.PairSemantics.sound2886`, `OAI.MUB6.Certificate.PairSemantics.sound2887`, `OAI.MUB6.Certificate.PairSemantics.sound2889`, `OAI.MUB6.Certificate.PairSemantics.sound2891`, `OAI.MUB6.Certificate.PairSemantics.sound2892`, `OAI.MUB6.Certificate.PairSemantics.sound2896`, `OAI.MUB6.Certificate.PairSemantics.sound2898`, `OAI.MUB6.Certificate.PairSemantics.sound2900`, `OAI.MUB6.Certificate.PairSemantics.sound2901`, `OAI.MUB6.Certificate.PairSemantics.sound2902`, `OAI.MUB6.Certificate.PairSemantics.sound2903`, `OAI.MUB6.Certificate.PairSemantics.sound2906`, `OAI.MUB6.Certificate.PairSemantics.sound2910`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2914`, `OAI.MUB6.Certificate.PairSemantics.sound2915`, `OAI.MUB6.Certificate.PairSemantics.sound2916`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2918`, `OAI.MUB6.Certificate.PairSemantics.sound2919`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2924`, `OAI.MUB6.Certificate.PairSemantics.sound2927`, `OAI.MUB6.Certificate.PairSemantics.sound2928`, `OAI.MUB6.Certificate.PairSemantics.sound2930`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2933`, `OAI.MUB6.Certificate.PairSemantics.sound2934`, `OAI.MUB6.Certificate.PairSemantics.sound2935`, `OAI.MUB6.Certificate.PairSemantics.sound2936`, `OAI.MUB6.Certificate.PairSemantics.sound2940`, `OAI.MUB6.Certificate.PairSemantics.sound2943`, `OAI.MUB6.Certificate.PairSemantics.sound2944`, `OAI.MUB6.Certificate.PairSemantics.sound2948`, `OAI.MUB6.Certificate.PairSemantics.sound2950`, `OAI.MUB6.Certificate.PairSemantics.sound2952`, `OAI.MUB6.Certificate.PairSemantics.sound2953`, `OAI.MUB6.Certificate.PairSemantics.sound2954`, `OAI.MUB6.Certificate.PairSemantics.sound2955`, `OAI.MUB6.Certificate.PairSemantics.sound2957`, `OAI.MUB6.Certificate.PairSemantics.sound2958`, `OAI.MUB6.Certificate.PairSemantics.sound2959`, `OAI.MUB6.Certificate.PairSemantics.sound2962`, `OAI.MUB6.Certificate.PairSemantics.sound2965`, `OAI.MUB6.Certificate.PairSemantics.sound2966`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2969`, `OAI.MUB6.Certificate.PairSemantics.sound2970`, `OAI.MUB6.Certificate.PairSemantics.sound2972`, `OAI.MUB6.Certificate.PairSemantics.sound2973`, `OAI.MUB6.Certificate.PairSemantics.sound2974`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2976`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound2982`, `OAI.MUB6.Certificate.PairSemantics.sound2986`, `OAI.MUB6.Certificate.PairSemantics.sound2987`, `OAI.MUB6.Certificate.PairSemantics.sound2988`, `OAI.MUB6.Certificate.PairSemantics.sound2990`, `OAI.MUB6.Certificate.PairSemantics.sound2991`, `OAI.MUB6.Certificate.PairSemantics.sound2993`, `OAI.MUB6.Certificate.PairSemantics.sound2994`, `OAI.MUB6.Certificate.PairSemantics.sound2996`, `OAI.MUB6.Certificate.PairSemantics.sound2997`, `OAI.MUB6.Certificate.PairSemantics.sound2998`, `OAI.MUB6.Certificate.PairSemantics.sound2999`, `OAI.MUB6.Certificate.PairSemantics.sound3000`, `OAI.MUB6.Certificate.PairSemantics.sound3001`, `OAI.MUB6.Certificate.PairSemantics.sound3002`, `OAI.MUB6.Certificate.PairSemantics.sound3004`, `OAI.MUB6.Certificate.PairSemantics.sound3006`, `OAI.MUB6.Certificate.PairSemantics.sound3009`, `OAI.MUB6.Certificate.PairSemantics.sound3010`, `OAI.MUB6.Certificate.PairSemantics.sound3011`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3013`, `OAI.MUB6.Certificate.PairSemantics.sound3014`, `OAI.MUB6.Certificate.PairSemantics.sound3015`, `OAI.MUB6.Certificate.PairSemantics.sound3016`, `OAI.MUB6.Certificate.PairSemantics.sound3018`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3020`, `OAI.MUB6.Certificate.PairSemantics.sound3021`, `OAI.MUB6.Certificate.PairSemantics.sound3022`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3024`, `OAI.MUB6.Certificate.PairSemantics.sound3025`, `OAI.MUB6.Certificate.PairSemantics.sound3026`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3028`, `OAI.MUB6.Certificate.PairSemantics.sound3030`, `OAI.MUB6.Certificate.PairSemantics.sound3031`, `OAI.MUB6.Certificate.PairSemantics.sound3032`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3034`, `OAI.MUB6.Certificate.PairSemantics.sound3035`, `OAI.MUB6.Certificate.PairSemantics.sound3036`, `OAI.MUB6.Certificate.PairSemantics.sound3038`, `OAI.MUB6.Certificate.PairSemantics.sound3039`, `OAI.MUB6.Certificate.PairSemantics.sound3040`, `OAI.MUB6.Certificate.PairSemantics.sound3041`, `OAI.MUB6.Certificate.PairSemantics.sound3042`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3044`, `OAI.MUB6.Certificate.PairSemantics.sound3045`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3048`, `OAI.MUB6.Certificate.PairSemantics.sound3049`, `OAI.MUB6.Certificate.PairSemantics.sound3050`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3053`, `OAI.MUB6.Certificate.PairSemantics.sound3054`, `OAI.MUB6.Certificate.PairSemantics.sound3056`, `OAI.MUB6.Certificate.PairSemantics.sound3058`, `OAI.MUB6.Certificate.PairSemantics.sound3059`, `OAI.MUB6.Certificate.PairSemantics.sound3060`, `OAI.MUB6.Certificate.PairSemantics.sound3061`, `OAI.MUB6.Certificate.PairSemantics.sound3062`, `OAI.MUB6.Certificate.PairSemantics.sound3063`, `OAI.MUB6.Certificate.PairSemantics.sound3065`, `OAI.MUB6.Certificate.PairSemantics.sound3066`, `OAI.MUB6.Certificate.PairSemantics.sound3067`, `OAI.MUB6.Certificate.PairSemantics.sound3068`, `OAI.MUB6.Certificate.PairSemantics.sound3069`, `OAI.MUB6.Certificate.PairSemantics.sound3071`, `OAI.MUB6.Certificate.PairSemantics.sound3072`, `OAI.MUB6.Certificate.PairSemantics.sound3073`, `OAI.MUB6.Certificate.PairSemantics.sound3074`, `OAI.MUB6.Certificate.PairSemantics.sound3075`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3077`, `OAI.MUB6.Certificate.PairSemantics.sound3078`, `OAI.MUB6.Certificate.PairSemantics.sound3079`, `OAI.MUB6.Certificate.PairSemantics.sound3080`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3082`, `OAI.MUB6.Certificate.PairSemantics.sound3083`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3086`, `OAI.MUB6.Certificate.PairSemantics.sound3090`, `OAI.MUB6.Certificate.PairSemantics.sound3091`, `OAI.MUB6.Certificate.PairSemantics.sound3092`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3094`, `OAI.MUB6.Certificate.PairSemantics.sound3095`, `OAI.MUB6.Certificate.PairSemantics.sound3096`, `OAI.MUB6.Certificate.PairSemantics.sound3097`, `OAI.MUB6.Certificate.PairSemantics.sound3098`, `OAI.MUB6.Certificate.PairSemantics.sound3099`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3101`, `OAI.MUB6.Certificate.PairSemantics.sound3105`, `OAI.MUB6.Certificate.PairSemantics.sound3107`, `OAI.MUB6.Certificate.PairSemantics.sound3109`, `OAI.MUB6.Certificate.PairSemantics.sound3112`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3114`, `OAI.MUB6.Certificate.PairSemantics.sound3115`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3118`, `OAI.MUB6.Certificate.PairSemantics.sound3120`, `OAI.MUB6.Certificate.PairSemantics.sound3121`, `OAI.MUB6.Certificate.PairSemantics.sound3122`, `OAI.MUB6.Certificate.PairSemantics.sound3123`, `OAI.MUB6.Certificate.PairSemantics.sound3124`, `OAI.MUB6.Certificate.PairSemantics.sound3125`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3131`, `OAI.MUB6.Certificate.PairSemantics.sound3133`, `OAI.MUB6.Certificate.PairSemantics.sound3135`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3138`, `OAI.MUB6.Certificate.PairSemantics.sound3139`, `OAI.MUB6.Certificate.PairSemantics.sound3140`, `OAI.MUB6.Certificate.PairSemantics.sound3141`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3144`, `OAI.MUB6.Certificate.PairSemantics.sound3145`, `OAI.MUB6.Certificate.PairSemantics.sound3146`, `OAI.MUB6.Certificate.PairSemantics.sound3150`, `OAI.MUB6.Certificate.PairSemantics.sound3151`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3159`, `OAI.MUB6.Certificate.PairSemantics.sound3160`, `OAI.MUB6.Certificate.PairSemantics.sound3161`, `OAI.MUB6.Certificate.PairSemantics.sound3162`, `OAI.MUB6.Certificate.PairSemantics.sound3163`, `OAI.MUB6.Certificate.PairSemantics.sound3164`, `OAI.MUB6.Certificate.PairSemantics.sound3166`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3168`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3171`, `OAI.MUB6.Certificate.PairSemantics.sound3172`, `OAI.MUB6.Certificate.PairSemantics.sound3173`, `OAI.MUB6.Certificate.PairSemantics.sound3174`, `OAI.MUB6.Certificate.PairSemantics.sound3176`, `OAI.MUB6.Certificate.PairSemantics.sound3178`, `OAI.MUB6.Certificate.PairSemantics.sound3179`, `OAI.MUB6.Certificate.PairSemantics.sound3180`, `OAI.MUB6.Certificate.PairSemantics.sound3181`, `OAI.MUB6.Certificate.PairSemantics.sound3183`, `OAI.MUB6.Certificate.PairSemantics.sound3184`, `OAI.MUB6.Certificate.PairSemantics.sound3185`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3188`, `OAI.MUB6.Certificate.PairSemantics.sound3189`, `OAI.MUB6.Certificate.PairSemantics.sound3191`, `OAI.MUB6.Certificate.PairSemantics.sound3192`, `OAI.MUB6.Certificate.PairSemantics.sound3193`, `OAI.MUB6.Certificate.PairSemantics.sound3194`, `OAI.MUB6.Certificate.PairSemantics.sound3195`, `OAI.MUB6.Certificate.PairSemantics.sound3196`, `OAI.MUB6.Certificate.PairSemantics.sound3197`, `OAI.MUB6.Certificate.PairSemantics.sound3198`, `OAI.MUB6.Certificate.PairSemantics.sound3199`, `OAI.MUB6.Certificate.PairSemantics.sound3200`, `OAI.MUB6.Certificate.PairSemantics.sound3201`, `OAI.MUB6.Certificate.PairSemantics.sound3202`, `OAI.MUB6.Certificate.PairSemantics.sound3203`, `OAI.MUB6.Certificate.PairSemantics.sound3204`, `OAI.MUB6.Certificate.PairSemantics.sound3205`, `OAI.MUB6.Certificate.PairSemantics.sound3206`, `OAI.MUB6.Certificate.PairSemantics.sound3208`, `OAI.MUB6.Certificate.PairSemantics.sound3211`, `OAI.MUB6.Certificate.PairSemantics.sound3212`, `OAI.MUB6.Certificate.PairSemantics.sound3213`, `OAI.MUB6.Certificate.PairSemantics.sound3214`, `OAI.MUB6.Certificate.PairSemantics.sound3215`, `OAI.MUB6.Certificate.PairSemantics.sound3216`, `OAI.MUB6.Certificate.PairSemantics.sound3217`, `OAI.MUB6.Certificate.PairSemantics.sound3218`, `OAI.MUB6.Certificate.PairSemantics.sound3219`, `OAI.MUB6.Certificate.PairSemantics.sound3221`, `OAI.MUB6.Certificate.PairSemantics.sound3222`, `OAI.MUB6.Certificate.PairSemantics.sound3223`, `OAI.MUB6.Certificate.PairSemantics.sound3224`, `OAI.MUB6.Certificate.PairSemantics.sound3226`, `OAI.MUB6.Certificate.PairSemantics.sound3227`, `OAI.MUB6.Certificate.PairSemantics.sound3228`, `OAI.MUB6.Certificate.PairSemantics.sound3230`, `OAI.MUB6.Certificate.PairSemantics.sound3231`, `OAI.MUB6.Certificate.PairSemantics.sound3233`, `OAI.MUB6.Certificate.PairSemantics.sound3234`, `OAI.MUB6.Certificate.PairSemantics.sound3235`, `OAI.MUB6.Certificate.PairSemantics.sound3237`, `OAI.MUB6.Certificate.PairSemantics.sound3238`, `OAI.MUB6.Certificate.PairSemantics.sound3239`, `OAI.MUB6.Certificate.PairSemantics.sound3240`, `OAI.MUB6.Certificate.PairSemantics.sound3241`, `OAI.MUB6.Certificate.PairSemantics.sound3242`, `OAI.MUB6.Certificate.PairSemantics.sound3243`, `OAI.MUB6.Certificate.PairSemantics.sound3244`, `OAI.MUB6.Certificate.PairSemantics.sound3246`, `OAI.MUB6.Certificate.PairSemantics.sound3247`, `OAI.MUB6.Certificate.PairSemantics.sound3248`, `OAI.MUB6.Certificate.PairSemantics.sound3249`, `OAI.MUB6.Certificate.PairSemantics.sound3250`, `OAI.MUB6.Certificate.PairSemantics.sound3251`, `OAI.MUB6.Certificate.PairSemantics.sound3253`, `OAI.MUB6.Certificate.PairSemantics.sound3254`, `OAI.MUB6.Certificate.PairSemantics.sound3255`, `OAI.MUB6.Certificate.PairSemantics.sound3256`, `OAI.MUB6.Certificate.PairSemantics.sound3258`, `OAI.MUB6.Certificate.PairSemantics.sound3259`, `OAI.MUB6.Certificate.PairSemantics.sound3261`, `OAI.MUB6.Certificate.PairSemantics.sound3262`, `OAI.MUB6.Certificate.PairSemantics.sound3263`, `OAI.MUB6.Certificate.PairSemantics.sound3266`, `OAI.MUB6.Certificate.PairSemantics.sound3267`, `OAI.MUB6.Certificate.PairSemantics.sound3268`, `OAI.MUB6.Certificate.PairSemantics.sound3269`, `OAI.MUB6.Certificate.PairSemantics.sound3270`, `OAI.MUB6.Certificate.PairSemantics.sound3271`, `OAI.MUB6.Certificate.PairSemantics.sound3273`, `OAI.MUB6.Certificate.PairSemantics.sound3275`, `OAI.MUB6.Certificate.PairSemantics.sound3276`, `OAI.MUB6.Certificate.PairSemantics.sound3277`, `OAI.MUB6.Certificate.PairSemantics.sound3279`, `OAI.MUB6.Certificate.PairSemantics.sound3280`, `OAI.MUB6.Certificate.PairSemantics.sound3281`, `OAI.MUB6.Certificate.PairSemantics.sound3282`, `OAI.MUB6.Certificate.PairSemantics.sound3283`, `OAI.MUB6.Certificate.PairSemantics.sound3284`, `OAI.MUB6.Certificate.PairSemantics.sound3288`, `OAI.MUB6.Certificate.PairSemantics.sound3289`, `OAI.MUB6.Certificate.PairSemantics.sound3290`, `OAI.MUB6.Certificate.PairSemantics.sound3291`, `OAI.MUB6.Certificate.PairSemantics.sound3292`, `OAI.MUB6.Certificate.PairSemantics.sound3293`, `OAI.MUB6.Certificate.PairSemantics.sound3294`, `OAI.MUB6.Certificate.PairSemantics.sound3295`, `OAI.MUB6.Certificate.PairSemantics.sound3296`, `OAI.MUB6.Certificate.PairSemantics.sound3297`, `OAI.MUB6.Certificate.PairSemantics.sound3298`, `OAI.MUB6.Certificate.PairSemantics.sound3299`, `OAI.MUB6.Certificate.PairSemantics.sound3300`, `OAI.MUB6.Certificate.PairSemantics.sound3301`, `OAI.MUB6.Certificate.PairSemantics.sound3302`, `OAI.MUB6.Certificate.PairSemantics.sound3303`, `OAI.MUB6.Certificate.PairSemantics.sound3304`, `OAI.MUB6.Certificate.PairSemantics.sound3305`, `OAI.MUB6.Certificate.PairSemantics.sound3307`, `OAI.MUB6.Certificate.PairSemantics.sound3308`, `OAI.MUB6.Certificate.PairSemantics.sound3310`, `OAI.MUB6.Certificate.PairSemantics.sound3311`, `OAI.MUB6.Certificate.PairSemantics.sound3312`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3314`, `OAI.MUB6.Certificate.PairSemantics.sound3315`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3319`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3323`, `OAI.MUB6.Certificate.PairSemantics.sound3325`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSemantics.sound3328`, `OAI.MUB6.Certificate.PairSemantics.sound3332`, `OAI.MUB6.Certificate.PairSemantics.sound3333`, `OAI.MUB6.Certificate.PairSemantics.sound3335`, `OAI.MUB6.Certificate.PairSemantics.sound3336`, `OAI.MUB6.Certificate.PairSemantics.sound3338`, `OAI.MUB6.Certificate.PairSemantics.sound3342`, `OAI.MUB6.Certificate.PairSemantics.sound3343`, `OAI.MUB6.Certificate.PairSemantics.sound3344`, `OAI.MUB6.Certificate.PairSemantics.sound3345`, `OAI.MUB6.Certificate.PairSemantics.sound3346`, `OAI.MUB6.Certificate.PairSemantics.sound3347`, `OAI.MUB6.Certificate.PairSemantics.sound3348`, `OAI.MUB6.Certificate.PairSemantics.sound3349`, `OAI.MUB6.Certificate.PairSemantics.sound3350`, `OAI.MUB6.Certificate.PairSemantics.sound3351`, `OAI.MUB6.Certificate.PairSemantics.sound3352`, `OAI.MUB6.Certificate.PairSemantics.sound3353`, `OAI.MUB6.Certificate.PairSemantics.sound3354`, `OAI.MUB6.Certificate.PairSemantics.sound3355`, `OAI.MUB6.Certificate.PairSemantics.sound3356`, `OAI.MUB6.Certificate.PairSemantics.sound3357`, `OAI.MUB6.Certificate.PairSemantics.sound3359`, `OAI.MUB6.Certificate.PairSemantics.sound3360`, `OAI.MUB6.Certificate.PairSemantics.sound3361`, `OAI.MUB6.Certificate.PairSemantics.sound3362`, `OAI.MUB6.Certificate.PairSemantics.sound3364`, `OAI.MUB6.Certificate.PairSemantics.sound3365`, `OAI.MUB6.Certificate.PairSemantics.sound3366`, `OAI.MUB6.Certificate.PairSemantics.sound3367`, `OAI.MUB6.Certificate.PairSemantics.sound3369`, `OAI.MUB6.Certificate.PairSemantics.sound3370`, `OAI.MUB6.Certificate.PairSemantics.sound3371`, `OAI.MUB6.Certificate.PairSemantics.sound3372`, `OAI.MUB6.Certificate.PairSemantics.sound3373`, `OAI.MUB6.Certificate.PairSemantics.sound3375`, `OAI.MUB6.Certificate.PairSemantics.sound3378`, `OAI.MUB6.Certificate.PairSemantics.sound3380`, `OAI.MUB6.Certificate.PairSemantics.sound3381`, `OAI.MUB6.Certificate.PairSemantics.sound3382`, `OAI.MUB6.Certificate.PairSemantics.sound3383`, `OAI.MUB6.Certificate.PairSemantics.sound3384`, `OAI.MUB6.Certificate.PairSemantics.sound3385`, `OAI.MUB6.Certificate.PairSemantics.sound3388`, `OAI.MUB6.Certificate.PairSemantics.sound3390`, `OAI.MUB6.Certificate.PairSemantics.sound3391`, `OAI.MUB6.Certificate.PairSemantics.sound3392`, `OAI.MUB6.Certificate.PairSemantics.sound3393`, `OAI.MUB6.Certificate.PairSemantics.sound3394`, `OAI.MUB6.Certificate.PairSemantics.sound3395`, `OAI.MUB6.Certificate.PairSemantics.sound3396`, `OAI.MUB6.Certificate.PairSemantics.sound3400`, `OAI.MUB6.Certificate.PairSemantics.sound3401`, `OAI.MUB6.Certificate.PairSemantics.sound3402`, `OAI.MUB6.Certificate.PairSemantics.sound3405`, `OAI.MUB6.Certificate.PairSemantics.sound3407`, `OAI.MUB6.Certificate.PairSemantics.sound3414`, `OAI.MUB6.Certificate.PairSemantics.sound3415`, `OAI.MUB6.Certificate.PairSemantics.sound3416`, `OAI.MUB6.Certificate.PairSemantics.sound3417`, `OAI.MUB6.Certificate.PairSemantics.sound3418`, `OAI.MUB6.Certificate.PairSemantics.sound3422`, `OAI.MUB6.Certificate.PairSemantics.sound3423`, `OAI.MUB6.Certificate.PairSemantics.sound3425`, `OAI.MUB6.Certificate.PairSemantics.sound3426`, `OAI.MUB6.Certificate.PairSemantics.sound3428`, `OAI.MUB6.Certificate.PairSemantics.sound3431`, `OAI.MUB6.Certificate.PairSemantics.sound3433`, `OAI.MUB6.Certificate.PairSemantics.sound3434`, `OAI.MUB6.Certificate.PairSemantics.sound3435`, `OAI.MUB6.Certificate.PairSemantics.sound3436`, `OAI.MUB6.Certificate.PairSemantics.sound3437`, `OAI.MUB6.Certificate.PairSemantics.sound3438`, `OAI.MUB6.Certificate.PairSemantics.sound3440`, `OAI.MUB6.Certificate.PairSemantics.sound3441`, `OAI.MUB6.Certificate.PairSemantics.sound3445`, `OAI.MUB6.Certificate.PairSemantics.sound3447`, `OAI.MUB6.Certificate.PairSemantics.sound3458`, `OAI.MUB6.Certificate.PairSemantics.sound3460`, `OAI.MUB6.Certificate.PairSemantics.sound3461`, `OAI.MUB6.Certificate.PairSemantics.sound3462`, `OAI.MUB6.Certificate.PairSemantics.sound3467`, `OAI.MUB6.Certificate.PairSemantics.sound381`, `OAI.MUB6.Certificate.PairSemantics.sound659`, `OAI.MUB6.Certificate.PairSemantics.sound711`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound126`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound13`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound25`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound57`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99`, `OAI.MUB6.Certificate.PairTargetSemantics.certificate_zero1`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity0`, `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition14`, `OAI.MUB6.Certificate.PairTargetSemantics.partition16`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.partition24`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm1`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw4step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw5 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw44step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw45 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]

def raw46 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]

def raw46step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw47 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

def raw48 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

def raw49 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]

def raw49step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw50 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![1, -1], ![2, -2]]

def raw50step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

def raw51 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw438 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]

def raw438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw439 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw440 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw441 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]

def raw441step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw442 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]

def raw442step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw444 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]

def raw444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]

def raw444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def raw445 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]

def raw445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4368 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4369 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4369step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, -1, 2], ![3, -1, 0, -2]]

def raw4369step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw4370 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4370step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw4371 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4372 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4372step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, 0, 1], ![3, -1, -1, -1]]

def raw4373step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4374 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4375 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4376 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4376step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4377 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw4377step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, 1, 0], ![3, -1, -2, 0]]

def raw4377step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw4378 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4379 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4379step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4380 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw4380step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 1, 2, -1], ![3, -1, -3, 1]]

def raw4380step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 2, -1, -2]]

def raw4381 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw4381step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![3, -1, 1, -3]]

def raw4381step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![2, -1, 0, -1], ![-3, 1, -1, 3]]

def raw4381step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw4382 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4382step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 1, 1, 0], ![3, -1, 0, -2]]

def raw4382step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4383 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw4383step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 1, 2, -1], ![3, -1, -1, -1]]

def raw4383step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4384 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4384step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![3, -1, 0, -2]]

def raw4384step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4385 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4385step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![3, -1, -1, -1]]

def raw4385step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4386 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4386step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4387step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4388 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw4390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4391 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4391step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 2, -1, 1], ![3, -2, 0, -1]]

def raw4391step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![2, -2, 1, -1], ![-3, 2, 0, 1]]

def raw4391step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

def raw4392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4393 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4393step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw4394 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4394step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 2, 0, 0], ![3, -2, -1, 0]]

def raw4394step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4395 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4396 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4396step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4397 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw4397step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 2, 1, -1], ![3, -2, -2, 1]]

def raw4397step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, -1, -2]]

def raw4398 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, 0, -2]]

def raw4398step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4399 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4399step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-2, 2, 1, -1], ![3, -2, 0, -1]]

def raw4399step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw4400 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw4400step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw4401 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4401step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![3, -2, 0, -1]]

def raw4401step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -2, 0, 0], ![-3, 2, 0, 1]]

def raw4401step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw4402 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4402step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 2, 1, -1], ![3, -2, -1, 0]]

def raw4402step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -2, -1, 1], ![-3, 2, 1, 0]]

def raw4402step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4403 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw4403step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-2, 2, -1, 1], ![3, -2, 0, -1]]

def raw4403step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![2, -2, 1, -1], ![-3, 2, 0, 1]]

def raw4403step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4404 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, 0, 1, -2], ![1, -1, -1, 1]]

def raw4404step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw4405 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4406 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4406step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 3, -1, 0], ![3, -3, 0, 0]]

def raw4406step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 0, -3, 3], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw4407 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4408 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4408step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4409 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4409step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-2, 3, 0, -1], ![3, -3, -1, 1]]

def raw4409step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 3, -1, -2], ![1, 0, -2, 1]]

def raw4410 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw4411 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4411step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 3, -1, 0], ![3, -3, 1, -1]]

def raw4411step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -3, 1, 0], ![-3, 3, -1, 1]]

def raw4411step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def raw4412 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4412step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-2, 3, 0, -1], ![3, -3, 0, 0]]

def raw4412step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![2, -3, 0, 1], ![-3, 3, 0, 0]]

def raw4412step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw4413 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw4413step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-2, 3, -1, 0], ![3, -3, 0, 0]]

def raw4413step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![2, -3, 1, 0], ![-3, 3, 0, 0]]

def raw4413step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw4414 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4414step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 0, 3], ![3, 0, 1, -4]]

def raw4414step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw4415 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw4415step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 1, 2], ![3, 0, 0, -3]]

def raw4415step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4416 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4416step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 2, 1], ![3, 0, -1, -2]]

def raw4416step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, 1, -2, -1], ![-3, 0, 1, 2]]

def raw4416step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4417 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4417step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, -1, 3, 0], ![3, 0, -2, -1]]

def raw4417step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4418 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4418step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, -1, 0, 3], ![3, 0, 0, -3]]

def raw4418step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4419 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4419step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, -1, 1, 2], ![3, 0, -1, -2]]

def raw4419step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, 1, -1, -2], ![-3, 0, 1, 2]]

def raw4419step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4420 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw4420step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, -1, 2, 1], ![3, 0, -2, -1]]

def raw4420step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, 1, -2, -1], ![-3, 0, 2, 1]]

def raw4420step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4421 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4421step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 0, 2, 0], ![3, -1, -1, -1]]

def raw4421step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4422 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4422step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 0, 3, -1], ![3, -1, -2, 0]]

def raw4422step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw4423 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4423step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 0, -1, 3], ![3, -1, 1, -3]]

def raw4423step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4424 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4424step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 0, 0, 2], ![3, -1, 0, -2]]

def raw4424step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4425 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4425step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 0, 1, 1], ![3, -1, -1, -1]]

def raw4425step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4426 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4426step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 1, 1, 0], ![3, -2, 0, -1]]

def raw4426step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4427 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4427step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 1, 2, -1], ![3, -2, -1, 0]]

def raw4427step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, -1, -2, 1], ![-3, 2, 1, 0]]

def raw4427step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4428 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw4429 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4429step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 1, 0, 1], ![3, -2, 0, -1]]

def raw4429step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -1, 0, -1], ![-3, 2, 0, 1]]

def raw4429step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw4430 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4430step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 2, 1, -1], ![3, -3, 0, 0]]

def raw4430step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, -2, -1, 1], ![-3, 3, 0, 0]]

def raw4430step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw4431 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4432 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4432step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 2, 0, 0], ![3, -3, 0, 0]]

def raw4432step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -2, 0, 0], ![-3, 3, 0, 0]]

def raw4432step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw4433 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4433step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-2, 3, 0, -1], ![3, -4, 1, 0]]

def raw4433step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![2, -3, 0, 1], ![-3, 4, -1, 0]]

def raw4433step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, 0, -3, 2]]

def raw4434 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4434step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 3, -1, 0], ![3, -4, 1, 0]]

def raw4434step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -3, 1, 0], ![-3, 4, -1, 0]]

def raw4434step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 1, -3, 2], ![1, 1, -1, -1]]

def raw4435 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4435step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-2, 3, 0, -1], ![3, -4, 0, 1]]

def raw4435step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![2, -3, 0, 1], ![-3, 4, 0, -1]]

def raw4435step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 1, -3, 2], ![1, 1, -1, -1]]

def raw4436 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw4436step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-2, 2, 1, -1], ![3, -1, -2, 0]]

def raw4436step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 2, -1, 0], ![2, -2, -1, 1], ![-3, 1, 2, 0]]

def raw4436step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4437 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![1, -1, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4437step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw4438 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4438step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw4439 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def raw4439step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-1, 0, 3, -2], ![2, 2, -4, 0]]

def raw4439step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 2, -1, 0], ![1, 0, -3, 2], ![-2, -2, 4, 0]]

def raw4439step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw4440 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 0, 2], ![1, 0, 3, -4], ![1, 1, -2, 0]]

def raw4440step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-1, 0, 3, -2], ![2, 2, -4, 0]]

def raw4440step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 2, 0, -1], ![1, 0, -3, 2], ![-2, -2, 4, 0]]

def raw4440step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

def raw4441 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def raw4441step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw4442 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4442step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-1, 1, -1, 1], ![2, 1, 0, -3]]

def raw4442step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 2, 0, -1], ![1, -1, 1, -1], ![-2, -1, 0, 3]]

def raw4442step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw4443 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw4443step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4444 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4444step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4445 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw4445step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-1, 2, -1, 0], ![2, 0, 0, -2]]

def raw4445step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4446 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4446step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-1, 2, 0, -1], ![2, 0, -1, -1]]

def raw4446step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4447 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -2, 2, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4447step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![-1, 2, 0, -1], ![2, 0, -1, -1]]

def raw4447step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4448 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4449 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4450 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw4450step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw4450step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![1, 1, -3, 1], ![-2, -2, 4, 0]]

def raw4450step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw4451 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4451step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, -1, 0, 2], ![2, 2, 0, -4]]

def raw4451step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw4452 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4452step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, -1, -1, 3], ![2, 2, 0, -4]]

def raw4452step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw4453 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw4453step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw4453step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw4454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4454step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw4454step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw4455 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4455step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw4456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4456step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4457 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4457step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4458 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4458step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4459 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4459step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw4460 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4460step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4461 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4461step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 1, -1, 1], ![2, 0, 1, -3]]

def raw4461step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw4462 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4462step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 1, 1, -1], ![2, 0, -1, -1]]

def raw4462step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw4463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4464 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![2, 0, 1, -3]]

def raw4464step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

def raw4465 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw4466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4466step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw4467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4467step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, -1, 0, -1, 1], ![-1, 2, 0, 0, -1], ![2, -1, 0, 0, -1]]

def raw4467step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 1, 0, 1, -1], ![1, -2, 0, 0, 1], ![-2, 1, 0, 0, 1]]

def raw4467step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![1, -2, 0, 1], ![-2, 1, 0, 1]]

def raw4467step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw4468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw4469 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4469step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw4469step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw4470 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4470step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw4470step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw4471 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4471step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-1, 2, -1, 0], ![2, -1, 0, -1]]

def raw4471step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4472 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4472step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4473 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4473step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw4473step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw4475 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4475step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw4476 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4476step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 2, 0, -1], ![2, -1, 0, -1]]

def raw4476step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![1, -2, 0, 1], ![-2, 1, 0, 1]]

def raw4476step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw4477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw4477step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 1, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0]]

def raw4477step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw4478 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4479 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw4479step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw4479step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw449 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw450 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw451 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]

def raw451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw452 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]

def raw452step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]

def raw452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw453 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw454 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]

def raw454step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw455 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]

def raw455step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

def raw456 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]

def raw456step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw457 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]

def raw457step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def raw459 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]

def raw459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw460 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]

def raw460step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]

def raw460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]

def raw461 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]

def raw461step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

def raw462 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw463 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def raw464 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]

def raw465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw466 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def raw467 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def raw468 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw469 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw470 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, 1, -2]]

def raw470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw471 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]

def raw471step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def raw472 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw473 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw474 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1], ![1, 0, -1]]

def raw474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def raw475 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]

def raw476 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

def raw476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]

def raw476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw477 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def raw478 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]

def raw478step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-2, -3, 5]]

def raw478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw479 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]

def raw479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4481 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4481step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw4482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4484 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw4485 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4485step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-1, 3, 0, -2], ![2, -2, 0, 0]]

def raw4485step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![1, -3, 0, 2], ![-2, 2, 0, 0]]

def raw4485step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw4486 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw4486step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw4486step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![1, -3, 2, 0], ![-2, 2, -1, 1]]

def raw4486step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw4487 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4487step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, 3, -1, -1], ![2, -2, 0, 0]]

def raw4487step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw4488 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, -2, 1]]

def raw4488step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-1, 3, 0, -2], ![2, -2, -1, 1]]

def raw4488step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![1, -3, 0, 2], ![-2, 2, 1, -1]]

def raw4488step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw4489 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4490 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4490step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw4491 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw4491step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw4492 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4493 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw4494step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -2, 0, 3], ![2, 2, -1, -3]]

def raw4494step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 2, 0, -3], ![-2, -2, 1, 3]]

def raw4494step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw4495 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw4497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -2, 3, 0], ![2, 2, -4, 0]]

def raw4498step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 2, -3, 0], ![-2, -2, 4, 0]]

def raw4498step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw4499 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4499step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -2, 1, 2], ![2, 2, 0, -4]]

def raw4499step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![1, 2, -1, -2], ![-2, -2, 0, 4]]

def raw4499step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def raw4500 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4501 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw4501step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -2, 3, 0], ![2, 2, -2, -2]]

def raw4501step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw4502 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4502step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -2, 0, 3], ![2, 2, 0, -4]]

def raw4502step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw4503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 0, 1, -2]]

def raw4503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw4504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw4504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -2, 3, 0], ![2, 2, -3, -1]]

def raw4504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, 2, -3, 0], ![-2, -2, 3, 1]]

def raw4504step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw4505 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw4505step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-1, -2, 3, 0], ![2, 2, -4, 0]]

def raw4505step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw4506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, 1, 1, -3], ![1, -2, 2, -1]]

def raw4506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4507 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4507step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw4507step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw4508 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4508step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw4509 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4509step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4510 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4510step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4511 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4512 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4513 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4514 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4514step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw4515 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw4515step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def raw4516 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4516step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, -1, 0, 0, 2], ![2, 1, 0, -1, -2]]

def raw4516step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 0, 2], ![2, 1, -1, -2]]

def raw4516step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw4517 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4518 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4518step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw4519 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw4520 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4520step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw4521 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4521step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw4522 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4523 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4524 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4524step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw4525 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4526 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4527 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw4527step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, -1, 3], ![2, 1, 0, -3]]

def raw4527step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def raw4528 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4528step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw4529 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4529step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 0, 2], ![2, 1, -1, -2]]

def raw4529step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw4530 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4530step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4530step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw4531 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4531step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 2, 0], ![2, 1, -3, 0]]

def raw4531step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 1, -2, 0], ![-2, -1, 3, 0]]

def raw4531step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw4532 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4533 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4533step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4534 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw4534step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, -1, 3, -1], ![2, 1, -4, 1]]

def raw4534step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![1, 1, -3, 1], ![-2, -1, 4, -1]]

def raw4534step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 1, 1, -3]]

def raw4535 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw4535step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![2, 1, 1, -4]]

def raw4535step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def raw4535step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw4536 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4536step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -1, 1, 1], ![2, 1, 0, -3]]

def raw4536step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![1, 1, -1, -1], ![-2, -1, 0, 3]]

def raw4536step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw4537 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4537step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, -1, 2, 0], ![2, 1, -1, -2]]

def raw4537step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4538 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4538step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![2, 1, 1, -4]]

def raw4538step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, 1, 1, -3], ![-2, -1, -1, 4]]

def raw4538step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw4539 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4539step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![2, 1, 0, -3]]

def raw4539step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def raw4539step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw4540 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw4540step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw4541 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw4541step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, -1, 2, 0], ![2, 1, -2, -1]]

def raw4541step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def raw4542 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4542step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, 0, 1, -1, 1], ![2, 0, -1, 0, -1]]

def raw4542step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -1, 1], ![2, -1, 0, -1]]

def raw4542step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4543 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4543step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, 0, 2, -1, 0], ![2, 0, -2, 0, 0]]

def raw4543step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, -1, 0], ![2, -2, 0, 0]]

def raw4543step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4544 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4544step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-1, 0, -1, 2, 0], ![2, 0, 0, -1, -1]]

def raw4544step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 2, 0], ![2, 0, -1, -1]]

def raw4544step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4545 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4545step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 0, -1, 2], ![2, 0, 0, -2]]

def raw4545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![-1, -1, 2], ![2, 0, -2]]

def raw4545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw4546 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4546step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-1, 0, 0, 2, -1], ![2, 0, -1, -1, 0]]

def raw4546step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 0, 2, -1], ![2, -1, -1, 0]]

def raw4546step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw4547 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4547step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![1, 0, 1, -2, 0], ![-1, 0, 1, 1, -1], ![2, 0, -2, 0, 0]]

def raw4547step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![-1, 0, -1, 2, 0], ![1, 0, -1, -1, 1], ![-2, 0, 2, 0, 0]]

def raw4547step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, -1, -1, 1], ![-2, 2, 0, 0]]

def raw4547step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw4548 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 0, 0], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw4548step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 0, 2, -1], ![2, 0, -1, -1]]

def raw4548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![2, -1, -1]]

def raw4548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4549 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4549step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![-1, 1, 0, -1, 1], ![2, -1, 0, 0, -1]]

def raw4549step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -1, 1], ![2, -1, 0, -1]]

def raw4549step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4550 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw4551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4551step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4552step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw4553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw4554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw4555 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4556 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4557step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4558 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4560 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw4560step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -2, 2], ![2, -1, 1, -2]]

def raw4560step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw4561 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw4561step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw4562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4562step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw4563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4563step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw4564 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4564step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, -1, 1], ![2, -1, 0, -1]]

def raw4564step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4565step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw4566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4567 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4567step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw4569 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def raw4569step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, 1, -1], ![2, -1, -2, 1]]

def raw4569step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw4570 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw4570step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 1, 2, -2], ![2, -1, -3, 2]]

def raw4570step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 2, -1, -2]]

def raw4571 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4571step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 1, 1, -1], ![2, -1, 0, -1]]

def raw4571step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw4572 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def raw4572step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 1, 2, -2], ![2, -1, -1, 0]]

def raw4572step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4573step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw4575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4576 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw4577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 0, -1]]

def raw4577step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw4578 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4578step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 2, -1, 0], ![-1, 0, 1, 0]]

def raw4578step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw4579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4579step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4579step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4580 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4580step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, -1, 0], ![2, -2, 0, 0]]

def raw4580step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def raw4581 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4581step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw4583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4583step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def raw4584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, 0, -1], ![2, -2, -1, 1]]

def raw4584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw4585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw4585step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 2, 1, -2], ![2, -2, -2, 2]]

def raw4585step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw4586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw4586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 2, 0, -1], ![2, -2, 1, -1]]

def raw4586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw4587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw4587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 1, -2], ![0, 0, -2, 2], ![-1, 2, -1, 0], ![-1, -1, 2, 0]]

def raw4587step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw4588 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4588step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, 2, -1, 0], ![2, -2, 1, -1]]

def raw4588step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw4589 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw4589step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4590 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, 0, -2, 1], ![1, -1, 1, -1]]

def raw4590step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4591 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4592 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw4592step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw4592step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw4593 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4594 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4595 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4595step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4596step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 3, -1, -1], ![2, -3, 0, 1]]

def raw4596step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 1, -2, 0]]

def raw4597 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4598 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw4599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4599step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-1, 3, 0, -2], ![2, -3, -1, 2]]

def raw4599step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 2, 2], ![0, 0, -2, 2], ![0, 3, -1, -2], ![1, 0, 1, -2]]

def raw4600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -2, 0]]

def raw4600step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-1, 3, 0, -2], ![2, -3, 1, 0]]

def raw4600step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw4601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw4601step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw4602 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4602step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, 3, -1, -1], ![2, -3, 1, 0]]

def raw4602step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw4603 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4603step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-1, 3, 0, -2], ![2, -3, 0, 1]]

def raw4603step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![1, -3, 0, 2], ![-2, 3, 0, -1]]

def raw4603step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw4604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, 0, -2, 1], ![1, -1, 0, 0]]

def raw4604step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw4604step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![1, -3, 2, 0], ![-2, 3, -1, 0]]

def raw4604step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw4605 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw4605step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-1, 3, -1, -1], ![2, -3, 0, 1]]

def raw4605step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw4606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4606step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4607step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -2, 0, 3], ![2, 1, 1, -4]]

def raw4607step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4609step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -2, 3, 0], ![2, 1, -2, -1]]

def raw4609step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, 2, -3, 0], ![-2, -1, 2, 1]]

def raw4609step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4610step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -2, 0, 3], ![2, 1, 0, -3]]

def raw4610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![1, 2, 0, -3], ![-2, -1, 0, 3]]

def raw4610step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw4611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw4612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw4613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, -1, 3], ![2, 0, 2, -4]]

def raw4613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw4614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw4614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 0, 2], ![2, 0, 1, -3]]

def raw4614step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw4615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 1, 1], ![2, 0, 0, -2]]

def raw4615step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, 1, -1, -1], ![-2, 0, 0, 2]]

def raw4615step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4616step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 2, 0], ![2, 0, -1, -1]]

def raw4616step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw4617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4617step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -1, -1, 3], ![2, 0, 1, -3]]

def raw4617step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw4618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4618step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -1, 0, 2], ![2, 0, 0, -2]]

def raw4618step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4619 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4619step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -1, 1, 1], ![2, 0, -1, -1]]

def raw4619step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw4620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4620step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 0, 2, -1], ![2, -1, -1, 0]]

def raw4620step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw4621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

def raw4621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 0, 3, -2], ![2, -1, -2, 1]]

def raw4621step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, 0, -3, 2], ![-2, 1, 2, -1]]

def raw4621step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4622 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4622step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 1, 1, -1], ![2, -2, 0, 0]]

def raw4622step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, -1, -1, 1], ![-2, 2, 0, 0]]

def raw4622step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw4623 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw4624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw4625 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4625step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 2, 0, -1], ![2, -3, 1, 0]]

def raw4625step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, -2, 0, 1], ![-2, 3, -1, 0]]

def raw4625step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def raw4626 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw4626step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 2, 1, -2], ![2, -3, 0, 1]]

def raw4626step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, 2, -1, 0], ![2, -3, 1, 0]]

def raw4627step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![1, -2, 1, 0], ![-2, 3, -1, 0]]

def raw4627step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def raw4628 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw4628step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 3, -1, -1], ![2, -4, 2, 0]]

def raw4628step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw4629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

def raw4629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 3, 0, -2], ![2, -4, 1, 1]]

def raw4629step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw4630 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4630step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, 3, -2, 0], ![2, -4, 2, 0]]

def raw4630step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw4631 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw4632 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -2, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw4632step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw4632step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw4633 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -2, 2, -1], ![0, 0, -2, 2], ![1, 1, 1, -3]]

def raw4633step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def raw4634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -2, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw4634step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw4634step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 2, -1, 0], ![1, -3, 2, 0], ![-2, 2, -1, 1]]

def raw4634step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw4635 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -1, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw4635step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![-1, -2, 3, 0], ![2, 2, -4, 0]]

def raw4635step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def raw4636 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -1, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4636step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4637 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw4637step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw4637step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 1, -1, 1], ![1, -3, 2, 0], ![-2, 3, -1, 0]]

def raw4637step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw4638 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4638step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def raw4639 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4639step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4640 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, -1, 3], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4640step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4641 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4641step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, 0, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw4641step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4642 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4642step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw4642step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw4643 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4643step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw4644 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4644step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw4644step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def raw4645 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4645step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -1, -1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw4645step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw4646 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw4646step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4647 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw4647step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, 0, 2, -1], ![-1, 0, 0, 1]]

def raw4647step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw4648 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4648step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def raw4648step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw4649 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw4649step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![0, -1, 0, 1], ![-2, 0, 2, 0]]

def raw4649step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw4650 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw4650step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 2, -2, 0], ![-1, 0, 2, -1], ![-1, -1, 0, 2]]

def raw4650step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw4651 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw4651step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw4651step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw4652 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4653 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4654 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw4655 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4655step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, -2, 0, 2], ![1, 3, 0, -4]]

def raw4655step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4656 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4656step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4657 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw4657step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4658 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4658step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw4658step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4659 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4659step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw4659step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4660 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4660step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4661 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw4661step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw4662 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4663 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![2, -1, 3, -4]]

def raw4663step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![0, -1, -2, 3], ![1, 2, 1, -4]]

def raw4663step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![-1, -2, -1, 4]]

def raw4663step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw4664 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4665 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4665step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw4665step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw4666 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw4667 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw4667step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw4668 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw4668step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![0, -1, -1, 2], ![1, 2, 0, -3]]

def raw4668step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def raw4669 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4669step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw4669step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw4670 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4671 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4672 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw4672step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![2, -1, -2, 1]]

def raw4673step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![0, -1, 3, -2], ![1, 2, -4, 1]]

def raw4673step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![0, 1, -3, 2], ![-1, -2, 4, -1]]

def raw4673step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw4674 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw4674step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw4674step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw4675 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4675step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw4675step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw4676 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw4676step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, -1, 3, -2], ![1, 2, -3, 0]]

def raw4676step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, 1, -3, 2], ![-1, -2, 3, 0]]

def raw4676step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw4677 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 0, -2, 1], ![1, 0, 3, -4]]

def raw4677step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4678 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw4678step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw4679 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 0, 3, -4], ![1, 0, -2, 1]]

def raw4679step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4680 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 1, 2, -4], ![1, -1, -1, 1]]

def raw4680step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![-1, -1, -2, 4], ![-1, 1, 1, -1]]

def raw4680step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw4681 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw4681step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw4681step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw4682step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw4682step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![-1, -1, -2, 4]]

def raw4682step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw4683 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw4683step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw4683step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![-1, 0, -2, 3]]

def raw4683step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw4684 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def raw4684step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw4684step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![-1, 0, 2, -1]]

def raw4684step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw4685 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4685step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4686 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4686step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw4687 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4687step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4688 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4688step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw4688step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def raw4689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw4689step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 2, -3, 1], ![1, -1, 3, -3]]

def raw4689step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, -2, 3, -1], ![-1, 1, -3, 3]]

def raw4689step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 0, -2]]

def raw4690step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw4691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw4691step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4692step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw4693 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw4694 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4694step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw4695 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw4695step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw4696 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![2, 0, -1, -1]]

def raw4696step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def raw4697 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4698 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![2, -1, 0, -1]]

def raw4699 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4700 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4700step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw4701 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![2, -1, -1, 0]]

def raw4701step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw4702 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw4703 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4703step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4704 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4704step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw4705 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw4706 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw4707 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw4708 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw4708step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 3, -3, 0], ![1, -2, 3, -2]]

def raw4708step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def raw4709 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 1, -1, -1]]

def raw4710 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw4710step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw4711 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw4711step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 3, 0, -3], ![1, -2, 0, 1]]

def raw4711step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw4712 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, -3, 2], ![1, 0, 0, -1]]

def raw4712step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4713 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 0, -1, 0]]

def raw4713step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw4714 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 0, -2, 1]]

def raw4714step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw4715 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, -3, 2]]

def raw4715step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4716 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, -1, -1, 1]]

def raw4716step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw4717 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4718 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw4718step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -3, 0, 3], ![1, 3, -1, -3]]

def raw4718step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 3, 0, -3], ![-1, -3, 1, 3]]

def raw4718step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw4719 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw4719step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -3, 1, 2], ![1, 3, -2, -2]]

def raw4719step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]

def raw4720 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4721 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4722 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4723 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4723step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4724 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw4724step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4725 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4726 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4727 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4727step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![0, -2, 0, 0, 2], ![1, 2, 0, -1, -2]]

def raw4727step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![-1, 0, 0, -1, 2], ![0, 2, 0, 0, -2], ![-1, -2, 0, 1, 2]]

def raw4727step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![-1, -2, 1, 2]]

def raw4727step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw4728 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4729 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4729step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw4729step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw4730 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4731 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -1, 0, -1]]

def raw4731step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4732 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4733 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4734 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw4734step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -2, -1, 3], ![1, 2, 0, -3]]

def raw4734step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw4735 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4735step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 2, -2, 1], ![-1, 0, 0, 1]]

def raw4735step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4736 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4736step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -2, 0, 2], ![1, 2, -1, -2]]

def raw4736step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![-1, -2, 1, 2]]

def raw4736step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw4737 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw4737step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, -1, 2], ![-2, 2, -1, 1]]

def raw4737step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw4738 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4738step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4738step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw4739 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4739step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, -2, 3], ![-2, 2, 0, 0]]

def raw4739step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw4740 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4741 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4741step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4742 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw4742step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -2, 3, -1], ![1, 2, -4, 1]]

def raw4742step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 2, -3, 1], ![-1, -2, 4, -1]]

def raw4742step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def raw4743 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw4743step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw4743step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw4744 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4744step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -2, 1, 1], ![1, 2, 0, -3]]

def raw4744step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![-1, -2, 0, 3]]

def raw4744step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw4745 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw4745step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -2, 3, -1], ![1, 2, -2, -1]]

def raw4745step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw4746 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4746step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4747 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4747step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw4748 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw4748step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, -2, 3, -1], ![1, 2, -3, 0]]

def raw4748step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw4749 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw4749step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![0, -2, -1, 3], ![1, 2, 0, -3]]

def raw4749step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw4750 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, 0, 3, -4], ![1, -1, -1, 1]]

def raw4750step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4751 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw4751step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw4751step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4753step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-2, 2, 0, 0]]

def raw4754step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw4756 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw4756step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw4756step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4757step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw4758 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4758step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw4759 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw4759step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw4760 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4760step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![0, -1, 0, -1, 2], ![1, 1, 0, 0, -2]]

def raw4760step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, -1, 2], ![1, 1, 0, -2]]

def raw4760step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw4762 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4762step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 2, -1, 1]]

def raw4762step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw4764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 2, 0, 0]]

def raw4764step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw4765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw4766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4767 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![2, -2, 3, -3]]

def raw4768step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, -2, 3], ![1, 1, 1, -3]]

def raw4768step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def raw4769 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw4769step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw4770step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, 0, -2, 3]]

def raw4770step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4771 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4771step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw4772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4773step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw4774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, -1, -1, 1]]

def raw4774step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4775 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4775step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, -1, 2], ![1, 1, 0, -2]]

def raw4775step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4776 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4776step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 0, 0]]

def raw4776step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def raw4777step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, 2, -1], ![1, 1, -3, 1]]

def raw4777step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![-1, -1, 3, -1]]

def raw4777step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw4778 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw4778step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4779 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4780 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw4781 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -2, 2]]

def raw4781step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, 3, -2], ![1, 1, -4, 2]]

def raw4781step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 1, -3, 2], ![-1, -1, 4, -2]]

def raw4781step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw4782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw4782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -1, -1, 2], ![1, 1, 2, -4]]

def raw4782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![-1, -1, -2, 4]]

def raw4782step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw4783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -2, 3, -2], ![1, 1, -2, 0]]

def raw4783step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -1, 3, -2], ![1, 1, -2, 0]]

def raw4783step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw4784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 0, 3, -4]]

def raw4784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, -1, -2, 3], ![1, 1, 2, -4]]

def raw4784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![0, 1, 2, -3], ![-1, -1, -2, 4]]

def raw4784step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw4785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw4785step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, -1, 3, -2], ![1, 1, -3, 1]]

def raw4785step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw4786 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 0, 0], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw4786step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 0, -2, 2], ![1, 0, 1, -2]]

def raw4786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, -2, 2], ![1, 1, -2]]

def raw4786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw4787 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 0, 0], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def raw4787step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 0, 2, -2], ![1, 0, -3, 2]]

def raw4787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, 2, -2], ![1, -3, 2]]

def raw4787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw4788 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4788step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 2, 1, -1]]

def raw4788step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw4789 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4789step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4790 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -3, 3]]

def raw4791 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw4792 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw4793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![2, -2, 2, -2]]

def raw4793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, -3, 2], ![1, -1, 2, -2]]

def raw4793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -1, 3, -2], ![-1, 1, -2, 2]]

def raw4793step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw4794 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4794step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw4795 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw4795step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4795step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -1, 2, -1], ![-1, 1, -1, 1]]

def raw4795step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4796 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw4797 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4797step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw4798 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw4798step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4799 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw4799step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw4799step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw480 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]

def raw480step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-2, -2, 4]]

def raw480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw481 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 1, -2]]

def raw481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def raw482 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]

def raw482step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw483 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, 0, -1]]

def raw483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-1, 0, 1], ![-1, 0, 1]]

def raw483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw484 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

def raw484step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]

def raw484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw485 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]

def raw485step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -3, 4], ![-2, 1, 1]]

def raw485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw486 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![2, 0, -2], ![1, 2, -3]]

def raw486step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-2, 0, 2], ![-1, -2, 3]]

def raw486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw487 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]

def raw487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]

def raw487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]

def raw487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw488 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]

def raw488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]

def raw488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw489 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]

def raw489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -2, 3], ![-2, 1, 1]]

def raw489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]

def raw489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw490 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]

def raw490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw491 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw492 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]

def raw493 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]

def raw493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw494 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]

def raw494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw495 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def raw496 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw497 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw498 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw499 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]

def raw499step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]

def raw499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw500 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw501 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw502 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]

def raw503 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw504 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw505 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw505step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw506 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

def raw506step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]

def raw506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw507 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw507step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw508 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]

def raw508step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]

def raw508step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw509 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw510 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]

def raw510step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, 2, -1], ![-2, -2, 4]]

def raw510step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-2, -2, 4]]

def raw510step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw511 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4800 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -3, 3]]

def raw4800step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw4800step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -1, -2, 3], ![-1, 1, 3, -3]]

def raw4800step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, 3, -3]]

def raw4801 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -2, -2, 3], ![1, 1, 1, -3]]

def raw4801step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def raw4801step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, -1, 2, -1], ![-1, 1, -3, 3]]

def raw4801step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw4802 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -3, 1]]

def raw4802step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw4802step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, -1, -2, 3], ![-1, 1, 1, -1]]

def raw4802step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw4803 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 0, 2, -3]]

def raw4803step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, 1, -3, 2], ![1, -1, 3, -3]]

def raw4803step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![0, -1, 3, -2], ![-1, 1, -3, 3]]

def raw4803step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def raw4804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 0, -3, 2]]

def raw4804step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw4804step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![0, -1, -2, 3], ![-1, 1, 2, -2]]

def raw4804step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw4805 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4805step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4806 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw4806step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw4807 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw4807step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw4808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -3, 2], ![2, -2, 1, -1]]

def raw4808step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, -3, 1], ![1, -2, 2, -1]]

def raw4808step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -2, 3, -1], ![-1, 2, -2, 1]]

def raw4808step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw4809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4809step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4809step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw4810 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def raw4810step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -2, 2], ![0, -1, 2, -1], ![-2, 2, 0, 0]]

def raw4810step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw4811 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4811step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, 0, 1, 0]]

def raw4811step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw4813 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4813step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw4814 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def raw4814step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, -1, -1], ![1, -2, 0, 1]]

def raw4814step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -2, 1, 1], ![-1, 2, 0, -1]]

def raw4814step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4815 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4815step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw4816 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def raw4816step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw4816step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw4817 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -3, 3]]

def raw4817step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def raw4817step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

def raw4818 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -2, -2, 3], ![1, 1, 0, -2]]

def raw4818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4819 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 0, 1, -2]]

def raw4819step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 0, 1]]

def raw4820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw4820step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw4821 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, 0, -3, 2], ![1, -1, 1, -1]]

def raw4821step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4822step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw4823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4824 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw4824step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 3, -1, -2], ![1, -3, 0, 2]]

def raw4824step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -3, 1, 2], ![-1, 3, 0, -2]]

def raw4824step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -3, 2]]

def raw4825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw4825step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, 3, 0, -3], ![1, -3, -1, 3]]

def raw4825step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, -3, 0, 3], ![-1, 3, 1, -3]]

def raw4825step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 2, 0, -2], ![1, -1, 3, -3]]

def raw4826 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw4826step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, 3, -2, -1], ![1, -3, 2, 0]]

def raw4826step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4827 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw4827step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw4828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw4828step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4829 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, 0, -3, 2], ![1, -1, 0, 0]]

def raw4829step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![0, 0, 2, -2], ![2, -2, 1, -1]]

def raw4830step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 1, 0, -2], ![0, -3, 2, 1], ![1, 2, -2, -1]]

def raw4830step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, -1, 0, 2], ![0, 3, -2, -1], ![-1, -2, 2, 1]]

def raw4830step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw4831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw4831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -3, 0, 3], ![1, 2, 1, -4]]

def raw4831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -2, 1, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4832 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4832step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -3, 3, 0], ![1, 2, -2, -1]]

def raw4832step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1]]

def raw4833 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4833step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -3, 0, 3], ![1, 2, 0, -3]]

def raw4833step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def raw4834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw4834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -2, -1, 3], ![1, 1, 2, -4]]

def raw4834step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw4835 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw4835step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, 2, -1], ![-1, 2, 0, -1], ![-1, 0, -2, 3]]

def raw4835step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw4836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw4836step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![0, -2, 3, -1], ![1, 1, -2, 0]]

def raw4836step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw4837 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4837step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -2, -1, 3], ![1, 1, 1, -3]]

def raw4837step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4838 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4838step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -2, 0, 2], ![1, 1, 0, -2]]

def raw4838step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![0, 2, 0, -2], ![-1, -1, 0, 2]]

def raw4838step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw4839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw4840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 3, -3]]

def raw4840step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -1, -2, 3], ![1, 0, 2, -3]]

def raw4840step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![0, 1, 2, -3], ![-1, 0, -2, 3]]

def raw4840step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw4841 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw4841step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, -1, -1, 2], ![1, 0, 1, -2]]

def raw4841step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw4842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw4842step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, 0, -2, 2], ![1, -1, 2, -2]]

def raw4842step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![0, 0, 2, -2], ![-1, 1, -2, 2]]

def raw4842step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw4843 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4843step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 1, -1, 1]]

def raw4843step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw4844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw4844step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4845 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw4845step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4846 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 2, -3], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4846step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, 2, -2, 0], ![1, -3, 2, 0]]

def raw4846step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4847 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def raw4847step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 1, -1]]

def raw4847step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw4848 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -3, 3], ![1, -1, 0, 0]]

def raw4848step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![0, 3, -3, 0], ![1, -4, 3, 0]]

def raw4848step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw4849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

def raw4850 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -2, 2]]

def raw4850step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

def raw4851 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, -2, 3], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw4851step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, -2, 3, -1], ![1, 3, -4, 0]]

def raw4851step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw4852 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, -1, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw4852step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, -1, -2, 3], ![1, 2, 1, -4]]

def raw4852step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

def raw4853 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, -1, 2], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw4853step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, -1, 3, -2], ![1, 2, -4, 1]]

def raw4853step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4854 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 3, -2], ![0, 0, -2, 2], ![1, 1, -1, -1]]

def raw4854step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![0, 3, -2, -1], ![1, -2, 2, -1]]

def raw4854step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw4855 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 3, -2], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw4855step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![0, 3, -3, 0], ![1, -2, 2, -1]]

def raw4855step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1]]

def raw4856 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw4856step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![0, -3, 3, 0], ![1, 3, -4, 0]]

def raw4856step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def raw4857 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw4857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

def raw4858 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 3, -3], ![0, 1, -2, 1], ![1, -1, -1, 1]]

def raw4858step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![0, 3, -2, -1], ![1, -3, 1, 1]]

def raw4858step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw4859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw4860 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw4860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw4860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4861 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]

def raw4861step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

def raw4862 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw4863 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]

def raw4863step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 2, -3], ![-1, 1, 0], ![-2, -2, 4]]

def raw4863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4864 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![2, -2, 0], ![1, 3, -4]]

def raw4864step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 2, -3], ![-2, 2, 0], ![-1, -3, 4]]

def raw4864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

def raw4865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw4865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw4865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw4868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw4868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw4869 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw4869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw4869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4870 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw4870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw4870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]

def raw4871 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw4871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4872 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw4872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw4873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def raw4874 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]

def raw4874step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 2, -1], ![-2, -2, 4]]

def raw4874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw4875 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 3, -4]]

def raw4875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

def raw4876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw4876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4878 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]

def raw4878step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4879 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, -3, 1], ![1, 3, -4]]

def raw4879step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-2, 3, -1], ![-1, -3, 4]]

def raw4879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def raw4880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw4880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw4882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw4882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw4884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw4884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw4885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw4887 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw4888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]

def raw4891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw4892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4893 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4894 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 3, -2], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

def raw4894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw4895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw4895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]

def raw4895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4896 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw4897 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4898 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw4898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw4899 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw4900 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw4901 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![2, 0, -2]]

def raw4901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![0, -2, 2], ![-2, 0, 2]]

def raw4901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw4902 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw4903 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

def raw4904 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw4905 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw4906 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw4907 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]

def raw4907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw4908 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]

def raw4908step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw4908step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw4909 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw4910 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw4911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2]]

def raw4911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw4911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4912 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw4913 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw4914 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw4914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw4915 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]

def raw4915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 0, 2]]

def raw4915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw4916 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw4917 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]

def raw4917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw4918 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw4919 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw4919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw4921 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw4922 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw4923 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

def raw4923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4924 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]

def raw4924step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4925 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]

def raw4925step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw4925step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw4926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw4926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw4927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

def raw4927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw4928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw4928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw4931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw4932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw4933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]

def raw4934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw4935 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]

def raw4935step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw4936 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw4936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw4936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw4937 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]

def raw4937step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw4939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]

def raw4939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw4940 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4941 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4942 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw4942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4943 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw4944 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw4945 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw4946 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw4947 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw4947step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw4947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw4948 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]

def raw4948step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

def raw4949 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]

def raw4949step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw4949step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw4949step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw4950 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![2, -1, -1]]

def raw4950step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]

def raw4950step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw4951 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

def raw4951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw4952 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

def raw4952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

def raw4953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw4953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw4954 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw4954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw4955 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw4955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]

def raw4955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw4956 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]

def raw4956step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]

def raw4956step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw4957 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw4957step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw4958 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4958step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4959 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 3, -3], ![1, -3, 2], ![1, -1, 0]]

def raw4959step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4960 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 3, -3], ![1, -2, 1], ![1, -2, 1]]

def raw4960step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw4961 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![0, 2, -2], ![1, 1, -2]]

def raw4961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw4962 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![0, 3, -3], ![1, 0, -1]]

def raw4962step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw4963 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 3, -4]]

def raw4964 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1]]

def raw4964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw4965 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw4966 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

def raw4967 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]

def raw4967step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw4967step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

def raw4968 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-2, -2, 1, 3], ![4, 1, -2, -3]]

def raw4968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 1, -2], ![0, 3, -3]]

def raw4968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

def raw4969 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-2, -2, 2, 2], ![4, 1, -3, -2]]

def raw4969step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 2, -3], ![0, 2, -2]]

def raw4969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def raw4970 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-2, 1, 2, -1], ![4, -2, -3, 1]]

def raw4970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 2, -3], ![0, -1, 1]]

def raw4970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw4971 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, -2, 1, 2], ![3, 1, -2, -2]]

def raw4971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 1, -2], ![0, 2, -2]]

def raw4971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw4972 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, -2, 2, 1], ![3, 1, -3, -1]]

def raw4972step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 2, -3], ![0, 1, -1]]

def raw4972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw4973 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, 1, 1, -1], ![3, -2, -2, 1]]

def raw4973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 1, -2], ![1, 1, -2], ![0, -1, 1]]

def raw4973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw4974 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, 1, 2, -2], ![3, -2, -3, 2]]

def raw4974step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 1, -2], ![1, 2, -3], ![0, -2, 2]]

def raw4974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def raw4975 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -3, 1, 2], ![2, 2, -2, -2]]

def raw4975step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![1, 1, -2], ![0, 2, -2]]

def raw4975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw4976 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -3, 2, 1], ![2, 2, -3, -1]]

def raw4976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![1, 2, -3], ![0, 1, -1]]

def raw4976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def raw4977 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, -2, 4], ![2, 1, 1, -4]]

def raw4977step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, -2, 1], ![0, 4, -4]]

def raw4977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def raw4978 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, -1, 3], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4978step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, -1, 3], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4979step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![1, -1, -1, 1], ![0, 3, 0, -3]]

def raw4979step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw4980 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4980step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw4981 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, 1, 1], ![2, 1, -2, -1]]

def raw4981step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1]]

def raw4981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw4982 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, 3, -1], ![2, 1, -4, 1]]

def raw4982step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 3, -4], ![0, -1, 1]]

def raw4982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw4983 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4984 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4985step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw4986 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![2, 0, 0, -2]]

def raw4987step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw4988 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4989 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw4990step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![1, -3, 1, 1], ![0, 4, -2, -2]]

def raw4990step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw4991 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw4992step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 1, 3, -4], ![0, -1, -2, 3], ![-2, 1, 0, 1]]

def raw4992step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

def raw4993 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw4993step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -3, 0, 2], ![0, 4, 0, -4]]

def raw4993step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, -2, 0, 1]]

def raw4994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw4995step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -3, 2, 0], ![0, 4, -2, -2]]

def raw4995step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw4996 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw4996step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw4997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw4997step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw4998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, 1, 1, -3], ![1, -1, 1, -1]]

def raw4998step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw4999 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw5000 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5000step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw5001 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5001step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw5002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw5002step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -2, -1, 2], ![0, 3, 1, -4]]

def raw5002step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]

def raw5003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw5003step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -2, 0, 1], ![0, 3, 0, -3]]

def raw5003step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw5004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw5004step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw5005 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw5006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![2, 1, 1, -4]]

def raw5006step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, -1, 1], ![1, -1, -1, 1], ![0, 2, 2, -4]]

def raw5006step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, 1, -1], ![-1, 1, 1, -1], ![0, -2, -2, 4]]

def raw5006step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw5007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw5008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![2, 0, 2, -4]]

def raw5008step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def raw5009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw5010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw5010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw5011 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw5011step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw5012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw5012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -1, -2, 2], ![0, 2, 2, -4]]

def raw5012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, 1, 2, -2], ![0, -2, -2, 4]]

def raw5012step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw5013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw5013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, -1, -1, 1], ![0, 2, 1, -3]]

def raw5013step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, 1, 1, -1], ![0, -2, -1, 3]]

def raw5013step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw5014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw5014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw5015 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw5015step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw5016 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw5017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw5017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, -1, 2]]

def raw5017step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 1, 0], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw5018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, 1, -3, 1], ![0, 0, 3, -3]]

def raw5018step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, -1, 3, -1], ![0, 0, -3, 3]]

def raw5018step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw5019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 2, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw5019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![1, 2, -3, 0], ![0, -1, 3, -2]]

def raw5019step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-1, -2, 3, 0], ![0, 1, -3, 2]]

def raw5019step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw5020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -3, 3], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw5020step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, -3, 0, 2], ![0, 3, -1, -2]]

def raw5020step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![-1, 3, 0, -2], ![0, -3, 1, 2]]

def raw5020step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -3, 2]]

def raw5021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw5021step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, -2, -1, 2], ![0, 2, 0, -2]]

def raw5021step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw5022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw5022step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, -2, 2, -1], ![0, 2, -1, -1]]

def raw5022step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw5023 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw5023step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5024 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw5024step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw5025 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw5025step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw5026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 1, 1, -3]]

def raw5026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, -1, -1, 1], ![0, 1, 2, -3]]

def raw5026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![-1, 1, 1, -1], ![0, -1, -2, 3]]

def raw5026step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw5027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw5027step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, -1, 2]]

def raw5027step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw5028 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw5028step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 2, 2, -2]]

def raw5028step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw5029 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw5029step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw5030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw5030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 2, -2], ![-1, 1, -1, 1]]

def raw5030step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5031 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -3, 3]]

def raw5031step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, 1, 1, -3], ![0, -1, -2, 3]]

def raw5031step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def raw5032 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![1, -2, -3, 4], ![1, 1, 1, -3]]

def raw5032step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, 1, -3, 1], ![0, -1, 4, -3]]

def raw5032step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![-1, -1, 3, -1], ![0, 1, -4, 3]]

def raw5032step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 3, -4]]

def raw5033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 0, 1, -2]]

def raw5033step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![1, 1, -3, 1], ![0, -1, 3, -2]]

def raw5033step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw5034 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw5034step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 1, 2, -2], ![-1, 1, 0, 0]]

def raw5034step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw5035 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw5035step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, 2, -1, -2], ![0, -2, 0, 2]]

def raw5035step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![-1, -2, 1, 2], ![0, 2, 0, -2]]

def raw5035step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw5036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw5036step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, 2, 0, -3], ![0, -2, -1, 3]]

def raw5036step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw5037 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![1, -2, -3, 4], ![1, 1, 0, -2]]

def raw5037step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, 2, -3, 0], ![0, -2, 4, -2]]

def raw5037step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw5038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 0, 0, -1]]

def raw5038step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![1, 2, -3, 0], ![0, -2, 3, -1]]

def raw5038step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw5039 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw5039step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![1, -3, 2, 0], ![0, 2, -1, -1]]

def raw5039step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw5040 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw5040step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![1, -1, -2, 2], ![0, 0, 2, -2]]

def raw5040step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![-1, 1, 2, -2], ![0, 0, -2, 2]]

def raw5040step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw5041 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw5041step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![0, -2, 2]]

def raw5041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def raw5042 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, 2, -3], ![2, -2, -3, 3]]

def raw5042step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 2, -3], ![0, -3, 3]]

def raw5042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def raw5043 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -4, 2, 1], ![1, 3, -3, -1]]

def raw5043step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 2, -3], ![0, 1, -1]]

def raw5043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def raw5044 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -3, 1, 1], ![1, 2, -2, -1]]

def raw5044step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1]]

def raw5044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw5045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -3, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw5045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![1, -3, 2, 0], ![0, 4, -2, -2]]

def raw5045step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw5046 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -3, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5046step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![1, -3, 1, 1], ![0, 4, -2, -2]]

def raw5046step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 1, -3]]

def raw5047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -3, 4], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![1, -3, 2, 0], ![0, 4, -3, -1]]

def raw5047step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def raw5048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw5048step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![1, -1, -2, 2], ![0, 2, 2, -4]]

def raw5048step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 2, 0, -1], ![-1, 1, 2, -2], ![0, -2, -2, 4]]

def raw5048step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def raw5049 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, 3, -2], ![1, 1, -4, 2]]

def raw5049step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 3, -4], ![0, -2, 2]]

def raw5049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def raw5050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -1, -3, 3], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw5050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![1, -3, 1, 1], ![0, 3, -2, -1]]

def raw5050step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw5051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -1, -2, 2], ![0, -1, -1, 2], ![1, 1, 2, -4]]

def raw5051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, -1, 1], ![1, -2, -1, 2], ![0, 2, 2, -4]]

def raw5051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 1, 1, -1], ![-1, 2, 1, -2], ![0, -2, -2, 4]]

def raw5051step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw5052 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, 1, 1, -3], ![1, -2, -2, 3]]

def raw5052step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 1, -2], ![1, 1, -2], ![0, -3, 3]]

def raw5052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def raw5053 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -3, 2, 1], ![2, 2, -4, 0]]

def raw5053step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![2, 2, -4], ![-1, 1, 0]]

def raw5053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw5054 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -2, 2, 0], ![2, 1, -4, 1]]

def raw5054step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![2, 2, -4], ![-1, 0, 1]]

def raw5054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-2, -2, 4], ![1, 0, -1]]

def raw5054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw5055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5057 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw5057step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![2, -3, 1, 0], ![-1, 4, -2, -1]]

def raw5057step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw5058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw5058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, -3, 0, 1], ![-1, 4, 0, -3]]

def raw5058step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-2, 3, 0, -1], ![1, -4, 0, 3]]

def raw5058step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 3, 1, -4], ![1, -1, -1, 1]]

def raw5059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw5059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, -3, 1, 0], ![-1, 4, -1, -2]]

def raw5059step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw5060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw5060step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![2, -3, 1, 0], ![-1, 4, -2, -1]]

def raw5060step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw5061 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5061step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw5062 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, -2, 0, 0], ![-1, 3, 0, -2]]

def raw5062step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-2, 2, 0, 0], ![1, -3, 0, 2]]

def raw5062step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def raw5063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5063step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -2, 1], ![0, 1, 1, -2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw5063step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw5064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, 1, 0], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw5064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![2, 1, -3, 0], ![-1, 0, 3, -2]]

def raw5064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-2, -1, 3, 0], ![1, 0, -3, 2]]

def raw5064step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw5065 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 0, 1, -1], ![1, -2, -3, 4], ![1, 1, 0, -2]]

def raw5065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![2, 1, -3, 0], ![-1, -1, 4, -2]]

def raw5065step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def raw5066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 0, 0, -1]]

def raw5066step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![2, 1, -3, 0], ![-1, -1, 3, -1]]

def raw5066step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw5067 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 1, -3, 2], ![2, -2, 1, -1]]

def raw5067step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![2, -3, 1], ![-1, 2, -1]]

def raw5067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw5068 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 2, -2, 0], ![2, -3, 0, 1]]

def raw5068step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![2, -2, 0], ![-1, 0, 1]]

def raw5068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -2, 3], ![-2, 2, 0], ![1, 0, -1]]

def raw5068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw5069 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 3, -3, 0], ![2, -4, 1, 1]]

def raw5069step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 3, -4], ![2, -3, 1], ![-1, 0, 1]]

def raw5069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -3, 4], ![-2, 3, -1], ![1, 0, -1]]

def raw5069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw5070 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, 3, -2, -1], ![2, -4, 0, 2]]

def raw5070step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 3, -4], ![2, -2, 0], ![-1, -1, 2]]

def raw5070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, -3, 4], ![-2, 2, 0], ![1, 1, -2]]

def raw5070step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw5071 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, -3, 2, 0], ![1, 2, -4, 1]]

def raw5071step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![2, 2, -4], ![-1, 0, 1]]

def raw5071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw5072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, -2, -3, 4], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![2, -3, 1, 0], ![-1, 4, -2, -1]]

def raw5072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw5073 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, -2, 2, -1], ![1, 1, -4, 2]]

def raw5073step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![2, 2, -4], ![-1, -1, 2]]

def raw5073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 2, -1], ![-2, -2, 4], ![1, 1, -2]]

def raw5073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw5074 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, 1, -3, 1], ![1, -2, 1, 0]]

def raw5074step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 1, -2], ![2, -3, 1], ![-1, 1, 0]]

def raw5074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw5075 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![1, 2, -2, -1], ![1, -3, 0, 2]]

def raw5075step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 2, -3], ![2, -2, 0], ![-1, -1, 2]]

def raw5075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw5076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5077 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5077step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![3, -3, 0, 0], ![-2, 4, 0, -2]]

def raw5077step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![-3, 3, 0, 0], ![2, -4, 0, 2]]

def raw5077step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -4, 2], ![1, -1, 1, -1]]

def raw5078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -3, 4], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5078step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, -3, 0, 0], ![-2, 4, -1, -1]]

def raw5078step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def raw5079 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5079step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw5080 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5081 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw5081step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw5083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw5083step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, -2, -1, 0], ![-2, 3, 0, -1]]

def raw5083step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![-3, 2, 1, 0], ![2, -3, 0, 1]]

def raw5083step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw5084 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw5085 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw5085step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw5086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![2, 0, 0, -2]]

def raw5086step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

def raw5087 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5088 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5088step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw5089 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw5090 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw5090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw5091 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 0, -2]]

def raw5092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw5092step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![3, -1, -2, 0], ![-2, 2, 1, -1]]

def raw5092step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 0, 0], ![-3, 1, 2, 0], ![2, -2, -1, 1]]

def raw5092step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw5093 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5093step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, -3, 0, 0], ![-2, 3, 0, -1]]

def raw5093step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![-3, 3, 0, 0], ![2, -3, 0, 1]]

def raw5093step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def raw5094 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def raw5094step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw5095 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -2, 2], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw5095step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![3, -2, -1, 0], ![-2, 2, 2, -2]]

def raw5095step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw5096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw5096step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, -2, -1, 0], ![-2, 2, 1, -1]]

def raw5096step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![-3, 2, 1, 0], ![2, -2, -1, 1]]

def raw5096step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw5097 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw5097step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw5098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def raw5098step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![3, -1, -2, 0], ![-2, 1, 2, -1]]

def raw5098step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw5099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 0, 0, -1]]

def raw5099step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![3, 0, -3, 0], ![-2, -1, 4, -1]]

def raw5099step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw5100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![1, -2, -1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def raw5100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![3, -1, -2, 0], ![-2, 2, 2, -2]]

def raw5100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw5101 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![2, -2], ![2, -2]]

def raw5101step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

def raw5102 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def raw5103 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]

def raw5103step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

def raw5104 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![2, -2]]

def raw5104step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![2, -2], ![2, -2]]

def raw5104step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw5105 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw5105step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5106 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![0, 0], ![2, -2], ![2, -2]]

def raw5106step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw5107 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]

def raw5107step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5108 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]

def raw5108step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5109 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw5110 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5111 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]

def raw5111step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5112 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]

def raw5112step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def raw5113 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![0, 0], ![1, -1], ![1, -1]]

def raw5113step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]

def raw5113step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5114 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![0, 0], ![2, -2]]

def raw5114step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw5115 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]

def raw5115step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5116 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

def raw5117 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]

def raw5117step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw5118 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def raw5118step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw5119 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![2, -2]]

def raw5119step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]

def raw5119step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw512 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]

def raw512step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, -2, 3], ![-2, 2, 0]]

def raw512step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]

def raw512step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw513 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]

def raw513step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5120 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw5122 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]

def raw5122step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw5123 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw5123step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5123step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5124 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw5124step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw5124step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5124step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5125 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]

def raw5125step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw5125step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5125step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5126 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

def raw5126step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5126step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5127 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw5127step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5128 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5128step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5129 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]

def raw5129step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5129step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5130 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]

def raw5130step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw5130step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5130step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5131 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw5131step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5131step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5132 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw5132step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5132step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5133 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3], ![0, 0]]

def raw5133step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw5133step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5133step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw5134 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw5134step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5134step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5135 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw5135step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5136 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5136step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5137 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]

def raw5137step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5137step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5138 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw5138step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5139 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5140 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw5140step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5141 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5142 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw5142step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw5143 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0], ![0, 0]]

def raw5143step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw5143step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7978step1 : Matrix (Fin 0) (Fin 1) ℤ := ![]

end MUB6.Certificate.PairSemantics

end OAI
end


