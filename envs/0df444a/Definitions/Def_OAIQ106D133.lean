-- Prove2me | Definitions.Def_OAIQ106D133
-- name    : OAIQ106D133
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:24:49.515016+00:00
-- url     : https://prove2.me/theorems/0dcfad88-1053-4e8c-a450-d3dacb976b71
-- title:
--   Definitions bundle OAIQ106D133 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1612 declarations of OpenAI's Lean: 1612 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.nodeValue4177`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4179`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4180`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4181`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4182`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4183`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4184`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4185`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4186`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4187`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4188`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4189`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4190`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4191`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4192`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4193`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4194`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4195`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4196`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4197`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4198`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4199`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4200`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4201`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4202`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4203`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4204`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4205`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4207`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4209`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4210`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4211`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4212`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4213`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4214`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4216`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4217`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4218`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4219`, `OAI.MUB6.Certificate.MixedSemantics.nodeValue4221` and 1572 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Single0`, `MutuallyUnbiased_MixedSemantics_Single1`, `MutuallyUnbiased_MixedSemantics_Single2`, `MutuallyUnbiased_MixedSemantics_SingleGroup0`, `MutuallyUnbiased_MixedSemantics_SingleGroup16`, `MutuallyUnbiased_MixedSemantics_SingleGroup5`, `MutuallyUnbiased_MixedSemantics_SingleGroup6`, `MutuallyUnbiased_MixedSemantics_SingleGroup7`, `MutuallyUnbiased_MixedSemantics_Values0`, `MutuallyUnbiased_MixedSemantics_Values1`, `MutuallyUnbiased_MixedSemantics_Values10`, `MutuallyUnbiased_MixedSemantics_Values11`, `MutuallyUnbiased_MixedSemantics_Values12`, `MutuallyUnbiased_MixedSemantics_Values13`, `MutuallyUnbiased_MixedSemantics_Values14`, `MutuallyUnbiased_MixedSemantics_Values15`, `MutuallyUnbiased_MixedSemantics_Values6`, `MutuallyUnbiased_MixedSemantics_Values65`, `MutuallyUnbiased_MixedSemantics_Values66`, `MutuallyUnbiased_MixedSemantics_Values67`, `MutuallyUnbiased_MixedSemantics_Values68`, `MutuallyUnbiased_MixedSemantics_Values69`, `MutuallyUnbiased_MixedSemantics_Values7`, `MutuallyUnbiased_MixedSemantics_Values70`, `MutuallyUnbiased_MixedSemantics_Values71`, `MutuallyUnbiased_MixedSemantics_Values72`, `MutuallyUnbiased_MixedSemantics_Values73`, `MutuallyUnbiased_MixedSemantics_Values74`, `MutuallyUnbiased_MixedSemantics_Values75`, `MutuallyUnbiased_MixedSemantics_Values76`, `MutuallyUnbiased_MixedSemantics_Values77`, `MutuallyUnbiased_MixedSemantics_Values78`, `MutuallyUnbiased_MixedSemantics_Values79`, `MutuallyUnbiased_MixedSemantics_Values8`, `MutuallyUnbiased_MixedSemantics_Values80`, `MutuallyUnbiased_MixedSemantics_Values81`, `MutuallyUnbiased_MixedSemantics_Values82`, `MutuallyUnbiased_MixedSemantics_Values83`, `MutuallyUnbiased_MixedSemantics_Values84`, `MutuallyUnbiased_MixedSemantics_Values85`, `MutuallyUnbiased_MixedSemantics_Values9`, `MutuallyUnbiased_PairSemantics_Values1`.
--
--   **Imports.** It imports the bundle `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D208`, `OAIQ106D209`, `OAIQ106D210`, `OAIQ106D211`, `OAIQ106D212`, `OAIQ106D213`, `OAIQ106D214`, `OAIQ106D215`, `OAIQ106D216`, `OAIQ106D217`, `OAIQ106D218`, `OAIQ106D219`, `OAIQ106D220`, `OAIQ106D221` and `OAIQ106D222`; the statements `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound4622`, `OAI.MUB6.Certificate.MixedSemantics.sound4623`, `OAI.MUB6.Certificate.MixedSemantics.sound4625`, `OAI.MUB6.Certificate.MixedSemantics.sound479`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound514`, `OAI.MUB6.Certificate.MixedSemantics.sound5167`, `OAI.MUB6.Certificate.MixedSemantics.sound5168`, `OAI.MUB6.Certificate.MixedSemantics.sound5169`, `OAI.MUB6.Certificate.MixedSemantics.sound5171`, `OAI.MUB6.Certificate.MixedSemantics.sound5172`, `OAI.MUB6.Certificate.MixedSemantics.sound5174`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5292`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSemantics.sound5386`, `OAI.MUB6.Certificate.MixedSemantics.sound5387`, `OAI.MUB6.Certificate.MixedSemantics.sound5388`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5416`, `OAI.MUB6.Certificate.MixedSemantics.sound5418`, `OAI.MUB6.Certificate.MixedSemantics.sound5433`, `OAI.MUB6.Certificate.MixedSemantics.sound5434`, `OAI.MUB6.Certificate.MixedSemantics.sound5435`, `OAI.MUB6.Certificate.MixedSemantics.sound5439`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5450`, `OAI.MUB6.Certificate.MixedSemantics.sound5451`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5465`, `OAI.MUB6.Certificate.MixedSemantics.sound5476`, `OAI.MUB6.Certificate.MixedSemantics.sound5482`, `OAI.MUB6.Certificate.MixedSemantics.sound5483`, `OAI.MUB6.Certificate.MixedSemantics.sound5485`, `OAI.MUB6.Certificate.MixedSemantics.sound5490`, `OAI.MUB6.Certificate.MixedSemantics.sound5491`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound5500`, `OAI.MUB6.Certificate.MixedSemantics.sound644` and `OAI.MUB6.Certificate.MixedSemantics.sound645`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1441`, `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3852`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3981`, `OAI.MUB6.Certificate.MixedSemantics.sound3982`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3995`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4013`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4050`, `OAI.MUB6.Certificate.MixedSemantics.sound4053`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound4622`, `OAI.MUB6.Certificate.MixedSemantics.sound4623`, `OAI.MUB6.Certificate.MixedSemantics.sound4625`, `OAI.MUB6.Certificate.MixedSemantics.sound479`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound514`, `OAI.MUB6.Certificate.MixedSemantics.sound5167`, `OAI.MUB6.Certificate.MixedSemantics.sound5168`, `OAI.MUB6.Certificate.MixedSemantics.sound5169`, `OAI.MUB6.Certificate.MixedSemantics.sound5171`, `OAI.MUB6.Certificate.MixedSemantics.sound5172`, `OAI.MUB6.Certificate.MixedSemantics.sound5174`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5292`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSemantics.sound5386`, `OAI.MUB6.Certificate.MixedSemantics.sound5387`, `OAI.MUB6.Certificate.MixedSemantics.sound5388`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5416`, `OAI.MUB6.Certificate.MixedSemantics.sound5418`, `OAI.MUB6.Certificate.MixedSemantics.sound5433`, `OAI.MUB6.Certificate.MixedSemantics.sound5434`, `OAI.MUB6.Certificate.MixedSemantics.sound5435`, `OAI.MUB6.Certificate.MixedSemantics.sound5439`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5450`, `OAI.MUB6.Certificate.MixedSemantics.sound5451`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5465`, `OAI.MUB6.Certificate.MixedSemantics.sound5476`, `OAI.MUB6.Certificate.MixedSemantics.sound5482`, `OAI.MUB6.Certificate.MixedSemantics.sound5483`, `OAI.MUB6.Certificate.MixedSemantics.sound5485`, `OAI.MUB6.Certificate.MixedSemantics.sound5490`, `OAI.MUB6.Certificate.MixedSemantics.sound5491`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound5500`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1674`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1777`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1793`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1852`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1853`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1882`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1913`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1914`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval334`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval368`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval360`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2201`, `OAI.MUB6.Certificate.PairSemantics.sound2243`, `OAI.MUB6.Certificate.PairSemantics.sound2244`, `OAI.MUB6.Certificate.PairSemantics.sound2293`, `OAI.MUB6.Certificate.PairSemantics.sound3241`, `OAI.MUB6.Certificate.PairSemantics.sound3254`, `OAI.MUB6.Certificate.PairSemantics.sound3258`, `OAI.MUB6.Certificate.PairSemantics.sound3284`, `OAI.MUB6.Certificate.PairSemantics.sound3293`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D002

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value101 : Sparse (Fin 909) := [(63, (1 / 1))]

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

def singlePairValue10 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 288)), (2, (-35 / 864)), (3, (-5 / 27)), (5, (5 / 18)), (6, (-5 / 144)), (7, (-5 / 9)), (8, (-5 / 27)), (9, (5 / 27)), (35, (-10 / 27)), (52, (-5 / 27)), (58, (-5 / 864)), (69, (-20 / 27)), (70, (-25 / 54)), (71, (-5 / 9)), (256, (5 / 9)), (257, (-5 / 27)), (495, (-5 / 27))]

def singlePairValue11 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (25 / 864)), (2, (65 / 864)), (5, (-5 / 54)), (6, (5 / 144)), (9, (-25 / 216)), (52, (5 / 54)), (58, (5 / 432)), (69, (5 / 27)), (71, (5 / 27)), (495, (5 / 54))]

def singlePairValue12 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 96)), (2, (-5 / 288)), (5, (-5 / 72)), (7, (5 / 27)), (9, (-5 / 54)), (35, (5 / 54)), (69, (5 / 18)), (70, (5 / 18)), (71, (5 / 54)), (257, (5 / 54))]

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

def singlePairValue270 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (5 / 48)), (13, (5 / 9))]

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

def singlePairValue121 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-35 / 864)), (2, (25 / 432)), (6, (25 / 864)), (8, (5 / 54)), (58, (-5 / 864)), (71, (5 / 54))]

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

def nodeValue5 : Sparse Master := [(Sum.inl 0, (5 / 24)), (Sum.inl 1, (-5 / 24))]

def nodeValue6 : Sparse Master := [(Sum.inl 0, (1 / 6)), (Sum.inl 1, (5 / 6))]

def nodeValue7 : Sparse Master := [(Sum.inl 0, (19 / 72)), (Sum.inl 1, (5 / 72))]

def nodeValue8 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (25 / 108)), (Sum.inl 58, (-5 / 864)), (Sum.inl 5, (25 / 72)), (Sum.inl 6, (-5 / 72)), (Sum.inl 257, (-5 / 27)), (Sum.inl 2, (-5 / 72)), (Sum.inl 69, (-5 / 6)), (Sum.inl 70, (-20 / 27)), (Sum.inl 71, (-5 / 9)), (Sum.inl 7, (-5 / 9)), (Sum.inl 35, (-5 / 18)), (Sum.inl 1, (-5 / 864))]

def nodeValue9 : Sparse Master := [(Sum.inl 0, (1 / 54)), (Sum.inl 9, (-5 / 36)), (Sum.inl 58, (5 / 432)), (Sum.inl 5, (-5 / 54)), (Sum.inl 6, (5 / 108)), (Sum.inl 2, (-5 / 288)), (Sum.inl 69, (5 / 54)), (Sum.inl 70, (5 / 54)), (Sum.inl 71, (5 / 27)), (Sum.inl 1, (5 / 288))]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue4177 : Sparse Master := [(Sum.inr 605, (-1 / 4)), (Sum.inr 1518, (-1 / 4))]

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

def nodeValue4391 : Sparse Master := [(Sum.inr 4391, (1 / 1))]

def nodeValue4392 : Sparse Master := [(Sum.inr 4392, (1 / 1))]

def nodeValue4396 : Sparse Master := [(Sum.inr 977, (-1 / 4)), (Sum.inr 1597, (-1 / 4))]

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


